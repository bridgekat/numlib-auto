/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CR
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter04.Section01
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter07.Section01
import NumlibSurface.SaadSparse.Chapter09.Section01

/-!
# Saad, Section 9.2: The preconditioned conjugate gradient method

This module formalizes Section 9.2 of [saad2003iterative], with Problems P-9.2, P-9.3, P-9.6,
P-9.8(c) and P-9.12. Let $A \in \mathbb{K}^{n \times n}$ be symmetric and let the preconditioner $M$
be symmetric positive definite. The preconditioned matrix $M^{-1} A$ is not symmetric for the
Euclidean inner product, but it is self-adjoint for the $M$-inner product $(x, y)_M = (Mx, y)$. The
conjugate gradient method can therefore be run on $M^{-1} A x = M^{-1} b$ in that inner product.
None of its $M$-inner products has to be formed, because $(z_j, z_j)_M = (r_j, z_j)$ and
$(M^{-1} A p_j, p_j)_M = (A p_j, p_j)$ for $z_j = M^{-1} r_j$. The result is Algorithm 9.1. Its
iterate $x_j$ is the Galerkin iterate of $Ax = b$ over $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$,
and it satisfies the conjugate gradient error bound with the condition number of the generalized
eigenvalue problem $Ax = \lambda Mx$.

For a factored preconditioner $M = L L^H$, Algorithm 9.2 runs the conjugate gradient method on
$L^{-1} A L^{-H} u = L^{-1} b$; its iterates are the iterates of Algorithm 9.1. The conjugate
gradient method for the right-preconditioned system $A M^{-1} u = b$ in the $M^{-1}$-inner product
is also Algorithm 9.1, after the change of variables $x = M^{-1} u$. Section 9.2.2 gives Eisenstat's
implementation: for $A = D_0 - E - E^T$ and the preconditioner $M = (D - E) D^{-1} (D - E^T)$, the
split-preconditioned matrix can be applied with two triangular solves and one product with the
diagonal $D_0 - 2D$. The proofs specialize the backbone recurrences `Krylov.PCG.iterate`,
`CG.iterate` and `CR.iterate` of `Numlib.Krylov.Preconditioned`, `Numlib.Krylov.CG` and
`Numlib.Krylov.CR`.

## Main definitions

* Algorithm 9.1, `SaadSparse.Chapter09.pcg`: the preconditioned conjugate gradient method.
* Algorithm 9.2, `SaadSparse.Chapter09.splitPcg`: the conjugate gradient method with the split
  preconditioner $M = L L^H$.
* Section 9.2.1, `SaadSparse.Chapter09.rightPcg`: the conjugate gradient method for $A M^{-1} u = b$
  in the $M^{-1}$-inner product.
* Algorithm 9.3, `SaadSparse.Chapter09.eisenstat`: Eisenstat's implementation of the product with
  the split-preconditioned matrix.
* Problem P-9.2, `SaadSparse.Chapter09.pcgEnergyA`: the analogue of Algorithm 9.1 in the $A$-inner
  product, with one matrix-vector product per step.
* Problem P-9.12, `SaadSparse.Chapter09.pcr`: the preconditioned conjugate residual method.

## Main results

* Section 9.2.1, `SaadSparse.Chapter09.isPreconditioner`: a symmetric positive definite matrix is a
  preconditioner in the sense of the backbone.
* Section 9.2.1, `SaadSparse.Chapter09.isSymmetric_energy`: $M^{-1} A$ is self-adjoint for the
  $M$-inner product.
* Section 9.2.1, `SaadSparse.Chapter09.pcg_eq`: Algorithm 9.1 is the backbone preconditioned
  conjugate gradient recurrence.
* Section 9.2.1, `SaadSparse.Chapter09.pcg_isGalerkinIterate`: the iterate of Algorithm 9.1 is the
  Galerkin iterate over $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$.
* Section 9.2.1 and Problem P-9.3, `SaadSparse.Chapter09.splitPcg_eq_pcg`: Algorithms 9.1 and 9.2
  produce the same iterates and search directions.
* Section 9.2.1, `SaadSparse.Chapter09.splitPcg_eq_cg`: Algorithm 9.2 computes the conjugate
  gradient iterates of $L^{-1} A L^{-H} u = L^{-1} b$ in the variable $u = L^H x$.
* Section 9.2.1, `SaadSparse.Chapter09.isSymmetric_energyInv`: $A M^{-1}$ is self-adjoint for the
  $M^{-1}$-inner product.
* Section 9.2.1, `SaadSparse.Chapter09.rightPcg_eq_pcg`: the right-preconditioned method in the
  $M^{-1}$-inner product is Algorithm 9.1.
* Section 9.2.2, `SaadSparse.Chapter09.leftPreconditioned_apply_eq_add`: for $M = A - R$,
  $M^{-1} A v = v + M^{-1} R v$.
* Section 9.2.2, `SaadSparse.Chapter09.decomp_symm`: a symmetric matrix splits as
  $A = D_0 - E - E^T$.
* Equation (9.8), `SaadSparse.Chapter09.equation_9_8`: the identity $(D - E)^{-1} A (D - E^T)^{-1} =
  (D - E)^{-1} D_1 (D - E^T)^{-1} + (D - E)^{-1} + (D - E^T)^{-1}$ with $D_1 = D_0 - 2D$.
* Algorithm 9.3, `SaadSparse.Chapter09.eisenstat_eq`: Eisenstat's implementation computes the
  product with the split-preconditioned matrix.
* Example 9.1, `SaadSparse.Chapter09.example_9_1`: the two operation counts of Section 9.2.2 at
  $N_z(A) = 5n$.
* Problem P-9.2(a), `SaadSparse.Chapter09.isSymmetric_energyA`: for positive definite $A$,
  $M^{-1} A$ is self-adjoint for the $A$-inner product.
* Problem P-9.2, `SaadSparse.Chapter09.pcgEnergyA_eq`: the algorithm in the $A$-inner product is the
  backbone preconditioned conjugate gradient recurrence for $A M^{-1} A x = A M^{-1} b$ with the
  preconditioner $A$.
* Problem P-9.2, `SaadSparse.Chapter09.pcgEnergyA_isGalerkinIterate`: its iterate is the Galerkin
  iterate of $A M^{-1} A x = A M^{-1} b$ over $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$.
* Problem P-9.6, `SaadSparse.Chapter09.problem_9_6`: the conjugate gradient error bound for
  Algorithm 9.1, with the condition number of $Ax = \lambda Mx$.
* Problem P-9.8(c), `SaadSparse.Chapter09.problem_9_8c`: Eisenstat's identity after the symmetric
  scaling by $D^{1/2}$.
* Problem P-9.8(c), `SaadSparse.Chapter09.problem_9_8c_ssor`: for the SSOR choice $D = D_0$, the
  matrix $D_2$ of the scaled identity is $-I$.
* Problem P-9.12, `SaadSparse.Chapter09.pcr_eq`: the preconditioned conjugate residual method is the
  backbone conjugate residual recurrence for $M^{-1} A$ in the $M$-inner product.

## Conventions

* The inner product $(x, y)$ of the book is linear in $x$; the Lean expression `inner 𝕜 y x` is
  $(x, y)$. The $M$-inner product $(x, y)_M = (Mx, y)$ appears as `energyInner (op M)`, defined as
  `energyInner (op M) x y = inner 𝕜 (op M x) y`. The norm $\|x\|_A = (Ax, x)^{1/2}$ is
  `energyNorm (op A) x`.
* "$M$ is a preconditioner" is `Krylov.IsPreconditioner (op M) (op M⁻¹)`: $M$ is symmetric and
  coercive, and $M^{-1}$ inverts it.
* $A = D_0 - E - F$ is the splitting (4.2): $D_0$, $E$ and $F$ are `SaadSparse.Chapter04.D A`,
  `SaadSparse.Chapter04.E A` and `SaadSparse.Chapter04.F A`.

## Implementation notes

* Each algorithm is a step function on a tuple of vectors, iterated $j$ times. Indices are
  $0$-based. Division by a vanishing quantity is $0$, which reproduces the breakdown behaviour of
  the book.
* The preconditioned residual $z_j = M^{-1} r_j$ of Algorithm 9.1 is recomputed from $r_j$ and is
  not stored in the state.
* The definition `SaadSparse.Chapter09.eisenstat` is the procedure that Section 9.2.2 states before
  Algorithm 9.3. Algorithm 9.3 itself is its rescaling by $D^{-1}$, which saves one product with the
  diagonal and computes the same vector.
* Example 9.1 is arithmetic on the two operation counts of Section 9.2.2. The library does not count
  operations, so the counts are hypotheses of the statement.

## Deviations from the source

* **Generalization.** The weighted self-adjointness arguments extend to Hermitian data and separate
  the symmetry hypotheses. See `SaadSparse.Chapter09.isPreconditioner`,
  `SaadSparse.Chapter09.isSymmetric_energy`, `SaadSparse.Chapter09.energyInner_leftPreconditioned`,
  `SaadSparse.Chapter09.energyInner_inv`, `SaadSparse.Chapter09.isSymmetric_energyA`,
  `SaadSparse.Chapter09.isSymmetric_energyInv`.
* **Generalization.** The PCG recurrence uses totalized operations and a fixed step count with the
  preconditioned residual derived from the state. See `SaadSparse.Chapter09.pcgStepAlpha`,
  `SaadSparse.Chapter09.pcgStepR`, `SaadSparse.Chapter09.pcgStepBeta`,
  `SaadSparse.Chapter09.pcgStep`, `SaadSparse.Chapter09.pcg`,
  `SaadSparse.Chapter09.pcgStepAlpha_def`, `SaadSparse.Chapter09.pcgStepR_def`,
  `SaadSparse.Chapter09.pcgStepBeta_def`, `SaadSparse.Chapter09.pcgAlpha`,
  `SaadSparse.Chapter09.pcgBeta`, `SaadSparse.Chapter09.pcgAlpha_eq`,
  `SaadSparse.Chapter09.pcgBeta_eq`.
* **Generalization.** The PCG Galerkin characterization uses explicit coercivity relative to the
  preconditioner. See `SaadSparse.Chapter09.pcg_isGalerkinIterate`.
* **Scope.** The PCG error bound uses relative quadratic-form constants and the
  weighted-inner-product proof. See `SaadSparse.Chapter09.problem_9_6`.
* **Generalization.** The split PCG recurrence uses the complex adjoint and totalized operations.
  See `SaadSparse.Chapter09.splitPcgStepAlpha`, `SaadSparse.Chapter09.splitPcgStepR`,
  `SaadSparse.Chapter09.splitPcgStepBeta`, `SaadSparse.Chapter09.splitPcgStep`,
  `SaadSparse.Chapter09.splitPcg`, `SaadSparse.Chapter09.splitPcg_succ`.
* **Generalization.** Split preconditioning compares full states, with invertibility required for
  the ordinary CG coordinate change. See `SaadSparse.Chapter09.splitPcg_eq_pcg`,
  `SaadSparse.Chapter09.splitPcg_eq_cg`.
* **Generalization.** The right-preconditioned recurrence extends to complex data, with symmetry
  sufficient for the state comparison. See `SaadSparse.Chapter09.rightPcgStepAlpha`,
  `SaadSparse.Chapter09.rightPcgStepR`, `SaadSparse.Chapter09.rightPcgStepBeta`,
  `SaadSparse.Chapter09.rightPcgStep`, `SaadSparse.Chapter09.rightPcg`,
  `SaadSparse.Chapter09.rightPcg_succ`, `SaadSparse.Chapter09.rightPcg_eq_pcg`.
* **Representation.** The solution to P-9.2 records the two auxiliary images and states algebraic
  updates. See `SaadSparse.Chapter09.pcgEnergyAStepAlpha`, `SaadSparse.Chapter09.pcgEnergyAStepZ`,
  `SaadSparse.Chapter09.pcgEnergyAStepW`, `SaadSparse.Chapter09.pcgEnergyAStepBeta`,
  `SaadSparse.Chapter09.pcgEnergyAStep`, `SaadSparse.Chapter09.pcgEnergyA`,
  `SaadSparse.Chapter09.pcgEnergyA_succ`.
* **Derivation.** The energy-A recurrence has a transformed-state equivalence and a Galerkin
  characterization. See `SaadSparse.Chapter09.pcgEnergyA_eq`,
  `SaadSparse.Chapter09.pcgEnergyA_isGalerkinIterate`.
* **Generalization.** The preconditioned CR recurrence gives total updates and their energy-space
  interpretation. See `SaadSparse.Chapter09.pcrStepAlpha`, `SaadSparse.Chapter09.pcrStepZ`,
  `SaadSparse.Chapter09.pcrStepBeta`, `SaadSparse.Chapter09.pcrStep`, `SaadSparse.Chapter09.pcr`,
  `SaadSparse.Chapter09.pcr_succ`, `SaadSparse.Chapter09.pcr_eq`,
  `SaadSparse.Chapter09.pcr_residual_eq`.
* **Generalization.** The inverse-sum formula allows a general matrix in place of the diagonal. See
  `SaadSparse.Chapter09.equation_9_8`.
* **Scope.** The Eisenstat product uses the unscaled formula preceding Algorithm 9.3. See
  `SaadSparse.Chapter09.eisenstat`, `SaadSparse.Chapter09.eisenstat_def`,
  `SaadSparse.Chapter09.eisenstat_eq`.
* **Scope.** The split Eisenstat exercise gives the matrix identity and the SSOR simplification. See
  `SaadSparse.Chapter09.problem_9_8c`, `SaadSparse.Chapter09.problem_9_8c_ssor`.
* **Scope.** Example 9.1 formalizes the arithmetic of the stated counts. See
  `SaadSparse.Chapter09.example_9_1`.

## Not formalized

* Problem P-9.7.
* Problem P-9.8(a) and (b).
* Problem P-9.9.
-/

open Matrix

open scoped ComplexOrder Matrix SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries: adjoints, products and preconditioners -/

/-- For $B, C \in \mathbb{K}^{n \times n}$, the operator of the product $BC$ is the composite of the
operators of $B$ and $C$. -/
theorem op_mul (B C : Matrix (Fin n) (Fin n) 𝕜) : op (B * C) = op B ∘ₗ op C :=
  Matrix.toEuclideanLin_mul B C

/-- For $B, C \in \mathbb{K}^{n \times n}$ and $x \in \mathbb{K}^n$, $(BC)x = B(Cx)$. -/
theorem op_mul_apply (B C : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : op (B * C) x = op B (op C x) := by
  rw [op_mul]; rfl

/-- The operator of a Hermitian matrix is symmetric. -/
theorem isSymmetric_op {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.IsHermitian) :
    (op B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 hB

/-- The inverse of a symmetric positive definite matrix is symmetric positive definite. So $M^{-1}$
defines an inner product, the $M^{-1}$-inner product of Section 9.2.1. -/
theorem posDef_inv {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M.PosDef) : M⁻¹.PosDef :=
  hM.inv

/-- **Section 9.2.1** of [saad2003iterative], the preconditioner. Let
$M \in \mathbb{K}^{n \times n}$ be symmetric positive definite. Then $M$ is a preconditioner in
the sense of the backbone: the operator of $M$ is symmetric and coercive, and the operator of
$M^{-1}$ is its inverse.

The conclusion is `Krylov.IsPreconditioner (op M) (op M⁻¹)`. Coercivity comes from
`Matrix.posDef_iff_isSymmetricCoercive`.

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem isPreconditioner {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M.PosDef) :
    Krylov.IsPreconditioner (op M) (op M⁻¹) where
  isSymmetricCoercive := (Matrix.posDef_iff_isSymmetricCoercive M).1 hM
  apply_inv x := by
    have h1 : op M ∘ₗ op M⁻¹ = LinearMap.id := by
      rw [← op_mul, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM.isUnit)]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 x

/-! ### Section 9.2.1: the three self-adjointness observations -/

variable {A M : Matrix (Fin n) (Fin n) 𝕜}

/-- **Section 9.2.1** of [saad2003iterative], self-adjointness of $M^{-1} A$. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric and let $M$ be a preconditioner. Then $M^{-1} A$ is
self-adjoint for the $M$-inner product $(x, y)_M = (Mx, y)$:
$$(M^{-1} A x, y)_M = (x, M^{-1} A y)_M \quad \text{for all } x, y.$$

This is why the conjugate gradient method can be run on the preconditioned system, although
$M^{-1} A$ is not symmetric for the Euclidean inner product. The statement is the symmetry of
`hM.energyEnd (op M⁻¹ ∘ₗ op A)`, the operator $M^{-1} A$ on the space with the $M$-inner
product.

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem isSymmetric_energy (hA : (op A).IsSymmetric)
    (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) :
    (hM.energyEnd (op M⁻¹ ∘ₗ op A)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective v
  rw [hM.inner_energyEnd_left (op A), hM.inner_energyEnd_right (op A), hA]

/-- Let $M$ be a preconditioner. Then $(M^{-1} A x, y)_M = (Ax, y)$ for all $x, y \in \mathbb{K}^n$.
This identity keeps the $M$-inner products out of Algorithm 9.1 of [saad2003iterative].

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem energyInner_leftPreconditioned (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (x y : 𝔼) :
    energyInner (op M) (op M⁻¹ (op A x)) y = inner 𝕜 (op A x) y := by
  rw [energyInner, hM.apply_inv]

/-- Let $M$ be a preconditioner. Then $(M^{-1} x, M^{-1} y)_M = (x, M^{-1} y)$ for all
$x, y \in \mathbb{K}^n$. With $x = y = r_j$ this is $(z_j, z_j)_M = (r_j, z_j)$, the numerator
of the step length in line 3 of Algorithm 9.1 of [saad2003iterative].

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem energyInner_inv (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (x y : 𝔼) :
    energyInner (op M) (op M⁻¹ x) (op M⁻¹ y) = inner 𝕜 x (op M⁻¹ y) := by
  rw [energyInner, hM.apply_inv]

/-- **Problem P-9.2(a)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be symmetric
positive definite, with inverse $A^{-1}$, and let $M^{-1}$ be symmetric. Then $M^{-1} A$ is
self-adjoint for the $A$-inner product $(x, y)_A = (Ax, y)$.

The hypothesis that $A$ is symmetric positive definite is
`Krylov.IsPreconditioner (op A) (op A⁻¹)`; the separate hypothesis that $A$ is symmetric is also
present. This observation is the basis of `SaadSparse.Chapter09.pcgEnergyA`.

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem isSymmetric_energyA (hA : (op A).IsSymmetric)
    (hMinv : (op M⁻¹).IsSymmetric) (hAp : Krylov.IsPreconditioner (op A) (op A⁻¹)) :
    (hAp.energyEnd (op M⁻¹ ∘ₗ op A)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hAp.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hAp.toEnergy.surjective v
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    WithEnergy.inner_equiv, WithEnergy.inner_equiv, energyInner, energyInner,
    LinearMap.comp_apply, LinearMap.comp_apply, hA]
  exact hMinv _ _

/-- **Section 9.2.1** of [saad2003iterative], closing paragraph. Let $A \in \mathbb{K}^{n \times n}$
be symmetric, and let $M^{-1}$ be symmetric positive definite with inverse $M$. Then $A M^{-1}$
is self-adjoint for the $M^{-1}$-inner product $(x, y)_{M^{-1}} = (M^{-1} x, y)$.

So right preconditioning in the $M^{-1}$-inner product is as legitimate as left preconditioning
in the $M$-inner product. By `SaadSparse.Chapter09.rightPcg_eq_pcg` the two give the same
method. The hypothesis on $M^{-1}$ is `Krylov.IsPreconditioner (op M⁻¹) (op M)`.

**Generalization.** The self-adjointness and inner-product identities extend to complex Hermitian
data. The proofs distinguish the positive definiteness needed for an energy inner product from
symmetry of the operator acting in it.
-/
theorem isSymmetric_energyInv (hA : (op A).IsSymmetric)
    (hMi : Krylov.IsPreconditioner (op M⁻¹) (op M)) :
    (hMi.energyEnd (op A ∘ₗ op M⁻¹)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hMi.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hMi.toEnergy.surjective v
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    WithEnergy.inner_equiv, WithEnergy.inner_equiv, energyInner, energyInner,
    LinearMap.comp_apply, LinearMap.comp_apply, hMi.isSymmetricCoercive.isSymmetric]
  exact hA _ _

/-! ### Algorithm 9.1: the preconditioned conjugate gradient method -/

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length $\alpha_j = (r_j, z_j)/(A p_j, p_j)$ of line 3 of Algorithm 9.1 of
[saad2003iterative], on a state $(x_j, r_j, p_j)$, with $z_j = M^{-1} r_j$. The vector $z_j$ is
recomputed from $r_j$ and is not stored.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- The next residual $r_{j+1} = r_j - \alpha_j A p_j$ of line 5 of Algorithm 9.1 of
[saad2003iterative], on a state $(x_j, r_j, p_j)$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 := s.2.1 - pcgStepAlpha A M s • op A s.2.2

/-- The coefficient $\beta_j = (r_{j+1}, z_{j+1})/(r_j, z_j)$ of line 7 of Algorithm 9.1 of
[saad2003iterative], on a state $(x_j, r_j, p_j)$, with $z = M^{-1} r$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ (pcgStepR A M s)) (pcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1

/-- One pass through lines 3–8 of Algorithm 9.1 of [saad2003iterative]. It maps the state
$(x_j, r_j, p_j)$ to $(x_j + \alpha_j p_j, \; r_{j+1}, \; M^{-1} r_{j+1} + \beta_j p_j)$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgStepAlpha A M s • s.2.2, pcgStepR A M s,
    op M⁻¹ (pcgStepR A M s) + pcgStepBeta A M s • s.2.2)

/-- **Algorithm 9.1** of [saad2003iterative] (preconditioned conjugate gradient). Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. Set $r_0 = b - A x_0$ and
$p_0 = z_0 = M^{-1} r_0$. For $j = 0, 1, \ldots$ compute
$$\alpha_j = \frac{(r_j, z_j)}{(A p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  r_{j+1} = r_j - \alpha_j A p_j,$$
$$z_{j+1} = M^{-1} r_{j+1}, \quad \beta_j = \frac{(r_{j+1}, z_{j+1})}{(r_j, z_j)}, \quad
  p_{j+1} = z_{j+1} + \beta_j p_j.$$
The value at $j$ is the triple $(x_j, r_j, p_j)$ after $j$ steps.

The definition accepts any matrices $A$ and $M$. The results below assume that $A$ is symmetric
and that $M$ is a preconditioner. A division by $0$ gives $0$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcg (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (pcgStep A M)^[j] (x₀, b - op A x₀, op M⁻¹ (b - op A x₀))

/-- The step length of Algorithm 9.1 on a state $(x, r, p)$ is $(r, M^{-1} r)/(Ap, p)$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
theorem pcgStepAlpha_def (s : 𝔼 × 𝔼 × 𝔼) :
    pcgStepAlpha A M s = inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 s.2.2 (op A s.2.2) := rfl

/-- The next residual of Algorithm 9.1 on a state $(x, r, p)$ is $r - \alpha A p$, with $\alpha$ the
step length.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
theorem pcgStepR_def (s : 𝔼 × 𝔼 × 𝔼) :
    pcgStepR A M s = s.2.1 - pcgStepAlpha A M s • op A s.2.2 := rfl

/-- The coefficient $\beta$ of Algorithm 9.1 on a state $(x, r, p)$ is
$(r', M^{-1} r')/(r, M^{-1} r)$, with $r'$ the next residual.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
theorem pcgStepBeta_def (s : 𝔼 × 𝔼 × 𝔼) : pcgStepBeta A M s =
    inner 𝕜 (op M⁻¹ (pcgStepR A M s)) (pcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1 := rfl

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The iterate $x_j$ of Algorithm 9.1 of [saad2003iterative]. -/
noncomputable def pcgX (j : ℕ) : 𝔼 := (pcg A M b x₀ j).1

/-- The residual $r_j$ of Algorithm 9.1 of [saad2003iterative], as computed by the recurrence. -/
noncomputable def pcgR (j : ℕ) : 𝔼 := (pcg A M b x₀ j).2.1

/-- The search direction $p_j$ of Algorithm 9.1 of [saad2003iterative]. -/
noncomputable def pcgP (j : ℕ) : 𝔼 := (pcg A M b x₀ j).2.2

/-- The preconditioned residual $z_j = M^{-1} r_j$ of line 6 of Algorithm 9.1 of
[saad2003iterative]. -/
noncomputable def pcgZ (j : ℕ) : 𝔼 := op M⁻¹ (pcgR A M b x₀ j)

/-- The step length $\alpha_j$ of Algorithm 9.1 of [saad2003iterative] at step $j$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgAlpha (j : ℕ) : 𝕜 := pcgStepAlpha A M (pcg A M b x₀ j)

/-- The coefficient $\beta_j$ of Algorithm 9.1 of [saad2003iterative] at step $j$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
noncomputable def pcgBeta (j : ℕ) : 𝕜 := pcgStepBeta A M (pcg A M b x₀ j)

/-- The state of Algorithm 9.1 after $j + 1$ steps is one step applied to the state after $j$ steps.
-/
theorem pcg_succ (j : ℕ) : pcg A M b x₀ (j + 1) = pcgStep A M (pcg A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Line 1 of Algorithm 9.1: the iteration starts at $x_0$. -/
@[simp] theorem pcgX_zero : pcgX A M b x₀ 0 = x₀ := rfl

/-- Line 1 of Algorithm 9.1: $r_0 = b - A x_0$. -/
@[simp] theorem pcgR_zero : pcgR A M b x₀ 0 = b - op A x₀ := rfl

/-- Line 1 of Algorithm 9.1: $p_0 = z_0$. -/
@[simp] theorem pcgP_zero : pcgP A M b x₀ 0 = pcgZ A M b x₀ 0 := rfl

/-- Line 3 of Algorithm 9.1: $\alpha_j = (r_j, z_j)/(A p_j, p_j)$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
theorem pcgAlpha_eq (j : ℕ) : pcgAlpha A M b x₀ j =
    inner 𝕜 (pcgZ A M b x₀ j) (pcgR A M b x₀ j) /
      inner 𝕜 (pcgP A M b x₀ j) (op A (pcgP A M b x₀ j)) := rfl

/-- Line 4 of Algorithm 9.1: $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem pcgX_succ (j : ℕ) :
    pcgX A M b x₀ (j + 1) = pcgX A M b x₀ j + pcgAlpha A M b x₀ j • pcgP A M b x₀ j := by
  rw [pcgX, pcg_succ]; rfl

/-- Line 5 of Algorithm 9.1: $r_{j+1} = r_j - \alpha_j A p_j$. -/
theorem pcgR_succ (j : ℕ) :
    pcgR A M b x₀ (j + 1) = pcgR A M b x₀ j - pcgAlpha A M b x₀ j • op A (pcgP A M b x₀ j) := by
  rw [pcgR, pcg_succ]; rfl

private theorem pcgR_succ_eq_pcgStepR (j : ℕ) :
    pcgR A M b x₀ (j + 1) = pcgStepR A M (pcg A M b x₀ j) := by
  rw [pcgR, pcg_succ]; rfl

/-- Line 7 of Algorithm 9.1: $\beta_j = (r_{j+1}, z_{j+1})/(r_j, z_j)$.

**Generalization.** The formulas use totalized inverses and quotients over complex scalars and are
available outside the source's SPD setting. The recurrences specify fixed step counts and compute
$z_j$ from the residual in the stored state.
-/
theorem pcgBeta_eq (j : ℕ) : pcgBeta A M b x₀ j =
    inner 𝕜 (pcgZ A M b x₀ (j + 1)) (pcgR A M b x₀ (j + 1)) /
      inner 𝕜 (pcgZ A M b x₀ j) (pcgR A M b x₀ j) := by
  rw [pcgBeta, pcgStepBeta_def, pcgZ, pcgZ, pcgR_succ_eq_pcgStepR]
  rfl

/-- Line 8 of Algorithm 9.1: $p_{j+1} = z_{j+1} + \beta_j p_j$. -/
theorem pcgP_succ (j : ℕ) :
    pcgP A M b x₀ (j + 1) = pcgZ A M b x₀ (j + 1) + pcgBeta A M b x₀ j • pcgP A M b x₀ j := by
  rw [pcgP, pcg_succ, pcgZ, pcgR_succ_eq_pcgStepR]
  rfl

/-! ### The bridge to the backbone preconditioned conjugate gradient recurrence -/

variable {A M}

private theorem pcgStepAlpha_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepAlpha A M (s.x, s.r, s.p) = Krylov.PCG.alpha (op A) (op M⁻¹) s := by
  rw [pcgStepAlpha_def, Krylov.PCG.alpha, hMinv s.r s.r, ← hA s.p s.p]

private theorem pcgStepR_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepR A M (s.x, s.r, s.p) = (Krylov.PCG.step (op A) (op M⁻¹) s).r := by
  rw [pcgStepR_def, pcgStepAlpha_eq_PCG hA hMinv s, Krylov.PCG.step_r]

private theorem pcgStepBeta_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepBeta A M (s.x, s.r, s.p) = Krylov.PCG.beta (op A) (op M⁻¹) s := by
  rw [pcgStepBeta_def, pcgStepR_eq_PCG hA hMinv s, Krylov.PCG.beta,
    hMinv (Krylov.PCG.step (op A) (op M⁻¹) s).r _, hMinv s.r s.r]

private theorem pcgStep_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStep A M (s.x, s.r, s.p) = ((Krylov.PCG.step (op A) (op M⁻¹) s).x,
      (Krylov.PCG.step (op A) (op M⁻¹) s).r, (Krylov.PCG.step (op A) (op M⁻¹) s).p) := by
  rw [pcgStep, pcgStepAlpha_eq_PCG hA hMinv s, pcgStepR_eq_PCG hA hMinv s,
    pcgStepBeta_eq_PCG hA hMinv s, Krylov.PCG.step_x, Krylov.PCG.step_p]

/-- **Section 9.2.1** of [saad2003iterative], Algorithm 9.1 as a backbone recurrence. Let
$A, M \in \mathbb{K}^{n \times n}$ with $A$ and $M^{-1}$ symmetric. Then for all
$b, x_0 \in \mathbb{K}^n$ and all $j$, the triple $(x_j, r_j, p_j)$ of Algorithm 9.1 is the
iterate, the residual and the search direction of the backbone preconditioned conjugate gradient
recurrence `Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j`.

The symmetry of $A$ and of $M^{-1}$ moves each operator across the inner products of lines 3
and 7. -/
theorem pcg_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcg A M b x₀ j = ((Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).x,
      (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).r,
      (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcg_succ, ih, Krylov.PCG.iterate_succ, pcgStep_eq_PCG hA hMinv]

/-- Let $A$ and $M^{-1}$ be symmetric. The iterate $x_j$ of Algorithm 9.1 is the iterate of
`Krylov.PCG.iterate`. -/
theorem pcgX_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgX A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).x := by
  rw [pcgX, pcg_eq hA hMinv]

/-- Let $A$ and $M^{-1}$ be symmetric. The residual $r_j$ of Algorithm 9.1 is the residual of
`Krylov.PCG.iterate`. -/
theorem pcgR_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgR A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).r := by
  rw [pcgR, pcg_eq hA hMinv]

/-- Let $A$ and $M^{-1}$ be symmetric. The search direction $p_j$ of Algorithm 9.1 is the search
direction of `Krylov.PCG.iterate`. -/
theorem pcgP_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgP A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).p := by
  rw [pcgP, pcg_eq hA hMinv]

/-- Let $M$ be a preconditioner and let $A$ be symmetric. Then the residual $r_j$ of Algorithm 9.1
is the true residual: $r_j = b - A x_j$. -/
theorem pcgR_eq_residual (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (hA : (op A).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgR A M b x₀ j = b - op A (pcgX A M b x₀ j) := by
  rw [pcgR_eq hA hM.isSymmetric_inv, pcgX_eq hA hM.isSymmetric_inv,
    Krylov.PCG.residual_eq _ _ _ _ hM]

/-- **Section 9.2.1** of [saad2003iterative], Algorithm 9.1 as a projection method. Let $M$ be a
preconditioner, and let $A \in \mathbb{K}^{n \times n}$ be symmetric with
$c\,(Mx, x) \le (Ax, x)$ for all $x$, for some $c > 0$. Then for all $b, x_0 \in \mathbb{K}^n$
and all $j$, the iterate $x_j$ of Algorithm 9.1 is the Galerkin iterate of $Ax = b$ over
$x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$, with $r_0 = b - A x_0$:
$$x_j - x_0 \in \mathcal{K}_j(M^{-1} A, M^{-1} r_0), \qquad b - A x_j \perp \mathcal{K}_j(M^{-1}
  A, M^{-1} r_0).$$

For symmetric positive definite $A$ this is the condition that $x_j$ minimizes the $A$-norm of
the error over that affine space. The Krylov subspace is `SaadSparse.Chapter06.krylov`, and the
conclusion is `IsGalerkin`.

**Generalization.** The Galerkin property is formalized over complex scalars with explicit
coercivity relative to the preconditioner, in the affine space generated by the left-preconditioned
operator.
-/
theorem pcg_isGalerkinIterate (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (hA : (op A).IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ RCLike.re (inner 𝕜 (op A x) x))
    (b x₀ : 𝔼) (j : ℕ) :
    IsGalerkin (op A) b x₀ (Chapter06.krylov (M⁻¹ * A) (op M⁻¹ (b - op A x₀)) j)
      (pcgX A M b x₀ j) := by
  rw [pcgX_eq hA hM.isSymmetric_inv, Chapter06.krylov_eq, op_mul]
  exact Krylov.PCG.isGalerkinIterate hM hA hc hcoer j

/-- **Problem P-9.6** of [saad2003iterative]. Let $M$ be a preconditioner and let
$A \in \mathbb{K}^{n \times n}$ be symmetric. Let $0 < \lambda_{\min} \le \lambda_{\max}$ be
real numbers with
$$\lambda_{\min} (Mx, x) \le (Ax, x) \le \lambda_{\max} (Mx, x) \quad \text{for all } x,$$
and let $A x_* = b$. Put $\kappa = \lambda_{\max}/\lambda_{\min}$. Then the iterates of
Algorithm 9.1 satisfy, for all $x_0$ and all $j$,
$$\|x_* - x_j\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^j \|x_* -
  x_0\|_A.$$

The number $\kappa$ is a bound on the condition number of the generalized eigenvalue problem
$Ax = \lambda Mx$, that is, of $M^{-1} A$ in the $M$-inner product. Preconditioning changes only
which condition number appears in the bound. The numbers $\lambda_{\min}$ and $\lambda_{\max}$
are bounds on the quadratic forms and need not be eigenvalues. The norm $\|\cdot\|_A$ is
`energyNorm (op A)`.

**Reading.** Lean gives the energy-norm bound using arbitrary positive relative quadratic-form
bounds, which need not be eigenvalues. The proof uses the weighted-inner-product argument. The
exercise also asks for a second derivation using the split recurrence.
-/
theorem problem_9_6 (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (hA : (op A).IsSymmetric)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : 𝔼, lmin * RCLike.re (inner 𝕜 (op M x) x) ≤ RCLike.re (inner 𝕜 (op A x) x))
    (hmax : ∀ x : 𝔼, RCLike.re (inner 𝕜 (op A x) x) ≤ lmax * RCLike.re (inner 𝕜 (op M x) x))
    {b x₀ xstar : 𝔼} (hstar : op A xstar = b) (j : ℕ) :
    energyNorm (op A) (xstar - pcgX A M b x₀ j) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ j *
        energyNorm (op A) (xstar - x₀) := by
  rw [pcgX_eq hA hM.isSymmetric_inv]
  exact Krylov.PCG.energyNorm_error_le hM hA hl hll hmin hmax hstar j

/-! ### Algorithm 9.2: the split-preconditioner conjugate gradient method -/

variable (A) (L : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length $\alpha_j = (\hat r_j, \hat r_j)/(A p_j, p_j)$ of line 3 of Algorithm 9.2 of
[saad2003iterative], on a state $(x_j, \hat r_j, p_j)$.

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
noncomputable def splitPcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- The next split residual $\hat r_{j+1} = \hat r_j - \alpha_j L^{-1} A p_j$ of line 5 of Algorithm
9.2 of [saad2003iterative].

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
noncomputable def splitPcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - splitPcgStepAlpha A s • op L⁻¹ (op A s.2.2)

/-- The coefficient $\beta_j = (\hat r_{j+1}, \hat r_{j+1})/(\hat r_j, \hat r_j)$ of line 6 of
Algorithm 9.2 of [saad2003iterative].

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
noncomputable def splitPcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (splitPcgStepR A L s) (splitPcgStepR A L s) / inner 𝕜 s.2.1 s.2.1

/-- One pass through lines 3–7 of Algorithm 9.2 of [saad2003iterative]. It maps the state
$(x_j, \hat r_j, p_j)$ to $(x_j + \alpha_j p_j, \; \hat r_{j+1}, \; L^{-H} \hat r_{j+1} +
\beta_j p_j)$.

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
noncomputable def splitPcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + splitPcgStepAlpha A s • s.2.2, splitPcgStepR A L s,
    op (Lᴴ)⁻¹ (splitPcgStepR A L s) + splitPcgStepBeta A L s • s.2.2)

/-- **Algorithm 9.2** of [saad2003iterative] (conjugate gradient with the split preconditioner
$M = L L^H$). Let $A, L \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. Set
$\hat r_0 = L^{-1}(b - A x_0)$ and $p_0 = L^{-H} \hat r_0$. For $j = 0, 1, \ldots$ compute
$$\alpha_j = \frac{(\hat r_j, \hat r_j)}{(A p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j,
  \quad \hat r_{j+1} = \hat r_j - \alpha_j L^{-1} A p_j,$$
$$\beta_j = \frac{(\hat r_{j+1}, \hat r_{j+1})}{(\hat r_j, \hat r_j)}, \quad p_{j+1} = L^{-H}
  \hat r_{j+1} + \beta_j p_j.$$
The value at $j$ is the triple $(x_j, \hat r_j, p_j)$ after $j$ steps.

The definition accepts any matrices $A$ and $L$. The inverse $L^{-H}$ is `(Lᴴ)⁻¹`.

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
noncomputable def splitPcg (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (splitPcgStep A L)^[j] (x₀, op L⁻¹ (b - op A x₀), op (Lᴴ)⁻¹ (op L⁻¹ (b - op A x₀)))

/-- The state of Algorithm 9.2 after $j + 1$ steps is one step applied to the state after $j$ steps.

**Generalization.** An adjoint replaces the transpose and the recurrence accepts any factor over
complex scalars. Total inverses and quotients give fixed-length iterates even when a source solve or
quotient is undefined.
-/
theorem splitPcg_succ (b x₀ : 𝔼) (j : ℕ) :
    splitPcg A L b x₀ (j + 1) = splitPcgStep A L (splitPcg A L b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A L}

/-- For $M = L L^H$, $L^{-H} L^{-1} y = M^{-1} y$: the two triangular solves of Algorithm 9.2 apply
$M^{-1}$. -/
private theorem op_inv_split {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (y : 𝔼) :
    op (Lᴴ)⁻¹ (op L⁻¹ y) = op M⁻¹ y := by
  rw [← op_mul_apply, ← Matrix.mul_inv_rev, ← hM]

/-- For $M = L L^H$, $(y, M^{-1} x) = (L^{-1} y, L^{-1} x)$: the $M^{-1}$-inner product of Algorithm
9.1 is the Euclidean inner product of the split residuals of Algorithm 9.2. -/
private theorem inner_op_inv_split {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (x y : 𝔼) :
    inner 𝕜 (op M⁻¹ x) y = inner 𝕜 (op L⁻¹ x) (op L⁻¹ y) := by
  have hc : (((Lᴴ)⁻¹)ᴴ) = L⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]
  rw [← op_inv_split hM, Chapter07.inner_op_conjTranspose, hc]

private theorem splitPcgStep_eq_pcgStep {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ)
    (s : 𝔼 × 𝔼 × 𝔼) :
    splitPcgStep A L (s.1, op L⁻¹ s.2.1, s.2.2)
      = ((pcgStep A M s).1, op L⁻¹ (pcgStep A M s).2.1, (pcgStep A M s).2.2) := by
  have halpha : splitPcgStepAlpha A (s.1, op L⁻¹ s.2.1, s.2.2) = pcgStepAlpha A M s := by
    rw [splitPcgStepAlpha, pcgStepAlpha_def, inner_op_inv_split hM]
  have hr : splitPcgStepR A L (s.1, op L⁻¹ s.2.1, s.2.2) = op L⁻¹ (pcgStepR A M s) := by
    rw [splitPcgStepR, pcgStepR_def, halpha, map_sub, map_smul]
  have hbeta : splitPcgStepBeta A L (s.1, op L⁻¹ s.2.1, s.2.2) = pcgStepBeta A M s := by
    rw [splitPcgStepBeta, hr, pcgStepBeta_def, inner_op_inv_split hM, inner_op_inv_split hM]
  rw [splitPcgStep, pcgStep, halpha, hr, hbeta, op_inv_split hM]

/-- **Section 9.2.1** and **Problem P-9.3** of [saad2003iterative], Algorithms 9.1 and 9.2 agree.
Let $A, L \in \mathbb{K}^{n \times n}$ and $M = L L^H$. Then for all $b, x_0 \in \mathbb{K}^n$
and all $j$, Algorithms 9.1 and 9.2 started at $x_0$ produce the same iterate $x_j$ and the same
search direction $p_j$, and the split residual of Algorithm 9.2 is $\hat r_j = L^{-1} r_j$,
where $r_j$ is the residual of Algorithm 9.1.

The change of variables $\hat r_j = L^{-1} r_j$ turns one recurrence into the other. Nothing is
assumed of $A$ or $L$ beyond $M = L L^H$. Problem P-9.3 is the same statement, read from
Algorithm 9.2 to Algorithm 9.1.

**Generalization.** Lean compares three-component states rather than only the original-coordinate
iterates. The equality of the two PCG states uses the factorization and total inverses even for
singular factors. The identification with ordinary CG on the split matrix requires an invertible
factor and a symmetric operator.
-/
theorem splitPcg_eq_pcg {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (b x₀ : 𝔼) (j : ℕ) :
    splitPcg A L b x₀ j =
      ((pcg A M b x₀ j).1, op L⁻¹ (pcg A M b x₀ j).2.1, (pcg A M b x₀ j).2.2) := by
  induction j with
  | zero =>
    exact congrArg (fun z => (x₀, op L⁻¹ (b - op A x₀), z)) (op_inv_split hM (b - op A x₀))
  | succ j ih => rw [splitPcg_succ, ih, pcg_succ, splitPcgStep_eq_pcgStep hM]

/-- **Section 9.2.1** of [saad2003iterative], Algorithm 9.2 as the conjugate gradient method for the
split system. Let $A \in \mathbb{K}^{n \times n}$ be symmetric and let
$L \in \mathbb{K}^{n \times n}$ be nonsingular. Put $\hat A = L^{-1} A L^{-H}$. Let
$(u_j, \rho_j, q_j)$ be the iterate, the residual and the search direction of the conjugate
gradient method for $\hat A u = L^{-1} b$ started at $u_0 = L^H x_0$. Then the state
$(x_j, \hat r_j, p_j)$ of Algorithm 9.2 satisfies, for all $j$,
$$L^H x_j = u_j, \qquad \hat r_j = \rho_j, \qquad L^H p_j = q_j.$$

With `SaadSparse.Chapter09.splitPcg_eq_pcg`, Algorithm 9.1 for $M = L L^H$ also computes these
iterates. The conjugate gradient method is the backbone `CG.iterate`.

**Generalization.** Lean compares three-component states rather than only the original-coordinate
iterates. The equality of the two PCG states uses the factorization and total inverses even for
singular factors. The identification with ordinary CG on the split matrix requires an invertible
factor and a symmetric operator.
-/
theorem splitPcg_eq_cg (hA : (op A).IsSymmetric) (hL : IsUnit L) (b x₀ : 𝔼) (j : ℕ) :
    op Lᴴ (splitPcg A L b x₀ j).1
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).x ∧
      (splitPcg A L b x₀ j).2.1
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).r ∧
      op Lᴴ (splitPcg A L b x₀ j).2.2
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).p := by
  have hLu : IsUnit L.det := (isUnit_iff_isUnit_det L).1 hL
  have hLHu : IsUnit (Lᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact hLu.star
  have hinv : ∀ y : 𝔼, op (Lᴴ)⁻¹ (op Lᴴ y) = y := fun y => by
    have h1 : op (Lᴴ)⁻¹ ∘ₗ op Lᴴ = LinearMap.id := by
      rw [← op_mul, Matrix.nonsing_inv_mul _ hLHu]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 y
  have hinv' : ∀ y : 𝔼, op Lᴴ (op (Lᴴ)⁻¹ y) = y := fun y => by
    have h1 : op Lᴴ ∘ₗ op (Lᴴ)⁻¹ = LinearMap.id := by
      rw [← op_mul, Matrix.mul_nonsing_inv _ hLHu]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 y
  -- `Â` applied to `Lᴴ p` is `L⁻¹ (A p)`
  have hAhat : ∀ p : 𝔼, op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ p) = op L⁻¹ (op A p) := fun p => by
    rw [op_mul_apply, op_mul_apply, hinv]
  -- the two quadratic forms agree
  have hquad : ∀ p : 𝔼, inner 𝕜 (op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ p)) (op Lᴴ p)
      = inner 𝕜 p (op A p) := fun p => by
    have hc : (((L : Matrix (Fin n) (Fin n) 𝕜)⁻¹)ᴴ) = (Lᴴ)⁻¹ :=
      Matrix.conjTranspose_nonsing_inv L
    rw [hAhat, Chapter07.inner_op_conjTranspose, hc, hinv, hA]
  induction j with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · change op L⁻¹ (b - op A x₀) = op L⁻¹ b - op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ x₀)
      rw [hAhat, map_sub]
    · change op Lᴴ (op (Lᴴ)⁻¹ (op L⁻¹ (b - op A x₀)))
        = op L⁻¹ b - op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ x₀)
      rw [hinv', hAhat, map_sub]
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : splitPcgStepAlpha A (splitPcg A L b x₀ j)
        = CG.alpha (op (L⁻¹ * A * (Lᴴ)⁻¹))
          (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j) := by
      rw [splitPcgStepAlpha, CG.alpha, hr, ← hp, hquad]
    have hr' : splitPcgStepR A L (splitPcg A L b x₀ j)
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) (j + 1)).r := by
      rw [splitPcgStepR, CG.iterate_succ_r, ← halpha, hr, ← hp, hAhat]
    have hbeta : splitPcgStepBeta A L (splitPcg A L b x₀ j)
        = CG.beta (op (L⁻¹ * A * (Lᴴ)⁻¹))
          (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j) := by
      rw [splitPcgStepBeta, CG.beta_iterate, hr', hr]
    refine ⟨?_, ?_, ?_⟩
    · rw [splitPcg_succ, splitPcgStep, CG.iterate_succ_x, map_add, map_smul, hx, hp, halpha]
    · rw [splitPcg_succ, splitPcgStep]
      exact hr'
    · rw [splitPcg_succ, splitPcgStep, CG.iterate_succ_p, map_add, map_smul, hinv', hr', hp,
        hbeta]

/-! ### Section 9.2.1, closing paragraph: right preconditioning in the $M^{-1}$-inner product -/

variable (A M)

/-- The step length $\alpha_j = (\rho_j, M^{-1} \rho_j)/(q_j, M^{-1} A M^{-1} q_j)$ of the conjugate
gradient method for the right-preconditioned system $A M^{-1} u = b$ in the $M^{-1}$-inner
product $(x, y)_{M^{-1}} = (M^{-1} x, y)$, on a state $(u_j, \rho_j, q_j)$.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
noncomputable def rightPcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 (op M⁻¹ (op A (op M⁻¹ s.2.2))) s.2.2

/-- The next residual $\rho_{j+1} = \rho_j - \alpha_j A M^{-1} q_j$ of the right-preconditioned
conjugate gradient method.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
noncomputable def rightPcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - rightPcgStepAlpha A M s • op A (op M⁻¹ s.2.2)

/-- The coefficient $\beta_j = (\rho_{j+1}, M^{-1} \rho_{j+1})/(\rho_j, M^{-1} \rho_j)$ of the
right-preconditioned conjugate gradient method, that is, $(\rho_{j+1},
\rho_{j+1})_{M^{-1}}/(\rho_j, \rho_j)_{M^{-1}}$ when $M^{-1}$ is symmetric.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
noncomputable def rightPcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ (rightPcgStepR A M s)) (rightPcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1

/-- One step of the conjugate gradient method for $A M^{-1} u = b$ in the $M^{-1}$-inner product. It
maps the state $(u_j, \rho_j, q_j)$ to $(u_j + \alpha_j q_j, \; \rho_{j+1}, \; \rho_{j+1} +
\beta_j q_j)$.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
noncomputable def rightPcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + rightPcgStepAlpha A M s • s.2.2, rightPcgStepR A M s,
    rightPcgStepR A M s + rightPcgStepBeta A M s • s.2.2)

/-- **Section 9.2.1** of [saad2003iterative], right preconditioning. Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, u_0 \in \mathbb{K}^n$. The conjugate gradient method
for the right-preconditioned system $A M^{-1} u = b$ in the $M^{-1}$-inner product starts from
$\rho_0 = q_0 = b - A M^{-1} u_0$ and computes, for $j = 0, 1, \ldots$,
$$\alpha_j = \frac{(\rho_j, M^{-1} \rho_j)}{(q_j, M^{-1} A M^{-1} q_j)}, \quad u_{j+1} = u_j +
  \alpha_j q_j, \quad \rho_{j+1} = \rho_j - \alpha_j A M^{-1} q_j,$$
$$\beta_j = \frac{(\rho_{j+1}, M^{-1} \rho_{j+1})}{(\rho_j, M^{-1} \rho_j)}, \quad q_{j+1} =
  \rho_{j+1} + \beta_j q_j.$$
The value at $j$ is the triple $(u_j, \rho_j, q_j)$ after $j$ steps.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
noncomputable def rightPcg (b u₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (rightPcgStep A M)^[j] (u₀, b - op A (op M⁻¹ u₀), b - op A (op M⁻¹ u₀))

/-- The state of the right-preconditioned conjugate gradient method after $j + 1$ steps is one step
applied to the state after $j$ steps.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
theorem rightPcg_succ (b u₀ : 𝔼) (j : ℕ) :
    rightPcg A M b u₀ (j + 1) = rightPcgStep A M (rightPcg A M b u₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

private theorem rightPcgStep_eq_pcgStep (hA : (op A).IsSymmetric)
    (hMinv : (op M⁻¹).IsSymmetric) (s : 𝔼 × 𝔼 × 𝔼) :
    (op M⁻¹ (rightPcgStep A M s).1, (rightPcgStep A M s).2.1, op M⁻¹ (rightPcgStep A M s).2.2)
      = pcgStep A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
  have halpha : rightPcgStepAlpha A M s = pcgStepAlpha A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepAlpha, pcgStepAlpha_def, hMinv (op A (op M⁻¹ s.2.2)) s.2.2, hA]
  have hr : rightPcgStepR A M s = pcgStepR A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepR, pcgStepR_def, halpha]
  have hbeta : rightPcgStepBeta A M s
      = pcgStepBeta A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepBeta, pcgStepBeta_def, hr]
  rw [rightPcgStep, pcgStep, halpha, hr, hbeta]
  exact congrArg₂ (fun a c => (a, pcgStepR A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2), c))
    (map_add _ _ _ |>.trans (by rw [map_smul])) (map_add _ _ _ |>.trans (by rw [map_smul]))

/-- **Section 9.2.1** of [saad2003iterative], closing paragraph. Let
$A, M \in \mathbb{K}^{n \times n}$ with $A$ and $M^{-1}$ symmetric. Let $(u_j, \rho_j, q_j)$ be
the state of the right-preconditioned conjugate gradient method in the $M^{-1}$-inner product,
started at $u_0$. Then $(M^{-1} u_j, \rho_j, M^{-1} q_j)$ is the state $(x_j, r_j, p_j)$ of
Algorithm 9.1 started at $x_0 = M^{-1} u_0$, for all $j$.

So in the variables $x = M^{-1} u$ and $p = M^{-1} q$ the right-preconditioned method is
Algorithm 9.1. Left preconditioning in the $M$-inner product and right preconditioning in the
$M^{-1}$-inner product are the same method.

**Generalization.** The recurrence is stated in the transformed coordinate and uses total operations
over complex scalars. State equivalence uses symmetry of $A$ and $M^{-1}$ without the SPD
assumptions of the source derivation.
-/
theorem rightPcg_eq_pcg (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b u₀ : 𝔼)
    (j : ℕ) :
    (op M⁻¹ (rightPcg A M b u₀ j).1, (rightPcg A M b u₀ j).2.1,
        op M⁻¹ (rightPcg A M b u₀ j).2.2) = pcg A M b (op M⁻¹ u₀) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rightPcg_succ, pcg_succ, ← ih, rightPcgStep_eq_pcgStep hA hMinv]

/-! ### Problem P-9.2: Algorithm 9.1 in the $A$-inner product -/

variable (A M)

/-- The step length $\alpha_j = (z_j, A z_j)/(p_j, A M^{-1} A p_j)$ of
`SaadSparse.Chapter09.pcgEnergyA`, on a state $(x_j, z_j, w_j, p_j, q_j)$ with $w_j = A z_j$ and
$q_j = A p_j$. It is computed as $(z_j, w_j)/(p_j, A M^{-1} q_j)$, so both $A$-inner products
are Euclidean ones and the denominator reuses the one matrix-vector product of the step.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyAStepAlpha (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.2.1 s.2.1 / inner 𝕜 (op A (op M⁻¹ s.2.2.2.2)) s.2.2.2.1

/-- The next preconditioned residual $z_{j+1} = z_j - \alpha_j M^{-1} q_j$ of
`SaadSparse.Chapter09.pcgEnergyA`, with $q_j = A p_j$.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyAStepZ (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - pcgEnergyAStepAlpha A M s • op M⁻¹ s.2.2.2.2

/-- The vector $w_{j+1} = w_j - \alpha_j A M^{-1} q_j$ of `SaadSparse.Chapter09.pcgEnergyA`, which
equals $A z_{j+1}$. It uses the single matrix-vector product of the step: $A$ is applied to
$M^{-1} q_j$ and to nothing else.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyAStepW (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.2.1 - pcgEnergyAStepAlpha A M s • op A (op M⁻¹ s.2.2.2.2)

/-- The coefficient $\beta_j = (z_{j+1}, w_{j+1})/(z_j, w_j)$ of `SaadSparse.Chapter09.pcgEnergyA`,
that is, $(A z_{j+1}, z_{j+1})/(A z_j, z_j)$ when $A$ is symmetric.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyAStepBeta (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (pcgEnergyAStepW A M s) (pcgEnergyAStepZ A M s) / inner 𝕜 s.2.2.1 s.2.1

/-- One step of **Problem P-9.2** of [saad2003iterative]: Algorithm 9.1 in the $A$-inner product. It
maps $(x_j, z_j, w_j, p_j, q_j)$ to
$$(x_j + \alpha_j p_j, \; z_{j+1}, \; w_{j+1}, \; z_{j+1} + \beta_j p_j, \; w_{j+1} + \beta_j
  q_j).$$
The state carries $w_j = A z_j$ and $q_j = A p_j$, so that the step applies $A$ once and
$M^{-1}$ once.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyAStep (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgEnergyAStepAlpha A M s • s.2.2.2.1, pcgEnergyAStepZ A M s, pcgEnergyAStepW A M s,
    pcgEnergyAStepZ A M s + pcgEnergyAStepBeta A M s • s.2.2.2.1,
    pcgEnergyAStepW A M s + pcgEnergyAStepBeta A M s • s.2.2.2.2)

/-- **Problem P-9.2** of [saad2003iterative]. Let $A, M \in \mathbb{K}^{n \times n}$ and
$b, x_0 \in \mathbb{K}^n$. The analogue of Algorithm 9.1 in the $A$-inner product starts from
$z_0 = p_0 = M^{-1}(b - A x_0)$, $w_0 = q_0 = A z_0$ and computes, for $j = 0, 1, \ldots$,
$$\alpha_j = \frac{(z_j, w_j)}{(p_j, A M^{-1} q_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  z_{j+1} = z_j - \alpha_j M^{-1} q_j, \quad w_{j+1} = w_j - \alpha_j A M^{-1} q_j,$$
$$\beta_j = \frac{(z_{j+1}, w_{j+1})}{(z_j, w_j)}, \quad p_{j+1} = z_{j+1} + \beta_j p_j, \quad
  q_{j+1} = w_{j+1} + \beta_j q_j.$$
The value at $j$ is the state $(x_j, z_j, w_j, p_j, q_j)$ after $j$ steps. The vectors $w_j$ and
$q_j$ equal $A z_j$ and $A p_j$ (see `SaadSparse.Chapter09.pcgEnergyA_eq`), so each step needs
one product with $A$.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
noncomputable def pcgEnergyA (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (pcgEnergyAStep A M)^[j] (x₀, op M⁻¹ (b - op A x₀), op A (op M⁻¹ (b - op A x₀)),
    op M⁻¹ (b - op A x₀), op A (op M⁻¹ (b - op A x₀)))

/-- The state of `SaadSparse.Chapter09.pcgEnergyA` after $j + 1$ steps is one step applied to the
state after $j$ steps.

**Reading.** The recurrence carries $Az_j$ and $Ap_j$ and expresses the updates in terms of the
common image $AM^{-1}(Ap_j)$. The noncomputable definitions state the algebraic recurrence without
an evaluation or cost model. They use total operations over complex scalars.
-/
theorem pcgEnergyA_succ (b x₀ : 𝔼) (j : ℕ) :
    pcgEnergyA A M b x₀ (j + 1) = pcgEnergyAStep A M (pcgEnergyA A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

/-- If the operators of $A$ and $M^{-1}$ are symmetric, then the operator of $A M^{-1} A$ is
symmetric. -/
theorem isSymmetric_op_mul_inv_mul (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) :
    (op (A * M⁻¹ * A)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [hA, hMinv]
  exact hA _ _

/-- **Problem P-9.2** of [saad2003iterative], the algorithm as a backbone recurrence. Let
$A, M \in \mathbb{K}^{n \times n}$ with $A^{-1}(Ay) = y$ for all $y$. Then for all $b, x_0$ and
all $j$, the state $(x_j, z_j, w_j, p_j, q_j)$ of `SaadSparse.Chapter09.pcgEnergyA` satisfies:
* $x_j$, $w_j$ and $p_j$ are the iterate, the residual and the search direction of the backbone
  preconditioned conjugate gradient recurrence for $A M^{-1} A x = A M^{-1} b$ with the
  preconditioner $A$, started at $x_0$;
* $w_j = A z_j$ and $q_j = A p_j$.

The recurrence is `Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j`. The
invariants $w_j = A z_j$ and $q_j = A p_j$ are kept by the recurrence, which is why one
matrix-vector product per step suffices.

**Reading.** Lean identifies the recurrence with PCG on the symmetric transformed system and derives
Galerkin orthogonality under explicit inversion, symmetry and coercivity assumptions.
-/
theorem pcgEnergyA_eq (hAinv : ∀ y : 𝔼, op A⁻¹ (op A y) = y)
    (b x₀ : 𝔼) (j : ℕ) :
    (pcgEnergyA A M b x₀ j).1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).x ∧
      (pcgEnergyA A M b x₀ j).2.2.1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).r ∧
      (pcgEnergyA A M b x₀ j).2.2.2.1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).p ∧
      (pcgEnergyA A M b x₀ j).2.2.1 = op A (pcgEnergyA A M b x₀ j).2.1 ∧
      (pcgEnergyA A M b x₀ j).2.2.2.2 = op A (pcgEnergyA A M b x₀ j).2.2.2.1 := by
  have hAhat : ∀ y : 𝔼, op (A * M⁻¹ * A) y = op A (op M⁻¹ (op A y)) := fun y => by
    simp only [op_mul_apply]
  have hbhat : op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀ = op A (op M⁻¹ (b - op A x₀)) := by
    rw [op_mul_apply, hAhat, ← map_sub, ← map_sub]
  induction j with
  | zero =>
    refine ⟨rfl, hbhat.symm, ?_, rfl, rfl⟩
    change op M⁻¹ (b - op A x₀) = op A⁻¹ (op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀)
    rw [hbhat, hAinv]
  | succ j ih =>
    obtain ⟨hx, hw, hp, hwz, hqp⟩ := ih
    set S := pcgEnergyA A M b x₀ j with hS
    set P := Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j with hP
    have hz : op A⁻¹ P.r = S.2.1 := by rw [← hw, hwz, hAinv]
    have halpha : pcgEnergyAStepAlpha A M S
        = Krylov.PCG.alpha (op (A * M⁻¹ * A)) (op A⁻¹) P := by
      rw [pcgEnergyAStepAlpha, Krylov.PCG.alpha, hz, hw, hAhat, ← hp, hqp]
    have hwnew : pcgEnergyAStepW A M S = op A (pcgEnergyAStepZ A M S) := by
      rw [pcgEnergyAStepW, pcgEnergyAStepZ, map_sub, map_smul, hwz]
    have hrnew : pcgEnergyAStepW A M S = (Krylov.PCG.step (op (A * M⁻¹ * A)) (op A⁻¹) P).r := by
      rw [pcgEnergyAStepW, Krylov.PCG.step_r, halpha, hw, hAhat, ← hp, hqp]
    have hznew : op A⁻¹ (Krylov.PCG.step (op (A * M⁻¹ * A)) (op A⁻¹) P).r
        = pcgEnergyAStepZ A M S := by rw [← hrnew, hwnew, hAinv]
    have hbeta : pcgEnergyAStepBeta A M S = Krylov.PCG.beta (op (A * M⁻¹ * A)) (op A⁻¹) P := by
      rw [pcgEnergyAStepBeta, Krylov.PCG.beta, hznew, hrnew, hz, hw]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ, Krylov.PCG.step_x, hx, hp,
        halpha]
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ]
      exact hrnew
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ, Krylov.PCG.step_p, hznew, hp,
        hbeta]
    · rw [pcgEnergyA_succ, pcgEnergyAStep]
      exact hwnew
    · rw [pcgEnergyA_succ, pcgEnergyAStep, hwnew, map_add, map_smul, hqp]

/-- **Problem P-9.2** of [saad2003iterative], the Galerkin property. Let
$A \in \mathbb{K}^{n \times n}$ be symmetric positive definite and nonsingular, with inverse
$A^{-1}$, let $M^{-1}$ be symmetric, and let $c\,(Ax, x) \le (A M^{-1} A x, x)$ for all $x$, for
some $c > 0$. Then for all $b, x_0$ and all $j$, the iterate $x_j$ of
`SaadSparse.Chapter09.pcgEnergyA` is the Galerkin iterate of $A M^{-1} A x = A M^{-1} b$ over
the space $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$ that Algorithm 9.1 searches, with
$r_0 = b - A x_0$.

Hence $x_j$ minimizes the $A M^{-1} A$-norm of the error over that space when $A M^{-1} A$ is
positive definite, and the algorithm is the preconditioned conjugate residual method. The
hypotheses on $A$ are `(op A).IsSymmetric`, `Krylov.IsPreconditioner (op A) (op A⁻¹)` and
`IsUnit A`.

**Reading.** Lean identifies the recurrence with PCG on the symmetric transformed system and derives
Galerkin orthogonality under explicit inversion, symmetry and coercivity assumptions.
-/
theorem pcgEnergyA_isGalerkinIterate (hA : (op A).IsSymmetric)
    (hAp : Krylov.IsPreconditioner (op A) (op A⁻¹)) (hAu : IsUnit A) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op A x) x)
      ≤ RCLike.re (inner 𝕜 (op (A * M⁻¹ * A) x) x))
    (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    IsGalerkin (op (A * M⁻¹ * A)) (op (A * M⁻¹) b) x₀
      (Chapter06.krylov (M⁻¹ * A) (op M⁻¹ (b - op A x₀)) j) (pcgEnergyA A M b x₀ j).1 := by
  have hAinv : ∀ y : 𝔼, op A⁻¹ (op A y) = y := hAp.inv_apply
  have hAhat : ∀ y : 𝔼, op (A * M⁻¹ * A) y = op A (op M⁻¹ (op A y)) := fun y => by
    simp only [op_mul_apply]
  have hspace : op A⁻¹ ∘ₗ op (A * M⁻¹ * A) = op (M⁻¹ * A) := by
    rw [← op_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hAu), Matrix.one_mul]
  have hres : op A⁻¹ (op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀) = op M⁻¹ (b - op A x₀) := by
    rw [op_mul_apply, hAhat, ← map_sub, ← map_sub, hAinv]
  have h := Krylov.PCG.isGalerkinIterate (A := op (A * M⁻¹ * A)) (Minv := op A⁻¹)
    (b := op (A * M⁻¹) b) (x₀ := x₀) hAp (isSymmetric_op_mul_inv_mul hA hMinv) hc hcoer j
  rw [hspace, hres] at h
  rw [(pcgEnergyA_eq hAinv b x₀ j).1, Chapter06.krylov_eq]
  exact h

/-! ### Problem P-9.12: the preconditioned conjugate residual method -/

section CRStep

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem crStep_x (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).x = s.x + CR.alpha B s • s.p := rfl

private theorem crStep_r (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).r = s.r - CR.alpha B s • s.q := rfl

private theorem crStep_p (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).p = (CR.step B s).r
      + (inner 𝕜 (CR.step B s).r (B (CR.step B s).r) / inner 𝕜 s.r (B s.r)) • s.p := rfl

private theorem crStep_q (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).q = B (CR.step B s).r
      + (inner 𝕜 (CR.step B s).r (B (CR.step B s).r) / inner 𝕜 s.r (B s.r)) • s.q := rfl

end CRStep

variable (A M)

/-- The step length $\alpha_j = (A z_j, z_j)/(q_j, M^{-1} q_j)$ of the preconditioned conjugate
residual method (Problem P-9.12 of [saad2003iterative]), on a state $(x_j, z_j, p_j, q_j)$ with
$q_j = A p_j$. As in Algorithm 9.1, both $M$-inner products of the underlying method are
Euclidean ones: $(M^{-1} A z_j, z_j)_M = (A z_j, z_j)$ and $(M^{-1} A p_j, M^{-1} A p_j)_M = (A
p_j, M^{-1} A p_j)$.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
noncomputable def pcrStepAlpha (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 (op A s.2.1) / inner 𝕜 (op M⁻¹ s.2.2.2) s.2.2.2

/-- The next preconditioned residual $z_{j+1} = z_j - \alpha_j M^{-1} q_j$ of Problem P-9.12 of
[saad2003iterative].

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
noncomputable def pcrStepZ (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - pcrStepAlpha A M s • op M⁻¹ s.2.2.2

/-- The coefficient $\beta_j = (A z_{j+1}, z_{j+1})/(A z_j, z_j)$ of Problem P-9.12 of
[saad2003iterative].

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
noncomputable def pcrStepBeta (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (pcrStepZ A M s) (op A (pcrStepZ A M s)) / inner 𝕜 s.2.1 (op A s.2.1)

/-- One step of **Problem P-9.12** of [saad2003iterative], the analogue of Algorithm 9.1 for the
conjugate residual method. It maps $(x_j, z_j, p_j, q_j)$ to
$$(x_j + \alpha_j p_j, \; z_{j+1}, \; z_{j+1} + \beta_j p_j, \; A z_{j+1} + \beta_j q_j).$$
It applies $A$ once, to the new preconditioned residual, and $M^{-1}$ once, to $q_j = A p_j$.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
noncomputable def pcrStep (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcrStepAlpha A M s • s.2.2.1, pcrStepZ A M s,
    pcrStepZ A M s + pcrStepBeta A M s • s.2.2.1,
    op A (pcrStepZ A M s) + pcrStepBeta A M s • s.2.2.2)

/-- **Problem P-9.12** of [saad2003iterative] (preconditioned conjugate residual). Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. Start from
$z_0 = p_0 = M^{-1}(b - A x_0)$ and $q_0 = A p_0$, and compute, for $j = 0, 1, \ldots$,
$$\alpha_j = \frac{(A z_j, z_j)}{(q_j, M^{-1} q_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  z_{j+1} = z_j - \alpha_j M^{-1} q_j,$$
$$\beta_j = \frac{(A z_{j+1}, z_{j+1})}{(A z_j, z_j)}, \quad p_{j+1} = z_{j+1} + \beta_j p_j,
  \quad q_{j+1} = A z_{j+1} + \beta_j q_j.$$
The value at $j$ is the state $(x_j, z_j, p_j, q_j)$ after $j$ steps.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
noncomputable def pcr (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (pcrStep A M)^[j] (x₀, op M⁻¹ (b - op A x₀), op M⁻¹ (b - op A x₀),
    op A (op M⁻¹ (b - op A x₀)))

/-- The state of Problem P-9.12 after $j + 1$ steps is one step applied to the state after $j$
steps.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
theorem pcr_succ (b x₀ : 𝔼) (j : ℕ) : pcr A M b x₀ (j + 1) = pcrStep A M (pcr A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

/-- **Problem P-9.12** of [saad2003iterative], the method as a backbone recurrence. Let $M$ be a
preconditioner and $A \in \mathbb{K}^{n \times n}$. Let $(\xi_j, \rho_j, \pi_j, \sigma_j)$ be
the iterate, the residual, the direction and the vector $B \pi_j$ of the backbone conjugate
residual recurrence for the operator $B = M^{-1} A$ on the space with the $M$-inner product,
with right-hand side $M^{-1} b$ and initial guess $x_0$. Then the state $(x_j, z_j, p_j, q_j)$
of `SaadSparse.Chapter09.pcr` satisfies, for all $j$,
$$x_j = \xi_j, \qquad z_j = \rho_j, \qquad p_j = \pi_j, \qquad M^{-1} q_j = \sigma_j.$$

This is the same reading as `SaadSparse.Chapter09.pcg_eq` for Algorithm 9.1. The recurrence is
`CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A))`, and each vector is moved to the $M$-inner product
space by `hM.toEnergy`.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
theorem pcr_eq (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (b x₀ : 𝔼) (j : ℕ) :
    hM.toEnergy (pcr A M b x₀ j).1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).x ∧
      hM.toEnergy (pcr A M b x₀ j).2.1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).r ∧
      hM.toEnergy (pcr A M b x₀ j).2.2.1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).p ∧
      hM.toEnergy (op M⁻¹ (pcr A M b x₀ j).2.2.2)
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).q := by
  set Ahat := hM.energyEnd (op M⁻¹ ∘ₗ op A) with hAhat
  have hstep : ∀ y : 𝔼, Ahat (hM.toEnergy y) = hM.toEnergy (op M⁻¹ (op A y)) := fun _ => rfl
  have hinit : hM.toEnergy (op M⁻¹ (b - op A x₀))
      = hM.toEnergy (op M⁻¹ b) - Ahat (hM.toEnergy x₀) := by
    rw [hstep, ← map_sub, ← map_sub]
  induction j with
  | zero =>
    refine ⟨rfl, hinit, hinit, ?_⟩
    change hM.toEnergy (op M⁻¹ (op A (op M⁻¹ (b - op A x₀))))
      = Ahat (hM.toEnergy (op M⁻¹ b) - Ahat (hM.toEnergy x₀))
    rw [← hinit, hstep]
  | succ j ih =>
    obtain ⟨hx, hr, hp, hq⟩ := ih
    set S := pcr A M b x₀ j with hS
    set C := CR.iterate Ahat (hM.toEnergy (op M⁻¹ b)) (hM.toEnergy x₀) j with hC
    have hnum : inner 𝕜 C.r (Ahat C.r) = inner 𝕜 S.2.1 (op A S.2.1) := by
      rw [← hr]
      exact hM.inner_energyEnd_right (op A) S.2.1 S.2.1
    have hden : inner 𝕜 C.q C.q = inner 𝕜 (op M⁻¹ S.2.2.2) S.2.2.2 := by
      rw [← hq, hM.inner_toEnergy_inv]
    have halpha : CR.alpha Ahat C = pcrStepAlpha A M S := by
      rw [CR.alpha, pcrStepAlpha, hnum, hden]
    have hznew : hM.toEnergy (pcrStepZ A M S) = (CR.step Ahat C).r := by
      rw [crStep_r, halpha, pcrStepZ, map_sub, map_smul, hr, hq]
    have hnum' : inner 𝕜 (CR.step Ahat C).r (Ahat (CR.step Ahat C).r)
        = inner 𝕜 (pcrStepZ A M S) (op A (pcrStepZ A M S)) := by
      rw [← hznew]
      exact hM.inner_energyEnd_right (op A) (pcrStepZ A M S) (pcrStepZ A M S)
    have hbeta : inner 𝕜 (CR.step Ahat C).r (Ahat (CR.step Ahat C).r) / inner 𝕜 C.r (Ahat C.r)
        = pcrStepBeta A M S := by
      rw [pcrStepBeta, hnum, hnum']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_x, map_add, map_smul, hx, hp,
        halpha]
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC]
      exact hznew
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_p, map_add, map_smul, hznew, hp,
        hbeta]
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_q, map_add, map_add, map_smul,
        map_smul, ← hstep, hznew, hq, hbeta]

/-- **Problem P-9.12** of [saad2003iterative]. Let $M$ be a preconditioner. Then the second
component of the state of `SaadSparse.Chapter09.pcr` is the preconditioned true residual:
$z_j = M^{-1}(b - A x_j)$. So the stopping test of Algorithm 9.1 reads the same way here.

**Generalization.** The recurrence is conjugate residual in the preconditioner energy inner product,
storing the preconditioned residual and unpreconditioned image of the search direction. The formulas
are total and accept complex data; the identification with energy-space CR assumes a valid
preconditioner.
-/
theorem pcr_residual_eq (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (b x₀ : 𝔼) (j : ℕ) :
    (pcr A M b x₀ j).2.1 = op M⁻¹ (b - op A (pcr A M b x₀ j).1) := by
  obtain ⟨hx, hr, -, -⟩ := pcr_eq hM b x₀ j
  refine (hM.toEnergy).injective ?_
  rw [hr, CR.residual_eq, ← hx, Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply,
    ← map_sub, ← map_sub]

/-! ### Section 9.2.2: the preconditioned product when $M = A - R$ -/

/-- **Section 9.2.2** of [saad2003iterative], opening paragraph. Let
$A, M, R \in \mathbb{K}^{n \times n}$ with $M$ nonsingular and $M = A - R$. Then for every $v$,
$$M^{-1} A v = v + M^{-1} R v.$$

Applying the left-preconditioned matrix therefore costs one solve with $M$ and one product with
$R$. This is the general form of the rearrangement that `SaadSparse.Chapter09.equation_9_8`
performs for the SSOR-type preconditioner, and the reason for storing an incomplete
factorization together with the entries it dropped. The left-preconditioned matrix is
`SaadSparse.Chapter09.leftPreconditioned`. -/
theorem leftPreconditioned_apply_eq_add {R : Matrix (Fin n) (Fin n) 𝕜} (hM : IsUnit M)
    (hR : M = A - R) (v : 𝔼) :
    op (leftPreconditioned M A) v = v + op M⁻¹ (op R v) := by
  have hA : A = M + R := by rw [hR]; abel
  have hmat : leftPreconditioned M A = 1 + M⁻¹ * R := by
    rw [show leftPreconditioned M A = M⁻¹ * A from rfl, hA, Matrix.mul_add,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).1 hM)]
  have hadd : op (1 + M⁻¹ * R) v = op (1 : Matrix (Fin n) (Fin n) 𝕜) v + op (M⁻¹ * R) v := by
    rw [show (op (1 + M⁻¹ * R) : 𝔼 →ₗ[𝕜] 𝔼) = op 1 + op (M⁻¹ * R) from map_add _ _ _]
    rfl
  have hone : op (1 : Matrix (Fin n) (Fin n) 𝕜) v = v := by
    rw [show (op (1 : Matrix (Fin n) (Fin n) 𝕜) : 𝔼 →ₗ[𝕜] 𝔼) = LinearMap.id from
      Matrix.toEuclideanLin_one]
    rfl
  rw [hmat, hadd, op_mul_apply, hone]

end General

/-! ### Section 9.2.2: Eisenstat's implementation -/

section Eisenstat

variable {n : ℕ} {A D : Matrix (Fin n) (Fin n) ℝ}

/-- For a symmetric real matrix $A$, the strict upper part $F$ of the splitting (4.2) is the
transpose of the strict lower part $E$: $E^T = F$. -/
theorem transpose_E (hA : A.IsSymm) : (Chapter04.E A)ᵀ = Chapter04.F A := by
  ext i j
  have hsym : A j i = A i j := congrFun (congrFun hA i) j
  simp [Chapter04.E, Chapter04.F, Matrix.strictLower_apply, Matrix.strictUpper_apply, hsym]

/-- **Section 9.2.2** of [saad2003iterative], the splitting of a symmetric matrix. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then
$$A = D_0 - E - E^T,$$
where $D_0$ is the diagonal of $A$ and $-E$ is its strict lower triangular part.

The matrices $D_0$ and $E$ are `SaadSparse.Chapter04.D A` and `SaadSparse.Chapter04.E A`, from
the splitting (4.2). -/
theorem decomp_symm (hA : A.IsSymm) : A = Chapter04.D A - Chapter04.E A - (Chapter04.E A)ᵀ := by
  rw [transpose_E hA]
  exact Chapter04.decomp A

/-- If $X = Y + B + C$ with $B^{-1} B = I$ and $C C^{-1} = I$, then $B^{-1} X C^{-1} = B^{-1} Y
C^{-1} + B^{-1} + C^{-1}$; this is the algebra behind (9.8). -/
private theorem inv_mul_mul_inv_eq {X Y B C : Matrix (Fin n) (Fin n) ℝ} (hB : B⁻¹ * B = 1)
    (hC : C * C⁻¹ = 1) (h : X = Y + B + C) :
    B⁻¹ * X * C⁻¹ = B⁻¹ * Y * C⁻¹ + B⁻¹ + C⁻¹ := by
  rw [h, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hB, Matrix.one_mul,
    Matrix.mul_assoc B⁻¹ C C⁻¹, hC, Matrix.mul_one]
  abel

/-- **Equation (9.8)** of [saad2003iterative], with (9.5)–(9.7). Let $A \in \mathbb{R}^{n \times n}$
be symmetric with the splitting $A = D_0 - E - E^T$, and let $D \in \mathbb{R}^{n \times n}$ be
such that $D - E$ and $D - E^T$ are nonsingular. Then the split-preconditioned matrix
$\hat A = (D - E)^{-1} A (D - E^T)^{-1}$ of the preconditioner $M = (D - E) D^{-1} (D - E^T)$
satisfies
$$\hat A = (D - E)^{-1} D_1 (D - E^T)^{-1} + (D - E)^{-1} + (D - E^T)^{-1}, \qquad D_1 = D_0 -
  2D.$$

This identity is the content of Eisenstat's implementation: $\hat A v$ costs one product with
the diagonal matrix $D_1$ and the two triangular solves that applying $M^{-1}$ needs anyway. The
statement holds for any matrix $D$ with these two invertibility conditions; the book takes $D$
diagonal.

**Generalization.** The inverse-sum identity holds for arbitrary $D$ with both indicated factors
invertible. The source takes $D$ diagonal.
-/
theorem equation_9_8 (hA : A.IsSymm) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) :
    (D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹
      = (D - Chapter04.E A)⁻¹ * (Chapter04.D A - (2 : ℝ) • D) * (D - (Chapter04.E A)ᵀ)⁻¹
        + (D - Chapter04.E A)⁻¹ + (D - (Chapter04.E A)ᵀ)⁻¹ := by
  refine inv_mul_mul_inv_eq (Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h1))
    (Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 h2)) ?_
  conv_lhs => rw [decomp_symm hA]
  module

open Chapter06 (op)

/-- **Algorithm 9.3** of [saad2003iterative] (Eisenstat's implementation). Let
$A, D \in \mathbb{R}^{n \times n}$, with $A = D_0 - E - F$ the splitting (4.2), and let
$v \in \mathbb{R}^n$. Compute
$$z = (D - E^T)^{-1} v, \qquad w = (D - E)^{-1} (v + D_1 z) + z, \qquad D_1 = D_0 - 2D.$$
The value is $w$.

This is the procedure that Section 9.2.2 states just before Algorithm 9.3. The printed algorithm
is its rescaling by $D^{-1}$, which saves one product with the diagonal and computes the same
vector $\hat A v$.

**Reading.** Lean uses the three-operation formula preceding the algorithm. The printed Algorithm
9.3 further rescales by $D^{-1}$ to save a diagonal operation. Lean proves equality of the product
under the factor invertibility conditions and uses totalized inverses in its definition.
-/
noncomputable def eisenstat (A D : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  let z := op (D - (Chapter04.E A)ᵀ)⁻¹ v
  op (D - Chapter04.E A)⁻¹ (v + op (Chapter04.D A - (2 : ℝ) • D) z) + z

/-- The value of `SaadSparse.Chapter09.eisenstat` at $v$ is $(D - E)^{-1}(v + D_1 (D - E^T)^{-1}
v) + (D - E^T)^{-1} v$, with $D_1 = D_0 - 2D$.

**Reading.** Lean uses the three-operation formula preceding the algorithm. The printed Algorithm
9.3 further rescales by $D^{-1}$ to save a diagonal operation. Lean proves equality of the product
under the factor invertibility conditions and uses totalized inverses in its definition.
-/
theorem eisenstat_def (A D : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    eisenstat A D v = op (D - Chapter04.E A)⁻¹
        (v + op (Chapter04.D A - (2 : ℝ) • D) (op (D - (Chapter04.E A)ᵀ)⁻¹ v))
      + op (D - (Chapter04.E A)ᵀ)⁻¹ v := rfl

/-- The operator of a sum of matrices is the sum of the operators. -/
private theorem op_add_apply (X Y : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : op (X + Y) v = op X v + op Y v := by
  have h : (op (X + Y) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      = op X + op Y := map_add _ _ _
  rw [h]
  rfl

/-- **Algorithm 9.3** of [saad2003iterative], correctness. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, and let $D \in \mathbb{R}^{n \times n}$ be such that $D - E$ and $D - E^T$ are
nonsingular. Then for every $v$, Eisenstat's implementation returns
$$(D - E)^{-1} A (D - E^T)^{-1} v = \hat A v,$$
the product with the matrix $\hat A$ of (9.8). It uses two triangular solves and one product
with the diagonal $D_1$, and no product with $A$.

**Reading.** Lean uses the three-operation formula preceding the algorithm. The printed Algorithm
9.3 further rescales by $D^{-1}$ to save a diagonal operation. Lean proves equality of the product
under the factor invertibility conditions and uses totalized inverses in its definition.
-/
theorem eisenstat_eq (hA : A.IsSymm) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) (v : EuclideanSpace ℝ (Fin n)) :
    eisenstat A D v = op ((D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹) v := by
  rw [equation_9_8 hA h1 h2, op_add_apply, op_add_apply, eisenstat_def, map_add,
    op_mul_apply, op_mul_apply]
  abel

/-!
### Problem P-9.8(c): the split-preconditioning option

The problem scales the system symmetrically by the square root of the diagonal $D$ of (9.6). With
$C = D^{1/2} \hat A D^{1/2}$ and $\hat E = D^{-1/2} E D^{-1/2}$, it asks for a matrix $D_2$ with
$C = (I - \hat E)^{-1} D_2 (I - \hat E)^{-T} + (I - \hat E)^{-1} + (I - \hat E)^{-T}$. The answer is
$D_2 = D^{-1/2} D_1 D^{-1/2}$ for the matrix $D_1 = D_0 - 2D$ of (9.8). For the SSOR choice
$D = D_0$ it is $-I$: after the scaling the triangular factors have a unit diagonal, and no diagonal
has to be stored.

The results below use only that the matrix $S$ that stands for $D^{1/2}$ is symmetric, nonsingular
and satisfies $S^2 = D$; they do not use that it is diagonal. For a positive diagonal
$D = \operatorname{diag}(d)$ the intended matrix is $\operatorname{diag}(\sqrt{d_i})$.
-/

section Sqrt

variable {S : Matrix (Fin n) (Fin n) ℝ} (hSu : IsUnit S) (hSD : S * S = D)

include hSu hSD in
/-- If $S$ is nonsingular and $S^2 = D$, then $S^{-1} D S^{-1} = I$. -/
private theorem inv_mul_self_mul_inv : S⁻¹ * D * S⁻¹ = 1 := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  rw [← hSD, ← Matrix.mul_assoc S⁻¹ S S, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

include hSu hSD in
/-- If $S$ is nonsingular and $S^2 = D$, then $(I - S^{-1} X S^{-1})^{-1} = S (D - X)^{-1} S$; this
scaling turns a triangular factor $D - X$ of (9.6) into one with a unit diagonal. -/
private theorem inv_one_sub_conj (X : Matrix (Fin n) (Fin n) ℝ) :
    (1 - S⁻¹ * X * S⁻¹)⁻¹ = S * (D - X)⁻¹ * S := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  have hconj : 1 - S⁻¹ * X * S⁻¹ = S⁻¹ * (D - X) * S⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, inv_mul_self_mul_inv hSu hSD]
  rw [hconj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu,
    ← Matrix.mul_assoc]

end Sqrt

/-- **Problem P-9.8(c)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
with $A = D_0 - E - E^T$, let $D \in \mathbb{R}^{n \times n}$ be such that $D - E$ and $D - E^T$
are nonsingular, and let $S$ be a symmetric nonsingular matrix with $S^2 = D$, which stands for
$D^{1/2}$. Put $\hat E = S^{-1} E S^{-1}$ and let $C = S \hat A S$, with
$\hat A = (D - E)^{-1} A (D - E^T)^{-1}$; $C$ is the matrix that the conjugate gradient method
is applied to in the split-preconditioning option. Then
$$C = (I - \hat E)^{-1} D_2 (I - \hat E)^{-T} + (I - \hat E)^{-1} + (I - \hat E)^{-T}, \qquad
  D_2 = S^{-1} (D_0 - 2D) S^{-1}.$$

The matrix $D_2$ is the conjugate of the matrix $D_1$ of `SaadSparse.Chapter09.equation_9_8`.
After the scaling, the two triangular factors are transposes of each other and have a unit
diagonal, which is the point of the exercise. The matrix $(I - \hat E)^{-T}$ is
`((1 - S⁻¹ * E * S⁻¹)ᵀ)⁻¹`.

**Reading.** The formula takes a symmetric invertible square root as input, with no diagonal
restriction, and identifies the middle factor. The SSOR specialization gives the negative identity.
The procedure and operation-count comparison requested by the exercise are outside these statements.
-/
theorem problem_9_8c {S : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hSs : S.IsSymm)
    (hSu : IsUnit S) (hSD : S * S = D) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) :
    S * ((D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹) * S
      = (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹
          * (S⁻¹ * (Chapter04.D A - (2 : ℝ) • D) * S⁻¹)
          * ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹
        + (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹ + ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹ := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  have hinvSymm : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSs.eq]
  -- the transposed factor is the conjugate of `D - Eᵀ`
  have htr : ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹ = S * (D - (Chapter04.E A)ᵀ)⁻¹ * S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
      hinvSymm, ← Matrix.mul_assoc S⁻¹ (Chapter04.E A)ᵀ S⁻¹, inv_one_sub_conj hSu hSD]
  have hfst : (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹ = S * (D - Chapter04.E A)⁻¹ * S :=
    inv_one_sub_conj hSu hSD _
  -- the middle term reassembles after cancelling `D^{1/2} D^{-1/2}` on both sides
  have hmid : ∀ X Y Z : Matrix (Fin n) (Fin n) ℝ,
      S * X * S * (S⁻¹ * Y * S⁻¹) * (S * Z * S) = S * (X * Y * Z) * S := fun X Y Z => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S (Z * S), Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
      ← Matrix.mul_assoc S S⁻¹ (Y * (Z * S)), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [hfst, htr, hmid, equation_9_8 hA h1 h2]
  simp only [Matrix.mul_add, Matrix.add_mul]

/-- **Problem P-9.8(c)** of [saad2003iterative], the SSOR case $D = D_0$. Let $S$ be nonsingular
with $S^2 = D_0$. Then
$$S^{-1} (D_0 - 2 D_0) S^{-1} = -I.$$
So the matrix $D_2$ of `SaadSparse.Chapter09.problem_9_8c` is $-I$, the scaled identity reads
$C = -(I - \hat E)^{-1} (I - \hat E)^{-T} + (I - \hat E)^{-1} + (I - \hat E)^{-T}$, and no
diagonal remains.

**Reading.** The formula takes a symmetric invertible square root as input, with no diagonal
restriction, and identifies the middle factor. The SSOR specialization gives the negative identity.
The procedure and operation-count comparison requested by the exercise are outside these statements.
-/
theorem problem_9_8c_ssor {S : Matrix (Fin n) (Fin n) ℝ} (hSu : IsUnit S)
    (hSD : S * S = Chapter04.D A) :
    S⁻¹ * (Chapter04.D A - (2 : ℝ) • Chapter04.D A) * S⁻¹ = -1 := by
  have h : Chapter04.D A - (2 : ℝ) • Chapter04.D A = -Chapter04.D A := by module
  rw [h, Matrix.mul_neg, Matrix.neg_mul, inv_mul_self_mul_inv hSu hSD]

/-- **Example 9.1** of [saad2003iterative]. Let $n > 0$ and $N_z = 5n$, the number of nonzeros of a
five-point finite difference matrix. Then
$$4 N_z - n = 19n, \qquad 3n + 2 N_z = 13n, \qquad (4 N_z - n) - (3n + 2 N_z) = 6n, \qquad
  \frac{(4 N_z - n) - (3n + 2 N_z)}{4 N_z - n} = \frac{6}{19},$$
$$(4 N_z - n) + 10n = 29n, \qquad (3n + 2 N_z) + 10n = 23n.$$

Section 9.2.2 counts $4 N_z(A) - n$ additions and multiplications for the straightforward
preconditioned product and $3n + 2 N_z(A)$ for Algorithm 9.3. At $N_z(A) = 5n$ these are $19n$
against $13n$, a saving of $6n$; this is the ratio $6/19$ that the book calls "about $1/3$".
With the remaining $10n$ operations of a conjugate gradient step, the counts are $29n$ against
$23n$.

This is arithmetic on the two counts of the book, not a statement about the algorithms. The
library does not count operations, so the counts are hypotheses of the statement, and neither
`SaadSparse.Chapter09.eisenstat` nor `SaadSparse.Chapter09.pcg` appears in it. The numbers $n$
and $N_z$ are real.

**Reading.** The theorem checks arithmetic for an exact input count $N_z=5n$, over real numbers. The
source uses $5n$ as an approximate stencil count. Lean does not prove the operation-count formulas
or model a stencil implementation.
-/
theorem example_9_1 {n Nz : ℝ} (hn : 0 < n) (hNz : Nz = 5 * n) :
    4 * Nz - n = 19 * n ∧
      3 * n + 2 * Nz = 13 * n ∧
      (4 * Nz - n) - (3 * n + 2 * Nz) = 6 * n ∧
      ((4 * Nz - n) - (3 * n + 2 * Nz)) / (4 * Nz - n) = 6 / 19 ∧
      (4 * Nz - n) + 10 * n = 29 * n ∧
      (3 * n + 2 * Nz) + 10 * n = 23 * n := by
  subst hNz
  refine ⟨by ring, by ring, by ring, ?_, by ring, by ring⟩
  rw [show 4 * (5 * n) - n - (3 * n + 2 * (5 * n)) = 6 * n by ring,
    show 4 * (5 * n) - n = 19 * n by ring]
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  ring

end Eisenstat

end SaadSparse.Chapter09
