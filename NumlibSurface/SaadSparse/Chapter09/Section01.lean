/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 9.1: Left, right and split preconditioning

This module formalizes Section 9.1 of [saad2003iterative], together with Problems P-9.1 and P-9.10.
A preconditioner is a nonsingular matrix $M$ that approximates $A$ and for which the system $Mz = r$
is cheap to solve. It can be applied on the left (9.1), on the right (9.2), or, when it is given in
factored form $M = M_L M_R$, split between the two sides (9.3). The three preconditioned matrices
are $M^{-1} A$, $A M^{-1}$ and $M_L^{-1} A M_R^{-1}$.

Each of the three preconditioned systems has exactly the solutions of $Ax = b$, after the changes of
variables $u = Mx$ (right) and $u = M_R x$ (split). The three preconditioned matrices are conjugate
to one another, so they have the same characteristic polynomial and the same spectrum. This is the
reason of the chapter for expecting the three options to behave alike; Section 9.3.4 shows that they
nevertheless minimize different quantities. The proofs are direct matrix algebra.

## Main definitions

* Equation (9.1), `SaadSparse.Chapter09.leftPreconditioned`: the left-preconditioned matrix
  $M^{-1} A$.
* Equation (9.2), `SaadSparse.Chapter09.rightPreconditioned`: the right-preconditioned matrix
  $A M^{-1}$.
* Equation (9.3), `SaadSparse.Chapter09.splitPreconditioned`: the split-preconditioned matrix
  $M_L^{-1} A M_R^{-1}$.

## Main results

* Section 9.1, `SaadSparse.Chapter09.solution_iff`: the three preconditioned systems are equivalent
  to $Ax = b$.
* Problems P-9.1 and P-9.10, `SaadSparse.Chapter09.problem_9_1`: the three preconditioned matrices
  are conjugate.
* Problems P-9.1 and P-9.10, `SaadSparse.Chapter09.problem_9_1_charpoly`: the three preconditioned
  matrices have the same characteristic polynomial.
* Problems P-9.1 and P-9.10, `SaadSparse.Chapter09.problem_9_1_spectrum`: the three preconditioned
  matrices have the same spectrum.

## Conventions

* The scalar field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`[RCLike 𝕜]`). All matrices are in
  $\mathbb{K}^{n \times n}$, and a matrix acts on a vector of `EuclideanSpace 𝕜 (Fin n)` by
  `Matrix.toEuclideanLin`, written `A ⬝ x`.
* "Nonsingular" is `IsUnit`. The inverse `M⁻¹` is Mathlib's matrix inverse, which is $0$ for a
  singular matrix. The three definitions accept any matrices; the results assume that $M_L$ and
  $M_R$ are nonsingular.
-/

open Matrix
open scoped SaadSparse

namespace SaadSparse.Chapter09

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The three preconditioned systems -/

/-- **Equation (9.1)** of [saad2003iterative]. For $M, A \in \mathbb{K}^{n \times n}$, the
**left-preconditioned matrix** is $M^{-1} A$. The left-preconditioned system is
$M^{-1} A x = M^{-1} b$, in the unknown $x$ itself. -/
noncomputable abbrev leftPreconditioned (M A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := M⁻¹ * A

/-- **Equation (9.2)** of [saad2003iterative]. For $M, A \in \mathbb{K}^{n \times n}$, the
**right-preconditioned matrix** is $A M^{-1}$. The right-preconditioned system is
$A M^{-1} u = b$ in the unknown $u = Mx$, and the solution of $Ax = b$ is recovered as
$x = M^{-1} u$. -/
noncomputable abbrev rightPreconditioned (M A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := A * M⁻¹

/-- **Equation (9.3)** of [saad2003iterative]. For $M_L, M_R, A \in \mathbb{K}^{n \times n}$, the
**split-preconditioned matrix** is $M_L^{-1} A M_R^{-1}$. It is used for a preconditioner given
in factored form $M = M_L M_R$. The split-preconditioned system is
$M_L^{-1} A M_R^{-1} u = M_L^{-1} b$ in the unknown $u = M_R x$.

The definition does not require $M = M_L M_R$; the results below take it as a hypothesis. -/
noncomputable abbrev splitPreconditioned (ML MR A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := ML⁻¹ * A * MR⁻¹

variable {A M ML MR : Matrix (Fin n) (Fin n) 𝕜}

/-- The action of a matrix product $BC$ on a vector $x$ is $B(Cx)$. -/
private theorem mul_apply_eq (B C : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) :
    ((B * C) ⬝ x) = (B ⬝ (C ⬝ x)) := by
  rw [toEuclideanLin_mul]
  rfl

/-- For a nonsingular matrix $M$, $M^{-1}(Mx) = x$. -/
private theorem inv_apply_apply (hM : IsUnit M) (x : 𝔼) : (M⁻¹ ⬝ (M ⬝ x)) = x := by
  rw [← mul_apply_eq, nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM), toEuclideanLin_one]
  rfl

/-- For a nonsingular matrix $M$, $M(M^{-1}x) = x$. -/
private theorem apply_inv_apply (hM : IsUnit M) (x : 𝔼) : (M ⬝ (M⁻¹ ⬝ x)) = x := by
  rw [← mul_apply_eq, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM), toEuclideanLin_one]
  rfl

/-- For a nonsingular matrix $M$, the map $x \mapsto M^{-1} x$ is injective. -/
private theorem inv_apply_injective (hM : IsUnit M) :
    Function.Injective fun x : 𝔼 => (M⁻¹ ⬝ x) :=
  Function.LeftInverse.injective (g := fun y : 𝔼 => (M ⬝ y)) (apply_inv_apply hM)

/-- **Section 9.1** of [saad2003iterative], equivalence of the preconditioned systems. Let
$A, M_L, M_R \in \mathbb{K}^{n \times n}$, let $M_L$ and $M_R$ be nonsingular, and let
$M = M_L M_R$. Then for all $b, x \in \mathbb{K}^n$:
$$M^{-1} A x = M^{-1} b \iff Ax = b, \qquad A M^{-1} (Mx) = b \iff Ax = b,$$
$$M_L^{-1} A M_R^{-1} (M_R x) = M_L^{-1} b \iff Ax = b.$$
So each of the systems (9.1), (9.2) and (9.3) has exactly the solutions of $Ax = b$, through the
change of variables $u = Mx$ for the right-preconditioned system and $u = M_R x$ for the split
one. -/
theorem solution_iff (hML : IsUnit ML) (hMR : IsUnit MR) (hM : M = ML * MR) (b x : 𝔼) :
    ((leftPreconditioned M A ⬝ x) = (M⁻¹ ⬝ b) ↔ (A ⬝ x) = b) ∧
      ((rightPreconditioned M A ⬝ (M ⬝ x)) = b ↔ (A ⬝ x) = b) ∧
        ((splitPreconditioned ML MR A ⬝ (MR ⬝ x)) = (ML⁻¹ ⬝ b) ↔ (A ⬝ x) = b) := by
  have hMu : IsUnit M := hM ▸ hML.mul hMR
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_apply_eq]
    exact ⟨fun h => inv_apply_injective hMu h, fun h => by rw [h]⟩
  · rw [mul_apply_eq, inv_apply_apply hMu]
  · rw [mul_apply_eq, mul_apply_eq, inv_apply_apply hMR]
    exact ⟨fun h => inv_apply_injective hML h, fun h => by rw [h]⟩

/-! ### P-9.1 and P-9.10: the three matrices are conjugate -/

/-- **Problems P-9.1 and P-9.10** of [saad2003iterative], conjugacy. Let
$A, M_L, M_R \in \mathbb{K}^{n \times n}$, let $M_L$ and $M_R$ be nonsingular, and let
$M = M_L M_R$. Then
$$A M^{-1} = M (M^{-1} A) M^{-1}, \qquad M_L^{-1} A M_R^{-1} = M_L^{-1} (A M^{-1}) M_L.$$
So the left-, right- and split-preconditioned matrices are conjugate to one another. -/
theorem problem_9_1 (hML : IsUnit ML) (hMR : IsUnit MR) (hM : M = ML * MR) :
    rightPreconditioned M A = M * leftPreconditioned M A * M⁻¹ ∧
      splitPreconditioned ML MR A = ML⁻¹ * rightPreconditioned M A * ML := by
  have hMu : IsUnit M := hM ▸ hML.mul hMR
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hMu)
  have hLL : ML⁻¹ * ML = 1 := nonsing_inv_mul ML ((isUnit_iff_isUnit_det ML).mp hML)
  refine ⟨?_, ?_⟩
  · change A * M⁻¹ = M * (M⁻¹ * A) * M⁻¹
    rw [← mul_assoc, hMM, one_mul]
  · change ML⁻¹ * A * MR⁻¹ = ML⁻¹ * (A * M⁻¹) * ML
    rw [hM, Matrix.mul_inv_rev]
    calc ML⁻¹ * A * MR⁻¹ = ML⁻¹ * A * MR⁻¹ * (ML⁻¹ * ML) := by rw [hLL, mul_one]
      _ = ML⁻¹ * (A * (MR⁻¹ * ML⁻¹)) * ML := by simp only [mul_assoc]

/-- **Problems P-9.1 and P-9.10** of [saad2003iterative], characteristic polynomials. Let
$A, M_L, M_R \in \mathbb{K}^{n \times n}$, let $M_L$ and $M_R$ be nonsingular, and let
$M = M_L M_R$. Then $A M^{-1}$ and $M_L^{-1} A M_R^{-1}$ have the same characteristic polynomial
as $M^{-1} A$.

The proof uses the conjugacy of `SaadSparse.Chapter09.problem_9_1`. -/
theorem problem_9_1_charpoly (hML : IsUnit ML) (hMR : IsUnit MR) (hM : M = ML * MR) :
    (rightPreconditioned M A).charpoly = (leftPreconditioned M A).charpoly ∧
      (splitPreconditioned ML MR A).charpoly = (leftPreconditioned M A).charpoly := by
  have hMu : IsUnit M := hM ▸ hML.mul hMR
  obtain ⟨h1, h2⟩ := problem_9_1 (A := A) hML hMR hM
  have hr : (rightPreconditioned M A).charpoly = (leftPreconditioned M A).charpoly := by
    rw [h1, ← hMu.unit_spec]
    exact charpoly_units_conj hMu.unit _
  refine ⟨hr, ?_⟩
  rw [h2, ← hML.unit_spec, charpoly_units_conj' hML.unit]
  exact hr

/-- **Problems P-9.1 and P-9.10** of [saad2003iterative], spectra. Let
$A, M_L, M_R \in \mathbb{K}^{n \times n}$, let $M_L$ and $M_R$ be nonsingular, and let
$M = M_L M_R$. Then $A M^{-1}$ and $M_L^{-1} A M_R^{-1}$ have the same spectrum in $\mathbb{K}$
as $M^{-1} A$.

This is the reason of the chapter for expecting the three ways of preconditioning to behave
alike. -/
theorem problem_9_1_spectrum (hML : IsUnit ML) (hMR : IsUnit MR) (hM : M = ML * MR) :
    spectrum 𝕜 (rightPreconditioned M A) = spectrum 𝕜 (leftPreconditioned M A) ∧
      spectrum 𝕜 (splitPreconditioned ML MR A) = spectrum 𝕜 (leftPreconditioned M A) := by
  have hMu : IsUnit M := hM ▸ hML.mul hMR
  obtain ⟨h1, h2⟩ := problem_9_1 (A := A) hML hMR hM
  have hr : spectrum 𝕜 (rightPreconditioned M A) = spectrum 𝕜 (leftPreconditioned M A) := by
    rw [h1, ← hMu.unit_spec, ← Matrix.coe_units_inv hMu.unit]
    exact spectrum.units_conjugate
  refine ⟨hr, ?_⟩
  rw [h2, ← hML.unit_spec, ← Matrix.coe_units_inv hML.unit, spectrum.units_conjugate']
  exact hr

end SaadSparse.Chapter09
