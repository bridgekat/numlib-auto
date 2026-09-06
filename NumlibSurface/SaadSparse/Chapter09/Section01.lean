import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.SaadSparse.Common

/-!
# Saad §9.1: preconditioned iterations — left, right and split preconditioning

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §9.1 , with P-9.1 and P-9.10.

A preconditioner is a nonsingular `M` for which `M z = r` is cheap to solve and `M ≈ A`. It can
be applied on the left (9.1), on the right (9.2) or split as `M = M_L M_R` (9.3); the three
give the matrices `M⁻¹ A`, `A M⁻¹` and `M_L⁻¹ A M_R⁻¹` of `leftPreconditioned`,
`rightPreconditioned` and `splitPreconditioned`.

`solution_iff` is the statement that the three preconditioned systems are equivalent to `A x = b`,
with the changes of variables `u = M x` (right) and `u = M_R x` (split) the book records, and
`problem_9_1` that the three matrices are conjugate, hence isospectral
(`problem_9_1_spectrum`) with equal characteristic polynomials (`problem_9_1_charpoly`). That is
the chapter's reason for expecting the three options to behave alike; §9.3.4 shows that they
nevertheless minimize different quantities.
-/

open Matrix
open scoped SaadSparse

namespace SaadSparse.Chapter09

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The three preconditioned systems -/

/-- Saad (9.1): the left-preconditioned matrix `M⁻¹ A`. The preconditioned system is
`M⁻¹ A x = M⁻¹ b`, in the unknown `x` itself. -/
noncomputable abbrev leftPreconditioned (M A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := M⁻¹ * A

/-- Saad (9.2): the right-preconditioned matrix `A M⁻¹`. The preconditioned system is
`A M⁻¹ u = b` in the unknown `u = M x`, and the solution of `A x = b` is recovered as
`x = M⁻¹ u`. -/
noncomputable abbrev rightPreconditioned (M A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := A * M⁻¹

/-- Saad (9.3): the split-preconditioned matrix `M_L⁻¹ A M_R⁻¹`, for a preconditioner given in
factored form `M = M_L M_R`. The preconditioned system is `M_L⁻¹ A M_R⁻¹ u = M_L⁻¹ b` in the
unknown `u = M_R x`. -/
noncomputable abbrev splitPreconditioned (ML MR A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 := ML⁻¹ * A * MR⁻¹

variable {A M ML MR : Matrix (Fin n) (Fin n) 𝕜}

/-- A matrix product acts as the composite of the two actions. -/
private theorem mul_apply_eq (B C : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) :
    ((B * C) ⬝ x) = (B ⬝ (C ⬝ x)) := by
  rw [toEuclideanLin_mul]
  rfl

/-- A nonsingular matrix is undone by its inverse. -/
private theorem inv_apply_apply (hM : IsUnit M) (x : 𝔼) : (M⁻¹ ⬝ (M ⬝ x)) = x := by
  rw [← mul_apply_eq, nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM), toEuclideanLin_one]
  rfl

/-- A nonsingular matrix undoes its inverse. -/
private theorem apply_inv_apply (hM : IsUnit M) (x : 𝔼) : (M ⬝ (M⁻¹ ⬝ x)) = x := by
  rw [← mul_apply_eq, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM), toEuclideanLin_one]
  rfl

/-- Acting by the inverse of a nonsingular matrix is injective. -/
private theorem inv_apply_injective (hM : IsUnit M) :
    Function.Injective fun x : 𝔼 => (M⁻¹ ⬝ x) :=
  Function.LeftInverse.injective (g := fun y : 𝔼 => (M ⬝ y)) (apply_inv_apply hM)

/-- Saad §9.1: the three preconditioned systems (9.1), (9.2) and (9.3) have exactly the solutions
of `A x = b`, through the changes of variables `u = M x` for the right-preconditioned system and
`u = M_R x` for the split one. -/
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

/-- **P-9.1** and **P-9.10**: `A M⁻¹ = M (M⁻¹ A) M⁻¹`, and `M_L⁻¹ A M_R⁻¹ = M_L⁻¹ (A M⁻¹) M_L`
when `M = M_L M_R`.  So the left-, right- and split-preconditioned matrices are conjugate to one
another. -/
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

/-- **P-9.1** and **P-9.10**: conjugate matrices have the same characteristic polynomial, so the
three preconditioned matrices do. -/
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

/-- **P-9.1** and **P-9.10**: the left-, right- and split-preconditioned matrices are isospectral.
This is the chapter's reason for expecting the three ways of preconditioning to behave alike. -/
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
