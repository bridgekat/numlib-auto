import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.SaadSparse.Common

/-!
# Saad §14.2: block Gaussian elimination and the Schur complement

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.2.1–14.2.2.

The partitioning is the edge-based one of (14.2): the interior variables come first and the
interface variables last, so the system matrix is `Matrix.fromBlocks B E F C` over the index type
`Fin p ⊕ Fin q` and no reindexing equivalence appears anywhere.

* `schurComplement` is `S = C - F B⁻¹ E` of (14.5), `reducedRhs` is `g' = g - F B⁻¹ f` of (14.4),
  and `interfaceRestrict` is Saad's `R_y`, the restriction of a vector to its interface block.
* `blockGaussianElimination` is Algorithm 14.1 as a function, and `blockGaussianElimination_eq`
  says that it solves the system.
* `equation_14_6` is the block `LU` factorization and `equation_14_7` the block inverse.
* `proposition_14_1_1`, `proposition_14_1_2` and `proposition_14_1_3` are the three clauses of
  Proposition 14.1.

Everything specializes `Numlib/LinearAlgebra/Matrix/SchurComplement`.
-/

open Matrix

namespace SaadSparse.Chapter14

variable {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {E : Matrix (Fin p) (Fin q) ℝ}
variable {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}

/-- **(14.5)**: the Schur complement `S = C - F B⁻¹ E` associated with the interface variables of
the block partitioning (14.2). -/
noncomputable def schurComplement (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  C - F * B⁻¹ * E

/-- The Schur complement of §14.2, unfolded. -/
theorem schurComplement_def (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = C - F * B⁻¹ * E := rfl

/-- The Schur complement of §14.2 is the backbone's `Matrix.schurComplement` of the block
matrix. -/
theorem schurComplement_eq (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = (fromBlocks B E F C).schurComplement := rfl

/-- **(14.4)**: the right-hand side `g' = g - F B⁻¹ f` of the reduced system `S y = g'`. -/
noncomputable def reducedRhs (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin q → ℝ :=
  g - F *ᵥ (B⁻¹ *ᵥ f)

/-- The reduced right-hand side, unfolded. -/
theorem reducedRhs_def (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : reducedRhs B F f g = g - F *ᵥ (B⁻¹ *ᵥ f) := rfl

/-- Saad's `R_y`: the restriction of a vector of the whole space to its interface block. -/
def interfaceRestrict (v : Fin p ⊕ Fin q → ℝ) : Fin q → ℝ := v ∘ Sum.inr

/-- The interface unknown `y = S⁻¹ g'` computed by Algorithm 14.1. -/
noncomputable def interfaceSolution (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ) :
    Fin q → ℝ :=
  (schurComplement B E F C)⁻¹ *ᵥ reducedRhs B F f g

/-- **Algorithm 14.1** (block Gaussian elimination) as a function: solve `B E' = E` and
`B f' = f`, form `g' = g - F f'` and `S = C - F E'`, solve `S y = g'`, and recover
`x = f' - E' y`. -/
noncomputable def blockGaussianElimination (B : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin p) (Fin q) ℝ) (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin p ⊕ Fin q → ℝ :=
  Sum.elim (B⁻¹ *ᵥ f - (B⁻¹ * E) *ᵥ interfaceSolution B E F C f g)
    (interfaceSolution B E F C f g)

/-- **(14.6)**: the block `LU` factorization of the partitioned matrix, whose second factor is
block upper triangular with the Schur complement in its `(2,2)` corner. -/
theorem equation_14_6 (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks B E 0 (schurComplement B E F C) :=
  Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement hB

/-- **(14.7)**: the block inverse of the partitioned matrix, with `S⁻¹` in its `(2,2)` corner. -/
theorem equation_14_7 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    (fromBlocks B E F C)⁻¹
      = fromBlocks (B⁻¹ + B⁻¹ * E * (schurComplement B E F C)⁻¹ * F * B⁻¹)
          (-(B⁻¹ * E * (schurComplement B E F C)⁻¹))
          (-((schurComplement B E F C)⁻¹ * F * B⁻¹)) (schurComplement B E F C)⁻¹ :=
  Matrix.inv_fromBlocks_eq hB hA

/-- **Proposition 14.1 (1)**: if the partitioned matrix and its `(1,1)` block are nonsingular,
then so is the Schur complement. -/
theorem proposition_14_1_1 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    IsUnit (schurComplement B E F C) :=
  Matrix.isUnit_schurComplement (by simpa using hB) hA

/-- **Proposition 14.1 (2)**: the Schur complement of a symmetric positive definite matrix is
symmetric positive definite. -/
theorem proposition_14_1_2 (hA : (fromBlocks B E F C).PosDef) :
    (schurComplement B E F C).PosDef :=
  Matrix.PosDef.schurComplement hA

/-- **Proposition 14.1 (3)**: `S⁻¹ y = R_y A⁻¹ (0, y)`, so a solver for the whole system provides
one for the reduced interface system. -/
theorem proposition_14_1_3 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) (y : Fin q → ℝ) :
    (schurComplement B E F C)⁻¹ *ᵥ y
      = interfaceRestrict ((fromBlocks B E F C)⁻¹ *ᵥ Sum.elim 0 y) := by
  have h22 : ((fromBlocks B E F C)⁻¹).toBlocks₂₂ = (schurComplement B E F C)⁻¹ :=
    Matrix.toBlocks₂₂_inv_eq_inv_schurComplement (by simpa using hB) hA
  funext j
  rw [← h22]
  simp [interfaceRestrict, Matrix.mulVec_apply_eq_sum, Fintype.sum_sum_type, Matrix.toBlocks₂₂]

/-- **Algorithm 14.1 solves the system**: the pair `(x, y)` it produces satisfies
`A (x, y) = (f, g)`. -/
theorem blockGaussianElimination_eq (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C))
    (f : Fin p → ℝ) (g : Fin q → ℝ) :
    fromBlocks B E F C *ᵥ blockGaussianElimination B E F C f g = Sum.elim f g := by
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det _).1 hB
  have hSdet : IsUnit (schurComplement B E F C).det :=
    (isUnit_iff_isUnit_det _).1 (proposition_14_1_1 hB hA)
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv B hBdet
  have hSS : schurComplement B E F C * (schurComplement B E F C)⁻¹ = 1 := mul_nonsing_inv _ hSdet
  have hy : schurComplement B E F C *ᵥ interfaceSolution B E F C f g = reducedRhs B F f g := by
    rw [show interfaceSolution B E F C f g
        = (schurComplement B E F C)⁻¹ *ᵥ reducedRhs B F f g from rfl,
      Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
  rw [blockGaussianElimination, Matrix.fromBlocks_mulVec]
  refine congrArg₂ Sum.elim ?_ ?_
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hBB, Matrix.one_mul, Matrix.one_mulVec]
    abel
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    have hsum : (F * B⁻¹) *ᵥ f - (F * B⁻¹ * E) *ᵥ interfaceSolution B E F C f g
          + C *ᵥ interfaceSolution B E F C f g
        = (F * B⁻¹) *ᵥ f + schurComplement B E F C *ᵥ interfaceSolution B E F C f g := by
      rw [schurComplement_def, Matrix.sub_mulVec]; abel
    rw [hsum, hy, reducedRhs_def, Matrix.mulVec_mulVec]
    abel

end SaadSparse.Chapter14
