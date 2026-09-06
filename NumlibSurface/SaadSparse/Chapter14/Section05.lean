import Numlib.LinearSolve.DomainDecomposition.Schur
import NumlibSurface.SaadSparse.Chapter14.Section02

/-!
# Saad §14.5: full matrix methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.5.

A *full matrix method* iterates on the unreduced system (14.2) with a block preconditioner, and
§14.5 says that this is the same computation as a Schur complement method on the reduced system.

* `blockLower B F L_S` and `blockUpper B E U_S` of the backbone are `L_A` and `U_A` of (14.49)
  (with `L_S = U_S = I`) and of (14.55); `blockPreconditioner` is their product `M_A = L_A U_A`,
  the preconditioner of `A` induced by an approximate factorization `S ≈ L_S U_S` of the Schur
  complement.  `equation_14_52`, `equation_14_58` and `equation_14_59`, `equation_14_60` are the
  four factorizations, and `blockPreconditioner_eq_fromBlocks` is Saad's closing remark: an exact
  preconditioner of `S` induces an exact block preconditioner of `A`.
* `consistentGuess B E f y₀` of the backbone is the initial guess (14.50)/(14.56), and
  `equation_14_51` is (14.51): the iterates of the preconditioned method are again of that form.
* `proposition_14_11` and `proposition_14_12` are the two propositions.  Saad states them for "the
  same Krylov subspace method", which is not a formal object; they are read here as statements
  about the specifications of `Numlib/LinearSolve/Projection/Basic`, so that they cover GMRES,
  MINRES, FOM, CG and the Lanczos method at once.  Both sides of the equivalence are written in the
  variable the split-preconditioned method actually iterates on — `u = U_A x` on the full system and
  `w = U_S y` on the reduced one — and `equation_14_51` translates the first back into Saad's `x_m`.
  `proposition_14_11_form` and `proposition_14_12_form` are the same results in the one-way form
  Saad writes — the iteration *produces* iterates of the form (14.51) — and
  `proposition_14_11_galerkin` and `proposition_14_12_galerkin` are the orthogonal-projection twins.

Everything specializes `Numlib/LinearSolve/DomainDecomposition/Schur`.
-/

open Matrix DomainDecomposition

namespace SaadSparse.Chapter14

variable {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {E : Matrix (Fin p) (Fin q) ℝ}
variable {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
variable {LS US MS : Matrix (Fin q) (Fin q) ℝ}

/-! ### The block preconditioners (14.49) and (14.55) -/

/-- **(14.49)**: the left preconditioner `L_A = (I 0; F B⁻¹ I)`. -/
theorem blockLower_one : blockLower B F 1 = fromBlocks 1 0 (F * B⁻¹) 1 := rfl

/-- **(14.49)**: the right preconditioner `U_A = (B E; 0 I)`. -/
theorem blockUpper_one : blockUpper B E 1 = fromBlocks B E 0 1 := rfl

/-- **(14.50)/(14.56)**: the consistent initial guess `x₀ = (B⁻¹(f - E y₀); y₀)`. -/
theorem consistentGuess_eq (f : Fin p → ℝ) (y : Fin q → ℝ) :
    consistentGuess B E f y = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y := rfl

/-- The reduced right-hand side `g'` of §14.2 is the backbone's. -/
theorem reducedRhs_eq (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) :
    reducedRhs B F f g = DomainDecomposition.reducedRhs B F f g := rfl

/-- With `L_S = U_S = I` the preconditioned Schur complement is `S` itself. -/
theorem precondSchurComplement_one_one :
    precondSchurComplement B E F C 1 1 = schurComplement B E F C := by
  rw [precondSchurComplement, inv_one, Matrix.one_mul, Matrix.mul_one]
  exact (schurComplement_eq B E F C).symm

/-- **(14.55)**: the block preconditioner `M_A = L_A U_A` of the full matrix built from an
approximate factorization `S ≈ L_S U_S` of the Schur complement.  Taking `L_S = U_S = I` gives the
preconditioner (14.49). -/
noncomputable def blockPreconditioner (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (LS US : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  blockLower B F LS * blockUpper B E US

/-- **(14.52)**: the factorization `A = L_A (I ⊕ S) U_A` behind Proposition 14.11. -/
theorem equation_14_52 (hB : IsUnit B) :
    fromBlocks B E F C
      = blockLower B F 1 * fromBlocks 1 0 0 (schurComplement B E F C) * blockUpper B E 1 := by
  rw [← precondSchurComplement_one_one]
  exact fromBlocks_eq_blockLower_mul hB isUnit_one isUnit_one

/-- **(14.58)**: the factorization `A = L_A (I ⊕ L_S⁻¹ S U_S⁻¹) U_A` behind Proposition 14.12. -/
theorem equation_14_58 (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    fromBlocks B E F C
      = blockLower B F LS * fromBlocks 1 0 0 (LS⁻¹ * schurComplement B E F C * US⁻¹)
        * blockUpper B E US :=
  fromBlocks_eq_blockLower_mul hB hLS hUS

/-- **(14.59)**: the factorization that preconditions `S` from the left by `M_S`. -/
theorem equation_14_59 (hB : IsUnit B) (hMS : IsUnit MS) :
    fromBlocks B E F C
      = blockLower B F MS * fromBlocks 1 0 0 (MS⁻¹ * schurComplement B E F C)
        * blockUpper B E 1 := by
  have h := fromBlocks_eq_blockLower_mul (E := E) (F := F) (C := C) hB hMS isUnit_one
  rwa [precondSchurComplement, inv_one, Matrix.mul_one] at h

/-- **(14.60)**: the factorization that preconditions `S` from the right by `M_S`. -/
theorem equation_14_60 (hB : IsUnit B) (hMS : IsUnit MS) :
    fromBlocks B E F C
      = blockLower B F 1 * fromBlocks 1 0 0 (schurComplement B E F C * MS⁻¹)
        * blockUpper B E MS := by
  have h := fromBlocks_eq_blockLower_mul (E := E) (F := F) (C := C) hB isUnit_one hMS
  rwa [precondSchurComplement, inv_one, Matrix.one_mul] at h

/-- **The closing remark of §14.5**: when the preconditioner `L_S U_S` of the Schur complement is
exact, the block preconditioner `M_A = L_A U_A` it induces on `A` is exact too. -/
theorem blockPreconditioner_eq_fromBlocks (hB : IsUnit B) (h : LS * US = schurComplement B E F C) :
    blockPreconditioner B E F LS US = fromBlocks B E F C := by
  have h1 : F * B⁻¹ * B = F := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul B
    ((Matrix.isUnit_iff_isUnit_det B).1 hB), Matrix.mul_one]
  rw [blockPreconditioner, blockLower, blockUpper, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [h1, h, schurComplement_def]
  congr 1
  abel

/-- **(14.51)/(14.57)**: an iterate of the preconditioned full system, read back in the original
variable through `x = U_A⁻¹ u`, is again of the consistent form `x_m = (B⁻¹(f - E y_m); y_m)`. -/
theorem equation_14_51 (hB : IsUnit B) (f : Fin p → ℝ) (y : Fin q → ℝ) :
    (blockUpper B E 1)⁻¹ *ᵥ Sum.elim f y = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y := by
  have h := blockUpper_inv_mulVec (E := E) (US := 1) hB isUnit_one f y
  rwa [Matrix.one_mulVec] at h

/-- **(14.57)**: the same for the preconditioner (14.55), where the transformed iterate is
`(f; U_S y_m)`. -/
theorem equation_14_57 (hB : IsUnit B) (hUS : IsUnit US) (f : Fin p → ℝ) (y : Fin q → ℝ) :
    (blockUpper B E US)⁻¹ *ᵥ Sum.elim f (US *ᵥ y) = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y :=
  blockUpper_inv_mulVec hB hUS f y

/-! ### Propositions 14.11 and 14.12 -/

/-- **Proposition 14.11**: run a minimal-residual Krylov method on the full system (14.2)
preconditioned on the left by `L_A` and on the right by `U_A` of (14.49), from a consistent initial
guess (14.50).  Then its iterate at step `k` is `U_A x` for `x = (B⁻¹(f - E y); y)` exactly when `y`
is the iterate of the same method applied without preconditioning to the reduced system
`S y = g'` from `y₀`.

Both sides are written in the variable the split-preconditioned method iterates on: `u = U_A x` on
the left, and `y` itself on the right, since `U_S = I` here.  `equation_14_51` turns the left-hand
iterate back into Saad's `x_m`. -/
theorem proposition_14_11 (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsMinResIterate (toEuclideanLin (precondMatrix B E F C 1 1))
        (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResIterate (toEuclideanLin (schurComplement B E F C))
        (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y) := by
  have h := isMinRes_iff_isMinRes_schurComplement (E := E) (F := F) (C := C) (LS := 1) (US := 1)
    hB isUnit_one isUnit_one f g y₀ y k
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at h
  simpa only [inv_one, Matrix.one_mulVec] using h

/-- **Proposition 14.11 in the direction the book states it**: the preconditioned iteration
*produces* iterates of the form (14.51).  Every minimal-residual iterate `u` of the preconditioned
full system is `U_A x` for a consistent `x = (B⁻¹(f - E y); y)` — `equation_14_51` recovers `x` from
`u` — and that `y` is the iterate of the same method on `S y = g'`. -/
theorem proposition_14_11_form (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ : Fin q → ℝ) (k : ℕ)
    {u : EuclideanSpace ℝ (Fin p ⊕ Fin q)}
    (hu : Krylov.IsMinResIterate (toEuclideanLin (precondMatrix B E F C 1 1))
      (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : Fin q → ℝ,
      Krylov.IsMinResIterate (toEuclideanLin (schurComplement B E F C))
          (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y)
        ∧ u = WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y) := by
  obtain ⟨y, hy, hyu⟩ := exists_isMinRes_schurComplement (E := E) (F := F) (C := C) (LS := 1)
    (US := 1) hB isUnit_one isUnit_one f g y₀ k hu
  refine ⟨y, ?_, hyu⟩
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at hy
  simpa only [inv_one, Matrix.one_mulVec] using hy

/-- **Proposition 14.12 in the direction the book states it**: the iterates have the form (14.57),
and their interface blocks are the iterates of the split-preconditioned reduced method. -/
theorem proposition_14_12_form (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : Fin p → ℝ)
    (g y₀ : Fin q → ℝ) (k : ℕ) {u : EuclideanSpace ℝ (Fin p ⊕ Fin q)}
    (hu : Krylov.IsMinResIterate (toEuclideanLin (precondMatrix B E F C LS US))
      (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : Fin q → ℝ,
      Krylov.IsMinResIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
          (WithLp.toLp 2 (US *ᵥ y))
        ∧ u = WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y) :=
  exists_isMinRes_schurComplement hB hLS hUS f g y₀ k hu

/-- **The Galerkin form of Proposition 14.11**, for FOM, CG and the Lanczos method. -/
theorem proposition_14_11_galerkin (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin (precondMatrix B E F C 1 1))
        (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate (toEuclideanLin (schurComplement B E F C))
        (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y) := by
  have h := isGalerkin_iff_isGalerkin_schurComplement (E := E) (F := F) (C := C) (LS := 1)
    (US := 1) hB isUnit_one isUnit_one f g y₀ y k
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at h
  simpa only [inv_one, Matrix.one_mulVec] using h

/-- **Proposition 14.12**: the same statement when the Schur complement is itself preconditioned,
`S ≈ L_S U_S`, with the block preconditioners (14.55) and the consistent initial guess (14.56).  The
iterate of the full system at step `k` corresponds to the iterate of the same method applied to
`S y = g'` preconditioned on the left by `L_S` and on the right by `U_S`, from `y₀`. -/
theorem proposition_14_12 (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : Fin p → ℝ)
    (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsMinResIterate (toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) :=
  isMinRes_iff_isMinRes_schurComplement hB hLS hUS f g y₀ y k

/-- **The Galerkin form of Proposition 14.12**. -/
theorem proposition_14_12_galerkin (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) :=
  isGalerkin_iff_isGalerkin_schurComplement hB hLS hUS f g y₀ y k

end SaadSparse.Chapter14
