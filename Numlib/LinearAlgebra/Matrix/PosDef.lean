/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PosDef`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definite matrices over a ring with trivial star

Mathlib's `Matrix.PosSemidef` and `Matrix.PosDef` bundle `Matrix.IsHermitian`, which over a ring
whose star is trivial — the real numbers, in every use a numerical method makes of a symmetric
positive definite system — is `Matrix.IsSymm` (`Matrix.isHermitian_iff_isSymm`). The two lemmas
below take that step under one name, so that a positive definite real matrix can be handed to a
theorem stated for a symmetric one. `Matrix.isUnit_of_posDef_add_transpose` is the companion of
Mathlib's `Matrix.PosDef.isUnit` for a matrix whose symmetric part is positive definite, and
`Matrix.PosDef.exists_isUnit_conj_eq_one` is the congruence of a positive definite matrix to the
identity, `Wᴴ B W = 1`.
-/

namespace Matrix

variable {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] [TrivialStar R] {A : Matrix n n R}

/-- Over a ring with trivial star, a positive semidefinite matrix is symmetric. -/
theorem PosSemidef.isSymm (hA : A.PosSemidef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

/-- Over a ring with trivial star, a positive definite matrix is symmetric. -/
theorem PosDef.isSymm (hA : A.PosDef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

/-- A real matrix whose symmetric part `P + Pᵀ` is positive definite is nonsingular: `P x = 0`
forces `xᵀ (P + Pᵀ) x = 2 xᵀ P x = 0`. -/
theorem isUnit_of_posDef_add_transpose {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : (P + Pᵀ).PosDef) : IsUnit P := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : ∃ a ≠ 0, P *ᵥ a = 0 := by
    obtain ⟨a, b, hab⟩ := Function.not_injective_iff.mp <| mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, hab, mulVec_sub]⟩
  have hpos := hP.dotProduct_mulVec_pos ha
  rw [star_trivial, add_mulVec, dotProduct_add, ha2, dotProduct_zero, zero_add, mulVec_transpose,
    dotProduct_comm, ← dotProduct_mulVec, ha2, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### Congruence to the identity -/

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix is congruent to the identity: `Wᴴ B W = 1` for the invertible
`W = V D^{-1/2}`, where `B = V D Vᴴ` is its spectral decomposition. This is the role the Cholesky
factor `H` plays in [quarteroni2000numerical] Theorem 5.7 (`W = H⁻¹`), without a triangular
structure. -/
theorem PosDef.exists_isUnit_conj_eq_one {B : Matrix n n 𝕜} (hB : B.PosDef) :
    ∃ W : Matrix n n 𝕜, IsUnit W ∧ star W * B * W = 1 := by
  set V : Matrix n n 𝕜 := (hB.1.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : star V * B * V = diagonal (RCLike.ofReal ∘ hB.1.eigenvalues) := by
    have := hB.1.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at this
  have hpos : ∀ i, 0 < hB.1.eigenvalues i := hB.eigenvalues_pos
  set D : Matrix n n 𝕜 := diagonal fun i => (((Real.sqrt (hB.1.eigenvalues i))⁻¹ : ℝ) : 𝕜)
    with hDdef
  refine ⟨V * D, ?_, ?_⟩
  · refine Unitary.isUnit_coe.mul ((isUnit_diagonal).mpr (Pi.isUnit_iff.mpr fun i => ?_))
    rw [isUnit_iff_ne_zero]
    exact_mod_cast (inv_ne_zero (Real.sqrt_pos.mpr (hpos i)).ne')
  · have hassoc : star (V * D) * B * (V * D) = star D * (star V * B * V) * D := by
      rw [star_mul]
      simp only [Matrix.mul_assoc]
    rw [hassoc, hV, hDdef, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have hs : Real.sqrt (hB.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_one]
    congr 1
    field_simp
    rw [Real.sq_sqrt (hpos i).le]

end RCLike

end Matrix
