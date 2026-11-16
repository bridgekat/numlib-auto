/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
import Numlib.LinearAlgebra.Matrix.Charpoly

/-!
# Symmetry, congruence and spectrum of positive definite matrices

Mathlib's `Matrix.PosSemidef` and `Matrix.PosDef` include the condition `Matrix.IsHermitian`. Over a
ring whose star operation is trivial, such as $\mathbb{R}$, this condition is the symmetry $A^T = A$
(`Matrix.isHermitian_iff_isSymm`). This module gives that step one name, so that a positive definite
real matrix can be passed to a theorem stated for a symmetric one; this is the use that numerical
methods for symmetric positive definite systems make of it. It also proves two facts over
$\mathbb{R}$ or $\mathbb{C}$: a positive definite matrix $B$ is congruent to the identity,
$W^H B W = I$ for an invertible $W$, and the eigenvalues of a positive definite complex matrix have
positive real part.

## Main results

* `Matrix.PosSemidef.isSymm`, `Matrix.PosDef.isSymm`: over a ring with trivial star, a positive
  semidefinite or positive definite matrix is symmetric.
* `Matrix.PosDef.exists_isUnit_conj_eq_one`: a positive definite matrix $B$ satisfies $W^H B W = I$
  for some invertible $W$.
* `Matrix.PosDef.re_pos_of_mem_spectrum`: every eigenvalue $\mu$ of a positive definite complex
  matrix has $\operatorname{Re} \mu > 0$.

## Implementation notes

* The nonsingularity of a real matrix $P$ whose symmetric part $P + P^T$ is positive definite,
  `Matrix.isUnit_of_posDef_add_transpose`, is in `Numlib.LinearAlgebra.Matrix.HermitianPart`, as the
  real case of the statement for the Hermitian part.
-/

namespace Matrix

variable {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] [TrivialStar R] {A : Matrix n n R}

/-- Let $R$ be a partially ordered ring whose star operation is trivial. A positive semidefinite
matrix $A$ over $R$ is symmetric: $A^T = A$. -/
theorem PosSemidef.isSymm (hA : A.PosSemidef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

/-- Let $R$ be a partially ordered ring whose star operation is trivial. A positive definite matrix
$A$ over $R$ is symmetric: $A^T = A$. -/
theorem PosDef.isSymm (hA : A.PosDef) : A.IsSymm := isHermitian_iff_isSymm.1 hA.1

/-! ### Congruence to the identity -/

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix is congruent to the identity: let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $B \in \mathbb{K}^{n \times n}$ be positive definite. Then there is an
invertible $W \in \mathbb{K}^{n \times n}$ with
$$W^H B W = I.$$

The proof takes $W = V D^{-1/2}$, where $B = V D V^H$ is the spectral decomposition of $B$ with
$V$ unitary and $D$ diagonal with positive entries. The matrix $W$ plays the role of the inverse
$H^{-1}$ of the Cholesky factor $H$ in Theorem 5.7 of [quarteroni2000numerical], without the
triangular structure. In Lean, $W^H$ is `star W`. -/
theorem PosDef.exists_isUnit_conj_eq_one {B : Matrix n n 𝕜} (hB : B.PosDef) :
    ∃ W : Matrix n n 𝕜, IsUnit W ∧ star W * B * W = 1 := by
  set V : Matrix n n 𝕜 := (hB.1.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : star V * B * V = diagonal (RCLike.ofReal ∘ hB.1.eigenvalues) :=
    hB.1.star_eigenvectorUnitary_mul_mul
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

/-! ### The spectrum of a positive definite complex matrix -/

section Complex

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalues of a positive definite complex matrix lie in the open right half-plane: if
$M \in \mathbb{C}^{n \times n}$ is positive definite and $\mu$ is in the spectrum of $M$, then
$\operatorname{Re} \mu > 0$. Indeed $M v = \mu v$ with $v \neq 0$ gives
$0 < v^H M v = \mu \, v^H v$, and $v^H v > 0$. -/
theorem PosDef.re_pos_of_mem_spectrum {M : Matrix n n ℂ} (hM : M.PosDef) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : 0 < μ.re := by
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← exists_mulVec_eq_zero_iff] at hμ
  obtain ⟨v, hv0, hv⟩ := hμ
  have hMv : M *ᵥ v = μ • v := by
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec] at hv
    exact hv.symm
  have h1 := hM.dotProduct_mulVec_pos hv0
  have h2 := PosDef.one.dotProduct_mulVec_pos hv0
  rw [hMv, dotProduct_smul, smul_eq_mul] at h1
  rw [one_mulVec] at h2
  obtain ⟨hre1, him1⟩ := Complex.lt_def.1 h1
  obtain ⟨hre2, him2⟩ := Complex.lt_def.1 h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re] at hre1 hre2 him2
  rw [← him2, mul_zero, sub_zero] at hre1
  exact pos_of_mul_pos_left hre1 hre2.le

end Complex

end Matrix
