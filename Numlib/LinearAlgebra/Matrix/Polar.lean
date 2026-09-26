/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix.Polar` (beside `Mathlib.Analysis.Matrix.Order`, whose
`CFC.sqrt` it uses), or a C⋆-algebraic polar decomposition once Mathlib has one.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# The polar decomposition of a matrix

A *polar decomposition* of `A : Matrix m n 𝕜` is a factorization `A = U P` with `U` having
orthonormal columns (`Uᴴ U = 1`) and `P` positive semidefinite — the matrix analogue of
`z = e^{iθ} |z|` ([golub2013matrix] Theorem 9.4.1, §6.4.1). It exists whenever `A` has at least
as many rows as columns, and the symmetric factor is always `P = (Aᴴ A)^{1/2}`.

## Main definitions

* `Matrix.IsPolarDecomposition A U P`: the specification, a structure with fields
  `conjTranspose_mul_self : Uᴴ * U = 1`, `posSemidef : P.PosSemidef` and `eq_mul : A = U * P`.

## Main results

* `Matrix.IsSVD.isPolarDecomposition`: an SVD `A = W Σ Vᴴ` gives the polar decomposition
  `A = (W₁ Vᴴ)(V Σ₁ Vᴴ)`, with `W₁` the first columns of `W` — the one place where the library
  builds the polar factor from singular vectors.
* `Matrix.exists_isPolarDecomposition`: [golub2013matrix] Theorem 9.4.1, for any finite index
  types with `card n ≤ card m`; `Matrix.exists_isPolarDecomposition_conjTranspose` is the dual
  `A = P Vᴴ` for wide matrices.
* `Matrix.IsPolarDecomposition.eq_cfcSqrt`: the symmetric factor is `CFC.sqrt (Aᴴ A)` (and
  `CFC.abs A` for square `A`, `Matrix.IsPolarDecomposition.eq_cfcAbs`); with `Aᴴ A` positive
  definite the orthonormal factor is `A (Aᴴ A)^{-1/2}`
  (`Matrix.IsPolarDecomposition.eq_mul_inv_cfcSqrt`), and for a nonsingular square `A` the
  decomposition is unique (`Matrix.IsPolarDecomposition.unique`).
* `Matrix.exists_orthonormal_cols_norm_sub_le`: **the nearest orthonormal block**
  ([golub2013matrix] (8.1.7)): if `‖Xᴴ X − 1‖₂ ≤ τ < 1`, the polar factor `Q` of `X` has the same
  range as `X` and `‖Q − X‖₂ ≤ τ` (`Matrix.IsPolarDecomposition.l2_opNorm_sub_le`).

## Implementation notes

Statements about "the polar factor" take an `IsPolarDecomposition` hypothesis rather than a chosen
factorization, as `Matrix.IsSVD` does for the SVD: the orthonormal factor is not unique for a
singular `A`. The orthogonal Procrustes problem (`Numlib/LinearAlgebra/Matrix/Procrustes`) and the
functional-calculus consumers (`Numlib/Analysis/Matrix/Function/Polar`) are stated through it.

## References

* [golub2013matrix] Theorem 9.4.1, §6.4.1, (8.1.7).
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Def

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **A polar decomposition, as a specification** ([golub2013matrix] Theorem 9.4.1): `A = U P`
with `U` having orthonormal columns (`Uᴴ U = 1`) and `P` positive semidefinite. For square `A`
the factor `U` is unitary (`Matrix.IsPolarDecomposition.mem_unitaryGroup`). -/
structure IsPolarDecomposition (A U : Matrix m n 𝕜) (P : Matrix n n 𝕜) : Prop where
  /-- The orthonormal factor has orthonormal columns. -/
  conjTranspose_mul_self : Uᴴ * U = 1
  /-- The symmetric factor is positive semidefinite. -/
  posSemidef : P.PosSemidef
  /-- The factorization. -/
  eq_mul : A = U * P

namespace IsPolarDecomposition

variable {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}

/-- The symmetric factor of a polar decomposition is Hermitian. -/
theorem isHermitian (h : IsPolarDecomposition A U P) : P.IsHermitian :=
  h.posSemidef.isHermitian

/-- The Gram matrix of `A = U P` is `P²`. -/
theorem conjTranspose_mul_self_eq (h : IsPolarDecomposition A U P) : Aᴴ * A = P * P := by
  rw [h.eq_mul, conjTranspose_mul, h.isHermitian.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
    h.conjTranspose_mul_self, Matrix.one_mul]

open scoped MatrixOrder in
/-- **The symmetric polar factor is `(Aᴴ A)^{1/2}`** ([golub2013matrix] §9.4.3): `P` is the
positive semidefinite square root of `Aᴴ A = P²`. -/
theorem eq_cfcSqrt (h : IsPolarDecomposition A U P) : P = CFC.sqrt (Aᴴ * A) := by
  rw [h.conjTranspose_mul_self_eq]
  exact (CFC.sqrt_mul_self P h.posSemidef.nonneg).symm

/-- The symmetric factor is invertible when `Aᴴ A` is. -/
theorem isUnit_of_isUnit_conjTranspose_mul_self (h : IsPolarDecomposition A U P)
    (hA : IsUnit (Aᴴ * A)) : IsUnit P := by
  rw [h.conjTranspose_mul_self_eq, isUnit_iff_isUnit_det, det_mul] at hA
  exact (isUnit_iff_isUnit_det P).2 (isUnit_of_mul_isUnit_left hA)

open scoped MatrixOrder in
/-- **The orthonormal factor of a matrix of full column rank** ([golub2013matrix] §9.4.3,
"if `rank(A) = n`, then `U = A (AᵀA)^{-1/2}`"): if `Aᴴ A` is positive definite then
`U = A (Aᴴ A)^{-1/2}`. -/
theorem eq_mul_inv_cfcSqrt (h : IsPolarDecomposition A U P) (hA : (Aᴴ * A).PosDef) :
    U = A * (CFC.sqrt (Aᴴ * A))⁻¹ := by
  have hP := h.isUnit_of_isUnit_conjTranspose_mul_self hA.isUnit
  rw [← h.eq_cfcSqrt, h.eq_mul, Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).1 hP), Matrix.mul_one]

/-- A polar decomposition transported along bijections of the index types. -/
theorem reindex {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (h : IsPolarDecomposition A U P) (e₁ : m ≃ m') (e₂ : n ≃ n') :
    IsPolarDecomposition (reindex e₁ e₂ A) (reindex e₁ e₂ U) (reindex e₂ e₂ P) where
  conjTranspose_mul_self := by
    rw [conjTranspose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv,
      h.conjTranspose_mul_self, submatrix_one_equiv]
  posSemidef := h.posSemidef.submatrix _
  eq_mul := by
    rw [h.eq_mul, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

/-- **The left polar decomposition**: a polar decomposition `Aᴴ = V P` of the adjoint is the
factorization `A = P Vᴴ`, with `Vᴴ` having orthonormal rows. -/
theorem eq_mul_conjTranspose {A : Matrix n m 𝕜} {V : Matrix m n 𝕜}
    (h : IsPolarDecomposition Aᴴ V P) : A = P * Vᴴ := by
  rw [← conjTranspose_conjTranspose A, h.eq_mul, conjTranspose_mul, h.isHermitian.eq]

end IsPolarDecomposition

namespace IsPolarDecomposition

variable {A U P : Matrix n n 𝕜}

/-- For a square matrix the orthonormal polar factor is unitary. -/
theorem mem_unitaryGroup (h : IsPolarDecomposition A U P) : U ∈ unitaryGroup n 𝕜 :=
  mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.conjTranspose_mul_self)

open scoped MatrixOrder in
/-- For a square matrix the symmetric polar factor is Mathlib's absolute value
`CFC.abs A = CFC.sqrt (star A * A)`. -/
theorem eq_cfcAbs (h : IsPolarDecomposition A U P) : P = CFC.abs A := by
  rw [CFC.abs, star_eq_conjTranspose]
  exact h.eq_cfcSqrt

/-- For a nonsingular square matrix the symmetric polar factor is invertible. -/
theorem isUnit (h : IsPolarDecomposition A U P) (hA : IsUnit A) : IsUnit P := by
  rw [isUnit_iff_isUnit_det, h.eq_mul, det_mul] at hA
  exact (isUnit_iff_isUnit_det P).2 (isUnit_of_mul_isUnit_right hA)

/-- **Uniqueness of the polar decomposition of a nonsingular matrix** ([golub2013matrix] P9.4.8):
`P = (Aᴴ A)^{1/2}` in both, and then `U = A P⁻¹`. -/
theorem unique {U' P' : Matrix n n 𝕜} (hA : IsUnit A) (h : IsPolarDecomposition A U P)
    (h' : IsPolarDecomposition A U' P') : U = U' ∧ P = P' := by
  have hPP : P = P' := h.eq_cfcSqrt.trans h'.eq_cfcSqrt.symm
  refine ⟨?_, hPP⟩
  have hP := (isUnit_iff_isUnit_det P).1 (h.isUnit hA)
  have h1 : U * P = U' * P := by rw [← h.eq_mul, h'.eq_mul, hPP]
  calc U = U * P * P⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
    _ = U' := by rw [h1, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]

end IsPolarDecomposition

end Def

/-! ### Existence, from the singular value decomposition -/

section SVD

variable {m n : ℕ}

/-- For `n ≤ m`, the product of a square matrix with a tall rectangular diagonal matrix only sees
the first `n` columns of the square matrix: `W Σ = W₁ diag(σ)`. -/
theorem mul_rectDiagonal_eq_submatrix_mul_diagonal (hnm : n ≤ m) (W : Matrix (Fin m) (Fin m) 𝕜)
    (σ : ℕ → 𝕜) :
    W * (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜)
      = W.submatrix id (Fin.castLE hnm) * diagonal fun i : Fin n => σ i := by
  ext i j
  rw [mul_apply, mul_apply, Finset.sum_eq_single (Fin.castLE hnm j), Finset.sum_eq_single j]
  · simp [rectDiagonal_apply, submatrix_apply]
  · intro l _ hl
    simp [hl]
  · simp
  · intro l _ hl
    have hl' : (l : ℕ) ≠ j := fun h' => hl (Fin.ext h')
    simp [rectDiagonal_apply, hl']
  · simp

/-- The first `n` columns of a unitary matrix are orthonormal. -/
theorem conjTranspose_submatrix_castLE_mul_self (hnm : n ≤ m) {W : Matrix (Fin m) (Fin m) 𝕜}
    (hW : W ∈ unitaryGroup (Fin m) 𝕜) :
    (W.submatrix id (Fin.castLE hnm))ᴴ * W.submatrix id (Fin.castLE hnm) = 1 := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hW]
  exact submatrix_one _ (Fin.castLE_injective hnm)

variable {A : Matrix (Fin m) (Fin n) 𝕜} {W : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) 𝕜}

/-- **The polar decomposition from an SVD** ([golub2013matrix] Theorem 9.4.1's proof, and §6.4.1:
"`A = UΣVᵀ` gives `A = (UVᵀ)(VΣVᵀ)`"): for `n ≤ m` and an SVD `Wᴴ A V = Σ`, with `W₁` the first
`n` columns of `W`, `A = (W₁ Vᴴ)(V diag(σ) Vᴴ)` is a polar decomposition. -/
theorem IsSVD.isPolarDecomposition (h : IsSVD A W σ V) (hnm : n ≤ m) :
    IsPolarDecomposition A (W.submatrix id (Fin.castLE hnm) * Vᴴ)
      (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ) where
  conjTranspose_mul_self := by
    have hV : V * Vᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Vᴴ,
      conjTranspose_submatrix_castLE_mul_self hnm h.mem_unitaryGroup_left, Matrix.one_mul, hV]
  posSemidef := by
    refine PosSemidef.mul_mul_conjTranspose_same ?_ V
    exact posSemidef_diagonal_iff.2 fun i => RCLike.ofReal_nonneg.2 (h.nonneg i)
  eq_mul := by
    have hV : Vᴴ * V = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
    conv_lhs => rw [h.eq_mul_mul_star, mul_rectDiagonal_eq_submatrix_mul_diagonal hnm,
      star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

/-- **The polar decomposition from an SVD of a square matrix**: `A = (W Vᴴ)(V diag(σ) Vᴴ)`. -/
theorem IsSVD.isPolarDecomposition_of_square {A W V : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsSVD A W σ V) :
    IsPolarDecomposition A (W * Vᴴ) (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ) := by
  simpa using h.isPolarDecomposition le_rfl

end SVD

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The polar decomposition** ([golub2013matrix] Theorem 9.4.1): every `A : Matrix m n 𝕜` with
`card n ≤ card m` is `A = U P` with `Uᴴ U = 1` and `P` positive semidefinite. Reindex to `Fin`,
take an SVD, and use `Matrix.IsSVD.isPolarDecomposition`. -/
theorem exists_isPolarDecomposition (A : Matrix m n 𝕜) (h : Fintype.card n ≤ Fintype.card m) :
    ∃ U P, IsPolarDecomposition A U P := by
  set e₁ := Fintype.equivFin m
  set e₂ := Fintype.equivFin n
  obtain ⟨W, σ, V, hs⟩ := exists_isSVD (reindex e₁ e₂ A)
  have hp := (hs.isPolarDecomposition h).reindex e₁.symm e₂.symm
  rw [← reindex_symm, Equiv.symm_apply_apply] at hp
  exact ⟨_, _, hp⟩

omit [DecidableEq n] in
/-- **The left polar decomposition of a wide matrix** ([golub2013matrix] §9.4.3 by transposition,
P9.4.11): for `card m ≤ card n` there are `V`, `P` with `IsPolarDecomposition Aᴴ V P`, that is
`A = P Vᴴ` (`Matrix.IsPolarDecomposition.eq_mul_conjTranspose`) with `Vᴴ` having orthonormal rows
and `P = (A Aᴴ)^{1/2}` positive semidefinite. -/
theorem exists_isPolarDecomposition_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜)
    (h : Fintype.card m ≤ Fintype.card n) : ∃ V P, IsPolarDecomposition Aᴴ V P :=
  exists_isPolarDecomposition Aᴴ h

end Exists

/-! ### The nearest orthonormal block -/

section Nearest

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

open scoped Matrix.Norms.L2Operator

/-- `|1 − s| ≤ |1 − s²|` for `s ≥ 0`. -/
private theorem abs_one_sub_le_abs_one_sub_sq {s : ℝ} (hs : 0 ≤ s) : |1 - s| ≤ |1 - s * s| := by
  rw [show 1 - s * s = (1 - s) * (1 + s) by ring, abs_mul]
  exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)

/-- For a positive semidefinite `P`, `‖1 − P‖₂ ≤ ‖1 − P²‖₂`: in an eigenbasis the two matrices
are diagonal with entries `1 − s` and `1 − s²`, `s ≥ 0`. -/
theorem PosSemidef.l2_opNorm_one_sub_le {P : Matrix r r 𝕜} (hP : P.PosSemidef) :
    ‖1 - P‖ ≤ ‖1 - P * P‖ := by
  set u := hP.isHermitian.eigenvectorUnitary
  set φ := Unitary.conjStarAlgAut 𝕜 (Matrix r r 𝕜) u
  set s := hP.isHermitian.eigenvalues
  have hφ : ∀ M, ‖φ M‖ = ‖M‖ := fun M => by
    rw [Unitary.conjStarAlgAut_apply]
    exact l2_opNorm_unitary_mul_mul_unitary u.2 M (Unitary.star_mem u.2)
  have hPd : P = φ (diagonal (RCLike.ofReal ∘ s)) := hP.isHermitian.spectral_theorem
  have h1 : 1 - P = φ (diagonal fun i => ((1 - s i : ℝ) : 𝕜)) := by
    rw [hPd, ← map_one φ, ← map_sub, ← diagonal_one, diagonal_sub]
    congr 2
    funext i
    simp
  have h2 : 1 - P * P = φ (diagonal fun i => ((1 - s i * s i : ℝ) : 𝕜)) := by
    rw [hPd, ← map_one φ, ← map_mul, ← map_sub, ← diagonal_one, diagonal_mul_diagonal,
      diagonal_sub]
    congr 2
    funext i
    simp
  rw [h1, h2, hφ, hφ, l2_opNorm_diagonal, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine le_trans ?_ (norm_le_pi_norm _ i)
  simp only [RCLike.norm_ofReal]
  exact abs_one_sub_le_abs_one_sub_sq (hP.eigenvalues_nonneg i)

omit [DecidableEq n] in
/-- **The polar factor is the nearest orthonormal block, quantitatively** ([golub2013matrix]
(8.1.7)): if `X = Q P` is a polar decomposition then `‖Q − X‖₂ ≤ ‖Xᴴ X − 1‖₂`. Indeed
`Q − X = Q (1 − P)`, `Q` is an isometry, and `‖1 − P‖₂ ≤ ‖1 − P²‖₂ = ‖1 − Xᴴ X‖₂`. -/
theorem IsPolarDecomposition.l2_opNorm_sub_le {X Q : Matrix n r 𝕜} {P : Matrix r r 𝕜}
    (h : IsPolarDecomposition X Q P) : ‖Q - X‖ ≤ ‖Xᴴ * X - 1‖ := by
  have hQ : Q - X = Q * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← h.eq_mul]
  rw [hQ, l2_opNorm_mul_of_conjTranspose_mul_self_eq_one h.conjTranspose_mul_self,
    h.conjTranspose_mul_self_eq, ← norm_neg (P * P - 1), neg_sub]
  exact h.posSemidef.l2_opNorm_one_sub_le

omit [DecidableEq n] in
/-- **The nearest orthonormal block** ([golub2013matrix] (8.1.7) in the proof of Theorem 8.1.16):
for `X : Matrix n r 𝕜` with `card r ≤ card n` and `‖Xᴴ X − 1‖₂ ≤ τ < 1` there is `Q` with
orthonormal columns, the same range as `X`, and `‖Q − X‖₂ ≤ τ`: the polar factor of `X`
(`Matrix.IsPolarDecomposition.l2_opNorm_sub_le`). `τ < 1` makes `Xᴴ X`, hence `P`, invertible,
so `Q = X P⁻¹` and `X = Q P` have the same range. (The book's intermediate "`1 − σ_r² = τ`" holds
only when the smallest singular value is the one farthest from `1`; the conclusion does not need
it.) -/
theorem exists_orthonormal_cols_norm_sub_le (X : Matrix n r 𝕜)
    (hcard : Fintype.card r ≤ Fintype.card n) {τ : ℝ} (hX : lpOpNorm 2 (Xᴴ * X - 1) ≤ τ)
    (hτ : τ < 1) :
    ∃ Q : Matrix n r 𝕜, Qᴴ * Q = 1 ∧
      LinearMap.range (toLin' Q) = LinearMap.range (toLin' X) ∧ lpOpNorm 2 (Q - X) ≤ τ := by
  obtain ⟨Q, P, h⟩ := exists_isPolarDecomposition X hcard
  rw [lpOpNorm_two] at hX
  refine ⟨Q, h.conjTranspose_mul_self, ?_, ?_⟩
  · have hG : IsUnit (Xᴴ * X) := by
      refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
      rw [← sub_eq_zero]
      set x : EuclideanSpace 𝕜 r := WithLp.toLp 2 (v - w)
      have hx : toEuclideanLin (Xᴴ * X) x = 0 := by
        rw [toEuclideanLin_toLp, mulVec_sub, hvw, sub_self, WithLp.toLp_zero]
      have hle := norm_toEuclideanLin_apply_le (Xᴴ * X - 1) x
      rw [toEuclideanLin_sub_apply, hx, toEuclideanLin_one_apply, zero_sub, norm_neg] at hle
      have hn : ‖x‖ = 0 := by
        by_contra hne
        have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
        have : ‖x‖ ≤ τ * ‖x‖ := hle.trans (mul_le_mul_of_nonneg_right hX hpos.le)
        nlinarith
      rw [norm_eq_zero] at hn
      exact (WithLp.toLp_eq_zero 2).1 hn
    have hP := (isUnit_iff_isUnit_det P).1 (h.isUnit_of_isUnit_conjTranspose_mul_self hG)
    have hQX : Q = X * P⁻¹ := by
      rw [h.eq_mul, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
    refine le_antisymm ?_ ?_
    · rw [hQX, toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · conv_lhs => rw [h.eq_mul]
      rw [toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
  · rw [lpOpNorm_two]
    exact h.l2_opNorm_sub_le.trans hX

end Nearest

end Matrix
