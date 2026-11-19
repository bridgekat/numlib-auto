/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section05
import NumlibSurface.BenIsraelGreville.Chapter06.Section04
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter05.Section02
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Perturbations of the Moore–Penrose inverse

Section 6.6 of [benIsrael2003generalized] relates changes in the
Moore–Penrose inverse to the gaps between row and column ranges.

## Deviations from the source

* **Theorem 14**, Equation (133) (correction). The left multiplier uses
  the lower-left block, and the right multiplier uses the upper-right block.
* **Theorem 15**, Equation (135b) (scope). The bound on the perturbed
  pseudoinverse alone uses a vector in the perturbed range orthogonal
  to the original range, or the corresponding row-space direction.
* **Theorem 16**, Equation (136c) (correction). With the perturbation
  defined as the new matrix minus the original one, the adjoint term
  supported on the perturbed kernel has positive sign.
* **Theorem 16**, Equation (136d) (correction). The simplified inverse
  difference holds when the row and column spaces agree. Acuteness allows
  the spaces to rotate, so the two projection corrections can be nonzero.
* **Theorem 17**, Equation (137) (correction). The two inverse norms in the
  maximum are squared to match the quadratic inverse factor in the bound.
* **Exercise 78** (correction). The derivative is negative as in (139).
  The first-order residual therefore adds the positive product term.
* **Exercise 81** (scope). Acuteness and vanishing off-diagonal perturbation
  blocks do not imply the smallness hypothesis (142). That hypothesis is
  required for the displayed estimates.
-/

namespace BenIsraelGreville.Chapter06

open Matrix Module Chapter02
open scoped InnerProductSpace ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Definition 5** of [benIsrael2003generalized], Chapter 6, Equation
(130). A perturbation is acute when both range gaps are below one. -/
def IsAcutePerturbation (A B : Matrix m n ℂ) : Prop :=
  subspaceDistance (toEuclideanLin A).range (toEuclideanLin B).range < 1 ∧
    subspaceDistance (toEuclideanLin Aᴴ).range (toEuclideanLin Bᴴ).range < 1

/-- **Theorem 13** of [benIsrael2003generalized], Chapter 6.
The column range gap is below one precisely when the column spaces
are totally inclined, equivalently when the ranks of both matrices
and of the perturbed matrix projected onto the original column space agree. -/
theorem theorem_6_13 (A B : Matrix m n ℂ) :
    let L := (toEuclideanLin A).range
    let M := (toEuclideanLin B).range
    (subspaceDistance L M < 1 ↔ TotallyInclined L M) ∧
      (TotallyInclined L M ↔ A.rank = B.rank ∧ B.rank = (orthogonalProjector L * B).rank) := by
  let L := (toEuclideanLin A).range
  let M := (toEuclideanLin B).range
  refine ⟨(exercise_6_68 L M).1, ?_⟩
  have hRange : (toEuclideanLin (orthogonalProjector L * B)).range =
      M.map L.starProjection.toLinearMap := by
    rw [toEuclideanLin_mul, toEuclideanLin_orthogonalProjector, LinearMap.range_comp]
  have hRank : (orthogonalProjector L * B).rank = inclinationDimension L M := by
    rw [← finrank_range_toEuclideanLin, hRange, (projectedSubspaces_finrank L M).1]
  have h := (exercise_6_68 L M).2
  change TotallyInclined L M ↔ A.rank = B.rank ∧ B.rank = (orthogonalProjector L * B).rank
  change TotallyInclined L M ↔ finrank ℂ (toEuclideanLin A).range = inclinationDimension L M ∧
    finrank ℂ (toEuclideanLin B).range = inclinationDimension L M at h
  rw [finrank_range_toEuclideanLin, finrank_range_toEuclideanLin] at h
  rw [h, hRank]
  omega

/-- **Theorem 13**, row-space form, of [benIsrael2003generalized], Chapter 6.
Applying the range criteria to the adjoints gives the corresponding
conditions on the row spaces. -/
theorem theorem_6_13_rows (A B : Matrix m n ℂ) :
    let L := (toEuclideanLin Aᴴ).range
    let M := (toEuclideanLin Bᴴ).range
    (subspaceDistance L M < 1 ↔ TotallyInclined L M) ∧
      (TotallyInclined L M ↔ A.rank = B.rank ∧ B.rank = (orthogonalProjector L * Bᴴ).rank) := by
  have h := theorem_6_13 Aᴴ Bᴴ
  dsimp only at h
  rwa [rank_conjTranspose A, rank_conjTranspose B] at h

private theorem range_eq_of_partialIsometry_final_projector
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {W : Matrix p q ℂ} {L : Submodule ℂ (EuclideanSpace ℂ p)}
    (hW : IsPartialIsometry W) (hL : W * Wᴴ = orthogonalProjector L) :
    (toEuclideanLin W).range = L := by
  have hp := W.mul_pinv_eq_starProjection
  rw [← (isPartialIsometry_iff_adjoint_eq_pinv W).mp hW, hL, toEuclideanLin_orthogonalProjector] at hp
  apply_fun (fun T : EuclideanSpace ℂ p →ₗ[ℂ] EuclideanSpace ℂ p => T.range) at hp
  simpa only [Submodule.range_starProjection] using hp.symm

/-- **Equations (129a)–(129c)** of [benIsrael2003generalized], Chapter 6.
Orthonormal bases adapted to the column and row ranges put a matrix
in a single nonsingular leading block. The same bases express the
perturbation and its sum with the original matrix in four blocks. -/
theorem rankAdaptedOrthonormalCoordinates {p q : ℕ} (A E : Matrix (Fin p) (Fin q) ℂ) :
    let r := A.rank
    let hm : r ≤ p := A.rank_le_height
    let hn : r ≤ q := A.rank_le_width
    let eₘ : Fin p ≃ Fin r ⊕ Fin (p - r) :=
      (finCongr (Nat.add_sub_of_le hm).symm).trans finSumFinEquiv.symm
    let eₙ : Fin q ≃ Fin r ⊕ Fin (q - r) :=
      (finCongr (Nat.add_sub_of_le hn).symm).trans finSumFinEquiv.symm
    ∃ (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
        (D F : Matrix (Fin r) (Fin r) ℂ) (R : Matrix (Fin r) (Fin (q - r)) ℂ)
        (S : Matrix (Fin (p - r)) (Fin r) ℂ) (T : Matrix (Fin (p - r)) (Fin (q - r)) ℂ),
      U ∈ unitaryGroup (Fin p) ℂ ∧ V ∈ unitaryGroup (Fin q) ℂ ∧ IsUnit D ∧
        (toEuclideanLin (U.submatrix id (Fin.castLE hm))).range = (toEuclideanLin A).range ∧
        (toEuclideanLin (V.submatrix id (Fin.castLE hn))).range = (toEuclideanLin Aᴴ).range ∧
        Matrix.reindex eₘ eₙ (Uᴴ * A * V) = fromBlocks D 0 0 0 ∧
        Matrix.reindex eₘ eₙ (Uᴴ * E * V) = fromBlocks F R S T ∧
        Matrix.reindex eₘ eₙ (Uᴴ * (A + E) * V) = fromBlocks (D + F) R S T := by
  let r := A.rank
  let hm : r ≤ p := A.rank_le_height
  let hn : r ≤ q := A.rank_le_width
  let eₘ : Fin p ≃ Fin r ⊕ Fin (p - r) :=
    (finCongr (Nat.add_sub_of_le hm).symm).trans finSumFinEquiv.symm
  let eₙ : Fin q ≃ Fin r ⊕ Fin (q - r) :=
    (finCongr (Nat.add_sub_of_le hn).symm).trans finSumFinEquiv.symm
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  let σ := A.sortedSingularValues
  let D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun i => (σ i : ℂ))
  let B := Matrix.reindex eₘ eₙ (Uᴴ * E * V)
  have hD : IsUnit D := by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.ofReal_ne_zero.mpr ?_)
    change ¬ A.sortedSingularValues i = 0
    rw [A.sortedSingularValues_eq_zero_iff_rank_le]
    exact not_le_of_gt i.isLt
  obtain ⟨hUr, hVr, -, -, -, hPr, hQr, -⟩ := theorem_6_6 h
  have hU'range := range_eq_of_partialIsometry_final_projector hUr hPr
  have hV'range := range_eq_of_partialIsometry_final_projector hVr hQr
  have hₘL (i : Fin r) : (eₘ.symm (Sum.inl i) : ℕ) = i := by
    simp [eₘ, finSumFinEquiv_apply_left]
  have hₙL (j : Fin r) : (eₙ.symm (Sum.inl j) : ℕ) = j := by
    simp [eₙ, finSumFinEquiv_apply_left]
  have hₘR (i : Fin (p - r)) : (eₘ.symm (Sum.inr i) : ℕ) = r + i := by
    simp [eₘ, finSumFinEquiv_apply_right]
  have hₙR (j : Fin (q - r)) : (eₙ.symm (Sum.inr j) : ℕ) = r + j := by
    simp [eₙ, finSumFinEquiv_apply_right]
  have hMain : Matrix.reindex eₘ eₙ (Uᴴ * A * V) = fromBlocks D 0 0 0 := by
    have hs : Uᴴ * A * V = rectDiagonal (fun i => (σ i : ℂ)) := h.1.star_mul_mul
    rw [hs]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [reindex_apply, submatrix_apply, rectDiagonal_apply, hₘL, hₙL,
        fromBlocks_apply₁₁, D, diagonal_apply, Fin.ext_iff]
    · rw [reindex_apply, submatrix_apply, rectDiagonal_apply, hₘL, hₙR,
        fromBlocks_apply₁₂, Matrix.zero_apply, ite_eq_right]
      have hi := i.isLt
      omega
    · rw [reindex_apply, submatrix_apply, rectDiagonal_apply, hₘR, hₙL,
        fromBlocks_apply₂₁, Matrix.zero_apply, ite_eq_right]
      have hj := j.isLt
      omega
    · rw [reindex_apply, submatrix_apply, rectDiagonal_apply, hₘR, hₙR,
        fromBlocks_apply₂₂, Matrix.zero_apply]
      rw [show σ (r + (i : ℕ)) = 0 from h.2 _ (Nat.le_add_right _ _), Complex.ofReal_zero, ite_self]
  have hE : B = fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂ :=
    (fromBlocks_toBlocks B).symm
  refine ⟨U, V, D, B.toBlocks₁₁, B.toBlocks₁₂, B.toBlocks₂₁, B.toBlocks₂₂,
    h.1.mem_unitaryGroup_left, h.1.mem_unitaryGroup_right, hD,
    hU'range, hV'range, hMain, hE, ?_⟩
  change Matrix.reindex eₘ eₙ (Uᴴ * (A + E) * V) =
    fromBlocks (D + B.toBlocks₁₁) B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂
  rw [Matrix.mul_add, Matrix.add_mul, ← coe_reindexAddEquiv, map_add]
  change Matrix.reindex eₘ eₙ (Uᴴ * A * V) + B = _
  calc
    _ = fromBlocks D 0 0 0 + fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂ :=
      congrArg₂ (· + ·) hMain hE
    _ = _ := by rw [fromBlocks_add, zero_add, zero_add, zero_add]

section Compression

variable {k : Type*} [Fintype k] [DecidableEq k]

private theorem isUnit_compression_of_acute (A B : Matrix m n ℂ)
    (J : Matrix m k ℂ) (K : Matrix n k ℂ) (hK : Kᴴ * K = 1)
    (hL : (toEuclideanLin A).range = (toEuclideanLin J).range)
    (hR : (toEuclideanLin Aᴴ).range = (toEuclideanLin K).range)
    (h : IsAcutePerturbation A B) : IsUnit (Jᴴ * B * K) := by
  have hc := ((theorem_6_13 A B).1.mp h.1).2
  have hr := ((theorem_6_13_rows A B).1.mp h.2).1
  change (toEuclideanLin B).range ⊓ (toEuclideanLin A).rangeᗮ = ⊥ at hc
  change (toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).rangeᗮ = ⊥ at hr
  have hinj : Function.Injective (toEuclideanLin (Jᴴ * B * K)) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm ?_ bot_le
    intro x hx
    let y := toEuclideanLin K x
    let z := toEuclideanLin B y
    have hJz : toEuclideanLin Jᴴ z = 0 := by
      change toEuclideanLin (Jᴴ * B * K) x = 0 at hx
      rwa [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply] at hx
    have hz : z ∈ (toEuclideanLin B).range ⊓ (toEuclideanLin A).rangeᗮ := by
      refine ⟨⟨y, rfl⟩, ?_⟩
      rw [hL, LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint]
      exact hJz
    rw [hc, Submodule.mem_bot] at hz
    have hy : y ∈ (toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).rangeᗮ := by
      refine ⟨hR.symm ▸ LinearMap.mem_range_self (toEuclideanLin K) x, ?_⟩
      rw [LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint,
        conjTranspose_conjTranspose]
      exact hz
    rw [hr, Submodule.mem_bot] at hy
    rw [Submodule.mem_bot]
    calc
      x = toEuclideanLin (Kᴴ * K) x := by
        rw [hK, toEuclideanLin_one, LinearMap.id_apply]
      _ = toEuclideanLin Kᴴ y := toEuclideanLin_mul_apply _ _ _
      _ = 0 := by rw [hy, map_zero]
  apply mulVec_injective_iff_isUnit.mp
  intro x y he
  have eq := congrArg (WithLp.toLp 2) he
  rw [← toEuclideanLin_toLp, ← toEuclideanLin_toLp] at eq
  exact congrArg WithLp.ofLp (hinj eq)

omit [DecidableEq n] in
private theorem rank_projected_eq_of_isUnit_compression (B : Matrix m n ℂ)
    (J : Matrix m k ℂ) (K : Matrix n k ℂ) (hJ : Jᴴ * J = 1)
    (hr : B.rank = Fintype.card k) (hF : IsUnit (Jᴴ * B * K)) :
    (orthogonalProjector (toEuclideanLin J).range * B).rank = B.rank := by
  let P := orthogonalProjector (toEuclideanLin J).range
  have hP : P = J * Jᴴ := by
    apply toEuclideanLin.injective
    rw [show P = orthogonalProjector (toEuclideanLin J).range from rfl,
      toEuclideanLin_orthogonalProjector, toEuclideanLin_mul_conjTranspose_eq_starProjection hJ]
  have hF' : Jᴴ * (P * B) * K = Jᴴ * B * K := by
    rw [hP]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul]
  have hl : (Jᴴ * (P * B) * K).rank ≤ (P * B).rank :=
    (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  rw [hF', rank_of_isUnit _ hF, ← hr] at hl
  exact le_antisymm (rank_mul_le_right _ _) hl

end Compression

section Blocks

variable {k p q : Type*} [Fintype k] [Fintype p] [Fintype q]
  [DecidableEq k] [DecidableEq p] [DecidableEq q]

omit [Fintype p] [DecidableEq p] in
private theorem range_fromBlocks_zero (D : Matrix k k ℂ) (hD : IsUnit D) :
    (toEuclideanLin (fromBlocks D (0 : Matrix k q ℂ) (0 : Matrix p k ℂ)
      (0 : Matrix p q ℂ))).range =
      (toEuclideanLin (fromRows (1 : Matrix k k ℂ) (0 : Matrix p k ℂ))).range := by
  let A := fromBlocks D (0 : Matrix k q ℂ) (0 : Matrix p k ℂ) (0 : Matrix p q ℂ)
  let J := fromRows (1 : Matrix k k ℂ) (0 : Matrix p k ℂ)
  let K := fromCols (1 : Matrix k k ℂ) (0 : Matrix k q ℂ)
  have hA : A = J * (D * K) := by
    change fromBlocks D 0 0 0 = fromRows 1 0 * (D * fromCols 1 0)
    rw [← Matrix.mul_assoc, fromRows_mul, fromRows_mul_fromCols]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero]
  have hJ : J = A * (Kᴴ * D⁻¹) := by
    have hK : K * Kᴴ = 1 := by
      simp only [K, conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_one,
        conjTranspose_zero, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]
    symm
    calc
      A * (Kᴴ * D⁻¹) = J * (D * K) * (Kᴴ * D⁻¹) := congrArg (· * (Kᴴ * D⁻¹)) hA
      _ = J * (D * (K * Kᴴ) * D⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hK, Matrix.mul_one, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hD),
        Matrix.mul_one]
  change (toEuclideanLin A).range = (toEuclideanLin J).range
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hA, toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · conv_lhs => rw [hJ, toEuclideanLin_mul]
    exact LinearMap.range_comp_le_range _ _

/-- **Theorem 14** of [benIsrael2003generalized], Chapter 6, Equation
(131). In rank-adapted orthonormal block coordinates the perturbation
is acute exactly when its leading block is nonsingular and its trailing
Schur complement vanishes. -/
theorem theorem_6_14 (D F : Matrix k k ℂ) (R : Matrix k q ℂ) (S : Matrix p k ℂ)
    (T : Matrix p q ℂ) (hD : IsUnit D) :
    IsAcutePerturbation (fromBlocks D 0 0 (0 : Matrix p q ℂ)) (fromBlocks F R S T) ↔
      IsUnit F ∧ T = S * F⁻¹ * R := by
  let A := fromBlocks D (0 : Matrix k q ℂ) (0 : Matrix p k ℂ) (0 : Matrix p q ℂ)
  let B := fromBlocks F R S T
  let J := fromRows (1 : Matrix k k ℂ) (0 : Matrix p k ℂ)
  let K := fromRows (1 : Matrix k k ℂ) (0 : Matrix q k ℂ)
  have hL : (toEuclideanLin A).range = (toEuclideanLin J).range := range_fromBlocks_zero D hD
  have hR : (toEuclideanLin Aᴴ).range = (toEuclideanLin K).range := by
    have he := range_fromBlocks_zero (p := q) (q := p) Dᴴ hD.star
    simpa only [A, fromBlocks_conjTranspose, conjTranspose_zero] using he
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      conjTranspose_zero, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]
  have hK : Kᴴ * K = 1 := by
    simp only [K, conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      conjTranspose_zero, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]
  have hF : Jᴴ * B * K = F := by
    simp only [J, K, B, conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      conjTranspose_zero, fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.one_mul,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hFa : Kᴴ * Bᴴ * J = Fᴴ := by
    have he := congrArg Matrix.conjTranspose hF
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using he
  have hAr : A.rank = Fintype.card k := by
    change (fromBlocks D (0 : Matrix k q ℂ) 0 0).rank = _
    rw [rank_fromBlocks_diagonal, rank_zero, add_zero, rank_of_isUnit _ hD]
  change IsAcutePerturbation A B ↔ _
  constructor
  · intro h
    have hUnit := isUnit_compression_of_acute A B J K hK hL hR h
    rw [hF] at hUnit
    have hr := (theorem_6_13 A B).2.mp ((theorem_6_13 A B).1.mp h.1)
    have ht : B.rank = F.rank := hr.1.symm.trans (hAr.trans (rank_of_isUnit _ hUnit).symm)
    have he := (Chapter05.exercise_3 R S T hUnit).mp ht
    exact ⟨hUnit, sub_eq_zero.mp he⟩
  · rintro ⟨hUnit, hT⟩
    have ht : B.rank = F.rank := (Chapter05.exercise_3 R S T hUnit).mpr
      (sub_eq_zero.mpr hT)
    have hr := ht.trans (rank_of_isUnit _ hUnit)
    have hp := rank_projected_eq_of_isUnit_compression B J K hJ hr (hF.symm ▸ hUnit)
    have hab : Bᴴ.rank = Fintype.card k := (rank_conjTranspose B).trans hr
    have hq := rank_projected_eq_of_isUnit_compression Bᴴ K J hK hab (hFa.symm ▸ hUnit.star)
    have hC : B.rank = (orthogonalProjector (toEuclideanLin A).range * B).rank := by
      simpa only [hL] using hp.symm
    have hD' : B.rank = (orthogonalProjector (toEuclideanLin Aᴴ).range * Bᴴ).rank := by
      simpa only [hR, rank_conjTranspose] using hq.symm
    exact ⟨(theorem_6_13 A B).1.mpr ((theorem_6_13 A B).2.mpr ⟨hAr.trans hr.symm, hC⟩),
      (theorem_6_13_rows A B).1.mpr ((theorem_6_13_rows A B).2.mpr ⟨hAr.trans hr.symm, hD'⟩)⟩

/-- **Theorem 14** of [benIsrael2003generalized], Chapter 6, Equations
(132)–(134). Acute block perturbations admit the two graph factors and
the reversed product formula for their Moore–Penrose inverse. -/
theorem acute_block_factorization (D F : Matrix k k ℂ) (R : Matrix k q ℂ)
    (S : Matrix p k ℂ) (T : Matrix p q ℂ) (hD : IsUnit D)
    (h : IsAcutePerturbation (fromBlocks D 0 0 (0 : Matrix p q ℂ)) (fromBlocks F R S T)) :
    let L := fromRows (1 : Matrix k k ℂ) (S * F⁻¹)
    let U := fromCols (1 : Matrix k k ℂ) (F⁻¹ * R)
    fromBlocks F R S T = L * F * U ∧
      (fromBlocks F R S T).pinv = U.pinv * F⁻¹ * L.pinv := by
  let L := fromRows (1 : Matrix k k ℂ) (S * F⁻¹)
  let U := fromCols (1 : Matrix k k ℂ) (F⁻¹ * R)
  let B := fromBlocks F R S T
  obtain ⟨hF, hT⟩ := (theorem_6_14 D F R S T hD).mp h
  have hr : B.rank = F.rank := (Chapter05.exercise_3 R S T hF).mpr (sub_eq_zero.mpr hT)
  have hRank := rank_of_isUnit _ hF
  have hEq : B = L * F * U := Chapter05.eq_rank_factorization_of_isUnit_block R S T hF hr
  have hLF : (L * F).rank = Fintype.card k := by
    refine le_antisymm (rank_le_card_width _) ?_
    have he := rank_mul_le_left (L * F) U
    rwa [← hEq, hr, hRank] at he
  have hL : L.rank = Fintype.card k :=
    le_antisymm (rank_le_card_width _) (hLF.ge.trans (rank_mul_le_left _ _))
  have hU : U.rank = Fintype.card k := by
    refine le_antisymm (rank_le_card_height _) ?_
    have he := rank_mul_le_right (L * F) U
    rwa [← hEq, hr, hRank] at he
  refine ⟨hEq, ?_⟩
  change B.pinv = U.pinv * F⁻¹ * L.pinv
  rw [hEq, Chapter01.pinv_rankFactorization (L * F) U hLF hU,
    Chapter01.pinv_rankFactorization L F hL hRank, Matrix.pinv_eq_inv hF, Matrix.mul_assoc]

end Blocks

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 15** of [benIsrael2003generalized], Chapter 6, Equations
(135a)–(135b), in the indicated column-space direction. A direction in
the perturbed range orthogonal to the original range forces both bounds. -/
theorem theorem_6_15_of_column_direction (A B : Matrix m n ℂ)
    (h : (toEuclideanLin B).range ⊓ (toEuclideanLin A).rangeᗮ ≠ ⊥) :
    1 ≤ ‖B - A‖ * ‖B.pinv - A.pinv‖ ∧ 1 ≤ ‖B - A‖ * ‖B.pinv‖ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  let y := toEuclideanLin B.pinv x
  let N := 1 - A * A.pinv
  let E := B - A
  have hBB : toEuclideanLin (B * B.pinv) x = x := by
    rw [B.mul_pinv_eq_starProjection, ContinuousLinearMap.coe_coe]
    exact Submodule.starProjection_eq_self_iff.mpr hx.1
  have hAA : toEuclideanLin (A * A.pinv) x = 0 := by
    rw [A.mul_pinv_eq_starProjection, ContinuousLinearMap.coe_coe]
    exact ((toEuclideanLin A).range.starProjection_apply_eq_zero_iff).mpr hx.2
  have hy : toEuclideanLin B y = x := by
    rw [show y = toEuclideanLin B.pinv x from rfl, ← toEuclideanLin_mul_apply, hBB]
  have hPx : toEuclideanLin A.pinv x = 0 := by
    have hPP : A.pinv * (A * A.pinv) = A.pinv := by
      rw [← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
    rw [← hPP, toEuclideanLin_mul_apply, hAA, map_zero]
  have hNA : N * A = 0 := by
    change (1 - A * A.pinv) * A = 0
    rw [Matrix.sub_mul, Matrix.one_mul, A.mul_pinv_mul_self, sub_self]
  have hNx : toEuclideanLin N x = x := by
    change toEuclideanLin (1 - A * A.pinv) x = x
    rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, hAA, sub_zero]
  have hEy : toEuclideanLin E y = x - toEuclideanLin A y := by
    change toEuclideanLin (B - A) y = _
    rw [map_sub, LinearMap.sub_apply, hy]
  have hEq : toEuclideanLin N (toEuclideanLin E y) = x := by
    rw [hEy, map_sub, hNx, ← toEuclideanLin_mul_apply, hNA,
      map_zero, LinearMap.zero_apply, sub_zero]
  have hN : ‖N‖ ≤ 1 := l2_opNorm_one_sub_mul_pinv_le_one A
  have hbound : ‖x‖ ≤ ‖E‖ * ‖y‖ := by
    calc
      ‖x‖ = ‖toEuclideanLin N (toEuclideanLin E y)‖ := by rw [hEq]
      _ ≤ ‖N‖ * ‖toEuclideanLin E y‖ := norm_toEuclideanLin_apply_le _ _
      _ ≤ 1 * (‖E‖ * ‖y‖) := mul_le_mul hN (norm_toEuclideanLin_apply_le _ _)
        (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hDiff : toEuclideanLin (B.pinv - A.pinv) x = y := by
    rw [map_sub, LinearMap.sub_apply, hPx, sub_zero]
  have combine {K : Matrix n m ℂ} (hK : toEuclideanLin K x = y) : 1 ≤ ‖E‖ * ‖K‖ := by
    have hh : ‖y‖ ≤ ‖K‖ * ‖x‖ := hK ▸ norm_toEuclideanLin_apply_le K x
    have hz := hbound.trans (mul_le_mul_of_nonneg_left hh (norm_nonneg E))
    rw [← mul_assoc] at hz
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hz) (norm_pos_iff.mpr hx0)
  exact ⟨combine hDiff, combine rfl⟩

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 15** of [benIsrael2003generalized], Chapter 6, Equation
(135b), in the perturbed row-space direction. -/
theorem theorem_6_15_row_direction (A B : Matrix m n ℂ)
    (h : (toEuclideanLin Bᴴ).range ⊓ (toEuclideanLin Aᴴ).rangeᗮ ≠ ⊥) :
    1 ≤ ‖B - A‖ * ‖B.pinv - A.pinv‖ ∧ 1 ≤ ‖B - A‖ * ‖B.pinv‖ := by
  have he := theorem_6_15_of_column_direction Aᴴ Bᴴ h
  rwa [pinv_conjTranspose, pinv_conjTranspose, ← conjTranspose_sub, ← conjTranspose_sub,
    l2_opNorm_conjTranspose, l2_opNorm_conjTranspose, l2_opNorm_conjTranspose] at he

open scoped Matrix.Norms.L2Operator in
private theorem mul_norm_pinv_sub_ge_one_of_column_not_totallyInclined
    (A B : Matrix m n ℂ)
    (h : ¬ TotallyInclined (toEuclideanLin A).range (toEuclideanLin B).range) :
    1 ≤ ‖B - A‖ * ‖B.pinv - A.pinv‖ := by
  classical
  unfold TotallyInclined CompletelyInclined at h
  rcases not_and_or.mp h with hA | hB
  · simpa only [norm_sub_rev A B, norm_sub_rev A.pinv B.pinv] using
      (theorem_6_15_of_column_direction B A hA).1
  · exact (theorem_6_15_of_column_direction A B hB).1

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 15** of [benIsrael2003generalized], Chapter 6, Equation
(135a). The inverse difference for a nonacute perturbation is at least
the reciprocal of the spectral norm of the perturbation. -/
theorem theorem_6_15 (A B : Matrix m n ℂ) (h : ¬ IsAcutePerturbation A B) :
    1 / ‖B - A‖ ≤ ‖B.pinv - A.pinv‖ := by
  classical
  unfold IsAcutePerturbation at h
  have hbound : 1 ≤ ‖B - A‖ * ‖B.pinv - A.pinv‖ := by
    rcases not_and_or.mp h with hL | hM
    · exact mul_norm_pinv_sub_ge_one_of_column_not_totallyInclined A B
        (fun ht => hL ((theorem_6_13 A B).1.mpr ht))
    · have he := mul_norm_pinv_sub_ge_one_of_column_not_totallyInclined Aᴴ Bᴴ
        (fun ht => hM ((theorem_6_13 Aᴴ Bᴴ).1.mpr ht))
      rwa [pinv_conjTranspose, pinv_conjTranspose, ← conjTranspose_sub, ← conjTranspose_sub,
        l2_opNorm_conjTranspose, l2_opNorm_conjTranspose] at he
  have hE : 0 < ‖B - A‖ := by
    rcases (norm_nonneg (B - A)).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul] at hbound
      linarith
    · exact hpos
  exact (div_le_iff₀ hE).mpr (by rwa [mul_comm])

open scoped Matrix.Norms.L2Operator in
/-- The unconditional individual bound printed in **Equation (135b)** of
[benIsrael2003generalized], Chapter 6, fails for perturbation to zero. -/
theorem nonacute_individual_inverse_bound_counterexample :
    ∃ A B : Matrix (Fin 1) (Fin 1) ℂ,
      ¬ IsAcutePerturbation A B ∧ ‖B.pinv‖ < 1 / ‖B - A‖ := by
  refine ⟨1, 0, ?_, ?_⟩
  · intro h
    have hr := ((theorem_6_13 1 0).2.mp ((theorem_6_13 1 0).1.mp h.1)).1
    simp only [rank_one, rank_zero, Fintype.card_fin, Nat.one_ne_zero] at hr
  · have hz : (0 : Matrix (Fin 1) (Fin 1) ℂ).pinv = 0 := by
      symm
      apply Matrix.pinv_unique <;> simp [Matrix.IsHermitian]
    rw [hz, norm_zero, zero_sub, norm_neg]
    exact one_div_pos.mpr (norm_pos_iff.mpr one_ne_zero)

open scoped Matrix.Norms.L2Operator in
private theorem isAcutePerturbation_of_small (A B : Matrix m n ℂ)
    (hE : ‖B - A‖ < 1) (hD : ‖B.pinv - A.pinv‖ < 1) : IsAcutePerturbation A B := by
  rcases eq_or_ne B A with rfl | hne
  · exact ⟨by simp [subspaceDistance], by simp [subspaceDistance]⟩
  · by_contra hn
    have hPos := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hl : 1 < 1 / ‖B - A‖ := (lt_div_iff₀ hPos).mpr (by rwa [one_mul])
    exact (not_lt_of_ge (hl.le.trans (theorem_6_15 A B hn))) hD

/-- **Theorem 16** of [benIsrael2003generalized], Chapter 6, Equation
(136a). The inverse difference is the leading perturbation term plus
two projection corrections. -/
theorem theorem_6_16 (A B : Matrix m n ℂ) :
    B.pinv - A.pinv =
      -(B.pinv * (B - A) * A.pinv) + B.pinv * (1 - A * A.pinv) -
        (1 - B.pinv * B) * A.pinv := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- **Theorem 16** of [benIsrael2003generalized], Chapter 6, Equation
(136b). The orthogonal range and row projections may be inserted into
the inverse difference formula. -/
theorem pinv_sub_pinv_eq_with_range_projections (A B : Matrix m n ℂ) :
    B.pinv - A.pinv =
      -(B.pinv * (B * B.pinv) * (B - A) * (A.pinv * A) * A.pinv) +
        B.pinv * (B * B.pinv) * (1 - A * A.pinv) -
          (1 - B.pinv * B) * ((A.pinv * A) * A.pinv) := by
  have hB : B.pinv * (B * B.pinv) = B.pinv := by
    rw [← Matrix.mul_assoc, B.pinv_mul_self_mul_pinv]
  rw [hB, Matrix.mul_assoc (B.pinv * (B - A)) (A.pinv * A) A.pinv,
    A.pinv_mul_self_mul_pinv, theorem_6_16 A B]

/-- **Theorem 16** of [benIsrael2003generalized], Chapter 6, Equation
(136c), with the Gram factors written as products of pseudoinverses. -/
theorem pinv_sub_pinv_eq_wedin (A B : Matrix m n ℂ) :
    B.pinv - A.pinv =
      -(B.pinv * (B - A) * A.pinv) +
        (B.pinv * B.pinvᴴ) * (B - A)ᴴ * (1 - A * A.pinv) +
          (1 - B.pinv * B) * (B - A)ᴴ * (A.pinvᴴ * A.pinv) := by
  simpa only [Matrix.mul_assoc] using Matrix.pinv_sub_pinv_eq A B

omit [DecidableEq m] in
private theorem mul_pinv_mul_pinv_adjoint (A : Matrix m n ℂ) :
    (A * A.pinv) * A.pinvᴴ = A.pinvᴴ := by
  have he := congrArg Matrix.conjTranspose A.pinv_mul_self_mul_pinv
  rw [Matrix.mul_assoc A.pinv A A.pinv, conjTranspose_mul, A.isHermitian_mul_pinv.eq] at he
  exact he

omit [DecidableEq m] in
/-- The pseudoinverse of the column Gram matrix is the product of the
pseudoinverse with its adjoint. -/
theorem pinv_columnGram (A : Matrix m n ℂ) : (Aᴴ * A).pinv = A.pinv * A.pinvᴴ := by
  classical
  let P := A.pinv
  let G := Aᴴ * A
  let Q := P * Pᴴ
  have hGP : G * Q = P * A := by
    calc
      G * Q = Aᴴ * ((A * P) * Pᴴ) := by simp only [G, Q, Matrix.mul_assoc]
      _ = Aᴴ * Pᴴ := by rw [mul_pinv_mul_pinv_adjoint A]
      _ = P * A := by rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq]
  have hPG : Q * G = P * A := by
    have he := congrArg Matrix.conjTranspose hGP
    rw [conjTranspose_mul, show Gᴴ = G from (isHermitian_conjTranspose_mul_self A).eq,
      show Qᴴ = Q from (isHermitian_mul_conjTranspose_self P).eq,
      A.isHermitian_pinv_mul.eq] at he
    exact he
  change G.pinv = Q
  symm
  refine G.pinv_unique ?_ ?_ (hGP ▸ A.isHermitian_pinv_mul) (hPG ▸ A.isHermitian_pinv_mul)
  · rw [hGP]
    change (P * A) * (Aᴴ * A) = G
    rw [← Matrix.mul_assoc (P * A) Aᴴ A, A.pinv_mul_self_mul_conjTranspose]
  · rw [hPG]
    change (P * A) * (P * Pᴴ) = Q
    rw [← Matrix.mul_assoc (P * A) P Pᴴ, A.pinv_mul_self_mul_pinv]

/-- **Theorem 16**, corrected Equation (136c), of [benIsrael2003generalized],
Chapter 6. The two projection corrections use the Gram pseudoinverses
and the adjoint of the perturbation. -/
theorem pinv_sub_pinv_eq_gram (A B : Matrix m n ℂ) :
    B.pinv - A.pinv =
      -(B.pinv * (B * B.pinv) * (B - A) * (A.pinv * A) * A.pinv) +
        (Bᴴ * B).pinv * (B.pinv * B) * (B - A)ᴴ * (1 - A * A.pinv) +
          (1 - B.pinv * B) * (B - A)ᴴ * (A * A.pinv) * (A * Aᴴ).pinv := by
  have hB : B.pinv * (B * B.pinv) = B.pinv := by
    rw [← Matrix.mul_assoc, B.pinv_mul_self_mul_pinv]
  have hB' : B.pinvᴴ * (B.pinv * B) = B.pinvᴴ := by
    have he := congrArg Matrix.conjTranspose B.pinv_mul_self_mul_pinv
    rwa [conjTranspose_mul, B.isHermitian_pinv_mul.eq] at he
  have hBQ : (B.pinv * B.pinvᴴ) * (B.pinv * B) = B.pinv * B.pinvᴴ := by
    rw [Matrix.mul_assoc, hB']
  have hA : (A * Aᴴ).pinv = A.pinvᴴ * A.pinv := by
    simpa only [pinv_conjTranspose, conjTranspose_conjTranspose] using pinv_columnGram Aᴴ
  have hAQ : (A * A.pinv) * (A.pinvᴴ * A.pinv) = A.pinvᴴ * A.pinv := by
    rw [← Matrix.mul_assoc (A * A.pinv) A.pinvᴴ A.pinv, mul_pinv_mul_pinv_adjoint A]
  rw [hB, Matrix.mul_assoc (B.pinv * (B - A)) (A.pinv * A) A.pinv,
    A.pinv_mul_self_mul_pinv, pinv_columnGram B, hBQ, hA,
    Matrix.mul_assoc ((1 - B.pinv * B) * (B - A)ᴴ), hAQ]
  exact pinv_sub_pinv_eq_wedin A B

/-- **Theorem 16**, corrected Equation (136d), of [benIsrael2003generalized],
Chapter 6. When the row and column spaces are stationary, both projection
corrections vanish. -/
theorem pinv_sub_pinv_eq_of_same_ranges (A B : Matrix m n ℂ)
    (hL : (toEuclideanLin A).range = (toEuclideanLin B).range)
    (hM : (toEuclideanLin Aᴴ).range = (toEuclideanLin Bᴴ).range) :
    B.pinv - A.pinv = -(B.pinv * (B - A) * A.pinv) := by
  have hA : A * A.pinv = B * B.pinv := by
    apply toEuclideanLin.injective
    rw [A.mul_pinv_eq_starProjection, B.mul_pinv_eq_starProjection]
    exact congrArg (fun L : Submodule ℂ (EuclideanSpace ℂ m) =>
      (L.starProjection : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m)) hL
  have hB : B.pinv * B = A.pinv * A := by
    apply toEuclideanLin.injective
    rw [A.pinv_mul_eq_starProjection, B.pinv_mul_eq_starProjection]
    exact congrArg (fun L : Submodule ℂ (EuclideanSpace ℂ n) =>
      (L.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) hM.symm
  have h1 : B.pinv * (1 - A * A.pinv) = 0 := by
    rw [hA, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, B.pinv_mul_self_mul_pinv,
      sub_self]
  have h2 : (1 - B.pinv * B) * A.pinv = 0 := by
    rw [hB, Matrix.sub_mul, Matrix.one_mul, A.pinv_mul_self_mul_pinv, sub_self]
  rw [theorem_6_16, h1, h2, add_zero, sub_zero]

/-- **Equation (136d)** of [benIsrael2003generalized], Chapter 6.
A rank-one perturbation can be acute and still have a nonzero
projection correction in the pseudoinverse difference. -/
theorem acute_inverse_difference_counterexample :
    ∃ A B : Matrix (Fin 2) (Fin 1) ℂ,
      IsAcutePerturbation A B ∧ B.pinv - A.pinv ≠ -(B.pinv * (B - A) * A.pinv) := by
  let A : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]
  let B : Matrix (Fin 2) (Fin 1) ℂ := !![1; 1]
  let P : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]
  let Q : Matrix (Fin 1) (Fin 2) ℂ := !![1 / 2, 1 / 2]
  have hPA : P * A = 1 := by
    ext i j
    fin_cases i; fin_cases j; norm_num [A, P, Matrix.mul_apply, Fin.sum_univ_two]
  have hQB : Q * B = 1 := by
    ext i j
    fin_cases i; fin_cases j; norm_num [B, Q, Matrix.mul_apply, Fin.sum_univ_two]
  have hPA' : A.pinv = P := by
    symm
    apply A.pinv_unique
    · rw [Matrix.mul_assoc, hPA, Matrix.mul_one]
    · rw [hPA, Matrix.one_mul]
    · have he : P = Aᴴ := by
        ext i j
        fin_cases i
        fin_cases j <;> norm_num [A, P]
      rw [he]
      exact isHermitian_mul_conjTranspose_self A
    · rw [hPA]
      exact isHermitian_one
  have hQB' : B.pinv = Q := by
    symm
    apply B.pinv_unique
    · rw [Matrix.mul_assoc, hQB, Matrix.mul_one]
    · rw [hQB, Matrix.one_mul]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Q, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat]
    · rw [hQB]
      exact isHermitian_one
  have hA : A.rank = 1 := by
    apply le_antisymm (by simpa using rank_le_card_width A)
    have h := rank_mul_le_right P A
    simpa only [hPA, rank_one, Fintype.card_fin] using h
  have hB : B.rank = 1 := by
    apply le_antisymm (by simpa using rank_le_card_width B)
    have h := rank_mul_le_right Q B
    simpa only [hQB, rank_one, Fintype.card_fin] using h
  have hProjA : orthogonalProjector (toEuclideanLin A).range = A * P := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, ← hPA', A.mul_pinv_eq_starProjection]
  have hProjA' : orthogonalProjector (toEuclideanLin Aᴴ).range = 1 := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, ← A.pinv_mul_eq_starProjection, hPA', hPA]
  have hFit : (A * P) * B = A := by
    have hPB : P * B = 1 := by
      ext i j
      fin_cases i; fin_cases j; norm_num [B, P, Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.mul_assoc, hPB, Matrix.mul_one]
  refine ⟨A, B, ⟨?_, ?_⟩, ?_⟩
  · apply (theorem_6_13 A B).1.mpr
    apply (theorem_6_13 A B).2.mpr
    rw [hProjA, hFit, hA, hB]
    exact ⟨rfl, rfl⟩
  · apply (theorem_6_13_rows A B).1.mpr
    apply (theorem_6_13_rows A B).2.mpr
    rw [hProjA', Matrix.one_mul, rank_conjTranspose, hA, hB]
    exact ⟨rfl, rfl⟩
  · intro h
    rw [hPA', hQB'] at h
    have hz := congrArg (fun M : Matrix (Fin 1) (Fin 2) ℂ => M 0 1) h
    norm_num [A, B, P, Q, Matrix.mul_apply, Fin.sum_univ_two] at hz

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 17** of [benIsrael2003generalized], Chapter 6, Equation
(137), in spectral norm. The change in the pseudoinverse is at most
three times the larger squared pseudoinverse norm times the perturbation norm. -/
theorem theorem_6_17 (A B : Matrix m n ℂ) :
    ‖B.pinv - A.pinv‖ ≤ 3 * max (‖A.pinv‖ ^ 2) (‖B.pinv‖ ^ 2) * ‖B - A‖ := by
  let P := A.pinv
  let Q := B.pinv
  let E := B - A
  let X := 1 - A * P
  let Y := 1 - Q * B
  let M := max (‖P‖ ^ 2) (‖Q‖ ^ 2)
  have hX : ‖X‖ ≤ 1 := l2_opNorm_one_sub_mul_pinv_le_one A
  have hY : ‖Y‖ ≤ 1 := l2_opNorm_one_sub_pinv_mul_le_one B
  have hp : ‖P‖ ^ 2 ≤ M := le_max_left _ _
  have hq : ‖Q‖ ^ 2 ≤ M := le_max_right _ _
  have hpq : ‖Q‖ * ‖P‖ ≤ M := by nlinarith [sq_nonneg (‖Q‖ - ‖P‖)]
  have h1 : ‖-(Q * E * P)‖ ≤ ‖Q‖ * ‖E‖ * ‖P‖ := by
    rw [norm_neg]
    exact (l2_opNorm_mul (Q * E) P).trans
      (mul_le_mul_of_nonneg_right (l2_opNorm_mul Q E) (norm_nonneg _))
  have h2 : ‖(Q * Qᴴ) * Eᴴ * X‖ ≤ ‖Q‖ ^ 2 * ‖E‖ := by
    calc
      _ ≤ ‖(Q * Qᴴ) * Eᴴ‖ * ‖X‖ := l2_opNorm_mul _ _
      _ ≤ (‖Q‖ * ‖Qᴴ‖ * ‖Eᴴ‖) * 1 := by
        refine mul_le_mul ((l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))) hX
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [l2_opNorm_conjTranspose Q, l2_opNorm_conjTranspose E, mul_one, pow_two]
  have h3 : ‖Y * Eᴴ * (Pᴴ * P)‖ ≤ ‖E‖ * ‖P‖ ^ 2 := by
    calc
      _ ≤ ‖Y * Eᴴ‖ * ‖Pᴴ * P‖ := l2_opNorm_mul _ _
      _ ≤ (1 * ‖Eᴴ‖) * (‖Pᴴ‖ * ‖P‖) := by
        refine mul_le_mul ((l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right hY (norm_nonneg _))) (l2_opNorm_mul _ _)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [l2_opNorm_conjTranspose E, l2_opNorm_conjTranspose P, one_mul, pow_two]
  change ‖B.pinv - A.pinv‖ ≤ 3 * M * ‖E‖
  rw [pinv_sub_pinv_eq_wedin]
  change ‖-(Q * E * P) + (Q * Qᴴ) * Eᴴ * X + Y * Eᴴ * (Pᴴ * P)‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  have h12 := norm_add_le (-(Q * E * P)) ((Q * Qᴴ) * Eᴴ * X)
  nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg E),
    mul_le_mul_of_nonneg_right hq (norm_nonneg E),
    mul_le_mul_of_nonneg_right hpq (norm_nonneg E)]

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 17** of [benIsrael2003generalized], Chapter 6. The
factor-three perturbation bound holds for a compatible pair of
matrix seminorms under adjoints and multiplication by spectral
norm factors. The squared inverse norms give the scaling in (137). -/
theorem theorem_6_17_unitarilyInvariant
    (μ : Seminorm ℂ (Matrix m n ℂ)) (ν : Seminorm ℂ (Matrix n m ℂ))
    (hAdj : ∀ X : Matrix m n ℂ, ν Xᴴ = μ X)
    (hLeft : ∀ (L : Matrix n n ℂ) (X : Matrix n m ℂ), ν (L * X) ≤ ‖L‖ * ν X)
    (hRight : ∀ (X : Matrix n m ℂ) (R : Matrix m m ℂ), ν (X * R) ≤ ν X * ‖R‖)
    (hBoth : ∀ (L R : Matrix n m ℂ) (X : Matrix m n ℂ),
      ν (L * X * R) ≤ ‖L‖ * μ X * ‖R‖)
    (A B : Matrix m n ℂ) :
    ν (B.pinv - A.pinv) ≤ 3 * max (‖A.pinv‖ ^ 2) (‖B.pinv‖ ^ 2) * μ (B - A) := by
  let P := A.pinv
  let Q := B.pinv
  let E := B - A
  let X := 1 - A * P
  let Y := 1 - Q * B
  let C := max (‖P‖ ^ 2) (‖Q‖ ^ 2)
  have hX : ‖X‖ ≤ 1 := l2_opNorm_one_sub_mul_pinv_le_one A
  have hY : ‖Y‖ ≤ 1 := l2_opNorm_one_sub_pinv_mul_le_one B
  have hp : ‖P‖ ^ 2 ≤ C := le_max_left _ _
  have hq : ‖Q‖ ^ 2 ≤ C := le_max_right _ _
  have hpq : ‖Q‖ * ‖P‖ ≤ C := by nlinarith [sq_nonneg (‖Q‖ - ‖P‖)]
  have hPGram : ‖Pᴴ * P‖ ≤ ‖P‖ ^ 2 := by
    simpa only [l2_opNorm_conjTranspose, pow_two] using l2_opNorm_mul Pᴴ P
  have hQGram : ‖Q * Qᴴ‖ ≤ ‖Q‖ ^ 2 := by
    simpa only [l2_opNorm_conjTranspose, pow_two] using l2_opNorm_mul Q Qᴴ
  have h₁ : ν (-(Q * E * P)) ≤ ‖Q‖ * μ E * ‖P‖ := by
    rw [map_neg_eq_map]
    exact hBoth Q P E
  have h₂ : ν ((Q * Qᴴ) * Eᴴ * X) ≤ ‖Q‖ ^ 2 * μ E := by
    calc
      _ = ν ((Q * Qᴴ) * (Eᴴ * X)) := by rw [Matrix.mul_assoc (Q * Qᴴ) Eᴴ X]
      _ ≤ ‖Q * Qᴴ‖ * ν (Eᴴ * X) := hLeft _ _
      _ ≤ ‖Q‖ ^ 2 * (ν Eᴴ * ‖X‖) :=
        mul_le_mul hQGram (hRight Eᴴ X) (apply_nonneg ν _) (sq_nonneg _)
      _ ≤ ‖Q‖ ^ 2 * (μ E * 1) := by
        rw [hAdj E]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hX (apply_nonneg μ _)) (sq_nonneg _)
      _ = _ := by rw [mul_one]
  have h₃ : ν (Y * Eᴴ * (Pᴴ * P)) ≤ μ E * ‖P‖ ^ 2 := by
    calc
      _ ≤ ν (Y * Eᴴ) * ‖Pᴴ * P‖ := hRight _ _
      _ ≤ (‖Y‖ * ν Eᴴ) * ‖P‖ ^ 2 :=
        mul_le_mul (hLeft Y Eᴴ) hPGram (norm_nonneg _) (by positivity)
      _ ≤ (1 * μ E) * ‖P‖ ^ 2 := by
        rw [hAdj E]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hY (apply_nonneg μ _)) (sq_nonneg _)
      _ = _ := by rw [one_mul]
  change ν (B.pinv - A.pinv) ≤ 3 * C * μ E
  rw [pinv_sub_pinv_eq_wedin]
  change ν (-(Q * E * P) + (Q * Qᴴ) * Eᴴ * X + Y * Eᴴ * (Pᴴ * P)) ≤ _
  refine (map_add_le_add ν _ _).trans ?_
  have h12 := map_add_le_add ν (-(Q * E * P)) ((Q * Qᴴ) * Eᴴ * X)
  nlinarith [mul_le_mul_of_nonneg_right hp (apply_nonneg μ E),
    mul_le_mul_of_nonneg_right hq (apply_nonneg μ E),
    mul_le_mul_of_nonneg_right hpq (apply_nonneg μ E)]


open scoped Matrix.Norms.L2Operator in
/-- The mixed estimates used in Theorem 17 follow for two seminorms
represented by the same absolute gauge of the singular values. The common
gauge fixes the relative normalization of the two shapes. -/
theorem theorem_6_17_mixed_estimates_of_unitary_invariance {d : ℕ}
    (φ : Seminorm ℝ (Fin d → ℝ)) (hφ : ∀ x, φ (fun i => |x i|) = φ x)
    (μ : Seminorm ℂ (Matrix m n ℂ)) (ν : Seminorm ℂ (Matrix n m ℂ))
    (hμ : ∀ X, μ X = matrixGaugeValue φ X) (hν : ∀ X, ν X = matrixGaugeValue φ X) :
    (∀ X : Matrix m n ℂ, ν Xᴴ = μ X) ∧
      (∀ (L : Matrix n n ℂ) (X : Matrix n m ℂ), ν (L * X) ≤ ‖L‖ * ν X) ∧
      (∀ (X : Matrix n m ℂ) (R : Matrix m m ℂ), ν (X * R) ≤ ν X * ‖R‖) ∧
      (∀ (L R : Matrix n m ℂ) (X : Matrix m n ℂ), ν (L * X * R) ≤ ‖L‖ * μ X * ‖R‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    rw [hν, hμ, matrixGaugeValue_conjTranspose]
  · intro L X
    rw [hν, hν]
    exact matrixGaugeValue_mul_le_left φ hφ L X
  · intro X R
    rw [hν, hν]
    exact matrixGaugeValue_mul_le_right φ hφ X R
  · intro L R X
    rw [hν, hμ]
    exact (matrixGaugeValue_mul_le_right φ hφ (L * X) R).trans
      (mul_le_mul_of_nonneg_right (matrixGaugeValue_mul_le_left φ hφ L X) (norm_nonneg R))

open scoped Matrix.Norms.L2Operator in
/-- Theorem 17 with a common absolute gauge, using the squared spectral
norms of the inverse factors. -/
theorem theorem_6_17_commonGauge {d : ℕ}
    (φ : Seminorm ℝ (Fin d → ℝ)) (hφ : ∀ x, φ (fun i => |x i|) = φ x)
    (μ : Seminorm ℂ (Matrix m n ℂ)) (ν : Seminorm ℂ (Matrix n m ℂ))
    (hμ : ∀ X, μ X = matrixGaugeValue φ X) (hν : ∀ X, ν X = matrixGaugeValue φ X)
    (A B : Matrix m n ℂ) :
    ν (B.pinv - A.pinv) ≤ 3 * max (‖A.pinv‖ ^ 2) (‖B.pinv‖ ^ 2) * μ (B - A) := by
  obtain ⟨hAdj, hLeft, hRight, hBoth⟩ :=
    theorem_6_17_mixed_estimates_of_unitary_invariance φ hφ μ ν hμ hν
  exact theorem_6_17_unitarilyInvariant μ ν hAdj hLeft hRight hBoth A B

open scoped Matrix.Norms.Frobenius in
/-- **Theorem 17** of [benIsrael2003generalized], Chapter 6, Equation
(137), in the Frobenius norm with spectral norms on the inverse factors.
The constant two follows from orthogonality of the three corrections. -/
theorem theorem_6_17_frobenius (A B : Matrix m n ℂ) :
    ‖B.pinv - A.pinv‖ ≤ 2 * ‖B - A‖ *
      max (lpOpNorm 2 A.pinv ^ 2) (lpOpNorm 2 B.pinv ^ 2) := by
  have h := Matrix.frobenius_norm_pinv_sub_le A (B - A)
  rwa [add_sub_cancel] at h

section Continuity

open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- The spectral norm of the Moore–Penrose inverse is the reciprocal of
the smallest positive singular value of a positive-rank matrix. -/
theorem l2_opNorm_pinv_eq_inv_smallest_positive {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ)
    (hA : 0 < A.rank) : ‖A.pinv‖ = (A.sortedSingularValues (A.rank - 1))⁻¹ := by
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  have hn (i : ℕ) : ‖((A.sortedSingularValues i : ℂ)⁻¹)‖ = (A.sortedSingularValues i)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (A.sortedSingularValues_nonneg i)]
  have hr : A.rank - 1 < A.rank := Nat.sub_lt hA one_pos
  have hPos (i : ℕ) (hi : i < A.rank) : 0 < A.sortedSingularValues i :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg i)
      (Ne.symm (fun he => (not_le_of_gt hi) ((A.sortedSingularValues_eq_zero_iff_rank_le i).mp he)))
  rw [corollary_6_1 h, l2_opNorm_unitary_mul_mul_unitary h.1.mem_unitaryGroup_right _
    (conjTranspose_mem_unitaryGroup h.1.mem_unitaryGroup_left), l2_opNorm_rectDiagonal]
  apply le_antisymm
  · refine Real.iSup_le (fun i => ?_) (inv_nonneg.mpr (A.sortedSingularValues_nonneg _))
    rw [hn]
    by_cases hi : (i : ℕ) < A.rank
    · exact inv_anti₀ (hPos _ hr)
        (A.sortedSingularValues_antitone (Nat.le_sub_one_of_lt hi))
    · rw [(A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (Nat.le_of_not_gt hi),
        _root_.inv_zero]
      exact inv_nonneg.mpr (A.sortedSingularValues_nonneg _)
  · let i : Fin (min q p) := ⟨A.rank - 1, hr.trans_le (le_min A.rank_le_width A.rank_le_height)⟩
    let f (k : Fin (min q p)) := ‖((A.sortedSingularValues k : ℂ)⁻¹)‖
    change (A.sortedSingularValues (A.rank - 1))⁻¹ ≤ ⨆ k, f k
    exact (hn i).symm.trans_le (le_ciSup (f := f) (Set.finite_range _).bddAbove i)

/-- **Section 6.6** of [benIsrael2003generalized]. For matrices converging
to a fixed matrix, the Moore–Penrose inverses converge precisely when the
ranks eventually agree with the rank of the limit. -/
theorem pinv_converges_iff_eventually_rank_eq {p q : ℕ} {ι : Type*}
    {l : Filter ι} {B : ι → Matrix (Fin p) (Fin q) ℂ} {A : Matrix (Fin p) (Fin q) ℂ}
    (h : Tendsto B l (𝓝 A)) :
    Tendsto (fun i => (B i).pinv) l (𝓝 A.pinv) ↔ ∀ᶠ i in l, (B i).rank = A.rank := by
  have hE := tendsto_iff_norm_sub_tendsto_zero.mp h
  constructor
  · intro hPinv
    have hD := tendsto_iff_norm_sub_tendsto_zero.mp hPinv
    have he : ∀ᶠ i in l, ‖B i - A‖ < 1 := hE.eventually (gt_mem_nhds zero_lt_one)
    have hd : ∀ᶠ i in l, ‖(B i).pinv - A.pinv‖ < 1 := hD.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [he, hd] with i hi hj
    have hAc := isAcutePerturbation_of_small A (B i) hi hj
    exact ((theorem_6_13 A (B i)).2.mp ((theorem_6_13 A (B i)).1.mp hAc.1)).1.symm
  · intro hRank
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    rcases Nat.eq_zero_or_pos A.rank with h0 | hA
    · have hA0 := Matrix.rank_eq_zero_iff.mp h0
      have hz : (fun i => ‖(B i).pinv - A.pinv‖) =ᶠ[l] fun _ => (0 : ℝ) :=
        hRank.mono (fun i hi => by
          change ‖(B i).pinv - A.pinv‖ = 0
          rw [(Matrix.rank_eq_zero_iff.mp (hi.trans h0)).trans hA0.symm, sub_self, norm_zero])
      exact tendsto_const_nhds.congr' hz.symm
    · let a := A.sortedSingularValues (A.rank - 1)
      have ha : 0 < a := lt_of_le_of_ne (A.sortedSingularValues_nonneg _)
        (Ne.symm fun hz => (not_le_of_gt (Nat.sub_lt hA one_pos))
          ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp hz))
      let c := max (‖A.pinv‖ ^ 2) ((a / 2)⁻¹ ^ 2)
      have hsmall : ∀ᶠ i in l, ‖B i - A‖ < a / 2 :=
        hE.eventually (gt_mem_nhds (half_pos ha))
      have hbounds : ∀ᶠ i in l, ‖(B i).pinv - A.pinv‖ ≤ 3 * c * ‖B i - A‖ := by
        filter_upwards [hRank, hsmall] with i hi hs
        have hb := abs_sortedSingularValues_add_sub_le A (B i - A) (A.rank - 1)
        rw [add_sub_cancel, sortedSingularValues_zero_eq_l2_opNorm] at hb
        have hbσ : a / 2 ≤ (B i).sortedSingularValues (A.rank - 1) := by
          have he := neg_abs_le ((B i).sortedSingularValues (A.rank - 1) - a)
          change |(B i).sortedSingularValues (A.rank - 1) - a| ≤ ‖B i - A‖ at hb
          linarith
        have hbi : ‖(B i).pinv‖ ≤ (a / 2)⁻¹ := by
          rw [l2_opNorm_pinv_eq_inv_smallest_positive (B i) (hi ▸ hA), hi]
          exact inv_anti₀ (half_pos ha) hbσ
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hbi 2
        exact (theorem_6_17 A (B i)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (max_le_max le_rfl hsq) (by norm_num)) (norm_nonneg _))
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbounds ?_
      simpa only [mul_zero] using (tendsto_const_nhds (x := 3 * c) (f := l)).mul hE

/-- **Section 6.6** of [benIsrael2003generalized]. Along convergence to
the base matrix, eventual constant rank is equivalent to eventual
acuteness of the perturbations. -/
theorem eventually_isAcutePerturbation_iff_eventually_rank_eq {p q : ℕ} {ι : Type*}
    {l : Filter ι} {B : ι → Matrix (Fin p) (Fin q) ℂ} {A : Matrix (Fin p) (Fin q) ℂ}
    (h : Tendsto B l (𝓝 A)) :
    (∀ᶠ i in l, IsAcutePerturbation A (B i)) ↔ (∀ᶠ i in l, (B i).rank = A.rank) := by
  constructor
  · intro ha
    filter_upwards [ha] with i hi
    exact ((theorem_6_13 A (B i)).2.mp ((theorem_6_13 A (B i)).1.mp hi.1)).1.symm
  · intro hr
    have hD := (pinv_converges_iff_eventually_rank_eq h).mpr hr
    have he := (tendsto_iff_norm_sub_tendsto_zero.mp h).eventually (gt_mem_nhds zero_lt_one)
    have hd := (tendsto_iff_norm_sub_tendsto_zero.mp hD).eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [he, hd] with i hi hj
    exact isAcutePerturbation_of_small A (B i) hi hj

/-- The Moore–Penrose inverse is continuous on each fixed-rank stratum. -/
theorem continuousOn_pinv_rank_eq {p q : ℕ} (r : ℕ) :
    ContinuousOn (fun A : Matrix (Fin p) (Fin q) ℂ => A.pinv) {A | A.rank = r} := by
  intro A hA
  have h := tendsto_id.mono_left (nhdsWithin_le_nhds (s := {A : Matrix (Fin p) (Fin q) ℂ |
    A.rank = r}) (a := A))
  apply (pinv_converges_iff_eventually_rank_eq h).mpr
  have he := self_mem_nhdsWithin (a := A) (s := {A : Matrix (Fin p) (Fin q) ℂ | A.rank = r})
  filter_upwards [he] with B hB
  exact hB.trans hA.symm

/-- **Equation (128)** of [benIsrael2003generalized], Chapter 6. A
rank-two diagonal sequence can converge to a rank-one matrix while its
Moore–Penrose inverses fail to converge to the limiting pseudoinverse. -/
theorem pinv_rankJump_example :
    let A : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]
    let B (i : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1 / ((i : ℂ) + 1)]
    Tendsto B atTop (𝓝 A) ∧ ¬ Tendsto (fun i => (B i).pinv) atTop (𝓝 A.pinv) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]
  let B (i : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 1 / ((i : ℂ) + 1)]
  have hA : A.rank = 1 := by
    change (diagonal (![1, 0] : Fin 2 → ℂ)).rank = 1
    rw [rank_diagonal, Fintype.card_subtype]
    have he : Finset.univ.filter (fun i : Fin 2 => (![1, 0] : Fin 2 → ℂ) i ≠ 0) = {0} := by
      ext i
      fin_cases i <;> simp
    rw [he, Finset.card_singleton]
  have hB (i : ℕ) : (B i).rank = 2 := by
    have hUnit : IsUnit (B i) := by
      apply (isUnit_iff_isUnit_det _).mpr
      rw [isUnit_iff_ne_zero]
      change (diagonal (![1, 1 / ((i : ℂ) + 1)] : Fin 2 → ℂ)).det ≠ 0
      rw [det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, one_mul, Matrix.cons_val_one]
      apply one_div_ne_zero
      exact_mod_cast Nat.succ_ne_zero i
    exact (rank_of_isUnit _ hUnit).trans (Fintype.card_fin _)
  have hc : Tendsto B atTop (𝓝 A) := by
    have h : Tendsto (fun i : ℕ => ![(1 : ℂ), 1 / ((i : ℂ) + 1)]) atTop (𝓝 ![1, 0]) := by
      rw [tendsto_pi_nhds]
      intro i
      fin_cases i
      · exact tendsto_const_nhds
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    exact continuous_id.matrix_diagonal.continuousAt.tendsto.comp h
  refine ⟨hc, fun hp => ?_⟩
  have hr := (pinv_converges_iff_eventually_rank_eq hc).mp hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hr
  have he := hN N le_rfl
  rw [hA, hB] at he
  norm_num at he

end Continuity

section Exercises

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 77** of [benIsrael2003generalized], Chapter 6, Equations
(127), (138), in spectral norm. A small perturbation of an invertible
matrix has the stated geometric-series inverse. -/
theorem exercise_6_77 (A E : Matrix n n ℂ) (hA : IsUnit A)
    (hE : ‖A⁻¹‖ * ‖E‖ < 1) :
    IsUnit (A + E) ∧ (A + E)⁻¹ = (∑' i : ℕ, (-(A⁻¹ * E)) ^ i) * A⁻¹ := by
  let W := -(A⁻¹ * E)
  have hW : ‖W‖ < 1 := by
    change ‖-(A⁻¹ * E)‖ < 1
    rw [norm_neg]
    exact (norm_mul_le _ _).trans_lt hE
  have hQ : IsUnit (1 - W) := isUnit_one_sub_of_norm_lt_one hW
  have hEq : A + E = A * (1 - W) := by
    change A + E = A * (1 - -(A⁻¹ * E))
    rw [sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA), Matrix.one_mul]
  refine ⟨hEq.symm ▸ hA.mul hQ, ?_⟩
  change (A + E)⁻¹ = (∑' i : ℕ, W ^ i) * A⁻¹
  rw [hEq, Introduction.inv_mul hA hQ, nonsing_inv_eq_ringInverse (1 - W),
    NormedRing.inverse_one_sub W hW]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 77** of [benIsrael2003generalized], Chapter 6. Any
submultiplicative algebra norm can certify the Neumann expansion.
The matrices in the series use their finite-dimensional topology. -/
theorem exercise_6_77_multiplicative (N : AlgebraNorm ℂ (Matrix n n ℂ))
    (A E : Matrix n n ℂ) (hA : IsUnit A) (hE : N A⁻¹ * N E < 1) :
    IsUnit (A + E) ∧ (A + E)⁻¹ = (∑' i : ℕ, (-(A⁻¹ * E)) ^ i) * A⁻¹ := by
  let W := -(A⁻¹ * E)
  have hW : N W < 1 := by
    change N (-(A⁻¹ * E)) < 1
    rw [map_neg_eq_map]
    exact (map_mul_le_mul N _ _).trans_lt hE
  have hQ : IsUnit (1 - W) := isUnit_one_sub_of_algebraNorm_lt_one N hW
  have hEq : A + E = A * (1 - W) := by
    change A + E = A * (1 - -(A⁻¹ * E))
    rw [sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA), Matrix.one_mul]
  refine ⟨hEq.symm ▸ hA.mul hQ, ?_⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · let _ := hn
    exact Subsingleton.elim _ _
  · let _ := hn
    have hs : spectralRadius ℂ W < 1 := (spectralRadius_le_algebraNorm N W).trans_lt
      (ENNReal.ofReal_lt_one.mpr hW)
    change (A + E)⁻¹ = (∑' i : ℕ, W ^ i) * A⁻¹
    rw [hEq, Introduction.inv_mul hA hQ, nonsing_inv_eq_ringInverse (1 - W),
      (hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one hs).tsum_eq]

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 78** of [benIsrael2003generalized], Chapter 6, Equation
(139). The Fréchet derivative of matrix inversion at an invertible
matrix acts by multiplication by the two inverse factors and a minus sign. -/
theorem exercise_6_78 (A : Matrix n n ℂ) (hA : IsUnit A) :
    HasFDerivAt (fun M : Matrix n n ℂ => M⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) A⁻¹ A⁻¹) A := by
  obtain ⟨u, rfl⟩ := hA
  simpa only [nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    hasFDerivAt_ringInverse (𝕜 := ℂ) u

open scoped Matrix.Norms.L2Operator in
/-- **Section 6.6** of [benIsrael2003generalized]. The nonsingular
square matrices form an open set on which matrix inversion is continuous. -/
theorem isOpen_nonsingular :
    IsOpen {A : Matrix n n ℂ | IsUnit A} ∧
      ContinuousOn (fun A : Matrix n n ℂ => A⁻¹) {A | IsUnit A} :=
  ⟨Units.isOpen, fun A hA => (exercise_6_78 A hA).continuousAt.continuousWithinAt⟩

omit [DecidableEq m] in
open scoped Matrix.Norms.Frobenius in
/-- **Exercise 79** of [benIsrael2003generalized], Chapter 6. The sum
of squares of singular values beyond the original rank is bounded
by the squared Frobenius norm of the perturbation. -/
theorem exercise_6_79 (A E : Matrix m n ℂ) :
    ∑ i ∈ Finset.Ico A.rank (Fintype.card n), (A + E).sortedSingularValues i ^ 2 ≤ ‖E‖ ^ 2 := by
  have h := sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le
    (C := A + E) (Ĉ := A) (le_refl A.rank)
  rw [add_sub_cancel_left] at h
  rw [← Finset.sum_Ico_consecutive _ (le_min (rank_le_card_height A) (rank_le_card_width A))
    (min_le_right _ _)]
  have hz : ∑ i ∈ Finset.Ico (min (Fintype.card m) (Fintype.card n)) (Fintype.card n),
      (A + E).sortedSingularValues i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [sortedSingularValues_eq_zero_of_min_le _ (Finset.mem_Ico.mp hi).1,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rwa [hz, add_zero]

omit [DecidableEq m] in
private theorem mul_pinv_mul_eq_of_range_le (A E : Matrix m n ℂ)
    (h : (toEuclideanLin E).range ≤ (toEuclideanLin A).range) :
    A * A.pinv * E = E := by
  classical
  apply toEuclideanLin.injective
  rw [toEuclideanLin_mul, A.mul_pinv_eq_starProjection]
  ext1 x
  rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.mpr (h (LinearMap.mem_range_self _ _))

private theorem supported_pinv_eq_inv_mul (A E : Matrix m n ℂ)
    (hL : (toEuclideanLin E).range ≤ (toEuclideanLin A).range)
    (hR : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range)
    (hQ : IsUnit (1 + A.pinv * E)) :
    (A + E).pinv = (1 + A.pinv * E)⁻¹ * A.pinv := by
  let P := A.pinv
  let Q := 1 + P * E
  let B := A + E
  let X := Q⁻¹ * P
  change IsUnit Q at hQ
  have heL : A * P * E = E := mul_pinv_mul_eq_of_range_le A E hL
  have heR : E * P * A = E := by
    have he := congrArg Matrix.conjTranspose (mul_pinv_mul_eq_of_range_le Aᴴ Eᴴ hR)
    simpa only [conjTranspose_mul, pinv_conjTranspose, conjTranspose_conjTranspose,
      Matrix.mul_assoc] using he
  have hInvR := mul_nonsing_inv Q ((isUnit_iff_isUnit_det Q).mp hQ)
  have hInvL := nonsing_inv_mul Q ((isUnit_iff_isUnit_det Q).mp hQ)
  have hB : B = A * Q := by
    change A + E = A * (1 + P * E)
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, heL]
  have hQPA : Q * (P * A) = P * A + P * E := by
    change (1 + P * E) * (P * A) = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc P E (P * A),
      ← Matrix.mul_assoc E P A, heR]
  have hPAQ : (P * A) * Q = P * A + P * E := by
    change (P * A) * (1 + P * E) = _
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc (P * A) P E,
      A.pinv_mul_self_mul_pinv]
  have hBX : B * X = A * P := by
    calc
      B * X = (A * Q) * (Q⁻¹ * P) := congrArg (· * X) hB
      _ = A * (Q * Q⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hInvR, Matrix.mul_one]
  have hXB : X * B = P * A := by
    calc
      X * B = (Q⁻¹ * P) * (A * Q) := congrArg (X * ·) hB
      _ = Q⁻¹ * ((P * A) * Q) := by simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (Q * (P * A)) := by rw [hPAQ, hQPA]
      _ = _ := by rw [← Matrix.mul_assoc, hInvL, Matrix.one_mul]
  change B.pinv = X
  symm
  refine B.pinv_unique ?_ ?_ (hBX ▸ A.isHermitian_mul_pinv) (hXB ▸ A.isHermitian_pinv_mul)
  · rw [hBX]
    change A * P * (A + E) = A + E
    rw [Matrix.mul_add, A.mul_pinv_mul_self, heL]
  · rw [Matrix.mul_assoc, hBX]
    change (Q⁻¹ * P) * (A * P) = Q⁻¹ * P
    rw [Matrix.mul_assoc Q⁻¹, ← Matrix.mul_assoc P A P, A.pinv_mul_self_mul_pinv]

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 80** of [benIsrael2003generalized], Chapter 6, Equations
(140)–(143), in spectral norm. A perturbation supported in the original
row and column spaces has the stated inverse formula. -/
theorem exercise_6_80 (A E : Matrix m n ℂ)
    (hL : (toEuclideanLin E).range ≤ (toEuclideanLin A).range)
    (hR : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range)
    (hSmall : ‖A.pinv * E‖ < 1) :
    (A + E).pinv = (1 + A.pinv * E)⁻¹ * A.pinv := by
  apply supported_pinv_eq_inv_mul A E hL hR
  rw [← sub_neg_eq_add]
  exact isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])

/-- **Exercise 80** of [benIsrael2003generalized], Chapter 6. The
supported perturbation formula holds under the smallness condition
measured in any submultiplicative algebra norm on the square factor. -/
theorem exercise_6_80_multiplicative (N : AlgebraNorm ℂ (Matrix n n ℂ))
    (A E : Matrix m n ℂ)
    (hL : (toEuclideanLin E).range ≤ (toEuclideanLin A).range)
    (hR : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range)
    (hSmall : N (A.pinv * E) < 1) :
    (A + E).pinv = (1 + A.pinv * E)⁻¹ * A.pinv := by
  apply supported_pinv_eq_inv_mul A E hL hR
  rw [← sub_neg_eq_add]
  exact isUnit_one_sub_of_algebraNorm_lt_one N (by rwa [map_neg_eq_map])

omit [DecidableEq m] in
private theorem range_le_of_mul_pinv_mul_eq (A E : Matrix m n ℂ)
    (h : A * A.pinv * E = E) : (toEuclideanLin E).range ≤ (toEuclideanLin A).range := by
  have he := h
  rw [Matrix.mul_assoc] at he
  conv_lhs => rw [← he, toEuclideanLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- **Exercise 80** of [benIsrael2003generalized], Chapter 6. For the
invertible square factor used in (143), the forward factorization
and the Moore–Penrose reverse-order formula together characterize
the two range inclusions. -/
theorem exercise_6_80_support_iff (A E : Matrix m n ℂ)
    (hW : IsUnit (1 + A.pinv * E)) :
    let W := 1 + A.pinv * E
    ((A + E = A * W) ∧ (A + E).pinv = W⁻¹ * A.pinv) ↔
      (toEuclideanLin E).range ≤ (toEuclideanLin A).range ∧
        (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range := by
  let P := A.pinv
  let K := P * E
  let W := 1 + K
  let D := P * A
  let J := 1 - D
  have hW₀ : IsUnit W := hW
  have hInv := mul_nonsing_inv W ((isUnit_iff_isUnit_det _).mp hW₀)
  have hInvAdj : (W⁻¹)ᴴ * Wᴴ = 1 := by
    simpa only [conjTranspose_mul, conjTranspose_one] using congrArg Matrix.conjTranspose hInv
  have hWD : A * W = A + A * P * E := by
    change A * (1 + P * E) = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc A P E]
  change (A + E = A * W ∧ (A + E).pinv = W⁻¹ * P) ↔ _
  constructor
  · rintro ⟨hFac, hPinv⟩
    have he : A * P * E = E := (add_left_cancel (hFac.trans hWD)).symm
    refine ⟨range_le_of_mul_pinv_mul_eq A E he, ?_⟩
    have hD : D.IsHermitian := A.isHermitian_pinv_mul
    have hDD : D * D = D := by
      change (P * A) * (P * A) = P * A
      rw [← Matrix.mul_assoc (P * A) P A, A.pinv_mul_self_mul_pinv]
    have hJ : J.IsHermitian := isHermitian_one.sub hD
    have hDJ : D * J = 0 := by
      change D * (1 - D) = 0
      rw [Matrix.mul_sub, Matrix.mul_one, hDD, sub_self]
    have hJP : J * P = 0 := by
      change (1 - P * A) * P = 0
      rw [Matrix.sub_mul, Matrix.one_mul, A.pinv_mul_self_mul_pinv, sub_self]
    have hJW : J * W = J := by
      change J * (1 + P * E) = J
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hJP, Matrix.zero_mul, add_zero]
    have hWJ : Wᴴ * J = J := by
      simpa only [conjTranspose_mul, hJ.eq] using congrArg Matrix.conjTranspose hJW
    have hHerm : (W⁻¹ * D * W).IsHermitian := by
      have hp := (A + E).isHermitian_pinv_mul
      rw [hPinv, hFac] at hp
      simpa only [D, Matrix.mul_assoc] using hp
    have hC : D * W * Wᴴ = W * Wᴴ * D := by
      calc
        _ = W * (W⁻¹ * (D * W)) * Wᴴ := by rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]
        _ = W * (W⁻¹ * D * W)ᴴ * Wᴴ := by rw [hHerm.eq, Matrix.mul_assoc W⁻¹ D W]
        _ = (W * Wᴴ) * D * ((W⁻¹)ᴴ * Wᴴ) := by
          rw [conjTranspose_mul, conjTranspose_mul, hD.eq]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hInvAdj, Matrix.mul_one]
    have hDZ : D * W * J = 0 := by
      calc
        _ = (D * W * Wᴴ) * J := by rw [Matrix.mul_assoc (D * W) Wᴴ J, hWJ]
        _ = (W * Wᴴ) * (D * J) := by rw [hC, Matrix.mul_assoc (W * Wᴴ) D J]
        _ = _ := by rw [hDJ, Matrix.mul_zero]
    have hDK : D * W = D + K := by
      change (P * A) * (1 + P * E) = (P * A) + (P * E)
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc (P * A) P E,
        A.pinv_mul_self_mul_pinv]
    have hKD : K * D = K := by
      rw [hDK, Matrix.add_mul, hDJ, zero_add] at hDZ
      change K * (1 - D) = 0 at hDZ
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hDZ
      exact hDZ.symm
    have hAK : A * K = E := by
      change A * (P * E) = E
      rw [← Matrix.mul_assoc, he]
    have hED : E * D = E := by
      calc
        _ = (A * K) * D := by rw [hAK]
        _ = A * K := by rw [Matrix.mul_assoc, hKD]
        _ = _ := hAK
    apply range_le_of_mul_pinv_mul_eq Aᴴ Eᴴ
    have hAdj := congrArg Matrix.conjTranspose hED
    simpa only [conjTranspose_mul, D, P, pinv_conjTranspose] using hAdj
  · rintro ⟨hL, hR⟩
    exact ⟨by rw [hWD, mul_pinv_mul_eq_of_range_le A E hL],
      supported_pinv_eq_inv_mul A E hL hR hW⟩

private theorem algebraNorm_inverse_one_add_sub_one_le
    (N : AlgebraNorm ℂ (Matrix n n ℂ)) (C : Matrix n n ℂ) (hC : N C < 1) :
    N ((1 + C)⁻¹ - 1) ≤ N C / (1 - N C) := by
  have hQ : IsUnit (1 + C) := by
    rw [← sub_neg_eq_add]
    exact isUnit_one_sub_of_algebraNorm_lt_one N (by rwa [map_neg_eq_map])
  let Z := (1 + C)⁻¹ - 1
  have hi : (1 + C)⁻¹ + C * (1 + C)⁻¹ = 1 := by
    have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hQ)
    simpa only [Matrix.add_mul, Matrix.one_mul] using h
  have hcZ : C + C * Z = C * (1 + C)⁻¹ := by
    dsimp [Z]
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  have hZ : Z = -(C + C * Z) := by
    rw [hcZ]
    calc
      _ = (1 + C)⁻¹ - ((1 + C)⁻¹ + C * (1 + C)⁻¹) :=
        congrArg ((1 + C)⁻¹ - ·) hi.symm
      _ = _ := by abel
  have hb : N Z ≤ N C + N C * N Z := by
    calc
      _ = N (C + C * Z) := (congrArg N hZ).trans (map_neg_eq_map N _)
      _ ≤ N C + N (C * Z) := map_add_le_add N _ _
      _ ≤ _ := add_le_add_right (map_mul_le_mul N _ _) _
  change N Z ≤ _
  apply (le_div_iff₀ (sub_pos.mpr hC)).mpr
  nlinarith

/-- **Exercise 81** of [benIsrael2003generalized], Chapter 6. Both
supported perturbation bounds hold for compatible matrix norms.
The second condition implies the smallness condition for the first
bound by submultiplicativity. -/
theorem exercise_6_81_multiplicative (N : AlgebraNorm ℂ (Matrix n n ℂ))
    (μ : Seminorm ℂ (Matrix m n ℂ)) (ν : Seminorm ℂ (Matrix n m ℂ))
    (hRect : ∀ (P : Matrix n m ℂ) (E : Matrix m n ℂ), N (P * E) ≤ ν P * μ E)
    (hSquare : ∀ (Q : Matrix n n ℂ) (P : Matrix n m ℂ), ν (Q * P) ≤ N Q * ν P)
    (A E : Matrix m n ℂ)
    (hL : (toEuclideanLin E).range ≤ (toEuclideanLin A).range)
    (hR : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range) :
    (N (A.pinv * E) < 1 →
      ν ((A + E).pinv - A.pinv) ≤ N (A.pinv * E) * ν A.pinv / (1 - N (A.pinv * E))) ∧
    (ν A.pinv * μ E < 1 →
      ν ((A + E).pinv - A.pinv) ≤ ν A.pinv ^ 2 * μ E / (1 - N (A.pinv * E))) := by
  let P := A.pinv
  let C := P * E
  have h₁ (hSmall : N C < 1) :
      ν ((A + E).pinv - P) ≤ N C * ν P / (1 - N C) := by
    have hf := exercise_6_80_multiplicative N A E hL hR hSmall
    change (A + E).pinv = (1 + C)⁻¹ * P at hf
    have he : (A + E).pinv - P = ((1 + C)⁻¹ - 1) * P := by
      rw [hf, Matrix.sub_mul, Matrix.one_mul]
    rw [he]
    refine (hSquare _ _).trans ?_
    rw [← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right (algebraNorm_inverse_one_add_sub_one_le N C hSmall)
      (apply_nonneg ν P)
  refine ⟨h₁, fun hStrong => ?_⟩
  have hc : N C ≤ ν P * μ E := hRect _ _
  have hSmall := hc.trans_lt hStrong
  refine (h₁ hSmall).trans (div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hSmall.le))
  calc
    N C * ν P ≤ (ν P * μ E) * ν P := mul_le_mul_of_nonneg_right hc (apply_nonneg ν P)
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 81** of [benIsrael2003generalized], Chapter 6, Equations
(146)–(148), in spectral norm. The supported perturbation error uses
the geometric-series bound with denominator $1-\|A^\dagger E\|_2$. -/
theorem exercise_6_81 (A E : Matrix m n ℂ)
    (hL : (toEuclideanLin E).range ≤ (toEuclideanLin A).range)
    (hR : (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range)
    (hSmall : ‖A.pinv * E‖ < 1) :
    ‖(A + E).pinv - A.pinv‖ ≤ ‖A.pinv * E‖ * ‖A.pinv‖ / (1 - ‖A.pinv * E‖) ∧
    ‖(A + E).pinv - A.pinv‖ ≤ ‖A.pinv‖ ^ 2 * ‖E‖ / (1 - ‖A.pinv * E‖) := by
  let P := A.pinv
  let W := -(P * E)
  have hW : ‖W‖ < 1 := by simpa only [W, norm_neg] using hSmall
  have h := NormedRing.norm_inverse_one_sub_sub_one_le hW
  change ‖Ring.inverse (1 - -(P * E)) - 1‖ ≤ ‖-(P * E)‖ / (1 - ‖-(P * E)‖) at h
  rw [← nonsing_inv_eq_ringInverse, sub_neg_eq_add, norm_neg] at h
  have hEq := exercise_6_80 A E hL hR hSmall
  have hDiff : (A + E).pinv - P = ((1 + P * E)⁻¹ - 1) * P := by
    rw [hEq, Matrix.sub_mul, Matrix.one_mul]
  have hb : ‖(A + E).pinv - P‖ ≤ ‖P * E‖ * ‖P‖ / (1 - ‖P * E‖) := by
    rw [hDiff]
    refine (l2_opNorm_mul _ _).trans ?_
    rw [← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  refine ⟨hb, hb.trans (div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hSmall.le))⟩
  calc
    ‖P * E‖ * ‖P‖ ≤ (‖P‖ * ‖E‖) * ‖P‖ :=
      mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖P‖ ^ 2 * ‖E‖ := by ring

private theorem pinv_smul_one_fin_one {z : ℂ} (hz : z ≠ 0) :
    ((z • (1 : Matrix (Fin 1) (Fin 1) ℂ))).pinv =
      z⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  let I : Matrix (Fin 1) (Fin 1) ℂ := 1
  have h₁ : (z • I) * (z⁻¹ • I) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
    exact Matrix.one_mul _
  have h₂ : (z⁻¹ • I) * (z • I) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul]
    exact Matrix.one_mul _
  symm
  refine (z • I).pinv_unique ?_ ?_ ?_ ?_
  · rw [h₁, Matrix.one_mul]
  · rw [h₂, Matrix.one_mul]
  · rw [h₁]
    exact isHermitian_one
  · rw [h₂]
    exact isHermitian_one

open scoped Matrix.Norms.L2Operator in
/-- The unsquared version of **Equation (137)** in
[benIsrael2003generalized], Chapter 6, already fails for scalar matrices. -/
theorem theorem_6_17_unsquared_counterexample :
    ∃ A B : Matrix (Fin 1) (Fin 1) ℂ,
      3 * max ‖A.pinv‖ ‖B.pinv‖ * ‖B - A‖ < ‖B.pinv - A.pinv‖ := by
  let I : Matrix (Fin 1) (Fin 1) ℂ := 1
  let A := (1 / 8 : ℂ) • I
  let B := (1 / 4 : ℂ) • I
  have ha : A.pinv = (8 : ℂ) • I := by
    change ((1 / 8 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).pinv = _
    rw [pinv_smul_one_fin_one (by norm_num)]
    norm_num [I]
  have hb : B.pinv = (4 : ℂ) • I := by
    change ((1 / 4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).pinv = _
    rw [pinv_smul_one_fin_one (by norm_num)]
    norm_num [I]
  have he : B - A = (1 / 8 : ℂ) • I := by
    change (1 / 4 : ℂ) • I - (1 / 8 : ℂ) • I = _
    rw [← sub_smul, show (1 / 4 - 1 / 8 : ℂ) = 1 / 8 by norm_num]
  have hd : B.pinv - A.pinv = (-4 : ℂ) • I := by
    rw [ha, hb, ← sub_smul]
    norm_num
  refine ⟨A, B, ?_⟩
  rw [hd, ha, hb, he]
  norm_num [norm_smul, I, norm_div, max_eq_left]

open scoped Matrix.Norms.L2Operator in
/-- In **Exercise 81** of [benIsrael2003generalized], Chapter 6, an acute
perturbation supported in both original ranges can still violate the
smallness hypothesis (142). -/
theorem exercise_6_81_smallness_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℂ := 1
    let E : Matrix (Fin 1) (Fin 1) ℂ := (2 : ℂ) • 1
    IsAcutePerturbation A (A + E) ∧
      (toEuclideanLin E).range ≤ (toEuclideanLin A).range ∧
      (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Aᴴ).range ∧ 1 ≤ ‖A.pinv * E‖ := by
  let I : Matrix (Fin 1) (Fin 1) ℂ := 1
  let E := (2 : ℂ) • I
  have hB : I + E = (3 : ℂ) • I := by
    change I + (2 : ℂ) • I = _
    calc
      _ = (1 : ℂ) • I + (2 : ℂ) • I :=
        congrArg (fun T => T + (2 : ℂ) • I) (one_smul ℂ I).symm
      _ = _ := by rw [← add_smul, show (1 + 2 : ℂ) = 3 by norm_num]
  have hU : IsUnit (I + E) := by
    rw [hB]
    apply (isUnit_iff_isUnit_det _).mpr
    apply isUnit_det_of_right_inverse (B := (3 : ℂ)⁻¹ • I)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul]
    exact Matrix.one_mul _
  have hU' : IsUnit (I + E)ᴴ := hU.star
  have hTop : (toEuclideanLin I).range = ⊤ := range_toEuclideanLin_eq_top_of_isUnit isUnit_one
  have hTop' : (toEuclideanLin Iᴴ).range = ⊤ := by simp [I]
  have hRec : I.pinv = I := by
    have h := pinv_smul_one_fin_one (z := 1) one_ne_zero
    simpa [I] using h
  change IsAcutePerturbation I (I + E) ∧
    (toEuclideanLin E).range ≤ (toEuclideanLin I).range ∧
    (toEuclideanLin Eᴴ).range ≤ (toEuclideanLin Iᴴ).range ∧ 1 ≤ ‖I.pinv * E‖
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsAcutePerturbation, hTop, hTop', range_toEuclideanLin_eq_top_of_isUnit hU,
      range_toEuclideanLin_eq_top_of_isUnit hU']
    simp [subspaceDistance]
  · rw [hTop]; exact le_top
  · rw [hTop']; exact le_top
  · rw [hRec, show I = 1 from rfl, Matrix.one_mul]
    norm_num [E, I, norm_smul]

end Exercises

end BenIsraelGreville.Chapter06
