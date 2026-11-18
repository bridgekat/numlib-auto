/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section09
import Numlib.LinearAlgebra.Matrix.Jordan
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Other spectral generalized inverses

Section 4.10 of [benIsrael2003generalized] studies strong spectral and
least-squares inverses and gives exercises on the nilpotent part.

## Deviations from the source

* Exercise 50 uses the nilpotent part of the proposed inverse in the
  right-hand Penrose condition, correcting the repeated original part.
* The converse grade statement is in general unavailable for the
  extension in Exercise 52. Its behavior on generalized nonzero
  eigenvectors of the original matrix is given by the forward transfer.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A strong spectral inverse is obtained by taking the Moore–Penrose
inverse in Jordan coordinates and transporting it by the same similarity. -/
def AreStrongSpectralInverses (A X : Matrix n n ℂ) : Prop :=
  ∃ (k : ℕ) (e : Fin k → ℕ) (c : Fin k → ℂ)
    (r : ((i : Fin k) × Fin (e i)) ≃ n) (P : (Matrix n n ℂ)ˣ),
      (∀ i, 0 < e i) ∧
      let J := (jordanForm e c).reindex r r
      A = (P : Matrix n n ℂ) * J * (↑P⁻¹ : Matrix n n ℂ) ∧
        X = (P : Matrix n n ℂ) * J.pinv * (↑P⁻¹ : Matrix n n ℂ)

private theorem jordanBlock_zero_mul_conjTranspose (k : ℕ) :
    jordanBlock k (0 : ℂ) * (jordanBlock k (0 : ℂ))ᴴ =
      diagonal (fun i : Fin k => if (i : ℕ) + 1 < k then 1 else 0) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) + 1 < k
  · let q : Fin k := ⟨(i : ℕ) + 1, hi⟩
    rw [Finset.sum_eq_single q]
    · by_cases hij : i = j
      · subst j
        simp [jordanBlock_zero_apply, conjTranspose_apply, q, hi]
      · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
        simp [jordanBlock_zero_apply, conjTranspose_apply, q, hne, diagonal_apply_ne _ hij]
    · intro b _ hb
      have hne : (i : ℕ) + 1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [jordanBlock_zero_apply, hne]
    · simp
  · rw [diagonal_apply]
    simp only [hi, ite_false, ite_self]
    apply Finset.sum_eq_zero
    intro b _
    have hne : (i : ℕ) + 1 ≠ (b : ℕ) := by have := b.isLt; omega
    simp [jordanBlock_zero_apply, hne]

private theorem jordanBlock_zero_pinv (k : ℕ) :
    (jordanBlock k (0 : ℂ)).pinv = (jordanBlock k (0 : ℂ))ᴴ := by
  let Z := jordanBlock k (0 : ℂ)
  have h₁ : Z * Zᴴ * Z = Z := by
    unfold Z
    rw [jordanBlock_zero_mul_conjTranspose]
    ext i j
    rw [diagonal_mul]
    by_cases hi : (i : ℕ) + 1 < k
    · simp [hi]
    · have hne : (i : ℕ) + 1 ≠ (j : ℕ) := by have := j.isLt; omega
      simp [hi, jordanBlock_zero_apply, hne]
  have h₂ : Zᴴ * Z * Zᴴ = Zᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
      using congrArg Matrix.conjTranspose h₁
  exact (Z.pinv_unique h₁ h₂ (isHermitian_mul_conjTranspose_self Z)
    (isHermitian_conjTranspose_mul_self Z)).symm

private theorem jordanBlock_zero_pow_eq_zero (k l : ℕ) (h : k ≤ l) :
    jordanBlock k (0 : ℂ) ^ l = 0 := by
  ext i j
  have hne : (i : ℕ) + l ≠ (j : ℕ) := by have := j.isLt; omega
  simp [jordanBlock_zero_pow_apply, hne]

private theorem jordanBlock_pow_commute_pinv (k l : ℕ) (h : k ≤ l) (μ : ℂ) :
    Commute (jordanBlock k μ ^ l) (jordanBlock k μ).pinv ∧
      Commute (jordanBlock k μ) ((jordanBlock k μ).pinv ^ l) := by
  by_cases hz : μ = 0
  · subst μ
    rw [jordanBlock_zero_pinv, jordanBlock_zero_pow_eq_zero k l h,
      ← conjTranspose_pow, jordanBlock_zero_pow_eq_zero k l h, conjTranspose_zero]
    exact ⟨Commute.zero_left _, Commute.zero_right _⟩
  · let B := jordanBlock k μ
    have hB : IsUnit B := Matrix.mulVec_injective_iff_isUnit.mp
      (LinearMap.ker_eq_bot.mp (by
        simpa only [pow_one] using ker_mulVecLin_jordanBlock_pow_eq_bot (n := k) hz 1))
    have hc : Commute B B.pinv := by
      change B * B.pinv = B.pinv * B
      have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hB
      rw [pinv_eq_inv hB, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet]
    exact ⟨hc.pow_left l, hc.pow_right l⟩

private theorem pinv_blockDiagonal_jordan {k : ℕ} (e : Fin k → ℕ) (μ : Fin k → ℂ) :
    (jordanForm e μ).pinv = blockDiagonal' (fun i => (jordanBlock (e i) (μ i)).pinv) := by
  let B (i : Fin k) := jordanBlock (e i) (μ i)
  rw [jordanForm_def]
  change (blockDiagonal' B).pinv = _
  symm
  apply (blockDiagonal' B).pinv_unique
  · simp only [← blockDiagonal'_mul]
    exact congrArg blockDiagonal' (funext fun i => (B i).mul_pinv_mul_self)
  · simp only [← blockDiagonal'_mul]
    exact congrArg blockDiagonal' (funext fun i => (B i).pinv_mul_self_mul_pinv)
  · rw [← blockDiagonal'_mul, isHermitian_blockDiagonal'_iff]
    exact fun i => (B i).isHermitian_mul_pinv
  · rw [← blockDiagonal'_mul, isHermitian_blockDiagonal'_iff]
    exact fun i => (B i).isHermitian_pinv_mul

private theorem pinv_reindex_same {m : Type*} [Fintype m] [DecidableEq m]
    (r : m ≃ n) (B : Matrix m m ℂ) :
    (B.reindex r r).pinv = B.pinv.reindex r r := by
  let f := reindexAlgEquiv ℂ ℂ r
  have hH {X : Matrix m m ℂ} (hX : X.IsHermitian) : (f X).IsHermitian := by
    change (X.reindex r r)ᴴ = X.reindex r r
    rw [conjTranspose_reindex, hX]
  change (f B).pinv = f B.pinv
  symm
  apply (f B).pinv_unique
  · rw [← map_mul, ← map_mul, B.mul_pinv_mul_self]
  · rw [← map_mul, ← map_mul, B.pinv_mul_self_mul_pinv]
  · rw [← map_mul]
    exact hH B.isHermitian_mul_pinv
  · rw [← map_mul]
    exact hH B.isHermitian_pinv_mul

private theorem quasiCommuting_map {m : Type*} [Fintype m] [DecidableEq m]
    (f : Matrix n n ℂ →* Matrix m m ℂ) {A X : Matrix n n ℂ}
    (h : AreQuasiCommutingInverses A X) : AreQuasiCommutingInverses (f A) (f X) := by
  obtain ⟨hi, ho, k, hk, hc, hd⟩ := h
  refine ⟨?_, ?_, k, hk, ?_, ?_⟩
  · rw [isInnerInverse_iff, ← map_mul, ← map_mul, isInnerInverse_iff.mp hi]
  · rw [isOuterInverse_iff, ← map_mul, ← map_mul, isOuterInverse_iff.mp ho]
  · simpa only [map_pow] using hc.map f
  · simpa only [map_pow] using hd.map f

private def matrixUnitConj (P : (Matrix n n ℂ)ˣ) : Matrix n n ℂ →+* Matrix n n ℂ where
  toFun B := (P : Matrix n n ℂ) * B * (↑P⁻¹ : Matrix n n ℂ)
  map_zero' := by simp
  map_one' := by rw [mul_one, Units.mul_inv]
  map_add' B C := by rw [mul_add, add_mul]
  map_mul' B C := by simp only [mul_assoc, Units.inv_mul_cancel_left]

private theorem matrixUnitConj_injective (P : (Matrix n n ℂ)ˣ) :
    Function.Injective (matrixUnitConj P) := by
  intro B C h
  change (P : Matrix n n ℂ) * B * (↑P⁻¹ : Matrix n n ℂ) =
    (P : Matrix n n ℂ) * C * (↑P⁻¹ : Matrix n n ℂ) at h
  have he := congrArg (fun M : Matrix n n ℂ => (↑P⁻¹ : Matrix n n ℂ) * M * (P : Matrix n n ℂ)) h
  simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using he

private theorem quasiCommuting_jordanForm {k : ℕ} (e : Fin k → ℕ) (μ : Fin k → ℂ) :
    AreQuasiCommutingInverses (jordanForm e μ) (jordanForm e μ).pinv := by
  let J := jordanForm e μ
  let l := (Finset.univ.sup e) + 1
  refine ⟨J.mul_pinv_mul_self, J.pinv_mul_self_mul_pinv, l, Nat.succ_pos _, ?_, ?_⟩
  · change (jordanForm e μ ^ l) * (jordanForm e μ).pinv =
      (jordanForm e μ).pinv * (jordanForm e μ ^ l)
    rw [pinv_blockDiagonal_jordan, jordanForm_def, ← blockDiagonal'_pow,
      ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    congr 1
    funext i
    have hle : e i ≤ l := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
    exact (jordanBlock_pow_commute_pinv (e i) l hle (μ i)).1.eq
  · change jordanForm e μ * ((jordanForm e μ).pinv ^ l) =
      ((jordanForm e μ).pinv ^ l) * jordanForm e μ
    rw [pinv_blockDiagonal_jordan, jordanForm_def, ← blockDiagonal'_pow,
      ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    congr 1
    funext i
    have hle : e i ≤ l := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
    exact (jordanBlock_pow_commute_pinv (e i) l hle (μ i)).2.eq

/-- Strong spectral inverses are quasi-commuting. -/
theorem quasiCommuting_of_strongSpectralInverse {A X : Matrix n n ℂ}
    (h : AreStrongSpectralInverses A X) : AreQuasiCommutingInverses A X := by
  obtain ⟨k, e, c, r, P, _, rfl, rfl⟩ := h
  let J := jordanForm e c
  let f := reindexAlgEquiv ℂ ℂ r
  have hej : (f J).pinv = f J.pinv := pinv_reindex_same r J
  have hJ : AreQuasiCommutingInverses (f J) (f J).pinv := by
    rw [hej]
    exact quasiCommuting_map f.toMonoidHom (quasiCommuting_jordanForm e c)
  exact quasiCommuting_map (matrixUnitConj P).toMonoidHom hJ

/-- An index-one matrix has at most one strong spectral inverse, its
group inverse. -/
theorem strongSpectralInverse_unique_of_index_one {A X : Matrix n n ℂ}
    (hA : matrixIndex A = 1) (hX : AreStrongSpectralInverses A X) : IsGroupInverse A X := by
  obtain ⟨hc, _, hN⟩ := (corollary_4_4 A X).mp (quasiCommuting_of_strongSpectralInverse hX)
  have hcore := groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart hc
  have hnil : nilpotentPart X = 0 := by
    rw [isOuterInverse_iff, nilpotentPart_eq_zero_of_matrixIndex_one A hA, mul_zero, zero_mul] at hN
    exact hN.symm
  have hD : X = drazinInverse A := by
    rw [← groupInvertiblePart_add_nilpotentPart X, hnil, add_zero, hcore]
  rw [hD]
  change IsDrazinInverseAt 1 A (drazinInverse A)
  rw [← hA]
  exact isDrazinInverseAt_drazinInverse A

/-- Every complex square matrix admits a strong spectral inverse. -/
theorem exists_strongSpectralInverse (A : Matrix n n ℂ) :
    ∃ X, AreStrongSpectralInverses A X := by
  let s := Fintype.equivFin n
  let f := reindexAlgEquiv ℂ ℂ s
  let B := f A
  obtain ⟨k, e, μ, he, T, hs, hT, hTB⟩ := B.exists_conj_jordanForm
  let r₀ := finSigmaFinEquiv.trans (finCongr he)
  let r := r₀.trans s.symm
  let Q := hT.unit
  let P := Q.map f.symm.toMonoidHom
  have hQ : (↑Q : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) = T := hT.unit_spec
  have hQi : (↑Q⁻¹ : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) = T⁻¹ := by
    rw [Matrix.coe_units_inv, hQ]
  have hq : (↑Q⁻¹ : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) * B *
      (Q : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) =
      (jordanForm e μ).reindex r₀ r₀ := by
    rw [hQi, hQ]
    exact hTB
  have hq' : B = (↑Q : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) *
      ((jordanForm e μ).reindex r₀ r₀) *
        (↑Q⁻¹ : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) := by
    rw [← hq]
    simp only [mul_assoc, Units.mul_inv, Units.mul_inv_cancel_left, mul_one]
  let J := (jordanForm e μ).reindex r r
  refine ⟨(P : Matrix n n ℂ) * J.pinv * (↑P⁻¹ : Matrix n n ℂ), k, e, μ, r, P, hs, ?_, rfl⟩
  have hf : f.symm ((jordanForm e μ).reindex r₀ r₀) = J := by
    unfold J r
    change ((jordanForm e μ).reindex r₀ r₀).reindex s.symm s.symm = _
    rfl
  have h := congrArg f.symm hq'
  rw [map_mul, map_mul, hf] at h
  have h₀ : f.symm B = A := f.symm_apply_apply A
  rw [h₀] at h
  change A = f.symm (Q : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) *
    J * f.symm (↑Q⁻¹ : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ)
  exact h

/-- The group inverse is the unique strong spectral inverse of an
index-one matrix. -/
theorem strongSpectralInverse_iff_isGroupInverse_of_index_one {A X : Matrix n n ℂ}
    (hA : matrixIndex A = 1) : AreStrongSpectralInverses A X ↔ IsGroupInverse A X := by
  constructor
  · exact strongSpectralInverse_unique_of_index_one hA
  · intro hX
    obtain ⟨Y, hY⟩ := exists_strongSpectralInverse A
    have he := hX.unique (strongSpectralInverse_unique_of_index_one hA hY)
    exact he.symm ▸ hY

/-- The Cline inverse for an index-one matrix is its group inverse times
the orthogonal projection onto the range. -/
noncomputable def clineSpectralInverse (A G : Matrix n n ℂ) : Matrix n n ℂ :=
  G * A * A.pinv

/-- For an existing group inverse, the Cline inverse satisfies the three
least-squares Penrose equations and has the original range. -/
theorem clineSpectralInverse_spec {A G : Matrix n n ℂ} (hG : IsGroupInverse A G) :
    let X := clineSpectralInverse A G
    A.IsInnerInverse X ∧ A.IsOuterInverse X ∧ (A * X).IsHermitian ∧
      X.mulVecLin.range = A.mulVecLin.range := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp hG
  intro X
  have hAX : A * X = A * A.pinv := by
    change A * (G * A * A.pinv) = _
    rw [← mul_assoc, ← mul_assoc, hi]
  have hXA : X * A = G * A := by
    change G * A * A.pinv * A = _
    rw [mul_assoc G A A.pinv, mul_assoc G, A.mul_pinv_mul_self]
  have hXAX : X * A * X = X := by
    rw [hXA]
    change G * A * (G * A * A.pinv) = _
    rw [← mul_assoc, ← mul_assoc, ho]
    rfl
  refine ⟨by rw [isInnerInverse_iff, hAX, A.mul_pinv_mul_self],
    hXAX, hAX.symm ▸ A.isHermitian_mul_pinv, ?_⟩
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨(G * A.pinv) *ᵥ v, ?_⟩
    change A *ᵥ ((G * A.pinv) *ᵥ v) = (G * A * A.pinv) *ᵥ v
    rw [mulVec_mulVec, ← mul_assoc, hc.eq]
  · rintro _ ⟨v, rfl⟩
    refine ⟨(A ^ 2) *ᵥ v, ?_⟩
    change X *ᵥ ((A ^ 2) *ᵥ v) = A *ᵥ v
    rw [mulVec_mulVec, pow_two, ← mul_assoc, hXA, ← hc.eq, hi]

/-- An index-one matrix has a least-squares inverse whose range equals
the original range. -/
theorem exists_leastSquaresInverse_same_range (A : Matrix n n ℂ) (hA : matrixIndex A = 1) :
    ∃ X, A.IsInnerInverse X ∧ A.IsOuterInverse X ∧ (A * X).IsHermitian ∧
      X.mulVecLin.range = A.mulVecLin.range := by
  obtain ⟨G, hG, _⟩ := (theorem_4_2 A).mpr hA
  exact ⟨clineSpectralInverse A G, clineSpectralInverse_spec hG⟩

/-- **Exercise 43** of [benIsrael2003generalized], Chapter 4.
An index-one matrix has zero nilpotent part. -/
theorem exercise_4_43 (A : Matrix n n ℂ) (hA : matrixIndex A = 1) : nilpotentPart A = 0 :=
  nilpotentPart_eq_zero_of_matrixIndex_one A hA

/-- **Exercise 44** of [benIsrael2003generalized], Chapter 4.
The ranks of the powers of a nilpotent matrix decrease strictly until
the power vanishes. -/
theorem exercise_4_44 {A : Matrix n n ℂ} (hA : IsNilpotent A) (l : ℕ)
    (h : A ^ l ≠ 0) : (A ^ (l + 1)).rank < (A ^ l).rank := by
  have hle : (A ^ (l + 1)).rank ≤ (A ^ l).rank := by
    rw [pow_succ]
    exact rank_mul_le_left _ _
  refine lt_of_le_of_ne hle ?_
  intro he
  obtain ⟨k, hk⟩ := hA
  have hs := A.rank_pow_eq_of_eq_succ he.symm (Nat.le_add_right l k)
  rw [pow_add, hk, mul_zero, rank_zero] at hs
  exact h (rank_eq_zero_iff.mp hs)

/-- **Exercise 45** of [benIsrael2003generalized], Chapter 4.
For a nilpotent matrix, the matrix index is its least positive
annihilating exponent. -/
theorem exercise_4_45 {A : Matrix n n ℂ} (hA : IsNilpotent A) :
    IsLeast {l : ℕ | 0 < l ∧ A ^ l = 0} (matrixIndex A) := by
  have hpos := A.rankStabilizationIndex_spec.1
  have hz : A ^ matrixIndex A = 0 := by
    by_contra h
    exact (ne_of_lt (exercise_4_44 hA _ h)) A.rankStabilizationIndex_spec.2.symm
  refine ⟨⟨hpos, hz⟩, ?_⟩
  intro l hl
  apply (A.rank_pow_eq_succ_iff hl.1).mp
  rw [pow_succ, hl.2, zero_mul]

/-- **Exercise 46** of [benIsrael2003generalized], Chapter 4.
The nilpotent part has the same index as the original matrix. -/
theorem exercise_4_46 (A : Matrix n n ℂ) : matrixIndex (nilpotentPart A) = matrixIndex A := by
  have hN := (theorem_4_11 A).1.2.2.1
  have hidx := exercise_4_45 hN
  refine le_antisymm (hidx.2 ⟨A.rankStabilizationIndex_spec.1, nilpotentPart_pow_matrixIndex A⟩) ?_
  obtain ⟨hl, hzero⟩ := hidx.1
  let l := matrixIndex (nilpotentPart A)
  have hzero' : nilpotentPart A ^ (l + 1) = 0 := by rw [pow_succ, hzero, zero_mul]
  have he₁ := pow_eq_groupInvertiblePart_add_nilpotentPart A hl
  have he₂ := pow_eq_groupInvertiblePart_add_nilpotentPart A (Nat.succ_pos l)
  rw [hzero, add_zero] at he₁
  rw [hzero', add_zero] at he₂
  apply (A.rank_pow_eq_succ_iff hl).mp
  rw [he₁, he₂]
  apply ((groupInvertiblePart A).rank_pow_eq_succ_iff hl).mpr
  change matrixIndex (groupInvertiblePart A) ≤ l
  rw [(theorem_4_11 A).1.2.1]
  exact hl

/-- **Exercise 48** of [benIsrael2003generalized], Chapter 4.
The Drazin inverse and the nilpotent part annihilate one another. -/
theorem exercise_4_48 (A : Matrix n n ℂ) :
    drazinInverse A * nilpotentPart A = 0 ∧ nilpotentPart A * drazinInverse A = 0 :=
  drazinInverse_mul_nilpotentPart A

/-- **Exercise 50** of [benIsrael2003generalized], Chapter 4.
When the Drazin inverses and cores are exchanged, both Penrose inverse
equations hold exactly when they hold for the nilpotent parts. -/
theorem exercise_4_50 {A X : Matrix n n ℂ} (h : drazinInverse X = groupInvertiblePart A) :
    (A.IsInnerInverse X ↔ (nilpotentPart A).IsInnerInverse (nilpotentPart X)) ∧
      (A.IsOuterInverse X ↔ (nilpotentPart A).IsOuterInverse (nilpotentPart X)) :=
  ⟨innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart h,
    innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart
      (groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart h).symm⟩

/-- **Exercise 51** of [benIsrael2003generalized], Chapter 4.
The Cline inverse preserves exact nonzero grades and is an S-inverse
precisely for a range-Hermitian matrix. -/
theorem exercise_4_51 {A G : Matrix n n ℂ} (hG : IsGroupInverse A G) :
    let X := clineSpectralInverse A G
    (∀ μ : ℂ, μ ≠ 0 → ∀ v p, IsVectorOfGrade A μ v p ↔ IsVectorOfGrade X μ⁻¹ v p) ∧
      (IsSInverse A X ↔ IsRangeHermitian A) := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp hG
  intro X
  have hX := clineSpectralInverse_spec hG
  have hAX : A * X = A * A.pinv := by
    change A * (G * A * A.pinv) = _
    rw [← mul_assoc, ← mul_assoc, hi]
  have hXA : X * A = G * A := by
    change G * A * A.pinv * A = _
    rw [mul_assoc G A A.pinv, mul_assoc G, A.mul_pinv_mul_self]
  have h₁ : X * A ^ (1 + 1) = A ^ 1 := by
    rw [pow_two, ← mul_assoc, hXA, ← hc.eq, hi, pow_one]
  have h₂ : A * X ^ (1 + 1) = X ^ 1 := by
    rw [pow_two, ← mul_assoc, hAX, pow_one]
    rw [ext_iff_mulVec]
    intro v
    obtain ⟨w, hw⟩ := hX.2.2.2 ▸ X.mulVecLin.mem_range_self v
    change A *ᵥ w = X *ᵥ v at hw
    rw [← mulVec_mulVec, ← hw, mulVec_mulVec, A.mul_pinv_mul_self]
  refine ⟨fun μ hμ v p => ⟨lemma_4_4 A X h₁ hμ, fun hv => ?_⟩, ?_⟩
  · simpa only [inv_inv] using lemma_4_4 X A h₂ (inv_ne_zero hμ) hv
  constructor
  · intro hS
    have hidx := (theorem_4_2 A).mp ⟨G, hG, fun _ h => h.unique hG⟩
    obtain ⟨H, hH, _, huniq⟩ := theorem_4_6 A hidx
    have hEq : X = G := (huniq X hS (Or.inl hX.1)).trans (hH.unique hG)
    have hAG : (A * G).IsHermitian := by rw [← hEq, hAX]; exact A.isHermitian_mul_pinv
    have hGA : (G * A).IsHermitian := hc.eq ▸ hAG
    exact (theorem_4_4 hG).mp (A.pinv_unique hi ho hAG hGA)
  · intro hR
    have he := (theorem_4_4 hG).mpr hR
    have hEq : X = G := by
      change G * A * A.pinv = G
      rw [← he, ho]
    rw [hEq]
    exact isSInverse_of_isGroupInverse hG

/-- **Exercise 47** of [benIsrael2003generalized], Chapter 4.
The original rank is the sum of the rank of the Drazin inverse and
the rank of the nilpotent part. -/
theorem exercise_4_47 (A : Matrix n n ℂ) :
    A.rank = (drazinInverse A).rank + (nilpotentPart A).rank := by
  let B := groupInvertiblePart A
  let D := drazinInverse A
  let N := nilpotentPart A
  let P := drazinProjector A
  have hAP : A * P = B := by
    simp only [P, B, drazinProjector, groupInvertiblePart, pow_two, mul_assoc]
  have hAN : A * (1 - P) = N := by
    change A * (1 - P) = A - B
    rw [mul_sub, mul_one, hAP]
  have hsum : B + N = A := groupInvertiblePart_add_nilpotentPart A
  have hR : A.mulVecLin.range = B.mulVecLin.range ⊔ N.mulVecLin.range := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      change A *ᵥ v ∈ B.mulVecLin.range ⊔ N.mulVecLin.range
      rw [← hsum, add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · apply sup_le
      · rintro _ ⟨v, rfl⟩
        exact ⟨P *ᵥ v, by change A *ᵥ (P *ᵥ v) = B *ᵥ v; rw [mulVec_mulVec, hAP]⟩
      · rintro _ ⟨v, rfl⟩
        exact ⟨(1 - P) *ᵥ v, by change A *ᵥ ((1 - P) *ᵥ v) = N *ᵥ v; rw [mulVec_mulVec, hAN]⟩
  obtain ⟨_, hi, ho⟩ := _root_.isGroupInverse_iff.mp
    (isGroupInverse_drazinInverse_groupInvertiblePart A)
  have hdis : Disjoint B.mulVecLin.range N.mulVecLin.range := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
    change N *ᵥ w = B *ᵥ v at hw
    change B *ᵥ v = 0
    calc
      _ = B *ᵥ (D *ᵥ (B *ᵥ v)) := by rw [mulVec_mulVec, mulVec_mulVec, hi]
      _ = 0 := by
        have hn : D *ᵥ (N *ᵥ w) = 0 := by
          rw [mulVec_mulVec, show D * N = 0 from (drazinInverse_mul_nilpotentPart A).1, zero_mulVec]
        rw [← hw, hn, mulVec_zero]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq B.mulVecLin.range N.mulVecLin.range
  rw [← hR, hdis.eq_bot, finrank_bot, add_zero] at hdim
  have hrank : B.rank = D.rank := le_antisymm
    (Matrix.IsInnerInverse.rank_le (A := B) (X := D) hi)
    (Matrix.IsInnerInverse.rank_le (A := D) (X := B) ho)
  exact hdim.trans (congrArg (· + N.rank) hrank)

private theorem positive_pow_mul_drazinInverse_pow_eq_projector (A : Matrix n n ℂ)
    {k : ℕ} (hk : 0 < k) :
    A ^ k * drazinInverse A ^ k = drazinProjector A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hD := isDrazinInverseAt_drazinInverse A
  rw [pow_succ' A, mul_assoc, hD.pow_mul_pow_succ j, drazinProjector]

private theorem pow_mulVec_eq_nilpotentPart_of_mem_maxGenEigenspace_zero (A : Matrix n n ℂ)
    {v : n → ℂ} (hv : v ∈ End.maxGenEigenspace A.mulVecLin 0) (k : ℕ) :
    (A ^ k) *ᵥ v = (nilpotentPart A ^ k) *ᵥ v := by
  let r := matrixIndex A
  let B := groupInvertiblePart A
  let D := drazinInverse A
  let P := drazinProjector A
  have hr : 0 < r := A.rankStabilizationIndex_spec.1
  have hD := isDrazinInverseAt_drazinInverse A
  have hA : (A ^ r) *ᵥ v = 0 :=
    LinearMap.mem_ker.mp ((maxGenEigenspace_zero_eq_stableKer A le_rfl).le hv)
  have hP : P *ᵥ v = 0 := by
    change drazinProjector A *ᵥ v = 0
    rw [← positive_pow_mul_drazinInverse_pow_eq_projector A hr, (hD.commute.pow_pow r r).eq,
      ← mulVec_mulVec, hA, mulVec_zero]
  have hB : B *ᵥ v = 0 := by
    change (A ^ 2 * D) *ᵥ v = 0
    rw [pow_two, mul_assoc, ← mulVec_mulVec, ← show P = A * D by rfl, hP, mulVec_zero]
  cases k with
  | zero => simp
  | succ k =>
    have hz : (B ^ (k + 1)) *ᵥ v = 0 := by rw [pow_succ, ← mulVec_mulVec, hB, mulVec_zero]
    rw [pow_eq_groupInvertiblePart_add_nilpotentPart A (Nat.succ_pos _), add_mulVec, hz, zero_add]

/-- **Exercise 49** of [benIsrael2003generalized], Chapter 4.
Every generalized zero-eigenvector has the same grade for the nilpotent
part of the matrix. -/
theorem exercise_4_49 {A : Matrix n n ℂ} {v : n → ℂ} {p : ℕ}
    (h : IsZeroVectorOfGrade A v p) : IsZeroVectorOfGrade (nilpotentPart A) v p := by
  have hv : v ∈ End.maxGenEigenspace A.mulVecLin 0 :=
    (mem_maxGenEigenspace_iff_exists_grade A 0 v).mpr
      (Or.inr ⟨p, (isVectorOfGrade_zero_iff A v p).mpr h⟩)
  exact ⟨h.1, (pow_mulVec_eq_nilpotentPart_of_mem_maxGenEigenspace_zero A hv p).symm.trans h.2.1,
    fun he => h.2.2
      ((pow_mulVec_eq_nilpotentPart_of_mem_maxGenEigenspace_zero A hv (p - 1)).trans he)⟩

/-- **Exercise 52** of [benIsrael2003generalized], Chapter 4.
The proposed Cline extension satisfies all three least-squares Penrose
equations and sends every generalized nonzero eigenvector of the original
matrix to the reciprocal eigenvalue with its grade unchanged. -/
theorem exercise_4_52 {A Y : Matrix n n ℂ} (hY : A.IsInnerInverse Y) :
    let X := drazinInverse A * A * A.pinv + Y * nilpotentPart A * A.pinv
    A.IsInnerInverse X ∧ A.IsOuterInverse X ∧ (A * X).IsHermitian ∧
      ∀ μ : ℂ, μ ≠ 0 → ∀ v p, IsVectorOfGrade A μ v p → IsVectorOfGrade X μ⁻¹ v p := by
  intro X
  let D := drazinInverse A
  let N := nilpotentPart A
  let P := drazinProjector A
  let B := groupInvertiblePart A
  let Z := D * A + Y * N
  have hD := isDrazinInverseAt_drazinInverse A
  have hN₁ : N = A * (1 - P) := by
    change A - A ^ 2 * D = A * (1 - A * D)
    rw [mul_sub, mul_one, pow_two, mul_assoc]
  have hN₂ : N = (1 - P) * A := by
    have hP : Commute A P := ((Commute.refl A).mul_right hD.commute)
    rw [hN₁, mul_sub, sub_mul, mul_one, one_mul, hP.eq]
  have hAYN : A * Y * N = N := by
    rw [hN₁, ← mul_assoc, isInnerInverse_iff.mp hY]
  have hADA : A * (D * A) = B := by
    change A * (D * A) = A ^ 2 * D
    rw [← hD.commute.eq, ← mul_assoc, ← pow_two]
  have hZ : A * Z = A := by
    change A * (D * A + Y * N) = A
    rw [mul_add, hADA, ← mul_assoc, hAYN, groupInvertiblePart_add_nilpotentPart]
  have hXZ : X = Z * A.pinv := by
    change _ = (D * A + Y * N) * A.pinv
    rw [add_mul]
  have hAX : A * X = A * A.pinv := by rw [hXZ, ← mul_assoc, hZ]
  refine ⟨by rw [isInnerInverse_iff, hAX, A.mul_pinv_mul_self], ?_,
    hAX.symm ▸ A.isHermitian_mul_pinv, ?_⟩
  · rw [isOuterInverse_iff]
    calc
      X * A * X = X * (A * A.pinv) := by rw [mul_assoc, hAX]
      _ = X := by rw [hXZ, mul_assoc Z, ← mul_assoc A.pinv, A.pinv_mul_self_mul_pinv]
  · have hP₁ : A * A.pinv * A ^ (matrixIndex A + 1) = A ^ (matrixIndex A + 1) := by
      rw [pow_succ' A, ← mul_assoc, A.mul_pinv_mul_self]
    have hNA : N * A.pinv * A = N := by
      rw [hN₂, mul_assoc (1 - P), mul_assoc (1 - P), A.mul_pinv_mul_self]
    have hNApow : N * A ^ matrixIndex A = 0 := by
      rw [← groupInvertiblePart_pow_eq A le_rfl]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero A.rankStabilizationIndex_spec.1.ne'
      have hk' : matrixIndex A = k + 1 := hk
      rw [hk', pow_succ', ← mul_assoc, (groupInvertiblePart_mul_nilpotentPart A).2, zero_mul]
    have hXp : X * A ^ (matrixIndex A + 1) = A ^ matrixIndex A := by
      change (D * A * A.pinv + Y * N * A.pinv) * A ^ (matrixIndex A + 1) = _
      have ha : D * A * A.pinv * A ^ (matrixIndex A + 1) = A ^ matrixIndex A := calc
        _ = D * (A * A.pinv * A ^ (matrixIndex A + 1)) := by simp only [mul_assoc]
        _ = _ := by rw [hP₁, hD.stable_left]
      have hn : Y * N * A.pinv * A ^ (matrixIndex A + 1) = 0 := calc
        _ = Y * ((N * A.pinv * A) * A ^ matrixIndex A) := by
          rw [pow_succ' A]
          simp only [mul_assoc]
        _ = _ := by rw [hNA, hNApow, mul_zero]
      rw [add_mul, ha, hn, add_zero]
    intro μ hμ v p
    exact lemma_4_4 A X hXp hμ

/-- **Exercise 53** of [benIsrael2003generalized], Chapter 4.
The S-inverse that retains the nilpotent part exchanges the
group-invertible part with the Drazin inverse. -/
noncomputable def retainedNilpotentSInverse (A : Matrix n n ℂ) : Matrix n n ℂ :=
  drazinInverse A + nilpotentPart A

private theorem retainedNilpotentSInverse_parts (A : Matrix n n ℂ) :
    groupInvertiblePart (retainedNilpotentSInverse A) = drazinInverse A ∧
      nilpotentPart (retainedNilpotentSInverse A) = nilpotentPart A := by
  have hparts : IsCoreNilpotentDecomposition (retainedNilpotentSInverse A)
      (drazinInverse A) (nilpotentPart A) :=
    ⟨rfl, matrixIndex_drazinInverse A, (theorem_4_11 A).1.2.2.1, drazinInverse_mul_nilpotentPart A⟩
  obtain ⟨hB, hN⟩ := (theorem_4_11 (retainedNilpotentSInverse A)).2 _ _ hparts
  exact ⟨hB.symm, hN.symm⟩

private theorem drazinInverse_retainedNilpotentSInverse (A : Matrix n n ℂ) :
    drazinInverse (retainedNilpotentSInverse A) = groupInvertiblePart A := by
  have h := isGroupInverse_drazinInverse_groupInvertiblePart (retainedNilpotentSInverse A)
  rw [(retainedNilpotentSInverse_parts A).1] at h
  exact h.unique (isGroupInverse_groupInvertiblePart A)

/-- The inverse that retains the nilpotent part preserves all reciprocal
grades, including the generalized zero-eigenvector grades. -/
theorem isSInverse_retainedNilpotentSInverse (A : Matrix n n ℂ) :
    IsSInverse A (retainedNilpotentSInverse A) := by
  let X := retainedNilpotentSInverse A
  have hX : IsSPrimeInverse A X :=
    theorem_4_12_of_drazinInverse_eq_groupInvertiblePart (drazinInverse_retainedNilpotentSInverse A)
  intro μ v p
  by_cases hz : μ = 0
  · subst μ
    rw [_root_.inv_zero, isVectorOfGrade_zero_iff, isVectorOfGrade_zero_iff]
    have equiv {M : Matrix n n ℂ} (hv : v ∈ End.maxGenEigenspace M.mulVecLin 0) :
        IsZeroVectorOfGrade M v p ↔ IsZeroVectorOfGrade (nilpotentPart M) v p := by
      unfold IsZeroVectorOfGrade
      rw [pow_mulVec_eq_nilpotentPart_of_mem_maxGenEigenspace_zero M hv p,
        pow_mulVec_eq_nilpotentPart_of_mem_maxGenEigenspace_zero M hv (p - 1)]
    have mem {M : Matrix n n ℂ} (h : IsZeroVectorOfGrade M v p) :
        v ∈ End.maxGenEigenspace M.mulVecLin 0 :=
      (mem_maxGenEigenspace_iff_exists_grade M 0 v).mpr
        (Or.inr ⟨p, (isVectorOfGrade_zero_iff M v p).mpr h⟩)
    have hN : nilpotentPart X = nilpotentPart A := (retainedNilpotentSInverse_parts A).2
    change IsZeroVectorOfGrade A v p ↔ IsZeroVectorOfGrade X v p
    constructor
    · intro h
      apply (equiv (hX.2 ▸ mem h)).mpr
      exact hN.symm ▸ (equiv (mem h)).mp h
    · intro h
      apply (equiv (hX.2.symm ▸ mem h)).mpr
      exact hN ▸ (equiv (mem h)).mp h
  · exact hX.1 μ hz v p

/-- Retaining the nilpotent part is an involutive spectral inversion. -/
theorem retainedNilpotentSInverse_involutive (A : Matrix n n ℂ) :
    retainedNilpotentSInverse (retainedNilpotentSInverse A) = A := by
  rw [retainedNilpotentSInverse, drazinInverse_retainedNilpotentSInverse,
    (retainedNilpotentSInverse_parts A).2, groupInvertiblePart_add_nilpotentPart]

/-- In the index-one case the S-inverse that retains the nilpotent part
is the group inverse. -/
theorem isGroupInverse_retainedNilpotentSInverse {A : Matrix n n ℂ} (hA : matrixIndex A = 1) :
    IsGroupInverse A (retainedNilpotentSInverse A) := by
  have h := isDrazinInverseAt_drazinInverse A
  rw [hA] at h
  rw [retainedNilpotentSInverse, nilpotentPart_eq_zero_of_matrixIndex_one A hA, add_zero]
  exact h

/-- Above index one, the S-inverse that retains the nilpotent part
satisfies neither of the first two Penrose equations. -/
theorem retainedNilpotentSInverse_not_penrose_of_index_gt_one (A : Matrix n n ℂ)
    (hA : 1 < matrixIndex A) :
    ¬ (A.IsInnerInverse (retainedNilpotentSInverse A) ∨
      A.IsOuterInverse (retainedNilpotentSInverse A)) := by
  intro h
  exact (ne_of_gt hA) (theorem_4_9 (isSInverse_retainedNilpotentSInverse A) h).1

/-- **Exercise 53**, algebraic characterization, of [benIsrael2003generalized].
At every exponent at or above the matrix index, the four displayed
equations have the unique solution that retains the nilpotent part. -/
theorem exercise_4_53 (A X : Matrix n n ℂ) {l : ℕ} (hl : matrixIndex A ≤ l) :
    (Commute A X ∧ A ^ (l + 1) * X = A ^ l ∧ A * X ^ (l + 1) = X ^ l ∧
      A - X = A ^ l * X ^ l * (A - X)) ↔ X = retainedNilpotentSInverse A := by
  let D := drazinInverse A
  let P := drazinProjector A
  let B := groupInvertiblePart A
  let N := nilpotentPart A
  have hD := isDrazinInverseAt_drazinInverse A
  have hl₀ : 0 < l := A.rankStabilizationIndex_spec.1.trans_le hl
  have hAP : A * P = B := by
    simp only [P, B, drazinProjector, groupInvertiblePart, pow_two, mul_assoc]
  have hpA : Commute P A := (((Commute.refl A).mul_right hD.commute) : Commute A P).symm
  have hDpow : A ^ l * D ^ l = P := positive_pow_mul_drazinInverse_pow_eq_projector A hl₀
  have hPL : A ^ l * P = A ^ l := calc
    _ = A ^ (l + 1) * D := by rw [pow_succ, mul_assoc]; rfl
    _ = _ := (hD.mono hl).stable
  constructor
  · rintro ⟨hc, h₁, _, hdiff⟩
    have hXP : X * P = D := calc
      _ = X * (A ^ (l + 1) * D ^ (l + 1)) :=
        congrArg (X * ·) (positive_pow_mul_drazinInverse_pow_eq_projector A (Nat.succ_pos l)).symm
      _ = A ^ l * D ^ (l + 1) := by rw [← mul_assoc, (hc.pow_left (l + 1)).eq.symm, h₁]
      _ = _ := hD.pow_mul_pow_succ l
    have hXD : Commute X D := by
      obtain ⟨q, hq⟩ := (theorem_4_7 A).1
      change Commute X (drazinInverse A)
      rw [hq]
      exact hc.symm.aeval_right q
    have hXPc : Commute X P := hc.symm.mul_right hXD
    have hPP : IsIdempotentElem P := drazinProjector_mul_self A
    have hPl : P ^ l = P := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl₀.ne'
      exact hPP.pow_succ_eq j
    have hPXl : X ^ l * P = D ^ l := by rw [← hPl, ← hXPc.mul_pow, hXP]
    have hAXl : A ^ l * X ^ l = P := calc
      _ = (A ^ l * P) * X ^ l := by rw [hPL]
      _ = A ^ l * (X ^ l * P) := by rw [mul_assoc, (hXPc.pow_left l).eq]
      _ = _ := by rw [hPXl, hDpow]
    have he : A - X = B - D := by
      rw [hAXl, mul_sub, hpA.eq, hAP, ← hXPc.eq, hXP] at hdiff
      exact hdiff
    change X = D + (A - B)
    calc
      X = A - (A - X) := (sub_sub_cancel A X).symm
      _ = D + (A - B) := by rw [he]; abel
  · rintro rfl
    let S := retainedNilpotentSInverse A
    have hparts := retainedNilpotentSInverse_parts A
    have hidx : matrixIndex S = matrixIndex A := by
      have h := exercise_4_46 S
      rw [hparts.2, exercise_4_46 A] at h
      exact h.symm
    have hSpow (k : ℕ) (hk : l ≤ k) : S ^ k = D ^ k := by
      have hle : matrixIndex S ≤ k := hidx ▸ hl.trans hk
      rw [← groupInvertiblePart_pow_eq S hle, hparts.1]
    have hAB : Commute A B := ((Commute.refl A).pow_right 2).mul_right hD.commute
    have hAS : Commute A S := hD.commute.add_right ((Commute.refl A).sub_right hAB)
    refine ⟨hAS, ?_, ?_, ?_⟩
    · have hNpow : A ^ (l + 1) * N = 0 := by
        rw [← groupInvertiblePart_pow_eq A (hl.trans (Nat.le_succ l)), pow_succ, mul_assoc,
          (groupInvertiblePart_mul_nilpotentPart A).1, mul_zero]
      change A ^ (l + 1) * (D + N) = A ^ l
      rw [mul_add, (hD.mono hl).stable, hNpow, add_zero]
    · change A * S ^ (l + 1) = S ^ l
      rw [hSpow (l + 1) (Nat.le_succ l), hSpow l le_rfl]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl₀.ne'
      rw [show j.succ + 1 = 2 + j by omega, pow_add, ← mul_assoc, hD.mul_sq, pow_succ']
    · have hPN : P * N = 0 := by
        change (A * D) * N = 0
        rw [mul_assoc, (drazinInverse_mul_nilpotentPart A).1, mul_zero]
      have hPD : P * D = D := by
        change (A * D) * D = D
        rw [mul_assoc, ← pow_two, hD.mul_sq]
      change A - S = A ^ l * S ^ l * (A - S)
      rw [hSpow l le_rfl, hDpow, mul_sub, hpA.eq, hAP]
      change A - (D + N) = B - P * (D + N)
      rw [mul_add, hPD, hPN, add_zero]
      change A - (D + (A - B)) = B - D
      abel

private theorem blockDiagonal_pow_eq_zero_iff {k : ℕ} {e : Fin k → ℕ}
    (B : ∀ i, Matrix (Fin (e i)) (Fin (e i)) ℂ) (l : ℕ) :
    (blockDiagonal' B) ^ l = 0 ↔ ∀ i, B i ^ l = 0 := by
  rw [← blockDiagonal'_pow, ← blockDiagonal'_zero, blockDiagonal'_inj]
  exact ⟨fun h i => congrFun h i, funext⟩

/-- A strong spectral inverse of a nilpotent matrix has the same
annihilating powers as the original matrix. -/
theorem strongSpectralInverse_pow_eq_zero_iff {A X : Matrix n n ℂ}
    (h : AreStrongSpectralInverses A X) (hN : IsNilpotent A) (l : ℕ) :
    A ^ l = 0 ↔ X ^ l = 0 := by
  obtain ⟨k, e, μ, r, P, he, rfl, rfl⟩ := h
  let J := jordanForm e μ
  let f := (matrixUnitConj P).comp (reindexAlgEquiv ℂ ℂ r).toRingHom
  have hf : Function.Injective f := (matrixUnitConj_injective P).comp (AlgEquiv.injective _)
  obtain ⟨j, hj⟩ := hN
  change (f J) ^ j = 0 at hj
  have hj' : J ^ j = 0 := hf (by rw [map_pow, hj, map_zero])
  change (jordanForm e μ) ^ j = 0 at hj'
  rw [jordanForm_def, blockDiagonal_pow_eq_zero_iff] at hj'
  have hmu (i : Fin k) : μ i = 0 := by
    by_contra hi
    have hb : IsUnit (jordanBlock (e i) (μ i) ^ j) :=
      Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp
        (ker_mulVecLin_jordanBlock_pow_eq_bot hi j))
    have : Nonempty (Fin (e i)) := ⟨⟨0, he i⟩⟩
    rw [hj' i] at hb
    exact not_isUnit_zero hb
  rw [pinv_reindex_same r J]
  change (f J) ^ l = 0 ↔ (f J.pinv) ^ l = 0
  have hf' (B : Matrix ((i : Fin k) × Fin (e i)) ((i : Fin k) × Fin (e i)) ℂ) :
      (f B) ^ l = 0 ↔ B ^ l = 0 := by
    rw [← map_pow, ← map_zero f, hf.eq_iff]
  rw [hf', hf']
  change jordanForm e μ ^ l = 0 ↔ (jordanForm e μ).pinv ^ l = 0
  rw [pinv_blockDiagonal_jordan, jordanForm_def,
    blockDiagonal_pow_eq_zero_iff, blockDiagonal_pow_eq_zero_iff]
  have hblock (i : Fin k) :
      jordanBlock (e i) (μ i) ^ l = 0 ↔ (jordanBlock (e i) (μ i)).pinv ^ l = 0 := by
    rw [hmu i, jordanBlock_zero_pinv, ← conjTranspose_pow]
    exact Matrix.conjTranspose_eq_zero.symm
  exact ⟨fun hh i => (hblock i).mp (hh i), fun hh i => (hblock i).mpr (hh i)⟩

/-- The inclusion of strong spectral inverses among quasi-commuting
inverses is strict in general above index one. -/
theorem exists_quasiCommuting_not_strongSpectral :
    ∃ A X : Matrix (Fin 4) (Fin 4) ℂ, 1 < matrixIndex A ∧
      AreQuasiCommutingInverses A X ∧ ¬ AreStrongSpectralInverses A X := by
  let A : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  let X : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, -1; 1, 0, 0, 0]
  have hi : A * X * A = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, X, Matrix.mul_apply, Fin.sum_univ_four]
  have ho : X * A * X = X := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, X, Matrix.mul_apply, Fin.sum_univ_four]
  have hA₃ : A ^ 3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]
  have hX₂ : X ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [X, pow_two, Matrix.mul_apply, Fin.sum_univ_four]
  have hA₂ : A ^ 2 ≠ 0 := by
    intro h
    have he := congrFun (congrFun h (0 : Fin 4)) (2 : Fin 4)
    norm_num [A, pow_two, Matrix.mul_apply, Fin.sum_univ_four] at he
  have hAn : IsNilpotent A := ⟨3, hA₃⟩
  have hAl : 1 < matrixIndex A := by
    by_contra! he
    have he' := le_antisymm he A.rankStabilizationIndex_spec.1
    have hz := (exercise_4_45 hAn).1.2
    rw [he', pow_one] at hz
    exact hA₂ (by rw [hz, pow_two, zero_mul])
  have hX₃ : X ^ 3 = 0 := by rw [show 3 = 2 + 1 by decide, pow_succ, hX₂, zero_mul]
  refine ⟨A, X, hAl, ⟨hi, ho, 3, by decide, ?_, ?_⟩, ?_⟩
  · rw [hA₃]
    exact Commute.zero_left X
  · rw [hX₃]
    exact Commute.zero_right A
  · intro h
    exact hA₂ ((strongSpectralInverse_pow_eq_zero_iff h hAn 2).mpr hX₂)

/-- **Exercise 54** of [benIsrael2003generalized], Chapter 4.
An index-one operator maps the range of a matrix it leaves invariant
onto the intersection with its own range. -/
theorem exercise_4_54 {m : Type*} [Fintype m] (F : Matrix n n ℂ) (G : Matrix n m ℂ)
    (hF : matrixIndex F = 1) (hG : (F * G).mulVecLin.range ≤ G.mulVecLin.range) :
    (F * G).mulVecLin.range = F.mulVecLin.range ⊓ G.mulVecLin.range := by
  let S := F.mulVecLin.range ⊓ G.mulVecLin.range
  refine le_antisymm (le_inf ?_ hG) ?_
  · rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hmap : Set.MapsTo F.mulVecLin S S := by
    intro v hv
    have hv' : v ∈ G.mulVecLin.range := hv.2
    obtain ⟨z, hz⟩ := hv'
    exact ⟨⟨v, rfl⟩, hG ⟨z, by rw [mulVecLin_mul, LinearMap.comp_apply, hz]⟩⟩
  let f := F.mulVecLin.restrict hmap
  have hdis : Disjoint F.mulVecLin.range F.mulVecLin.ker := by
    have he := ((F.isCompl_range_ker_pow_iff Nat.one_pos).mpr hF.le).disjoint
    simpa only [pow_one] using he
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    apply Subtype.ext
    have hz : (v : n → ℂ) ∈ F.mulVecLin.ker := by
      rw [LinearMap.mem_ker] at hv ⊢
      exact congrArg Subtype.val hv
    exact Submodule.disjoint_def.mp hdis _ v.property.1 hz
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro v hv
  obtain ⟨u, hu⟩ := hsurj ⟨v, hv⟩
  obtain ⟨w, hw⟩ := u.property.2
  exact ⟨w, by rw [mulVecLin_mul, LinearMap.comp_apply, hw]; exact congrArg Subtype.val hu⟩

private theorem jordanBlock_isUnit {k : ℕ} {μ : ℂ} (hμ : μ ≠ 0) :
    IsUnit (jordanBlock k μ) :=
  Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp (by
    simpa only [pow_one] using ker_mulVecLin_jordanBlock_pow_eq_bot (n := k) hμ 1))

private theorem jordanBlock_pinv_pair_similarity_nonzero {k : ℕ} (hk : 0 < k) {μ : ℂ}
    (hμ : μ ≠ 0) :
    ∃ P : (Matrix (Fin k) (Fin k) ℂ)ˣ,
      (jordanBlock k μ).pinv = matrixUnitConj P (jordanBlock k μ⁻¹) ∧
        jordanBlock k μ = matrixUnitConj P (jordanBlock k μ⁻¹).pinv := by
  let A := jordanBlock k μ
  let B := jordanBlock k μ⁻¹
  let E := jordanBlock k (0 : ℂ)
  let C := A⁻¹
  let T := C - μ⁻¹ • 1
  let s := -μ⁻¹
  have hA : IsUnit A := jordanBlock_isUnit hμ
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hCA : C * A = 1 := Matrix.nonsing_inv_mul _ hAd
  have hAC : A * C = 1 := Matrix.mul_nonsing_inv _ hAd
  have hAE : A = E + μ • 1 := jordanBlock_eq_add_smul_one
  have hC : C.IsUpperTriangular := (isUpperTriangular_jordanBlock (n := k) (μ := μ)).inv
  have hdiag (i : Fin k) : C i i = μ⁻¹ := by
    have h := congrFun (congrFun hCA i) i
    rw [hC.mul_apply_self isUpperTriangular_jordanBlock, Matrix.one_apply_eq] at h
    change C i i * A i i = 1 at h
    rw [show A i i = μ from Matrix.jordanBlock_apply_self i] at h
    calc
      C i i = C i i * μ * μ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hμ, mul_one]
      _ = μ⁻¹ := by rw [h, one_mul]
  have hCE : Commute C E := by
    have h : Commute C A := hCA.trans hAC.symm
    have he : E = A - μ • 1 := by rw [hAE, add_sub_cancel_right]
    rw [he]
    have hμC : Commute C (μ • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Algebra.commute_algebraMap_right _ _
    exact h.sub_right hμC
  have hT : T = s • (C * E) := by
    have he : E = A - μ • 1 := by rw [hAE, add_sub_cancel_right]
    change C - μ⁻¹ • 1 = (-μ⁻¹) • (C * E)
    rw [he, mul_sub, hCA, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_mul,
      inv_mul_cancel₀ hμ, neg_one_smul, neg_smul]
    abel
  have hTp (q : ℕ) : T ^ q = s ^ q • (C ^ q * E ^ q) := by
    rw [hT, smul_pow, hCE.mul_pow]
  have hTnil : T ^ k = 0 := by
    rw [hTp, show E ^ k = 0 from jordanBlock_zero_pow_eq_zero k k le_rfl, mul_zero, smul_zero]
  let last : Fin k := ⟨k - 1, by omega⟩
  let z : Fin k → ℂ := Pi.single last 1
  let q (j : Fin k) := k - 1 - (j : ℕ)
  let Q : Matrix (Fin k) (Fin k) ℂ :=
    Matrix.of fun i j => (s ^ q j) * (C ^ q j) i j
  have hz (j : Fin k) : (E ^ q j) *ᵥ z = Pi.single j 1 := by
    rw [show z = Pi.single last 1 from rfl, mulVec_single_one]
    ext i
    change (E ^ q j) i last = ((Pi.single j 1 : Fin k → ℂ) i)
    rw [show (E ^ q j) i last = if (i : ℕ) + q j = (last : ℕ) then 1 else 0
      from jordanBlock_zero_pow_apply (q j) i last, Pi.single_apply]
    have he : ((i : ℕ) + q j = (last : ℕ)) ↔ i = j := by
      change ((i : ℕ) + (k - 1 - (j : ℕ)) = k - 1) ↔ i = j
      rw [Fin.ext_iff]
      have := j.isLt
      omega
    simp only [he]
  have hQcol (j : Fin k) : Q.col j = (T ^ q j) *ᵥ z := by
    rw [hTp, smul_mulVec, ← mulVec_mulVec, hz, mulVec_single_one]
    rfl
  have hQE : T * Q = Q * E := by
    ext i j
    change (T * Q).col j i = (Q * E).col j i
    rw [col_mul_eq_mulVec_col, col_mul_eq_mulVec_col, hQcol, mulVec_mulVec, ← pow_succ']
    by_cases hj : (j : ℕ) = 0
    · have hzero : E.col j = 0 := by
        funext a
        change E a j = 0
        rw [show E a j = if (a : ℕ) + 1 = (j : ℕ) then 1 else 0 from jordanBlock_zero_apply a j]
        simp [hj]
      have hq : q j + 1 = k := by dsimp [q]; omega
      rw [hzero, mulVec_zero, hq, hTnil, zero_mulVec]
    · let j₀ : Fin k := ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩
      have hecol : E.col j = Pi.single j₀ 1 := by
        funext a
        change E a j = ((Pi.single j₀ 1 : Fin k → ℂ) a)
        rw [show E a j = if (a : ℕ) + 1 = (j : ℕ) then 1 else 0 from jordanBlock_zero_apply a j,
          Pi.single_apply]
        have hs : (a = j₀) ↔ (a : ℕ) + 1 = (j : ℕ) := by
          rw [Fin.ext_iff]
          change (a : ℕ) = (j : ℕ) - 1 ↔ _
          omega
        simp only [hs]
      have hq : q j + 1 = q j₀ := by
        change k - 1 - (j : ℕ) + 1 = k - 1 - ((j : ℕ) - 1)
        have := j.isLt
        omega
      have hVec : Q *ᵥ Pi.single j₀ (1 : ℂ) = Q.col j₀ := mulVec_single_one Q j₀
      rw [hecol, hVec, hQcol, hq]
  have hQU : Q.IsUpperTriangular := by
    intro i j hij
    change s ^ q j * (C ^ q j) i j = 0
    rw [hC.pow (q j) hij, mul_zero]
  have hQu : IsUnit Q := hQU.isUnit_iff.mpr fun i => by
    change s ^ q i * (C ^ q i) i i ≠ 0
    rw [hC.pow_apply_self, hdiag]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hμ)))
      (pow_ne_zero _ (inv_ne_zero hμ))
  have hCQ : C * Q = Q * B := by
    have hB : B = E + μ⁻¹ • 1 := jordanBlock_eq_add_smul_one
    rw [hB, mul_add, mul_smul_comm, mul_one]
    have he : C * Q - μ⁻¹ • Q = Q * E := by
      change (C - μ⁻¹ • 1) * Q = Q * E at hQE
      simpa only [sub_mul, smul_mul_assoc, one_mul] using hQE
    exact eq_add_of_sub_eq he
  have hB : IsUnit B := jordanBlock_isUnit (inv_ne_zero hμ)
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hAQ : A * Q = Q * B⁻¹ := calc
    _ = A * (Q * B) * B⁻¹ := by
      rw [mul_assoc A, mul_assoc Q, Matrix.mul_nonsing_inv _ hBd, mul_one]
    _ = A * (C * Q) * B⁻¹ := by rw [← hCQ]
    _ = _ := by rw [← mul_assoc A, hAC, one_mul]
  let P := hQu.unit
  have hp : (P : Matrix (Fin k) (Fin k) ℂ) = Q := hQu.unit_spec
  refine ⟨P, ?_, ?_⟩
  · rw [pinv_eq_inv hA]
    change C = (P : Matrix (Fin k) (Fin k) ℂ) * B * (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ)
    rw [hp, ← hCQ, ← hp, Units.mul_inv_cancel_right]
  · rw [pinv_eq_inv hB]
    change A = (P : Matrix (Fin k) (Fin k) ℂ) * B⁻¹ * (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ)
    rw [hp, ← hAQ, ← hp, Units.mul_inv_cancel_right]

private theorem jordanBlock_pinv_pair_similarity_zero (k : ℕ) :
    ∃ P : (Matrix (Fin k) (Fin k) ℂ)ˣ,
      (jordanBlock k (0 : ℂ)).pinv = matrixUnitConj P (jordanBlock k 0) ∧
        jordanBlock k (0 : ℂ) = matrixUnitConj P (jordanBlock k 0).pinv := by
  let σ : Equiv.Perm (Fin k) := Fin.revPerm
  let P := Units.map (Matrix.permMatrixHom (R := ℂ)) (toUnits σ)
  let J := jordanBlock k (0 : ℂ)
  have hP : (P : Matrix (Fin k) (Fin k) ℂ) = σ.permMatrix ℂ := by
    change σ⁻¹.permMatrix ℂ = σ.permMatrix ℂ
    rw [Equiv.Perm.inv_def, show σ.symm = σ from Fin.revPerm_symm]
  have hPi : (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ) = σ.permMatrix ℂ := rfl
  have hJ : Jᴴ = matrixUnitConj P J := by
    change Jᴴ = (P : Matrix (Fin k) (Fin k) ℂ) * J * (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ)
    rw [hP, hPi, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    change star (J j i) = J (Fin.rev i) (Fin.rev j)
    simp only [J, jordanBlock_zero_apply]
    have hrev : ((j : ℕ) + 1 = (i : ℕ)) ↔
        ((Fin.rev i : ℕ) + 1 = (Fin.rev j : ℕ)) := by
      simp only [Fin.val_rev]
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp only [← hrev]
    split_ifs <;> simp
  refine ⟨P, (jordanBlock_zero_pinv k).trans hJ, ?_⟩
  rw [jordanBlock_zero_pinv]
  have hstar : (σ.permMatrix ℂ)ᴴ = σ.permMatrix ℂ := by
    rw [conjTranspose_permMatrix, Equiv.Perm.inv_def, show σ.symm = σ from Fin.revPerm_symm]
  have he := congrArg Matrix.conjTranspose hJ
  change Jᴴᴴ = ((P : Matrix (Fin k) (Fin k) ℂ) * J * (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ))ᴴ at he
  change J = (P : Matrix (Fin k) (Fin k) ℂ) * Jᴴ * (↑P⁻¹ : Matrix (Fin k) (Fin k) ℂ)
  rw [hP, hPi] at he ⊢
  simpa only [conjTranspose_conjTranspose, conjTranspose_mul, hstar, mul_assoc] using he

private theorem jordanBlock_pinv_pair_similarity {k : ℕ} (hk : 0 < k) (μ : ℂ) :
    ∃ P : (Matrix (Fin k) (Fin k) ℂ)ˣ,
      (jordanBlock k μ).pinv = matrixUnitConj P (jordanBlock k μ⁻¹) ∧
        jordanBlock k μ = matrixUnitConj P (jordanBlock k μ⁻¹).pinv := by
  by_cases hμ : μ = 0
  · subst μ
    simpa only [_root_.inv_zero] using jordanBlock_pinv_pair_similarity_zero k
  · exact jordanBlock_pinv_pair_similarity_nonzero hk hμ

/-- Strong spectral inversion is reciprocal. In each nonzero block a
basis of powers of the shifted inverse restores Jordan form at the
reciprocal eigenvalue. Reversal does the same for the adjoint zero block. -/
theorem AreStrongSpectralInverses.symm {A X : Matrix n n ℂ}
    (h : AreStrongSpectralInverses A X) : AreStrongSpectralInverses X A := by
  classical
  obtain ⟨k, e, μ, r, P, he, rfl, rfl⟩ := h
  choose T h₁ h₂ using fun i => jordanBlock_pinv_pair_similarity (he i) (μ i)
  let ι := (i : Fin k) × Fin (e i)
  let F := reindexAlgEquiv ℂ ℂ r
  let D := blockDiagonal'RingHom (fun i : Fin k => Fin (e i)) ℂ
  let u : (∀ i : Fin k, Matrix (Fin (e i)) (Fin (e i)) ℂ)ˣ :=
    ⟨fun i => T i, fun i => ↑(T i)⁻¹,
      funext fun i => (T i).mul_inv, funext fun i => (T i).inv_mul⟩
  let Q := (u.map D.toMonoidHom).map F.toMonoidHom
  have hQ : (Q : Matrix n n ℂ) =
      F (blockDiagonal' fun i => (T i : Matrix (Fin (e i)) (Fin (e i)) ℂ)) := rfl
  have hQi : (↑Q⁻¹ : Matrix n n ℂ) =
      F (blockDiagonal' fun i => (↑(T i)⁻¹ : Matrix (Fin (e i)) (Fin (e i)) ℂ)) := rfl
  have htransport (B : ∀ i : Fin k, Matrix (Fin (e i)) (Fin (e i)) ℂ) :
      matrixUnitConj (P * Q) (F (blockDiagonal' B)) =
        matrixUnitConj P (F (blockDiagonal' fun i => matrixUnitConj (T i) (B i))) := by
    have hblock :
        F (blockDiagonal' fun i => matrixUnitConj (T i) (B i)) =
          (Q : Matrix n n ℂ) * F (blockDiagonal' B) * (↑Q⁻¹ : Matrix n n ℂ) := by
      rw [hQ, hQi, ← map_mul, ← map_mul, ← blockDiagonal'_mul, ← blockDiagonal'_mul]
      rfl
    rw [hblock]
    change ((P : Matrix n n ℂ) * (Q : Matrix n n ℂ)) * F (blockDiagonal' B) *
      (↑((P * Q)⁻¹) : Matrix n n ℂ) =
        (P : Matrix n n ℂ) *
          ((Q : Matrix n n ℂ) * F (blockDiagonal' B) * (↑Q⁻¹ : Matrix n n ℂ)) *
          (↑P⁻¹ : Matrix n n ℂ)
    rw [_root_.mul_inv_rev, Units.val_mul]
    simp only [mul_assoc]
  let ν (i : Fin k) := (μ i)⁻¹
  let J := jordanForm e μ
  let J' := jordanForm e ν
  refine ⟨k, e, ν, r, P * Q, he, ?_, ?_⟩
  · change matrixUnitConj P (F J).pinv = matrixUnitConj (P * Q) (F J')
    rw [show (F J).pinv = F J.pinv from pinv_reindex_same r J]
    change matrixUnitConj P (F (jordanForm e μ).pinv) =
      matrixUnitConj (P * Q) (F (jordanForm e ν))
    rw [pinv_blockDiagonal_jordan, jordanForm_def, htransport]
    exact congrArg (fun B => matrixUnitConj P (F (blockDiagonal' B))) (funext h₁)
  · change matrixUnitConj P (F J) = matrixUnitConj (P * Q) (F J').pinv
    rw [show (F J').pinv = F J'.pinv from pinv_reindex_same r J']
    change matrixUnitConj P (F (jordanForm e μ)) =
      matrixUnitConj (P * Q) (F (jordanForm e ν).pinv)
    rw [pinv_blockDiagonal_jordan, jordanForm_def, htransport]
    exact congrArg (fun B => matrixUnitConj P (F (blockDiagonal' B))) (funext h₂)

end BenIsraelGreville.Chapter04
