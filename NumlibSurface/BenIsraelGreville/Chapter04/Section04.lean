/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section02
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import Numlib.LinearAlgebra.Matrix.Jordan
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import Mathlib.Topology.Instances.Matrix

/-!
# The group inverse

Section 4.4 of [benIsrael2003generalized] studies the commuting reflexive inverse of a
square matrix. It exists exactly at index one, and its rank-factorization formula uses
the inverse of the square product of the factors in reverse order.

## Deviations from the source

* The printed converse of Exercise 18 fails for ordinary similarity.
  The explicit two-dimensional counterexample separates it from the
  unitary-similarity formulation.
* The limits in Exercises 19–21 are taken in a punctured complex
  neighborhood. The shifted inverses are eventually defined there.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n k : Type*} [Fintype n] [DecidableEq n]

/-- **Section 4.4** of [benIsrael2003generalized]. A group inverse satisfies
$AXA=A$, $XAX=X$, and $AX=XA$. -/
abbrev IsGroupInverse (A X : Matrix n n ℂ) : Prop :=
  _root_.IsGroupInverse A X

/-- **Equations (23)–(24)** of [benIsrael2003generalized], Chapter 4. A matrix is
range-Hermitian when its column range equals the column range of its conjugate transpose. -/
def IsRangeHermitian (A : Matrix n n ℂ) : Prop :=
  LinearMap.range (toEuclideanLin A) = LinearMap.range (toEuclideanLin Aᴴ)

private theorem groupInverseFormula [Fintype k] [DecidableEq k] (F : Matrix n k ℂ)
    (G : Matrix k n ℂ) (hUnit : IsUnit (G * F)) :
    IsGroupInverse (F * G) (F * (G * F)⁻¹ ^ 2 * G) := by
  let J := G * F
  let Q := J⁻¹
  have hL : J * Q = 1 := J.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hUnit)
  have hR : Q * J = 1 := J.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp hUnit)
  let X := F * Q ^ 2 * G
  change IsGroupInverse (F * G) X
  have hAX : (F * G) * X = F * Q * G := calc
    (F * G) * X = F * (J * Q) * Q * G := by
      dsimp only [X, J]
      simp only [pow_two, Matrix.mul_assoc]
    _ = _ := by rw [hL, Matrix.mul_one]
  have hXA : X * (F * G) = F * Q * G := calc
    X * (F * G) = F * Q * (Q * J) * G := by
      dsimp only [X, J]
      simp only [pow_two, Matrix.mul_assoc]
    _ = _ := by rw [hR, Matrix.mul_one]
  refine isGroupInverse_iff.mpr ⟨hAX.trans hXA.symm, ?_, ?_⟩
  · calc
      (F * G) * X * (F * G) = F * (Q * J) * G := by
        rw [hAX]
        dsimp only [J]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one]
  · calc
      X * (F * G) * X = F * (Q * J) * Q ^ 2 * G := by
        rw [hXA]
        dsimp only [X, J]
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hR, Matrix.mul_one]

private theorem rank_square_factor [Fintype k] (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    ((F * G) ^ 2).rank = (G * F).rank := by
  have h : (F * G) ^ 2 = F * (G * F) * G := by
    simp only [pow_two, Matrix.mul_assoc]
  rw [h, Chapter01.exercise_7 F (G * F) G hF hG]

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 4. A square matrix has
a group inverse exactly when its index is one, in which case the inverse is unique. -/
theorem theorem_4_2 (A : Matrix n n ℂ) :
    (∃! X, IsGroupInverse A X) ↔ matrixIndex A = 1 := by
  constructor
  · rintro ⟨X, hX, _⟩
    have hle := (theorem_4_1_solvable A Nat.one_pos).mp ⟨X, hX.stable⟩
    have hpos := A.rankStabilizationIndex_spec.1
    exact le_antisymm hle hpos
  · intro hidx
    obtain ⟨F, G, hFG⟩ := (rank_le_iff_exists_mul A A.rank).mp le_rfl
    have hFG_rank : (F * G).rank = A.rank := congrArg rank hFG.symm
    have hcard : Fintype.card (Fin A.rank) = (F * G).rank :=
      (Fintype.card_fin _).trans hFG_rank.symm
    have hF : F.rank = Fintype.card (Fin A.rank) :=
      le_antisymm F.rank_le_card_width (hcard.le.trans (rank_mul_le_left _ _))
    have hG : G.rank = Fintype.card (Fin A.rank) :=
      le_antisymm G.rank_le_card_height (hcard.le.trans (rank_mul_le_right _ _))
    have hA₂ := (A.rank_pow_eq_succ_iff Nat.one_pos).mpr hidx.le
    have hUnit : IsUnit (G * F) := by
      apply isUnit_of_rank_eq_card
      calc
        (G * F).rank = ((F * G) ^ 2).rank := (rank_square_factor F G hF hG).symm
        _ = (A ^ 2).rank := congrArg (fun B : Matrix n n ℂ => (B ^ 2).rank) hFG.symm
        _ = A.rank := by simpa only [pow_one] using hA₂.symm
        _ = _ := (Fintype.card_fin _).symm
    let X := F * (G * F)⁻¹ ^ 2 * G
    have hX : IsGroupInverse A X := hFG ▸ groupInverseFormula F G hUnit
    exact ⟨X, hX, fun Y hY => hY.unique hX⟩

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 4. For a full-rank factorization
$A=FG$, the group inverse exists precisely when $GF$ is nonsingular, and then it is
$F(GF)^{-2}G$. -/
theorem theorem_4_3 [Fintype k] [DecidableEq k] (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) (X : Matrix n n ℂ) :
    IsGroupInverse (F * G) X ↔ IsUnit (G * F) ∧ X = F * (G * F)⁻¹ ^ 2 * G := by
  constructor
  · intro hX
    have hle := (theorem_4_1_solvable (F * G) Nat.one_pos).mp ⟨X, hX.stable⟩
    have hRank := ((F * G).rank_pow_eq_succ_iff Nat.one_pos).mpr hle
    have hFG := Chapter01.exercise_7 F (1 : Matrix k k ℂ) G hF hG
    rw [Matrix.mul_one, rank_one] at hFG
    have hUnit : IsUnit (G * F) := by
      apply isUnit_of_rank_eq_card
      rw [← rank_square_factor F G hF hG, ← hFG]
      simpa only [pow_one] using hRank.symm
    exact ⟨hUnit, hX.unique (groupInverseFormula F G hUnit)⟩
  · rintro ⟨hUnit, rfl⟩
    exact groupInverseFormula F G hUnit

/-- A square matrix is range-Hermitian exactly when it commutes with its
Moore–Penrose inverse. -/
theorem rangeHermitian_iff_commute_pinv (A : Matrix n n ℂ) :
    IsRangeHermitian A ↔ Commute A A.pinv := by
  have h₁ := A.mul_pinv_eq_starProjection
  have h₂ := A.pinv_mul_eq_starProjection
  constructor
  · intro hrange
    have hmap : toEuclideanLin (A * A.pinv) = toEuclideanLin (A.pinv * A) := by
      rw [h₁, h₂]
      exact congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ n) =>
        (S.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) hrange
    exact toEuclideanLin.injective hmap
  · intro hc
    have h : LinearMap.range (toEuclideanLin (A * A.pinv)) =
        LinearMap.range (toEuclideanLin (A.pinv * A)) := by rw [hc.eq]
    rw [h₁, h₂, Submodule.range_starProjection, Submodule.range_starProjection] at h
    exact h

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 4. An existing group inverse
equals the Moore–Penrose inverse exactly when $A$ is range-Hermitian. -/
theorem theorem_4_4 {A X : Matrix n n ℂ} (hX : IsGroupInverse A X) :
    X = A.pinv ↔ IsRangeHermitian A := by
  rw [rangeHermitian_iff_commute_pinv]
  exact ⟨fun he => he ▸ hX.commute, fun hc =>
    hX.unique (isGroupInverse_iff.mpr ⟨hc, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩)⟩

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 4.
Every range-Hermitian matrix has index one. -/
theorem exercise_4_12 (A : Matrix n n ℂ) (hA : IsRangeHermitian A) :
    matrixIndex A = 1 := by
  have hG : IsGroupInverse A A.pinv := _root_.isGroupInverse_iff.mpr
    ⟨(rangeHermitian_iff_commute_pinv A).mp hA, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩
  exact (theorem_4_2 A).mp ⟨_, hG, fun _ h => h.unique hG⟩

/-- In Jordan coordinates the Moore–Penrose inverse is block diagonal
with the Moore–Penrose inverses of the individual blocks. -/
theorem jordanForm_pinv_eq_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (μ : ι → ℂ) :
    (jordanForm e μ).pinv = blockDiagonal' (fun i => (jordanBlock (e i) (μ i)).pinv) := by
  let B (i : ι) := jordanBlock (e i) (μ i)
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

/-- Simultaneous relabeling of the row and column coordinates preserves
the Moore–Penrose inverse. -/
theorem pinv_reindex_square {m : Type*} [Fintype m] [DecidableEq m]
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

private theorem jordanForm_zeroBlockSize_le_one_of_rank_eq_square {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (μ : ι → ℂ)
    (h : (jordanForm e μ).rank = (jordanForm e μ ^ 2).rank) :
    ∀ i, μ i = 0 → e i ≤ 1 := by
  let J := jordanForm e μ
  have hr : (J ^ 1).rank = (J ^ (1 + 1)).rank := by simpa only [pow_one] using h
  have hk := (J.rank_pow_eq_iff_ker_eq (Nat.le_succ 1)).mp hr
  have hdim := congrArg (fun W : Submodule ℂ (((i : ι) × Fin (e i)) → ℂ) =>
    Module.finrank ℂ W) hk.symm
  have hiff := finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff e μ (0 : ℂ) 1
  have hshift : jordanForm e μ - (0 : ℂ) • 1 = jordanForm e μ := by simp
  rw [hshift] at hiff
  exact hiff.mp hdim

private theorem jordanBlock_commute_pinv_of_zeroBlockSize_le_one (k : ℕ) (μ : ℂ)
    (hzero : μ = 0 → k ≤ 1) : Commute (jordanBlock k μ) (jordanBlock k μ).pinv := by
  by_cases hμ : μ = 0
  · have hB : jordanBlock k μ = 0 := by
      ext i j
      have hn : (i : ℕ) + 1 ≠ (j : ℕ) := by
        have hj := j.isLt
        have := hzero hμ
        omega
      simp [hμ, jordanBlock_zero_apply, hn]
    rw [hB]
    exact Commute.zero_left _
  · let B := jordanBlock k μ
    have hB : IsUnit B := Matrix.mulVec_injective_iff_isUnit.mp
      (LinearMap.ker_eq_bot.mp (by
        simpa only [pow_one] using ker_mulVecLin_jordanBlock_pow_eq_bot (n := k) hμ 1))
    have hD := (Matrix.isUnit_iff_isUnit_det B).mp hB
    change B * B.pinv = B.pinv * B
    rw [pinv_eq_inv hB, Matrix.mul_nonsing_inv _ hD, Matrix.nonsing_inv_mul _ hD]

/-- **Lemma 2** of [benIsrael2003generalized], Chapter 4.
A matrix in Jordan form is range-Hermitian exactly when its index is one. -/
theorem lemma_4_2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (μ : ι → ℂ) (r : ((i : ι) × Fin (e i)) ≃ n) :
    let J := (jordanForm e μ).reindex r r
    IsRangeHermitian J ↔ matrixIndex J = 1 := by
  intro J
  constructor
  · exact exercise_4_12 J
  · intro hidx
    let J₀ := jordanForm e μ
    let f := reindexAlgEquiv ℂ ℂ r
    have hr : J.rank = (J ^ 2).rank := by
      simpa only [pow_one] using (J.rank_pow_eq_succ_iff Nat.one_pos).mpr hidx.le
    have hr' : J₀.rank = (J₀ ^ 2).rank := by
      change (f J₀).rank = (f J₀ ^ 2).rank at hr
      rw [← map_pow] at hr
      change (J₀.reindex r r).rank = ((J₀ ^ 2).reindex r r).rank at hr
      simpa only [rank_reindex] using hr
    have hsize := jordanForm_zeroBlockSize_le_one_of_rank_eq_square e μ hr'
    have hc : Commute J₀ J₀.pinv := by
      change J₀ * J₀.pinv = J₀.pinv * J₀
      change jordanForm e μ * (jordanForm e μ).pinv =
        (jordanForm e μ).pinv * jordanForm e μ
      rw [jordanForm_pinv_eq_blockDiagonal, jordanForm_def, ← blockDiagonal'_mul,
        ← blockDiagonal'_mul]
      exact congrArg blockDiagonal' (funext fun i =>
        (jordanBlock_commute_pinv_of_zeroBlockSize_le_one (e i) (μ i) (hsize i)).eq)
    apply (rangeHermitian_iff_commute_pinv J).mpr
    change Commute (J₀.reindex r r) (J₀.reindex r r).pinv
    rw [pinv_reindex_square]
    exact hc.map f

/-- **Theorem 5** of [benIsrael2003generalized], Chapter 4.
At index one the group inverse is the similarity transform of the
Moore–Penrose inverse of the Jordan form. -/
theorem theorem_4_5 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (μ : ι → ℂ) (r : ((i : ι) × Fin (e i)) ≃ n) (P : (Matrix n n ℂ)ˣ) :
    let J := (jordanForm e μ).reindex r r
    let A := (P : Matrix n n ℂ) * J * (↑P⁻¹ : Matrix n n ℂ)
    matrixIndex A = 1 →
      IsGroupInverse A ((P : Matrix n n ℂ) * J.pinv * (↑P⁻¹ : Matrix n n ℂ)) := by
  intro J A hA
  obtain ⟨G, hG, _⟩ := (theorem_4_2 A).mpr hA
  have hJ := hG.conj P⁻¹
  have hJ' : IsGroupInverse J ((↑P⁻¹ : Matrix n n ℂ) * G * (P : Matrix n n ℂ)) := by
    change IsGroupInverse ((↑P⁻¹ : Matrix n n ℂ) * A * (↑(P⁻¹)⁻¹ : Matrix n n ℂ))
      ((↑P⁻¹ : Matrix n n ℂ) * G * (↑(P⁻¹)⁻¹ : Matrix n n ℂ)) at hJ
    have h : (↑P⁻¹ : Matrix n n ℂ) * A * (↑(P⁻¹)⁻¹ : Matrix n n ℂ) = J := by
      change (↑P⁻¹ : Matrix n n ℂ) * ((P : Matrix n n ℂ) * J * (↑P⁻¹ : Matrix n n ℂ)) *
        (↑(P⁻¹)⁻¹ : Matrix n n ℂ) = J
      simp only [inv_inv, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    rwa [h, inv_inv] at hJ
  have hidx : matrixIndex J = 1 := (theorem_4_2 J).mp ⟨_, hJ', fun _ h => h.unique hJ'⟩
  have hep : IsRangeHermitian J := (lemma_4_2 e μ r).mpr hidx
  have hjp : IsGroupInverse J J.pinv := _root_.isGroupInverse_iff.mpr
    ⟨(rangeHermitian_iff_commute_pinv J).mp hep, J.mul_pinv_mul_self, J.pinv_mul_self_mul_pinv⟩
  exact hjp.conj P

/-- **Exercise 8** of [benIsrael2003generalized], Chapter 4.
Two group inverses of the same matrix coincide. -/
theorem exercise_4_8 {A X Y : Matrix n n ℂ}
    (hX : IsGroupInverse A X) (hY : IsGroupInverse A Y) : X = Y := hX.unique hY

/-- **Exercise 9(a)** of [benIsrael2003generalized], Chapter 4.
For a nonsingular matrix the ordinary inverse is its group inverse. -/
theorem exercise_4_9_a (A : Matrix n n ℂ) (hA : IsUnit A) : IsGroupInverse A A⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hL := Matrix.nonsing_inv_mul A hd
  have hR := Matrix.mul_nonsing_inv A hd
  exact _root_.isGroupInverse_iff.mpr
    ⟨hR.trans hL.symm, by rw [hR, one_mul], by rw [hL, one_mul]⟩

/-- **Exercise 9(b)** of [benIsrael2003generalized], Chapter 4.
Taking the group inverse is an involution when it is defined. -/
theorem exercise_4_9_b {A X : Matrix n n ℂ} (h : IsGroupInverse A X) : IsGroupInverse X A := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp h
  exact _root_.isGroupInverse_iff.mpr ⟨hc.symm, ho, hi⟩

/-- **Exercise 9(c)** of [benIsrael2003generalized], Chapter 4.
Conjugate transposition preserves the group inverse relation. -/
theorem exercise_4_9_c {A X : Matrix n n ℂ} (h : IsGroupInverse A X) :
    IsGroupInverse Aᴴ Xᴴ := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp h
  apply _root_.isGroupInverse_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · change Aᴴ * Xᴴ = Xᴴ * Aᴴ
    simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose hc.eq.symm
  · simpa only [conjTranspose_mul, mul_assoc] using congrArg Matrix.conjTranspose hi
  · simpa only [conjTranspose_mul, mul_assoc] using congrArg Matrix.conjTranspose ho

/-- **Exercise 9(d)** of [benIsrael2003generalized], Chapter 4.
Transposition preserves the group inverse relation. -/
theorem exercise_4_9_d {A X : Matrix n n ℂ} (h : IsGroupInverse A X) :
    IsGroupInverse Aᵀ Xᵀ := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp h
  apply _root_.isGroupInverse_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · change Aᵀ * Xᵀ = Xᵀ * Aᵀ
    simpa only [transpose_mul] using congrArg Matrix.transpose hc.eq.symm
  · simpa only [transpose_mul, mul_assoc] using congrArg Matrix.transpose hi
  · simpa only [transpose_mul, mul_assoc] using congrArg Matrix.transpose ho

/-- **Exercise 9(e)** of [benIsrael2003generalized], Chapter 4.
The group inverse of a positive power is the corresponding inverse power. -/
theorem exercise_4_9_e {A X : Matrix n n ℂ} (h : IsGroupInverse A X) (l : ℕ) :
    IsGroupInverse (A ^ l) (X ^ l) := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp h
  have hCA : Commute (A * X) A := (Commute.refl A).mul_left hc.symm
  have hCX : Commute (X * A) X := (Commute.refl X).mul_left hc
  refine _root_.isGroupInverse_iff.mpr ⟨hc.pow_pow _ _, ?_, ?_⟩
  · rw [← hc.mul_pow, ← hCA.mul_pow, hi]
  · rw [← hc.symm.mul_pow, ← hCX.mul_pow, ho]

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 4.
The integer powers use positive powers of the group inverse on the negative
side, the matrix itself on the positive side, and the group projector at zero. -/
theorem exercise_4_10 {A X : Matrix n n ℂ} (h : IsGroupInverse A X) :
    ∃ p : ℤ → Matrix n n ℂ, p 0 = A * X ∧
      (∀ k : ℕ, p ((k + 1 : ℕ) : ℤ) = A ^ (k + 1)) ∧
      (∀ k : ℕ, p (-((k + 1 : ℕ) : ℤ)) = X ^ (k + 1)) ∧
      ∀ j k : ℤ, p j * p k = p (j + k) := by
  obtain ⟨hc, ha, hx⟩ := _root_.isGroupInverse_iff.mp h
  let P := A * X
  have hP : P * P = P := by
    change (A * X) * (A * X) = A * X
    rw [← mul_assoc, ha]
  let S := {B : Matrix n n ℂ // P * B = B ∧ B * P = B}
  let _ : Monoid S :=
    { one := ⟨P, hP, hP⟩
      mul := fun B C => ⟨B.1 * C.1, by rw [← mul_assoc, B.2.1],
        by rw [mul_assoc, C.2.2]⟩
      one_mul := fun B => Subtype.ext B.2.1
      mul_one := fun B => Subtype.ext B.2.2
      mul_assoc := fun B C D => Subtype.ext (mul_assoc B.1 C.1 D.1) }
  let a : S := ⟨A, ha, by
    change A * (A * X) = A
    rw [hc.eq, ← mul_assoc, ha]⟩
  let x : S := ⟨X, by
    change (A * X) * X = X
    rw [hc.eq, hx], by
    change X * (A * X) = X
    rw [← mul_assoc, hx]⟩
  let u : Sˣ := ⟨a, x, Subtype.ext rfl, Subtype.ext hc.eq.symm⟩
  let p (j : ℤ) : Matrix n n ℂ := ((u ^ j : Sˣ) : S).1
  have hp (B : S) (k : ℕ) : ((B ^ (k + 1) : S) : Matrix n n ℂ) = (B : Matrix n n ℂ) ^ (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ B, pow_succ (B : Matrix n n ℂ)]
      change ((B ^ (k + 1) : S) : Matrix n n ℂ) * (B : Matrix n n ℂ) = _
      rw [ih]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simp only [p, zpow_zero]
    rfl
  · intro k
    change ((u ^ ((k + 1 : ℕ) : ℤ) : Sˣ) : S).1 = A ^ (k + 1)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hp]
  · intro k
    change ((u ^ (-((k + 1 : ℕ) : ℤ)) : Sˣ) : S).1 = X ^ (k + 1)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, hp]
    rfl
  · intro j k
    change ((u ^ j : Sˣ) : S).1 * ((u ^ k : Sˣ) : S).1 = ((u ^ (j + k) : Sˣ) : S).1
    rw [_root_.zpow_add, Units.val_mul]
    rfl

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 4.
Sandwiching any inner inverse of the cube by the original matrix
gives its group inverse. -/
theorem exercise_4_11 {A X Y : Matrix n n ℂ} (h : IsGroupInverse A X)
    (hY : (A ^ 3).IsInnerInverse Y) : X = A * Y * A := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp h
  have hAA : A ^ 2 * X = A := by
    rw [pow_two, mul_assoc, hc.eq, ← mul_assoc, hi]
  have hXX : A * X ^ 2 = X := h.mul_sq
  have hA₃ : A ^ 3 * X ^ 2 = A := calc
    _ = A ^ 2 * (A * X ^ 2) := by rw [show 3 = 2 + 1 by decide, pow_succ, mul_assoc]
    _ = A := by rw [hXX, hAA]
  have hA₃' : X ^ 2 * A ^ 3 = A := ((hc.pow_pow 3 2).symm.eq).trans hA₃
  have hX : X ^ 2 * A = X := ((hc.pow_right 2).symm.eq).trans hXX
  calc
    X = X ^ 2 * A := hX.symm
    _ = X ^ 2 * (A ^ 3) * X ^ 2 := by rw [mul_assoc, hA₃]
    _ = X ^ 2 * (A ^ 3 * Y * A ^ 3) * X ^ 2 := by rw [isInnerInverse_iff.mp hY]
    _ = (X ^ 2 * A ^ 3) * Y * (A ^ 3 * X ^ 2) := by simp only [mul_assoc]
    _ = A * Y * A := by rw [hA₃', hA₃]

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 4.
The Moore–Penrose inverse of a range-Hermitian matrix is the unique
matrix satisfying the four equations with its range projection. -/
theorem exercise_4_13 (A X : Matrix n n ℂ) (hA : IsRangeHermitian A) :
    let P := A * A.pinv
    (A * X = P ∧ X * A = P ∧ P * X = X ∧ X * P = X) ↔ X = A.pinv := by
  intro P
  have hc := (rangeHermitian_iff_commute_pinv A).mp hA
  have hG : IsGroupInverse A A.pinv := _root_.isGroupInverse_iff.mpr
    ⟨hc, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩
  constructor
  · rintro ⟨h₁, h₂, h₃, _⟩
    apply IsDrazinInverseAt.unique _ hG
    refine _root_.isGroupInverse_iff.mpr ⟨h₁.trans h₂.symm, ?_, ?_⟩
    · rw [h₁]
      exact A.mul_pinv_mul_self
    · rw [h₂, h₃]
  · rintro rfl
    refine ⟨rfl, hc.eq.symm, ?_, ?_⟩
    · change A * A.pinv * A.pinv = A.pinv
      rw [hc.eq, A.pinv_mul_self_mul_pinv]
    · change A.pinv * (A * A.pinv) = A.pinv
      rw [← mul_assoc, A.pinv_mul_self_mul_pinv]

/-- **Exercise 14** of [benIsrael2003generalized], Chapter 4.
Every nonsingular matrix is range-Hermitian. -/
theorem exercise_4_14 (A : Matrix n n ℂ) (hA : IsUnit A) : IsRangeHermitian A :=
  (rangeHermitian_iff_commute_pinv A).mpr (pinv_eq_inv hA ▸ (exercise_4_9_a A hA).commute)

/-- **Exercise 16** of [benIsrael2003generalized], Chapter 4.
Commutation with the Moore–Penrose inverse characterizes range-Hermitian matrices. -/
theorem exercise_4_16 (A : Matrix n n ℂ) :
    IsRangeHermitian A ↔ Commute A A.pinv := rangeHermitian_iff_commute_pinv A

/-- **Exercise 17** of [benIsrael2003generalized], Chapter 4.
A square matrix is range-Hermitian exactly when its adjoint is a left multiple. -/
theorem exercise_4_17 (A : Matrix n n ℂ) :
    IsRangeHermitian A ↔ ∃ Y : Matrix n n ℂ, Aᴴ = Y * A := by
  constructor
  · intro hA
    have hc := (rangeHermitian_iff_commute_pinv A).mp hA
    refine ⟨Aᴴ * A.pinv, ?_⟩
    rw [mul_assoc, ← hc.eq, A.conjTranspose_mul_mul_pinv]
  · rintro ⟨Y, hY⟩
    have he := congrArg Matrix.conjTranspose hY
    rw [conjTranspose_conjTranspose, conjTranspose_mul] at he
    unfold IsRangeHermitian
    have hle : LinearMap.range (toEuclideanLin A) ≤ LinearMap.range (toEuclideanLin Aᴴ) := by
      rintro _ ⟨v, rfl⟩
      refine ⟨toEuclideanLin Yᴴ v, ?_⟩
      rw [← toEuclideanLin_mul_apply, ← he]
    have hdim : Module.finrank ℂ (LinearMap.range (toEuclideanLin A)) =
        Module.finrank ℂ (LinearMap.range (toEuclideanLin Aᴴ)) := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.finrank_range_adjoint]
    exact Submodule.eq_of_le_of_finrank_eq hle hdim

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 4.
Every normal matrix is range-Hermitian. -/
theorem exercise_4_15 (A : Matrix n n ℂ) (hA : Commute A Aᴴ) : IsRangeHermitian A := by
  let F := toEuclideanLin A
  let G := toEuclideanLin Aᴴ
  have hg : G = F.adjoint := toEuclideanLin_conjTranspose_eq_adjoint A
  have hf : F = G.adjoint := by
    change toEuclideanLin A = (toEuclideanLin Aᴴ).adjoint
    rw [← toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose]
  have hnorm (v : EuclideanSpace ℂ n) : inner ℂ (F v) (F v) = inner ℂ (G v) (G v) := by
    rw [← F.adjoint_inner_right v (F v), ← G.adjoint_inner_right v (G v), ← hg, ← hf]
    change inner ℂ v (toEuclideanLin Aᴴ (toEuclideanLin A v)) =
      inner ℂ v (toEuclideanLin A (toEuclideanLin Aᴴ v))
    rw [← toEuclideanLin_mul_apply, hA.eq.symm, toEuclideanLin_mul_apply]
  have hK : F.ker = G.ker := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [← hnorm, h, inner_zero_left]
    · intro h
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      rw [hnorm, h, inner_zero_left]
  change F.range = G.range
  calc
    _ = G.kerᗮ := by rw [LinearMap.orthogonal_ker, ← hf]
    _ = F.kerᗮ := by rw [hK]
    _ = _ := by rw [LinearMap.orthogonal_ker, ← hg]

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 4.
Ordinary similarity in the printed converse is insufficient. The matrix
in this example is similar to a nonsingular block plus zero and has
distinct column ranges from its conjugate transpose. -/
theorem exercise_4_18_counterexample :
    ∃ A P : Matrix (Fin 2) (Fin 2) ℂ, IsUnit P ∧
      A * P = P * (diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∧ ¬ IsRangeHermitian A := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 0, 1]
  refine ⟨A, P, ?_, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det P).mpr
    norm_num [P, Matrix.det_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  · intro hA
    obtain ⟨Y, hY⟩ := (exercise_4_17 A).mp hA
    have h₀ := congrFun (congrFun hY (0 : Fin 2)) (0 : Fin 2)
    have h₁ := congrFun (congrFun hY (0 : Fin 2)) (1 : Fin 2)
    norm_num [A, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] at h₀ h₁
    exact one_ne_zero (h₀.trans h₁.symm)

section Resolvent

open Filter Set
open scoped Topology

private theorem isUnit_smul_one_add_eventually (A : Matrix n n ℂ) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0, IsUnit (z • (1 : Matrix n n ℂ) + A) := by
  classical
  let S := (-A).charpoly.roots.toFinset
  have hsub : {z : ℂ | z ∈ S ∧ z ≠ 0} ⊆ (S : Set ℂ) := by
    intro z hz
    exact hz.1
  have hclosed : IsClosed {z : ℂ | z ∈ S ∧ z ≠ 0} :=
    ((Finset.finite_toSet S).subset hsub).isClosed
  have h₀ : (0 : ℂ) ∉ {z : ℂ | z ∈ S ∧ z ≠ 0} := by simp
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ∉ {z : ℂ | z ∈ S ∧ z ≠ 0} :=
    hclosed.isOpen_compl.mem_nhds h₀
  have hs : {(0 : ℂ)}ᶜ ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hs] with z hz hnz
  have hnz' : z ≠ 0 := hnz
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hd
  have hr : (-A).charpoly.IsRoot z := by
    rw [Polynomial.IsRoot.def, Matrix.eval_charpoly, sub_neg_eq_add]
    simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hd
  exact hz ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (-A).charpoly_monic.ne_zero).mpr hr), hnz'⟩

private theorem resolvent_mul_original_at_unit (A : Matrix n n ℂ) {z : ℂ}
    (h : IsUnit (z • (1 : Matrix n n ℂ) + A)) :
    (z • (1 : Matrix n n ℂ) + A) * ((z • (1 : Matrix n n ℂ) + A)⁻¹ * A) = A := by
  rw [← mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h), one_mul]

private theorem resolvent_mul_original_algebra (A : Matrix n n ℂ) {L : Matrix n n ℂ}
    (hL : Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + A)⁻¹ * A) (𝓝[≠] 0) (𝓝 L)) :
    A * L = A ∧ Commute A L ∧ A.mulVecLin.ker ≤ L.mulVecLin.ker := by
  let R (z : ℂ) := z • (1 : Matrix n n ℂ) + A
  let F (z : ℂ) := (R z)⁻¹ * A
  have hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), IsUnit (R z) := isUnit_smul_one_add_eventually A
  have hR : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 A) := by
    have h : Continuous R := (continuous_id.smul continuous_const).add continuous_const
    have ht : Tendsto R (𝓝 (0 : ℂ)) (𝓝 (R 0)) := h.continuousAt
    simpa [R] using ht.mono_left nhdsWithin_le_nhds
  have hProd : Tendsto (fun z => R z * F z) (𝓝[≠] (0 : ℂ)) (𝓝 (A * L)) := hR.mul hL
  have hEq : (fun z => R z * F z) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => A :=
    hu.mono fun z hz => resolvent_mul_original_at_unit A hz
  have hAL := tendsto_nhds_unique (hProd.congr' hEq) tendsto_const_nhds
  have heComm : (fun z => A * F z) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => F z * A) := by
    filter_upwards [hu] with z hz
    have hc : Commute (R z) A := by
      change (z • (1 : Matrix n n ℂ) + A) * A = A * (z • (1 : Matrix n n ℂ) + A)
      rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have hh : R z * (A * F z) = R z * (F z * A) := calc
      _ = A * (R z * F z) := by rw [← mul_assoc, hc.eq, mul_assoc]
      _ = _ := by rw [← mul_assoc (R z) (F z), resolvent_mul_original_at_unit A hz]
    exact hz.mul_left_cancel hh
  have hComm : Commute A L := by
    exact tendsto_nhds_unique (((tendsto_const_nhds (x := A)).mul hL).congr' heComm)
      (hL.mul (tendsto_const_nhds (x := A)))
  refine ⟨hAL, hComm, ?_⟩
  intro v hv
  change A *ᵥ v = 0 at hv
  change L *ᵥ v = 0
  have hc : Continuous (fun M : Matrix n n ℂ => M *ᵥ v) :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have h := hc.continuousAt.tendsto.comp hL
  have he : (fun z => F z *ᵥ v) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 :=
    Eventually.of_forall (fun z => by
      change ((R z)⁻¹ * A) *ᵥ v = 0
      rw [← mulVec_mulVec, hv, mulVec_zero])
  exact tendsto_nhds_unique (h.congr' he) tendsto_const_nhds

/-- At index one the resolvent product tends to the range projection
along the kernel. -/
theorem resolvent_mul_original_tendsto_groupProjector {A X : Matrix n n ℂ}
    (hX : IsGroupInverse A X) :
    Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + A)⁻¹ * A) (𝓝[≠] 0) (𝓝 (A * X)) := by
  let Q (z : ℂ) := 1 + z • X
  let P := A * X
  have hQ : Continuous Q := continuous_const.add (continuous_id.smul continuous_const)
  have hQ₀ : Q 0 = 1 := by simp [Q]
  have hInv : ContinuousAt (Inv.inv : Matrix n n ℂ → Matrix n n ℂ) (1 : Matrix n n ℂ) := by
    apply continuousAt_matrix_inv
    simpa only [Matrix.det_one, Ring.inverse_eq_inv'] using continuousAt_inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)
  have ht : Tendsto (fun z : ℂ => P * (Q z)⁻¹) (𝓝[≠] 0) (𝓝 P) := by
    have h : Tendsto Q (𝓝 (0 : ℂ)) (𝓝 (Q 0)) := hQ.continuousAt
    rw [hQ₀] at h
    have hi : Tendsto (fun z : ℂ => (Q z)⁻¹) (𝓝[≠] 0)
        (𝓝 ((1 : Matrix n n ℂ)⁻¹)) := (hInv.tendsto.comp h).mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_apply, inv_one, mul_one] using
      (tendsto_const_nhds (x := P)).mul hi
  have hQdet : Tendsto (fun z : ℂ => (Q z).det) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have h : Tendsto (fun z => (Q z).det) (𝓝 (0 : ℂ)) (𝓝 (Q 0).det) :=
      (hQ.matrix_det).continuousAt
    simpa only [hQ₀, Matrix.det_one] using h
  have hQne : ∀ᶠ z in 𝓝 (0 : ℂ), (Q z).det ≠ 0 :=
    hQdet (isOpen_compl_singleton.mem_nhds (show (1 : ℂ) ∉ {0} from one_ne_zero))
  apply ht.congr'
  filter_upwards [isUnit_smul_one_add_eventually A, hQne.filter_mono nhdsWithin_le_nhds] with z hz hq
  symm
  apply hz.mul_left_cancel
  rw [resolvent_mul_original_at_unit A hz, ← mul_assoc]
  have hP : (z • (1 : Matrix n n ℂ) + A) * P = A * Q z := by
    have hA : A * P = A := by
      change A * (A * X) = A
      have h := hX.stable
      rw [pow_two, pow_one, mul_assoc] at h
      exact h
    rw [add_mul, smul_mul_assoc, one_mul, hA]
    change z • P + A = A * (1 + z • X)
    rw [mul_add, mul_one, mul_smul_comm, add_comm]
  rw [hP, mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq), mul_one]

/-- **Exercise 19** of [benIsrael2003generalized], Chapter 4.
The resolvent product has a finite limit at zero exactly at index one. -/
theorem exercise_4_19 (A : Matrix n n ℂ) :
    (∃ L, Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + A)⁻¹ * A) (𝓝[≠] 0) (𝓝 L)) ↔
      matrixIndex A = 1 := by
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨hAL, hc, hk⟩ := resolvent_mul_original_algebra A hL
    have hker : (A ^ 1).mulVecLin.ker = (A ^ (1 + 1)).mulVecLin.ker := by
      refine le_antisymm (A.monotone_ker_mulVecLin_pow (by decide)) ?_
      intro v hv
      have hAv : A *ᵥ v ∈ A.mulVecLin.ker := by
        change A *ᵥ (A *ᵥ v) = 0
        rw [mulVec_mulVec, ← pow_two]
        exact hv
      have hLv : L *ᵥ (A *ᵥ v) = 0 := hk hAv
      change (A ^ 1) *ᵥ v = 0
      rw [pow_one, ← hAL, hc.eq, ← mulVec_mulVec, hLv]
    exact le_antisymm ((A.rank_pow_eq_succ_iff Nat.one_pos).mp
      ((A.rank_pow_eq_iff_ker_eq (Nat.le_succ 1)).mpr hker)) A.rankStabilizationIndex_spec.1
  · intro hA
    obtain ⟨X, hX, _⟩ := (theorem_4_2 A).mpr hA
    exact ⟨A * X, resolvent_mul_original_tendsto_groupProjector hX⟩

/-- **Exercise 20** of [benIsrael2003generalized], Chapter 4.
The resolvent of the range projection tends to the Moore–Penrose inverse
exactly for a range-Hermitian matrix. -/
theorem exercise_4_20 (A : Matrix n n ℂ) :
    IsRangeHermitian A ↔
      Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + A)⁻¹ * (A * A.pinv))
        (𝓝[≠] 0) (𝓝 A.pinv) := by
  constructor
  · intro hA
    have hc := (rangeHermitian_iff_commute_pinv A).mp hA
    have hX : IsGroupInverse A A.pinv := _root_.isGroupInverse_iff.mpr
      ⟨hc, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩
    have h := (resolvent_mul_original_tendsto_groupProjector hX).mul (tendsto_const_nhds (x := A.pinv))
    rw [hc.eq, A.pinv_mul_self_mul_pinv] at h
    simpa only [mul_assoc] using h
  · intro h
    have hT := h.mul (tendsto_const_nhds (x := A))
    have hF : Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + A)⁻¹ * A)
        (𝓝[≠] 0) (𝓝 (A.pinv * A)) := by
      simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc A A.pinv A, A.mul_pinv_mul_self] using hT
    obtain ⟨hAL, hc, _⟩ := resolvent_mul_original_algebra A hF
    unfold IsRangeHermitian
    have hR : LinearMap.range (toEuclideanLin A) ≤ LinearMap.range (toEuclideanLin Aᴴ) := by
      intro u hu
      obtain ⟨v, rfl⟩ := hu
      have he : toEuclideanLin (A.pinv * A) (toEuclideanLin A v) = toEuclideanLin A v := by
        rw [← toEuclideanLin_mul_apply, ← hc.eq, hAL]
      rw [A.pinv_mul_eq_starProjection] at he
      exact Submodule.starProjection_eq_self_iff.mp he
    exact Submodule.eq_of_le_of_finrank_eq hR (by
      rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.finrank_range_adjoint])

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 4.
The Gram resolvent times the adjoint converges to the Moore–Penrose
inverse at zero, including for the zero matrix. -/
theorem exercise_4_21 {m : Type*} [Fintype m] (A : Matrix m n ℂ) :
    Tendsto (fun z : ℂ => (z • (1 : Matrix n n ℂ) + Aᴴ * A)⁻¹ * Aᴴ)
      (𝓝[≠] 0) (𝓝 A.pinv) := by
  classical
  let G := Aᴴ * A
  have hG : G.IsHermitian := isHermitian_conjTranspose_mul_self A
  have hGR : IsRangeHermitian G := exercise_4_15 G (by
    change G * Gᴴ = Gᴴ * G
    rw [hG.eq])
  have hcont : Continuous (fun B : Matrix n n ℂ => B * Aᴴ) :=
    Continuous.matrix_mul continuous_id continuous_const
  have h := hcont.continuousAt.tendsto.comp ((exercise_4_20 G).mp hGR)
  have hp : G.pinv * Aᴴ = A.pinv := (BenIsraelGreville.Chapter01.pinv_gram A).1.symm
  have hc : (G * G.pinv) * Aᴴ = Aᴴ := by
    rw [Matrix.mul_assoc, hp]
    change Aᴴ * A * A.pinv = Aᴴ
    rw [Matrix.mul_assoc, A.conjTranspose_mul_mul_pinv]
  have he (z : ℂ) :
      ((z • (1 : Matrix n n ℂ) + G)⁻¹ * (G * G.pinv)) * Aᴴ =
        (z • (1 : Matrix n n ℂ) + G)⁻¹ * Aᴴ := by
    rw [Matrix.mul_assoc, hc]
  rw [hp] at h
  exact h.congr' (Eventually.of_forall he)

end Resolvent

end BenIsraelGreville.Chapter04
