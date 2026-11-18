/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Drazin
import NumlibSurface.BenIsraelGreville.Chapter02.Section05
import NumlibSurface.BenIsraelGreville.Chapter04.Section04
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Block

/-!
# The Drazin inverse

Section 4.6 of [benIsrael2003generalized] constructs the Drazin inverse as a polynomial
in the matrix. The inverse satisfies the spectral inverse equations at the matrix index
and at every larger exponent.

## Deviations from the source

* **Theorem 8** (generalization). The block formula applies to any nonsingular and nilpotent
  diagonal blocks in a similarity decomposition.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Polynomial
open BenIsraelGreville.Chapter02 (spectralValues principalIdempotent primaryIndex)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Drazin inverse relation at $k$ consists of the first power equation, the second
Penrose equation, and commutation with the original matrix. -/
theorem isDrazinInverseAt_iff (k : ℕ) (A X : Matrix n n ℂ) :
    IsDrazinInverseAt k A X ↔
      SatisfiesFirstPowerEquation k A X ∧ A.IsOuterInverse X ∧ Commute A X := by
  have shift (h : Commute A X) :
      SatisfiesFirstPowerEquation k A X ↔ A ^ (k + 1) * X = A ^ k := by
    rw [SatisfiesFirstPowerEquation, pow_succ, Matrix.mul_assoc (A ^ k) A X, h.eq,
      ← Matrix.mul_assoc (A ^ k) X A]
  refine ⟨fun h => ⟨(shift h.commute).mpr h.stable, h.outer, h.commute⟩, ?_⟩
  rintro ⟨hk, ho, hc⟩
  exact ⟨hc, ho, (shift hc).mp hk⟩

/-- **Lemma 5** of [benIsrael2003generalized], Chapter 4. If $Y$ satisfies the first power
equation at exponent $k$ and commutes with $A$, then $A^k Y^{k+1}$ is a Drazin inverse
at exponent $k$. -/
theorem lemma_4_5 (k : ℕ) (A Y : Matrix n n ℂ)
    (h₁ : SatisfiesFirstPowerEquation k A Y) (h₅ : Commute A Y) :
    IsDrazinInverseAt k A (A ^ k * Y ^ (k + 1)) := by
  have h : A ^ (k + 1) * Y = A ^ k := by
    rw [pow_succ, Matrix.mul_assoc (A ^ k), h₅.eq, ← Matrix.mul_assoc (A ^ k)]
    exact h₁
  exact IsDrazinInverseAt.of_commute_pow h₅ h

/-- **Section 4.6** of [benIsrael2003generalized]. The Drazin inverse is the unique matrix
satisfying the spectral inverse equations at the index of $A$. -/
noncomputable def drazinInverse (A : Matrix n n ℂ) : Matrix n n ℂ :=
  Classical.choose (A.existsUnique_isDrazinInverseAt A.rankStabilizationIndex_spec.2).exists

/-- The Drazin inverse satisfies the spectral inverse equations at the matrix index. -/
theorem isDrazinInverseAt_drazinInverse (A : Matrix n n ℂ) :
    IsDrazinInverseAt (matrixIndex A) A (drazinInverse A) :=
  (Classical.choose_spec
    (A.existsUnique_isDrazinInverseAt A.rankStabilizationIndex_spec.2).exists).1

/-- **Theorem 7** of [benIsrael2003generalized], Chapter 4. The Drazin inverse is a polynomial
in $A$. For every $\ell$ at least the matrix index it is the unique
$\{1^\ell,2,5\}$-inverse of $A$. -/
theorem theorem_4_7 (A : Matrix n n ℂ) :
    (∃ p : ℂ[X], drazinInverse A = aeval A p) ∧
      ∀ l : ℕ, matrixIndex A ≤ l →
        IsDrazinInverseAt l A (drazinInverse A) ∧
          ∀ Y, IsDrazinInverseAt l A Y → Y = drazinInverse A := by
  refine ⟨(Classical.choose_spec
    (A.existsUnique_isDrazinInverseAt A.rankStabilizationIndex_spec.2).exists).2, ?_⟩
  intro l hl
  have h := (isDrazinInverseAt_drazinInverse A).mono hl
  exact ⟨h, fun _ hy => hy.unique h⟩

/-- At the stable range, applying the Drazin inverse and then $A$ recovers the vector. -/
theorem mulVec_drazinInverse_of_mem_stableRange {A : Matrix n n ℂ} {v : n → ℂ}
    (hv : v ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin) :
    A *ᵥ (drazinInverse A *ᵥ v) = v := by
  let k := matrixIndex A
  let X := drazinInverse A
  have h := isDrazinInverseAt_drazinInverse A
  have hEq : A * X * A ^ k = A ^ k := calc
    A * X * A ^ k = A * (A ^ k * X) := by
      rw [Matrix.mul_assoc, (h.commute.pow_left k).symm.eq]
    _ = A ^ k := by rw [← Matrix.mul_assoc, ← pow_succ' A k, h.stable]
  obtain ⟨w, rfl⟩ := hv
  change A *ᵥ (X *ᵥ (A ^ k *ᵥ w)) = A ^ k *ᵥ w
  rw [mulVec_mulVec, mulVec_mulVec, hEq]

/-- The Drazin inverse vanishes on the stable kernel of $A$. -/
theorem drazinInverse_mulVec_of_mem_stableKer {A : Matrix n n ℂ} {v : n → ℂ}
    (hv : v ∈ LinearMap.ker (A ^ matrixIndex A).mulVecLin) :
    drazinInverse A *ᵥ v = 0 := by
  let k := matrixIndex A
  let X := drazinInverse A
  have h := isDrazinInverseAt_drazinInverse A
  have hx : X ^ (k + 1) * A ^ k = X :=
    (h.commute.pow_pow k (k + 1)).symm.eq.trans (h.pow_mul_pow_succ k)
  change X *ᵥ v = 0
  change A ^ k *ᵥ v = 0 at hv
  rw [← hx, ← mulVec_mulVec, hv, mulVec_zero]

/-- **Theorem 8** of [benIsrael2003generalized], Chapter 4. In a basis where $A$ has a
nonsingular block $J_1$ and a nilpotent block $J_0$, the Drazin inverse has blocks
$J_1^{-1}$ and zero in that basis.

**Generalization.** The two blocks may be any nonsingular and nilpotent blocks. The
nonzero and zero spectral blocks of a Jordan form meet these conditions. -/
theorem theorem_4_8 {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    {A P : Matrix (i ⊕ j) (i ⊕ j) ℂ} (hP : IsUnit P)
    {J₁ : Matrix i i ℂ} {J₀ : Matrix j j ℂ} (h₁ : IsUnit J₁) (h₀ : IsNilpotent J₀)
    (hA : A = P * fromBlocks J₁ 0 0 J₀ * P⁻¹) :
    drazinInverse A = P * fromBlocks J₁⁻¹ 0 0 0 * P⁻¹ := by
  obtain ⟨k, hk⟩ := h₀
  let l := max k (matrixIndex A)
  have hz : J₀ ^ l = 0 := pow_eq_zero_of_le (le_max_left _ _) hk
  have hL := J₁.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp h₁)
  have hR := J₁.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp h₁)
  have hs : J₁ ^ (l + 1) * J₁⁻¹ = J₁ ^ l := by
    rw [pow_succ, Matrix.mul_assoc, hL, Matrix.mul_one]
  have hJ : IsDrazinInverseAt l (fromBlocks J₁ 0 0 J₀) (fromBlocks J₁⁻¹ 0 0 0) := by
    refine ⟨?_, ?_, ?_⟩
    · change fromBlocks J₁ 0 0 J₀ * fromBlocks J₁⁻¹ 0 0 0 =
        fromBlocks J₁⁻¹ 0 0 0 * fromBlocks J₁ 0 0 J₀
      simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, hL, hR]
    · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, hR,
        Matrix.one_mul]
    · simp only [fromBlocks_diagonal_pow, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, hs, hz]
  have hX := hJ.conj hP.unit
  rw [Matrix.coe_units_inv, hP.unit_spec, ← hA] at hX
  exact ((theorem_4_7 A).2 l (le_max_right _ _)).2 _ hX |>.symm

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 4. The Drazin inverse is
the sum over the nonzero spectral values of the truncated inverse expansions on
the corresponding primary components. -/
theorem corollary_4_1 (A : Matrix n n ℂ) :
    drazinInverse A = ∑ z ∈ (spectralValues A).erase 0,
      principalIdempotent A z *
        (∑ j ∈ Finset.range (primaryIndex A z),
          (((-1 : ℂ) ^ j) / z ^ (j + 1)) • (A - z • 1) ^ j) := by
  classical
  let E := principalIdempotent A
  let L := (spectralValues A).erase 0
  let S (z : ℂ) : Matrix n n ℂ := A - z • 1
  let T (z : ℂ) := ∑ j ∈ Finset.range (primaryIndex A z),
    (((-1 : ℂ) ^ j) / z ^ (j + 1)) • (S z) ^ j
  let X := ∑ z ∈ L, E z * T z
  have hE := (Chapter02.theorem_10 A).1
  have h₁ (z : ℂ) (hz : z ≠ 0) : A * (E z * T z) = E z := by
    let Y := (-z⁻¹) • S z
    have hT : T z = z⁻¹ • ∑ j ∈ Finset.range (primaryIndex A z), Y ^ j := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [Y]
      rw [smul_pow, smul_smul, ← neg_one_mul (z⁻¹), mul_pow]
      congr 1
      rw [div_eq_mul_inv, inv_pow, pow_succ]
      ring
    have hY : z⁻¹ • A = 1 - Y := by
      dsimp only [Y, S]
      rw [neg_smul, sub_neg_eq_add, smul_sub, smul_smul, inv_mul_cancel₀ hz, one_smul]
      abel
    calc
      A * (E z * T z) = E z * (A * T z) := by
        rw [← Matrix.mul_assoc, (hE.commute z).eq, Matrix.mul_assoc]
      _ = E z * ((1 - Y) * ∑ j ∈ Finset.range (primaryIndex A z), Y ^ j) := by
        rw [hT, Matrix.mul_smul, ← Matrix.smul_mul, hY]
      _ = E z := by
        rw [mul_neg_geom_sum, Matrix.mul_sub, Matrix.mul_one]
        dsimp only [Y]
        rw [smul_pow, Matrix.mul_smul, hE.annihilate z _ le_rfl, smul_zero, sub_zero]
  have hX : Commute A X := by
    apply Commute.sum_right
    intro z _
    apply (hE.commute z).mul_right
    apply Commute.sum_right
    intro j _
    have hS : Commute A (S z) := (Commute.refl A).sub_right ((Commute.one_right A).smul_right z)
    exact (hS.pow_right j).smul_right _
  have hAX : A * X = 1 - E 0 := by
    have hSum : (∑ z ∈ L, E z) + E 0 = 1 := by
      by_cases hz : 0 ∈ spectralValues A
      · calc
          (∑ z ∈ L, E z) + E 0 = ∑ z ∈ spectralValues A, E z := by
            rw [add_comm]
            exact Finset.add_sum_erase (spectralValues A) E hz
          _ = 1 := hE.sum
      · change (∑ z ∈ (spectralValues A).erase 0, E z) + E 0 = 1
        have h₀ : E 0 = 0 := hE.supported 0 hz
        rw [Finset.erase_eq_of_notMem hz, hE.sum, h₀, add_zero]
    calc
      A * X = ∑ z ∈ L, A * (E z * T z) := Finset.mul_sum _ _ _
      _ = ∑ z ∈ L, E z := Finset.sum_congr rfl fun z hz => h₁ z (Finset.mem_erase.mp hz).1
      _ = 1 - E 0 := eq_sub_of_add_eq hSum
  have hZero : E 0 * X = 0 := by
    change E 0 * (∑ z ∈ L, E z * T z) = 0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro z hz
    have hz₀ := (Finset.mem_erase.mp hz).1
    rw [← Matrix.mul_assoc, hE.mul, ite_eq_right (Ne.symm hz₀), Matrix.zero_mul]
  let k := max (matrixIndex A) (primaryIndex A 0)
  have hNil : A ^ k * E 0 = 0 := by
    have h := hE.annihilate 0 k (le_max_right _ _)
    rw [zero_smul, sub_zero] at h
    exact ((hE.commute 0).pow_left k).eq.trans h
  have hD : IsDrazinInverseAt k A X := by
    refine ⟨hX, ?_, ?_⟩
    · rw [← hX.eq, hAX, Matrix.sub_mul, Matrix.one_mul, hZero, sub_zero]
    · rw [pow_succ, Matrix.mul_assoc, hAX, Matrix.mul_sub, Matrix.mul_one, hNil, sub_zero]
  exact ((theorem_4_7 A).2 k (le_max_left _ _)).2 X hD |>.symm

/-- **Corollary 2, existence and uniqueness** of [benIsrael2003generalized], Chapter 4.
The reflexive inverses expressible as polynomials in $A$ exist exactly at index one.
In that case the only such inverse is the group inverse. -/
theorem corollary_4_2_polynomial (A : Matrix n n ℂ) :
    (∃! X : Matrix n n ℂ, A.IsInnerInverse X ∧ A.IsOuterInverse X ∧
      ∃ p : ℂ[X], X = aeval A p) ↔ matrixIndex A = 1 := by
  constructor
  · rintro ⟨X, ⟨hi, ho, p, rfl⟩, _⟩
    have hX : IsGroupInverse A (aeval A p) :=
      isGroupInverse_iff.mpr ⟨(Commute.refl A).aeval_right p, hi, ho⟩
    exact (theorem_4_2 A).mp ⟨_, hX, fun _ hY => hY.unique hX⟩
  · intro hidx
    have hX : IsGroupInverse A (drazinInverse A) :=
      ((theorem_4_7 A).2 1 hidx.le).1
    obtain ⟨hc, hi, ho⟩ := isGroupInverse_iff.mp hX
    refine ⟨_, ⟨hi, ho, (theorem_4_7 A).1⟩, ?_⟩
    rintro Y ⟨hYi, hYo, p, rfl⟩
    exact (isGroupInverse_iff.mpr ⟨(Commute.refl A).aeval_right p, hYi, hYo⟩).unique hX

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 4. A polynomial reflexive
inverse exists precisely at index one. There it is the group inverse $Aq(A)^2$ for
$q$ in the normalized factorization of the minimal polynomial. -/
theorem corollary_4_2 (A : Matrix n n ℂ) {c : ℂ} {q : ℂ[X]} (hc : c ≠ 0)
    (h : minpoly ℂ A = C c * X ^ (minpoly ℂ A).rootMultiplicity 0 * (1 - X * q)) :
    ((∃! X : Matrix n n ℂ, A.IsInnerInverse X ∧ A.IsOuterInverse X ∧
      ∃ p : ℂ[X], X = aeval A p) ↔ matrixIndex A = 1) ∧
    (matrixIndex A = 1 →
      IsGroupInverse A (A * aeval A q ^ 2) ∧
        ∀ X, IsGroupInverse A X → X = A * aeval A q ^ 2) := by
  refine ⟨corollary_4_2_polynomial A, fun hidx => ?_⟩
  let l := (minpoly ℂ A).rootMultiplicity 0
  have hl : A ^ (l + 1) * aeval A q = A ^ l := equation_14 A hc h
  have hone : A ^ (1 + 1) * aeval A q = A ^ 1 := by
    by_cases ha : IsUnit A
    · have hinv : A * aeval A q = 1 := by
        apply (ha.pow l).mul_left_cancel
        rwa [← Matrix.mul_assoc, ← pow_succ, Matrix.mul_one]
      rw [pow_succ, Matrix.mul_assoc, hinv, Matrix.mul_one]
    · have he : l = 1 := (A.rankStabilizationIndex_eq_rootMultiplicity_minpoly ha).symm.trans hidx
      rwa [he] at hl
  have hp : IsGroupInverse A (A * aeval A q ^ 2) := by
    simpa only [pow_one] using IsDrazinInverseAt.of_commute_pow
      ((Commute.refl A).aeval_right q) hone
  exact ⟨hp, fun _ hX => hX.unique hp⟩

/-- **Corollary 3** of [benIsrael2003generalized], Chapter 4. The Moore–Penrose inverse is
a polynomial in $A$ exactly when $A$ is range-Hermitian. -/
theorem corollary_4_3 (A : Matrix n n ℂ) :
    (∃ p : ℂ[X], A.pinv = aeval A p) ↔ IsRangeHermitian A := by
  constructor
  · rintro ⟨p, hp⟩
    have hC : Commute A A.pinv := by rw [hp]; exact (Commute.refl A).aeval_right p
    have hX : IsGroupInverse A A.pinv :=
      isGroupInverse_iff.mpr ⟨hC, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩
    exact (theorem_4_4 hX).mp rfl
  · intro hr
    have hc := (rangeHermitian_iff_commute_pinv A).mp hr
    have hX : IsGroupInverse A A.pinv :=
      isGroupInverse_iff.mpr ⟨hc, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩
    have hidx := (theorem_4_2 A).mp ⟨_, hX, fun _ hY => hY.unique hX⟩
    have hz := ((theorem_4_7 A).2 1 hidx.le).2 _ hX
    rw [hz]
    exact (theorem_4_7 A).1

end BenIsraelGreville.Chapter04
