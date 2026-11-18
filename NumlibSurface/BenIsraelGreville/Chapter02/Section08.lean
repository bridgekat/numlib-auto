/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import Numlib.LinearAlgebra.Matrix.Rank
import NumlibSurface.BenIsraelGreville.Chapter02.Section01
import NumlibSurface.BenIsraelGreville.Chapter00.Section04

/-!
# Efficient characterizations of classes of generalized inverses

Section 2.8 of [benIsrael2003generalized] uses bases of the two null spaces
and of the range of a projection to give nonredundant matrix coordinates
for several Penrose classes.

## Deviations from the source

* The parameter count in (110) is `m(n − r)`, the number of entries in
  its displayed parameter matrix.
* The identities in (107) have sizes `n − r` for `GF`, `r` for `DB`,
  and `m − r` for `KH`.
-/

noncomputable section

namespace BenIsraelGreville.Chapter02

open Matrix
open scoped ComplexOrder
open BenIsraelGreville.Chapter01 (definition_1)

variable {m n k l r s : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [Fintype r] [Fintype s]

section Coordinates

omit [Fintype n] [Fintype s] in
private theorem mat_mul_eq_of_columns {F : Matrix n k ℂ} {X Y : Matrix k s ℂ}
    (hF : Function.Injective F.mulVecLin) (h : F * X = F * Y) : X = Y := by
  ext i j
  have he : X.col j = Y.col j := hF (by
    change F *ᵥ X.col j = F *ᵥ Y.col j
    rw [← col_mul_eq_mulVec_col, ← col_mul_eq_mulVec_col, h])
  exact congrFun he i

omit [Fintype s] in
private theorem mat_eq_of_mul_surj {K : Matrix k n ℂ} {X Y : Matrix s k ℂ}
    (hK : Function.Surjective K.mulVecLin) (h : X * K = Y * K) : X = Y := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  obtain ⟨y, rfl⟩ := hK x
  change X *ᵥ (K *ᵥ y) = Y *ᵥ (K *ᵥ y)
  rw [mulVec_mulVec, mulVec_mulVec, h]

private theorem matrix_mul_eq_self_of_range {P : Matrix n n ℂ} {F : Matrix n k ℂ}
    (hP : IsIdempotentElem P) (hF : LinearMap.range F.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    P * F = F := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  obtain ⟨y, hy⟩ := hF (LinearMap.mem_range_self F.mulVecLin x)
  change P *ᵥ y = F *ᵥ x at hy
  rw [← mulVec_mulVec, ← hy, mulVec_mulVec, hP.eq]

private theorem exists_projectionCoordinates [DecidableEq k]
    {P : Matrix n n ℂ} {F : Matrix n k ℂ}
    (hP : IsIdempotentElem P) (hF : Function.Injective F.mulVecLin)
    (hR : LinearMap.range F.mulVecLin = LinearMap.range P.mulVecLin) :
    ∃ G : Matrix k n ℂ, F * G = P ∧ G * F = 1 := by
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_mulVecLin_le (le_of_eq hR.symm)
  refine ⟨G, hG, mat_mul_eq_of_columns hF ?_⟩
  rw [← Matrix.mul_assoc, hG, Matrix.mul_one, matrix_mul_eq_self_of_range hP (le_of_eq hR)]

private theorem range_kernelProjection [DecidableEq n] {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    (hU : A.IsInnerInverse U) :
    LinearMap.range (1 - U * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  have he : A * (1 - U * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, sub_self]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change A *ᵥ ((1 - U * A) *ᵥ y) = 0
    rw [mulVec_mulVec, he, zero_mulVec]
  · intro hx
    change A *ᵥ x = 0 at hx
    refine ⟨x, ?_⟩
    change (1 - U * A) *ᵥ x = x
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hx, mulVec_zero, sub_zero]

private theorem idempotent_kernelProjection [DecidableEq n]
    {A : Matrix m n ℂ} {U : Matrix n m ℂ} (hU : A.IsInnerInverse U) :
    IsIdempotentElem (1 - U * A) := by
  have h := hU.isIdempotentElem_mul_rev.eq
  change (1 - U * A) * (1 - U * A) = 1 - U * A
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, h, sub_self, sub_zero]

private theorem adjoint_innerInverse {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    (hU : A.IsInnerInverse U) : Aᴴ.IsInnerInverse Uᴴ := by
  simpa only [isInnerInverse_iff, conjTranspose_mul, Matrix.mul_assoc] using
    congrArg Matrix.conjTranspose (isInnerInverse_iff.mp hU)

variable [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l] [DecidableEq r]

/-- The fixed coordinate matrices in (106)–(108). The first and third
basis matrices are indexed by the two nullities, and the range basis is
indexed by the rank. -/
structure InnerInverseCoordinates (A : Matrix m n ℂ) (U : Matrix n m ℂ)
    (F : Matrix n k ℂ) (B : Matrix n r ℂ) (K : Matrix l m ℂ) where
  /-- Coordinates of the projection onto the right null space. -/
  G : Matrix k n ℂ
  /-- The coordinate transpose for the left null space. -/
  H : Matrix m l ℂ
  /-- Coordinates of the complementary range projection. -/
  D : Matrix r n ℂ
  FG : F * G = 1 - U * A
  HK : H * K = 1 - A * U
  BD : B * D = U * A
  GF : G * F = 1
  KH : K * H = 1
  DB : D * B = 1
  GB : G * B = 0
  DF : D * F = 0
  AF : A * F = 0
  KA : K * A = 0

omit [DecidableEq n] in
private theorem exists_leftNull_coordinates {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {K : Matrix l m ℂ} (hU : A.IsInnerInverse U)
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker Aᴴ.mulVecLin) :
    ∃ H : Matrix m l ℂ, H * K = 1 - A * U ∧ K * H = 1 ∧ K * A = 0 := by
  have hUa := adjoint_innerInverse hU
  obtain ⟨J, hJ, hJK⟩ := exists_projectionCoordinates (idempotent_kernelProjection hUa) hK
    (hKr.trans (range_kernelProjection hUa).symm)
  have hzero : Aᴴ * Kᴴ = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    rw [← mulVec_mulVec, zero_mulVec]
    have hy := LinearMap.mem_range_self Kᴴ.mulVecLin y
    rw [hKr] at hy
    exact hy
  refine ⟨Jᴴ, ?_, ?_, ?_⟩
  · simpa only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
      conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose hJ
  · simpa only [conjTranspose_mul, conjTranspose_one, conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hJK
  · simpa only [conjTranspose_mul, conjTranspose_zero, conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hzero

omit [DecidableEq m] in
private theorem exists_rightNull_coordinates {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} (hU : A.IsInnerInverse U)
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin) :
    ∃ G : Matrix k n ℂ, F * G = 1 - U * A ∧ G * F = 1 ∧ A * F = 0 := by
  obtain ⟨G, hG, hGF⟩ := exists_projectionCoordinates (idempotent_kernelProjection hU) hF
    (hFr.trans (range_kernelProjection hU).symm)
  refine ⟨G, hG, hGF, Matrix.ext_iff_mulVec.mpr fun y => ?_⟩
  rw [← mulVec_mulVec, zero_mulVec]
  have hy := LinearMap.mem_range_self F.mulVecLin y
  rw [hFr] at hy
  exact hy

/-- **Equations (106)–(108)** of [benIsrael2003generalized], Chapter 2.
The three indicated column bases give coordinate matrices with the required
projection and cancellation identities. -/
theorem exists_innerInverseCoordinates {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} {B : Matrix n r ℂ} {K : Matrix l m ℂ}
    (hU : A.IsInnerInverse U)
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin)
    (hB : Function.Injective B.mulVecLin)
    (hBr : LinearMap.range B.mulVecLin = LinearMap.range (U * A).mulVecLin)
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker Aᴴ.mulVecLin) :
    Nonempty (InnerInverseCoordinates A U F B K) := by
  obtain ⟨G, hG, hGF, hAF⟩ := exists_rightNull_coordinates hU hF hFr
  obtain ⟨D, hD, hDB⟩ := exists_projectionCoordinates hU.isIdempotentElem_mul_rev hB hBr
  obtain ⟨H, hH, hKH, hKA⟩ := exists_leftNull_coordinates hU hK hKr
  have hBfix := matrix_mul_eq_self_of_range hU.isIdempotentElem_mul_rev (le_of_eq hBr)
  have hGB : G * B = 0 := by
    apply mat_mul_eq_of_columns hF
    rw [← Matrix.mul_assoc, hG, Matrix.sub_mul, Matrix.one_mul, hBfix, sub_self, Matrix.mul_zero]
  have hDF : D * F = 0 := by
    apply mat_mul_eq_of_columns hB
    rw [← Matrix.mul_assoc, hD, Matrix.mul_assoc, hAF, Matrix.mul_zero, Matrix.mul_zero]
  exact ⟨⟨G, H, D, hG, hH, hD, hGF, hKH, hDB, hGB, hDF, hAF, hKA⟩⟩

omit [DecidableEq m] [DecidableEq n] in
private theorem innerInverse_difference {A : Matrix m n ℂ} {U X : Matrix n m ℂ}
    (hU : A.IsInnerInverse U) :
    A.IsInnerInverse X ↔ A * (X - U) * A = 0 := by
  rw [isInnerInverse_iff, Matrix.mul_sub, Matrix.sub_mul, hU, sub_eq_zero]

/-- **Equations (105) and (109)** of [benIsrael2003generalized], Chapter 2.
All inner inverses have unique coordinates `(Y,Z)`, given by the stated
products with the coordinate matrices. -/
theorem innerInverse_parameters {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} {B : Matrix n r ℂ} {K : Matrix l m ℂ}
    (hU : A.IsInnerInverse U) (C : InnerInverseCoordinates A U F B K) (X : Matrix n m ℂ) :
    (A.IsInnerInverse X ↔ ∃! yz : Matrix k m ℂ × Matrix r l ℂ,
      X = U + F * yz.1 + B * yz.2 * K) ∧
    ∀ (Y : Matrix k m ℂ) (Z : Matrix r l ℂ), X = U + F * Y + B * Z * K →
      Y = C.G * (X - U) ∧ Z = C.D * (X - U) * C.H := by
  have hRecover (Y : Matrix k m ℂ) (Z : Matrix r l ℂ)
      (h : X = U + F * Y + B * Z * K) :
      Y = C.G * (X - U) ∧ Z = C.D * (X - U) * C.H := by
    have he : X - U = F * Y + B * Z * K := by rw [h]; abel
    constructor
    · rw [he, Matrix.mul_add, ← Matrix.mul_assoc C.G F, C.GF, Matrix.one_mul,
        ← Matrix.mul_assoc C.G (B * Z), ← Matrix.mul_assoc C.G B, C.GB,
        Matrix.zero_mul, Matrix.zero_mul, add_zero]
    · rw [he, Matrix.mul_add, ← Matrix.mul_assoc C.D F, C.DF, Matrix.zero_mul,
        ← Matrix.mul_assoc C.D (B * Z), ← Matrix.mul_assoc C.D B, C.DB,
        Matrix.one_mul, zero_add, Matrix.mul_assoc Z, C.KH, Matrix.mul_one]
  refine ⟨⟨?_, ?_⟩, hRecover⟩
  · intro hX
    let W := X - U
    have hw : A * W * A = 0 := (innerInverse_difference hU).mp hX
    have hz : (U * A) * W * (A * U) = 0 := calc
      _ = U * (A * W * A) * U := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hw, Matrix.mul_zero, Matrix.zero_mul]
    have hs : F * (C.G * W) + B * (C.D * W * C.H) * K = W := calc
      _ = (F * C.G) * W + (B * C.D) * W * (C.H * K) := by simp only [Matrix.mul_assoc]
      _ = W := by
        rw [C.FG, C.BD, C.HK, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub ((U * A) * W), Matrix.mul_one, hz, sub_zero]
        abel
    refine ⟨(C.G * W, C.D * W * C.H), ?_, ?_⟩
    · change X = U + F * (C.G * W) + B * (C.D * W * C.H) * K
      rw [add_assoc, hs]
      dsimp [W]
      abel
    · rintro ⟨Y, Z⟩ he
      exact Prod.ext (hRecover Y Z he).1 (hRecover Y Z he).2
  · rintro ⟨⟨Y, Z⟩, he, _⟩
    have hy : A * (F * Y) * A = 0 := by
      rw [← Matrix.mul_assoc, C.AF, Matrix.zero_mul, Matrix.zero_mul]
    have hz : A * (B * Z * K) * A = 0 := by
      simp only [Matrix.mul_assoc, C.KA, Matrix.mul_zero]
    apply (innerInverse_difference hU).mpr
    have heq : X - U = F * Y + B * Z * K := by rw [he]; abel
    rw [heq, Matrix.mul_add, Matrix.add_mul, hy, hz, add_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- **Equation (110)** of [benIsrael2003generalized], Chapter 2.
Adding a linear combination of the right-null-space basis gives each
Hermitian left-product inner inverse exactly once. -/
theorem hermitianInnerInverse_left_parameters {A : Matrix m n ℂ} {U X : Matrix n m ℂ}
    {F : Matrix n k ℂ} (hU : U ∈ definition_1 A {.inner, .hermitianMul})
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin) :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔ ∃! Y : Matrix k m ℂ, X = U + F * Y := by
  classical
  rw [theorem_3 hU]
  obtain ⟨G, hG, hGF, hAF⟩ := exists_rightNull_coordinates
    (BenIsraelGreville.Chapter01.mem_one_three_iff.mp hU).1 hF hFr
  constructor
  · intro h
    have hz : A * (X - U) = 0 := by rw [Matrix.mul_sub, h, sub_self]
    have he : F * (G * (X - U)) = X - U := by
      rw [← Matrix.mul_assoc, hG, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hz,
        Matrix.mul_zero, sub_zero]
    refine ⟨G * (X - U), ?_, fun Y hY => ?_⟩
    · change X = U + F * (G * (X - U))
      rw [he]
      abel
    · have hY' : X - U = F * Y := by rw [hY]; abel
      rw [hY', ← Matrix.mul_assoc, hGF, Matrix.one_mul]
  · rintro ⟨Y, rfl, _⟩
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hAF, Matrix.zero_mul, add_zero]

omit [DecidableEq n] [DecidableEq m] [DecidableEq l] in
/-- **Equation (111)** of [benIsrael2003generalized], Chapter 2.
Adding a linear combination of the left-null-space rows gives each
Hermitian right-product inner inverse exactly once. -/
theorem hermitianInnerInverse_right_parameters {A : Matrix m n ℂ} {U X : Matrix n m ℂ}
    {K : Matrix l m ℂ} (hU : U ∈ definition_1 A {.inner, .hermitianMulRev})
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker Aᴴ.mulVecLin) :
    X ∈ definition_1 A {.inner, .hermitianMulRev} ↔ ∃! Y : Matrix n l ℂ, X = U + Y * K := by
  classical
  rw [theorem_4 hU]
  obtain ⟨H, hH, hKH, hKA⟩ := exists_leftNull_coordinates
    (BenIsraelGreville.Chapter01.mem_one_four_iff.mp hU).1 hK hKr
  constructor
  · intro h
    have hz : (X - U) * A = 0 := by rw [Matrix.sub_mul, h, sub_self]
    have he : (X - U) * H * K = X - U := by
      rw [Matrix.mul_assoc, hH, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hz,
        Matrix.zero_mul, sub_zero]
    refine ⟨(X - U) * H, ?_, fun Y hY => ?_⟩
    · change X = U + (X - U) * H * K
      rw [he]
      abel
    · have hY' : X - U = Y * K := by rw [hY]; abel
      rw [hY', Matrix.mul_assoc, hKH, Matrix.mul_one]
  · rintro ⟨Y, rfl, _⟩
    rw [Matrix.add_mul, Matrix.mul_assoc, hKA, Matrix.mul_zero, add_zero]

/-- **Exercise 80** of [benIsrael2003generalized], Chapter 2.
Any inner inverses of the three basis matrices give the fixed coordinates. -/
theorem exercise_80 {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} {B : Matrix n r ℂ} {K : Matrix l m ℂ}
    (C : InnerInverseCoordinates A U F B K)
    {F' : Matrix k n ℂ} {B' : Matrix r n ℂ} {K' : Matrix m l ℂ}
    (hF : F.IsInnerInverse F') (hB : B.IsInnerInverse B') (hK : K.IsInnerInverse K') :
    C.G = F' * (1 - U * A) ∧ C.H = (1 - A * U) * K' ∧ C.D = B' * (U * A) := by
  have hf : F' * F = 1 := calc
    F' * F = 1 * (F' * F) := (Matrix.one_mul _).symm
    _ = C.G * (F * F' * F) := by rw [← C.GF]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hF, C.GF]
  have hb : B' * B = 1 := calc
    B' * B = 1 * (B' * B) := (Matrix.one_mul _).symm
    _ = C.D * (B * B' * B) := by rw [← C.DB]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hB, C.DB]
  have hk : K * K' = 1 := calc
    K * K' = (K * K') * 1 := (Matrix.mul_one _).symm
    _ = (K * K' * K) * C.H := by rw [← C.KH]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hK, C.KH]
  refine ⟨?_, ?_, ?_⟩
  · rw [← C.FG, ← Matrix.mul_assoc, hf, Matrix.one_mul]
  · rw [← C.HK, Matrix.mul_assoc, hk, Matrix.mul_one]
  · rw [← C.BD, ← Matrix.mul_assoc, hb, Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- The middle product of a full-rank factorization of a reflexive inverse
is the identity in its inner coordinates. -/
theorem reflexiveInverse_middle_identity {A : Matrix m n ℂ}
    (Y₀ : Matrix n r ℂ) (Z₀ : Matrix r m ℂ)
    (hY : Function.Injective Y₀.mulVecLin) (hZ : Function.Surjective Z₀.mulVecLin)
    (hU : A.IsOuterInverse (Y₀ * Z₀)) :
    Z₀ * A * Y₀ = 1 := by
  apply mat_mul_eq_of_columns hY
  apply mat_eq_of_mul_surj hZ
  simpa only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul] using
    (isOuterInverse_iff.mp hU)

/-- **Equations (112)–(113)** of [benIsrael2003generalized], Chapter 2.
The displayed products give all reflexive inverses exactly once, and the
two recovery formulas are inverse to this parametrization. -/
theorem reflexiveInverse_parameters {A : Matrix m n ℂ}
    {F : Matrix n k ℂ} {K : Matrix l m ℂ} (Y₀ : Matrix n r ℂ) (Z₀ : Matrix r m ℂ)
    (hU : A.IsInnerInverse (Y₀ * Z₀))
    (hmid : Z₀ * A * Y₀ = 1)
    (C : InnerInverseCoordinates A (Y₀ * Z₀) F Y₀ K) (X : Matrix n m ℂ) :
    ((A.IsInnerInverse X ∧ A.IsOuterInverse X) ↔
      ∃! pq : Matrix k r ℂ × Matrix r l ℂ, X = (Y₀ + F * pq.1) * (Z₀ + pq.2 * K)) ∧
    ∀ (P : Matrix k r ℂ) (Q : Matrix r l ℂ), X = (Y₀ + F * P) * (Z₀ + Q * K) →
      P = C.G * X * A * Y₀ ∧ Q = Z₀ * A * X * C.H := by
  let U := Y₀ * Z₀
  have hUY : U * A * Y₀ = Y₀ := calc
    _ = Y₀ * (Z₀ * A * Y₀) := by simp only [U, Matrix.mul_assoc]
    _ = _ := by rw [hmid, Matrix.mul_one]
  have hZU : Z₀ * A * U = Z₀ := by rw [← Matrix.mul_assoc, hmid, Matrix.one_mul]
  have hAY (P : Matrix k r ℂ) : A * (Y₀ + F * P) = A * Y₀ := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, C.AF, Matrix.zero_mul, add_zero]
  have hZA (Q : Matrix r l ℂ) : (Z₀ + Q * K) * A = Z₀ * A := by
    rw [Matrix.add_mul, Matrix.mul_assoc Q, C.KA, Matrix.mul_zero, add_zero]
  have hRecover (P : Matrix k r ℂ) (Q : Matrix r l ℂ)
      (h : X = (Y₀ + F * P) * (Z₀ + Q * K)) :
      P = C.G * X * A * Y₀ ∧ Q = Z₀ * A * X * C.H := by
    have hZY : Z₀ * C.H = 0 := by
      apply mat_eq_of_mul_surj (K := K) ?_
      · rw [Matrix.mul_assoc, C.HK, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
          hZU, sub_self, Matrix.zero_mul]
      · intro x
        refine ⟨C.H *ᵥ x, ?_⟩
        change K *ᵥ (C.H *ᵥ x) = x
        rw [mulVec_mulVec, C.KH, one_mulVec]
    constructor
    · have he : X * A * Y₀ = Y₀ + F * P := calc
        _ = (Y₀ + F * P) * (((Z₀ + Q * K) * A) * Y₀) := by
          rw [h]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hZA, hmid, Matrix.mul_one]
      rw [Matrix.mul_assoc C.G X, Matrix.mul_assoc C.G, he, Matrix.mul_add,
        ← Matrix.mul_assoc C.G F, C.GF, C.GB, Matrix.one_mul, zero_add]
    · have he : Z₀ * A * X = Z₀ + Q * K := calc
        _ = (Z₀ * (A * (Y₀ + F * P))) * (Z₀ + Q * K) := by
          rw [h]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hAY, ← Matrix.mul_assoc, hmid, Matrix.one_mul]
      rw [he, Matrix.add_mul, Matrix.mul_assoc Q, C.KH, Matrix.mul_one, hZY, zero_add]
  refine ⟨⟨?_, ?_⟩, hRecover⟩
  · rintro ⟨hi, ho⟩
    let P := C.G * X * A * Y₀
    let Q := Z₀ * A * X * C.H
    have hY : Y₀ + F * P = X * A * Y₀ := calc
      _ = Y₀ + (F * C.G) * (X * A * Y₀) := by simp only [P, Matrix.mul_assoc]
      _ = _ := by
        rw [C.FG, Matrix.sub_mul, Matrix.one_mul]
        have h : (U * A) * (X * A * Y₀) = U * (A * X * A) * Y₀ := by
          simp only [Matrix.mul_assoc]
        change _ + (_ - (U * A) * (X * A * Y₀)) = _
        rw [h, hi, hUY]
        abel
    have hZ : Z₀ + Q * K = Z₀ * A * X := calc
      _ = Z₀ + (Z₀ * A * X) * (C.H * K) := by simp only [Q, Matrix.mul_assoc]
      _ = _ := by
        rw [C.HK, Matrix.mul_sub, Matrix.mul_one]
        have h : (Z₀ * A * X) * (A * U) = Z₀ * (A * X * A) * U := by
          simp only [Matrix.mul_assoc]
        change _ + (_ - (Z₀ * A * X) * (A * U)) = _
        rw [h, hi, hZU]
        abel
    refine ⟨(P, Q), ?_, ?_⟩
    · change X = (Y₀ + F * P) * (Z₀ + Q * K)
      rw [hY, hZ]
      calc
        X = X * A * X := (isOuterInverse_iff.mp ho).symm
        _ = X * (A * U * A) * X := by rw [hU]
        _ = _ := by simp only [U, Matrix.mul_assoc]
    · rintro ⟨P', Q'⟩ he
      exact Prod.ext (hRecover P' Q' he).1 (hRecover P' Q' he).2
  · rintro ⟨⟨P, Q⟩, he, _⟩
    change X = (Y₀ + F * P) * (Z₀ + Q * K) at he
    have hZX : (Z₀ + Q * K) * A * (Y₀ + F * P) = 1 := by
      rw [hZA, Matrix.mul_assoc, hAY, ← Matrix.mul_assoc, hmid]
    constructor
    · rw [isInnerInverse_iff, he]
      calc
        _ = (A * (Y₀ + F * P)) * ((Z₀ + Q * K) * A) := by simp only [Matrix.mul_assoc]
        _ = A := by
          rw [hAY, hZA]
          simpa only [U, Matrix.mul_assoc] using isInnerInverse_iff.mp hU
    · rw [isOuterInverse_iff, he]
      calc
        _ = (Y₀ + F * P) * ((Z₀ + Q * K) * A * (Y₀ + F * P)) * (Z₀ + Q * K) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hZX, Matrix.mul_one]

/-- For a full-rank factorization of a reflexive inverse, the first
factor is the range basis required by the fixed coordinate construction. -/
theorem exists_reflexiveInverseCoordinates {A : Matrix m n ℂ}
    {F : Matrix n k ℂ} {K : Matrix l m ℂ} (Y₀ : Matrix n r ℂ) (Z₀ : Matrix r m ℂ)
    (hU : A.IsInnerInverse (Y₀ * Z₀)) (hV : A.IsOuterInverse (Y₀ * Z₀))
    (hY : Function.Injective Y₀.mulVecLin) (hZ : Function.Surjective Z₀.mulVecLin)
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin)
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker Aᴴ.mulVecLin) :
    Nonempty (InnerInverseCoordinates A (Y₀ * Z₀) F Y₀ K) := by
  have hm := reflexiveInverse_middle_identity Y₀ Z₀ hY hZ hV
  have hY₀ : (Y₀ * Z₀ * A) * Y₀ = Y₀ := calc
    _ = Y₀ * (Z₀ * A * Y₀) := by simp only [Matrix.mul_assoc]
    _ = Y₀ := by rw [hm, Matrix.mul_one]
  have hr : LinearMap.range Y₀.mulVecLin = LinearMap.range (Y₀ * Z₀ * A).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨Y₀ *ᵥ x, ?_⟩
      change (Y₀ * Z₀ * A) *ᵥ (Y₀ *ᵥ x) = Y₀ *ᵥ x
      rw [mulVec_mulVec, hY₀]
    · rw [Matrix.mul_assoc, mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
  exact exists_innerInverseCoordinates hU hF hFr hY hr hK hKr

/-- **Equation (114) and Exercise 83** of [benIsrael2003generalized], Chapter 2.
With range and kernel of the two induced projections prescribed, the
remaining coordinates are exactly one arbitrary matrix. -/
theorem exercise_83 {A : Matrix m n ℂ}
    {S : Submodule ℂ (m → ℂ)} {T : Submodule ℂ (n → ℂ)}
    (hS : IsCompl A.mulVecLin.range S) (hT : IsCompl T A.mulVecLin.ker)
    {U : Matrix n m ℂ} (hU : A.IsInnerInverse U)
    {F : Matrix n k ℂ} {B : Matrix n r ℂ} {K : Matrix l m ℂ}
    (C : InnerInverseCoordinates A U F B K) (X : Matrix n m ℂ) :
    let Z := projectorMatrix hT * U * projectorMatrix hS
    (A.IsInnerInverse X ∧ (A * X).mulVecLin.ker = S ∧ (X * A).mulVecLin.range = T) ↔
      ∃! W : Matrix k l ℂ, X = Z + F * W * K := by
  intro Z
  have h := theorem_12 A hS hT U hU
  rw [h.1 X, h.2.1 X]
  change (∃ Y, X = Z + (1 - U * A) * Y * (1 - A * U)) ↔ _
  rw [← C.FG, ← C.HK]
  constructor
  · rintro ⟨Y, hY⟩
    let W := C.G * Y * C.H
    have hW : X = Z + F * W * K := by
      rw [hY]
      simp only [W, Matrix.mul_assoc]
    refine ⟨W, hW, fun V hV => ?_⟩
    have he : F * V * K = F * W * K := add_left_cancel (hV.symm.trans hW)
    have h' := congrArg (fun M : Matrix n m ℂ => C.G * M * C.H) he
    have hcancel (M : Matrix k l ℂ) : C.G * (F * M * K) * C.H = M := calc
      _ = (C.G * F) * M * (K * C.H) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [C.GF, C.KH, Matrix.one_mul, Matrix.mul_one]
    change C.G * (F * V * K) * C.H = C.G * (F * W * K) * C.H at h'
    simpa only [hcancel] using h'
  · rintro ⟨W, hW, _⟩
    refine ⟨F * W * K, ?_⟩
    rw [hW]
    have h : (F * C.G) * (F * W * K) * (C.H * K) = F * W * K := calc
      _ = F * (C.G * F) * W * (K * C.H) * K := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [C.GF, C.KH, Matrix.mul_one, Matrix.mul_one]
    rw [h]

/-- **Equation (115)** of [benIsrael2003generalized], Chapter 2.
The null-space perturbation adds exactly the rank of its coordinate
matrix to the rank of the reference reflexive inverse. -/
theorem exercise_82_rank {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} {B : Matrix n r ℂ} {K : Matrix l m ℂ}
    (hU : A.IsInnerInverse U) (hV : A.IsOuterInverse U)
    (C : InnerInverseCoordinates A U F B K) (Z : Matrix k l ℂ) :
    (U + F * Z * K).rank = A.rank + Z.rank := by
  let N := F * Z * K
  let X := U + N
  have hAN : A * N = 0 := by simp [N, ← Matrix.mul_assoc, C.AF]
  have hNA : N * A = 0 := by simp [N, Matrix.mul_assoc, C.KA]
  have hXU : X * (A * U) = U := by
    rw [show X = U + N from rfl, Matrix.add_mul, ← Matrix.mul_assoc U, hV,
      ← Matrix.mul_assoc N, hNA, Matrix.zero_mul, add_zero]
  have hXN : X * (1 - A * U) = N := by
    rw [Matrix.mul_sub, Matrix.mul_one, hXU]
    change U + N - U = N
    abel
  have hRU : LinearMap.range U.mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [← hXU, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hRN : LinearMap.range N.mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [← hXN, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hR : LinearMap.range X.mulVecLin =
      LinearMap.range U.mulVecLin ⊔ LinearMap.range N.mulVecLin := by
    refine le_antisymm ?_ (sup_le hRU hRN)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.mpr ⟨U.mulVecLin x, ⟨x, rfl⟩, N.mulVecLin x, ⟨x, rfl⟩,
      by change _ = (U + N) *ᵥ x; rw [add_mulVec]; rfl⟩
  have hDS : Disjoint (LinearMap.range U.mulVecLin) (LinearMap.range N.mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨u, hu⟩ ⟨v, hv⟩
    change U *ᵥ u = x at hu
    change N *ᵥ v = x at hv
    have hx : A *ᵥ x = 0 := by rw [← hv, mulVec_mulVec, hAN, zero_mulVec]
    rw [← hu, ← show U * A * U = U from hV, ← mulVec_mulVec, ← mulVec_mulVec,
      hu, hx, mulVec_zero]
  have hN : N.rank = Z.rank := by
    refine le_antisymm ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)) ?_
    have he : C.G * N * C.H = Z := calc
      _ = (C.G * F) * Z * (K * C.H) := by simp only [N, Matrix.mul_assoc]
      _ = _ := by rw [C.GF, C.KH, Matrix.one_mul, Matrix.mul_one]
    rw [← he]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hr := (Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range U.mulVecLin) (LinearMap.range N.mulVecLin))
  rw [← hR, hDS.eq_bot, finrank_bot, add_zero] at hr
  change X.rank = U.rank + N.rank at hr
  rw [(hU.isOuterInverse_iff_rank_eq).mp hV, hN] at hr
  exact hr

end Coordinates

omit [Fintype m] in
private theorem card_nullSpaceBasis {A : Matrix m n ℂ} {F : Matrix n k ℂ}
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin) :
    Fintype.card k + A.rank = Fintype.card n := by
  have hf := LinearMap.finrank_range_of_inj hF
  rw [hFr, Module.finrank_fintype_fun_eq_card] at hf
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) = _ at h
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

/-- The parameter counts of (105), (110), (111), and (112), computed
from bases of the two null spaces and the rank of the matrix. -/
theorem efficientInverse_parameterCounts {A : Matrix m n ℂ} {F : Matrix n k ℂ}
    {K : Matrix l m ℂ} (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin)
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker Aᴴ.mulVecLin) :
    Fintype.card k * Fintype.card m + A.rank * Fintype.card l =
      Fintype.card m * Fintype.card n - A.rank ^ 2 ∧
    Fintype.card k * Fintype.card m = Fintype.card m * (Fintype.card n - A.rank) ∧
    Fintype.card n * Fintype.card l = Fintype.card n * (Fintype.card m - A.rank) ∧
    Fintype.card k * A.rank + A.rank * Fintype.card l =
      A.rank * (Fintype.card m + Fintype.card n - 2 * A.rank) := by
  have hn := card_nullSpaceBasis hF hFr
  have hm := card_nullSpaceBasis hK hKr
  rw [Matrix.rank_conjTranspose] at hm
  have hn' : Fintype.card n = Fintype.card k + A.rank := hn.symm
  have hm' : Fintype.card m = Fintype.card l + A.rank := hm.symm
  have hsum : Fintype.card m + Fintype.card n - 2 * A.rank = Fintype.card k + Fintype.card l :=
    by omega
  have hp : Fintype.card k * Fintype.card m + A.rank * Fintype.card l + A.rank ^ 2 =
      Fintype.card m * Fintype.card n := by rw [hn', hm']; ring
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [show Fintype.card n - A.rank = Fintype.card k by omega, mul_comm]
  · rw [show Fintype.card m - A.rank = Fintype.card l by omega]
  · rw [hsum]
    ring

section RankExercises

open Matrix
open scoped ComplexOrder
open BenIsraelGreville.Chapter01 (exists_innerInverse mem_one_iff mem_one_two_iff)

private theorem exists_basisMatrix_of_finrank {m r : ℕ} (V : Submodule ℂ (Fin m → ℂ))
    (hr : Module.finrank ℂ V = r) :
    ∃ B : Matrix (Fin m) (Fin r) ℂ, Function.Injective B.mulVecLin ∧
      LinearMap.range B.mulVecLin = V := by
  let e := (Module.finBasisOfFinrankEq ℂ V hr).equivFun.symm
  let b := V.subtype.comp e.toLinearMap
  refine ⟨LinearMap.toMatrix' b, ?_⟩
  have hb : (LinearMap.toMatrix' b).mulVecLin = b := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  rw [hb]
  refine ⟨Subtype.val_injective.comp e.injective, ?_⟩
  rw [show b = V.subtype.comp e.toLinearMap from rfl, LinearMap.range_comp,
    e.range, Submodule.map_top, Submodule.range_subtype]

private theorem finrank_ker_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Module.finrank ℂ A.mulVecLin.ker = n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℂ A.mulVecLin.ker = Module.finrank ℂ (Fin n → ℂ) at h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

/-- **Exercise 84** of [benIsrael2003generalized], Chapter 2.
An inner inverse with the prescribed projections has rank (\rho) for some
choice of parameters exactly when the rank of (A) is at most (\rho) and
(\rho) is at most the smaller dimension of (A). -/
theorem exercise_84 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    {S : Submodule ℂ (Fin m → ℂ)} {T : Submodule ℂ (Fin n → ℂ)}
    (hS : IsCompl A.mulVecLin.range S) (hT : IsCompl T A.mulVecLin.ker) (ρ : ℕ) :
    (∃ X : Matrix (Fin n) (Fin m) ℂ, A.IsInnerInverse X ∧
      (A * X).mulVecLin.ker = S ∧ (X * A).mulVecLin.range = T ∧ X.rank = ρ) ↔
      A.rank ≤ ρ ∧ ρ ≤ min m n := by
  constructor
  · rintro ⟨X, hX, _, _, hρ⟩
    exact hρ ▸ ⟨hX.rank_le, le_min X.rank_le_width X.rank_le_height⟩
  · rintro ⟨hρ, hρ'⟩
    obtain ⟨U, hU⟩ := exists_innerInverse A
    have hU := mem_one_iff.mp hU
    let U₀ := projectorMatrix hT * U * projectorMatrix hS
    have hRef := (theorem_12 A hS hT U hU).2.2.1
    have hU₀ := mem_one_two_iff.mp hRef.1
    have hCenter : A.IsInnerInverse U₀ ∧
        (A * U₀).mulVecLin.ker = S ∧ (U₀ * A).mulVecLin.range = T := by
      have ho := isOuterInverse_iff_isInnerInverse.mp hU₀.2
      exact ⟨hU₀.1, ho.ker_mul_rev.trans hRef.2.2, ho.range_mul.trans hRef.2.1⟩
    obtain ⟨F, hF, hFr⟩ := exists_basisMatrix_of_finrank _ (finrank_ker_matrix A)
    obtain ⟨K₀, hK, hKr⟩ := exists_basisMatrix_of_finrank _ (by
      rw [finrank_ker_matrix, Matrix.rank_conjTranspose] :
      Module.finrank ℂ Aᴴ.mulVecLin.ker = m - A.rank)
    obtain ⟨B, hB, hBr⟩ := exists_basisMatrix_of_finrank
      (LinearMap.range (U₀ * A).mulVecLin) rfl
    obtain ⟨C⟩ := exists_innerInverseCoordinates hU₀.1 hF hFr hB hBr
      (K := K₀ᴴ) (by simpa only [conjTranspose_conjTranspose] using hK)
      (by simpa only [conjTranspose_conjTranspose] using hKr)
    have ht₁ : ρ - A.rank ≤ n - A.rank := Nat.sub_le_sub_right (hρ'.trans (min_le_right _ _)) _
    have ht₂ : ρ - A.rank ≤ m - A.rank := Nat.sub_le_sub_right (hρ'.trans (min_le_left _ _)) _
    let Z : Matrix (Fin (n - A.rank)) (Fin (m - A.rank)) ℂ :=
      rectDiagonal fun i => if i < ρ - A.rank then 1 else 0
    have hZ : Z.rank = ρ - A.rank := by
      dsimp only [Z]
      rw [rank_rectDiagonal]
      let e : {j : Fin (m - A.rank) //
          (j : ℕ) < n - A.rank ∧ (if (j : ℕ) < ρ - A.rank then (1 : ℂ) else 0) ≠ 0} ≃
          Fin (ρ - A.rank) :=
        { toFun := fun j => ⟨j.val.val, by
            have hz := j.property.2
            by_contra! hj
            exact hz (ite_eq_right (not_lt.mpr hj))⟩
          invFun := fun j => ⟨Fin.castLE ht₂ j, j.isLt.trans_le ht₁, by
            rw [Fin.val_castLE, ite_eq_left j.isLt]
            exact one_ne_zero⟩
          left_inv := fun j => Subtype.ext (Fin.ext rfl)
          right_inv := fun j => Fin.ext rfl }
      rw [Fintype.card_congr e, Fintype.card_fin]
    let X := U₀ + F * Z * K₀ᴴ
    have hAX : A * X = A * U₀ := by
      change A * (U₀ + F * Z * K₀ᴴ) = A * U₀
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, C.AF, Matrix.zero_mul, add_zero]
    have hXA : X * A = U₀ * A := by
      change (U₀ + F * Z * K₀ᴴ) * A = U₀ * A
      simp only [Matrix.add_mul, Matrix.mul_assoc, C.KA, Matrix.mul_zero, add_zero]
    refine ⟨X, ?_, hAX ▸ hCenter.2.1, hXA ▸ hCenter.2.2, ?_⟩
    · rw [isInnerInverse_iff, hAX]
      exact hCenter.1
    · change (U₀ + F * Z * K₀ᴴ).rank = ρ
      rw [exercise_82_rank hU₀.1 hU₀.2 C Z, hZ, Nat.add_sub_of_le hρ]

end RankExercises

section FamiliesExercises

open Matrix

variable {m n r k l : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype k] [Fintype l]

/-- The six efficient families in **Exercise 85** of [benIsrael2003generalized].
The matrices $S$ and $T$ are the factors, $Y$ and $Z$ are their chosen one-sided
inverses, and $F$ and $K^H$ give the two null-space bases of $ST$. -/
structure FullRankInverseFamilies
    (S : Matrix m r ℂ) (T : Matrix r n ℂ) (Y : Matrix n r ℂ) (Z : Matrix r m ℂ)
    (F : Matrix n k ℂ) (K : Matrix l m ℂ) : Prop where
  /-- All left inverses of the first factor, with unique coordinates. -/
  first : ∀ Z' : Matrix r m ℂ, S.IsInnerInverse Z' ↔ ∃! V : Matrix r l ℂ, Z' = Z + V * K
  /-- All right inverses of the second factor, with unique coordinates. -/
  second : ∀ Y' : Matrix n r ℂ, T.IsInnerInverse Y' ↔ ∃! U : Matrix k r ℂ, Y' = Y + F * U
  /-- All left products, described using either the original matrix or its first factor. -/
  leftProducts : ∀ M : Matrix m m ℂ,
    ((∃ X, (S * T).IsInnerInverse X ∧ (S * T) * X = M) ↔
      (∃ Z', S.IsInnerInverse Z' ∧ S * Z' = M)) ∧
    ((∃ Z', S.IsInnerInverse Z' ∧ S * Z' = M) ↔
      ∃! V : Matrix r l ℂ, M = S * (Z + V * K))
  /-- All right products, described using either the original matrix or its second factor. -/
  rightProducts : ∀ M : Matrix n n ℂ,
    ((∃ X, (S * T).IsInnerInverse X ∧ X * (S * T) = M) ↔
      (∃ Y', T.IsInnerInverse Y' ∧ Y' * T = M)) ∧
    ((∃ Y', T.IsInnerInverse Y' ∧ Y' * T = M) ↔
      ∃! U : Matrix k r ℂ, M = (Y + F * U) * T)
  /-- The three affine coordinate blocks of an arbitrary inner inverse. -/
  inner : ∀ X : Matrix n m ℂ, (S * T).IsInnerInverse X ↔
    ∃! p : Matrix k r ℂ × Matrix r l ℂ × Matrix k l ℂ,
      X = Y * Z + Y * p.2.1 * K + F * p.1 * Z + F * p.2.2 * K
  /-- Decomposition as a reflexive inverse and a uniquely determined null-space perturbation. -/
  split : ∀ X : Matrix n m ℂ, (S * T).IsInnerInverse X ↔
    ∃! p : Matrix n m ℂ × Matrix k l ℂ,
      (S * T).IsInnerInverse p.1 ∧ (S * T).IsOuterInverse p.1 ∧ X = p.1 + F * p.2 * K

variable [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq k] [DecidableEq l]

/-- **Exercise 85** of [benIsrael2003generalized], Chapter 2.
For a full-rank factorization $ST$ with chosen inverses $Y,Z$ of the
factors, the six displayed parametrizations are exact and nonredundant.
Here $TY=I$ and $ZS=I$ express that the inverses are one-sided. -/
theorem exercise_85 (S : Matrix m r ℂ) (T : Matrix r n ℂ) (Y : Matrix n r ℂ) (Z : Matrix r m ℂ)
    (hY : T * Y = 1) (hZ : Z * S = 1) (F : Matrix n k ℂ) (K : Matrix l m ℂ)
    (hF : Function.Injective F.mulVecLin)
    (hFr : LinearMap.range F.mulVecLin = LinearMap.ker (S * T).mulVecLin)
    (hK : Function.Injective Kᴴ.mulVecLin)
    (hKr : LinearMap.range Kᴴ.mulVecLin = LinearMap.ker (S * T)ᴴ.mulVecLin) :
    FullRankInverseFamilies S T Y Z F K := by
  let A := S * T
  have hin : A.IsInnerInverse (Y * Z) := by
    rw [isInnerInverse_iff]
    calc
      A * (Y * Z) * A = S * (T * Y) * (Z * S) * T := by simp [A, Matrix.mul_assoc]
      _ = A := by simp [A, hY, hZ]
  have hmid : Z * A * Y = 1 := by
    calc
      Z * A * Y = (Z * S) * (T * Y) := by simp [A, Matrix.mul_assoc]
      _ = 1 := by simp [hY, hZ]
  have hout : A.IsOuterInverse (Y * Z) := by
    rw [isOuterInverse_iff]
    calc
      Y * Z * A * (Y * Z) = Y * (Z * A * Y) * Z := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hmid, Matrix.mul_one]
  have hYinj : Function.Injective Y.mulVecLin :=
    fun x y h => by
      have he := congrArg (T *ᵥ ·) h
      change T *ᵥ (Y *ᵥ x) = T *ᵥ (Y *ᵥ y) at he
      simpa only [mulVec_mulVec, hY, one_mulVec] using he
  have hZsurj : Function.Surjective Z.mulVecLin := fun x =>
    ⟨S *ᵥ x, by
      change Z *ᵥ (S *ᵥ x) = x
      rw [mulVec_mulVec, hZ, one_mulVec]⟩
  obtain ⟨C⟩ := exists_reflexiveInverseCoordinates Y Z hin hout hYinj hZsurj hF hFr hK hKr
  have hKS : K * S = 0 := by
    calc
      _ = (K * A) * Y := by simp [A, Matrix.mul_assoc, hY]
      _ = _ := by rw [C.KA, Matrix.zero_mul]
  have hTF : T * F = 0 := by
    calc
      _ = Z * (A * F) := by simp only [A, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
      _ = _ := by rw [C.AF, Matrix.mul_zero]
  have hSZ : A * (Y * Z) = S * Z := by
    calc
      _ = S * (T * Y) * Z := by simp [A, Matrix.mul_assoc]
      _ = _ := by rw [hY, Matrix.mul_one]
  have hYT : (Y * Z) * A = Y * T := by
    calc
      _ = Y * (Z * S) * T := by simp [A, Matrix.mul_assoc]
      _ = _ := by rw [hZ, Matrix.mul_one]
  have hHK : C.H * K = 1 - S * Z := C.HK.trans (congrArg (1 - ·) hSZ)
  have hFG : F * C.G = 1 - Y * T := C.FG.trans (congrArg (1 - ·) hYT)
  have hZH : Z * C.H = 0 := by
    calc
      _ = (Z * (C.H * K)) * C.H := by
        simp only [Matrix.mul_assoc, C.KH, Matrix.mul_one]
      _ = _ := by
        rw [hHK, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hZ, Matrix.one_mul,
          sub_self, Matrix.zero_mul]
  have hZSiff (Z' : Matrix r m ℂ) : S.IsInnerInverse Z' ↔ Z' * S = 1 := by
    constructor
    · intro hz
      calc
        Z' * S = Z * (S * Z' * S) := by
          simp only [← Matrix.mul_assoc, hZ, Matrix.one_mul]
        _ = 1 := by rw [isInnerInverse_iff.mp hz, hZ]
    · intro hz
      rw [isInnerInverse_iff, Matrix.mul_assoc, hz, Matrix.mul_one]
  have hTYiff (Y' : Matrix n r ℂ) : T.IsInnerInverse Y' ↔ T * Y' = 1 := by
    constructor
    · intro hy
      calc
        T * Y' = (T * Y' * T) * Y := by simp only [Matrix.mul_assoc, hY, Matrix.mul_one]
        _ = 1 := by rw [isInnerInverse_iff.mp hy, hY]
    · intro hy
      rw [isInnerInverse_iff, hy, Matrix.one_mul]
  have hfirst (Z' : Matrix r m ℂ) :
      S.IsInnerInverse Z' ↔ ∃! V : Matrix r l ℂ, Z' = Z + V * K := by
    rw [hZSiff]
    constructor
    · intro hz
      refine ⟨(Z' - Z) * C.H, ?_, ?_⟩
      · change Z' = Z + ((Z' - Z) * C.H) * K
        have hz₀ : (Z' - Z) * (S * Z) = 0 := by
          rw [← Matrix.mul_assoc, Matrix.sub_mul, hz, hZ, sub_self, Matrix.zero_mul]
        rw [Matrix.mul_assoc, hHK, Matrix.mul_sub, Matrix.mul_one, hz₀, sub_zero]
        abel
      · intro v hv
        rw [hv, add_sub_cancel_left, Matrix.mul_assoc, C.KH, Matrix.mul_one]
    · rintro ⟨v, rfl, _⟩
      simp only [Matrix.add_mul, Matrix.mul_assoc, hZ, hKS, Matrix.mul_zero, add_zero]
  have hsecond (Y' : Matrix n r ℂ) :
      T.IsInnerInverse Y' ↔ ∃! U : Matrix k r ℂ, Y' = Y + F * U := by
    rw [hTYiff]
    constructor
    · intro hy
      refine ⟨C.G * (Y' - Y), ?_, ?_⟩
      · change Y' = Y + F * (C.G * (Y' - Y))
        have hy₀ : (Y * T) * (Y' - Y) = 0 := by
          rw [Matrix.mul_assoc, Matrix.mul_sub, hy, hY, sub_self, Matrix.mul_zero]
        rw [← Matrix.mul_assoc, hFG, Matrix.sub_mul, Matrix.one_mul, hy₀, sub_zero]
        abel
      · intro u hu
        rw [hu, add_sub_cancel_left, ← Matrix.mul_assoc, C.GF, Matrix.one_mul]
    · rintro ⟨u, rfl, _⟩
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, hY, hTF, Matrix.zero_mul, add_zero]
  have hinner (X : Matrix n m ℂ) : A.IsInnerInverse X ↔ T * X * S = 1 := by
    constructor
    · intro hx
      calc
        T * X * S = Z * (A * X * A) * Y := by simp only [A, ← Matrix.mul_assoc, hZ,
          Matrix.one_mul, Matrix.mul_assoc (T * X * S), hY, Matrix.mul_one]
        _ = 1 := by rw [isInnerInverse_iff.mp hx, hmid]
    · intro hx
      rw [isInnerInverse_iff]
      calc
        A * X * A = S * (T * X * S) * T := by simp [A, Matrix.mul_assoc]
        _ = A := by simp [A, hx]
  refine ⟨hfirst, hsecond, ?_, ?_, ?_, ?_⟩
  · intro M
    constructor
    · constructor
      · rintro ⟨X, hx, hM⟩
        exact ⟨T * X, (hZSiff _).mpr ((hinner X).mp hx), by simpa [A, Matrix.mul_assoc] using hM⟩
      · rintro ⟨Z', hz, hM⟩
        refine ⟨Y * Z', (hinner _).mpr ?_, ?_⟩
        · rw [← Matrix.mul_assoc, hY, Matrix.one_mul, (hZSiff _).mp hz]
        · simpa only [A, ← Matrix.mul_assoc, Matrix.mul_assoc S T Y, hY, Matrix.mul_one] using hM
    · constructor
      · rintro ⟨Z', hz, rfl⟩
        obtain ⟨V, hV, huniq⟩ := (hfirst Z').mp hz
        refine ⟨V, congrArg (S * ·) hV, fun W hW => huniq W ?_⟩
        have he := congrArg (Z * ·) hW
        simpa only [← Matrix.mul_assoc, hZ, Matrix.one_mul] using he
      · rintro ⟨V, rfl, _⟩
        exact ⟨Z + V * K, (hZSiff _).mpr (by
          rw [Matrix.add_mul, hZ, Matrix.mul_assoc, hKS, Matrix.mul_zero, add_zero]), rfl⟩
  · intro M
    constructor
    · constructor
      · rintro ⟨X, hx, hM⟩
        exact ⟨X * S, (hTYiff _).mpr (by simpa [Matrix.mul_assoc] using (hinner X).mp hx),
          by simpa [A, Matrix.mul_assoc] using hM⟩
      · rintro ⟨Y', hy, hM⟩
        refine ⟨Y' * Z, (hinner _).mpr ?_, ?_⟩
        · simpa only [Matrix.mul_assoc, hZ, Matrix.mul_one] using (hTYiff _).mp hy
        · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Z S T, hZ, Matrix.one_mul]
          exact hM
    · constructor
      · rintro ⟨Y', hy, rfl⟩
        obtain ⟨U, hU, huniq⟩ := (hsecond Y').mp hy
        refine ⟨U, congrArg (· * T) hU, fun W hW => huniq W ?_⟩
        have he := congrArg (· * Y) hW
        simpa only [Matrix.mul_assoc, hY, Matrix.mul_one] using he
      · rintro ⟨U, rfl, _⟩
        exact ⟨Y + F * U, (hTYiff _).mpr (by
          rw [Matrix.mul_add, hY, ← Matrix.mul_assoc, hTF, Matrix.zero_mul, add_zero]), rfl⟩
  · intro X
    change A.IsInnerInverse X ↔ _
    let P (u : Matrix k r ℂ) (w : Matrix k l ℂ) := u * Z + w * K
    have hrepr (p : Matrix k r ℂ × Matrix r l ℂ × Matrix k l ℂ) :
        Y * Z + Y * p.2.1 * K + F * p.1 * Z + F * p.2.2 * K =
          Y * Z + F * P p.1 p.2.2 + Y * p.2.1 * K := by
      simp only [P, Matrix.mul_add, ← Matrix.mul_assoc]
      abel
    have hPS (u : Matrix k r ℂ) (w : Matrix k l ℂ) : P u w * S = u := by
      simp [P, Matrix.add_mul, Matrix.mul_assoc, hKS, hZ]
    have hPH (u : Matrix k r ℂ) (w : Matrix k l ℂ) : P u w * C.H = w := by
      simp [P, Matrix.add_mul, Matrix.mul_assoc, hZH, C.KH]
    have hP (p : Matrix k m ℂ) : P (p * S) (p * C.H) = p := by
      change (p * S) * Z + (p * C.H) * K = p
      rw [Matrix.mul_assoc _ S, Matrix.mul_assoc _ C.H, hHK, ← Matrix.mul_add]
      rw [show S * Z + (1 - S * Z) = 1 by abel, Matrix.mul_one]
    rw [(innerInverse_parameters hin C X).1]
    constructor
    · rintro ⟨⟨p, v⟩, hp, huniq⟩
      refine ⟨(p * S, v, p * C.H), ?_, ?_⟩
      · change X = Y * Z + Y * v * K + F * (p * S) * Z + F * (p * C.H) * K
        rw [hrepr (p * S, v, p * C.H), hP]
        exact hp
      · rintro ⟨u', v', w'⟩ h'
        change X = Y * Z + Y * v' * K + F * u' * Z + F * w' * K at h'
        rw [hrepr (u', v', w')] at h'
        have hq := huniq (P u' w', v') h'
        have hq₁ : P u' w' = p := congrArg Prod.fst hq
        exact Prod.ext (by change u' = p * S; rw [← hq₁, hPS])
          (Prod.ext (congrArg Prod.snd hq) (by change w' = p * C.H; rw [← hq₁, hPH]))
    · rintro ⟨⟨u, v, w⟩, h, huniq⟩
      change X = Y * Z + Y * v * K + F * u * Z + F * w * K at h
      rw [hrepr (u, v, w)] at h
      refine ⟨(P u w, v), h, ?_⟩
      rintro ⟨p', v'⟩ h'
      have hq := huniq (p' * S, v', p' * C.H) (by
        change X = Y * Z + Y * v' * K + F * (p' * S) * Z + F * (p' * C.H) * K
        rw [hrepr (p' * S, v', p' * C.H), hP]
        exact h')
      refine Prod.ext ?_ (congrArg (fun t => t.2.1) hq)
      have he : P (p' * S) (p' * C.H) = P u w :=
        congrArg (fun t : Matrix k r ℂ × Matrix r l ℂ × Matrix k l ℂ => P t.1 t.2.2) hq
      rw [hP] at he
      exact he
  · intro X
    change A.IsInnerInverse X ↔ _
    have hcancel (D : Matrix k l ℂ) : C.G * (F * D * K) * C.H = D := by
      calc
        _ = (C.G * F) * D * (K * C.H) := by simp only [Matrix.mul_assoc]
        _ = D := by simp [C.GF, C.KH]
    have hproj (R : Matrix n m ℂ) (D : Matrix k l ℂ) :
        A * (R + F * D * K) = A * R ∧ (R + F * D * K) * A = R * A := by
      constructor
      · simp only [Matrix.mul_add, ← Matrix.mul_assoc, C.AF, Matrix.zero_mul, add_zero]
      · simp only [Matrix.add_mul, Matrix.mul_assoc, C.KA, Matrix.mul_zero, add_zero]
    constructor
    · intro hx
      let R := X * A * X
      let D := C.G * (X - R) * C.H
      have hR : A.IsInnerInverse R ∧ A.IsOuterInverse R :=
        ⟨hx.isInnerInverse_mul hx, hx.isOuterInverse_mul hx⟩
      have hleft : A * (X - R) = 0 := by rw [Matrix.mul_sub, hx.mul_mul_inner, sub_self]
      have hright : (X - R) * A = 0 := by rw [Matrix.sub_mul, hx.inner_mul_mul, sub_self]
      have he : F * D * K = X - R := by
        calc
          _ = (F * C.G) * (X - R) * (C.H * K) := by simp only [D, Matrix.mul_assoc]
          _ = X - R := by
            rw [C.FG, C.HK, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ A, hleft,
              Matrix.mul_zero, sub_zero, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
              hright, Matrix.zero_mul, sub_zero]
      have hX : X = R + F * D * K := by rw [he]; abel
      refine ⟨(R, D), ⟨hR.1, hR.2, hX⟩, ?_⟩
      rintro ⟨R', D'⟩ ⟨_, ho, hX'⟩
      change X = R' + F * D' * K at hX'
      have hRR : R = R' := by
        change X * A * X = R'
        nth_rw 1 [hX']
        rw [(hproj R' D').2, hX', Matrix.mul_assoc, (hproj R' D').1, ← Matrix.mul_assoc]
        exact ho
      have hDD : D' = D := by
        have he' : F * D' * K = F * D * K := add_left_cancel (hX'.symm.trans (hRR ▸ hX))
        have h := congrArg (fun W : Matrix n m ℂ => C.G * W * C.H) he'
        simpa only [hcancel] using h
      exact Prod.ext hRR.symm hDD
    · rintro ⟨⟨R, D⟩, ⟨hi, _, hX⟩, _⟩
      change X = R + F * D * K at hX
      rw [isInnerInverse_iff, hX, (hproj R D).1]
      exact hi

end FamiliesExercises

section HermiteExample

open Matrix
open BenIsraelGreville.Chapter00 (hermiteExampleMatrix)
open BenIsraelGreville.Chapter01 (mem_one_iff)

noncomputable section

/-- The first rank factor of the example matrix in Equation (0.85). -/
def hermiteExampleFirst : Matrix (Fin 3) (Fin 2) ℂ := !![2 * Complex.I, 0; 0, -3; 2, 1]

/-- The second rank factor of the example matrix in Equation (0.85). -/
def hermiteExampleSecond : Matrix (Fin 2) (Fin 6) ℂ :=
  !![0, 1, 1 / 2, 0, 1 - 2 * Complex.I, -(Complex.I / 2);
    0, 0, 0, 1, 2, 1 + Complex.I]

/-- The right inverse of the second rank factor selects columns two and four. -/
def hermiteExampleY : Matrix (Fin 6) (Fin 2) ℂ :=
  !![0, 0; 1, 0; 0, 0; 0, 1; 0, 0; 0, 0]

/-- The left inverse of the first rank factor printed in Exercise 86. -/
def hermiteExampleZ : Matrix (Fin 2) (Fin 3) ℂ := !![-(Complex.I / 2), 0, 0; 0, -1 / 3, 0]

/-- The right null-space basis printed in Exercise 81. -/
def hermiteExampleF : Matrix (Fin 6) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, -1 + 2 * Complex.I, 0; 0, -2, 0, Complex.I;
    0, 0, -2, -1 - Complex.I; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The conjugate-transposed left null-space basis printed in Exercise 81. -/
def hermiteExampleK : Matrix (Fin 1) (Fin 3) ℂ := !![3 * Complex.I, 1, 3]

private def hermiteExampleG : Matrix (Fin 4) (Fin 6) ℂ :=
  !![1, 0, 0, 0, 0, 0; 0, 0, -1 / 2, 0, 0, Complex.I / 2;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

private def hermiteExampleH : Matrix (Fin 3) (Fin 1) ℂ := !![0; 0; 1 / 3]

/-- The zero-parameter inverse of the example in Chapter 1, Exercise 6. -/
def hermiteExampleReflexiveInverse : Matrix (Fin 6) (Fin 3) ℂ :=
  !![0, 0, 0; -(Complex.I / 2), 0, 0; 0, 0, 0; 0, -1 / 3, 0; 0, 0, 0; 0, 0, 0]

set_option maxHeartbeats 4000000 in
/-- The concrete matrices in Exercises 81 and 86 satisfy the printed
factorization, one-sided inverse, and kernel projection identities. -/
private theorem hermiteExample_inverse_data :
    hermiteExampleFirst * hermiteExampleSecond = hermiteExampleMatrix ∧
      hermiteExampleSecond * hermiteExampleY = 1 ∧ hermiteExampleZ * hermiteExampleFirst = 1 ∧
      hermiteExampleY * hermiteExampleZ = hermiteExampleReflexiveInverse ∧
      hermiteExampleSecond * hermiteExampleF = 0 ∧ hermiteExampleK * hermiteExampleFirst = 0 ∧
      hermiteExampleG * hermiteExampleF = 1 ∧ hermiteExampleK * hermiteExampleH = 1 ∧
      hermiteExampleF * hermiteExampleG = 1 - hermiteExampleY * hermiteExampleSecond ∧
      hermiteExampleH * hermiteExampleK = 1 - hermiteExampleFirst * hermiteExampleZ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [hermiteExampleFirst, hermiteExampleSecond, hermiteExampleMatrix,
        hermiteExampleY, hermiteExampleZ, hermiteExampleF, hermiteExampleK,
        hermiteExampleG, hermiteExampleH, hermiteExampleReflexiveInverse,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, Fin.succ]

/-- The rank factorization in Equation (0.85) has the stated one-sided inverses. -/
theorem hermiteExample_rankFactorization :
    hermiteExampleMatrix = hermiteExampleFirst * hermiteExampleSecond ∧
      hermiteExampleSecond * hermiteExampleY = 1 ∧ hermiteExampleZ * hermiteExampleFirst = 1 :=
  ⟨hermiteExample_inverse_data.1.symm, hermiteExample_inverse_data.2.1,
    hermiteExample_inverse_data.2.2.1⟩

private theorem kernel_basis_of_splitting {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] {A : Matrix m n ℂ} {U : Matrix n m ℂ}
    {F : Matrix n k ℂ} {G : Matrix k n ℂ}
    (hAF : A * F = 0) (hGF : G * F = 1) (hFG : F * G = 1 - U * A) :
    Function.Injective F.mulVecLin ∧ LinearMap.range F.mulVecLin = LinearMap.ker A.mulVecLin := by
  constructor
  · intro x y h
    have he := congrArg (G *ᵥ ·) h
    change G *ᵥ (F *ᵥ x) = G *ᵥ (F *ᵥ y) at he
    simpa only [mulVec_mulVec, hGF, one_mulVec] using he
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change A *ᵥ (F *ᵥ y) = 0
      rw [mulVec_mulVec, hAF, zero_mulVec]
    · intro hx
      change A *ᵥ x = 0 at hx
      refine ⟨G *ᵥ x, ?_⟩
      change F *ᵥ (G *ᵥ x) = x
      rw [mulVec_mulVec, hFG, sub_mulVec, one_mulVec, ← mulVec_mulVec, hx, mulVec_zero, sub_zero]

/-- The printed columns of $F$ and $K^H$ give bases of the two kernels in Exercise 81. -/
theorem hermiteExample_nullSpaceBases :
    Function.Injective hermiteExampleF.mulVecLin ∧
      LinearMap.range hermiteExampleF.mulVecLin = LinearMap.ker hermiteExampleMatrix.mulVecLin ∧
      Function.Injective hermiteExampleKᴴ.mulVecLin ∧
      LinearMap.range hermiteExampleKᴴ.mulVecLin =
        LinearMap.ker hermiteExampleMatrixᴴ.mulVecLin := by
  obtain ⟨hA, hY, hZ, hU, hTF, hKS, hGF, hKH, hFG, hHK⟩ := hermiteExample_inverse_data
  have hAF : hermiteExampleMatrix * hermiteExampleF = 0 := by
    simp only [← hA, Matrix.mul_assoc, hTF, Matrix.mul_zero]
  have hKA : hermiteExampleK * hermiteExampleMatrix = 0 := by
    simp only [← hA, ← Matrix.mul_assoc, hKS, Matrix.zero_mul]
  have hFG' : hermiteExampleF * hermiteExampleG =
      1 - hermiteExampleReflexiveInverse * hermiteExampleMatrix := by
    rw [hFG, ← hU, ← hA, Matrix.mul_assoc, ← Matrix.mul_assoc hermiteExampleZ,
      hZ, Matrix.one_mul]
  have hHK' : hermiteExampleH * hermiteExampleK =
      1 - hermiteExampleMatrix * hermiteExampleReflexiveInverse := by
    rw [hHK, ← hU, ← hA, ← Matrix.mul_assoc,
      Matrix.mul_assoc hermiteExampleFirst, hY, Matrix.mul_one]
  obtain ⟨hF, hFr⟩ := kernel_basis_of_splitting hAF hGF hFG'
  obtain ⟨hK, hKr⟩ := kernel_basis_of_splitting
    (A := hermiteExampleMatrixᴴ) (U := hermiteExampleReflexiveInverseᴴ)
    (F := hermiteExampleKᴴ) (G := hermiteExampleHᴴ)
    (by simpa only [conjTranspose_mul, conjTranspose_zero] using congrArg conjTranspose hKA)
    (by simpa only [conjTranspose_mul, conjTranspose_one] using congrArg conjTranspose hKH)
    (by simpa only [conjTranspose_mul, conjTranspose_one, conjTranspose_sub] using
      congrArg conjTranspose hHK')
  exact ⟨hF, hFr, hK, hKr⟩

/-- The inverse obtained by setting the four parameters in Equation (1.7) to zero
satisfies the two Penrose equations. -/
theorem hermiteExample_reflexiveInverse :
    hermiteExampleMatrix.IsInnerInverse hermiteExampleReflexiveInverse ∧
      hermiteExampleMatrix.IsOuterInverse hermiteExampleReflexiveInverse := by
  obtain ⟨hA, hY, hZ, hU, _⟩ := hermiteExample_inverse_data
  rw [← hA, ← hU]
  constructor
  · change (hermiteExampleFirst * hermiteExampleSecond) * (hermiteExampleY * hermiteExampleZ) *
      (hermiteExampleFirst * hermiteExampleSecond) = hermiteExampleFirst * hermiteExampleSecond
    calc
      _ = hermiteExampleFirst * (hermiteExampleSecond * hermiteExampleY) *
          (hermiteExampleZ * hermiteExampleFirst) * hermiteExampleSecond := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hY, hZ, Matrix.mul_one]
  · change (hermiteExampleY * hermiteExampleZ) * (hermiteExampleFirst * hermiteExampleSecond) *
      (hermiteExampleY * hermiteExampleZ) = hermiteExampleY * hermiteExampleZ
    calc
      _ = hermiteExampleY * (hermiteExampleZ * hermiteExampleFirst) *
          (hermiteExampleSecond * hermiteExampleY) * hermiteExampleZ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hY, hZ, Matrix.mul_one]

/-- **Exercise 81** of [benIsrael2003generalized], Chapter 2.
For the matrix of Equation (0.80), the redundant family has eighteen scalar
parameters, and the efficient family has twelve plus two scalar parameters.
The two affine descriptions both give exactly the inner inverses. -/
theorem exercise_81 :
    (∀ X : Matrix (Fin 6) (Fin 3) ℂ, hermiteExampleMatrix.IsInnerInverse X ↔
      ∃ V : Matrix (Fin 6) (Fin 3) ℂ,
        X = hermiteExampleReflexiveInverse + V -
          hermiteExampleReflexiveInverse * hermiteExampleMatrix * V * hermiteExampleMatrix *
            hermiteExampleReflexiveInverse) ∧
    (∀ X : Matrix (Fin 6) (Fin 3) ℂ, hermiteExampleMatrix.IsInnerInverse X ↔
      ∃! yz : Matrix (Fin 4) (Fin 3) ℂ × Matrix (Fin 2) (Fin 1) ℂ,
        X = hermiteExampleReflexiveInverse + hermiteExampleF * yz.1 +
          hermiteExampleY * yz.2 * hermiteExampleK) ∧
    Fintype.card (Fin 6 × Fin 3) = 18 ∧
      Fintype.card ((Fin 4 × Fin 3) ⊕ (Fin 2 × Fin 1)) = 14 := by
  obtain ⟨hA, hY, hZ, hU, _⟩ := hermiteExample_inverse_data
  obtain ⟨hF, hFr, hK, hKr⟩ := hermiteExample_nullSpaceBases
  have hYinj : Function.Injective hermiteExampleY.mulVecLin :=
    fun x y h => by
      have he := congrArg (hermiteExampleSecond *ᵥ ·) h
      change hermiteExampleSecond *ᵥ (hermiteExampleY *ᵥ x) =
        hermiteExampleSecond *ᵥ (hermiteExampleY *ᵥ y) at he
      simpa only [mulVec_mulVec, hY, one_mulVec] using he
  have hZsurj : Function.Surjective hermiteExampleZ.mulVecLin := fun x =>
    ⟨hermiteExampleFirst *ᵥ x, by
      change hermiteExampleZ *ᵥ (hermiteExampleFirst *ᵥ x) = x
      rw [mulVec_mulVec, hZ, one_mulVec]⟩
  have hi := hermiteExample_reflexiveInverse.1
  have ho := hermiteExample_reflexiveInverse.2
  have hprod : hermiteExampleMatrix.IsInnerInverse (hermiteExampleY * hermiteExampleZ) ∧
      hermiteExampleMatrix.IsOuterInverse (hermiteExampleY * hermiteExampleZ) :=
    hU.symm ▸ ⟨hi, ho⟩
  obtain ⟨C⟩ := exists_reflexiveInverseCoordinates hermiteExampleY hermiteExampleZ hprod.1 hprod.2
    hYinj hZsurj hF hFr hK hKr
  refine ⟨?_, ?_, by simp, by simp⟩
  · intro X
    simpa only [mem_one_iff] using corollary_1 (X := X) (mem_one_iff.mpr hi)
  · intro X
    simpa only [hU] using (innerInverse_parameters hprod.1 C X).1

/-- **Exercise 86** of [benIsrael2003generalized], Chapter 2.
The exact matrices of Equations (0.80) and (0.85), with the printed $Z_0$,
satisfy all six efficient inverse characterizations of Exercise 85. -/
theorem exercise_86 :
    FullRankInverseFamilies hermiteExampleFirst hermiteExampleSecond hermiteExampleY
      hermiteExampleZ hermiteExampleF hermiteExampleK := by
  obtain ⟨hA, hY, hZ, _⟩ := hermiteExample_inverse_data
  obtain ⟨hF, hFr, hK, hKr⟩ := hermiteExample_nullSpaceBases
  exact exercise_85 hermiteExampleFirst hermiteExampleSecond hermiteExampleY hermiteExampleZ
    hY hZ hermiteExampleF hermiteExampleK hF (hA.symm ▸ hFr) hK (hA.symm ▸ hKr)

end

end HermiteExample

end BenIsraelGreville.Chapter02
