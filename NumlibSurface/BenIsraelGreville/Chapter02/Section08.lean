/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import Numlib.LinearAlgebra.Matrix.Rank

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

end BenIsraelGreville.Chapter02
