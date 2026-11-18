/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section08
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Integral solutions of linear equations

Section 2.12 of [benIsrael2003generalized] constructs a rational
reflexive inverse from the Smith normal form and uses its integral
products to describe all integral solutions.

## Deviations from the source

* The last factor of the affine correction in Corollary 14 is a single
  copy of the inverse of `B` constructed from its Smith form.
-/

noncomputable section

namespace BenIsraelGreville.Chapter02

open Matrix

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Entrywise inclusion of integer matrices into rational matrices. -/
abbrev integerMatrixCast (A : Matrix m n ℤ) : Matrix m n ℚ :=
  A.map (Int.castRingHom ℚ)

/-- A rational matrix is integral when every entry comes from an integer matrix. -/
def IsIntegralMatrix (X : Matrix m n ℚ) : Prop :=
  ∃ Z : Matrix m n ℤ, integerMatrixCast Z = X

/-- A rational reflexive inverse whose two associated projections are integral. -/
structure IsIntegralReflexiveInverse (A : Matrix m n ℤ) (U : Matrix n m ℚ) : Prop where
  /-- The first Penrose equation. -/
  inner : (integerMatrixCast A).IsInnerInverse U
  /-- The second Penrose equation. -/
  outer : (integerMatrixCast A).IsOuterInverse U
  /-- Integrality of `AU`. -/
  mul : IsIntegralMatrix (integerMatrixCast A * U)
  /-- Integrality of `UA`. -/
  mul_rev : IsIntegralMatrix (U * integerMatrixCast A)

omit [Fintype m] [Fintype n] in
private theorem integerMatrixCast_injective :
    Function.Injective (integerMatrixCast : Matrix m n ℤ → Matrix m n ℚ) := by
  intro A B h
  ext i j
  have he := congrArg (fun C : Matrix m n ℚ => C i j) h
  exact Int.cast_injective he

omit [Fintype m] [Fintype p] in
@[simp] theorem integerMatrixCast_mul (A : Matrix m n ℤ) (B : Matrix n p ℤ) :
    integerMatrixCast (A * B) = integerMatrixCast A * integerMatrixCast B :=
  Matrix.map_mul

variable {a b : ℕ}

/-- The rational reciprocal diagonal of a rectangular integer diagonal matrix,
with zero entries retaining their value. -/
def reciprocalSmithDiagonal (S : Matrix (Fin a) (Fin b) ℤ) : Matrix (Fin b) (Fin a) ℚ :=
  Matrix.of fun j i => ((S i j : ℤ) : ℚ)⁻¹

private theorem integerMatrixCast_rectDiagonal (d : ℕ → ℤ) :
    integerMatrixCast (rectDiagonal d : Matrix (Fin a) (Fin b) ℤ) =
      (rectDiagonal (fun i => (d i : ℚ)) : Matrix (Fin a) (Fin b) ℚ) := by
  ext i j
  by_cases h : (i : ℕ) = j <;> simp [rectDiagonal_apply, h]

private theorem reciprocalSmithDiagonal_rectDiagonal (d : ℕ → ℤ) :
    reciprocalSmithDiagonal (rectDiagonal d : Matrix (Fin a) (Fin b) ℤ) =
      (rectDiagonal (fun i => (d i : ℚ)⁻¹) : Matrix (Fin b) (Fin a) ℚ) := by
  ext i j
  change ((rectDiagonal d j i : ℤ) : ℚ)⁻¹ = rectDiagonal (fun k => (d k : ℚ)⁻¹) i j
  rw [rectDiagonal_apply, rectDiagonal_apply]
  by_cases h : (i : ℕ) = j
  · rw [ite_eq_left h, ite_eq_left h.symm, h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Int.cast_zero, _root_.inv_zero]

private theorem isIntegralMatrix_rectDiagonal_mul_reciprocal (d : ℕ → ℤ) :
    IsIntegralMatrix ((rectDiagonal (fun i => (d i : ℚ)) : Matrix (Fin a) (Fin b) ℚ) *
      (rectDiagonal (fun i => (d i : ℚ)⁻¹) : Matrix (Fin b) (Fin a) ℚ)) := by
  refine ⟨rectDiagonal fun i => if i < b ∧ d i ≠ 0 then 1 else 0, ?_⟩
  rw [integerMatrixCast_rectDiagonal, rectDiagonal_mul_rectDiagonal]
  refine rectDiagonal_congr fun i _ _ => ?_
  by_cases hb : i < b <;> by_cases hd : d i = 0 <;> simp [hb, hd]

/-- The reciprocal diagonal satisfies both Penrose equations and both
products have integral diagonal entries. -/
theorem isIntegralReflexiveInverse_reciprocalSmithDiagonal
    {S : Matrix (Fin a) (Fin b) ℤ} {r : ℕ}
    (hS : BenIsraelGreville.Chapter00.IsSmithNormalForm S r) :
    IsIntegralReflexiveInverse S (reciprocalSmithDiagonal S) := by
  obtain ⟨d, _, rfl, _, _, _⟩ := hS
  rw [reciprocalSmithDiagonal_rectDiagonal]
  constructor
  · rw [isInnerInverse_iff, integerMatrixCast_rectDiagonal,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_mul_rectDiagonal]
    refine rectDiagonal_congr fun i ha hb => ?_
    rw [ite_eq_left ha, ite_eq_left hb, mul_inv_mul_cancel]
  · rw [isOuterInverse_iff, integerMatrixCast_rectDiagonal,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_mul_rectDiagonal]
    refine rectDiagonal_congr fun i hb ha => ?_
    rw [ite_eq_left hb, ite_eq_left ha]
    by_cases hi : (d i : ℚ) = 0
    · simp [hi]
    · rw [inv_mul_cancel₀ hi, one_mul]
  · rw [integerMatrixCast_rectDiagonal]
    exact isIntegralMatrix_rectDiagonal_mul_reciprocal d
  · rw [integerMatrixCast_rectDiagonal]
    rw [rectDiagonal_mul_rectDiagonal]
    refine ⟨rectDiagonal fun i => if i < a ∧ d i ≠ 0 then 1 else 0, ?_⟩
    rw [integerMatrixCast_rectDiagonal]
    refine rectDiagonal_congr fun i _ _ => ?_
    by_cases ha : i < a <;> by_cases hd : d i = 0 <;> simp [ha, hd]

/-- **Equation (146)** of [benIsrael2003generalized], Chapter 2.
If `PAQ=S` is a Smith normal form, the rational reflexive inverse is
`Q` times the reciprocal Smith diagonal times `P`. -/
def smithReflexiveInverse (P : Matrix (Fin a) (Fin a) ℤ)
    (S : Matrix (Fin a) (Fin b) ℤ) (Q : Matrix (Fin b) (Fin b) ℤ) : Matrix (Fin b) (Fin a) ℚ :=
  integerMatrixCast Q * reciprocalSmithDiagonal S * integerMatrixCast P

/-- The Smith-form formula satisfies the integral projection conditions. -/
theorem smithReflexiveInverse_spec {A S : Matrix (Fin a) (Fin b) ℤ}
    (P : (Matrix (Fin a) (Fin a) ℤ)ˣ) (Q : (Matrix (Fin b) (Fin b) ℤ)ˣ) {r : ℕ}
    (hS : P.val * A * Q.val = S) (hD : BenIsraelGreville.Chapter00.IsSmithNormalForm S r) :
    IsIntegralReflexiveInverse A (smithReflexiveInverse P.val S Q.val) := by
  let A' := integerMatrixCast A
  let S' := integerMatrixCast S
  let P' := integerMatrixCast P.val
  let Q' := integerMatrixCast Q.val
  let Pi' := integerMatrixCast (P⁻¹).val
  let Qi' := integerMatrixCast (Q⁻¹).val
  let V := reciprocalSmithDiagonal S
  let U := smithReflexiveInverse P.val S Q.val
  have hU : U = Q' * V * P' := rfl
  have hPAQ : P' * A' * Q' = S' := by
    simpa only [Matrix.map_mul] using congrArg integerMatrixCast hS
  have hPiP : Pi' * P' = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg integerMatrixCast P.inv_mul
  have hQQi : Q' * Qi' = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg integerMatrixCast Q.mul_inv
  have hAQ : A' * Q' = Pi' * S' := calc
    A' * Q' = (Pi' * P') * A' * Q' := by rw [hPiP, Matrix.one_mul]
    _ = Pi' * S' := by rw [← hPAQ]; simp only [Matrix.mul_assoc]
  have hPA : P' * A' = S' * Qi' := calc
    P' * A' = P' * A' * (Q' * Qi') := by rw [hQQi, Matrix.mul_one]
    _ = S' * Qi' := by rw [← hPAQ]; simp only [Matrix.mul_assoc]
  have hA : A' = Pi' * S' * Qi' := calc
    A' = A' * (Q' * Qi') := by rw [hQQi, Matrix.mul_one]
    _ = Pi' * S' * Qi' := by rw [← Matrix.mul_assoc, hAQ]
  have hV := isIntegralReflexiveInverse_reciprocalSmithDiagonal hD
  constructor
  · change A' * U * A' = A'
    calc
      A' * U * A' = (A' * Q') * V * (P' * A') := by rw [hU]; simp only [Matrix.mul_assoc]
      _ = Pi' * (S' * V * S') * Qi' := by rw [hAQ, hPA]; simp only [Matrix.mul_assoc]
      _ = A' := by rw [show S' * V * S' = S' from hV.inner, ← hA]
  · change U * A' * U = U
    calc
      U * A' * U = Q' * (V * (P' * A' * Q') * V) * P' := by
        rw [hU]
        simp only [Matrix.mul_assoc]
      _ = U := by rw [hPAQ, show V * S' * V = V from hV.outer, ← hU]
  · obtain ⟨C, hC⟩ := hV.mul
    refine ⟨(P⁻¹).val * C * P.val, ?_⟩
    have he : A' * U = Pi' * (S' * V) * P' := calc
      A' * U = (A' * Q') * V * P' := by rw [hU]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAQ]; simp only [Matrix.mul_assoc]
    change integerMatrixCast C = S' * V at hC
    change integerMatrixCast _ = A' * U
    rw [he, ← hC]
    simp only [integerMatrixCast_mul, P', Pi']
  · obtain ⟨C, hC⟩ := hV.mul_rev
    refine ⟨Q.val * C * (Q⁻¹).val, ?_⟩
    have he : U * A' = Q' * (V * S') * Qi' := calc
      U * A' = Q' * V * (P' * A') := by rw [hU]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPA]; simp only [Matrix.mul_assoc]
    change integerMatrixCast C = V * S' at hC
    change integerMatrixCast _ = U * A'
    rw [he, ← hC]
    simp only [integerMatrixCast_mul, Q', Qi']

/-- **Corollary 13** of [benIsrael2003generalized], Chapter 2.
An integer matrix has a rational reflexive inverse with integral products. -/
theorem corollary_13 (A : Matrix (Fin a) (Fin b) ℤ) :
    ∃ U, IsIntegralReflexiveInverse A U := by
  obtain ⟨S, ⟨P, Q, hS⟩, hD⟩ := BenIsraelGreville.Chapter00.theorem_4 A
  exact ⟨smithReflexiveInverse P.val S Q.val, smithReflexiveInverse_spec P Q hS hD⟩

private theorem rationalMatrix_canonical_solution {A : Matrix m n ℚ} {B : Matrix p q ℚ}
    {D : Matrix m q ℚ} {U : Matrix n m ℚ} {V : Matrix q p ℚ}
    (hU : A.IsInnerInverse U) (hV : B.IsInnerInverse V)
    (h : ∃ W, A * W * B = D) : A * (U * D * V) * B = D := by
  obtain ⟨W, rfl⟩ := h
  calc
    A * (U * (A * W * B) * V) * B = (A * U * A) * W * (B * V * B) := by
      simp only [Matrix.mul_assoc]
    _ = A * W * B := by rw [hU, hV]

/-- **Corollary 14** of [benIsrael2003generalized], Chapter 2.
For a consistent rational system, integral solvability is equivalent to
integrality of the canonical product `UDV`. -/
theorem corollary_14 {A : Matrix m n ℤ} {B : Matrix p q ℤ} {D : Matrix m q ℤ}
    {U : Matrix n m ℚ} {V : Matrix q p ℚ}
    (hU : IsIntegralReflexiveInverse A U) (hV : IsIntegralReflexiveInverse B V)
    (h : ∃ W, integerMatrixCast A * W * integerMatrixCast B = integerMatrixCast D) :
    (∃ X : Matrix n p ℤ, A * X * B = D) ↔ IsIntegralMatrix (U * integerMatrixCast D * V) := by
  constructor
  · rintro ⟨X, rfl⟩
    obtain ⟨E, hE⟩ := hU.mul_rev
    obtain ⟨F, hF⟩ := hV.mul
    refine ⟨E * X * F, ?_⟩
    rw [integerMatrixCast_mul, integerMatrixCast_mul, integerMatrixCast_mul,
      integerMatrixCast_mul, hE, hF]
    simp only [Matrix.mul_assoc]
  · rintro ⟨X, hX⟩
    refine ⟨X, integerMatrixCast_injective ?_⟩
    rw [integerMatrixCast_mul, integerMatrixCast_mul, hX]
    exact rationalMatrix_canonical_solution hU.inner hV.inner h

/-- The affine family in Corollary 14, with an arbitrary integral parameter. -/
theorem corollary_14_solutions {A : Matrix m n ℤ} {B : Matrix p q ℤ} {D : Matrix m q ℤ}
    {U : Matrix n m ℚ} {V : Matrix q p ℚ}
    (hU : IsIntegralReflexiveInverse A U) (hV : IsIntegralReflexiveInverse B V)
    (h : ∃ W, integerMatrixCast A * W * integerMatrixCast B = integerMatrixCast D)
    (X : Matrix n p ℤ) :
    A * X * B = D ↔ ∃ Y : Matrix n p ℤ,
      integerMatrixCast X = U * integerMatrixCast D * V + integerMatrixCast Y -
        (U * integerMatrixCast A) * integerMatrixCast Y * (integerMatrixCast B * V) := by
  let A' := integerMatrixCast A
  let B' := integerMatrixCast B
  let D' := integerMatrixCast D
  have hD : A' * (U * D' * V) * B' = D' :=
    rationalMatrix_canonical_solution hU.inner hV.inner h
  constructor
  · intro hX
    refine ⟨X, ?_⟩
    have hx : A' * integerMatrixCast X * B' = D' := by
      simpa only [Matrix.map_mul] using congrArg integerMatrixCast hX
    have he : U * D' * V = (U * A') * integerMatrixCast X * (B' * V) := by
      rw [← hx]
      simp only [Matrix.mul_assoc]
    rw [← he, add_comm, add_sub_cancel_right]
  · rintro ⟨Y, hX⟩
    have hY : A' * ((U * A') * integerMatrixCast Y * (B' * V)) * B' =
        A' * integerMatrixCast Y * B' := calc
      _ = (A' * U * A') * integerMatrixCast Y * (B' * V * B') := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [show A' * U * A' = A' from hU.inner, show B' * V * B' = B' from hV.inner]
    apply integerMatrixCast_injective
    rw [integerMatrixCast_mul, integerMatrixCast_mul, hX, Matrix.mul_sub, Matrix.mul_add,
      Matrix.sub_mul, Matrix.add_mul]
    change A' * (U * D' * V) * B' + A' * integerMatrixCast Y * B' -
      A' * ((U * A') * integerMatrixCast Y * (B' * V)) * B' = D'
    rw [hD, hY, add_sub_cancel_right]

/-- Entrywise inclusion of integer vectors into rational vectors. -/
abbrev integerVectorCast (x : n → ℤ) : n → ℚ := fun i => x i

/-- A rational vector is integral when it comes from an integer vector. -/
def IsIntegralVector (x : n → ℚ) : Prop := ∃ z : n → ℤ, integerVectorCast z = x

omit [Fintype n] in
private theorem integerVectorCast_injective :
    Function.Injective (integerVectorCast : (n → ℤ) → (n → ℚ)) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

omit [Fintype m] in
theorem integerVectorCast_mulVec (A : Matrix m n ℤ) (x : n → ℤ) :
    integerVectorCast (A *ᵥ x) = integerMatrixCast A *ᵥ integerVectorCast x :=
  funext fun i => RingHom.map_mulVec (Int.castRingHom ℚ) A x i

private theorem rationalVector_canonical_solution {A : Matrix m n ℚ} {U : Matrix n m ℚ}
    (hU : A.IsInnerInverse U) {b : m → ℚ} (hb : ∃ w, A *ᵥ w = b) :
    A *ᵥ (U *ᵥ b) = b := by
  obtain ⟨w, rfl⟩ := hb
  rw [mulVec_mulVec, mulVec_mulVec, hU]

/-- **Corollary 15** of [benIsrael2003generalized], Chapter 2.
For a consistent rational equation, an integral solution exists exactly when
the vector obtained by applying the Smith inverse to the datum is integral. -/
theorem corollary_15 {A : Matrix m n ℤ} {b : m → ℤ} {U : Matrix n m ℚ}
    (hU : IsIntegralReflexiveInverse A U)
    (hb : ∃ w, integerMatrixCast A *ᵥ w = integerVectorCast b) :
    (∃ x : n → ℤ, A *ᵥ x = b) ↔ IsIntegralVector (U *ᵥ integerVectorCast b) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨E, hE⟩ := hU.mul_rev
    refine ⟨E *ᵥ x, ?_⟩
    rw [integerVectorCast_mulVec, integerVectorCast_mulVec, hE, mulVec_mulVec]
  · rintro ⟨x, hx⟩
    refine ⟨x, integerVectorCast_injective ?_⟩
    rw [integerVectorCast_mulVec, hx]
    exact rationalVector_canonical_solution hU.inner hb

/-- All the integral solutions in Corollary 15, parametrized by an integral vector. -/
theorem corollary_15_solutions [DecidableEq n] {A : Matrix m n ℤ} {b : m → ℤ}
    {U : Matrix n m ℚ} (hU : IsIntegralReflexiveInverse A U)
    (hb : ∃ w, integerMatrixCast A *ᵥ w = integerVectorCast b) (x : n → ℤ) :
    A *ᵥ x = b ↔ ∃ y : n → ℤ, integerVectorCast x =
      U *ᵥ integerVectorCast b + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast y := by
  have h := rationalVector_canonical_solution hU.inner hb
  constructor
  · rintro rfl
    refine ⟨x, ?_⟩
    rw [integerVectorCast_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec]
    abel
  · rintro ⟨y, hy⟩
    have hzero : integerMatrixCast A * (1 - U * integerMatrixCast A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU.inner, sub_self]
    apply integerVectorCast_injective
    rw [integerVectorCast_mulVec, hy, mulVec_add, h, mulVec_mulVec, hzero, zero_mulVec, add_zero]

/-- If the canonical product is integral, every integral parameter in
Corollary 14 yields an integral solution. -/
theorem corollary_14_integral_parameters {A : Matrix m n ℤ} {B : Matrix p q ℤ} {D : Matrix m q ℤ}
    {U : Matrix n m ℚ} {V : Matrix q p ℚ}
    (hU : IsIntegralReflexiveInverse A U) (hV : IsIntegralReflexiveInverse B V)
    (h : ∃ W, integerMatrixCast A * W * integerMatrixCast B = integerMatrixCast D)
    (h₀ : IsIntegralMatrix (U * integerMatrixCast D * V)) (Y : Matrix n p ℤ) :
    ∃ X : Matrix n p ℤ, A * X * B = D ∧
      integerMatrixCast X = U * integerMatrixCast D * V + integerMatrixCast Y -
        (U * integerMatrixCast A) * integerMatrixCast Y * (integerMatrixCast B * V) := by
  obtain ⟨X₀, hX₀⟩ := h₀
  obtain ⟨E, hE⟩ := hU.mul_rev
  obtain ⟨F, hF⟩ := hV.mul
  let X := X₀ + Y - E * Y * F
  have hX : integerMatrixCast X = U * integerMatrixCast D * V + integerMatrixCast Y -
      (U * integerMatrixCast A) * integerMatrixCast Y * (integerMatrixCast B * V) := by
    dsimp only [X]
    change (X₀ + Y - E * Y * F).map (Int.castRingHom ℚ) = _
    rw [Matrix.map_sub (Int.castRingHom ℚ) (map_sub _),
      Matrix.map_add (Int.castRingHom ℚ) (map_add _)]
    change integerMatrixCast X₀ + integerMatrixCast Y - integerMatrixCast (E * Y * F) = _
    rw [integerMatrixCast_mul, integerMatrixCast_mul, hE, hF, hX₀]
  exact ⟨X, (corollary_14_solutions hU hV h X).mpr ⟨Y, hX⟩, hX⟩

/-- If the canonical vector is integral, every integral parameter in
Corollary 15 yields an integral solution. -/
theorem corollary_15_integral_parameters [DecidableEq n] {A : Matrix m n ℤ} {b : m → ℤ}
    {U : Matrix n m ℚ} (hU : IsIntegralReflexiveInverse A U)
    (hb : ∃ w, integerMatrixCast A *ᵥ w = integerVectorCast b)
    (h₀ : IsIntegralVector (U *ᵥ integerVectorCast b)) (y : n → ℤ) :
    ∃ x : n → ℤ, A *ᵥ x = b ∧ integerVectorCast x =
      U *ᵥ integerVectorCast b + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast y := by
  obtain ⟨x₀, hx₀⟩ := h₀
  obtain ⟨E, hE⟩ := hU.mul_rev
  let x := x₀ + y - E *ᵥ y
  have hx : integerVectorCast x =
      U *ᵥ integerVectorCast b + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast y := by
    have hm : integerVectorCast (E *ᵥ y) = (U * integerMatrixCast A) *ᵥ integerVectorCast y :=
      (integerVectorCast_mulVec E y).trans (by rw [hE])
    rw [sub_mulVec, one_mulVec, ← hx₀, ← hm]
    funext i
    change ((x₀ i + y i - (E *ᵥ y) i : ℤ) : ℚ) = _
    simp
    ring
  exact ⟨x, (corollary_15_solutions hU hb x).mpr ⟨y, hx⟩, hx⟩

end BenIsraelGreville.Chapter02
