/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section08
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Integral solutions of linear equations

Section 2.12 of [benIsrael2003generalized] constructs a rational
reflexive inverse from the Smith normal form and uses its integral
products to describe all integral solutions.

## Deviations from the source

* The last factor of the affine correction in Corollary 14 is a single
  copy of the inverse of `B` constructed from its Smith form.

* **Exercise 105** (correction). The interval constraint applies to $Ax$.
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

section IntervalResults

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The integral vectors satisfying the interval constraints on the image under $A$. -/
def integerIntervalFeasible (A : Matrix m n ℤ) (a b : m → ℤ) : Set (n → ℤ) :=
  {x | ∀ i, a i ≤ (A *ᵥ x) i ∧ (A *ᵥ x) i ≤ b i}

/-- The integer image vectors in the box whose Smith test gives an integral lift. -/
def smithIntervalImages (A : Matrix m n ℤ) (U : Matrix n m ℚ) (a b : m → ℤ) :
    Set (m → ℤ) :=
  {y | (∀ i, a i ≤ y i ∧ y i ≤ b i) ∧
    integerMatrixCast A *ᵥ (U *ᵥ integerVectorCast y) = integerVectorCast y ∧
    IsIntegralVector (U *ᵥ integerVectorCast y)}

/-- Smith consistency and integrality characterize the attainable integer image vectors. -/
theorem smithIntervalImages_eq_image {A : Matrix m n ℤ} {U : Matrix n m ℚ}
    (hU : IsIntegralReflexiveInverse A U) (a b : m → ℤ) :
    smithIntervalImages A U a b = (A *ᵥ ·) '' integerIntervalFeasible A a b := by
  ext y
  constructor
  · rintro ⟨hy, hcon, hint⟩
    obtain ⟨x, hx⟩ := (corollary_15 hU ⟨_, hcon⟩).mpr hint
    exact ⟨x, fun i => hx.symm ▸ hy i, hx⟩
  · rintro ⟨x, hx, rfl⟩
    have hcon : integerMatrixCast A *ᵥ (U *ᵥ integerVectorCast (A *ᵥ x)) =
        integerVectorCast (A *ᵥ x) := by
      rw [integerVectorCast_mulVec, mulVec_mulVec, mulVec_mulVec, hU.inner]
    exact ⟨hx, hcon, (corollary_15 hU ⟨_, hcon⟩).mp ⟨x, rfl⟩⟩

/-- A bounded box contains only finitely many attainable integer image vectors. -/
theorem smithIntervalImages_finite (A : Matrix m n ℤ) (U : Matrix n m ℚ) (a b : m → ℤ) :
    (smithIntervalImages A U a b).Finite := by
  refine (Set.Finite.pi fun i => Set.finite_Icc (a i) (b i)).subset ?_
  intro y hy j _
  exact hy.1 j

omit [Fintype m] in
/-- On a nonempty feasible set, a bounded objective vanishes on each integral
vector in the kernel of the constraint matrix. -/
theorem dotProduct_eq_zero_of_bddAbove_integerInterval {A : Matrix m n ℤ}
    {a b : m → ℤ} {c : n → ℤ}
    (hne : (integerIntervalFeasible A a b).Nonempty)
    (hbounded : BddAbove ((c ⬝ᵥ ·) '' integerIntervalFeasible A a b))
    (z : n → ℤ) (hz : A *ᵥ z = 0) : c ⬝ᵥ z = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨M, hM⟩ := hbounded
  have hxM : c ⬝ᵥ x ≤ M := hM ⟨x, hx, rfl⟩
  have hnneg : 0 ≤ M - c ⬝ᵥ x + 1 := by omega
  have hnpos (w : n → ℤ) (hw : A *ᵥ w = 0) : c ⬝ᵥ w ≤ 0 := by
    by_contra! hpos
    let t := M - c ⬝ᵥ x + 1
    have hAx : A *ᵥ (x + t • w) = A *ᵥ x := by
      simp only [mulVec_add, mulVec_smul, hw, smul_zero, add_zero]
    have hf : x + t • w ∈ integerIntervalFeasible A a b := by
      intro i
      rw [hAx]
      exact hx i
    have hupper := hM ⟨x + t • w, hf, rfl⟩
    change c ⬝ᵥ (x + t • w) ≤ M at hupper
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hupper
    have hprod : t * 1 ≤ t * (c ⬝ᵥ w) :=
      mul_le_mul_of_nonneg_left (by omega) hnneg
    dsimp [t] at hupper hprod
    omega
  have hpos := hnpos z hz
  have hn := hnpos (-z) (by rw [mulVec_neg, hz, neg_zero])
  rw [dotProduct_neg] at hn
  omega

/-- The objective induced on an attainable image by its canonical Smith lift. -/
def smithIntervalObjective (U : Matrix n m ℚ) (c : n → ℤ) (y : m → ℤ) : ℚ :=
  integerVectorCast c ⬝ᵥ (U *ᵥ integerVectorCast y)

private theorem integerInterval_objective_eq_smith {A : Matrix m n ℤ} {U : Matrix n m ℚ}
    (hU : IsIntegralReflexiveInverse A U) {a b : m → ℤ} {c : n → ℤ}
    (hbounded : BddAbove ((c ⬝ᵥ ·) '' integerIntervalFeasible A a b))
    {x : n → ℤ} (hx : x ∈ integerIntervalFeasible A a b) :
    ((c ⬝ᵥ x : ℤ) : ℚ) = smithIntervalObjective U c (A *ᵥ x) := by
  have himg : A *ᵥ x ∈ smithIntervalImages A U a b := by
    rw [smithIntervalImages_eq_image hU]
    exact ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := himg.2.2
  have hAz : A *ᵥ z = A *ᵥ x := by
    have he := (integerVectorCast_mulVec A z).trans
      ((congrArg (integerMatrixCast A *ᵥ ·) hz).trans himg.2.1)
    funext i
    exact Int.cast_injective (congrFun he i)
  have hker : A *ᵥ (x - z) = 0 := by rw [mulVec_sub, hAz, sub_self]
  have hcz := dotProduct_eq_zero_of_bddAbove_integerInterval ⟨x, hx⟩ hbounded (x - z) hker
  rw [dotProduct_sub, sub_eq_zero] at hcz
  unfold smithIntervalObjective
  rw [← hz, hcz]
  exact RingHom.map_dotProduct (Int.castRingHom ℚ) c z

/-- **Exercise 105** of [benIsrael2003generalized], Chapter 2. For a bounded
integer interval program, maximize the induced objective over the finite set
of attainable images. All optimal integer solutions are exactly the affine
Smith lifts of the maximizing images. A nonempty feasible set has an optimum.

The display in the source gives bounds on $x$ while listing a matrix $A$
among the input data. Here the bounds are on $Ax$, the form using all four
listed inputs and reducing to the printed box when $A=I$. -/
theorem exercise_105 [DecidableEq n] {A : Matrix m n ℤ} {U : Matrix n m ℚ}
    (hU : IsIntegralReflexiveInverse A U) (a b : m → ℤ) (c : n → ℤ)
    (hbounded : BddAbove ((c ⬝ᵥ ·) '' integerIntervalFeasible A a b)) :
    let feasible := integerIntervalFeasible A a b
    let images := smithIntervalImages A U a b
    let score := smithIntervalObjective U c
    (∀ x : n → ℤ, (x ∈ feasible ∧ ∀ z ∈ feasible, c ⬝ᵥ z ≤ c ⬝ᵥ x) ↔
      ∃ y ∈ images, (∀ w ∈ images, score w ≤ score y) ∧
        ∃ t : n → ℤ, integerVectorCast x =
          U *ᵥ integerVectorCast y + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast t) ∧
    (feasible.Nonempty → ∃ x ∈ feasible, ∀ z ∈ feasible, c ⬝ᵥ z ≤ c ⬝ᵥ x) := by
  intro feasible images score
  have himage : images = (A *ᵥ ·) '' feasible := smithIntervalImages_eq_image hU a b
  have hlift (y : m → ℤ) (hy : y ∈ images) (x : n → ℤ) :
      A *ᵥ x = y ↔ ∃ t : n → ℤ, integerVectorCast x =
        U *ᵥ integerVectorCast y + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast t :=
    corollary_15_solutions hU ⟨_, hy.2.1⟩ x
  have hscore (x : n → ℤ) (hx : x ∈ feasible) : ((c ⬝ᵥ x : ℤ) : ℚ) = score (A *ᵥ x) :=
    integerInterval_objective_eq_smith hU hbounded hx
  have hopt (x : n → ℤ) :
      (x ∈ feasible ∧ ∀ z ∈ feasible, c ⬝ᵥ z ≤ c ⬝ᵥ x) ↔
        ∃ y ∈ images, (∀ w ∈ images, score w ≤ score y) ∧
          ∃ t : n → ℤ, integerVectorCast x =
            U *ᵥ integerVectorCast y + (1 - U * integerMatrixCast A) *ᵥ integerVectorCast t := by
    constructor
    · rintro ⟨hx, hmax⟩
      have hx' : A *ᵥ x ∈ images := himage.symm ▸ ⟨x, hx, rfl⟩
      refine ⟨A *ᵥ x, hx', ?_, (hlift (A *ᵥ x) hx' x).mp rfl⟩
      intro w hw
      rw [himage] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      rw [← hscore z hz, ← hscore x hx]
      exact_mod_cast hmax z hz
    · rintro ⟨y, hy, hmax, t, ht⟩
      have hxy := (hlift y hy x).mpr ⟨t, ht⟩
      have hx : x ∈ feasible := fun i => hxy.symm ▸ hy.1 i
      refine ⟨hx, fun z hz => ?_⟩
      have hz' : A *ᵥ z ∈ images := himage.symm ▸ ⟨z, hz, rfl⟩
      have he := hmax _ hz'
      rw [← hxy, ← hscore z hz, ← hscore x hx] at he
      exact_mod_cast he
  refine ⟨hopt, fun hne => ?_⟩
  classical
  have hi : images.Nonempty := himage.symm ▸ hne.image _
  have hfin := smithIntervalImages_finite A U a b
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image hfin.toFinset score (by simpa using hi)
  have hy' : y ∈ images := hfin.mem_toFinset.mp hy
  obtain ⟨x, hx, hAx⟩ := show y ∈ (A *ᵥ ·) '' feasible from himage ▸ hy'
  refine ⟨x, (hopt x).mpr ⟨y, hy', ?_, (hlift y hy' x).mp hAx⟩⟩
  exact fun w hw => hmax w (hfin.mem_toFinset.mpr hw)

end IntervalResults

section PolynomialResults

open Matrix Module

variable {m n : Type*} [Fintype m] [Fintype n]
variable {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

/-- Entrywise inclusion in the field of fractions. -/
abbrev fractionMatrixCast (A : Matrix m n R) : Matrix m n L := A.map (algebraMap R L)

/-- A reflexive inverse over the field of fractions with both projections over the base ring. -/
structure IsFractionalReflexiveInverse (A : Matrix m n R) (U : Matrix n m L) : Prop where
  /-- The first Penrose equation. -/
  inner : (fractionMatrixCast A).IsInnerInverse U
  /-- The second Penrose equation. -/
  outer : (fractionMatrixCast A).IsOuterInverse U
  /-- The left projection has entries in the base ring. -/
  mul : ∃ E : Matrix m m R, fractionMatrixCast E = fractionMatrixCast A * U
  /-- The right projection has entries in the base ring. -/
  mul_rev : ∃ E : Matrix n n R, fractionMatrixCast E = U * fractionMatrixCast A

omit [IsDomain R] in
private theorem equivFun_symm_single {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module R M] (b : Basis ι R M) (i : ι) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  apply b.equivFun.injective
  ext j
  rw [LinearEquiv.apply_symm_apply, Basis.equivFun_self, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The Smith bases of the image of a matrix over a principal ideal domain
give a reflexive inverse over its fraction field with both products in
the original ring. This is Corollary 13 in the setting of Exercise 106. -/
theorem exists_fractionalReflexiveInverse [IsPrincipalIdealRing R] (A : Matrix m n R) :
    ∃ U : Matrix n m L, IsFractionalReflexiveInverse A U := by
  classical
  let N := A.mulVecLin.range
  obtain ⟨r, snf⟩ := N.smithNormalForm (Pi.basisFun R m)
  let P := LinearMap.toMatrix' snf.bM.equivFun.toLinearMap
  let Pback := LinearMap.toMatrix' snf.bM.equivFun.symm.toLinearMap
  let V := LinearMap.toMatrix' (snf.bN.equivFun.toLinearMap.comp A.mulVecLin.rangeRestrict)
  let E := LinearMap.toMatrix' (N.subtype.comp snf.bN.equivFun.symm.toLinearMap)
  have hA : A = E * V := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← mulVec_mulVec]
    simp [E, V, N]
  have hPPback : P * Pback = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← mulVec_mulVec]
    simp only [P, Pback, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, one_mulVec]
  have hPbackP : Pback * P = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← mulVec_mulVec]
    simp only [P, Pback, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, one_mulVec]
  choose y hy using fun j : Fin r => (snf.bN j).property
  let Y : Matrix n (Fin r) R := Matrix.of fun i j => y j i
  have hVY : V * Y = 1 := by
    ext i j
    change (V *ᵥ y j) i = _
    have hyj : A.mulVecLin.rangeRestrict (y j) = snf.bN j := Subtype.ext (hy j)
    simp [V, hyj, Basis.equivFun_self, Matrix.one_apply, eq_comm]
  let J : Matrix m (Fin r) R := Matrix.of fun i j => if i = snf.f j then 1 else 0
  have hJ : Jᵀ * J = 1 := by
    ext i j
    simp [J, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq',
      snf.f.injective.eq_iff, eq_comm]
  have hPE : P * E = J * diagonal snf.a := by
    ext i j
    change (P *ᵥ E.col j) i = _
    have hEj : E.col j = (snf.bN j : m → R) := by
      funext k
      simp only [E, Matrix.col, Matrix.transpose_apply, LinearMap.toMatrix'_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, equivFun_symm_single, Submodule.subtype_apply]
    rw [hEj, mul_diagonal]
    simp [P, J, snf.snf j, eq_comm, ite_mul, mul_ite, Finsupp.single_apply]
  have hE : E = Pback * J * diagonal snf.a := by
    calc
      E = Pback * (P * E) := by rw [← Matrix.mul_assoc, hPbackP, Matrix.one_mul]
      _ = _ := by rw [hPE, Matrix.mul_assoc]
  have ha (j : Fin r) : snf.a j ≠ 0 := by
    intro hj
    exact snf.bN.ne_zero j (Subtype.ext (by simp [snf.snf j, hj]))
  let α := algebraMap R L
  let p := P.map α
  let pback := Pback.map α
  let j := J.map α
  let jT := Jᵀ.map α
  let v := V.map α
  let y' := Y.map α
  let e := E.map α
  let d := diagonal fun i => α (snf.a i)
  let dInv := diagonal fun i => (α (snf.a i))⁻¹
  let f := dInv * jT * p
  let U := y' * f
  have hA' : fractionMatrixCast (L := L) A = e * v := by
    simpa only [Matrix.map_mul] using congrArg (fun W => W.map α) hA
  have hp : p * pback = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun W => W.map α) hPPback
  have hj : jT * j = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun W => W.map α) hJ
  have hv : v * y' = 1 := by
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using
      congrArg (fun W => W.map α) hVY
  have he : e = pback * j * d := by
    simpa only [Matrix.map_mul, diagonal_map (map_zero α)] using
      congrArg (fun W => W.map α) hE
  have hd : d * dInv = 1 := by
    change diagonal (fun i => α (snf.a i)) * diagonal (fun i => (α (snf.a i))⁻¹) = 1
    rw [diagonal_mul_diagonal]
    have h i : α (snf.a i) ≠ 0 := by
      rw [← map_zero α]
      exact (IsFractionRing.injective R L).ne (ha i)
    simp [h]
  have hd' : dInv * d = 1 := by
    change diagonal (fun i => (α (snf.a i))⁻¹) * diagonal (fun i => α (snf.a i)) = 1
    rw [diagonal_mul_diagonal]
    have h i : α (snf.a i) ≠ 0 := by
      rw [← map_zero α]
      exact (IsFractionRing.injective R L).ne (ha i)
    simp [h]
  have hfe : f * e = 1 := by
    calc
      f * e = dInv * (jT * (p * pback) * j) * d := by
        rw [he]
        simp only [f, Matrix.mul_assoc]
      _ = 1 := by rw [hp, Matrix.mul_one, hj, Matrix.mul_one, hd']
  have hleft : fractionMatrixCast A * U = e * f := by
    rw [hA']
    calc
      (e * v) * U = e * (v * y') * f := by simp only [U, Matrix.mul_assoc]
      _ = _ := by rw [hv, Matrix.mul_one]
  have hright : U * fractionMatrixCast A = y' * v := by
    rw [hA']
    calc
      U * (e * v) = y' * (f * e) * v := by simp only [U, Matrix.mul_assoc]
      _ = _ := by rw [hfe, Matrix.mul_one]
  refine ⟨U, ⟨?_, ?_, ⟨Pback * J * Jᵀ * P, ?_⟩, ⟨Y * V, ?_⟩⟩⟩
  · rw [isInnerInverse_iff, hleft, hA']
    calc
      (e * f) * (e * v) = e * (f * e) * v := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hfe, Matrix.mul_one]
  · rw [isOuterInverse_iff, hright]
    calc
      (y' * v) * U = y' * (v * y') * f := by simp only [U, Matrix.mul_assoc]
      _ = U := by rw [hv, Matrix.mul_one]
  · rw [hleft]
    calc
      _ = pback * j * jT * p := by simp only [fractionMatrixCast, Matrix.map_mul]; rfl
      _ = pback * j * (d * dInv) * jT * p := by rw [hd, Matrix.mul_one]
      _ = e * f := by rw [he]; simp only [f, Matrix.mul_assoc]
  · rw [hright]
    exact Matrix.map_mul

/-- Entrywise inclusion of vectors in the field of fractions. -/
abbrev fractionVectorCast (x : n → R) : n → L := algebraMap R L ∘ x

omit [Fintype m] [IsDomain R] [IsFractionRing R L] in
private theorem fractionVectorCast_mulVec (A : Matrix m n R) (x : n → R) :
    fractionVectorCast (L := L) (A *ᵥ x) = fractionMatrixCast A *ᵥ fractionVectorCast x :=
  funext fun i => RingHom.map_mulVec (algebraMap R L) A x i

omit [Fintype n] [IsDomain R] in
private theorem fractionVectorCast_inj :
    Function.Injective (fractionVectorCast : (n → R) → (n → L)) :=
  fun _ _ h => funext fun i => IsFractionRing.injective R L (congrFun h i)

omit [IsDomain R] in
/-- The solvability test and the complete affine parametrization of
Corollary 15 over a base ring with fraction field. If the test succeeds,
each base-ring parameter produces a base-ring solution. -/
theorem fractionalVectorSolutions [DecidableEq n]
    {A : Matrix m n R} {U : Matrix n m L} (hU : IsFractionalReflexiveInverse A U)
    (b : m → R) (hb : ∃ w : n → L, fractionMatrixCast A *ᵥ w = fractionVectorCast b) :
    ((∃ x : n → R, A *ᵥ x = b) ↔ ∃ x₀ : n → R,
      fractionVectorCast x₀ = U *ᵥ fractionVectorCast b) ∧
    (∀ x : n → R, A *ᵥ x = b ↔ ∃ y : n → R, fractionVectorCast x =
      U *ᵥ fractionVectorCast b + (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y) ∧
    ((∃ x₀ : n → R, fractionVectorCast x₀ = U *ᵥ fractionVectorCast b) →
      ∀ y : n → R, ∃ x : n → R, A *ᵥ x = b ∧ fractionVectorCast x =
        U *ᵥ fractionVectorCast b + (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y) := by
  have hbase : fractionMatrixCast A *ᵥ (U *ᵥ fractionVectorCast b) = fractionVectorCast b := by
    obtain ⟨w, hw⟩ := hb
    rw [← hw, mulVec_mulVec, mulVec_mulVec, hU.inner]
  obtain ⟨E, hE⟩ := hU.mul_rev
  have hsol (x : n → R) : A *ᵥ x = b ↔ ∃ y : n → R, fractionVectorCast x =
      U *ᵥ fractionVectorCast b + (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y := by
    constructor
    · rintro rfl
      refine ⟨x, ?_⟩
      rw [fractionVectorCast_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec]
      abel
    · rintro ⟨y, hy⟩
      have hzero : fractionMatrixCast (L := L) A *
          ((1 : Matrix n n L) - U * fractionMatrixCast A) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU.inner, sub_self]
      apply fractionVectorCast_inj (L := L)
      rw [fractionVectorCast_mulVec, hy, mulVec_add, hbase, mulVec_mulVec, hzero, zero_mulVec,
        add_zero]
  refine ⟨⟨?_, ?_⟩, hsol, ?_⟩
  · rintro ⟨x, rfl⟩
    refine ⟨E *ᵥ x, ?_⟩
    rw [fractionVectorCast_mulVec, fractionVectorCast_mulVec, hE, mulVec_mulVec]
  · rintro ⟨x, hx⟩
    refine ⟨x, fractionVectorCast_inj (L := L) ?_⟩
    rw [fractionVectorCast_mulVec, hx, hbase]
  · rintro ⟨x₀, hx₀⟩ y
    let x := x₀ + y - E *ᵥ y
    have hx : fractionVectorCast x = U *ᵥ fractionVectorCast b +
        (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y := by
      have hm : fractionVectorCast (E *ᵥ y) = (U * fractionMatrixCast A) *ᵥ fractionVectorCast y :=
        (fractionVectorCast_mulVec E y).trans (by rw [hE])
      rw [sub_mulVec, one_mulVec, ← hx₀, ← hm]
      funext i
      change algebraMap R L (x₀ i + y i - (E *ᵥ y) i) =
        algebraMap R L (x₀ i) + (algebraMap R L (y i) - algebraMap R L ((E *ᵥ y) i))
      rw [map_sub, map_add, add_sub_assoc]
    exact ⟨x, (hsol x).mpr ⟨y, hx⟩, hx⟩

/-- **Exercise 106** of [benIsrael2003generalized], Chapter 2.
In particular for real and complex coefficient fields, a polynomial
matrix has a rational-function reflexive inverse whose two products are
polynomial. For every consistent right-hand side, denominator-free Smith
lifts characterize polynomial solvability and give all polynomial solutions. -/
theorem exercise_106 [DecidableEq n] {K : Type*} [Field K] (A : Matrix m n (Polynomial K)) :
    ∃ U : Matrix n m (RatFunc K), IsFractionalReflexiveInverse A U ∧
      ∀ b : m → Polynomial K,
        (∃ w : n → RatFunc K, fractionMatrixCast A *ᵥ w = fractionVectorCast b) →
        (((∃ x : n → Polynomial K, A *ᵥ x = b) ↔ ∃ x₀ : n → Polynomial K,
          fractionVectorCast x₀ = U *ᵥ fractionVectorCast b) ∧
        (∀ x : n → Polynomial K, A *ᵥ x = b ↔ ∃ y : n → Polynomial K,
          fractionVectorCast x =
            U *ᵥ fractionVectorCast b + (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y) ∧
        ((∃ x₀ : n → Polynomial K, fractionVectorCast x₀ = U *ᵥ fractionVectorCast b) →
          ∀ y : n → Polynomial K, ∃ x : n → Polynomial K, A *ᵥ x = b ∧
            fractionVectorCast x =
              U *ᵥ fractionVectorCast b +
                (1 - U * fractionMatrixCast A) *ᵥ fractionVectorCast y)) := by
  obtain ⟨U, hU⟩ := exists_fractionalReflexiveInverse (L := RatFunc K) A
  exact ⟨U, hU, fractionalVectorSolutions hU⟩

end PolynomialResults

end BenIsraelGreville.Chapter02
