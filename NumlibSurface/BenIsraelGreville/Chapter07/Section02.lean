/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section02
import NumlibSurface.BenIsraelGreville.Chapter05.Section02

/-!
# Computation of inner and reflexive inverses

Section 7.2 of [benIsrael2003generalized] constructs generalized inverses from a
maximal nonsingular pivot or from the Hermite form of a matrix. The Hermite
construction also gives a consistency test and a particular solution. The
Hermite formula with an arbitrary lower block is `Chapter01.theorem_1`.
-/

namespace BenIsraelGreville.Chapter07

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff mem_one_two_iff)

section Elimination

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

private theorem reflexiveInverse_of_reduction {A H : Matrix m n ℂ} {Y : Matrix n m ℂ}
    {E : Matrix m m ℂ} {P : Matrix n n ℂ} (hE : IsUnit E) (hP : IsUnit P)
    (h : E * A * P = H) (hi : H.IsInnerInverse Y) (ho : H.IsOuterInverse Y) :
    P * Y * E ∈ definition_1 A {.inner, .outer} := by
  have hLeft := E.nonsing_inv_mul ((isUnit_iff_isUnit_det E).mp hE)
  have hRight := P.mul_nonsing_inv ((isUnit_iff_isUnit_det P).mp hP)
  have hCancel (B : Matrix m n ℂ) : E⁻¹ * (E * B * P) * P⁻¹ = B := by
    calc
      E⁻¹ * (E * B * P) * P⁻¹ = (E⁻¹ * E) * B * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hLeft, hRight, Matrix.one_mul, Matrix.mul_one]
  apply mem_one_two_iff.mpr
  constructor
  · rw [isInnerInverse_iff]
    calc
      A * (P * Y * E) * A = E⁻¹ * ((E * A * P) * Y * (E * A * P)) * P⁻¹ := by
        rw [← hCancel (A * (P * Y * E) * A)]
        simp only [Matrix.mul_assoc]
      _ = A := by rw [h, isInnerInverse_iff.mp hi, ← h, hCancel]
  · rw [isOuterInverse_iff]
    calc
      P * Y * E * A * (P * Y * E) = P * (Y * (E * A * P) * Y) * E := by
        simp only [Matrix.mul_assoc]
      _ = P * Y * E := by rw [h, isOuterInverse_iff.mp ho]

/-- **Equations (5.19), (5.39), (5.25)** of [benIsrael2003generalized], as used in
Chapter 7. A nonsingular leading block of maximal rank has zero Schur complement.
Inverting that block and undoing the reductions gives a reflexive inverse.

**Generalization.** The two coordinate changes may be any invertible matrices,
which includes the permutations used in the book. -/
theorem isReflexiveInverse_of_maximal_nonsingular_submatrix
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {P : Matrix (r ⊕ m) (r ⊕ m) ℂ} {Q : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    {B : Matrix r r ℂ} {C : Matrix r n ℂ} {D : Matrix m r ℂ} {F : Matrix m n ℂ}
    (hP : IsUnit P) (hQ : IsUnit Q) (hB : IsUnit B) (hrank : A.rank = B.rank)
    (hA : P * A * Q = fromBlocks B C D F) :
    F = D * B⁻¹ * C ∧
      Q * (fromBlocks B⁻¹ 0 0 0 : Matrix (r ⊕ n) (r ⊕ m) ℂ) * P ∈
        definition_1 A {.inner, .outer} := by
  have hRank : (fromBlocks B C D F).rank = B.rank := by
    rw [← hA, rank_mul_eq_left_of_isUnit_det Q _ ((isUnit_iff_isUnit_det Q).mp hQ),
      rank_mul_eq_right_of_isUnit_det P A ((isUnit_iff_isUnit_det P).mp hP), hrank]
  have hSchur := (Chapter05.exercise_3 C D F hB).mp hRank
  have hF : F = D * B⁻¹ * C := sub_eq_zero.mp hSchur
  have hd := (isUnit_iff_isUnit_det B).mp hB
  have hL := B.mul_nonsing_inv hd
  have hR := B.nonsing_inv_mul hd
  refine ⟨hF, reflexiveInverse_of_reduction hP hQ hA ?_ ?_⟩
  · rw [isInnerInverse_iff]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      hL, Matrix.one_mul]
    rw [Matrix.mul_assoc D B⁻¹ B, hR, Matrix.mul_one, ← hF]
  · rw [isOuterInverse_iff]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      hR, Matrix.one_mul]

/-- **Equation (1.11)** of [benIsrael2003generalized], as used in Chapter 7.
The zero lower block in the Hermite construction gives a reflexive inverse. -/
theorem hermite_reflexiveInverse
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (K : Matrix r n ℂ)
    (hA : E * A * P = fromBlocks 1 K 0 0) :
    P * (fromBlocks 1 0 0 0 : Matrix (r ⊕ n) (r ⊕ m) ℂ) * E ∈ definition_1 A {.inner, .outer} := by
  refine reflexiveInverse_of_reduction hE hP hA ?_ ?_
  · rw [isInnerInverse_iff]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero]
  · rw [isOuterInverse_iff]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero]

omit [Fintype n] [DecidableEq n] in
/-- **Section 7.2** of [benIsrael2003generalized]. For a square Hermite reduction,
the product $PE$ is an invertible inner inverse. -/
theorem isUnit_innerInverse_of_hermite
    {A E P : Matrix (r ⊕ m) (r ⊕ m) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (K : Matrix r m ℂ)
    (hA : E * A * P = fromBlocks 1 K 0 0) :
    IsUnit (P * E) ∧ A.IsInnerInverse (P * E) := by
  refine ⟨hP.mul hE, mem_one_iff.mp ?_⟩
  simpa only [fromBlocks_one, Matrix.mul_one] using Chapter01.theorem_1 hE hP K hA 1

omit [DecidableEq m] [DecidableEq n] in
/-- **Equation (2)** of [benIsrael2003generalized], Chapter 7. The augmented
reduction applies the same row operations to the right-hand side while
leaving its column outside the permutation of the coefficient columns. -/
theorem hermite_augmented_matrix
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (K : Matrix r n ℂ) (b : Matrix (r ⊕ m) (Fin 1) ℂ)
    (hA : E * A * P = fromBlocks 1 K 0 0) :
    E * fromCols A b * fromBlocks P 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      fromCols (fromBlocks 1 K 0 0) (E * b) := by
  rw [mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, hA]

/-- **Theorem 1**, Equations (1)–(3) of [benIsrael2003generalized], Chapter 7.
For a Hermite reduction, the lower block of the transformed right-hand side
tests consistency. When the system is consistent, the canonical reflexive
inverse applies the column change to the leading part with zeros appended. -/
theorem theorem_1
    {A : Matrix (r ⊕ m) (r ⊕ n) ℂ}
    {E : Matrix (r ⊕ m) (r ⊕ m) ℂ} {P : Matrix (r ⊕ n) (r ⊕ n) ℂ}
    (hE : IsUnit E) (hP : IsUnit P) (K : Matrix r n ℂ)
    (hA : E * A * P = fromBlocks 1 K 0 0)
    (b : r ⊕ m → ℂ) (bhat : r → ℂ) (z : m → ℂ) (hb : E *ᵥ b = Sum.elim bhat z) :
    ((∃ x, A *ᵥ x = b) ↔ z = 0) ∧
      (P * (fromBlocks 1 0 0 0 : Matrix (r ⊕ n) (r ⊕ m) ℂ) * E) *ᵥ b =
        P *ᵥ Sum.elim bhat (0 : n → ℂ) ∧
      (z = 0 → A *ᵥ (P *ᵥ Sum.elim bhat (0 : n → ℂ)) = b) := by
  let H : Matrix (r ⊕ m) (r ⊕ n) ℂ := fromBlocks 1 K 0 0
  change E * A * P = H at hA
  have hs (x : r ⊕ n → ℂ) : A *ᵥ (P *ᵥ x) = b ↔ H *ᵥ x = Sum.elim bhat z := by
    rw [← hb, ← hA, ← mulVec_mulVec, ← mulVec_mulVec]
    exact (mulVec_injective_of_isUnit hE).eq_iff.symm
  have hpart (hz : z = 0) : A *ᵥ (P *ᵥ Sum.elim bhat (0 : n → ℂ)) = b := by
    apply (hs _).mpr
    rw [hz]
    simp [H, fromBlocks_mulVec]
  refine ⟨⟨?_, fun hz => ⟨_, hpart hz⟩⟩, ?_, hpart⟩
  · rintro ⟨x, hx⟩
    let y := P⁻¹ *ᵥ x
    have hPy : P *ᵥ y = x := by
      rw [show y = P⁻¹ *ᵥ x from rfl, mulVec_mulVec,
        mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP), one_mulVec]
    have hy := (hs y).mp (hPy.symm ▸ hx)
    funext i
    have hi := congrFun hy (Sum.inr i)
    simpa [H, fromBlocks_mulVec] using hi.symm
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hb]
    simp [fromBlocks_mulVec]

end Elimination

section ColumnUpdate

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- **Equations (5)–(8)** of [benIsrael2003generalized], Chapter 7. Append a
column using an inner inverse of the residual column. When the residual is
zero, the added row is zero. -/
noncomputable def appendColumnInverse (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (a : Matrix m (Fin 1) ℂ) (W : Matrix (Fin 1) m ℂ) : Matrix (n ⊕ Fin 1) m ℂ := by
  classical
  let d := X * a
  let c := a - A * d
  let b := if c = 0 then 0 else W * (1 - A * X)
  exact fromRows (X - d * b) b

/-- **Exercises 2–3**, Equations (4)–(8) of [benIsrael2003generalized], Chapter 7.
Appending a column preserves the inner inverse equation. If the old inverse
and the residual-column inverse are reflexive, the update is reflexive. -/
theorem exercise_7_2_3_update {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : A.IsInnerInverse X) (a : Matrix m (Fin 1) ℂ) (W : Matrix (Fin 1) m ℂ)
    (hW : (a - A * (X * a)).IsInnerInverse W) :
    (fromCols A a).IsInnerInverse (appendColumnInverse A X a W) ∧
      (A.IsOuterInverse X → (a - A * (X * a)).IsOuterInverse W →
        (fromCols A a).IsOuterInverse (appendColumnInverse A X a W)) := by
  classical
  let d := X * a
  let c := a - A * d
  let P := 1 - A * X
  let b := if c = 0 then 0 else W * P
  have hP : P * A = 0 := by
    dsimp only [P]
    rw [Matrix.sub_mul, Matrix.one_mul, isInnerInverse_iff.mp hX, sub_self]
  have hPc : P * c = c := by
    calc
      P * c = P * a - (P * A) * d := by
        dsimp only [c]
        rw [Matrix.mul_sub, Matrix.mul_assoc]
      _ = c := by
        rw [hP, Matrix.zero_mul, sub_zero]
        simp [P, c, d, Matrix.sub_mul, Matrix.mul_assoc]
  have hbA : b * A = 0 := by
    by_cases hz : c = 0
    · simp [b, hz]
    · simp [b, hz, Matrix.mul_assoc, hP]
  have hb : c * b * c = c := by
    by_cases hz : c = 0
    · simp [hz]
    · have hw : c * W * c = c := isInnerInverse_iff.mp hW
      simpa only [b, ite_eq_right hz, Matrix.mul_assoc, hPc] using
        (show c * W * (P * c) = c by rw [hPc, hw])
  have hImage : fromCols A a * appendColumnInverse A X a W = A * X + c * b := by
    change fromCols A a * fromRows (X - d * b) b = _
    rw [fromCols_mul_fromRows, Matrix.mul_sub, ← Matrix.mul_assoc A d b]
    rw [show c = a - A * d from rfl, Matrix.sub_mul]
    abel
  refine ⟨?_, ?_⟩
  · rw [isInnerInverse_iff, hImage, mul_fromCols]
    have hA : (A * X + c * b) * A = A := by
      rw [Matrix.add_mul, isInnerInverse_iff.mp hX, Matrix.mul_assoc c b A, hbA,
        Matrix.mul_zero, add_zero]
    have hba : b * a = b * c := by
      change b * a = b * (a - A * d)
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hbA, Matrix.zero_mul, sub_zero]
    have ha : (A * X + c * b) * a = a := by
      rw [Matrix.add_mul, Matrix.mul_assoc A X a, Matrix.mul_assoc c b a, hba,
        ← Matrix.mul_assoc c b c, hb]
      change A * d + (a - A * d) = a
      abel
    rw [hA, ha]
  · intro hXo hWo
    have hbo : b * c * b = b := by
      by_cases hz : c = 0
      · simp [b, hz]
      · have hw : W * c * W = W := isOuterInverse_iff.mp hWo
        dsimp only [b]
        rw [ite_eq_right hz]
        calc
          W * P * c * (W * P) = (W * (P * c) * W) * P := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hPc, hw]
    have hXc : X * c = 0 := by
      change X * (a - A * (X * a)) = 0
      simp only [Matrix.mul_sub, ← Matrix.mul_assoc, isOuterInverse_iff.mp hXo, sub_self]
    have hRight : b * (A * X + c * b) = b := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc b A X, hbA, Matrix.zero_mul,
        zero_add, ← Matrix.mul_assoc, hbo]
    have hLeft : X * (A * X + c * b) = X := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc X A X, isOuterInverse_iff.mp hXo,
        ← Matrix.mul_assoc X c b, hXc, Matrix.zero_mul, add_zero]
    rw [isOuterInverse_iff, Matrix.mul_assoc, hImage]
    change fromRows (X - d * b) b * (A * X + c * b) = fromRows (X - d * b) b
    rw [fromRows_mul, Matrix.sub_mul, hLeft, Matrix.mul_assoc d b, hRight]

/-- **Exercises 2–3** of [benIsrael2003generalized], Chapter 7. Invert a
single nonzero entry of the residual column, and put zeros in the other
entries of the inverse row. For a zero column the inverse row is zero. -/
noncomputable def residualColumnInverse (c : Matrix m (Fin 1) ℂ) : Matrix (Fin 1) m ℂ := by
  classical
  exact if h : ∃ i, c i 0 ≠ 0 then Matrix.of (fun _ => Pi.single h.choose (c h.choose 0)⁻¹)
    else 0

/-- **Exercises 2–3** of [benIsrael2003generalized], Chapter 7. A single
reciprocal suffices to construct a reflexive inverse of a nonzero column. -/
theorem residualColumnInverse_spec (c : Matrix m (Fin 1) ℂ) :
    c.IsInnerInverse (residualColumnInverse c) ∧ c.IsOuterInverse (residualColumnInverse c) := by
  classical
  by_cases h : ∃ i, c i 0 ≠ 0
  · have hLeft : residualColumnInverse c * c = 1 := by
      rw [residualColumnInverse, dite_eq_left h]
      ext i j
      have hi : i = 0 := Subsingleton.elim ..
      have hj : j = 0 := Subsingleton.elim ..
      rw [hi, hj]
      change Pi.single h.choose (c h.choose 0)⁻¹ ⬝ᵥ (fun k => c k 0) =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
      rw [dotProduct_comm, dotProduct_single, mul_inv_cancel₀ h.choose_spec]
      simp
    rw [isInnerInverse_iff, isOuterInverse_iff]
    exact ⟨by rw [Matrix.mul_assoc, hLeft, Matrix.mul_one], by rw [hLeft, Matrix.one_mul]⟩
  · have hc : c = 0 := by
      ext i j
      rw [show j = 0 from Subsingleton.elim ..]
      exact not_ne_iff.mp fun hi => h ⟨i, hi⟩
    rw [residualColumnInverse, dite_eq_right h, hc, isInnerInverse_iff, isOuterInverse_iff]
    simp

/-- **Exercises 2–3** of [benIsrael2003generalized], Chapter 7. Process the
columns from left to right, using a scalar reciprocal for each nonzero
residual column. -/
noncomputable def columnwiseReflexiveInverse (m : Type*) [Fintype m] [DecidableEq m] :
    (k : ℕ) → Matrix m (Fin k) ℂ → Matrix (Fin k) m ℂ
  | 0, _ => 0
  | k + 1, A =>
    let B := A.submatrix id (Fin.castAdd 1)
    let a := A.submatrix id (Fin.natAdd k : Fin 1 → Fin (k + 1))
    let X := columnwiseReflexiveInverse m k B
    let c := a - B * (X * a)
    (appendColumnInverse B X a (residualColumnInverse c)).submatrix finSumFinEquiv.symm id

/-- **Exercises 2–3** of [benIsrael2003generalized], Chapter 7. The finite
columnwise iteration returns an inner and outer inverse. -/
theorem columnwiseReflexiveInverse_spec {k : ℕ} (A : Matrix m (Fin k) ℂ) :
    columnwiseReflexiveInverse m k A ∈ definition_1 A {.inner, .outer} := by
  induction k with
  | zero =>
    have hA : A = 0 := by
      ext _ j
      exact Fin.elim0 j
    rw [hA, columnwiseReflexiveInverse, mem_one_two_iff, isInnerInverse_iff, isOuterInverse_iff]
    simp
  | succ k ih =>
    let B := A.submatrix id (Fin.castAdd 1)
    let a := A.submatrix id (Fin.natAdd k : Fin 1 → Fin (k + 1))
    let X := columnwiseReflexiveInverse m k B
    let c := a - B * (X * a)
    let Y := appendColumnInverse B X a (residualColumnInverse c)
    have hA : (fromCols B a).submatrix id (finSumFinEquiv (m := k) (n := 1)).symm = A := by
      have hBlock : fromCols B a = A.submatrix id (finSumFinEquiv (m := k) (n := 1)) := by
        ext i j
        cases j <;> simp [B, a, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      rw [hBlock]
      ext i j
      simp [Matrix.submatrix_apply]
    obtain ⟨hXi, hXo⟩ := mem_one_two_iff.mp (ih B)
    obtain ⟨hWi, hWo⟩ := residualColumnInverse_spec c
    obtain ⟨hYi, hYo⟩ := exercise_7_2_3_update hXi a (residualColumnInverse c) hWi
    have hY : Y ∈ definition_1 (fromCols B a) {.inner, .outer} :=
      mem_one_two_iff.mpr ⟨hYi, hYo hXo hWo⟩
    change Y.submatrix finSumFinEquiv.symm id ∈ definition_1 A {.inner, .outer}
    rw [← hA]
    exact (Chapter05.penroseInverses_submatrix_equiv _ Y (Equiv.refl m)
      (finSumFinEquiv (m := k) (n := 1)).symm _).mpr hY

end ColumnUpdate

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 7. For the two
matrices in the exercise, starting at the small first entry introduces
its reciprocal. A unit first pivot delays division for the first matrix
and leaves the second matrix with $1-\varepsilon$ as its remaining pivot.
The final elimination and scaling step sends each resulting triangular
matrix with nonzero second pivot to the identity. -/
theorem exercise_7_1 (ε : ℂ) (hε : ε ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![ε, 1; 0, 1]
    let B : Matrix (Fin 2) (Fin 2) ℂ := !![ε, 1; 1, 1]
    (!![ε⁻¹, 0; 0, 1] * A = !![1, ε⁻¹; 0, 1]) ∧
      (!![1, 0; -1, 1] * A * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
        !![1, ε; 0, -ε]) ∧
      (!![ε⁻¹, 0; -ε⁻¹, 1] * B = !![1, ε⁻¹; 0, 1 - ε⁻¹]) ∧
      (!![0, 1; 1, -ε] * B = !![1, 1; 0, 1 - ε]) ∧
      ∀ c d : ℂ, d ≠ 0 →
        (!![1, -c / d; 0, d⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, c; 0, d] = 1 := by
  intro A B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two, hε, sub_eq_add_neg, add_comm]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  · intro c d hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]

end BenIsraelGreville.Chapter07
