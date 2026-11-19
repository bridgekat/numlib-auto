/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Transvection
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Substitution
import Numlib.FloatingPoint.System
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.BenIsraelGreville.Chapter02.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter01.Section05
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Least-squares solutions

Section 3.1 of [benIsrael2003generalized] characterizes $\{1,3\}$-inverses as the matrices
that send every right-hand side to a least-squares solution. The least-squares solution set
is an affine space whose direction is the kernel of the original matrix.

## Deviations from the source

* Exercise 4 uses nearest rounding with ties to even for the final
  rounding. The working-precision midpoint can be attained at the
  higher precision. The rounding functions use unrestricted exponents.
* In Exercise 6, convergence gives an exact solution when the net
  arithmetic error vanishes. An explicit finite-precision run can
  converge to a point with nonzero exact residual.
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_three_iff)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix m n ℂ}

/-- **Section 3.1** of [benIsrael2003generalized]. A least-squares solution of $Ax=b$ is
a minimizer of the Euclidean norm of the residual. -/
abbrev leastSquaresSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) : Prop :=
  IsLeastSquaresSolution A b x

/-- A vector solves least squares exactly when its image equals the image of $A^\dagger b$. -/
theorem leastSquaresSolution_iff_image_eq {b : EuclideanSpace ℂ m} {x : EuclideanSpace ℂ n} :
    leastSquaresSolution A b x ↔
      toEuclideanLin A x = toEuclideanLin A (toEuclideanLin A.pinv b) := by
  constructor
  · intro hx
    have hd := toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
      (isLeastSquaresSolution_iff_normalEquations.mp hx)
    rw [map_sub, sub_eq_zero] at hd
    exact hd
  · intro hx
    apply isLeastSquaresSolution_iff_normalEquations.mpr
    rw [toEuclideanLin_mul_apply, hx,
      ← toEuclideanLin_mul_apply, normalEquations_pinv]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 3. A matrix $X$ maps each right-hand
side $b$ to a least-squares solution of $Ax=b$ exactly when $X$ is a $\{1,3\}$-inverse of $A$. -/
theorem theorem_1 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    X ∈ definition_1 A {.inner, .hermitianMul} ↔
      ∀ b, leastSquaresSolution A b (toEuclideanLin X b) := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMul} :=
    mem_one_three_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_mul_pinv⟩
  rw [Chapter02.theorem_3 hp]
  simp only [leastSquaresSolution_iff_image_eq, ← toEuclideanLin_mul_apply]
  exact ⟨fun h b => congrArg (fun M => toEuclideanLin M b) h,
    fun h => toEuclideanLin.injective (LinearMap.ext h)⟩

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 3. For a $\{1,3\}$-inverse $X$,
the least-squares solutions are precisely the vectors with image $AXb$, which are all vectors
of the form $Xb+(I-XA)y$. -/
theorem corollary_1 {X : Matrix n m ℂ} (hX : X ∈ definition_1 A {.inner, .hermitianMul})
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    (leastSquaresSolution A b x ↔ toEuclideanLin A x = toEuclideanLin (A * X) b) ∧
      (leastSquaresSolution A b x ↔ ∃ y : EuclideanSpace ℂ n,
        x = toEuclideanLin X b + toEuclideanLin (1 - X * A) y) := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMul} :=
    mem_one_three_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_mul_pinv⟩
  have hEq := (Chapter02.theorem_3 hp).mp hX
  have hx : leastSquaresSolution A b x ↔ toEuclideanLin A x = toEuclideanLin (A * X) b := by
    rw [leastSquaresSolution_iff_image_eq, ← toEuclideanLin_mul_apply, hEq]
  refine ⟨hx, hx.trans ?_⟩
  constructor
  · intro h
    have hd : toEuclideanLin A (x - toEuclideanLin X b) = 0 := by
      rw [map_sub, ← toEuclideanLin_mul_apply, h, sub_self]
    refine ⟨x - toEuclideanLin X b, ?_⟩
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply, hd,
      map_zero, sub_zero, add_sub_cancel]
  · rintro ⟨y, rfl⟩
    have hzero : A * (1 - X * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        isInnerInverse_iff.mp (mem_one_three_iff.mp hX).1, sub_self]
    rw [map_add, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, hzero]
    simp only [toEuclideanLin_zero_apply, add_zero]

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 3.
A least-squares solution is precisely a solution of the normal equation. -/
theorem exercise_3_1 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    leastSquaresSolution A b x ↔ toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b :=
  isLeastSquaresSolution_iff_normalEquations

/-- **Exercise 2** of [benIsrael2003generalized], Chapter 3.
The normal equation is consistent for every right-hand side of the original system. -/
theorem exercise_3_2 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    ∃ x, toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ b :=
  ⟨toEuclideanLin A.pinv b, normalEquations_pinv A b⟩

/-- **Exercise 3** of [benIsrael2003generalized], Chapter 3.
Any inner inverse of the Gram matrix gives the affine least-squares solution set. -/
theorem exercise_3_3 (A : Matrix m n ℂ) (U : Matrix n n ℂ)
    (hU : (Aᴴ * A).IsInnerInverse U) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    leastSquaresSolution A b x ↔ ∃ y : EuclideanSpace ℂ n,
      x = toEuclideanLin (U * Aᴴ) b + toEuclideanLin (1 - U * Aᴴ * A) y := by
  have hG := Chapter01.theorem_3_a A (Chapter01.mem_one_iff.mpr hU)
  have h13 : U * Aᴴ ∈ definition_1 A {.inner, .hermitianMul} := by
    refine Matrix.mem_penroseInverses_iff.mpr fun c hc => ?_
    exact Matrix.mem_penroseInverses_iff.mp hG c (by
      rcases hc with rfl | rfl <;> simp)
  exact (corollary_1 h13 b x).2

/-- **Exercise 4** of [benIsrael2003generalized], Chapter 3.
A full-column-rank example has a rank-one computed Gram matrix whenever
the entrywise rounding identifies 1+ε² with 1. The rounded normal
equation can be inconsistent and can admit a spurious solution. -/
theorem exercise_3_4 (ε : ℝ) (hε : ε ≠ 0) (round : ℝ → ℝ)
    (h₁ : round 1 = 1) (h₂ : round (1 + ε ^ 2) = 1) :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, 1; ε, 0; 0, ε]
    let G : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
    A.rank = 2 ∧ (Aᵀ * A).map round = G ∧ G.rank = 1 ∧
      (¬ ∃ x : Fin 2 → ℝ, G *ᵥ x = Aᵀ *ᵥ ![0, 1, 0]) ∧
      G *ᵥ ![1, -1] = 0 ∧ ¬ IsLeastSquaresSolution A 0 (WithLp.toLp 2 ![1, -1]) := by
  let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, 1; ε, 0; 0, ε]
  let G : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
  have hA : A.rank = 2 := by
    refine le_antisymm (by simpa using rank_le_card_width A) ?_
    apply A.card_le_rank_of_det_submatrix_ne_zero (r := Fin.succ) (c := id)
    simpa [A, Matrix.det_fin_two] using mul_ne_zero hε hε
  have hGG : Aᵀ * A = !![1 + ε ^ 2, 1; 1, 1 + ε ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_succ, pow_two]
  have hG : G.rank = 1 := by
    have hR : G.rank ≤ 1 := (Matrix.rank_le_iff_exists_mul G 1).mpr
      ⟨!![1; 1], !![1, 1], by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [G, Matrix.mul_apply]⟩
    have hG0 : G.rank ≠ 0 := by
      intro h
      have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
        (rank_eq_zero_iff.mp h)
      norm_num [G] at hz
    omega
  have hrounded : (Aᵀ * A).map round = G := by
    rw [hGG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G, h₁, h₂]
  refine ⟨hA, hrounded, hG, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have h0 := congrFun hx (0 : Fin 2)
    have h1 := congrFun hx (1 : Fin 2)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    exact hε (h0.symm.trans h1)
  · funext i
    fin_cases i <;> norm_num [G, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have he := h 0
    simp only [map_zero, sub_zero, norm_zero] at he
    have hv : toEuclideanLin A (WithLp.toLp 2 ![1, -1]) = 0 :=
      norm_eq_zero.mp (le_antisymm he (norm_nonneg _))
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x (1 : Fin 3)) hv
    exact hε (by simpa [A, toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh)

/-- **Exercise 5**, Equations (12)–(13), of [benIsrael2003generalized],
Chapter 3. The invertible upper block reduces the stacked normal equation
to the equation with Gram matrix I+SᴴS. -/
theorem exercise_3_5 {p : Type*} [Fintype p] [DecidableEq p]
    (A₁ : Matrix n n ℂ) (A₂ : Matrix p n ℂ) (hA₁ : IsUnit A₁)
    (b₁ : n → ℂ) (b₂ : p → ℂ) (x : n → ℂ) :
    let A := fromRows A₁ A₂
    let S := A₂ * A₁⁻¹
    A = fromRows (1 : Matrix n n ℂ) S * A₁ ∧
    (leastSquaresSolution A (WithLp.toLp 2 (Sum.elim b₁ b₂)) (WithLp.toLp 2 x) ↔
      (1 + Sᴴ * S) *ᵥ (A₁ *ᵥ x) = b₁ + Sᴴ *ᵥ b₂) := by
  let S := A₂ * A₁⁻¹
  let A := fromRows A₁ A₂
  let E := fromRows (1 : Matrix n n ℂ) S
  have hA : A = E * A₁ := by
    dsimp only [A, E, S]
    rw [fromRows_mul, Matrix.one_mul, Matrix.mul_assoc A₂ A₁⁻¹ A₁,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA₁), Matrix.mul_one]
  have hS : Eᴴ * E = 1 + Sᴴ * S := by
    rw [show E = fromRows 1 S from rfl, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromRows, conjTranspose_one, Matrix.one_mul]
  have hb : Eᴴ *ᵥ Sum.elim b₁ b₂ = b₁ + Sᴴ *ᵥ b₂ := by
    ext i
    simp only [E, conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
      Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    change ((1 : Matrix n n ℂ) *ᵥ b₁) i + _ = _
    rw [one_mulVec]
  have hnormal : Aᴴ * A = A₁ᴴ * (1 + Sᴴ * S) * A₁ := calc
    _ = A₁ᴴ * (Eᴴ * E) * A₁ := by rw [hA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hS]
  have hright : Aᴴ *ᵥ Sum.elim b₁ b₂ = A₁ᴴ *ᵥ (b₁ + Sᴴ *ᵥ b₂) := by
    rw [hA, conjTranspose_mul, ← mulVec_mulVec, hb]
  refine ⟨hA, ?_⟩
  change leastSquaresSolution A (WithLp.toLp 2 (Sum.elim b₁ b₂)) (WithLp.toLp 2 x) ↔
    (1 + Sᴴ * S) *ᵥ (A₁ *ᵥ x) = b₁ + Sᴴ *ᵥ b₂
  rw [exercise_3_1, toEuclideanLin_toLp, toEuclideanLin_toLp, (WithLp.toLp_injective 2).eq_iff,
    hnormal, hright, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  exact (mulVec_injective_iff_isUnit.mpr hA₁.star).eq_iff

/-- The reduced equation from **Exercise 5** gives the solution of the
top block exactly when the lower discrepancy is orthogonal to the
columns of S. Consistency of the entire stack implies this condition. -/
theorem exercise_3_5_reduction {p : Type*} [Fintype p] [DecidableEq p]
    (S : Matrix p n ℂ) (b₁ : n → ℂ) (b₂ : p → ℂ) :
    ((1 + Sᴴ * S) *ᵥ b₁ = b₁ + Sᴴ *ᵥ b₂ ↔ Sᴴ *ᵥ (b₂ - S *ᵥ b₁) = 0) ∧
      (S *ᵥ b₁ = b₂ → Sᴴ *ᵥ (b₂ - S *ᵥ b₁) = 0) := by
  constructor
  · rw [add_mulVec, one_mulVec, ← mulVec_mulVec, mulVec_sub, sub_eq_zero, add_right_inj, eq_comm]
  · intro h
    rw [h, sub_self, mulVec_zero]


omit [Fintype m] [DecidableEq m] in
/-- **Exercise 6** of [benIsrael2003generalized], Chapter 3.
Every exact residual correction yields a solution at the next refinement step. -/
theorem exercise_3_6 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (x δ : ℕ → EuclideanSpace ℂ n)
    (hδ : ∀ k, toEuclideanLin A (δ k) = b - toEuclideanLin A (x k))
    (hx : ∀ k, x (k + 1) = x k + δ k) :
    ∀ k, toEuclideanLin A (x (k + 1)) = b := by
  intro k
  rw [hx, map_add, hδ, add_sub_cancel]

/-- **Exercise 7** of [benIsrael2003generalized], Chapter 3.
The two block rows say that the residual is the difference from the fit
and is in the kernel of the adjoint. -/
theorem exercise_3_7 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    leastSquaresSolution A b x ↔ ∃ r : EuclideanSpace ℂ m,
      r + toEuclideanLin A x = b ∧ toEuclideanLin Aᴴ r = 0 := by
  rw [exercise_3_1, toEuclideanLin_mul_apply]
  constructor
  · intro h
    refine ⟨b - toEuclideanLin A x, sub_add_cancel _ _, ?_⟩
    rw [map_sub, h, sub_self]
  · rintro ⟨r, hr, hzero⟩
    rw [← hr, map_add, hzero, zero_add]

section SeveralRightHandSides

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exercise 9**, Equations (15)–(16), of [benIsrael2003generalized],
Chapter 3. Summing squared residuals is least squares for the stacked
matrix, and its normal equation is the sum of the individual equations. -/
theorem exercise_3_9 (A : ι → Matrix m n ℂ) (b : ι → EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) :
    IsMinOn (fun z : EuclideanSpace ℂ n => ∑ i, ‖toEuclideanLin (A i) z - b i‖ ^ 2) Set.univ x ↔
      toEuclideanLin (∑ i, (A i)ᴴ * A i) x = ∑ i, toEuclideanLin (A i)ᴴ (b i) := by
  let S : Matrix (ι × m) n ℂ := fun i j => A i.1 i.2 j
  let c : EuclideanSpace ℂ (ι × m) := WithLp.toLp 2 fun i => b i.1 i.2
  have hrs (z : EuclideanSpace ℂ n) :
      ‖toEuclideanLin S z - c‖ ^ 2 = ∑ i, ‖toEuclideanLin (A i) z - b i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hG : Sᴴ * S = ∑ i, (A i)ᴴ * A i := by
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
    rfl
  have hC : toEuclideanLin Sᴴ c = ∑ i, toEuclideanLin (A i)ᴴ (b i) := by
    ext i
    simp only [c, WithLp.ofLp_sum, Finset.sum_apply, toEuclideanLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    rfl
  rw [← hG, ← hC, ← exercise_3_1, isMinOn_univ_iff]
  change (∀ y, (∑ i, ‖toEuclideanLin (A i) x - b i‖ ^ 2) ≤
    ∑ i, ‖toEuclideanLin (A i) y - b i‖ ^ 2) ↔
    ∀ y, ‖toEuclideanLin S x - c‖ ≤ ‖toEuclideanLin S y - c‖
  simp only [← hrs, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

/-- **Exercise 8** of [benIsrael2003generalized], Chapter 3.
Several observations for one matrix are equivalent to fitting their mean. -/
theorem exercise_3_8 [Nonempty ι] (A : Matrix m n ℂ) (b : ι → EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) :
    IsMinOn (fun z : EuclideanSpace ℂ n => ∑ i, ‖toEuclideanLin A z - b i‖ ^ 2) Set.univ x ↔
      leastSquaresSolution A ((Fintype.card ι : ℂ)⁻¹ • ∑ i, b i) x := by
  let c : ℂ := Fintype.card ι
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [exercise_3_9 (fun _ : ι => A) b, exercise_3_1]
  have hG : (∑ _ : ι, Aᴴ * A) = c • (Aᴴ * A) := by
    simp only [Finset.sum_const, Finset.card_univ, c, Nat.cast_smul_eq_nsmul]
  rw [hG, ← map_sum, toEuclideanLin_smul_apply, map_smul]
  constructor
  · intro h
    rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro h
    rw [h, smul_smul, mul_inv_cancel₀ hc, one_smul]

end SeveralRightHandSides

section Constrained

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- A compatible equation has an affine solution set for every chosen inner inverse. -/
theorem exactSolution_iff_innerParameter {B : Matrix p n ℂ} {U : Matrix n p ℂ}
    (hU : B.IsInnerInverse U) {d : EuclideanSpace ℂ p}
    (hd : d ∈ LinearMap.range (toEuclideanLin B)) (x : EuclideanSpace ℂ n) :
    toEuclideanLin B x = d ↔ ∃ y : EuclideanSpace ℂ n,
      x = toEuclideanLin U d + toEuclideanLin (1 - U * B) y := by
  have hb : toEuclideanLin B (toEuclideanLin U d) = d := by
    obtain ⟨z, rfl⟩ := hd
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, isInnerInverse_iff.mp hU]
  constructor
  · intro h
    refine ⟨x, ?_⟩
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply, h]
    abel
  · rintro ⟨y, rfl⟩
    rw [map_add, hb, ← toEuclideanLin_mul_apply, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, isInnerInverse_iff.mp hU, sub_self, toEuclideanLin_zero_apply, add_zero]

/-- A feasible vector with least residual norm on its affine constraint set. -/
def IsConstrainedLeastSquaresSolution (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (b : EuclideanSpace ℂ m) (d : EuclideanSpace ℂ p) (x : EuclideanSpace ℂ n) : Prop :=
  toEuclideanLin B x = d ∧ ∀ y, toEuclideanLin B y = d →
    ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

omit [DecidableEq m] in
private theorem constrained_iff_reduced {A : Matrix m n ℂ} {B : Matrix p n ℂ}
    {U : Matrix n p ℂ} (hU : B.IsInnerInverse U)
    (b : EuclideanSpace ℂ m) {d : EuclideanSpace ℂ p}
    (hd : d ∈ LinearMap.range (toEuclideanLin B)) (x : EuclideanSpace ℂ n) :
    let P := 1 - U * B
    let z := toEuclideanLin U d
    IsConstrainedLeastSquaresSolution A B b d x ↔ ∃ y : EuclideanSpace ℂ n,
      x = z + toEuclideanLin P y ∧ leastSquaresSolution (A * P) (b - toEuclideanLin A z) y := by
  intro P z
  have hfeasible (x : EuclideanSpace ℂ n) :
      toEuclideanLin B x = d ↔ ∃ y : EuclideanSpace ℂ n, x = z + toEuclideanLin P y :=
    exactSolution_iff_innerParameter hU hd x
  have hres (y : EuclideanSpace ℂ n) : toEuclideanLin A (z + toEuclideanLin P y) - b =
      toEuclideanLin (A * P) y - (b - toEuclideanLin A z) := by
    rw [map_add, toEuclideanLin_mul_apply]
    abel
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨y, rfl⟩ := (hfeasible x).mp hx
    refine ⟨y, rfl, fun w => ?_⟩
    rw [← hres, ← hres]
    exact hmin _ ((hfeasible _).mpr ⟨w, rfl⟩)
  · rintro ⟨y, rfl, hmin⟩
    refine ⟨(hfeasible _).mpr ⟨y, rfl⟩, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := (hfeasible w).mp hw
    rw [hres, hres]
    exact hmin v

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 3.
Parameterizing the feasible affine space gives the complete constrained
least-squares solution set by a reduced ordinary least-squares problem. -/
theorem exercise_3_10 (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (U : Matrix n p ℂ) (hU : B.IsInnerInverse U)
    (b : EuclideanSpace ℂ m) {d : EuclideanSpace ℂ p}
    (hd : d ∈ LinearMap.range (toEuclideanLin B)) (x : EuclideanSpace ℂ n)
    (Z : Matrix n m ℂ) (hZ : Z ∈ definition_1 (A * (1 - U * B)) {.inner, .hermitianMul}) :
    let P := 1 - U * B
    let z := toEuclideanLin U d
    let C := A * P
    let e := b - toEuclideanLin A z
    IsConstrainedLeastSquaresSolution A B b d x ↔ ∃ w : EuclideanSpace ℂ n,
      x = z + toEuclideanLin P (toEuclideanLin Z e + toEuclideanLin (1 - Z * C) w) := by
  intro P z C e
  have h := constrained_iff_reduced (A := A) hU b hd x
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨y, hy, hls⟩
    obtain ⟨w, rfl⟩ := ((corollary_1 hZ e y).2).mp hls
    exact ⟨w, hy⟩
  · rintro ⟨w, hw⟩
    exact ⟨_, hw, (corollary_1 hZ e _).2.mpr ⟨w, rfl⟩⟩

/-- **Exercise 11**, Equation (21), of [benIsrael2003generalized], Chapter 3.
The constrained residual minimizers are exactly the feasible vectors
that admit a multiplier satisfying the displayed saddle system. -/
theorem exercise_3_11 (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (b : EuclideanSpace ℂ m) (d : EuclideanSpace ℂ p) (x : EuclideanSpace ℂ n) :
    IsConstrainedLeastSquaresSolution A B b d x ↔
      toEuclideanLin B x = d ∧ ∃ z : EuclideanSpace ℂ p,
        toEuclideanLin (Aᴴ * A) x + toEuclideanLin Bᴴ z = toEuclideanLin Aᴴ b := by
  unfold IsConstrainedLeastSquaresSolution
  apply and_congr_right
  intro hx
  let K := (toEuclideanLin B).ker
  let P := Chapter02.orthogonalProjector K
  let b' := b - toEuclideanLin A x
  have hp : toEuclideanLin P = K.starProjection.toLinearMap :=
    Chapter02.toEuclideanLin_orthogonalProjector K
  have hshift (u : EuclideanSpace ℂ n) :
      toEuclideanLin (A * P) u - b' = toEuclideanLin A (x + toEuclideanLin P u) - b := by
    rw [toEuclideanLin_mul_apply, map_add]
    dsimp only [b']
    abel
  have heq : (∀ y, toEuclideanLin B y = d →
      ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖) ↔
      leastSquaresSolution (A * P) b' 0 := by
    have hstart : toEuclideanLin (A * P) 0 - b' = toEuclideanLin A x - b := by
      rw [hshift, map_zero, add_zero]
    constructor
    · intro h u
      rw [hstart, hshift]
      apply h
      have hnull : toEuclideanLin B (toEuclideanLin P u) = 0 := by
        rw [hp]
        exact K.starProjection_apply_mem u
      rw [map_add, hx, hnull, add_zero]
    · intro h y hy
      have hmem : y - x ∈ K := by
        change toEuclideanLin B (y - x) = 0
        rw [map_sub, hy, hx, sub_self]
      have hf : toEuclideanLin P (y - x) = y - x := by
        rw [hp]
        exact K.starProjection_eq_self_iff.mpr hmem
      have hh := h (y - x)
      rw [hstart, hshift, hf] at hh
      rw [show x + (y - x) = y by abel] at hh
      exact hh
  rw [heq, exercise_3_1 (A * P) b' 0, map_zero, eq_comm (a := (0 : EuclideanSpace ℂ n))]
  have hM : (A * P)ᴴ = P * Aᴴ := by
    rw [conjTranspose_mul, (Chapter02.isHermitian_orthogonalProjector K).eq]
  rw [hM, toEuclideanLin_mul_apply, hp]
  change K.starProjection (toEuclideanLin Aᴴ b') = 0 ↔ _
  rw [K.starProjection_apply_eq_zero_iff]
  have hK : Kᗮ = LinearMap.range (toEuclideanLin Bᴴ) := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint]
    exact (toEuclideanLin B).orthogonal_ker
  rw [hK]
  change (∃ z, toEuclideanLin Bᴴ z = toEuclideanLin Aᴴ b') ↔ _
  simp only [b', map_sub, ← toEuclideanLin_mul_apply, eq_sub_iff_add_eq, add_comm]

/-- The residual-variable form of the saddle system in **Exercise 11**. -/
theorem exercise_3_11_residual (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (b : EuclideanSpace ℂ m) (d : EuclideanSpace ℂ p) (x : EuclideanSpace ℂ n) :
    IsConstrainedLeastSquaresSolution A B b d x ↔
      ∃ (r : EuclideanSpace ℂ m) (z : EuclideanSpace ℂ p),
        r + toEuclideanLin A x = b ∧ toEuclideanLin Aᴴ r = toEuclideanLin Bᴴ z ∧
          toEuclideanLin B x = d := by
  rw [exercise_3_11]
  constructor
  · rintro ⟨hx, z, hz⟩
    refine ⟨b - toEuclideanLin A x, z, sub_add_cancel _ _, ?_, hx⟩
    rw [map_sub, ← toEuclideanLin_mul_apply, sub_eq_iff_eq_add]
    exact hz.symm.trans (add_comm _ _)
  · rintro ⟨r, z, hr, hz, hx⟩
    refine ⟨hx, z, ?_⟩
    rw [← hr, map_add, hz, ← toEuclideanLin_mul_apply, add_comm]

end Constrained

section BinaryRounding

open Matrix FloatingPoint

/-- Nearest rounding in a floating-point system, with an even integer
mantissa chosen at an exact midpoint. -/
noncomputable def roundNearestEven (s : FloatingPoint.System) (x : ℝ) : ℝ :=
  let μ := s.mantissa x
  let m := ⌊μ⌋
  if μ = (m : ℝ) + 1 / 2 ∧ Even m then
    (SignType.sign x : ℝ) * (m : ℝ) * (s.β : ℝ) ^ (s.exponent x - s.t)
  else s.round x

private theorem binary_binade (s : FloatingPoint.System) (hs : s.β = 2)
    {x : ℝ} (hlo : 1 ≤ x) (hhi : x < 2) :
    s.exponent x = 1 ∧ s.mantissa x = x * (2 : ℝ) ^ ((s.t : ℤ) - 1) := by
  have hn : 0 ≤ x := by linarith
  have he : s.exponent x = 1 := s.exponent_eq_of_le_of_lt
    (by simpa [hs, abs_of_nonneg hn] using hlo) (by simpa [hs, abs_of_nonneg hn] using hhi)
  exact ⟨he, by simp [FloatingPoint.System.mantissa, he, hs, abs_of_nonneg hn]⟩

private theorem binary_round_zpow (s : FloatingPoint.System) (hs : s.β = 2) (a : ℤ) :
    s.round ((2 : ℝ) ^ a) = (2 : ℝ) ^ a := by
  have hp : 0 < (2 : ℝ) ^ a := zpow_pos (by norm_num) _
  have he : s.exponent ((2 : ℝ) ^ a) = a + 1 := by
    rw [FloatingPoint.System.exponent, abs_of_pos hp, hs]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Int.log_zpow (by decide : 1 < 2)]
  rw [s.round_of_pos hp, FloatingPoint.System.mantissa, he, abs_of_pos hp, hs, Nat.cast_ofNat,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    show a + ((s.t : ℤ) - (a + 1)) = (s.t : ℤ) - 1 by omega]
  rw [show (2 : ℝ) ^ ((s.t : ℤ) - 1) = (((2 ^ (s.t - 1) : ℕ) : ℤ) : ℝ) by
    simpa [hs] using (s.natCast_pow_t_sub_one (K := ℝ)).symm, round_intCast]
  rw [show (((2 ^ (s.t - 1) : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ ((s.t : ℤ) - 1) by
    simpa [hs] using (s.natCast_pow_t_sub_one (K := ℝ))]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

private theorem binary_round_midpoint (s : FloatingPoint.System) (hs : s.β = 2)
    {t : ℕ} (ht : 0 < t) (hT : t < s.t) :
    s.round (1 + (2 : ℝ) ^ (-(t : ℤ))) = 1 + (2 : ℝ) ^ (-(t : ℤ)) := by
  let x := 1 + (2 : ℝ) ^ (-(t : ℤ))
  have hx : 1 ≤ x := le_add_of_nonneg_right (zpow_nonneg (by norm_num) _)
  have hx' : x < 2 := by
    have hp : (2 : ℝ) ^ (-(t : ℤ)) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    dsimp [x]
    linarith
  obtain ⟨he, hm⟩ := binary_binade s hs hx hx'
  have hnon : 0 ≤ (s.t : ℤ) - 1 - t := by omega
  let d : ℤ := 2 ^ (s.t - 1) + 2 ^ ((s.t : ℤ) - 1 - t).toNat
  have hscale : (2 : ℝ) ^ ((s.t : ℤ) - 1) = (((2 ^ (s.t - 1) : ℕ) : ℤ) : ℝ) := by
    simpa [hs] using (s.natCast_pow_t_sub_one (K := ℝ)).symm
  have hrest : (2 : ℝ) ^ ((s.t : ℤ) - 1 - t) =
      (((2 ^ ((s.t : ℤ) - 1 - t).toNat : ℕ) : ℤ) : ℝ) := by
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg hnon]
  have hd : s.mantissa x = (d : ℝ) := by
    rw [hm]
    dsimp only [x,d]
    push_cast
    rw [add_mul, one_mul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show -(t : ℤ) + ((s.t : ℤ) - 1) = (s.t : ℤ) - 1 - t by omega]
    push_cast at hscale hrest
    rw [hscale, hrest]
  change s.round x = x
  rw [s.round_of_pos (by linarith : 0 < x), hd, round_intCast, ← hd]
  simpa only [abs_of_nonneg (by linarith : 0 ≤ x)] using
    (s.abs_eq_mantissa_mul_zpow x).symm

private theorem binary_roundNearestEven_one_binade (s : FloatingPoint.System) (hs : s.β = 2)
    (ht : 2 ≤ s.t) {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 1 + (2 : ℝ) ^ (-(s.t : ℤ))) :
    roundNearestEven s x = 1 := by
  have htop : x < 2 := by
    have hp : (2 : ℝ) ^ (-(s.t : ℤ)) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    linarith
  obtain ⟨he, hm⟩ := binary_binade s hs hlo htop
  let m : ℤ := (2 : ℕ) ^ (s.t - 1)
  have hbase : (2 : ℝ) ^ ((s.t : ℤ) - 1) = (m : ℝ) := by
    simpa [m, hs] using (s.natCast_pow_t_sub_one (K := ℝ)).symm
  have hm' : (m : ℝ) ≤ s.mantissa x ∧ s.mantissa x ≤ (m : ℝ) + 1 / 2 := by
    rw [hm, ← hbase]
    constructor
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hlo
        (zpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ((s.t : ℤ) - 1))
    · calc
        _ ≤ (1 + (2 : ℝ) ^ (-(s.t : ℤ))) * (2 : ℝ) ^ ((s.t : ℤ) - 1) :=
          mul_le_mul_of_nonneg_right hhi (zpow_nonneg (by norm_num) _)
        _ = _ := by
          rw [add_mul, one_mul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            show -(s.t : ℤ) + ((s.t : ℤ) - 1) = -1 by omega, _root_.zpow_neg_one]
          ring
  have hfloor : ⌊s.mantissa x⌋ = m := Int.floor_eq_iff.mpr ⟨hm'.1, by linarith [hm'.2]⟩
  have heven : Even m := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s.t - 1 = k + 1 := ⟨s.t - 2, by omega⟩
    refine ⟨(2 ^ k : ℕ), ?_⟩
    dsimp [m]
    rw [hk, pow_succ]
    ring
  have hprod : (m : ℝ) * (s.β : ℝ) ^ (s.exponent x - s.t) = 1 := by
    rw [← hbase, hs, Nat.cast_ofNat, he, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  by_cases hh : s.mantissa x = (m : ℝ) + 1 / 2
  · unfold roundNearestEven
    dsimp only
    rw [hfloor, ite_eq_left ⟨hh, heven⟩, sign_pos (by linarith : 0 < x)]
    simpa only [SignType.coe_one, one_mul] using hprod
  · have hr : _root_.round (s.mantissa x) = m :=
      round_eq_iff.mpr ⟨by linarith [hm'.1], lt_of_le_of_ne hm'.2 hh⟩
    simp only [roundNearestEven, hfloor, hh, false_and, ite_false]
    rw [s.round_of_pos (by linarith), hr, hprod]

/-- **Exercise 4** of [benIsrael2003generalized], Chapter 3.
With binary working precision and at least one extra digit for the dot
products, both rounded diagonal entries of the Gram matrix equal one.
The final rounding uses ties to even since the higher precision can land
exactly on the working-precision midpoint. -/
theorem exercise_3_4_double_then_single_rounding
    (work high : FloatingPoint.System) (hw : work.β = 2) (hh : high.β = 2)
    (ht : 2 ≤ work.t) (hp : work.t < high.t) (ε : ℝ) (hε : ε ≠ 0)
    (hsmall : |ε| < √((2 : ℝ) ^ (-(work.t : ℤ)))) :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, 1; ε, 0; 0, ε]
    let d := high.round (1 + high.round (ε * ε))
    let G : Matrix (Fin 2) (Fin 2) ℝ := !![d, 1; 1, d]
    RoundsMul (high.roundingModel ℝ) Aᵀ A G ∧
      G.map (roundNearestEven work) = !![1, 1; 1, 1] ∧
      A.rank = 2 ∧ (G.map (roundNearestEven work)).rank = 1 := by
  intro A d G
  have h1 : high.round (1 : ℝ) = 1 := by
    simpa only [zpow_zero] using binary_round_zpow high hh 0
  have he : 0 ≤ high.round (ε * ε) := by
    simpa only [FloatingPoint.System.round_zero] using high.round_mono (mul_self_nonneg ε)
  have h0 : ε * ε ≤ (2 : ℝ) ^ (-(work.t : ℤ)) := by
    have hSQ := (sq_lt_sq₀ (abs_nonneg ε) (Real.sqrt_nonneg _)).mpr hsmall
    rw [sq_abs, Real.sq_sqrt (by positivity), pow_two] at hSQ
    exact hSQ.le
  have hR := high.round_mono h0
  rw [binary_round_zpow high hh] at hR
  have hd₁ : 1 ≤ d := by
    have H : (1 : ℝ) ≤ 1 + high.round (ε * ε) := by linarith
    simpa only [d, h1] using high.round_mono H
  have hd₂ : d ≤ 1 + (2 : ℝ) ^ (-(work.t : ℤ)) := by
    have H := high.round_mono (add_le_add (le_refl (1 : ℝ)) hR)
    rw [binary_round_midpoint high hh (by omega : 0 < work.t) hp] at H
    exact H
  have hwork1 := binary_roundNearestEven_one_binade work hw ht (le_refl (1 : ℝ))
    (le_add_of_nonneg_right (zpow_nonneg (by norm_num) _))
  have hworkd := binary_roundNearestEven_one_binade work hw ht hd₁ hd₂
  have hmap : G.map (roundNearestEven work) = !![1, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G, hwork1, hworkd]
  have hRank := exercise_3_4 ε hε (fun _ => 1) rfl rfl
  refine ⟨?_, hmap, hRank.1, hmap ▸ hRank.2.2.1⟩
  intro i j
  let p : Fin 3 → ℝ := fun k => high.round (A k i * A k j)
  refine ⟨[0, 1, 2], p, by decide, by intro k; fin_cases k <;> decide,
    fun k => rfl, ?_⟩
  have hR1 : (high.roundingModel ℝ).Rounds (1 + 0) 1 := by
    simp [h1]
  have hRd : (high.roundingModel ℝ).Rounds (1 + high.round (ε * ε)) d := rfl
  have hRd0 : (high.roundingModel ℝ).Rounds (d + 0) d := by
    simp [d, FloatingPoint.System.round_round]
  fin_cases i <;> fin_cases j
  · simpa [A, G, p, h1, RoundsSum] using
      (RoundsSumFrom.cons hRd (RoundsSumFrom.cons hRd0 (RoundsSumFrom.nil d)))
  · simpa [A, G, p, h1, RoundsSum] using
      (RoundsSumFrom.cons hR1 (RoundsSumFrom.cons hR1 (RoundsSumFrom.nil (1 : ℝ))))
  · simpa [A, G, p, h1, RoundsSum] using
      (RoundsSumFrom.cons hR1 (RoundsSumFrom.cons hR1 (RoundsSumFrom.nil (1 : ℝ))))
  · simpa [A, G, p, h1, RoundsSum] using
      (RoundsSumFrom.cons hR1 (RoundsSumFrom.cons hRd (RoundsSumFrom.nil d)))

end BinaryRounding

section AugmentedElimination

open Matrix

private theorem nonsingular_factors_for_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    ∃ L : List (Matrix ι ι ℂ), L.prod = A ∧
      ∀ M ∈ L, (∃ d : ι → ℂ, (∀ i, d i ≠ 0) ∧ M = diagonal d) ∨
        ∃ t : TransvectionStruct ι ℂ, M = t.toMatrix := by
  let P : Matrix ι ι ℂ → Prop := fun A =>
    ∃ L : List (Matrix ι ι ℂ), L.prod = A ∧
      ∀ M ∈ L, (∃ d : ι → ℂ, (∀ i, d i ≠ 0) ∧ M = diagonal d) ∨
        ∃ t : TransvectionStruct ι ℂ, M = t.toMatrix
  apply diagonal_transvection_induction_of_det_ne_zero P A hA
  · intro d hd
    have hdi (i : ι) : d i ≠ 0 := by
      rw [det_diagonal] at hd
      intro h
      exact hd (Finset.prod_eq_zero (Finset.mem_univ i) h)
    refine ⟨[diagonal d], by simp, ?_⟩
    intro M hM
    rw [List.mem_singleton] at hM
    exact Or.inl ⟨d, hdi, hM⟩
  · intro t
    refine ⟨[t.toMatrix], by simp, ?_⟩
    intro M hM
    exact Or.inr ⟨t, List.mem_singleton.mp hM⟩
  · rintro A B _ _ ⟨L, hL, hF⟩ ⟨K, hK, hG⟩
    refine ⟨L ++ K, by rw [List.prod_append, hL, hK], ?_⟩
    intro M hM
    exact (List.mem_append.mp hM).elim (hF M) (hG M)

/-- **Exercise 5** of [benIsrael2003generalized], Chapter 3.
The full augmented matrix admits the displayed row reduction. Each row
scaling has a nonzero factor, and the other factors are row additions. -/
theorem exercise_3_5_augmented_gauss_jordan {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A₁ : Matrix n n ℂ) (A₂ : Matrix p n ℂ) (hA₁ : IsUnit A₁)
    (b₁ : n → ℂ) (b₂ : p → ℂ) :
    let S := A₂ * A₁⁻¹
    let B₁ : Matrix n Unit ℂ := Matrix.of fun i _ => b₁ i
    let B₂ : Matrix p Unit ℂ := Matrix.of fun i _ => b₂ i
    let M := fromBlocks A₁ (fromCols B₁ 1) A₂ (fromCols B₂ 0)
    ∃ L : List (Matrix (n ⊕ p) (n ⊕ p) ℂ),
      (∀ E ∈ L, (∃ d : n ⊕ p → ℂ, (∀ i, d i ≠ 0) ∧ E = diagonal d) ∨
        ∃ t : TransvectionStruct (n ⊕ p) ℂ, E = t.toMatrix) ∧
      L.prod * M = fromBlocks 1 (fromCols (A₁⁻¹ * B₁) A₁⁻¹)
        0 (fromCols (B₂ - S * B₁) (-S)) := by
  intro S B₁ B₂ M
  let E := fromBlocks A₁⁻¹ (0 : Matrix n p ℂ) (-S) 1
  have hdet := (isUnit_iff_isUnit_det _).mp hA₁
  have hE : E.det ≠ 0 := by
    change (fromBlocks A₁⁻¹ (0 : Matrix n p ℂ) (-S) (1 : Matrix p p ℂ)).det ≠ 0
    rw [det_fromBlocks_zero₁₂, det_one, mul_one]
    exact (isUnit_nonsing_inv_det _ hdet).ne_zero
  obtain ⟨L, hL, hF⟩ := nonsingular_factors_for_rows E hE
  refine ⟨L, hF, ?_⟩
  have hS : S * A₁ = A₂ := by
    change (A₂ * A₁⁻¹) * A₁ = A₂
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  rw [hL]
  change fromBlocks A₁⁻¹ (0 : Matrix n p ℂ) (-S) 1 *
      fromBlocks A₁ (fromCols B₁ 1) A₂ (fromCols B₂ 0) = _
  rw [fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.zero_mul, Matrix.one_mul, add_zero, Matrix.neg_mul, hS, neg_add_cancel,
    nonsing_inv_mul _ hdet, mul_fromCols, Matrix.mul_one, neg_add_eq_sub, true_and]
  ext i (j | j) <;> simp [Matrix.sub_apply]

end AugmentedElimination

section MixedPrecisionRefinementExamples

open Filter FloatingPoint Matrix
open scoped Topology

variable {n : ℕ}

/-- A mixed-precision refinement run with a single working-precision LU
factorization shared by all correction solves. -/
structure MixedPrecisionRefinement (work residual : RoundingModel ℝ)
    (A L U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x : ℕ → Fin n → ℝ) where
  /-- Residual evaluation uses the higher precision. -/
  roundoff_le : residual.u ≤ work.u
  /-- The fixed factors are computed at working precision. -/
  factorization : RoundsLU work A L U
  /-- The back substitutions use nonzero pivots. -/
  pivot_ne_zero : ∀ i, U i i ≠ 0
  /-- The computed high-precision matrix-vector products. -/
  fitted : ℕ → Fin n → ℝ
  /-- The residuals before rounding to working precision. -/
  highResidual : ℕ → Fin n → ℝ
  /-- The residual right-hand sides used by the triangular solver. -/
  solveResidual : ℕ → Fin n → ℝ
  /-- The intermediate forward-substitution solutions. -/
  intermediate : ℕ → Fin n → ℝ
  /-- The working-precision corrections. -/
  correction : ℕ → Fin n → ℝ
  /-- The dot products in the residual are evaluated at the higher precision. -/
  fitted_rounds : ∀ k, RoundsMulVec residual A (x k) (fitted k)
  /-- The residual subtraction is evaluated at the higher precision. -/
  highResidual_rounds : ∀ k i, residual.Rounds (b i - fitted k i) (highResidual k i)
  /-- The triangular solver receives a working-precision right-hand side. -/
  solveResidual_rounds : ∀ k i, work.Rounds (highResidual k i) (solveResidual k i)
  /-- Every forward substitution uses the same lower factor. -/
  forward : ∀ k, RoundsForwardSubst work L (solveResidual k) (intermediate k)
  /-- Every backward substitution uses the same upper factor. -/
  backward : ∀ k, RoundsBackSubst work U (intermediate k) (correction k)
  /-- The correction is accumulated at working precision. -/
  update : ∀ k i, work.Rounds (x k i + correction k i) (x (k + 1) i)

variable {work residual : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ}
  {b : Fin n → ℝ} {x : ℕ → Fin n → ℝ}

/-- The printed stopping ratio is defined when the previous correction is nonzero. -/
def MixedPrecisionRefinement.stopsAt (r : MixedPrecisionRefinement work residual A L U b x)
    (τ : ℝ) (k : ℕ) : Prop :=
  r.correction k ≠ 0 ∧ ‖r.correction (k + 1)‖ / ‖r.correction k‖ < τ

/-- The new exact residual is the negative sum of the residual-evaluation
error, the correction-solve error, and the propagated update error. -/
theorem MixedPrecisionRefinement.residual_identity
    (r : MixedPrecisionRefinement work residual A L U b x) (k : ℕ) :
    b - A *ᵥ x (k + 1) =
      -(r.solveResidual k - (b - A *ᵥ x k)) - (A *ᵥ r.correction k - r.solveResidual k) -
        A *ᵥ (x (k + 1) - (x k + r.correction k)) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_add]
  abel

/-- **Exercise 6** of [benIsrael2003generalized], Chapter 3.
For a convergent mixed-precision run, vanishing net arithmetic defect
gives an exact solution at the limit. At any finite step the same identity
gives the exact residual from the three individual errors. -/
theorem exercise_3_6_finite_precision_refinement
    (r : MixedPrecisionRefinement work residual A L U b x)
    (limit : Fin n → ℝ) (hx : Tendsto x atTop (𝓝 limit))
    (hdefect : Tendsto (fun k =>
      (r.solveResidual k - (b - A *ᵥ x k)) + (A *ᵥ r.correction k - r.solveResidual k) +
        A *ᵥ (x (k + 1) - (x k + r.correction k))) atTop (𝓝 0)) :
    A *ᵥ limit = b := by
  let T := A.mulVecLin
  have hT : Continuous T := T.continuous_of_finiteDimensional
  have hx' : Tendsto (fun k : ℕ => x (k + 1)) atTop (𝓝 limit) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hlimit : Tendsto (fun k => b - A *ᵥ x (k + 1)) atTop (𝓝 (b - A *ᵥ limit)) :=
    tendsto_const_nhds.sub ((hT.tendsto limit).comp hx')
  have hzero : Tendsto (fun k => b - A *ᵥ x (k + 1)) atTop (𝓝 0) := by
    convert hdefect.neg using 1
    · funext k
      rw [r.residual_identity]
      abel
    · simp
  exact (sub_eq_zero.mp (tendsto_nhds_unique hlimit hzero)).symm

private def refinementWorkSystem : FloatingPoint.System :=
  ⟨2, 2, -10, 10, by decide, by decide, by decide⟩

private def refinementResidualSystem : FloatingPoint.System :=
  ⟨2, 4, -10, 10, by decide, by decide, by decide⟩

private theorem refinement_work_rounds :
    refinementWorkSystem.round (-(1 / 8 : ℝ)) = -1 / 8 ∧
      refinementWorkSystem.round (-(1 / 24 : ℝ)) = -3 / 64 ∧
      refinementWorkSystem.round (21 / 64 : ℝ) = 3 / 8 := by
  constructor
  · rw [refinementWorkSystem.round_neg,
      refinementWorkSystem.round_eq_of_le_of_lt (e := -2)
        (by norm_num [refinementWorkSystem]) (by norm_num [refinementWorkSystem])]
    norm_num [refinementWorkSystem, round_eq]
  constructor
  · rw [refinementWorkSystem.round_neg,
      refinementWorkSystem.round_eq_of_le_of_lt (e := -4)
        (by norm_num [refinementWorkSystem]) (by norm_num [refinementWorkSystem])]
    norm_num [refinementWorkSystem, round_eq]
  · rw [refinementWorkSystem.round_eq_of_le_of_lt (e := -1)
        (by norm_num [refinementWorkSystem]) (by norm_num [refinementWorkSystem])]
    norm_num [refinementWorkSystem, round_eq]

private theorem refinement_residual_rounds :
    refinementResidualSystem.round (9 / 8 : ℝ) = 9 / 8 ∧
      refinementResidualSystem.round (-(1 / 8 : ℝ)) = -1 / 8 := by
  constructor
  · rw [refinementResidualSystem.round_eq_of_le_of_lt (e := 1)
        (by norm_num [refinementResidualSystem]) (by norm_num [refinementResidualSystem])]
    norm_num [refinementResidualSystem, round_eq]
  · rw [refinementResidualSystem.round_neg,
      refinementResidualSystem.round_eq_of_le_of_lt (e := -2)
        (by norm_num [refinementResidualSystem]) (by norm_num [refinementResidualSystem])]
    norm_num [refinementResidualSystem, round_eq]

/-- The finite-precision refinement of (3/8) for the scalar equation
(3x = 1) can stagnate, even when the residual is computed exactly. -/
theorem exercise_3_6_refinement_stagnation :
    let A : Matrix (Fin 1) (Fin 1) ℝ := of fun _ _ => 3
    let b : Fin 1 → ℝ := fun _ => 1
    let x : ℕ → Fin 1 → ℝ := fun _ _ => 3 / 8
    Nonempty (MixedPrecisionRefinement (refinementWorkSystem.roundingModel ℝ)
        (refinementResidualSystem.roundingModel ℝ) A 1 A b x) ∧
      Tendsto x atTop (𝓝 (x 0)) ∧ A *ᵥ x 0 ≠ b := by
  intro A b x
  have hw := refinement_work_rounds
  have hr := refinement_residual_rounds
  let work := refinementWorkSystem.roundingModel ℝ
  let high := refinementResidualSystem.roundingModel ℝ
  refine ⟨⟨{
    roundoff_le := by
      norm_num [work, high, FloatingPoint.System.unitRoundoff, refinementWorkSystem,
        refinementResidualSystem]
    factorization := {
      lower_apply_eq_zero := fun i j hij => False.elim (hij.ne (Subsingleton.elim i j))
      lower_diag := fun i => Matrix.one_apply_eq i
      upper_apply_eq_zero := fun i j hij => False.elim (hij.ne (Subsingleton.elim j i))
      upper := by
        intro i j _
        refine ⟨[], List.nodup_nil, fun k => ?_, ⟨0, by simp, RoundsSumFrom.nil _⟩⟩
        simp [Subsingleton.elim k i]
      lower := fun i j hij => False.elim (hij.ne (Subsingleton.elim j i))
    }
    pivot_ne_zero := by intro i; norm_num [A]
    fitted := fun _ _ => 9 / 8
    highResidual := fun _ _ => -1 / 8
    solveResidual := fun _ _ => -1 / 8
    intermediate := fun _ _ => -1 / 8
    correction := fun _ _ => -3 / 64
    fitted_rounds := by
      intro k i
      refine ⟨[0], fun _ => 9 / 8, by simp, fun j => ?_, fun j => ?_, ?_⟩
      · rw [Subsingleton.elim j 0]
        simp
      · change (9 / 8 : ℝ) = refinementResidualSystem.round (3 * (3 / 8 : ℝ))
        norm_num [hr.1]
      · exact RoundsSumFrom.nil _
    highResidual_rounds := by
      intro k i
      change (-1 / 8 : ℝ) = refinementResidualSystem.round (1 - (9 / 8 : ℝ))
      norm_num [hr.2]
    solveResidual_rounds := by
      intro k i
      change (-1 / 8 : ℝ) = refinementWorkSystem.round (-1 / 8 : ℝ)
      simpa only [neg_div] using hw.1.symm
    forward := by
      intro k i
      refine ⟨[], -1 / 8, List.nodup_nil, fun j => ?_, ⟨0, by simp, RoundsSumFrom.nil _⟩, ?_⟩
      · simp [Subsingleton.elim j i]
      · simpa only [Matrix.one_apply_eq, div_one, work,
          FloatingPoint.System.roundingModel_rounds_iff, neg_div] using hw.1.symm
    backward := by
      intro k i
      refine ⟨[], -1 / 8, List.nodup_nil, fun j => ?_, ⟨0, by simp, RoundsSumFrom.nil _⟩, ?_⟩
      · simp [Subsingleton.elim j i]
      · change (-3 / 64 : ℝ) = refinementWorkSystem.round ((-1 / 8) / 3 : ℝ)
        norm_num [hw.2.1]
    update := by
      intro k i
      change (3 / 8 : ℝ) = refinementWorkSystem.round (3 / 8 + -3 / 64)
      norm_num [hw.2.2]
  }⟩, tendsto_const_nhds, ?_⟩
  intro he
  have h := congrFun he (0 : Fin 1)
  norm_num [A, b, x, Matrix.mulVec, dotProduct] at h

end MixedPrecisionRefinementExamples

end BenIsraelGreville.Chapter03
