/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

end BenIsraelGreville.Chapter03
