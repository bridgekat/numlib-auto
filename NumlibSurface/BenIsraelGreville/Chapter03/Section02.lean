/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter03.Section01

/-!
# Solutions of minimum norm

Section 3.2 of [benIsrael2003generalized] characterizes $\{1,4\}$-inverses by their action
on consistent right-hand sides. It also characterizes the Moore–Penrose inverse by the
minimum-norm property among least-squares solutions.
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open BenIsraelGreville.Chapter01 (definition_1 mem_one_four_iff)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {A : Matrix m n ℂ}

/-- A minimum-norm solution of $Ax=b$ is an exact solution whose norm is at most the norm
of every exact solution. -/
def IsMinNormSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    Prop :=
  toEuclideanLin A x = b ∧ ∀ y, toEuclideanLin A y = b → ‖x‖ ≤ ‖y‖

private theorem pinv_solves_of_mem_range {b : EuclideanSpace ℂ m}
    (hb : b ∈ LinearMap.range (toEuclideanLin A)) :
    toEuclideanLin A (toEuclideanLin A.pinv b) = b := by
  obtain ⟨z, rfl⟩ := hb
  change toEuclideanLin A (toEuclideanLin A.pinv (toEuclideanLin A z)) = toEuclideanLin A z
  rw [← toEuclideanLin_mul_apply A.pinv A, ← toEuclideanLin_mul_apply,
    ← Matrix.mul_assoc, mul_pinv_mul_self]

private theorem pinv_mem_adjoint_range (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    toEuclideanLin A.pinv b ∈ LinearMap.range (toEuclideanLin Aᴴ) := by
  have h : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv b) =
      toEuclideanLin A.pinv b := by
    rw [← toEuclideanLin_mul_apply, pinv_mul_self_mul_pinv]
  rw [← h, pinv_mul_eq_starProjection]
  exact Submodule.starProjection_apply_mem _ _

omit [DecidableEq m] in
private theorem minNormSolution_iff_minNormLeastSquares {b : EuclideanSpace ℂ m}
    {x : EuclideanSpace ℂ n} (hb : b ∈ LinearMap.range (toEuclideanLin A)) :
    IsMinNormSolution A b x ↔ IsMinNormLeastSquaresSolution A b x := by
  classical
  have hEquiv (y : EuclideanSpace ℂ n) :
      leastSquaresSolution A b y ↔ toEuclideanLin A y = b := by
    rw [leastSquaresSolution_iff_image_eq, pinv_solves_of_mem_range hb]
  refine ⟨fun hx => ⟨(hEquiv x).mpr hx.1, fun y hy => hx.2 y ((hEquiv y).mp hy)⟩, ?_⟩
  exact fun hx => ⟨(hEquiv x).mp hx.1, fun y hy => hx.2 y ((hEquiv y).mpr hy)⟩

/-- **Lemma 1** of [benIsrael2003generalized], Chapter 3. The restriction of $A$ to the range
of $A^H$ is a bijection onto the range of $A$. -/
theorem lemma_1 (A : Matrix m n ℂ) :
    Set.BijOn (toEuclideanLin A) (LinearMap.range (toEuclideanLin Aᴴ))
      (LinearMap.range (toEuclideanLin A)) := by
  have hleft (x : EuclideanSpace ℂ n) (hx : x ∈ LinearMap.range (toEuclideanLin Aᴴ)) :
      toEuclideanLin A.pinv (toEuclideanLin A x) = x := by
    obtain ⟨w, rfl⟩ := hx
    rw [← toEuclideanLin_mul_apply A.pinv A, ← toEuclideanLin_mul_apply,
      pinv_mul_self_mul_conjTranspose]
  refine ⟨fun x _ => LinearMap.mem_range_self _ x, ?_, ?_⟩
  · intro x hx y hy h
    rw [← hleft x hx, ← hleft y hy, h]
  · intro b hb
    exact ⟨toEuclideanLin A.pinv b, pinv_mem_adjoint_range A b, pinv_solves_of_mem_range hb⟩

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 3. For a consistent right-hand
side $b$, the unique exact solution in the range of $A^H$ is the unique minimum-norm solution. -/
theorem corollary_2 {b : EuclideanSpace ℂ m} (hb : b ∈ LinearMap.range (toEuclideanLin A)) :
    ∃ x, (toEuclideanLin A x = b ∧ x ∈ LinearMap.range (toEuclideanLin Aᴴ)) ∧
      IsMinNormSolution A b x ∧
      (∀ y, toEuclideanLin A y = b → y ∈ LinearMap.range (toEuclideanLin Aᴴ) → y = x) ∧
      (∀ y, IsMinNormSolution A b y → y = x) := by
  refine ⟨toEuclideanLin A.pinv b, ⟨pinv_solves_of_mem_range hb, pinv_mem_adjoint_range A b⟩,
    (minNormSolution_iff_minNormLeastSquares hb).mpr (isMinNormLeastSquaresSolution_pinv A b),
    ?_, ?_⟩
  · exact fun y hy hmem => (lemma_1 A).2.1 hmem (pinv_mem_adjoint_range A b)
      (hy.trans (pinv_solves_of_mem_range hb).symm)
  · exact fun y hy => ((minNormSolution_iff_minNormLeastSquares hb).mp hy).eq_pinv

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 3. A matrix $X$ is a
$\{1,4\}$-inverse exactly when it maps every consistent right-hand side to the minimum-norm
exact solution. -/
theorem theorem_2 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    X ∈ definition_1 A {.inner, .hermitianMulRev} ↔
      ∀ b ∈ LinearMap.range (toEuclideanLin A), IsMinNormSolution A b (toEuclideanLin X b) := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMulRev} :=
    mem_one_four_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_pinv_mul⟩
  rw [Chapter02.theorem_4 hp]
  constructor
  · intro h b hb
    have heq : toEuclideanLin X b = toEuclideanLin A.pinv b := by
      obtain ⟨z, rfl⟩ := hb
      change toEuclideanLin X (toEuclideanLin A z) = toEuclideanLin A.pinv (toEuclideanLin A z)
      rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, h]
    rw [heq]
    exact (minNormSolution_iff_minNormLeastSquares hb).mpr (isMinNormLeastSquaresSolution_pinv A b)
  · intro h
    apply toEuclideanLin.injective
    ext z : 1
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    exact ((minNormSolution_iff_minNormLeastSquares (LinearMap.mem_range_self _ z)).mp
      (h _ (LinearMap.mem_range_self _ z))).eq_pinv

/-- **Corollary 3** of [benIsrael2003generalized], Chapter 3. A matrix maps every
right-hand side to a minimum-norm least-squares solution exactly when it is the
Moore–Penrose inverse. Each minimum-norm least-squares solution is unique. -/
theorem corollary_3 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    (∀ b, IsMinNormLeastSquaresSolution A b (toEuclideanLin X b)) ↔ X = A.pinv := by
  refine ⟨fun h => toEuclideanLin.injective (LinearMap.ext fun b => (h b).eq_pinv), ?_⟩
  rintro rfl b
  exact isMinNormLeastSquaresSolution_pinv A b

end BenIsraelGreville.Chapter03
