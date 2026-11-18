/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter03.Section01
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter02.Section01
import NumlibSurface.BenIsraelGreville.Chapter02.Section09
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import Numlib.LinearAlgebra.Matrix.Kronecker
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Solutions of minimum norm

Section 3.2 of [benIsrael2003generalized] characterizes $\{1,4\}$-inverses by their action
on consistent right-hand sides. It also characterizes the Moore–Penrose inverse by the
minimum-norm property among least-squares solutions.
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open scoped InnerProductSpace
open BenIsraelGreville.Chapter01 (definition_1 mem_one_four_iff mem_one_three_iff)

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

noncomputable section HermiteWorkedExample

private def hermiteLeastSquaresDatum : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![-Complex.I, 1, 1]

private def hermiteLeastSquaresParticular : EuclideanSpace ℂ (Fin 6) :=
  WithLp.toLp 2 ![0, 1 / 19, 0, -4 / 19, 0, 0]

private def hermiteLeastSquaresFit : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![2 * Complex.I / 19, 12 / 19, -2 / 19]

private def hermiteLeastSquaresKernelMap : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, 0, 0, 0, 0, 0;
    0, 0, -1 / 2, 0, -1 + 2 * Complex.I, Complex.I / 2;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, -2, -1 - Complex.I;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

private theorem hermiteLeastSquares_normal :
    toEuclideanLin Chapter00.hermiteExampleMatrixᴴ hermiteLeastSquaresFit =
      toEuclideanLin Chapter00.hermiteExampleMatrixᴴ hermiteLeastSquaresDatum := by
  ext j
  fin_cases j <;>
    norm_num [hermiteLeastSquaresFit, hermiteLeastSquaresDatum, Chapter00.hermiteExampleMatrix,
      toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.I_mul_I] <;>
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

private theorem hermiteLeastSquaresParticular_fit :
    toEuclideanLin Chapter00.hermiteExampleMatrix hermiteLeastSquaresParticular =
      hermiteLeastSquaresFit := by
  ext j
  fin_cases j <;>
    norm_num [hermiteLeastSquaresFit, hermiteLeastSquaresParticular, Chapter00.hermiteExampleMatrix,
      toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 3.
The displayed affine family is the full solution set. The vector called
the residual in the text is the fitted vector, whose difference from
the datum gives the actual residual. -/
theorem exercise_3_12 (x : EuclideanSpace ℂ (Fin 6)) :
    let A := Chapter00.hermiteExampleMatrix
    let b := hermiteLeastSquaresDatum
    (leastSquaresSolution A b x ↔ ∃ y : EuclideanSpace ℂ (Fin 6),
      x = hermiteLeastSquaresParticular + toEuclideanLin hermiteLeastSquaresKernelMap y) ∧
    (leastSquaresSolution A b x → toEuclideanLin A x = hermiteLeastSquaresFit ∧
      b - toEuclideanLin A x = WithLp.toLp 2 ![-21 * Complex.I / 19, 7 / 19, 21 / 19]) := by
  let A := Chapter00.hermiteExampleMatrix
  let b := hermiteLeastSquaresDatum
  let q := hermiteLeastSquaresParticular
  let U : Matrix (Fin 6) (Fin 3) ℂ :=
    !![0, 0, 0; -Complex.I / 2, 0, 0; 0, 0, 0; 0, -1 / 3, 0; 0, 0, 0; 0, 0, 0]
  have hU : A.IsInnerInverse U := by
    apply isInnerInverse_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [A, U, Chapter00.hermiteExampleMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hP : 1 - U * A = hermiteLeastSquaresKernelMap := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, U, hermiteLeastSquaresKernelMap, Chapter00.hermiteExampleMatrix,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I] <;>
      apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hq : toEuclideanLin U (toEuclideanLin A q) = q := by
    rw [hermiteLeastSquaresParticular_fit]
    ext i
    fin_cases i <;>
      norm_num [q, U, hermiteLeastSquaresFit, hermiteLeastSquaresParticular, toEuclideanLin_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.I_mul_I];
      apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hlsq : leastSquaresSolution A b q := by
    rw [exercise_3_1, toEuclideanLin_mul_apply, hermiteLeastSquaresParticular_fit]
    exact hermiteLeastSquares_normal
  have he : leastSquaresSolution A b x ↔ toEuclideanLin A x = toEuclideanLin A q := by
    rw [leastSquaresSolution_iff_image_eq,
      leastSquaresSolution_iff_image_eq.mp hlsq]
  refine ⟨he.trans ?_, fun hx => ?_⟩
  · rw [exactSolution_iff_innerParameter hU (LinearMap.mem_range_self _ q) x, hq, hP]
  · have hfit : toEuclideanLin A x = hermiteLeastSquaresFit :=
      (he.mp hx).trans hermiteLeastSquaresParticular_fit
    refine ⟨hfit, ?_⟩
    rw [hfit]
    ext i
    fin_cases i <;>
      norm_num [b, hermiteLeastSquaresDatum, hermiteLeastSquaresFit]; ring

private def hermiteLeastSquaresReciprocalValue : EuclideanSpace ℂ (Fin 6) :=
  WithLp.toLp 2 ![0, (26 - 36 * Complex.I) / 874, (13 - 18 * Complex.I) / 874,
    (-55 - 9 * Complex.I) / 874, (-12 - 2 * Complex.I) / 874, (-46 + 59 * Complex.I) / 874]

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 3.
The printed vector is the minimum-norm least-squares solution. -/
theorem exercise_3_13 :
    toEuclideanLin Chapter00.hermiteExampleMatrix.pinv hermiteLeastSquaresDatum =
      hermiteLeastSquaresReciprocalValue := by
  let A := Chapter00.hermiteExampleMatrix
  let x := hermiteLeastSquaresReciprocalValue
  let b := hermiteLeastSquaresDatum
  have hfit : toEuclideanLin A x = hermiteLeastSquaresFit := by
    ext i
    fin_cases i <;>
      norm_num [A, x, Chapter00.hermiteExampleMatrix, hermiteLeastSquaresFit,
        hermiteLeastSquaresReciprocalValue, toEuclideanLin_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;>
      apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hls : leastSquaresSolution A b x := by
    rw [exercise_3_1, toEuclideanLin_mul_apply, hfit]
    exact hermiteLeastSquares_normal
  let y : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![
    (18 + 13 * Complex.I) / 874, (55 + 9 * Complex.I) / 2622, 0]
  have hr : toEuclideanLin Aᴴ y = x := by
    ext i
    fin_cases i <;>
      norm_num [A, x, y, Chapter00.hermiteExampleMatrix, hermiteLeastSquaresReciprocalValue,
        toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ, Complex.I_mul_I] <;>
      apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hx : toEuclideanLin A.pinv (toEuclideanLin A x) = x := by
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr ⟨y, hr⟩
  rw [leastSquaresSolution_iff_image_eq.mp hls, ← toEuclideanLin_mul_apply,
    ← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv] at hx
  exact hx

end HermiteWorkedExample

/-- **Exercise 14** of [benIsrael2003generalized], Chapter 3.
The unique solution nearest a reference vector is its kernel component
added to the minimum-norm solution of the original system. -/
theorem exercise_3_14 (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (hX : X ∈ definition_1 A {.inner, .hermitianMulRev})
    (a : EuclideanSpace ℂ n) {b : EuclideanSpace ℂ m}
    (hb : b ∈ LinearMap.range (toEuclideanLin A)) (x : EuclideanSpace ℂ n) :
    (toEuclideanLin A x = b ∧ ∀ y, toEuclideanLin A y = b → ‖x - a‖ ≤ ‖y - a‖) ↔
      x = toEuclideanLin X b + toEuclideanLin (1 - X * A) a := by
  let c := b - toEuclideanLin A a
  have hc : c ∈ LinearMap.range (toEuclideanLin A) :=
    Submodule.sub_mem _ hb (LinearMap.mem_range_self _ a)
  have hmin := (theorem_2 A X).mp hX c hc
  have hshift : (toEuclideanLin A x = b ∧ ∀ y, toEuclideanLin A y = b →
      ‖x - a‖ ≤ ‖y - a‖) ↔ IsMinNormSolution A c (x - a) := by
    constructor
    · rintro ⟨hx, hx'⟩
      refine ⟨by rw [map_sub, hx], fun y hy => ?_⟩
      have hy' : toEuclideanLin A (y + a) = b := by rw [map_add, hy, sub_add_cancel]
      simpa only [add_sub_cancel_right] using hx' (y + a) hy'
    · rintro ⟨hx, hx'⟩
      rw [map_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff] at hx
      refine ⟨hx, fun y hy => hx' (y - a) ?_⟩
      rw [map_sub, hy]
  have he : toEuclideanLin X b + toEuclideanLin (1 - X * A) a =
      toEuclideanLin X c + a := by
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]
    simp only [c, map_sub]
    abel
  rw [hshift, he]
  constructor
  · intro h
    have hh := ((minNormSolution_iff_minNormLeastSquares hc).mp h).eq_pinv
    have hh' := ((minNormSolution_iff_minNormLeastSquares hc).mp hmin).eq_pinv
    exact sub_eq_iff_eq_add.mp (hh.trans hh'.symm)
  · rintro rfl
    simpa only [add_sub_cancel_right] using hmin

section Restricted

open BenIsraelGreville.Chapter02 (orthogonalProjector toEuclideanLin_orthogonalProjector)

/-- Least squares limited to the subspace S. -/
def IsRestrictedLeastSquaresSolution (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

/-- Smallest Euclidean norm among all restricted exact solutions. -/
def IsRestrictedMinNormSolution (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  x ∈ S ∧ toEuclideanLin A x = b ∧
    ∀ y ∈ S, toEuclideanLin A y = b → ‖x‖ ≤ ‖y‖

/-- Smallest Euclidean norm among all restricted least-squares solutions. -/
def IsRestrictedMinNormLeastSquaresSolution (A : Matrix m n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n))
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  IsRestrictedLeastSquaresSolution A S b x ∧
    ∀ y, IsRestrictedLeastSquaresSolution A S b y → ‖x‖ ≤ ‖y‖

omit [DecidableEq m] in
private theorem projected_ls_iff (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsRestrictedLeastSquaresSolution A S b (S.starProjection x) ↔
      leastSquaresSolution (A * orthogonalProjector S) b x := by
  have hP (y : EuclideanSpace ℂ n) :
      toEuclideanLin (A * orthogonalProjector S) y = toEuclideanLin A (S.starProjection y) := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
    rfl
  constructor
  · intro hx y
    rw [hP, hP]
    exact hx.2 _ (S.starProjection_apply_mem y)
  · intro hx
    refine ⟨S.starProjection_apply_mem x, fun y hy => ?_⟩
    have h := hx y
    change ‖toEuclideanLin (A * orthogonalProjector S) x - b‖ ≤
      ‖toEuclideanLin (A * orthogonalProjector S) y - b‖ at h
    rwa [hP, hP, S.starProjection_eq_self_iff.mpr hy] at h

private theorem matrix_projected_eq_of_range_le (S : Submodule ℂ (EuclideanSpace ℂ n))
    (X : Matrix n m ℂ) (hX : ∀ b, toEuclideanLin X b ∈ S) :
    orthogonalProjector S * X = X := by
  apply toEuclideanLin.injective
  ext1 b
  rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
  exact S.starProjection_eq_self_iff.mpr (hX b)

/-- **Exercise 20** of [benIsrael2003generalized], Chapter 3.
Restricted least-squares solution maps are the restricted first and third
Penrose inverses. -/
theorem exercise_3_20 (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (X : Matrix n m ℂ) :
    (∀ b, IsRestrictedLeastSquaresSolution A S b (toEuclideanLin X b)) ↔
      Chapter02.definition_2 A S {.inner, .hermitianMul} X := by
  constructor
  · intro hX
    have hR := matrix_projected_eq_of_range_le S X (fun b => (hX b).1)
    refine ⟨X, (theorem_1 (A * orthogonalProjector S) X).mpr (fun b => ?_), hR.symm⟩
    apply (projected_ls_iff A S b _).mp
    rw [S.starProjection_eq_self_iff.mpr (hX b).1]
    exact hX b
  · rintro ⟨Y, hY, rfl⟩ b
    rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
    exact (projected_ls_iff A S b _).mpr ((theorem_1 _ _).mp hY b)

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 3.
A map into S returns the minimum-norm restricted exact solution on every
compatible datum precisely when it is a restricted first and fourth
Penrose inverse. -/
theorem exercise_3_21 (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (X : Matrix n m ℂ) :
    ((∀ b, toEuclideanLin X b ∈ S) ∧
      ∀ b ∈ LinearMap.range (toEuclideanLin (A * orthogonalProjector S)),
        IsRestrictedMinNormSolution A S b (toEuclideanLin X b)) ↔
      Chapter02.definition_2 A S {.inner, .hermitianMulRev} X := by
  have hP (x : EuclideanSpace ℂ n) :
      toEuclideanLin (A * orthogonalProjector S) x = toEuclideanLin A (S.starProjection x) := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
    rfl
  constructor
  · rintro ⟨hR, hX⟩
    have hPX := matrix_projected_eq_of_range_le S X hR
    refine ⟨X, (theorem_2 _ _).mpr (fun b hb => ?_), hPX.symm⟩
    obtain ⟨_, hF, hN⟩ := hX b hb
    refine ⟨by rw [hP, S.starProjection_eq_self_iff.mpr (hR b), hF], fun y hy => ?_⟩
    exact (hN _ (S.starProjection_apply_mem y) ((hP y).symm.trans hy)).trans
      (S.norm_starProjection_apply_le y)
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨fun b => ?_, fun b hb => ?_⟩
    · rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
      exact S.starProjection_apply_mem _
    · have hmin := (theorem_2 _ _).mp hY b hb
      rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
      refine ⟨S.starProjection_apply_mem _, (hP _).symm.trans hmin.1, fun y hy hya => ?_⟩
      refine (S.norm_starProjection_apply_le _).trans (hmin.2 y ?_)
      rwa [hP, S.starProjection_eq_self_iff.mpr hy]

/-- The restricted minimum-norm least-squares solution is the projected
reciprocal solution of the extended restricted matrix. -/
theorem restrictedMinNormLeastSquaresSolution_iff (A : Matrix m n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsRestrictedMinNormLeastSquaresSolution A S b x ↔
      x = toEuclideanLin (orthogonalProjector S * (A * orthogonalProjector S).pinv) b := by
  let C := A * orthogonalProjector S
  let z := toEuclideanLin C.pinv b
  have hz : z ∈ S := by
    obtain ⟨y, hy⟩ := pinv_mem_adjoint_range C b
    have hC : Cᴴ = orthogonalProjector S * Aᴴ := by
      dsimp only [C]
      rw [conjTranspose_mul, (Chapter02.isHermitian_orthogonalProjector S).eq]
    change toEuclideanLin C.pinv b ∈ S
    rw [← hy, hC, toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
    exact S.starProjection_apply_mem _
  rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
  change IsRestrictedMinNormLeastSquaresSolution A S b x ↔ x = S.starProjection z
  rw [S.starProjection_eq_self_iff.mpr hz]
  constructor
  · intro h
    have hx : S.starProjection x = x := S.starProjection_eq_self_iff.mpr h.1.1
    have hm : IsMinNormLeastSquaresSolution C b x := by
      refine ⟨(projected_ls_iff A S b x).mp (hx.symm ▸ h.1), fun y hy => ?_⟩
      exact (h.2 _ ((projected_ls_iff A S b y).mpr hy)).trans (S.norm_starProjection_apply_le y)
    exact hm.eq_pinv
  · rintro rfl
    have hmin := isMinNormLeastSquaresSolution_pinv C b
    have hfix := S.starProjection_eq_self_iff.mpr hz
    refine ⟨hfix ▸ (projected_ls_iff A S b _).mpr hmin.1, fun y hy => ?_⟩
    have hyfix := S.starProjection_eq_self_iff.mpr hy.1
    exact hmin.2 y ((projected_ls_iff A S b y).mp (hyfix.symm ▸ hy))

/-- **Exercise 22** of [benIsrael2003generalized], Chapter 3.
The unique restricted solution map of least norm is the restriction
projector times the reciprocal of the extended restricted matrix. -/
theorem exercise_3_22 (A : Matrix m n ℂ) (S : Submodule ℂ (EuclideanSpace ℂ n))
    (X : Matrix n m ℂ) :
    (∀ b, IsRestrictedMinNormLeastSquaresSolution A S b (toEuclideanLin X b)) ↔
      X = orthogonalProjector S * (A * orthogonalProjector S).pinv := by
  constructor
  · intro h
    apply toEuclideanLin.injective
    ext1 b
    exact (restrictedMinNormLeastSquaresSolution_iff A S b _).mp (h b)
  · rintro rfl b
    exact (restrictedMinNormLeastSquaresSolution_iff A S b _).mpr rfl

/-- **Exercise 23**, Equation (32), of [benIsrael2003generalized], Chapter 3.
The least-norm constrained minimizer is the least-norm feasible point
plus the least-norm correction in the kernel of the constraint matrix. -/
theorem exercise_3_23 {p : Type*} [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ) (b : EuclideanSpace ℂ m)
    {d : EuclideanSpace ℂ p} (hd : d ∈ LinearMap.range (toEuclideanLin B)) (x : EuclideanSpace ℂ n) :
    let z := toEuclideanLin B.pinv d
    let P := orthogonalProjector (toEuclideanLin B).ker
    (IsConstrainedLeastSquaresSolution A B b d x ∧
      ∀ y, IsConstrainedLeastSquaresSolution A B b d y → ‖x‖ ≤ ‖y‖) ↔
      x = z + toEuclideanLin (P * (A * P).pinv) (b - toEuclideanLin A z) := by
  let z := toEuclideanLin B.pinv d
  let K := (toEuclideanLin B).ker
  let e := b - toEuclideanLin A z
  have hz : toEuclideanLin B z = d := pinv_solves_of_mem_range hd
  have hzK : z ∈ Kᗮ := by
    rw [show Kᗮ = LinearMap.range (toEuclideanLin Bᴴ) by
      rw [toEuclideanLin_conjTranspose_eq_adjoint]
      exact (toEuclideanLin B).orthogonal_ker]
    exact pinv_mem_adjoint_range B d
  have hres (y : EuclideanSpace ℂ n) :
      toEuclideanLin A (z + y) - b = toEuclideanLin A y - e := by
    rw [map_add]
    dsimp only [e]
    abel
  have hfeas (y : EuclideanSpace ℂ n) :
      toEuclideanLin B (z + y) = d ↔ y ∈ K := by
    rw [map_add, hz]
    change d + toEuclideanLin B y = d ↔ toEuclideanLin B y = 0
    constructor
    · intro h
      exact add_left_cancel (h.trans (add_zero _).symm)
    · intro h
      rw [h, add_zero]
  have hLS (y : EuclideanSpace ℂ n) :
      IsConstrainedLeastSquaresSolution A B b d (z + y) ↔
        IsRestrictedLeastSquaresSolution A K e y := by
    rw [IsConstrainedLeastSquaresSolution, IsRestrictedLeastSquaresSolution, hfeas, hres]
    apply and_congr_right
    intro hy
    constructor
    · intro h w hw
      have he := h (z + w) ((hfeas w).mpr hw)
      rwa [hres] at he
    · intro h w hw
      have he : w = z + (w - z) := by abel
      rw [he] at hw ⊢
      rw [hres]
      exact h (w - z) ((hfeas _).mp hw)
  have hnorm (y : EuclideanSpace ℂ n) (hy : y ∈ K) :
      ‖z + y‖ ^ 2 = ‖z‖ ^ 2 + ‖y‖ ^ 2 := by
    have ho : inner ℂ y z = 0 := hzK y hy
    have hzo : inner ℂ z y = 0 := by rw [← inner_conj_symm, ho, map_zero]
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero z y hzo
  have hCompare (y w : EuclideanSpace ℂ n) (hy : y ∈ K) (hw : w ∈ K) :
      ‖z + y‖ ≤ ‖z + w‖ ↔ ‖y‖ ≤ ‖w‖ := by
    rw [← sq_le_sq₀ (norm_nonneg (z + y)) (norm_nonneg (z + w)),
      hnorm y hy, hnorm w hw, add_le_add_iff_left, sq_le_sq₀ (norm_nonneg y) (norm_nonneg w)]
  have hMin (y : EuclideanSpace ℂ n) :
      (IsConstrainedLeastSquaresSolution A B b d (z + y) ∧
        ∀ w, IsConstrainedLeastSquaresSolution A B b d w → ‖z + y‖ ≤ ‖w‖) ↔
        IsRestrictedMinNormLeastSquaresSolution A K e y := by
    rw [IsRestrictedMinNormLeastSquaresSolution, hLS]
    apply and_congr_right
    intro hy
    constructor
    · intro h w hw
      exact (hCompare y w hy.1 hw.1).mp (h _ ((hLS w).mpr hw))
    · intro h w hw
      have he : w = z + (w - z) := by abel
      rw [he] at hw ⊢
      have hw' := (hLS (w - z)).mp hw
      exact (hCompare y (w - z) hy.1 hw'.1).mpr (h _ hw')
  have hx : z + (x - z) = x := by abel
  have h := (hMin (x - z)).trans (restrictedMinNormLeastSquaresSolution_iff A K e (x - z))
  rw [hx, sub_eq_iff_eq_add, add_comm _ z] at h
  exact h

/-- **Exercise 24**, Equation (33), of [benIsrael2003generalized], Chapter 3.
For an invertible Hermitian left weight, the pseudoinverse is obtained by
removing the orthogonal projection onto the weighted kernel. The projection
uses the range of VP, so its factors occur as (VP)(VP)†. -/
theorem exercise_3_24 {p : Type*} [Fintype p] [DecidableEq p]
    (V : Matrix n n ℂ) (hV : V.IsHermitian) (hVu : IsUnit V) (X : Matrix n p ℂ) :
    let P := orthogonalProjector (toEuclideanLin Xᴴ).ker
    (V⁻¹ * X).pinv = X.pinv * V * (1 - (V * P) * (V * P).pinv) := by
  let P := orthogonalProjector (toEuclideanLin Xᴴ).ker
  let T := V⁻¹ * X
  let W := V * P
  let Z := X.pinv * V * (1 - W * W.pinv)
  have hd := (isUnit_iff_isUnit_det V).mp hVu
  have hTH : Tᴴ = Xᴴ * V⁻¹ := by
    dsimp only [T]
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hV.eq]
  have hVleft (y : EuclideanSpace ℂ n) :
      toEuclideanLin V⁻¹ (toEuclideanLin V y) = y := by
    rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul _ hd, toEuclideanLin_one_apply]
  have hVright (y : EuclideanSpace ℂ n) :
      toEuclideanLin V (toEuclideanLin V⁻¹ y) = y := by
    rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv _ hd, toEuclideanLin_one_apply]
  have hR : LinearMap.range (toEuclideanLin W) = (toEuclideanLin Tᴴ).ker := by
    ext y
    rw [LinearMap.mem_ker, hTH, toEuclideanLin_mul_apply]
    constructor
    · rintro ⟨z, rfl⟩
      change toEuclideanLin Xᴴ (toEuclideanLin V⁻¹ (toEuclideanLin (V * P) z)) = 0
      rw [toEuclideanLin_mul_apply, hVleft, toEuclideanLin_orthogonalProjector]
      exact (toEuclideanLin Xᴴ).ker.starProjection_apply_mem z
    · intro hy
      let z := toEuclideanLin V⁻¹ y
      have hz : toEuclideanLin P z = z := by
        rw [toEuclideanLin_orthogonalProjector]
        exact (LinearMap.ker (toEuclideanLin Xᴴ)).starProjection_eq_self_iff.mpr hy
      refine ⟨z, ?_⟩
      change toEuclideanLin (V * P) z = y
      rw [toEuclideanLin_mul_apply, hz, hVright]
  let L := LinearMap.range (toEuclideanLin W)
  have hL : Lᗮ = LinearMap.range (toEuclideanLin T) := by
    change (LinearMap.range (toEuclideanLin W))ᗮ = _
    rw [hR, LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_conjTranspose]
  have hProj : 1 - W * W.pinv = T * T.pinv := by
    apply toEuclideanLin.injective
    ext1 y
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, W.mul_pinv_eq_starProjection,
      T.mul_pinv_eq_starProjection]
    change y - L.starProjection y = (LinearMap.range (toEuclideanLin T)).starProjection y
    symm
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · rw [← hL]
      exact L.sub_starProjection_mem_orthogonal y
    · rw [← hL, Submodule.orthogonal_orthogonal, sub_sub_cancel]
      exact L.starProjection_apply_mem y
  have hZT : (X.pinv * V) * T = X.pinv * X := by
    dsimp only [T]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V V⁻¹ X, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hZTr : Z * T = X.pinv * X := by
    rw [show Z = (X.pinv * V) * (1 - W * W.pinv) from rfl,
      hProj, Matrix.mul_assoc, T.mul_pinv_mul_self, hZT]
  have hTZ : T * Z = T * T.pinv := calc
    _ = (T * ((X.pinv * V) * T)) * T.pinv := by
      rw [show Z = (X.pinv * V) * (1 - W * W.pinv) from rfl, hProj]
      simp only [Matrix.mul_assoc]
    _ = (T * (X.pinv * X)) * T.pinv := by rw [hZT]
    _ = T * T.pinv := by
      have he : T * (X.pinv * X) = T := calc
        _ = V⁻¹ * (X * X.pinv * X) := by simp only [T, Matrix.mul_assoc]
        _ = T := by rw [X.mul_pinv_mul_self]
      rw [he]
  change T.pinv = Z
  symm
  apply T.pinv_unique
  · rw [hTZ, T.mul_pinv_mul_self]
  · rw [hZTr]
    calc
      _ = (X.pinv * X * X.pinv) * V * (1 - W * W.pinv) := by simp only [Z, Matrix.mul_assoc]
      _ = Z := by rw [X.pinv_mul_self_mul_pinv]
  · rw [hTZ]
    exact T.isHermitian_mul_pinv
  · rw [hZTr]
    exact X.isHermitian_pinv_mul


end Restricted

section MatrixEquations

open scoped Kronecker Matrix.Norms.Frobenius

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- Equation (26) of [benIsrael2003generalized], Chapter 3.
Column stacking identifies the matrix's Frobenius norm with a Euclidean norm. -/
def matrixEuclideanVec {a b : Type*} (X : Matrix a b ℂ) : EuclideanSpace ℂ (b × a) :=
  WithLp.toLp 2 (Matrix.vec X)

private theorem matrixEuclideanVec_injective {a b : Type*} :
    Function.Injective (matrixEuclideanVec : Matrix a b ℂ → EuclideanSpace ℂ (b × a)) := by
  intro X Y h
  exact Matrix.vec_inj.mp ((WithLp.toLp_injective 2) h)

private theorem matrixEuclideanVec_surjective {a b : Type*} :
    Function.Surjective (matrixEuclideanVec : Matrix a b ℂ → EuclideanSpace ℂ (b × a)) := by
  intro x
  exact ⟨Matrix.unvec (WithLp.ofLp x), by simp only [matrixEuclideanVec, vec_unvec, WithLp.toLp_ofLp]⟩

private theorem matrixEuclideanVec_norm {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b ℂ) :
    ‖matrixEuclideanVec X‖ = ‖X‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  rw [EuclideanSpace.norm_sq_eq, Matrix.frobenius_norm_sq_eq_sum_sq, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private theorem twoSided_matrixEuclideanVec (A : Matrix m p ℂ) (B : Matrix q n ℂ)
    (X : Matrix p q ℂ) :
    toEuclideanLin (Bᵀ ⊗ₖ A) (matrixEuclideanVec X) = matrixEuclideanVec (A * X * B) := by
  rw [matrixEuclideanVec, toEuclideanLin_toLp, Matrix.kronecker_mulVec_vec, transpose_transpose]
  rfl

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
private theorem twoSided_adjoint (A : Matrix m p ℂ) (B : Matrix q n ℂ) :
    (Bᵀ ⊗ₖ A)ᴴ = Bᴴᵀ ⊗ₖ Aᴴ := by
  rw [Matrix.conjTranspose_kronecker, conjTranspose_transpose_eq_transpose_conjTranspose]

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 3.
Under the Euclidean vectorization for the Frobenius form, the range of
the two-sided product is perpendicular to the null space of its adjoint. -/
theorem exercise_3_15 (A : Matrix m p ℂ) (B : Matrix q n ℂ) :
    (LinearMap.range (toEuclideanLin (Bᵀ ⊗ₖ A)))ᗮ =
      (toEuclideanLin (Bᴴᵀ ⊗ₖ Aᴴ)).ker ∧
    (∀ X : Matrix m n ℂ, matrixEuclideanVec X ∈ LinearMap.range (toEuclideanLin (Bᵀ ⊗ₖ A)) ↔
      ∃ Y : Matrix p q ℂ, A * Y * B = X) ∧
    ∀ X : Matrix m n ℂ, matrixEuclideanVec X ∈ (toEuclideanLin (Bᴴᵀ ⊗ₖ Aᴴ)).ker ↔
      Aᴴ * X * Bᴴ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint, twoSided_adjoint]
  · intro X
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨Y, rfl⟩ := matrixEuclideanVec_surjective y
      exact ⟨Y, matrixEuclideanVec_injective ((twoSided_matrixEuclideanVec A B Y).symm.trans hy)⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨matrixEuclideanVec Y, twoSided_matrixEuclideanVec A B Y⟩
  · intro X
    rw [LinearMap.mem_ker, twoSided_matrixEuclideanVec]
    change matrixEuclideanVec (Aᴴ * X * Bᴴ) = matrixEuclideanVec (0 : Matrix p q ℂ) ↔ _
    exact matrixEuclideanVec_injective.eq_iff

/-- A Frobenius least-squares solution for two-sided multiplication. -/
def IsMatrixLeastSquaresSolution (A : Matrix m p ℂ) (B : Matrix q n ℂ) (D : Matrix m n ℂ)
    (X : Matrix p q ℂ) : Prop :=
  ∀ Y, ‖A * X * B - D‖ ≤ ‖A * Y * B - D‖

/-- A matrix least-squares solution of minimum Frobenius norm. -/
def IsMinNormMatrixLeastSquaresSolution (A : Matrix m p ℂ) (B : Matrix q n ℂ)
    (D : Matrix m n ℂ) (X : Matrix p q ℂ) : Prop :=
  IsMatrixLeastSquaresSolution A B D X ∧
    ∀ Y, IsMatrixLeastSquaresSolution A B D Y → ‖X‖ ≤ ‖Y‖

omit [DecidableEq m] [DecidableEq n] in
private theorem matrixLeastSquares_iff_euclideanVec (A : Matrix m p ℂ) (B : Matrix q n ℂ)
    (D : Matrix m n ℂ) (X : Matrix p q ℂ) :
    IsMatrixLeastSquaresSolution A B D X ↔
      leastSquaresSolution (Bᵀ ⊗ₖ A) (matrixEuclideanVec D) (matrixEuclideanVec X) := by
  have he (Y : Matrix p q ℂ) :
      ‖toEuclideanLin (Bᵀ ⊗ₖ A) (matrixEuclideanVec Y) - matrixEuclideanVec D‖ =
        ‖A * Y * B - D‖ := by
    rw [twoSided_matrixEuclideanVec]
    change ‖matrixEuclideanVec (A * Y * B - D)‖ = _
    exact matrixEuclideanVec_norm _
  constructor
  · intro h y
    obtain ⟨Y, rfl⟩ := matrixEuclideanVec_surjective y
    simpa only [he] using h Y
  · intro h Y
    simpa only [he] using h (matrixEuclideanVec Y)

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 3.
The unique Frobenius minimum-norm least-squares solution of AXB=D is
obtained by multiplying D by the two pseudoinverses. -/
theorem exercise_3_18 (A : Matrix m p ℂ) (B : Matrix q n ℂ) (D : Matrix m n ℂ)
    (X : Matrix p q ℂ) :
    IsMinNormMatrixLeastSquaresSolution A B D X ↔ X = A.pinv * D * B.pinv := by
  have hpow :
      toEuclideanLin (Bᵀ ⊗ₖ A).pinv (matrixEuclideanVec D) =
        matrixEuclideanVec (A.pinv * D * B.pinv) := by
    rw [Chapter02.pinv_kronecker, Chapter01.pinv_transpose, twoSided_matrixEuclideanVec]
  constructor
  · rintro ⟨hx, hmin⟩
    have hm : IsMinNormLeastSquaresSolution (Bᵀ ⊗ₖ A) (matrixEuclideanVec D)
        (matrixEuclideanVec X) := by
      refine ⟨(matrixLeastSquares_iff_euclideanVec A B D X).mp hx, fun y hy => ?_⟩
      obtain ⟨Y, rfl⟩ := matrixEuclideanVec_surjective y
      simpa only [matrixEuclideanVec_norm] using
        hmin Y ((matrixLeastSquares_iff_euclideanVec A B D Y).mpr hy)
    exact matrixEuclideanVec_injective (hm.eq_pinv.trans hpow)
  · rintro rfl
    have hm := isMinNormLeastSquaresSolution_pinv (Bᵀ ⊗ₖ A) (matrixEuclideanVec D)
    rw [hpow] at hm
    exact ⟨(matrixLeastSquares_iff_euclideanVec A B D _).mpr hm.1, fun Y hY => by
      simpa only [matrixEuclideanVec_norm] using
        hm.2 _ ((matrixLeastSquares_iff_euclideanVec A B D Y).mp hY)⟩

/-- **Exercise 19** of [benIsrael2003generalized], Chapter 3.
An inner inverse is the pseudoinverse exactly when it is an adjoint-range
matrix or it has the least Frobenius norm among all inner inverses. -/
theorem exercise_3_19 (A : Matrix m n ℂ) (X : Matrix n m ℂ) (hX : A.IsInnerInverse X) :
    (X = A.pinv ↔ ∃ Y : Matrix m n ℂ, X = Aᴴ * Y * Aᴴ) ∧
    (X = A.pinv ↔ ∀ Y : Matrix n m ℂ, A.IsInnerInverse Y → ‖X‖ ≤ ‖Y‖) := by
  have hinner : ∀ Y : Matrix n m ℂ,
      IsMatrixLeastSquaresSolution A A A Y ↔ A.IsInnerInverse Y := by
    intro Y
    constructor
    · intro hY
      apply isInnerInverse_iff.mpr
      have ho := hY A.pinv
      rw [A.mul_pinv_mul_self, sub_self, norm_zero] at ho
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ho (norm_nonneg _)))
    · intro hY Z
      rw [isInnerInverse_iff.mp hY, sub_self, norm_zero]
      exact norm_nonneg _
  refine ⟨?_, ?_⟩
  · constructor
    · rintro rfl
      refine ⟨A.pinvᴴ * A.pinv * A.pinvᴴ, ?_⟩
      have h₁ : Aᴴ * A.pinvᴴ = A.pinv * A := by
        rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq]
      have h₂ : A.pinvᴴ * Aᴴ = A * A.pinv := by
        rw [← conjTranspose_mul, A.isHermitian_mul_pinv.eq]
      calc
        A.pinv = (A.pinv * A * A.pinv) * (A * A.pinv) := by
          rw [A.pinv_mul_self_mul_pinv, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
        _ = Aᴴ * (A.pinvᴴ * A.pinv * A.pinvᴴ) * Aᴴ := by
          simp only [← h₁, ← h₂, Matrix.mul_assoc]
    · rintro ⟨Y, hY⟩
      have hL : A.pinv * A * X = X := by
        rw [hY]
        calc
          _ = (A.pinv * A * Aᴴ) * Y * Aᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [A.pinv_mul_self_mul_conjTranspose]
      have hR : X * (A * A.pinv) = X := by
        rw [hY]
        calc
          _ = Aᴴ * Y * (Aᴴ * (A * A.pinv)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [A.conjTranspose_mul_mul_pinv]
      calc
        X = A.pinv * (A * X * A) * A.pinv := by
          rw [show A.pinv * (A * X * A) * A.pinv = (A.pinv * A * X) * (A * A.pinv) by
            simp only [Matrix.mul_assoc], hL, hR]
        _ = A.pinv := by rw [isInnerInverse_iff.mp hX, A.pinv_mul_self_mul_pinv]
  · rw [← A.pinv_mul_self_mul_pinv, ← (exercise_3_18 A A A X)]
    exact ⟨fun h Y hy => h.2 Y ((hinner Y).mpr hy), fun h =>
      ⟨(hinner X).mpr hX, fun Y hy => h Y ((hinner Y).mp hy)⟩⟩

omit [DecidableEq m] in
private theorem frobeniusMin_right_normal (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    IsMinOn (fun Y : Matrix n m ℂ => ‖Y * A - 1‖) Set.univ X ↔ X * A * Aᴴ = Aᴴ := by
  have h := Matrix.isMinOn_norm_sub_mul_conjTranspose_iff (1 : Matrix n n ℂ) Aᴴ X
  simpa only [norm_sub_rev (1 : Matrix n n ℂ), conjTranspose_conjTranspose,
    Matrix.one_mul, ← Matrix.mul_assoc] using h

omit [DecidableEq n] in
private theorem frobeniusMin_left_adjoint (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    IsMinOn (fun Y : Matrix n m ℂ => ‖A * Y - 1‖) Set.univ X ↔
      IsMinOn (fun Y : Matrix m n ℂ => ‖Y * Aᴴ - 1‖) Set.univ Xᴴ := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  have hn (Y : Matrix n m ℂ) : ‖Yᴴ * Aᴴ - 1‖ = ‖A * Y - 1‖ := by
    rw [← conjTranspose_mul, ← conjTranspose_one, ← conjTranspose_sub, frobenius_norm_conjTranspose, conjTranspose_one]
  constructor
  · intro h Z
    have he := h Zᴴ
    rwa [← hn X, ← hn Zᴴ, conjTranspose_conjTranspose] at he
  · intro h Y
    simpa only [hn] using h Yᴴ

omit [DecidableEq m] in
private theorem frobeniusMin_right_iff (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    IsMinOn (fun Y : Matrix n m ℂ => ‖Y * A - 1‖) Set.univ X ↔
      X ∈ definition_1 A {.inner, .hermitianMulRev} := by
  have hp : A.pinv ∈ definition_1 A {.inner, .hermitianMulRev} :=
    mem_one_four_iff.mpr ⟨A.mul_pinv_mul_self, A.isHermitian_pinv_mul⟩
  rw [frobeniusMin_right_normal, Chapter02.theorem_4 hp]
  constructor
  · intro h
    have hcap : Aᴴ * A.pinvᴴ = A.pinv * A := by
      rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq]
    calc
      X * A = X * (A * A.pinv * A) := by rw [A.mul_pinv_mul_self]
      _ = (X * A) * (A.pinv * A) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hcap, ← Matrix.mul_assoc, h, hcap]
  · intro h
    rw [h, A.pinv_mul_self_mul_conjTranspose]

/-- **Exercise 17(a)–(b)** of [benIsrael2003generalized], Chapter 3.
The left and right identity equations characterize the two indicated
classes of inverses by their Frobenius least-squares properties. -/
theorem exercise_3_17 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    (X ∈ definition_1 A {.inner, .hermitianMul} ↔
      IsMinOn (fun Y : Matrix n m ℂ => ‖A * Y - 1‖) Set.univ X) ∧
    (X ∈ definition_1 A {.inner, .hermitianMulRev} ↔
      IsMinOn (fun Y : Matrix n m ℂ => ‖Y * A - 1‖) Set.univ X) := by
  refine ⟨?_, (frobeniusMin_right_iff A X).symm⟩
  rw [frobeniusMin_left_adjoint, frobeniusMin_right_iff, mem_one_three_iff, mem_one_four_iff]
  have hi : (Aᴴ * Xᴴ * Aᴴ = Aᴴ) ↔ (A * X * A = A) := by
    rw [← conjTranspose_mul, ← conjTranspose_mul, ← Matrix.mul_assoc, conjTranspose_inj]
  have hh : (Xᴴ * Aᴴ).IsHermitian ↔ (A * X).IsHermitian := by
    rw [← conjTranspose_mul]
    change (A * X)ᴴᴴ = (A * X)ᴴ ↔ (A * X)ᴴ = A * X
    rw [conjTranspose_conjTranspose]
    exact eq_comm
  exact and_congr hi.symm hh.symm

/-- **Exercise 17(c)** of [benIsrael2003generalized], Chapter 3.
The pseudoinverse uniquely has least Frobenius norm among the
least-squares solutions of either of the identity equations. -/
theorem exercise_3_17_minNorm (A : Matrix m n ℂ) :
    (IsMinOn (fun Y : Matrix n m ℂ => ‖A * Y - 1‖) Set.univ A.pinv ∧
      ∀ X : Matrix n m ℂ, ‖A * X - 1‖ = ‖A * A.pinv - 1‖ →
        ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv)) ∧
    (IsMinOn (fun Y : Matrix n m ℂ => ‖Y * A - 1‖) Set.univ A.pinv ∧
      ∀ X : Matrix n m ℂ, ‖X * A - 1‖ = ‖A.pinv * A - 1‖ →
        ‖A.pinv‖ ≤ ‖X‖ ∧ (‖X‖ = ‖A.pinv‖ → X = A.pinv)) := by
  refine ⟨isMinOn_norm_mul_sub_one_pinv A, ?_⟩
  have hh := isMinOn_norm_mul_sub_one_pinv Aᴴ
  rw [A.pinv_conjTranspose] at hh
  refine ⟨?_, ?_⟩
  · have h := (frobeniusMin_left_adjoint Aᴴ A.pinvᴴ).mp hh.1
    simpa only [conjTranspose_conjTranspose] using h
  · intro X hX
    have hn (Y : Matrix n m ℂ) : ‖Aᴴ * Yᴴ - 1‖ = ‖Y * A - 1‖ := by
      rw [← conjTranspose_mul, ← conjTranspose_one, ← conjTranspose_sub, frobenius_norm_conjTranspose, conjTranspose_one]
    have h := hh.2 Xᴴ (by simpa only [hn] using hX)
    simp only [frobenius_norm_conjTranspose] at h
    exact ⟨h.1, fun he => conjTranspose_injective (h.2 he)⟩

/-- Independence of the inner inverse chosen in the sandwiched product. -/
def IsInnerInverseProductInvariant (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (C : Matrix m q ℂ) : Prop :=
  ∀ U V : Matrix n m ℂ, A.IsInnerInverse U → A.IsInnerInverse V → B * U * C = B * V * C

private theorem range_le_iff_pinv_projection_mul {l : Type*} [Fintype l] [DecidableEq l]
    (A : Matrix m n ℂ) (C : Matrix m l ℂ) :
    (toEuclideanLin C).range ≤ (toEuclideanLin A).range ↔ A * A.pinv * C = C := by
  constructor
  · intro h
    apply toEuclideanLin.injective
    ext1 z
    rw [toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr (h ⟨z, rfl⟩)
  · rintro h x ⟨z, rfl⟩
    have f := congrArg (fun M => toEuclideanLin M z) h
    rw [toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection] at f
    exact Submodule.starProjection_eq_self_iff.mp f

private theorem adjoint_range_le_iff_mul_pinv_projection (A : Matrix m n ℂ) (B : Matrix p n ℂ) :
    (toEuclideanLin Bᴴ).range ≤ (toEuclideanLin Aᴴ).range ↔ B * (A.pinv * A) = B := by
  rw [range_le_iff_pinv_projection_mul Aᴴ Bᴴ, A.pinv_conjTranspose, ← conjTranspose_mul,
    A.isHermitian_pinv_mul.eq, ← conjTranspose_inj]
  rw [conjTranspose_mul, conjTranspose_conjTranspose, A.isHermitian_pinv_mul.eq]

private theorem sandwich_zero_for_all
    (L : Matrix p n ℂ) (R : Matrix m q ℂ) (h : ∀ Z : Matrix n m ℂ, L * Z * R = 0) :
    L = 0 ∨ R = 0 := by
  classical
  by_contra hn
  have hnL : L ≠ 0 := fun he => hn (Or.inl he)
  have hnR : R ≠ 0 := fun he => hn (Or.inr he)
  obtain ⟨i, j, hi⟩ : ∃ i j, L i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hnL (Matrix.ext h)
  obtain ⟨k, l, hk⟩ : ∃ k l, R k l ≠ 0 := by
    by_contra h
    push Not at h
    exact hnR (Matrix.ext h)
  let S := Matrix.single j k (1 : ℂ)
  have hz := congrArg (fun M : Matrix p q ℂ => M i l) (h S)
  have hs : (L * S * R) i l = L i j * R k l := calc
    _ = (L * S) i k * R k l := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_single k (fun b _ hb => by
        rw [show (L * S) i b = 0 from mul_single_apply_of_ne (1 : ℂ) j k i b hb L, zero_mul])
        (fun h => (h (Finset.mem_univ _)).elim)
    _ = _ := by rw [show (L * S) i k = L i j from (mul_single_apply_same (1 : ℂ) j k i L).trans (mul_one _)]
  rw [hs] at hz
  exact mul_ne_zero hi hk hz

/-- **Exercise 16** of [benIsrael2003generalized], Chapter 3.
The range criterion includes the case of a zero outer factor. The
null-space criterion applies to every choice of outer factors. -/
theorem exercise_3_16 (A : Matrix m n ℂ) (B : Matrix p n ℂ) (C : Matrix m q ℂ) :
    (IsInnerInverseProductInvariant A B C ↔
      B = 0 ∨ C = 0 ∨ ((toEuclideanLin C).range ≤ (toEuclideanLin A).range ∧
        (toEuclideanLin Bᴴ).range ≤ (toEuclideanLin Aᴴ).range)) ∧
    (IsInnerInverseProductInvariant A B C ↔
      ∀ Z : Matrix n m ℂ, A * Z * A = 0 → B * Z * C = 0) := by
  have hnull : IsInnerInverseProductInvariant A B C ↔
      ∀ Z : Matrix n m ℂ, A * Z * A = 0 → B * Z * C = 0 := by
    constructor
    · intro h Z hZ
      have hu : A.IsInnerInverse (A.pinv + Z) := by
        apply isInnerInverse_iff.mpr
        rw [Matrix.mul_add, Matrix.add_mul, A.mul_pinv_mul_self, hZ, add_zero]
      have he := h (A.pinv + Z) A.pinv hu A.mul_pinv_mul_self
      rw [Matrix.mul_add, Matrix.add_mul] at he
      exact add_left_cancel (he.trans (add_zero _).symm)
    · intro h U V hU hV
      have hK : A * (U - V) * A = 0 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, isInnerInverse_iff.mp hU,
          isInnerInverse_iff.mp hV, sub_self]
      have he := h _ hK
      rwa [Matrix.mul_sub, Matrix.sub_mul, sub_eq_zero] at he
  refine ⟨hnull.trans ?_, hnull⟩
  constructor
  · intro h
    by_cases hB : B = 0
    · exact Or.inl hB
    by_cases hC : C = 0
    · exact Or.inr (Or.inl hC)
    have hR : (1 - A * A.pinv) * A = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, A.mul_pinv_mul_self, sub_self]
    have hL : A * (1 - A.pinv * A) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, A.mul_pinv_mul_self, sub_self]
    have hbZ (Z : Matrix n m ℂ) : (B * (1 - A.pinv * A)) * Z * C = 0 := by
      have hZ := h ((1 - A.pinv * A) * Z) (by
        rw [← Matrix.mul_assoc A, hL, Matrix.zero_mul, Matrix.zero_mul])
      simpa only [Matrix.mul_assoc] using hZ
    have hcZ (Z : Matrix n m ℂ) : B * Z * ((1 - A * A.pinv) * C) = 0 := by
      have hZ := h (Z * (1 - A * A.pinv)) (by
        rw [Matrix.mul_assoc A, Matrix.mul_assoc Z, hR, Matrix.mul_zero, Matrix.mul_zero])
      simpa only [Matrix.mul_assoc] using hZ
    have hb := (sandwich_zero_for_all _ _ hbZ).resolve_right hC
    have hc := (sandwich_zero_for_all _ _ hcZ).resolve_left hB
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hb
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hc
    exact Or.inr (Or.inr ⟨(range_le_iff_pinv_projection_mul A C).mpr hc.symm,
      (adjoint_range_le_iff_mul_pinv_projection A B).mpr hb.symm⟩)
  · rintro (hB | hC | ⟨hC, hB⟩) Z hZ
    · simp [hB]
    · simp [hC]
    · rw [range_le_iff_pinv_projection_mul A C] at hC
      rw [adjoint_range_le_iff_mul_pinv_projection A B] at hB
      calc
        B * Z * C = (B * (A.pinv * A)) * Z * (A * A.pinv * C) := by rw [hB, hC]
        _ = (B * A.pinv) * (A * Z * A) * (A.pinv * C) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]


end MatrixEquations

end BenIsraelGreville.Chapter03
