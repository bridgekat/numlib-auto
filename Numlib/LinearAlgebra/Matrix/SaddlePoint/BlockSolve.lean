import Numlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real

/-!
# Exact block elimination

For a block system with invertible first diagonal block $A$, a block row operation eliminates
the lower left block $F$. The resulting second diagonal block is the Schur complement
$S = D - FA^{-1}E$. Solving the transformed upper triangular system gives the same solutions
as solving the original system.

## Main results

* `Matrix.lower_elimination_mul_fromBlocks`: the block row operation transforms the coefficient
  matrix to block upper triangular form.
* `Matrix.fromBlocks_mulVec_eq_iff_schur`: the Schur equation and back-substitution equation
  characterize solutions of the block system.
* `Matrix.fromBlocks_transpose_zero_augment_iff`: adding a multiple of the constraint equation
  to the primal equation does not change the solutions.
* `Matrix.posDef_add_scaled_gram_of_ker_inf_eq_bot`: positive scalar augmentation yields a
  positive definite primal block when the primal and constraint kernels meet trivially.
-/

open scoped Matrix

namespace Matrix

variable {K n m : Type*} [CommRing K] [Fintype n] [Fintype m] [DecidableEq n]
variable {A : Matrix n n K} (E : Matrix n m K) (F : Matrix m n K) (D : Matrix m m K)

/-- If $A$ is invertible, multiplying $\begin{bmatrix}A&E\\F&D\end{bmatrix}$ on the left by
$\begin{bmatrix}I&0\\-FA^{-1}&I\end{bmatrix}$ gives
$\begin{bmatrix}A&E\\0&D-FA^{-1}E\end{bmatrix}$. All blocks are finite matrices over a
commutative ring. -/
theorem lower_elimination_mul_fromBlocks [DecidableEq m] (hA : IsUnit A) :
    fromBlocks 1 0 (-(F * A⁻¹)) 1 * fromBlocks A E F D =
      fromBlocks A E 0 (fromBlocks A E F D).schurComplement := by
  have h := (isUnit_iff_isUnit_det A).1 hA
  simp [fromBlocks_multiply, schurComplement_fromBlocks, Matrix.mul_assoc, sub_eq_add_neg,
    add_comm, nonsing_inv_mul A h]

/-- For finite matrices over a commutative ring, let $A$ be invertible and
$S = D - FA^{-1}E$. The block equations $Ax+Ey=f$ and $Fx+Dy=g$ are equivalent to
$Sy=g-FA^{-1}f$ and $Ax=f-Ey$. No invertibility of $S$ is needed for this equivalence. -/
theorem fromBlocks_mulVec_eq_iff_schur (hA : IsUnit A)
    (x : n → K) (y : m → K) (f : n → K) (g : m → K) :
    fromBlocks A E F D *ᵥ Sum.elim x y = Sum.elim f g ↔
      (fromBlocks A E F D).schurComplement *ᵥ y = g - (F * A⁻¹) *ᵥ f ∧
        A *ᵥ x = f - E *ᵥ y := by
  classical
  let T := fromBlocks (1 : Matrix n n K) 0 (-(F * A⁻¹)) (1 : Matrix m m K)
  have hT : Function.Injective T.mulVec := by
    intro u v huv
    simp only [T, fromBlocks_mulVec, one_mulVec, Matrix.zero_mulVec, add_zero,
      Sum.elim_eq_iff] at huv
    rw [← Sum.elim_comp_inl_inr u, ← Sum.elim_comp_inl_inr v]
    exact Sum.elim_eq_iff.2 ⟨huv.1, by simpa [huv.1] using huv.2⟩
  rw [← hT.eq_iff, mulVec_mulVec]
  change (T * fromBlocks A E F D) *ᵥ Sum.elim x y = T *ᵥ Sum.elim f g ↔ _
  rw [lower_elimination_mul_fromBlocks E F D hA]
  simp only [T, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, neg_mulVec, Sum.elim_eq_iff]
  rw [add_comm (-((F * A⁻¹) *ᵥ f)) g, ← sub_eq_add_neg, ← eq_sub_iff_add_eq]
  exact and_comm

omit [DecidableEq n] in
/-- Adding $Q$ times the constraint row $Bx=g$ to $Ax+B^Ty=f$ preserves solutions. -/
theorem saddleEquations_augment_iff (B : Matrix m n K) (Q : Matrix n m K)
    (x : n → K) (y : m → K) (f : n → K) (g : m → K) :
    ((A + Q * B) *ᵥ x + Bᵀ *ᵥ y = f + Q *ᵥ g ∧ B *ᵥ x = g) ↔
      (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x = g) := by
  refine and_congr_left fun hx => ?_
  rw [add_mulVec, ← mulVec_mulVec, hx, add_right_comm, add_left_inj]

omit [DecidableEq n] in
/-- Let $A$, $B$ and $W$ be finite matrices over a commutative ring. The unregularized saddle
system $Ax+B^T y=f$, $Bx=g$ has the same solutions as the augmented system
$(A+B^TWB)x+B^Ty=f+B^TWg$, $Bx=g$. -/
theorem fromBlocks_transpose_zero_augment_iff
    (B : Matrix m n K) (W : Matrix m m K) (x : n → K) (y : m → K)
    (f : n → K) (g : m → K) :
    fromBlocks (A + Bᵀ * W * B) Bᵀ B 0 *ᵥ Sum.elim x y =
        Sum.elim (f + (Bᵀ * W) *ᵥ g) g ↔
      fromBlocks A Bᵀ B (0 : Matrix m m K) *ᵥ Sum.elim x y = Sum.elim f g := by
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_eq_iff,
    zero_mulVec, add_zero]
  exact saddleEquations_augment_iff B (Bᵀ * W) x y f g

end Matrix

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- Let $A$ be real symmetric positive semidefinite, let $B$ be a real matrix of compatible size,
and suppose $\ker A\cap\ker B=\{0\}$. For each $\gamma>0$, the augmented primal block
$A+\gamma B^TB$ is symmetric positive definite. -/
theorem posDef_add_scaled_gram_of_ker_inf_eq_bot {A : Matrix n n ℝ} {B : Matrix m n ℝ}
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) :
    (A + γ • (Bᵀ * B)).PosDef := by
  have hG : (Bᵀ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self B
  have hsum := hA.add (hG.smul hγ.le)
  refine PosDef.of_dotProduct_mulVec_pos hsum.isHermitian fun x hx => ?_
  refine lt_of_le_of_ne (hsum.dotProduct_mulVec_nonneg x) (Ne.symm fun hzero => hx ?_)
  have hnonnegA : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa using hA.dotProduct_mulVec_nonneg x
  have hnonnegB : 0 ≤ x ⬝ᵥ ((Bᵀ * B) *ᵥ x) := by simpa using hG.dotProduct_mulVec_nonneg x
  simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at hzero
  have ha : x ⬝ᵥ (A *ᵥ x) = 0 := by
    linarith only [hzero, hnonnegA, mul_nonneg hγ.le hnonnegB]
  have hb : x ⬝ᵥ ((Bᵀ * B) *ᵥ x) = 0 := by
    have hmul : γ * (x ⬝ᵥ ((Bᵀ * B) *ᵥ x)) = 0 := by rwa [ha, zero_add] at hzero
    exact (mul_eq_zero.mp hmul).resolve_left hγ.ne'
  have hAx : A *ᵥ x = 0 := hA.dotProduct_mulVec_zero_iff.1 (by simpa using ha)
  rw [← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_self_eq_zero] at hb
  exact (Submodule.eq_bot_iff _).1 hker x ⟨hAx, hb⟩

end Matrix
