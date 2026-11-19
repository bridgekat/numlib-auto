import Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve
import NumlibSurface.BenziGolubLiesen.Section03.Factorization

/-!
# Benzi, Golub and Liesen, Section 3: Conditioning and augmentation

A zero constraint right-hand side removes the second block column of the inverse from the
solution. When $C=0$, adding $B^T W$ times the constraint equation to the primal equation
leaves the solution set unchanged. With $W=\gamma I$, this can make the leading block positive
definite.

## Main results

* `BenziGolubLiesen.saddlePointMatrix_inv_mulVec_zero_right`: the inverse acts through its first
  block column when $g=0$.
* `BenziGolubLiesen.augmentedSaddlePointSystem_iff`: equivalence with (3.14).
* `BenziGolubLiesen.posDef_augmentedTopBlock`: positivity of the augmented leading block.

## Deviations from the source

* **Section 3.5, zero constraint right-hand side** (reading). The block-column identity
  holds for the total matrix inverse. It describes a solution via the inverse when the
  saddle matrix is nonsingular. See `BenziGolubLiesen.saddlePointMatrix_inv_mulVec_zero_right`.
* **Equation (3.14)** (generalization). Adding $B^TW$ times the constraint equation
  preserves the solution set for arbitrary $W$. See
  `BenziGolubLiesen.augmentedSaddlePointSystem_iff`.
* **After (3.14)** (correction). Positivity of $A$ on $\ker B$ alone need not make
  $A+\gamma B^TB$ positive definite for every $\gamma>0$. The result uses positive
  semidefiniteness of $A$ and the trivial kernel intersection. See
  `BenziGolubLiesen.posDef_augmentedTopBlock`.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Section 3.5** of [benzi2005numerical]. The inverse applied to the right-hand side
$(f,0)$ acts by its first block column.

**Reading.** The source applies the genuine inverse to get a solution. The identity
here is stated for the total matrix inverse, which is zero when the matrix is singular. -/
theorem saddlePointMatrix_inv_mulVec_zero_right (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (C : Matrix m m ℝ) (f : n → ℝ) :
    let N := (saddlePointMatrix A B₁ B₂ C)⁻¹
    N *ᵥ Sum.elim f 0 = Sum.elim (N.toBlocks₁₁ *ᵥ f) (N.toBlocks₂₁ *ᵥ f) := by
  intro N
  conv_lhs => rw [← fromBlocks_toBlocks N, fromBlocks_mulVec]
  simp

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (3.14)** of [benzi2005numerical]. For $C=0$, the modification
$A \mapsto A+B^T W B$, $f \mapsto f+B^T Wg$ preserves all solutions.

**Generalization.** The source assumes $W$ is symmetric positive semidefinite. The
equivalence follows by adding $B^TW$ times the constraint equation for any $W$. -/
theorem augmentedSaddlePointSystem_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (W : Matrix m m ℝ) (x f : n → ℝ) (y g : m → ℝ) :
    saddlePointMatrix (A + Bᵀ * W * B) B B 0 *ᵥ Sum.elim x y =
        Sum.elim (f + (Bᵀ * W) *ᵥ g) g ↔
      saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g := by
  simpa [saddlePointMatrix] using fromBlocks_transpose_zero_augment_iff B W x y f g (A := A)

omit [DecidableEq n] in
/-- **Sections 3.5 and 5** of [benzi2005numerical]. If $A$ is positive semidefinite and
$\ker A\cap\ker B=\{0\}$, choosing $W=\gamma I$ with $\gamma>0$ makes the augmented leading
block positive definite. The leading block can thus be used for Schur reduction even if $A$
itself is singular.

**Correction.** The discussion after (3.14) only requires $A$ positive definite on $\ker B$.
This does not suffice for each $\gamma>0$: take $A=\operatorname{diag}(-1,1)$, $B=[1,0]$
and $\gamma=1$. The augmented block is then singular. Positive semidefiniteness of $A$
with the stated kernel condition gives the uniform conclusion. -/
theorem posDef_augmentedTopBlock {A : Matrix n n ℝ} (hA : A.PosSemidef) (B : Matrix m n ℝ)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) : (A + Bᵀ * (γ • (1 : Matrix m m ℝ)) * B).PosDef := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  exact posDef_add_scaled_gram_of_ker_inf_eq_bot hA hker hγ

end BenziGolubLiesen
