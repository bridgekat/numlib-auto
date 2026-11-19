import Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve
import NumlibSurface.BenziGolubLiesen.Section03.Conditioning

/-!
# Benzi, Golub and Liesen, Section 5: Schur complement reduction

Section 5 of [benzi2005numerical] eliminates the first variable $x$ from a saddle-point
system with nonsingular primal block $A$. The reduced equation for $y$ has coefficient
$-S = B_2 A^{-1} B_1^T + C$, where $S$ is the Schur complement. The second step recovers
$x$ from $Ax=f-B_1^Ty$. The proofs use the block elimination identities of
`Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve`.

## Main definitions

* Section 5, `BenziGolubLiesen.negativeSchurComplement`: the reduced coefficient $-S$.

## Main results

* Section 5, `BenziGolubLiesen.isUnit_negativeSchurComplement`: the reduced coefficient
  is nonsingular when both $A$ and the full matrix are nonsingular.
* Equations (5.1) and (5.2), `BenziGolubLiesen.saddlePointMatrix_mulVec_iff_schurReduction`:
  the two reduced systems describe exactly the solutions of the coupled system.
* Section 5, `BenziGolubLiesen.saddlePointMatrix_schur_elimination`: the block row operation
  transforms both the matrix and the right-hand side.
* Section 5, `BenziGolubLiesen.negativeSchurComplement_mulVec`: the action of $-S$ requires
  only a solve with $A$ and products by the original blocks.
* Equation (3.14), `BenziGolubLiesen.augmentedSaddlePointSystem_iff`: constraint
  augmentation leaves the solution set unchanged.
* Equation (3.14), `BenziGolubLiesen.posDef_augmentedTopBlock`: a positive scalar
  augmentation gives a nonsingular primal block under the kernel condition.

## Deviations from the source

* **Equations (5.1)–(5.2)** (generalization). The reduced equations are equivalent to the
  original equations even when the full saddle matrix is singular, provided $A$ is
  invertible. See `BenziGolubLiesen.saddlePointMatrix_mulVec_iff_schurReduction`.

## Not formalized

* Sparse storage, fill growth, and numerical stability of forming the Schur complement are not
  formalized here; they depend on the sparsity model, ordering, and arithmetic.
-/

noncomputable section

open Matrix

namespace BenziGolubLiesen

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {A : Matrix n n ℝ} {B₁ B₂ : Matrix m n ℝ} {C : Matrix m m ℝ}

/-- **Section 5** of [benzi2005numerical]. For the real saddle-point matrix with blocks $A$,
$B_1^T$, $B_2$ and $-C$, its **negative Schur complement** is $-S=B_2A^{-1}B_1^T+C$.
It is defined through `Matrix.schurComplement`; the totalized inverse is zero for singular
$A$, although Schur reduction assumes $A$ is nonsingular.

**Reading.** Uses the signed formula, with total inverse at singular A documented in the
declaration.
-/
abbrev negativeSchurComplement (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (C : Matrix m m ℝ) : Matrix m m ℝ :=
  -(saddlePointMatrix A B₁ B₂ C).schurComplement

omit [Fintype m] [DecidableEq m] in
/-- In blocks, the negative Schur complement is $B_2A^{-1}B_1^T+C$. -/
@[simp]
theorem negativeSchurComplement_eq (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (C : Matrix m m ℝ) :
    negativeSchurComplement A B₁ B₂ C = B₂ * A⁻¹ * B₁ᵀ + C := by
  rw [negativeSchurComplement, saddlePointMatrix, schurComplement_fromBlocks, neg_sub,
    sub_neg_eq_add, Matrix.mul_assoc]

/-- **Section 5** of [benzi2005numerical]. If both $A$ and the real saddle-point matrix with
blocks $A$, $B_1^T$, $B_2$ and $-C$ are nonsingular, then $-S$ is nonsingular. -/
theorem isUnit_negativeSchurComplement (hA : IsUnit A)
    (hM : IsUnit (saddlePointMatrix A B₁ B₂ C)) :
    IsUnit (negativeSchurComplement A B₁ B₂ C) :=
  (isUnit_schurComplement (by simpa [saddlePointMatrix] using hA) hM).neg

omit [DecidableEq m] in
/-- **Equations (5.1) and (5.2)** of [benzi2005numerical]. Let the real primal block $A$ be
nonsingular. For real vectors $x,f$ on the primal coordinates and $y,g$ on the constraint
coordinates, the coupled saddle-point system holds if and only if
$$(-S)y=B_2A^{-1}f-g \quad\text{and}\quad Ax=f-B_1^Ty.$$

**Generalization.** The source assumes a nonsingular full saddle matrix. The equation
equivalence needs only invertibility of $A$, since it is a row operation. -/
theorem saddlePointMatrix_mulVec_iff_schurReduction (hA : IsUnit A)
    (x f : n → ℝ) (y g : m → ℝ) :
    saddlePointMatrix A B₁ B₂ C *ᵥ Sum.elim x y = Sum.elim f g ↔
      negativeSchurComplement A B₁ B₂ C *ᵥ y = (B₂ * A⁻¹) *ᵥ f - g ∧
        A *ᵥ x = f - B₁ᵀ *ᵥ y := by
  rw [saddlePointMatrix, fromBlocks_mulVec_eq_iff_schur _ _ _ hA]
  simp only [negativeSchurComplement, saddlePointMatrix, neg_mulVec, neg_eq_iff_eq_neg, neg_sub]

/-- **Section 5** of [benzi2005numerical]. Let $A$ be nonsingular in the real saddle-point
matrix. The row operation $T=\begin{bmatrix}I&0\\-B_2A^{-1}&I\end{bmatrix}$ gives
$$T\mathcal A=\begin{bmatrix}A&B_1^T\\0&S\end{bmatrix},
\qquad T(f,g)=(f,g-B_2A^{-1}f).$$
Here $f$ and $g$ are real vectors on the primal and constraint coordinates. -/
theorem saddlePointMatrix_schur_elimination (hA : IsUnit A) (f : n → ℝ) (g : m → ℝ) :
    let T := fromBlocks (1 : Matrix n n ℝ) 0 (-(B₂ * A⁻¹)) (1 : Matrix m m ℝ)
    T * saddlePointMatrix A B₁ B₂ C =
        fromBlocks A B₁ᵀ 0 (saddlePointMatrix A B₁ B₂ C).schurComplement ∧
      T *ᵥ Sum.elim f g = Sum.elim f (g - (B₂ * A⁻¹) *ᵥ f) := by
  exact ⟨lower_elimination_mul_fromBlocks _ _ _ hA,
    by simp [fromBlocks_mulVec, neg_mulVec, sub_eq_add_neg, add_comm]⟩

omit [DecidableEq m] in
/-- **Section 5** of [benzi2005numerical]. Let $A$ be nonsingular. For real vectors $y$ and $v$
on the constraint and primal coordinates, respectively, if $Av=B_1^Ty$, then
$(-S)y=B_2v+Cy$. Thus the reduced matrix need not be formed to apply it. -/
theorem negativeSchurComplement_mulVec (hA : IsUnit A) {y : m → ℝ} {v : n → ℝ}
    (hv : A *ᵥ v = B₁ᵀ *ᵥ y) :
    negativeSchurComplement A B₁ B₂ C *ᵥ y = B₂ *ᵥ v + C *ᵥ y := by
  have hv' : A⁻¹ *ᵥ (B₁ᵀ *ᵥ y) = v := by
    rw [← hv, mulVec_mulVec, nonsing_inv_mul A ((isUnit_iff_isUnit_det A).1 hA), one_mulVec]
  rw [negativeSchurComplement_eq, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv']

end BenziGolubLiesen
