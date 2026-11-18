import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.LeastSquares.ResidualKKT
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 2.2: Constrained and weighted least squares

The augmented systems in [benzi2005numerical] use a residual variable to avoid
forming the normal equations explicitly. Equality constraints add multiplier
coordinates; covariance weighting replaces the residual identity block by the
covariance, and Tikhonov regularization adds a negative Gram block.
The results use `Numlib.LinearAlgebra.Matrix.LeastSquares.ResidualKKT`.

## Main definitions

* Equation (2.23), `BenziGolubLiesen.equalityLeastSquaresAugmentedMatrix`: the augmented matrix.

## Main results

* Equations (2.21)–(2.23), `BenziGolubLiesen.equalityLeastSquares_iff_augmented`: equality constraints.
* Equation (2.24), `BenziGolubLiesen.weightedLeastSquares_iff_augmented`: positive definite covariance.
* After (2.24), `BenziGolubLiesen.generalizedLeastSquares_iff_augmented`: possibly singular covariance.
* Final paragraph, `BenziGolubLiesen.regularizedLeastSquares_iff_augmented`: Tikhonov regularization.

## Deviations from the source

* **(2.21)** (typo). The objective and the constraints depend on $y$, so minimization is over $y$.
* **Paragraph after (2.24)** (reading). With singular covariance the objective is minimum noise
  norm subject to the factored observation equation, rather than an inverse-weighted norm.
* **(2.21)–(2.24)** (generalization). The equivalences do not need the printed dimension inequalities.

## Not formalized

* **Paragraph after (2.24).** Indefinite weighting requires a separate choice of optimization
  model and existence conditions; the augmented equations alone do not imply a minimum.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m p q k : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype q] [Fintype k]

/-- **Equation (2.23)** of [benzi2005numerical]. For design $G\in\mathbb R^{p\times m}$
and constraint matrix $E\in\mathbb R^{q\times m}$ the **augmented matrix** is
$$\begin{bmatrix}I_p&0&G\\0&0&E\\G^T&E^T&0\end{bmatrix}.$$
It is a symmetric saddle-point matrix with primal coordinates indexed by $p\sqcup q$. -/
abbrev equalityLeastSquaresAugmentedMatrix [DecidableEq p] (G : Matrix p m ℝ)
    (E : Matrix q m ℝ) : Matrix ((p ⊕ q) ⊕ m) ((p ⊕ q) ⊕ m) ℝ :=
  saddlePointMatrix (fromBlocks 1 0 0 0) (fromRows G E)ᵀ (fromRows G E)ᵀ 0

private theorem equalityLeastSquaresAugmentedMatrix_mulVec [DecidableEq p] (G : Matrix p m ℝ)
    (E : Matrix q m ℝ) (r : p → ℝ) (multiplier : q → ℝ) (y : m → ℝ) :
    equalityLeastSquaresAugmentedMatrix G E *ᵥ Sum.elim (Sum.elim r multiplier) y =
      Sum.elim (Sum.elim (r + G *ᵥ y) (E *ᵥ y)) (Gᵀ *ᵥ r + Eᵀ *ᵥ multiplier) := by
  simp only [equalityLeastSquaresAugmentedMatrix, saddlePointMatrix, neg_zero,
    fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec,
    add_zero, transpose_fromRows]
  funext i
  rcases i with (i | i) | i <;> simp [mulVec, dotProduct]

/-- **Equations (2.21)–(2.23)** of [benzi2005numerical]. For real matrices $G,E$ and
compatible data $c,d$, a vector $y$ minimizes $\|c-Gy\|_2$ subject to $Ey=d$ if and
only if there are $r,\lambda$ such that the augmented matrix times $(r,\lambda,y)$
equals $(c,d,0)$.

**Typo.** The minimization subscript in (2.21) is $x$, but both the objective and the
constraint use $y$, which is the vector minimized over here.

**Generalization.** The equivalence also holds when the number of rows of $E$ is not
less than its number of columns. -/
theorem equalityLeastSquares_iff_augmented [DecidableEq p] [DecidableEq q] [DecidableEq m]
    (G : Matrix p m ℝ) (E : Matrix q m ℝ) (c : p → ℝ) (d : q → ℝ) (y : m → ℝ) :
    IsLSESolution G (WithLp.toLp 2 c) E (WithLp.toLp 2 d) (WithLp.toLp 2 y) ↔
      ∃ (r : p → ℝ) (multiplier : q → ℝ),
        equalityLeastSquaresAugmentedMatrix G E *ᵥ Sum.elim (Sum.elim r multiplier) y =
          Sum.elim (Sum.elim c d) (0 : m → ℝ) := by
  simp only [equalityLeastSquaresAugmentedMatrix_mulVec, Sum.elim_eq_iff, and_assoc]
  exact isLSESolution_iff_exists_residual_kkt G E c d y

/-- **Equation (2.24)** of [benzi2005numerical]. For a real design matrix $G$ and a
positive definite covariance $W$, the minimizers of $(f-Gx)^TW^{-1}(f-Gx)$ are exactly
the vectors $x$ occurring in solutions $(r,x)$ of
$\begin{bmatrix}W&G\\G^T&0\end{bmatrix}(r,x)=(f,0)$.

**Generalization.** The equivalence does not require fewer columns than rows in $G$. -/
theorem weightedLeastSquares_iff_augmented [DecidableEq n] (G : Matrix n m ℝ)
    (W : Matrix n n ℝ) (f : n → ℝ) (x : m → ℝ) (hW : W.PosDef) :
    IsMinOn (fun u ↦ (f - G *ᵥ u) ⬝ᵥ (W⁻¹ *ᵥ (f - G *ᵥ u))) Set.univ x ↔
      ∃ r : n → ℝ, saddlePointMatrix W Gᵀ Gᵀ 0 *ᵥ Sum.elim r x =
        Sum.elim f (0 : m → ℝ) := by
  have hobj : weightedRegularizedResidualSq W G f (0 : Matrix n m ℝ) 0 =
      (fun u ↦ (f - G *ᵥ u) ⬝ᵥ (W⁻¹ *ᵥ (f - G *ᵥ u))) := by
    funext u
    simp [weightedRegularizedResidualSq_apply]
  rw [← hobj, isMinOn_weightedRegularizedResidualSq_iff W G f 0 0 x hW le_rfl]
  simp [saddlePointMatrix, fromBlocks_mulVec, Sum.elim_eq_iff]

/-- **Section 2.2** of [benzi2005numerical], singular covariance. Let the design be $G$,
$f$ the observed vector, and $F$ a possibly rank-deficient noise factor. The pair $(x,v)$
minimizes $\|v\|_2$ subject to $Gx+Fv=f$ if and only if there is $r$ such that $(r,x)$
solves the augmented system with covariance $FF^T$, design $G$ and right-hand side $(f,0)$,
and $v=F^T r$.

**Reading.** The source notes that the augmented system extends to singular covariance. The
factored feasible-noise model supplies the optimization problem in that case. -/
theorem generalizedLeastSquares_iff_augmented [DecidableEq n] [DecidableEq m] [DecidableEq k]
    (G : Matrix n m ℝ) (F : Matrix n k ℝ) (f : n → ℝ) (x : m → ℝ) (v : k → ℝ) :
    IsGeneralizedLeastSquaresSolution G F (WithLp.toLp 2 f) (WithLp.toLp 2 x) (WithLp.toLp 2 v) ↔
      ∃ r : n → ℝ, saddlePointMatrix (F * Fᵀ) Gᵀ Gᵀ 0 *ᵥ Sum.elim r x =
        Sum.elim f (0 : m → ℝ) ∧ Fᵀ *ᵥ r = v := by
  simp only [saddlePointMatrix, transpose_transpose, neg_zero, fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, Sum.elim_eq_iff, and_assoc]
  exact isGeneralizedLeastSquaresSolution_iff_exists_residual_kkt G F f x v

/-- **Section 2.2** of [benzi2005numerical], Tikhonov regularization. For data $G,f$,
penalty matrix $L$ and parameter $\gamma>0$, a vector $x$ minimizes
$\|f-Gx\|_2^2+\gamma\|Lx\|_2^2$ if and only if some residual $r$ makes $(r,x)$ a
solution of the augmented system with primal block $I$, coupling $G^T$, dual block
$-\gamma L^T L$, and right-hand side $(f,0)$. -/
theorem regularizedLeastSquares_iff_augmented [DecidableEq n] [DecidableEq k] (G : Matrix n m ℝ)
    (f : n → ℝ) (L : Matrix k m ℝ) {γ : ℝ} (hγ : 0 < γ) (x : m → ℝ) :
    IsMinOn (fun u ↦ ‖WithLp.toLp 2 (f - G *ᵥ u)‖ ^ 2 + γ * ‖WithLp.toLp 2 (L *ᵥ u)‖ ^ 2)
      Set.univ x ↔
      ∃ r : n → ℝ, saddlePointMatrix (1 : Matrix n n ℝ) Gᵀ Gᵀ (γ • (Lᵀ * L)) *ᵥ Sum.elim r x =
        Sum.elim f (0 : m → ℝ) := by
  have hobj : weightedRegularizedResidualSq (1 : Matrix n n ℝ) G f L γ =
      (fun u ↦ ‖WithLp.toLp 2 (f - G *ᵥ u)‖ ^ 2 + γ * ‖WithLp.toLp 2 (L *ᵥ u)‖ ^ 2) := by
    funext u
    rw [weightedRegularizedResidualSq_apply, inv_one, one_mulVec, dotProduct_self_eq_norm_sq]
  rw [← hobj, isMinOn_weightedRegularizedResidualSq_iff 1 G f L γ x PosDef.one hγ.le]
  simp [saddlePointMatrix, fromBlocks_mulVec, Sum.elim_eq_iff, neg_mulVec, smul_mulVec,
    ← sub_eq_add_neg, sub_eq_zero]

end BenziGolubLiesen
