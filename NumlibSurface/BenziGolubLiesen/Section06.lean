import Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve
import Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 6: Null space methods

For a real saddle-point system with a full-row-rank constraint matrix $B$ and $C=0$,
Section 6 of [benzi2005numerical] writes $x=Zv+\hat x$ using a basis $Z$ of $\ker B$
and a particular solution $B\hat x=g$. The reduced matrix is $Z^TAZ$. After finding $x$,
one can recover $y$ from the multiplier normal equations with coefficient $BB^T$. The
proofs use `Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction` and
`Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve`.

## Main definitions

* Section 6, `BenziGolubLiesen.IsNullBasis`: a matrix whose columns form a basis of $\ker B$.
* Equation (6.3), `BenziGolubLiesen.fundamentalNullBasis`: the null basis from pivot columns.

## Main results

* Section 6, `BenziGolubLiesen.nullSpace_feasible_iff`: feasible vectors have unique coordinates
  $x=Zv+\hat x$.
* Equations (6.1) and (6.2), `BenziGolubLiesen.nullSpace_reduced_system_iff`: two reduced
  systems give exactly the original saddle-point solutions after reconstruction.
* Equation (6.1), `BenziGolubLiesen.isUnit_reducedHessian` and
  `BenziGolubLiesen.posDef_reducedHessian`: nonsingularity and, for symmetric $A$,
  positive definiteness under the semidefiniteness and kernel hypotheses.
* Equation (6.2), `BenziGolubLiesen.posDef_multiplierGram` and
  `BenziGolubLiesen.multiplier_normalEquation_iff_isLeastSquares`: the multiplier coefficient is
  positive definite and the equation is the least-squares normal equation.
* Section 6, `BenziGolubLiesen.dual_saddlePoint_schurReduction`: Schur elimination of
  the dual system gives equation (6.1).
* Equation (6.3), `BenziGolubLiesen.isNullBasis_fundamentalNullBasis`: nonsingular pivot columns
  give a null basis.
* Section 6, `BenziGolubLiesen.isNullBasis_of_split_qr`: the last columns of the orthogonal QR
  factor give an orthonormal null basis.
* Equation (6.4), `BenziGolubLiesen.reducedHessian_add_smul_one` and
  `BenziGolubLiesen.reducedHessian_add_smul_one_eq_spectral`: a scalar shift passes through
  orthonormal compression and shifts the eigenvalues of the reduced matrix.

## Deviations from the source

* **Equations (6.1)–(6.2)** (generalization). The equivalence of the equations
  does not require the kernel condition used for uniqueness. See
  `BenziGolubLiesen.nullSpace_reduced_system_iff`.
* **Equation (6.4)** (generalization). The two shift identities use any real $\rho$
  and any matrix $A$ with the stated compression hypotheses. See
  `BenziGolubLiesen.reducedHessian_add_smul_one` and
  `BenziGolubLiesen.reducedHessian_add_smul_one_eq_spectral`.
* **Null basis** (reading). The condition $BZ=0$ is not sufficient for a basis; the text also
  requires that the columns span $\ker B$ and uses their full rank.
* **Equation (6.1), nonsingularity** (correction). The symmetric part $H$ must also be positive
  semidefinite for the stated kernel-intersection test; this is condition C2 of Section 1.1.

## Not formalized

* The graph-specific incidence and cycle-basis results, matrix-tree formula, and complexity
  statements for sparse basis selection require graph and algorithm models separate from the
  exact reduction.
* The mesh-independent conditioning and convergence statements need a uniform operator norm and
  spectral estimate for the constrained discretizations.
-/

noncomputable section

open Matrix WithLp

namespace BenziGolubLiesen

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
variable {A : Matrix n n ℝ} {B : Matrix m n ℝ} {Z : Matrix n k ℝ}

/-- **Section 6** of [benzi2005numerical]. A **null basis** of $B$ is a matrix $Z$ whose
columns are independent and span $\ker B$.

**Reading.** The printed $BZ=0$ follows from the basis condition, but on its own does not
ensure that the columns span $\ker B$. The source also uses the full column rank of $Z$. -/
abbrev IsNullBasis (B : Matrix m n ℝ) (Z : Matrix n k ℝ) : Prop :=
  Matrix.IsNullBasis B Z

omit [Fintype m] in
/-- **Section 6** of [benzi2005numerical]. Given a real null basis $Z$ of $B$ and a particular
solution $\hat x$ of $B\hat x=g$, a real vector $x$ is feasible if and only if
$x=Zv+\hat x$ for exactly one real coordinate vector $v$. -/
theorem nullSpace_feasible_iff (hZ : IsNullBasis B Z) {x xhat : n → ℝ} {g : m → ℝ}
    (hxhat : B *ᵥ xhat = g) :
    B *ᵥ x = g ↔ ∃! v : k → ℝ, x = Z *ᵥ v + xhat :=
  hZ.mulVec_eq_iff_existsUnique hxhat

/-- **Equations (6.1) and (6.2)** of [benzi2005numerical]. Let $B$ have full row rank, $Z$ be a
null basis of $B$, and $\hat x$ satisfy $B\hat x=g$. For real data, the pair $(x,y)$ solves the
saddle-point system with $C=0$ if and only if there is a vector $v$ with
$$x=Zv+\hat x,\qquad Z^TAZv=Z^T(f-A\hat x),\qquad BB^Ty=B(f-Ax).$$

**Generalization.** The source assumes a nonsingular reduced Hessian via a kernel
condition. The equation equivalence holds even when $Z^TAZ$ is singular. -/
theorem nullSpace_reduced_system_iff (hB : B.rank = Fintype.card m) (hZ : IsNullBasis B Z)
    {x xhat f : n → ℝ} {y g : m → ℝ} (hxhat : B *ᵥ xhat = g) :
    saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g ↔
      ∃ v : k → ℝ, x = Z *ᵥ v + xhat ∧
        (Zᵀ * A * Z) *ᵥ v = Zᵀ *ᵥ (f - A *ᵥ xhat) ∧
        (B * Bᵀ) *ᵥ y = B *ᵥ (f - A *ᵥ x) := by
  have hBt : Function.Injective Bᵀ.mulVec := mulVec_injective_iff_rank_eq_card.2
    (by simpa only [rank_transpose] using hB)
  simpa only [saddlePointMatrix, neg_zero] using
    fromBlocks_transpose_zero_mulVec_eq_iff_nullSpace (A := A) hZ hBt hxhat

omit [Fintype m] in
/-- **Equation (6.1)** of [benzi2005numerical], nonsingularity. Let $Z$ be a null basis of $B$,
let the symmetric part $H=(A+A^T)/2$ be positive semidefinite, and suppose
$\ker H\cap\ker B=\{0\}$. Then the reduced matrix $Z^TAZ$ is nonsingular.

**Correction.** The section states the kernel condition but does not repeat the
semidefiniteness assumption (C2 in Section 1.1). The kernel condition alone is insufficient:
if $A=\operatorname{diag}(1,-1)$ and $B=[1\ {-1}]$, then $H$ is invertible, but
$Z=(1,1)^T$ gives $Z^TAZ=0$. -/
theorem isUnit_reducedHessian [DecidableEq k] (hZ : IsNullBasis B Z)
    (hA : (hermitianPart A).PosSemidef)
    (hker : LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    IsUnit (Zᵀ * A * Z) :=
  hZ.isUnit_compress_of_hermitianPart hA hker

omit [Fintype m] in
/-- **Equation (6.1)** of [benzi2005numerical], symmetric case. If $Z$ is a null basis of $B$,
$A$ is symmetric positive semidefinite and $\ker A\cap\ker B=\{0\}$, then the reduced Hessian
$Z^TAZ$ is symmetric positive definite. -/
theorem posDef_reducedHessian (hZ : IsNullBasis B Z) (hA : A.PosSemidef)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    (Zᵀ * A * Z).PosDef :=
  hZ.posDef_compress hA hker

/-- **Equation (6.2)** of [benzi2005numerical], definiteness. For a real matrix $B$ with full
row rank, the multiplier coefficient $BB^T$ is symmetric positive definite. -/
theorem posDef_multiplierGram (hB : B.rank = Fintype.card m) : (B * Bᵀ).PosDef := by
  have hBt : Function.Injective Bᵀ.mulVec := mulVec_injective_iff_rank_eq_card.2
    (by simpa only [rank_transpose] using hB)
  simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    PosDef.conjTranspose_mul_self Bᵀ hBt

/-- **Equation (6.2)** of [benzi2005numerical], least-squares interpretation. For a real
constraint matrix $B$ and residual vector $r=f-Ax$, the equation $BB^Ty=Br$ is equivalent to
$y$ minimizing $\|r-B^Ty\|_2$. The equivalence itself does not require full row rank. -/
theorem multiplier_normalEquation_iff_isLeastSquares [DecidableEq m]
    (r : n → ℝ) (y : m → ℝ) :
    (B * Bᵀ) *ᵥ y = B *ᵥ r ↔ IsLeastSquaresSolution Bᵀ (toLp 2 r) (toLp 2 y) := by
  classical
  rw [isLeastSquaresSolution_iff_normalEquations]
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose, toEuclideanLin_toLp,
    (toLp_injective 2).eq_iff]

omit [Fintype m] in
/-- **Section 6** of [benzi2005numerical], the dual saddle-point problem. For a nonsingular
real $A$, a real matrix $Z$, and real vectors $\hat x,f,w,v$, the dual system
$$\begin{bmatrix}A^{-1}&Z\\ Z^T&0\end{bmatrix}\begin{bmatrix}w\\v\end{bmatrix}
   =\begin{bmatrix}-\hat x\\-Z^Tf\end{bmatrix}$$
is equivalent to $Z^TAZv=Z^T(f-A\hat x)$ together with $A^{-1}w=-\hat x-Zv$.
The first equation is exactly the reduced equation (6.1). -/
theorem dual_saddlePoint_schurReduction [DecidableEq n] (hA : IsUnit A)
    (xhat f w : n → ℝ) (v : k → ℝ) :
    fromBlocks A⁻¹ Z Zᵀ (0 : Matrix k k ℝ) *ᵥ Sum.elim w v =
        Sum.elim (-xhat) (-(Zᵀ *ᵥ f)) ↔
      (Zᵀ * A * Z) *ᵥ v = Zᵀ *ᵥ (f - A *ᵥ xhat) ∧
        A⁻¹ *ᵥ w = -xhat - Z *ᵥ v := by
  rw [fromBlocks_mulVec_eq_iff_schur _ _ _ (isUnit_nonsing_inv_iff.2 hA),
    schurComplement_fromBlocks, nonsing_inv_nonsing_inv A ((isUnit_iff_isUnit_det A).1 hA),
    zero_sub, neg_mulVec, mulVec_neg, sub_neg_eq_add]
  have hneg : -(Zᵀ *ᵥ f) + (Zᵀ * A) *ᵥ xhat = -(Zᵀ *ᵥ (f - A *ᵥ xhat)) := by
    rw [mulVec_sub, mulVec_mulVec, neg_sub]
    abel
  rw [hneg, neg_inj]

/-- **Equation (6.3)** of [benzi2005numerical]. Given real blocks $B_b,B_n$ and the column
permutation $e:m\sqcup k\simeq n$, the **fundamental basis** has coordinates
$\begin{bmatrix}-B_b^{-1}B_n\\I\end{bmatrix}$ in the reordered columns. Returning to
the original coordinates is multiplication by the source's permutation matrix $P$. The
inverse is totalized to zero if $B_b$ is singular. -/
abbrev fundamentalNullBasis [DecidableEq m] [DecidableEq k] (e : m ⊕ k ≃ n)
    (Bb : Matrix m m ℝ) (Bn : Matrix m k ℝ) : Matrix n k ℝ :=
  (fromRows (-(Bb⁻¹ * Bn)) 1).submatrix e.symm id

/-- **Equation (6.3)** of [benzi2005numerical], basis property. Suppose that reordering
the columns of $B$ gives $[B_b\ B_n]$ and $B_b$ is nonsingular. Then
$P\begin{bmatrix}-B_b^{-1}B_n\\I\end{bmatrix}$ is a null basis of $B$, where $P$ returns
vectors to the original coordinate order. -/
theorem isNullBasis_fundamentalNullBasis [DecidableEq m] [DecidableEq k]
    (e : m ⊕ k ≃ n) {Bb : Matrix m m ℝ} {Bn : Matrix m k ℝ}
    (hB : B.submatrix id e = fromCols Bb Bn) (hBb : IsUnit Bb) :
    IsNullBasis B (fundamentalNullBasis e Bb Bn) := by
  have hbasis := isNullBasis_fundamental Bn hBb
  rw [← hB] at hbasis
  simpa [fundamentalNullBasis, submatrix_submatrix] using hbasis.reindex e.symm

/-- **Section 6** of [benzi2005numerical], QR construction. Suppose the real orthogonal
matrix $Q$ is split into its first $m$ columns $Q_1$ and its remaining columns $Q_2$, and
$B^T=Q\begin{bmatrix}R\\0\end{bmatrix}$ with $R$ nonsingular. Then
$Z=Q_2$ is a null basis and $Z^TZ=I$. The conclusion uses nonsingularity of $R$, not its
upper triangular structure. -/
theorem isNullBasis_of_split_qr [DecidableEq m] [DecidableEq k]
    {B : Matrix m (m ⊕ k) ℝ} {Q₁ : Matrix (m ⊕ k) m ℝ} {Q₂ : Matrix (m ⊕ k) k ℝ}
    {R : Matrix m m ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1)
    (hfact : Bᵀ = fromCols Q₁ Q₂ * fromRows R 0) (hR : IsUnit R) :
    IsNullBasis B Q₂ ∧ Q₂ᵀ * Q₂ = 1 :=
  Matrix.isNullBasis_of_split_qr hQ hfact hR

omit [Fintype m] [Fintype k] in
/-- **Equation (6.4)** of [benzi2005numerical], shift of the reduced Hessian. For real matrices
$A,Z$ with $Z^TZ=I$, and any real $\rho$, the compression of $A+\rho I$ is $Z^TAZ+\rho I$.

**Generalization.** The source uses a positive smoothing parameter and a symmetric
primal matrix. The identity needs neither restriction. -/
theorem reducedHessian_add_smul_one [DecidableEq n] [DecidableEq k]
    (hZ : Zᵀ * Z = 1) (ρ : ℝ) :
    Zᵀ * (A + ρ • (1 : Matrix n n ℝ)) * Z = Zᵀ * A * Z + ρ • (1 : Matrix k k ℝ) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hZ]

omit [Fintype m] in
/-- **Equation (6.4)** of [benzi2005numerical], spectral reuse. Let $Z$ have orthonormal
columns, and suppose $Z^TAZ=U\Lambda U^T$ with $UU^T=I$. Then, for any real $\rho$,
$$Z^T(A+\rho I)Z = U(\Lambda+\rho I)U^T.$$
For a diagonal $\Lambda$ this shifts the eigenvalues while retaining the same eigenvectors.

**Generalization.** The source takes a real symmetric matrix with a spectral
decomposition. The identity holds for any such orthogonal factorization, whether or
not $\Lambda$ is diagonal. -/
theorem reducedHessian_add_smul_one_eq_spectral [DecidableEq n] [DecidableEq k]
    (hZ : Zᵀ * Z = 1) {U Λ : Matrix k k ℝ} (hU : U * Uᵀ = 1)
    (hspec : Zᵀ * A * Z = U * Λ * Uᵀ) (ρ : ℝ) :
    Zᵀ * (A + ρ • (1 : Matrix n n ℝ)) * Z = U * (Λ + ρ • (1 : Matrix k k ℝ)) * Uᵀ := by
  rw [reducedHessian_add_smul_one hZ, hspec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hU]

end BenziGolubLiesen
