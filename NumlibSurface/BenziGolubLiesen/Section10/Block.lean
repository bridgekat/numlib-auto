import Numlib.Preconditioner.BlockSaddle

/-!
# Benzi, Golub and Liesen, Section 10.1: Block preconditioners

This module formalizes block diagonal and block triangular preconditioning from
[benzi2005numerical], together with the algebraic formulas for Schur complement approximations.
The proofs use `Numlib.Preconditioner.BlockSaddle`.

## Main definitions

* Equations (10.1) and (10.3), `BenziGolubLiesen.blockDiagonalPreconditioner`: the exact or
  approximate block diagonal preconditioner.
* Equation (10.7), `BenziGolubLiesen.scaledBlockDiagonalPreconditioner`: scale the primal and
  Schur blocks separately.
* `BenziGolubLiesen.blockTriangularPreconditioner`: the upper block triangular preconditioner.
* Equations (10.12)–(10.14), `BenziGolubLiesen.elmanSchurInverse`,
  `BenziGolubLiesen.scaledElmanSchurInverse` and
  `BenziGolubLiesen.pressureConvectionDiffusionInverse`: inverse Schur approximations.

## Main results

* Equation (10.2), `BenziGolubLiesen.blockDiagonalPreconditioned_eq`: the result of left
  block diagonal preconditioning.
* `BenziGolubLiesen.blockDiagonalPreconditioned_cubic` and
  `BenziGolubLiesen.blockDiagonalPreconditioned_eigenvalues`: the exact cubic and its spectral
  restriction.
* `BenziGolubLiesen.inv_saddle_eq_blockDiagonalCorrection`: the saddle inverse in terms of the
  ideal preconditioned matrix.
* Equation (10.4), `BenziGolubLiesen.blockDiagonalSplit_eq`: an inexact diagonal splitting.
* Equations (10.5)–(10.6), `BenziGolubLiesen.blockDiagonalSplit_iteration`: the block iteration
  matrix, whose action depends only on the primal component.
* Equation (10.8), `BenziGolubLiesen.scaledBlockDiagonal_transform`: the change of variables
  and row scaling using Cholesky factors.
* `BenziGolubLiesen.blockTriangularPreconditioned_charpoly`: the spectrum and annihilator for exact
  triangular preconditioning.
* Equation (10.11), `BenziGolubLiesen.inv_blockTriangularPreconditioner`: the factored inverse.
* `BenziGolubLiesen.incompleteBlockLU_eq`: explicit blocks of the SIMPLE-type approximation.

## Conventions

* $U=B_1^T$ is the upper-right block, and $B=B_2$ is the lower-left block. The signed Schur
  complement is $S=-BA^{-1}U$ for zero stabilization.

## Deviations from the source

* **Section 10.1.1** (qualification). The exact block diagonal spectrum is contained in the
  three-point set; some points need not occur, for example when one block is empty or $B$ is square.
* **Section 10.1.2** (qualification). The minimal polynomial divides $(X-1)^2$; its degree is not
  always exactly two.
* **Equation (10.8)** (correction). The sign in the lower block row must also multiply its
  right-hand side in the negative-sign variant.

## Not formalized

* Exact diagonalization and eigenvalue multiplicities for the ideal block diagonal case, and
  extension of the ideal spectral analysis to centered and stabilized preconditioners.
* The special-initial-residual MINRES–GMRES equivalence, the stabilized Stokes mesh bounds
  in (10.9)–(10.10), and discretization-specific or empirical convergence claims.
* Frobenius minimization and the mesh-dependent Schur approximation analysis; the Elman normal
  equation and inverse formulas are included.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable [CommRing R]

/-- Equations (10.1) and (10.3) of [benzi2005numerical]: the block diagonal preconditioner
with primal block $A$ and signed Schur block $S$ is $\operatorname{diag}(A,-S)$. -/
abbrev blockDiagonalPreconditioner (A : Matrix n n R) (S : Matrix m m R) :
    Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks A 0 0 (-S)

variable {A D : Matrix n n R} {U : Matrix n m R} {B : Matrix m n R} {S : Matrix m m R}

/-- Equation (10.2) of [benzi2005numerical]. With invertible $A$ and $S$, left preconditioning
by $\operatorname{diag}(A,-S)$ gives $[I,A^{-1}U;-S^{-1}B,0]$. -/
theorem blockDiagonalPreconditioned_eq (hA : IsUnit A) (hS : IsUnit S) :
    (blockDiagonalPreconditioner A S)⁻¹ * fromBlocks A U B 0 =
      fromBlocks 1 (A⁻¹ * U) (-(S⁻¹ * B)) 0 := by
  rw [blockDiagonalPreconditioner, inv_fromBlocks_diag_of_isUnit hA hS.neg, fromBlocks_multiply]
  simp [nonsing_inv_neg_eq_neg, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA)]

private theorem normalized_blocks_mul_eq_one (hS : IsUnit (-B * A⁻¹ * U)) :
    -((-B * A⁻¹ * U)⁻¹ * B) * (A⁻¹ * U) = 1 := by
  have h := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS)
  simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc] using h

/-- For the exact Schur complement $S=-BA^{-1}U$, the preconditioned matrix $M$ in (10.2)
annihilates the cubic $(X-1)(X^2-X-1)$. -/
theorem blockDiagonalPreconditioned_cubic (hA : IsUnit A) (hS : IsUnit (-B * A⁻¹ * U)) :
    let M := (blockDiagonalPreconditioner A (-B * A⁻¹ * U))⁻¹ * fromBlocks A U B 0
    (M - 1) * (M ^ 2 - M - 1) = 0 := by
  dsimp only
  rw [blockDiagonalPreconditioned_eq hA hS]
  exact fromBlocks_one_zero_cubic (normalized_blocks_mul_eq_one hS)

/-- In the real case the roots of the annihilating cubic are $1$ and $(1 \pm \sqrt{5})/2$.
Only the values supported by the sizes of the two blocks need occur. -/
theorem blockDiagonalPreconditioned_eigenvalues {A : Matrix n n ℝ} {U : Matrix n m ℝ}
    {B : Matrix m n ℝ} (hA : IsUnit A) (hS : IsUnit (-B * A⁻¹ * U)) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ
      ((blockDiagonalPreconditioner A (-B * A⁻¹ * U))⁻¹ * fromBlocks A U B 0)) :
    μ = 1 ∨ μ = (1 + Real.sqrt 5) / 2 ∨ μ = (1 - Real.sqrt 5) / 2 := by
  rw [blockDiagonalPreconditioned_eq hA hS] at hμ
  rcases mul_eq_zero.mp (fromBlocks_one_zero_eigenvalue (normalized_blocks_mul_eq_one hS) hμ) with
    h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    have hprod : (μ - (1 + Real.sqrt 5) / 2) * (μ - (1 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    exact (mul_eq_zero.mp hprod).imp sub_eq_zero.mp sub_eq_zero.mp

/-- The inverse of the unstabilized saddle matrix can be recovered by correcting the
diagonal-preconditioned matrix and right multiplying by the inverse preconditioner. -/
theorem inv_saddle_eq_blockDiagonalCorrection (hA : IsUnit A) (hS : IsUnit (-B * A⁻¹ * U)) :
    let S := -B * A⁻¹ * U
    let P := blockDiagonalPreconditioner A S
    let M := P⁻¹ * fromBlocks A U B 0
    (fromBlocks A U B 0)⁻¹ = (M + fromBlocks (A⁻¹ * U * S⁻¹ * B) 0 0 (-1)) * P⁻¹ := by
  dsimp only
  let S := -B * A⁻¹ * U
  let P := blockDiagonalPreconditioner A S
  change (fromBlocks A U B 0)⁻¹ = (P⁻¹ * fromBlocks A U B 0 +
    fromBlocks (A⁻¹ * U * S⁻¹ * B) 0 0 (-1)) * P⁻¹
  have hPP : P * P⁻¹ = 1 := by
    have hP : IsUnit P := isUnit_fromBlocks_zero₂₁.mpr ⟨hA, hS.neg⟩
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)
  calc
    (fromBlocks A U B 0)⁻¹ = (P * (P⁻¹ * fromBlocks A U B 0))⁻¹ := by
      rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    _ = _ := by
      rw [Matrix.mul_inv_rev, blockDiagonalPreconditioned_eq hA hS,
        inv_fromBlocks_diag_one_zero_of_mul_eq_one (normalized_blocks_mul_eq_one hS),
        fromBlocks_add]
      simp [S, sub_eq_add_neg, Matrix.mul_assoc]

/-- Equation (10.4) of [benzi2005numerical]. If $A=D-E$, the approximate block diagonal
preconditioning is the exact preconditioning with primal block $D$ minus the block containing
$D^{-1}E$. The signed block $S$ can be any nonsingular Schur approximation. -/
theorem blockDiagonalSplit_eq (E : Matrix n n R) (hD : IsUnit D) (hS : IsUnit S) :
    (blockDiagonalPreconditioner D S)⁻¹ * fromBlocks (D - E) U B 0 =
      fromBlocks 1 (D⁻¹ * U) (-(S⁻¹ * B)) 0 - fromBlocks (D⁻¹ * E) 0 0 0 := by
  rw [blockDiagonalPreconditioner, inv_fromBlocks_diag_of_isUnit hD hS.neg, fromBlocks_multiply]
  simp [Matrix.mul_add, nonsing_inv_neg_eq_neg, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hD),
    sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

/-- Equations (10.5)–(10.6) of [benzi2005numerical]. With the matching Schur block
$S=-BD^{-1}U$, the iteration matrix $P_1^{-1}P_2$ has zero second block column. Its upper-left
block is $(I+D^{-1}US^{-1}B)D^{-1}E$, so subtracting it from the identity gives the reduced
primal system matrix. -/
theorem blockDiagonalSplit_iteration (E : Matrix n n R) (hS : IsUnit (-B * D⁻¹ * U)) :
    let S := -B * D⁻¹ * U
    (fromBlocks 1 (D⁻¹ * U) (-(S⁻¹ * B)) 0)⁻¹ * fromBlocks (D⁻¹ * E) 0 0 0 =
      fromBlocks ((1 + D⁻¹ * U * S⁻¹ * B) * (D⁻¹ * E)) 0
        (-(S⁻¹ * B * (D⁻¹ * E))) 0 := by
  dsimp only
  rw [inv_fromBlocks_diag_one_zero_of_mul_eq_one (normalized_blocks_mul_eq_one hS),
    fromBlocks_multiply]
  simp [sub_eq_add_neg, Matrix.mul_assoc]

/-- The upper block triangular preconditioner with primal block $A$, upper coupling $U$ and
signed Schur block $S$. -/
abbrev blockTriangularPreconditioner (A : Matrix n n R) (U : Matrix n m R) (S : Matrix m m R) :
    Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks A U 0 S

/-- With the exact Schur complement $S=C-BA^{-1}U$, the characteristic polynomial is
$(X-1)^{n+m}$ and the square of the difference from the identity is zero. -/
theorem blockTriangularPreconditioned_charpoly {C : Matrix m m R} (hA : IsUnit A)
    (hS : IsUnit (C - B * A⁻¹ * U)) :
    let M := (blockTriangularPreconditioner A U (C - B * A⁻¹ * U))⁻¹ * fromBlocks A U B C
    M.charpoly = (Polynomial.X - 1) ^ (Fintype.card n + Fintype.card m) ∧ (M - 1) ^ 2 = 0 :=
  ⟨charpoly_left_preconditioned_fromBlocks_upper hA hS,
    sq_sub_one_left_preconditioned_fromBlocks_upper hA hS⟩

/-- Equation (10.11) of [benzi2005numerical]. The triangular inverse factors into a primal
solve, a signed coupling matrix and a Schur solve. -/
theorem inv_blockTriangularPreconditioner (hA : IsUnit A) (hS : IsUnit S) :
    (blockTriangularPreconditioner A U S)⁻¹ =
      fromBlocks A⁻¹ 0 0 (1 : Matrix m m R) * fromBlocks 1 U 0 (-1) *
        fromBlocks (1 : Matrix n n R) 0 0 (-S⁻¹) := by
  rw [blockTriangularPreconditioner, inv_fromBlocks_upper U hA hS]
  simp [fromBlocks_multiply]

/-- The incomplete block LU product has the same off-diagonal blocks as the saddle matrix.
Its pressure block is $BA^{-1}U+S$, which vanishes for the original SIMPLE choice
$S=-BA^{-1}U$. -/
theorem incompleteBlockLU_eq (hA : IsUnit A) :
    fromBlocks A 0 B S * fromBlocks 1 (A⁻¹ * U) 0 1 =
      fromBlocks A U B (B * A⁻¹ * U + S) := by
  simp [fromBlocks_multiply, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA)]

/-- Equation (10.12) of [benzi2005numerical]. Elman's approximation to the inverse
of the positive-signed Schur block is $(BB^T)^{-1}BAB^T(BB^T)^{-1}$. -/
noncomputable def elmanSchurInverse (A : Matrix n n R) (B : Matrix m n R) : Matrix m m R :=
  (B * Bᵀ)⁻¹ * B * A * Bᵀ * (B * Bᵀ)⁻¹

/-- Equation (10.13) of [benzi2005numerical]. The scaled Elman approximation uses the
two weighted Gram blocks $BM_2^{-2}B^T$ and $BM_1^{-2}B^T$. -/
noncomputable def scaledElmanSchurInverse (A : Matrix n n R) (B : Matrix m n R)
    (M₁ M₂ : Matrix n n R) : Matrix m m R :=
  (B * (M₂⁻¹ ^ 2) * Bᵀ)⁻¹ * B * (M₂⁻¹ ^ 2) * A * M₁⁻¹ * Bᵀ * (B * (M₁⁻¹ ^ 2) * Bᵀ)⁻¹

/-- Equation (10.14) of [benzi2005numerical]. The pressure convection-diffusion approximation
is $M_p^{-1}A_p(BM_u^{-1}B^T)^{-1}$. -/
noncomputable def pressureConvectionDiffusionInverse (B : Matrix m n R)
    (Mₚ Aₚ : Matrix m m R) (Mᵤ : Matrix n n R) : Matrix m m R :=
  Mₚ⁻¹ * Aₚ * (B * Mᵤ⁻¹ * Bᵀ)⁻¹


/-- The signed, scaled block diagonal preconditioner in (10.7) of [benzi2005numerical].
Use $\varepsilon=1$ for the positive definite version and $\varepsilon=-1$ for the
indefinite version. -/
noncomputable def scaledBlockDiagonalPreconditioner (A : Matrix n n ℝ) (S : Matrix m m ℝ)
    (η ε : ℝ) : Matrix (n ⊕ m) (n ⊕ m) ℝ := fromBlocks (η⁻¹ • A) 0 0 (ε • S)

/-- Equation (10.8) of [benzi2005numerical], with the same sign on the lower block row
of the right-hand side. For $A=LL^T$, let $\widetilde B=M^{-1}BL^{-T}$ and transform
the unknowns by $\operatorname{diag}(\eta^{-1}L^T,M^T)$. The left row scaling of the
original equations is $\operatorname{diag}(L^{-1},\varepsilon\eta^{-1}M^{-1})$.
The printed negative-sign variant omits $\varepsilon$ from the lower right-hand side.
The row and unknown transformations give an equivalence of systems, not in general a
similarity with the left-preconditioned matrix in (10.7). -/
theorem scaledBlockDiagonal_transform (L : Matrix n n ℝ) (M : Matrix m m ℝ)
    (B : Matrix m n ℝ) {η : ℝ} (hη : η ≠ 0) (ε : ℝ) (hL : IsUnit L) (hM : IsUnit M) :
    let B' := M⁻¹ * B * Lᵀ⁻¹
    fromBlocks L⁻¹ 0 0 ((ε * η⁻¹) • M⁻¹) * fromBlocks (L * Lᵀ) Bᵀ B 0 =
      fromBlocks (η • 1) B'ᵀ (ε • B') 0 *
        fromBlocks (η⁻¹ • Lᵀ) 0 0 Mᵀ := by
  dsimp only
  have hLt : IsUnit Lᵀ := by simpa only [isUnit_transpose] using hL
  have hMt : IsUnit Mᵀ := by simpa only [isUnit_transpose] using hM
  have hLL := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hL)
  have hLLt := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hLt)
  have hMMt := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hMt)
  have htop : (M⁻¹ * B * Lᵀ⁻¹)ᵀ * Mᵀ = L⁻¹ * Bᵀ := by
    rw [transpose_mul, transpose_mul, transpose_nonsing_inv, transpose_nonsing_inv,
      transpose_transpose]
    simp [Matrix.mul_assoc, hMMt]
  have hbottom : M⁻¹ * B * Lᵀ⁻¹ * Lᵀ = M⁻¹ * B := by
    rw [Matrix.mul_assoc _ Lᵀ⁻¹, hLLt, Matrix.mul_one]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    htop, ← Matrix.mul_assoc L⁻¹ L Lᵀ, hLL, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, hbottom, smul_smul, inv_mul_cancel₀ hη, one_smul,
    mul_comm η⁻¹ ε]

omit [DecidableEq n] in
/-- If $BB^T$ is invertible, the unweighted approximate commutator
$X=(BB^T)^{-1}BAB^T$ satisfies the Frobenius least-squares normal equation
$B(AB^T-B^TX)=0$. -/
theorem elmanCommutator_normalEquation (A : Matrix n n R) (B : Matrix m n R)
    (hB : IsUnit (B * Bᵀ)) :
    B * (A * Bᵀ - Bᵀ * ((B * Bᵀ)⁻¹ * B * A * Bᵀ)) = 0 := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc B Bᵀ]
  simp [← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hB)]

open Polynomial in
/-- Exact block diagonal preconditioning bounds the dimension of the Krylov space by three
for every initial residual. This is the algebraic basis for the three-step GMRES bound. -/
theorem blockDiagonalPreconditioned_krylovGrade {K : Type*} [Field K]
    {A : Matrix n n K} {U : Matrix n m K} {B : Matrix m n K}
    (hA : IsUnit A) (hS : IsUnit (-B * A⁻¹ * U)) (r : n ⊕ m → K) :
    let M := (blockDiagonalPreconditioner A (-B * A⁻¹ * U))⁻¹ * fromBlocks A U B 0
    Krylov.grade (toLinAlgEquiv' M) r ≤ 3 := by
  dsimp only
  let p : K[X] := (X - 1) * (X ^ 2 - (X + 1))
  have hqdeg : (X + 1 : K[X]).degree < 2 := by
    rw [← C_1, degree_X_add_C]
    decide
  have hp1m : (X - 1 : K[X]).Monic := monic_X_sub_C (1 : K)
  have hq : (X ^ 2 - (X + 1) : K[X]).Monic := monic_X_pow_sub hqdeg
  have hp : p.Monic := hp1m.mul hq
  have hdeg : p.natDegree ≤ 3 := by
    change ((X - 1) * (X ^ 2 - (X + 1)) : K[X]).natDegree ≤ 3
    rw [natDegree_mul hp1m.ne_zero hq.ne_zero]
    have h := natDegree_sub_le (X ^ 2 : K[X]) (X + 1)
    rw [natDegree_X_pow] at h
    have hone : (X + 1 : K[X]).natDegree ≤ 1 := by
      calc
        _ ≤ max (X : K[X]).natDegree (1 : K[X]).natDegree := natDegree_add_le _ _
        _ = 1 := by simp
    have hmax : max 2 (X + 1 : K[X]).natDegree = 2 := max_eq_left (hone.trans (by decide))
    rw [hmax] at h
    have hp1 : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
    rw [hp1]
    omega
  refine (krylov_grade_le_of_aeval_eq_zero _ hp.ne_zero ?_ r).trans hdeg
  simpa [p, sub_add_eq_sub_sub] using blockDiagonalPreconditioned_cubic hA hS

open Polynomial in
/-- Exact upper block triangular preconditioning bounds the dimension of every Krylov space by two,
because the preconditioned matrix is annihilated by $(X-1)^2$. -/
theorem blockTriangularPreconditioned_krylovGrade {K : Type*} [Field K]
    {A : Matrix n n K} {U : Matrix n m K} {B : Matrix m n K} {C : Matrix m m K}
    (hA : IsUnit A) (hS : IsUnit (C - B * A⁻¹ * U)) (r : n ⊕ m → K) :
    let M := (blockTriangularPreconditioner A U (C - B * A⁻¹ * U))⁻¹ * fromBlocks A U B C
    Krylov.grade (toLinAlgEquiv' M) r ≤ 2 := by
  dsimp only
  let p : K[X] := (X - 1) ^ 2
  have hp1 : (X - 1 : K[X]).Monic := monic_X_sub_C (1 : K)
  have hdeg : p.natDegree = 2 := by
    rw [show p = (X - 1 : K[X]) ^ 2 from rfl, hp1.natDegree_pow]
    simp [show (X - 1 : K[X]).natDegree = 1 by simpa using natDegree_X_sub_C (1 : K)]
  rw [← hdeg]
  exact krylov_grade_le_of_aeval_eq_zero _ (hp1.pow 2).ne_zero
    (by simpa [p] using (blockTriangularPreconditioned_charpoly hA hS).2) r

end BenziGolubLiesen
