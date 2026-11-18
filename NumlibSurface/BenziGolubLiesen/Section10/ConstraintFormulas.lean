import Numlib.Preconditioner.ConstraintPencil
import Numlib.Preconditioner.BlockSaddle

/-!
# Benzi, Golub and Liesen, Section 10.2: Constraint and indefinite preconditioning

This module formalizes the block formulas for constraint preconditioning in
[benzi2005numerical]. The constraint rows are unchanged, the algebraic basis of
feasibility preservation. Regularization of the zero pressure block leads
to a reduced pressure eigenproblem.

## Main definitions

* Equations (10.15) and (10.20), `BenziGolubLiesen.constraintPreconditioner`: the constraint
  preconditioner with or without a stabilization block.
* `BenziGolubLiesen.constraintProjector`: the projector obtained by eliminating the primal block.

## Main results

* Equation (10.16), `BenziGolubLiesen.inv_constraintPreconditioner_zero`: factor the inverse.
* Equation (10.17), `BenziGolubLiesen.constraintPreconditioned_blocks`: explicit block action.
* `BenziGolubLiesen.constraintPreconditioned_preserves`: the constraint row is invariant.
* `BenziGolubLiesen.constraintPreconditioned_square_case`: for square invertible constraint
  blocks the difference from the identity is square-zero.
* `BenziGolubLiesen.constraintPencil_shift`: stabilized constraint preconditioning shifts
  the eigenvalues of the difference pencil by one.
* Equation (10.22), `BenziGolubLiesen.constraintPencil_normalize`: an inverse square-root
  congruence normalizes the primal block of the preconditioner.
* `BenziGolubLiesen.regularizedConstraintPreconditioned_eq` and
  `BenziGolubLiesen.regularizedConstraintPreconditioned_charpoly`: the block formula and
  characteristic polynomial of the regularized preconditioned matrix.

## Deviations from the source

* **Section 10.2** (qualification). With square invertible $B$, the degree of the minimal
  polynomial is at most two, since the difference from the identity can vanish.

## Not formalized

* The full Krylov feasibility argument, $n-m+2$ grade bound, and the mesh-independent
  convergence and condition estimates.
* The $P$-regular splitting convergence in (10.18), least-squares implementation,
  the quantitative regularization lower edge and the algebraic multiplicity of $1$.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing R]

/-- Equations (10.15) and (10.20) of [benzi2005numerical]. A constraint preconditioner retains
the two constraint blocks and the stabilization block, replacing the primal block by $G$. -/
abbrev constraintPreconditioner (G : Matrix n n R) (B : Matrix m n R) (C : Matrix m m R) :
    Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks G Bᵀ B (-C)

variable {A G : Matrix n n R} {B : Matrix m n R} {C : Matrix m m R}

/-- Equation (10.16) of [benzi2005numerical]. With invertible $G$, the inverse of the
unstabilized constraint preconditioner factors into two block elimination matrices and the
inverse block diagonal matrix. -/
theorem inv_constraintPreconditioner_zero (hG : IsUnit G)
    (hP : IsUnit (constraintPreconditioner G B 0)) :
    (constraintPreconditioner G B 0)⁻¹ =
      fromBlocks (1 : Matrix n n R) (-(G⁻¹ * Bᵀ)) 0 (1 : Matrix m m R) *
        fromBlocks G⁻¹ 0 0 (-(B * G⁻¹ * Bᵀ)⁻¹) *
        fromBlocks (1 : Matrix n n R) 0 (-(B * G⁻¹)) (1 : Matrix m m R) := by
  rw [constraintPreconditioner, neg_zero, inv_fromBlocks_eq hG (by simpa [constraintPreconditioner] using hP)]
  simp [fromBlocks_multiply, Matrix.mul_assoc, nonsing_inv_neg_eq_neg]

/-- For invertible $G$ and $BG^{-1}B^T$, the constraint projector is
$\Pi=G^{-1}B^T(BG^{-1}B^T)^{-1}B$. -/
noncomputable def constraintProjector (G : Matrix n n R) (B : Matrix m n R) : Matrix n n R :=
  G⁻¹ * Bᵀ * (B * G⁻¹ * Bᵀ)⁻¹ * B

/-- The constraint projector leaves $B$ unchanged on its right and is idempotent. -/
theorem constraintProjector_mul_self (hT : IsUnit (B * G⁻¹ * Bᵀ)) :
    B * constraintProjector G B = B ∧
      constraintProjector G B * constraintProjector G B = constraintProjector G B := by
  have hBT : B * constraintProjector G B = B := by
    simp [constraintProjector, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hT)]
  refine ⟨hBT, ?_⟩
  change G⁻¹ * Bᵀ * (B * G⁻¹ * Bᵀ)⁻¹ * B * constraintProjector G B = _
  rw [Matrix.mul_assoc, hBT]
  rfl

/-- Equation (10.17) of [benzi2005numerical]. The blocks of the left-preconditioned matrix
are $(I-\Pi)G^{-1}A+\Pi$, $0$, $(BG^{-1}B^T)^{-1}B(G^{-1}A-I)$ and $I$. -/
theorem constraintPreconditioned_blocks (hG : IsUnit G)
    (hT : IsUnit (B * G⁻¹ * Bᵀ)) :
    (constraintPreconditioner G B 0)⁻¹ * constraintPreconditioner A B 0 =
      fromBlocks ((1 - constraintProjector G B) * G⁻¹ * A + constraintProjector G B) 0
        ((B * G⁻¹ * Bᵀ)⁻¹ * B * (G⁻¹ * A - 1)) 1 := by
  have hP : IsUnit (constraintPreconditioner G B 0) := by
    apply isUnit_of_isUnit_schurComplement
    · simpa using hG
    · simpa [constraintPreconditioner] using hT.neg
  have hTL := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hT)
  rw [inv_constraintPreconditioner_zero hG hP, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [constraintPreconditioner, neg_zero, fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, hTL]
  simp only [constraintProjector, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_neg]
  congr 1 <;> abel

/-- Constraint preconditioning preserves the constraint row. If $v$ is split as $(x,y)$,
the constraint row applied to $P^{-1}\mathcal A v$ gives exactly $Bx-Cy$. The algebraic statement
is $[B,-C]P^{-1}\mathcal A=[B,-C]$. -/
theorem constraintPreconditioned_preserves (hP : IsUnit (constraintPreconditioner G B C)) :
    (constraintPreconditioner G B C *
      ((constraintPreconditioner G B C)⁻¹ * constraintPreconditioner A B C)).toBlocks₂₁ = B ∧
    (constraintPreconditioner G B C *
      ((constraintPreconditioner G B C)⁻¹ * constraintPreconditioner A B C)).toBlocks₂₂ = -C := by
  rw [← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP), Matrix.one_mul]
  exact ⟨toBlocks_fromBlocks₂₁ _ _ _ _, toBlocks_fromBlocks₂₂ _ _ _ _⟩

/-- For square invertible $B$, the projection $\Pi$ in (10.17) equals the identity and
the left-preconditioned matrix is annihilated by $(X-1)^2$. -/
theorem constraintPreconditioned_square_case {B : Matrix n n R} (hG : IsUnit G)
    (hB : IsUnit B) :
    ((constraintPreconditioner G B 0)⁻¹ * constraintPreconditioner A B 0 - 1) ^ 2 = 0 := by
  have hBT : IsUnit Bᵀ := (isUnit_iff_isUnit_det _).mpr
    (by simpa using (isUnit_iff_isUnit_det _).mp hB)
  have hT : IsUnit (B * G⁻¹ * Bᵀ) :=
    (hB.mul (isUnit_nonsing_inv_iff.mpr hG)).mul hBT
  have hproj := (constraintProjector_mul_self hT).1
  have heq : constraintProjector G B = 1 := by
    have hs := congrArg (fun M => B⁻¹ * M) hproj
    simpa [← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hB)] using hs
  rw [constraintPreconditioned_blocks hG hT, heq]
  simp [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    fromBlocks_multiply, pow_two, fromBlocks_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- A pencil eigenvalue $\lambda$ for the same stabilization on both sides corresponds
to the eigenvalue $\lambda-1$ for the difference pencil used in (10.22). -/
theorem constraintPencil_shift {K : Type*} [Field K] (A G : Matrix n n K) (B : Matrix m n K)
    (C : Matrix m m K) (μ : K) (v : n ⊕ m → K) :
    HasPencilEigenvector (constraintPreconditioner A B C) (constraintPreconditioner G B C) μ v ↔
      HasPencilEigenvector (fromBlocks (A - G) 0 0 0) (constraintPreconditioner G B C) (μ - 1) v := by
  have hsum : constraintPreconditioner A B C =
      fromBlocks (A - G) 0 0 0 + constraintPreconditioner G B C := by
    simp [constraintPreconditioner, fromBlocks_add]
  rw [HasPencilEigenvector, HasPencilEigenvector, hsum, add_mulVec]
  rw [sub_smul, one_smul, eq_sub_iff_add_eq]

/-- For regularized constraint preconditioning with unchanged $A$, the preconditioned
matrix is upper block triangular. With $T=BA^{-1}B^T$ its lower diagonal block is
$I-(C+T)^{-1}C$. The upper-right block is $A^{-1}B^T(C+T)^{-1}C$. -/
theorem regularizedConstraintPreconditioned_eq (hA : IsUnit A)
    (hP : IsUnit (constraintPreconditioner A B C)) :
    let T := B * A⁻¹ * Bᵀ
    (constraintPreconditioner A B C)⁻¹ * constraintPreconditioner A B 0 =
      fromBlocks 1 (A⁻¹ * Bᵀ * (C + T)⁻¹ * C) 0 (1 - (C + T)⁻¹ * C) := by
  dsimp only
  have hsum : constraintPreconditioner A B 0 =
      constraintPreconditioner A B C + fromBlocks 0 0 0 C := by
    simp [constraintPreconditioner, fromBlocks_add]
  rw [hsum, Matrix.mul_add, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hP)]
  rw [constraintPreconditioner, inv_fromBlocks_eq hA hP]
  rw [show -C - B * A⁻¹ * Bᵀ = -(C + B * A⁻¹ * Bᵀ) by abel, nonsing_inv_neg_eq_neg]
  simp [← fromBlocks_one, fromBlocks_multiply, fromBlocks_add, sub_eq_add_neg]

/-- The characteristic polynomial of the regularized system separates the primal
factor $(X-1)^n$ and the characteristic polynomial of the reduced pressure block. -/
theorem regularizedConstraintPreconditioned_charpoly (hA : IsUnit A)
    (hP : IsUnit (constraintPreconditioner A B C)) :
    ((constraintPreconditioner A B C)⁻¹ * constraintPreconditioner A B 0).charpoly =
      (Polynomial.X - 1) ^ Fintype.card n *
        (1 - (C + B * A⁻¹ * Bᵀ)⁻¹ * C).charpoly := by
  rw [regularizedConstraintPreconditioned_eq hA hP, charpoly_fromBlocks_zero₂₁, charpoly_one]


/-- Equation (10.22) of [benzi2005numerical]. Let $W=G^{-1/2}$, or more generally
any matrix with $W^T G W=I$. Applying the congruence with
$\operatorname{diag}(W,I)$ to both sides of the shifted pencil gives the normalized
constraint blocks $\widehat B=BW$ and $\widehat E=W^T A W-I$. -/
theorem constraintPencil_normalize (A G W : Matrix n n R) (B : Matrix m n R) (C : Matrix m m R)
    (hW : Wᵀ * G * W = 1) :
    let Q := fromBlocks W 0 0 (1 : Matrix m m R)
    Qᵀ * fromBlocks (A - G) 0 0 (0 : Matrix m m R) * Q =
      fromBlocks (Wᵀ * A * W - 1) 0 0 (0 : Matrix m m R) ∧
    Qᵀ * constraintPreconditioner G B C * Q =
      constraintPreconditioner 1 (B * W) C := by
  dsimp only
  constructor
  · simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_sub, Matrix.sub_mul, hW]
  · simp [constraintPreconditioner, fromBlocks_transpose, fromBlocks_multiply, transpose_mul, hW]

open scoped ComplexOrder in
/-- For the regularization considered in Section 10.2 of [benzi2005numerical],
with $A$ positive definite, $B^H$ injective, and $C$ positive semidefinite, every
eigenvalue of $[A,B^H;B,-C]^{-1}[A,B^H;B,0]$ is real and belongs to $(0,1]$.
The survey's stronger interval $(\beta,1]$ can exclude an attained endpoint: for
$A=B=C=[1]$, the eigenvalue $1/2$ equals $\beta$. -/
theorem regularizedConstraintPreconditioned_spectrum {A : Matrix n n ℂ} {B : Matrix m n ℂ}
    {C : Matrix m m ℂ} (hA : A.PosDef) (hB : Function.Injective Bᴴ.mulVec) (hC : C.PosSemidef)
    {ell : ℂ} (hell : ell ∈ spectrum ℂ ((fromBlocks A Bᴴ B (-C))⁻¹ * fromBlocks A Bᴴ B 0)) :
    ell ∈ Complex.ofReal '' Set.Ioc 0 1 := by
  let T := B * A⁻¹ * Bᴴ
  have hT : T.PosDef := by
    simpa [T] using hA.conjTranspose_mul_inv_mul hB
  have hCT : (C + T).PosDef := hT.posSemidef_add hC
  have hP : IsUnit (fromBlocks A Bᴴ B (-C)) := by
    apply isUnit_of_isUnit_schurComplement
    · simpa using hA.isUnit
    · rw [schurComplement_fromBlocks, show -C - B * A⁻¹ * Bᴴ = -(C + T) by dsimp [T]; abel]
      exact hCT.isUnit.neg
  have heq : ((fromBlocks A Bᴴ B (-C))⁻¹ * fromBlocks A Bᴴ B 0).charpoly =
      (Polynomial.X - 1) ^ Fintype.card n * (1 - (C + T)⁻¹ * C).charpoly := by
    have hsum : fromBlocks A Bᴴ B 0 = fromBlocks A Bᴴ B (-C) + fromBlocks 0 0 0 C := by
      simp [fromBlocks_add]
    rw [hsum, Matrix.mul_add, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hP)]
    rw [inv_fromBlocks_eq hA.isUnit hP,
      show -C - B * A⁻¹ * Bᴴ = -(C + T) by dsimp [T]; abel, nonsing_inv_neg_eq_neg]
    simp only [← fromBlocks_one, fromBlocks_multiply, fromBlocks_add, Matrix.mul_zero,
      zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [charpoly_fromBlocks_zero₂₁, charpoly_one, sub_eq_add_neg (1 : Matrix m m ℂ)]
  have hc := (mem_spectrum_iff_isRoot_charpoly.mp hell)
  rw [heq, Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at hc
  rcases mul_eq_zero.mp hc with hroot | hroot
  · have h := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hroot)
    exact ⟨1, by norm_num, by simpa using h.symm⟩
  · have hT' : 1 - (C + T)⁻¹ * C = (C + T)⁻¹ * T := by
      have hI := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hCT.isUnit)
      rw [Matrix.mul_add] at hI
      rw [← hI, add_sub_cancel_left]
    have hs : ell ∈ pencilSpectrum T (C + T) := by
      rw [pencilSpectrum_eq_spectrum_of_isUnit T hCT.isUnit, ← hT',
        mem_spectrum_iff_isRoot_charpoly]
      exact hroot
    obtain ⟨l, rfl⟩ := pencilSpectrum_subset_range_ofReal_of_posDef hT.1 hCT hs
    have hl := re_pos_of_mem_pencilSpectrum_of_posDef hT hCT hs
    obtain ⟨v, hv, he⟩ := (mem_pencilSpectrum_iff_exists _ _ _).mp hs
    have hquad : (star v ⬝ᵥ (T *ᵥ v)).re = l * (star v ⬝ᵥ ((C + T) *ᵥ v)).re := by
      have h := congrArg (fun w => (star v ⬝ᵥ w).re) he
      change (star v ⬝ᵥ (T *ᵥ v)).re = (star v ⬝ᵥ ((l : ℂ) • ((C + T) *ᵥ v))).re at h
      simpa only [dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul] using h
    have hpos := (Complex.pos_iff.mp (hCT.dotProduct_mulVec_pos hv)).1
    have hnon := (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg v)).1
    have hsum : (star v ⬝ᵥ ((C + T) *ᵥ v)).re =
        (star v ⬝ᵥ (C *ᵥ v)).re + (star v ⬝ᵥ (T *ᵥ v)).re := by
      rw [add_mulVec, dotProduct_add, Complex.add_re]
    refine ⟨l, ⟨by simpa using hl, ?_⟩, rfl⟩
    apply (mul_le_mul_iff_left₀ hpos).mp
    rw [← hquad, one_mul, hsum]
    linarith

end BenziGolubLiesen
