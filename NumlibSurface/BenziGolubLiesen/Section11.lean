import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NoncommRing
import Numlib.DomainDecomposition.LocalResidual
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 11: Multilevel methods

Section 11 of [benzi2005numerical] applies multilevel methods to coupled saddle-point systems.
With restriction $R$, prolongation $P$ and coarse solver $D$, the coarse correction adds
$\alpha PDR(b-Ax)$ to the iterate between two smoothing sweeps. The coarse operator can come
from rediscretization or be constructed as $RAP$. Local patch solves give additive and
multiplicative Vanka smoothing and two-level Schwarz corrections. The proofs use
`Numlib.Multigrid.ResidualCycle` and `Numlib.DomainDecomposition.LocalResidual`.

## Main definitions

* Section 11.1, `BenziGolubLiesen.blockRestriction`: independent transfers for the two blocks.
* Section 11.1, `BenziGolubLiesen.galerkinCoarseMatrix`: the coarse operator $RAP$.
* Section 11.1, `BenziGolubLiesen.twoGridCycle`: the linear two-grid residual-correction cycle.
* Equation (11.1), `BenziGolubLiesen.distributiveRelaxation`: distributive residual correction
  $u+\mathcal{B}\mathcal{S}^{-1}(b-\mathcal{A}u)$.
* Section 11.1, `BenziGolubLiesen.simpleSmoother`: the original SIMPLE distribution and splitting.
* Section 11.1, `BenziGolubLiesen.braessSarazinStep`: the constraint-type correction of (10.18).
* Section 11.1, `BenziGolubLiesen.additiveVanka` and `BenziGolubLiesen.multiplicativeVanka`:
  simultaneous and successive coupled patch corrections.
* Section 11.2, `BenziGolubLiesen.twoLevelAdditiveSchwarz` and
  `BenziGolubLiesen.twoLevelHybridSchwarz`: additive local corrections with a coarse correction
  included additively or applied successively, respectively.

## Main results

* Section 11.1, `BenziGolubLiesen.galerkinCoarseMatrix_isSymm`: $RAR^T$ preserves symmetry.
* Section 11.1, `BenziGolubLiesen.galerkinCoarseMatrix_saddlePoint`: block-diagonal transfers
  preserve the unstabilized saddle block form.
* Section 11.1, `BenziGolubLiesen.twoGridCycle_error`: the error operator is the product of
  the post-smoothing, coarse-correction and pre-smoothing error maps.
* Section 11.1, `BenziGolubLiesen.pairedSmootherCycleMatrix_isSymm`: paired transpose
  smoothing responses and a symmetric coarse response preserve symmetry of the cycle response.
* Section 11.1, `BenziGolubLiesen.twoGridCycle_eq_vCycle`: using one recursive cycle as the
  coarse solver yields a V-cycle.
* Section 11.1, `BenziGolubLiesen.distributiveRelaxation_limit_solves`: a convergent
  distributive iteration with invertible distribution and splitting matrices has a solution limit.
* Section 11.1, `BenziGolubLiesen.distributiveTransform_mul`: a block triangular distribution
  transforms the lower-right block to the Schur complement times the pressure scaling.
* Equation (10.18), `BenziGolubLiesen.braessSarazinStep_eq_eq10_18`: the constraint-type
  correction solves the block splitting equation.

## Implementation notes

* The vectors are real-valued functions on finite index types in the matrix formulas. The linear
  two-level algebra works with independent restriction and prolongation and does not require
  coercivity. Rediscretization corresponds to choosing a coarse operator independently of $RAP$.
* The matrix inverse is Mathlib's nonsingular inverse, equal to zero on singular square matrices.
  A claim about an exact solve assumes nonsingularity of the corresponding matrix.

## Deviations from the source

* **Two-grid procedure** (reading). The six listed steps are a linear residual-correction scheme,
  called FAS in the survey; the formal cycle takes fixed damping and linear responses.
* **Limit of (11.1)** (reading). The limit solves the system; a formula using
  $\mathcal{A}^{-1}$ additionally requires that $\mathcal{A}$ is nonsingular.
* **Pressure-scaled distribution** (reading). The printed $M=-BA^{-1}B^TQ$ is for $C=0$;
  retaining $C$ gives $M=(-BA^{-1}B^T-C)Q$.
* **Hybrid additive-local/coarse correction** (reading). The coarse update in this realization is
  applied after, and to the residual left by, the additive local update.

## Not formalized

* **Section 11.1.** Adaptive damping, nonlinear FAS, and discretization-dependent smoothing,
  complexity and convergence results are not implied by the fixed linear algebra.
* **Section 11.2.** The cited PDE-specific decompositions, boundary conditions, spectral and
  scalability estimates, and the Schöberl–Zulehner comparison to inexact Uzawa require data and
  hypotheses not specified by the survey's overview.
-/

namespace BenziGolubLiesen

open Matrix Multigrid DomainDecomposition

/-! ### Intergrid transfer and coarse solves -/

section Transfer

variable {n m nc mc fine coarse : Type*}

/-- **Section 11.1** of [benzi2005numerical]. The **block restriction** is
$R=\operatorname{diag}(R_x,R_y)$, where $R_x$ and $R_y$ take the two fine-grid blocks to
their respective coarse-grid blocks. -/
def blockRestriction (Rx : Matrix nc n ℝ) (Ry : Matrix mc m ℝ) :
    Matrix (nc ⊕ mc) (n ⊕ m) ℝ :=
  fromBlocks Rx 0 0 Ry

variable [Fintype fine]

/-- **Section 11.1** of [benzi2005numerical]. For a real fine-grid matrix $A$, restriction $R$,
and prolongation $P$, the **Galerkin coarse-grid approximation** is $RAP$. -/
noncomputable def galerkinCoarseMatrix (R : Matrix coarse fine ℝ) (A : Matrix fine fine ℝ)
    (P : Matrix fine coarse ℝ) : Matrix coarse coarse ℝ :=
  R * A * P

/-- **Section 11.1** of [benzi2005numerical]. When the prolongation equals $R^T$, the
Galerkin coarse matrix $RAR^T$ is symmetric if the real fine-grid matrix $A$ is symmetric. -/
theorem galerkinCoarseMatrix_isSymm (R : Matrix coarse fine ℝ) (A : Matrix fine fine ℝ)
    (hA : A.IsSymm) : (galerkinCoarseMatrix R A Rᵀ).IsSymm := by
  change (R * A * Rᵀ)ᵀ = R * A * Rᵀ
  rw [transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

/-- **Section 11.1** of [benzi2005numerical]. The real saddle matrix
$\mathcal A_h=\left[\begin{smallmatrix}A_h&B_h^T\\B_h&0\end{smallmatrix}\right]$ with block
restriction $R=\operatorname{diag}(R_x,R_y)$ and prolongation $R^T$ gives the same coarse block
form, with $A_H=R_xA_hR_x^T$ and $B_H=R_y B_h R_x^T$. -/
theorem galerkinCoarseMatrix_saddlePoint [Fintype n] [Fintype m] (A : Matrix n n ℝ)
    (B : Matrix m n ℝ) (Rx : Matrix nc n ℝ) (Ry : Matrix mc m ℝ) :
    galerkinCoarseMatrix (blockRestriction Rx Ry) (saddlePointMatrix A B B 0)
      (blockRestriction Rx Ry)ᵀ =
        saddlePointMatrix (Rx * A * Rxᵀ) (Ry * B * Rxᵀ) (Ry * B * Rxᵀ) 0 := by
  simp [galerkinCoarseMatrix, blockRestriction, saddlePointMatrix, fromBlocks_transpose,
    fromBlocks_multiply, transpose_mul, Matrix.mul_assoc]

variable [Fintype coarse]

/-- The real matrix transfers $R$ and $P$ act on coordinate vectors by multiplication. -/
noncomputable def matrixTransferPair (R : Matrix coarse fine ℝ) (P : Matrix fine coarse ℝ) :
    TransferPair ℝ (fine → ℝ) (coarse → ℝ) :=
  ⟨R.mulVecLin, P.mulVecLin⟩

/-- In coordinate spaces the Petrov–Galerkin coarse map is multiplication by $RAP$. -/
theorem matrixTransferPair_petrovGalerkinCoarse (A : Matrix fine fine ℝ)
    (R : Matrix coarse fine ℝ) (P : Matrix fine coarse ℝ) :
    (matrixTransferPair R P).petrovGalerkinCoarse A.mulVecLin =
      (galerkinCoarseMatrix R A P).mulVecLin :=
  LinearMap.ext fun vector => by
    simp only [TransferPair.petrovGalerkinCoarse_apply, matrixTransferPair, galerkinCoarseMatrix,
      mulVecLin_apply, ← mulVec_mulVec]

/-- The coarse response with matrix solver $D$ is multiplication by $\alpha PDR$. -/
theorem matrixTransferPair_coarseResponse (R : Matrix coarse fine ℝ) (P : Matrix fine coarse ℝ)
    (D : Matrix coarse coarse ℝ) (α : ℝ) :
    (matrixTransferPair R P).coarseResponse D.mulVecLin α = (α • (P * D * R)).mulVecLin :=
  LinearMap.ext fun vector => by
    simp only [TransferPair.coarseResponse_apply, matrixTransferPair, mulVecLin_apply,
      smul_mulVec, ← mulVec_mulVec]

/-- An exact coarse solve with nonsingular Galerkin matrix $A_H=RAP$ gives a correction
that sets the coarse residual to zero: $R(b-A(x+PA_H^{-1}R(b-Ax)))=0$. -/
theorem galerkinCoarse_residual_eq_zero [DecidableEq coarse] (R : Matrix coarse fine ℝ)
    (A : Matrix fine fine ℝ) (P : Matrix fine coarse ℝ)
    (hcoarse : IsUnit (galerkinCoarseMatrix R A P).det) (rhs iterate : fine → ℝ) :
    R *ᵥ (rhs - A *ᵥ
      (iterate + P *ᵥ ((galerkinCoarseMatrix R A P)⁻¹ *ᵥ (R *ᵥ (rhs - A *ᵥ iterate))))) = 0 := by
  apply (matrixTransferPair R P).restricted_residual_eq_zero A.mulVecLin
  change R *ᵥ (A *ᵥ (P *ᵥ (_ *ᵥ _))) = _
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
    ← galerkinCoarseMatrix, mul_nonsing_inv _ hcoarse, one_mulVec]
  rfl

/-- **Section 11.1** of [benzi2005numerical], steps (i)–(vi). For real fine and coarse spaces,
the **linear two-grid cycle** applies $\nu_1$ pre-smoothing corrections, restricts the fine
residual, solves the coarse problem with a linear solver $D$, adds the prolonged correction
scaled by $\alpha$, then applies $\nu_2$ post-smoothing corrections.

**Reading.** The source calls the printed six-step correction scheme FAS and allows adaptive
$\alpha$. The formal cycle implements those steps with fixed $\alpha$ and linear responses, not
a nonlinear full-approximation scheme. Taking $D=A_H^{-1}$ gives an exact coarse solve when
$A_H$ is nonsingular, whether it comes from rediscretization or from $RAP$. -/
abbrev twoGridCycle {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] :=
  @Multigrid.twoGridStep ℝ E F _ _ _ _ _

/-- For a real fine-grid system with solution $x_*$, the two-grid step with fixed damping
$\alpha$, linear coarse solver $D$ and $\nu_1,\nu_2$ smoothing steps sends $x_*-x$ to
$S_{\rm post}^{\nu_2}(I-\alpha PDRA)S_{\rm pre}^{\nu_1}(x_*-x)$, where
$S_{\rm pre},S_{\rm post}$ are the respective smoothing error operators. -/
theorem twoGridCycle_error (A : Matrix fine fine ℝ) (R : Matrix coarse fine ℝ)
    (P : Matrix fine coarse ℝ) (D : Matrix coarse coarse ℝ) (α : ℝ)
    (pre post : Matrix fine fine ℝ) (nuPre nuPost : ℕ) {rhs solution : fine → ℝ}
    (hsol : A *ᵥ solution = rhs) (iterate : fine → ℝ) :
    solution - twoGridCycle A.mulVecLin (matrixTransferPair R P) D.mulVecLin α
      pre.mulVecLin post.mulVecLin nuPre nuPost rhs iterate =
        (residualError A.mulVecLin post.mulVecLin ^ nuPost *
          residualError A.mulVecLin ((matrixTransferPair R P).coarseResponse D.mulVecLin α) *
          residualError A.mulVecLin pre.mulVecLin ^ nuPre) (solution - iterate) :=
  twoGridStep_error A.mulVecLin (matrixTransferPair R P) D.mulVecLin α
    pre.mulVecLin post.mulVecLin nuPre nuPost hsol iterate

/-- In matrix coordinates the two-grid error operator is
$$ (I-M_{\rm post}A)^{\nu_2}(I-\alpha PDRA)(I-M_{\rm pre}A)^{\nu_1}.$$
For an exact coarse solve on a nonsingular matrix $A_H$, use $D=A_H^{-1}$. -/
theorem twoGridCycle_matrix_error [DecidableEq fine] (A : Matrix fine fine ℝ)
    (R : Matrix coarse fine ℝ) (P : Matrix fine coarse ℝ) (D : Matrix coarse coarse ℝ)
    (α : ℝ) (pre post : Matrix fine fine ℝ) (nuPre nuPost : ℕ) {rhs solution : fine → ℝ}
    (hsol : A *ᵥ solution = rhs) (iterate : fine → ℝ) :
    solution - twoGridCycle A.mulVecLin (matrixTransferPair R P) D.mulVecLin α
      pre.mulVecLin post.mulVecLin nuPre nuPost rhs iterate =
        ((1 - post * A) ^ nuPost * (1 - (α • (P * D * R)) * A) * (1 - pre * A) ^ nuPre) *ᵥ
          (solution - iterate) := by
  rw [twoGridCycle_error A R P D α pre post nuPre nuPost hsol iterate,
    matrixTransferPair_coarseResponse, ← Matrix.toLinAlgEquiv'_apply]
  simp only [map_mul, map_pow, map_sub, map_one, residualError]
  rfl

variable [DecidableEq fine]

/-- For a fine matrix $A$, an aggregate pre-smoothing response $L$ and a coarse response
$M$, the **transpose-paired cycle response** combines the responses $L,M,L^T$ in this order.
Each response acts on the residual left by the preceding correction. -/
noncomputable def pairedSmootherCycleMatrix (A pre coarseResponse : Matrix fine fine ℝ) :
    Matrix fine fine ℝ :=
  let first := pre + coarseResponse * (1 - A * pre)
  first + preᵀ * (1 - A * first)

/-- The transpose-paired cycle matrix represents the combined linear response to the
original residual of the three successive corrections. -/
theorem pairedSmootherCycleMatrix_mulVecLin (A pre coarseResponse : Matrix fine fine ℝ) :
    (pairedSmootherCycleMatrix A pre coarseResponse).mulVecLin =
      combineResponses A.mulVecLin
        (combineResponses A.mulVecLin pre.mulVecLin coarseResponse.mulVecLin) preᵀ.mulVecLin := by
  change Matrix.toLinAlgEquiv' _ = _
  simp only [pairedSmootherCycleMatrix, combineResponses, map_add, map_mul, map_sub, map_one]
  rfl

/-- **Section 11.1** of [benzi2005numerical], symmetry of the cycle response. If the real
fine matrix $A$ and lifted coarse response $M$ are symmetric, then using aggregate
pre-smoothing response $L$ and post-smoothing response $L^T$ gives a symmetric residual
response for the entire cycle. This does not assert symmetry of its error operator. -/
theorem pairedSmootherCycleMatrix_isSymm (A pre coarseResponse : Matrix fine fine ℝ)
    (hA : A.IsSymm) (hcoarse : coarseResponse.IsSymm) :
    (pairedSmootherCycleMatrix A pre coarseResponse).IsSymm := by
  have hsplit : pairedSmootherCycleMatrix A pre coarseResponse =
      pre + preᵀ - preᵀ * A * pre + (1 - preᵀ * A) * coarseResponse * (1 - A * pre) := by
    unfold pairedSmootherCycleMatrix
    noncomm_ring
  rw [hsplit]
  unfold Matrix.IsSymm
  simp only [transpose_add, transpose_sub, transpose_mul, transpose_transpose, transpose_one,
    hA.eq, hcoarse.eq]
  noncomm_ring

end Transfer

/-- **Section 11.1** of [benzi2005numerical]. At level $\ell+1$, a V-cycle correction for a
hierarchy of real spaces equals a two-grid cycle with the level $\ell$ V-cycle from zero as
coarse solver. At level zero the response is the prescribed base solver. -/
theorem twoGridCycle_eq_vCycle {Grid : ℕ → Type*}
    [∀ level, AddCommGroup (Grid level)] [∀ level, Module ℝ (Grid level)]
    (A pre post : ∀ level, Module.End ℝ (Grid level))
    (transfer : ∀ level, TransferPair ℝ (Grid (level + 1)) (Grid level))
    (α : ℕ → ℝ) (nuPre nuPost : ℕ → ℕ) (base : Module.End ℝ (Grid 0))
    (level : ℕ) (rhs iterate : Grid (level + 1)) :
    twoGridCycle (A (level + 1)) (transfer level)
        (vCycleResponse A pre post transfer α nuPre nuPost base level) (α (level + 1))
        (pre (level + 1)) (post (level + 1)) (nuPre (level + 1)) (nuPost (level + 1))
        rhs iterate =
      residualCorrection (A (level + 1))
        (vCycleResponse A pre post transfer α nuPre nuPost base (level + 1)) rhs iterate :=
  (residualCorrection_vCycleResponse_succ A pre post transfer α nuPre nuPost base level
    rhs iterate).symm

/-! ### Distributive and constraint smoothers -/

section Smoothers

variable {idx n m : Type*} [Fintype idx] [DecidableEq idx]

/-- **Equation (11.1)** of [benzi2005numerical]. For real matrices $\mathcal A$,
$\mathcal B$ and $\mathcal S$, the **distributive relaxation** update is
$u+\mathcal B\mathcal S^{-1}(b-\mathcal A u)$. The total inverse gives zero correction if
$\mathcal S$ is singular. -/
noncomputable def distributiveRelaxation (A distribution splitting : Matrix idx idx ℝ)
    (rhs iterate : idx → ℝ) : idx → ℝ :=
  residualCorrection A.mulVecLin (distribution * splitting⁻¹).mulVecLin rhs iterate

/-- **Section 11.1** of [benzi2005numerical]. If $\mathcal A\mathcal B=\mathcal S-\mathcal T$
and the real distribution matrix $\mathcal B$ is nonsingular, then
$\mathcal A=\mathcal S\mathcal B^{-1}-\mathcal T\mathcal B^{-1}$. -/
theorem distributiveSplitting (A distribution splitting remainder : Matrix idx idx ℝ)
    (hdistribution : IsUnit distribution.det) (hsplit : A * distribution = splitting - remainder) :
    A = splitting * distribution⁻¹ - remainder * distribution⁻¹ := by
  rw [← Matrix.sub_mul, ← hsplit, Matrix.mul_nonsing_inv_cancel_right _ _ hdistribution]

/-- Multiplying $x + N(b-Ax)$ by a left inverse $L$ of $N$ gives $(L-A)x+b$. -/
private theorem mulVec_residualCorrection (A left response : Matrix idx idx ℝ)
    (hresponse : left * response = 1) (rhs iterate : idx → ℝ) :
    left *ᵥ residualCorrection A.mulVecLin response.mulVecLin rhs iterate =
      (left - A) *ᵥ iterate + rhs := by
  change left *ᵥ (iterate + response *ᵥ (rhs - A *ᵥ iterate)) = _
  rw [mulVec_add, mulVec_mulVec, hresponse, one_mulVec, sub_mulVec]
  abel

/-- **Equation (11.1)** of [benzi2005numerical], splitting form. For nonsingular real
$\mathcal B,\mathcal S$ and $\mathcal A\mathcal B=\mathcal S-\mathcal T$, the updated
iterate $u'$ satisfies $\mathcal S\mathcal B^{-1}u'=\mathcal T\mathcal B^{-1}u+b$. -/
theorem distributiveRelaxation_eq_splitting (A distribution splitting remainder : Matrix idx idx ℝ)
    (hdistribution : IsUnit distribution.det) (hsplitting : IsUnit splitting.det)
    (hsplit : A * distribution = splitting - remainder) (rhs iterate : idx → ℝ) :
    (splitting * distribution⁻¹) *ᵥ distributiveRelaxation A distribution splitting rhs iterate =
      (remainder * distribution⁻¹) *ᵥ iterate + rhs := by
  have hresponse : (splitting * distribution⁻¹) * (distribution * splitting⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hdistribution,
      Matrix.mul_nonsing_inv _ hsplitting]
  rw [distributiveRelaxation, mulVec_residualCorrection _ _ _ hresponse,
    distributiveSplitting A distribution splitting remainder hdistribution hsplit, sub_sub_cancel]

/-- **Section 11.1** of [benzi2005numerical], consistency of (11.1). For nonsingular real
distribution and splitting matrices, if the iterates of distributive relaxation converge to
$u_*$, then $\mathcal A u_*=b$.

**Reading.** The source describes the limit as $\mathcal A^{-1}b$. Nonsingularity of
$\mathcal A$ is needed for that expression; the limit satisfies the system even if
$\mathcal A$ is singular. -/
theorem distributiveRelaxation_limit_solves (A distribution splitting : Matrix idx idx ℝ)
    (hdistribution : IsUnit distribution.det) (hsplitting : IsUnit splitting.det)
    (rhs start limit : idx → ℝ)
    (hlimit : Filter.Tendsto (fun count =>
      (distributiveRelaxation A distribution splitting rhs)^[count] start)
        Filter.atTop (nhds limit)) : A *ᵥ limit = rhs := by
  let response : Matrix idx idx ℝ := distribution * splitting⁻¹
  have hresp : IsUnit response := (distribution.isUnit_iff_isUnit_det.mpr hdistribution).mul
    ((splitting⁻¹).isUnit_iff_isUnit_det.mpr (isUnit_nonsing_inv_det_iff.2 hsplitting))
  have hcont : Continuous (distributiveRelaxation A distribution splitting rhs) := by
    change Continuous (fun iterate => iterate + response.mulVecLin (rhs - A.mulVecLin iterate))
    exact continuous_id.add (response.mulVecLin.continuous_of_finiteDimensional.comp
      (continuous_const.sub A.mulVecLin.continuous_of_finiteDimensional))
  have hshift : Filter.Tendsto
      (fun count => distributiveRelaxation A distribution splitting rhs
        ((distributiveRelaxation A distribution splitting rhs)^[count] start))
      Filter.atTop (nhds limit) := by
    have h := hlimit.comp (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto (fun count =>
      (distributiveRelaxation A distribution splitting rhs)^[count + 1] start)
      Filter.atTop (nhds limit) at h
    simpa only [Function.iterate_succ_apply'] using h
  have hfixed := tendsto_nhds_unique ((hcont.tendsto limit).comp hlimit) hshift
  exact (residualCorrection_fixed_iff A.mulVecLin response.mulVecLin
    (mulVec_injective_iff_isUnit.mpr hresp) rhs limit).mp hfixed

/-- With nonsingular $\mathcal A$ as well as nonsingular distribution and splitting matrices,
any limit of (11.1) is the unique solution $\mathcal A^{-1}b$. -/
theorem distributiveRelaxation_limit_eq (A distribution splitting : Matrix idx idx ℝ)
    (hA : IsUnit A.det) (hdistribution : IsUnit distribution.det)
    (hsplitting : IsUnit splitting.det)
    (rhs start limit : idx → ℝ)
    (hlimit : Filter.Tendsto (fun count =>
      (distributiveRelaxation A distribution splitting rhs)^[count] start)
        Filter.atTop (nhds limit)) : limit = A⁻¹ *ᵥ rhs := by
  rw [← distributiveRelaxation_limit_solves A distribution splitting hdistribution hsplitting
    rhs start limit hlimit, mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]

variable [Fintype n] [DecidableEq n] [Fintype m]

/-- **Section 11.1** of [benzi2005numerical]. Given real blocks $A,B,Q$, the **distributive
transform** has blocks $I$, $-A^{-1}B^TQ$, $0$, and $Q$ in row order. -/
noncomputable def distributiveTransform (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (Q : Matrix m m ℝ) : Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks 1 (-(A⁻¹ * Bᵀ * Q)) 0 Q

/-- **Section 11.1** of [benzi2005numerical]. For nonsingular real $A$, applying the
$Q$-scaled distributive transform on the right makes the real saddle matrix lower triangular
with lower blocks $B$ and $(-BA^{-1}B^T-C)Q$.

**Reading.** The survey prints the scaled block as $-BA^{-1}B^TQ$, corresponding to $C=0$.
The displayed Lean identity allows general $C$ and specializes to the printed formula. -/
theorem distributiveTransform_mul (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (C Q : Matrix m m ℝ) (hA : IsUnit A.det) :
    saddlePointMatrix A B B C * distributiveTransform A B Q =
      fromBlocks A 0 B ((-(B * A⁻¹ * Bᵀ) - C) * Q) := by
  simp only [saddlePointMatrix, distributiveTransform, fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, add_zero, Matrix.mul_neg, Matrix.neg_mul, Matrix.sub_mul]
  rw [← Matrix.mul_assoc A (A⁻¹ * Bᵀ) Q, Matrix.mul_nonsing_inv_cancel_left _ _ hA, neg_add_cancel]
  simp [Matrix.mul_assoc, sub_eq_add_neg]

variable [DecidableEq m]

/-- **Section 11.1** of [benzi2005numerical]. The original **SIMPLE smoother** uses $D_A$,
the diagonal of the real primal block $A$, and $\widehat S=-BD_A^{-1}B^T$. It uses the
distribution $\left[\begin{smallmatrix}I&-D_A^{-1}B^T\\0&I\end{smallmatrix}\right]$ and the
splitting matrix $\left[\begin{smallmatrix}D_A&0\\B&\widehat S\end{smallmatrix}\right]$
in distributive relaxation for the unstabilized real saddle system. Inverse operations are
totalized and give genuine inverses when the corresponding matrices are nonsingular. -/
noncomputable def simpleSmoother (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (rhs iterate : n ⊕ m → ℝ) : n ⊕ m → ℝ :=
  let diagonalA := Matrix.diagonal A.diag
  distributiveRelaxation (saddlePointMatrix A B B 0) (distributiveTransform diagonalA B 1)
    (fromBlocks diagonalA 0 B (-(B * diagonalA⁻¹ * Bᵀ))) rhs iterate

/-- **Section 11.1** of [benzi2005numerical], referring to (10.18).
The **Braess–Sarazin-type step** for the real unstabilized saddle system applies the inverse
of $M=\left[\begin{smallmatrix}G&B^T\\B&0\end{smallmatrix}\right]$ to the residual and adds the
result. When $M$ is singular the total inverse returns zero correction. -/
noncomputable def braessSarazinStep (A G : Matrix n n ℝ) (B : Matrix m n ℝ)
    (rhs iterate : n ⊕ m → ℝ) : n ⊕ m → ℝ :=
  residualCorrection (saddlePointMatrix A B B 0).mulVecLin
    ((saddlePointMatrix G B B 0)⁻¹).mulVecLin rhs iterate

/-- **Equation (10.18)** of [benzi2005numerical], as a smoother in Section 11.1. If the real
constraint matrix $M=\left[\begin{smallmatrix}G&B^T\\B&0\end{smallmatrix}\right]$ is nonsingular,
the updated iterate $u'$ satisfies
$Mu'=\left[\begin{smallmatrix}G-A&0\\0&0\end{smallmatrix}\right]u+b$. -/
theorem braessSarazinStep_eq_eq10_18 (A G : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hM : IsUnit (saddlePointMatrix G B B 0).det) (rhs iterate : n ⊕ m → ℝ) :
    saddlePointMatrix G B B 0 *ᵥ braessSarazinStep A G B rhs iterate =
      fromBlocks (G - A) 0 0 0 *ᵥ iterate + rhs := by
  have hdiff : saddlePointMatrix G B B 0 - saddlePointMatrix A B B 0 =
      fromBlocks (G - A) 0 0 0 := by
    ext (row | row) (col | col) <;> simp [saddlePointMatrix, Matrix.sub_apply]
  rw [braessSarazinStep, mulVec_residualCorrection _ _ _ (mul_nonsing_inv _ hM), hdiff]

/-- An exact Braess–Sarazin step with nonsingular constraint matrix enforces the constraint
$Bx'=g$ on the updated primal vector $x'$, regardless of the input iterate. -/
theorem braessSarazinStep_constraint (A G : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hM : IsUnit (saddlePointMatrix G B B 0).det) (rhs iterate : n ⊕ m → ℝ) :
    B *ᵥ (braessSarazinStep A G B rhs iterate ∘ Sum.inl) = rhs ∘ Sum.inr := by
  funext pressure
  have h := congrFun (braessSarazinStep_eq_eq10_18 A G B hM rhs iterate) (Sum.inr pressure)
  simpa [saddlePointMatrix, Matrix.fromBlocks_mulVec] using h

end Smoothers

/-! ### Vanka relaxation and domain decomposition -/

section Patches

variable {n m localPrimal localDual fine patch J : Type*}

/-- The Vanka patch formed by embeddings of the primal and dual indices of a cell has a local
saddle operator: the submatrix of the global saddle matrix is obtained by restricting each of
its blocks to the corresponding local row and column indices. -/
theorem vankaPatch_saddlePoint (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ) (C : Matrix m m ℝ)
    (primal : localPrimal ↪ n) (dual : localDual ↪ m) :
    (saddlePointMatrix A B₁ B₂ C).submatrix (primal.sumMap dual) (primal.sumMap dual) =
      saddlePointMatrix (A.submatrix primal primal)
        (B₁.submatrix dual primal) (B₂.submatrix dual primal) (C.submatrix dual dual) := by
  ext (row | row) (col | col) <;> rfl

variable [Fintype fine] [DecidableEq fine]

/-- **Section 11.1** of [benzi2005numerical]. For a real matrix $\mathcal A$ and a Vanka patch
with index embedding $\iota$, its **patch response** is
$$M_i=R_i^T(\mathcal A_{\iota,\iota})^{-1}R_i,$$
where $R_i$ selects the patch coordinates. The response is zero for a singular patch matrix
under the total inverse convention. -/
noncomputable def vankaPatchResponse [Fintype patch] [DecidableEq patch]
    (A : Matrix fine fine ℝ) (embed : patch ↪ fine) : Module.End ℝ (fine → ℝ) :=
  let R : Matrix patch fine ℝ := coordinateRestriction embed
  exactLocalResponse A.mulVecLin (matrixTransferPair R Rᵀ)

/-- The patch response multiplies the fine residual by $R_i^T A_i^{-1} R_i$, with $A_i$
the principal submatrix on patch $i$. -/
theorem vankaPatchResponse_eq_mulVecLin [Fintype patch] [DecidableEq patch]
    (A : Matrix fine fine ℝ) (embed : patch ↪ fine) :
    vankaPatchResponse A embed =
      ((coordinateRestriction embed)ᵀ * (A.submatrix embed embed)⁻¹ *
        coordinateRestriction embed).mulVecLin := by
  let R : Matrix patch fine ℝ := coordinateRestriction embed
  have hgal : galerkinCoarseMatrix R A Rᵀ = A.submatrix embed embed :=
    coordinateRestriction_mul_mul_transpose embed A
  have hinverse : Ring.inverse (A.submatrix embed embed).mulVecLin =
      ((A.submatrix embed embed)⁻¹).mulVecLin := by
    rw [nonsing_inv_eq_ringInverse]
    exact (map_ringInverse Matrix.toLinAlgEquiv' (A.submatrix embed embed)).symm
  change exactLocalResponse A.mulVecLin (matrixTransferPair R Rᵀ) = _
  rw [exactLocalResponse, matrixTransferPair_petrovGalerkinCoarse, hgal, hinverse,
    matrixTransferPair_coarseResponse, one_smul]

/-- An undamped exact Vanka update on a nonsingular patch annihilates the residual on that patch. -/
theorem vankaPatch_residual_eq_zero [Fintype patch] [DecidableEq patch]
    (A : Matrix fine fine ℝ) (embed : patch ↪ fine)
    (hpatch : IsUnit (A.submatrix embed embed).det) (rhs iterate : fine → ℝ) :
    (rhs - A *ᵥ residualCorrection A.mulVecLin (vankaPatchResponse A embed) rhs iterate) ∘ embed
      = 0 := by
  let R : Matrix patch fine ℝ := coordinateRestriction embed
  have hgal : galerkinCoarseMatrix R A Rᵀ = A.submatrix embed embed :=
    coordinateRestriction_mul_mul_transpose embed A
  rw [← coordinateRestriction_mulVec embed]
  apply restricted_residual_exactLocalResponse A.mulVecLin (matrixTransferPair R Rᵀ)
  rw [matrixTransferPair_petrovGalerkinCoarse, hgal]
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mpr hpatch).map Matrix.toLinAlgEquiv'

variable {Cell : J → Type*} [∀ cell, Fintype (Cell cell)] [∀ cell, DecidableEq (Cell cell)]

/-- **Sections 11.1–11.2** of [benzi2005numerical]. **Additive Vanka** for a finite collection
of coordinate patches solves each local problem on the same old residual $b-\mathcal A u$
and adds the sum of the extended corrections, each scaled by its patch weight $\omega_i$.
The patch solve uses the total matrix inverse. -/
noncomputable def additiveVanka [Fintype J] (A : Matrix fine fine ℝ)
    (embed : ∀ cell, Cell cell ↪ fine) (weight : J → ℝ) (rhs iterate : fine → ℝ) : fine → ℝ :=
  residualCorrection A.mulVecLin (additiveResponse (fun cell => vankaPatchResponse A (embed cell))
    weight) rhs iterate

/-- An additive Vanka update adds $\sum_i \omega_i M_i(b-\mathcal A u)$ to the input iterate. -/
theorem additiveVanka_apply [Fintype J] (A : Matrix fine fine ℝ)
    (embed : ∀ cell, Cell cell ↪ fine) (weight : J → ℝ) (rhs iterate : fine → ℝ) :
    additiveVanka A embed weight rhs iterate =
      iterate + ∑ cell, weight cell • vankaPatchResponse A (embed cell) (rhs - A *ᵥ iterate) :=
  residualCorrection_additiveResponse A.mulVecLin
    (fun cell => vankaPatchResponse A (embed cell)) weight rhs iterate

/-- **Section 11.1** of [benzi2005numerical]. **Multiplicative Vanka** applies the extended,
damped Vanka patch response to the current residual at each visit in the specified order.
An empty order performs no corrections; repeated visits are permitted. -/
noncomputable def multiplicativeVanka (A : Matrix fine fine ℝ)
    (embed : ∀ cell, Cell cell ↪ fine) (weight : J → ℝ) (order : List J)
    (rhs iterate : fine → ℝ) : fine → ℝ :=
  multiplicativeSweep A.mulVecLin (fun cell => vankaPatchResponse A (embed cell)) weight
    rhs order iterate

/-- Given an exact solution, the multiplicative Vanka error propagates by the ordered product of
$I-\omega_i M_i \mathcal A$, with the first visit contributing the rightmost factor. -/
theorem multiplicativeVanka_error (A : Matrix fine fine ℝ)
    (embed : ∀ cell, Cell cell ↪ fine) (weight : J → ℝ) (order : List J)
    {rhs solution : fine → ℝ} (hsol : A *ᵥ solution = rhs) (iterate : fine → ℝ) :
    solution - multiplicativeVanka A embed weight order rhs iterate =
      multiplicativeSweepError A.mulVecLin (fun cell => vankaPatchResponse A (embed cell))
        weight order (solution - iterate) :=
  multiplicativeSweep_error A.mulVecLin _ weight hsol order iterate

end Patches

section Schwarz

variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

/-- **Section 11.2** of [benzi2005numerical]. The **two-level additive Schwarz update** adds
the correction from the lifted coarse response $M_0$ and the corrections from all the
lifted local responses $M_i$ to the current iterate. They act on the same residual, so the
response is $M_0+\sum_i\omega_i M_i$. The local subdomains may overlap. -/
noncomputable def twoLevelAdditiveSchwarz (A coarseResponse : Module.End ℝ E)
    (localResponse : J → Module.End ℝ E) (weight : J → ℝ) (rhs iterate : E) : E :=
  residualCorrection A (coarseResponse + additiveResponse localResponse weight) rhs iterate

/-- **Section 11.2** of [benzi2005numerical]. A **two-level hybrid Schwarz update** applies the
weighted sum of the lifted local responses to the old residual and the lifted coarse response
to the resulting residual.

**Reading.** The survey describes the local solves as additive and the coarse solve as
multiplicative. Here the additive local update is applied first, followed by the coarse update;
the definition does not specify Neumann boundary operators or a balanced preconditioner. -/
noncomputable def twoLevelHybridSchwarz (A coarseResponse : Module.End ℝ E)
    (localResponse : J → Module.End ℝ E) (weight : J → ℝ) (rhs iterate : E) : E :=
  residualCorrection A (combineResponses A (additiveResponse localResponse weight) coarseResponse)
    rhs iterate

/-- The hybrid update is the composition of the additive local and coarse corrections. -/
theorem twoLevelHybridSchwarz_eq (A coarseResponse : Module.End ℝ E)
    (localResponse : J → Module.End ℝ E) (weight : J → ℝ) (rhs iterate : E) :
    twoLevelHybridSchwarz A coarseResponse localResponse weight rhs iterate =
      residualCorrection A coarseResponse rhs
        (residualCorrection A (additiveResponse localResponse weight) rhs iterate) :=
  residualCorrection_combineResponses A _ coarseResponse rhs iterate

/-- If $Ax_*=b$, the hybrid error operator is $(I-M_0A)(I-(\sum_i\omega_i M_i)A)$. -/
theorem twoLevelHybridSchwarz_error (A coarseResponse : Module.End ℝ E)
    (localResponse : J → Module.End ℝ E) (weight : J → ℝ)
    {rhs solution : E} (hsol : A solution = rhs) (iterate : E) :
    solution - twoLevelHybridSchwarz A coarseResponse localResponse weight rhs iterate =
      (residualError A coarseResponse * residualError A (additiveResponse localResponse weight))
        (solution - iterate) := by
  rw [twoLevelHybridSchwarz_eq, residualCorrection_error A _ hsol,
    residualCorrection_error A _ hsol, Module.End.mul_apply]

end Schwarz

end BenziGolubLiesen
