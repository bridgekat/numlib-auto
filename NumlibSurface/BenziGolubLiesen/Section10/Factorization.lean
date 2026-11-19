import Numlib.LinearAlgebra.Matrix.Block
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Benzi, Golub and Liesen, Section 10.4: Approximate and incomplete factorization methods

This module formalizes the factorized preconditioners of [benzi2005numerical]. The Saunders
and Schilders formulas reorganize a constraint matrix using an invertible square part of
the constraint. Signed Cholesky yields an exact split preconditioner when its factors are
used without dropping.

## Main definitions

* Section 10.4, `BenziGolubLiesen.absolutePivotPreconditioner`: replace the pivot eigenvalues
  by their absolute values in an orthogonally diagonalized pivot factor.
* Equation (10.33), `BenziGolubLiesen.repartitionedDiagonalPreconditioner`: keep the trailing
  block, take the diagonal of the leading block, and discard the couplings.

## Main results

* Equation (10.34), `BenziGolubLiesen.schilders_factorization`: Schilders' factorization.
* Equation (10.35), `BenziGolubLiesen.saunders_factorization`: the null-space factorization.
* Equation (10.36), `BenziGolubLiesen.signedCholesky_factorization` and
  `BenziGolubLiesen.exists_signedCholesky`: the factorization and its existence.
* `BenziGolubLiesen.signedCholesky_split`: split preconditioning yields $\operatorname{diag}(I,-I)$.

## Deviations from the source

* **Absolute pivot and signed Cholesky formulas** (reading). The formulas are stated as
  algebraic identities for supplied factors. The SPD construction supplies an invertible
  signed Cholesky factor and the exact split gives the signature matrix.
* **Equation (10.34)** (correction). The transpose-congruence formula requires symmetric
  $G_{11}$ and $G_{21}=G_{12}^T$. The algebraic identity here still permits nonsymmetric
  $G_{22}$. See `BenziGolubLiesen.schilders_factorization`.
* **Equation (10.35)** (generalization). The congruence needs symmetry of $G_{11}$ and
  transposed off-diagonal blocks, but $G_{22}$ may be nonsymmetric. See
  `BenziGolubLiesen.saunders_factorization`.

## Not formalized

* Sparse pivot selection, the existence of incomplete factors for a given dropping rule,
  and fill-in, stability and performance claims.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m k R : Type*} [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq k] [CommRing R]

/-- If the symmetric pivot factor is diagonalized into orthonormal eigenvectors $V$
and pivot eigenvalues $d$, replace $d_i$ by $|d_i|$ and retain the congruence factors.

**Generalization.** The algebraic definition accepts arbitrary matrices. The absolute pivot
construction in the source uses an orthonormal pivot eigenbasis. -/
noncomputable def absolutePivotPreconditioner (Q L V : Matrix n n ℝ) (d : n → ℝ) :
    Matrix n n ℝ :=
  Qᵀ * L * (V * diagonal (fun i ↦ |d i|) * Vᵀ) * Lᵀ * Q

/-- The approximate preconditioner associated with (10.33) of [benzi2005numerical]
retains the trailing block $A_{22}$ and the diagonal of the leading block $A_{11}$. -/
def repartitionedDiagonalPreconditioner (A₁₁ : Matrix n n R) (A₂₂ : Matrix m m R) :
    Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks (diagonal A₁₁.diag) 0 0 A₂₂

/-- Equation (10.35) of [benzi2005numerical]. If the first constraint block $B_1$ is
nonsingular, put $W=B_1^{-1}B_2$ and $Z=[-W;I]$. The constraint matrix is the
congruence of a matrix with a zero second constraint block and middle block $Z^TGZ$.
Its middle/first off-diagonal block is the transpose of $G_{12}-G_{11}W$.

**Generalization.** The source assumes symmetric $G$. The formula continues to hold for
nonsymmetric $G_{22}$ because that block contributes only to the congruence-compressed
block $Z^TGZ$. -/
theorem saunders_factorization (G₁₁ : Matrix m m R) (G₁₂ : Matrix m k R) (G₂₂ : Matrix k k R)
    (B₁ : Matrix m m R) (B₂ : Matrix m k R) (hB : IsUnit B₁) (hG : G₁₁ᵀ = G₁₁) :
    let G := fromBlocks G₁₁ G₁₂ G₁₂ᵀ G₂₂
    let B := fromCols B₁ B₂
    let W := B₁⁻¹ * B₂
    let Z := fromRows (-W) 1
    let X := G₁₂ - G₁₁ * W
    let T := fromBlocks (fromBlocks 1 W 0 1) 0 0 (1 : Matrix m m R)
    let B₀ := fromCols B₁ (0 : Matrix m k R)
    fromBlocks G Bᵀ B (0 : Matrix m m R) =
      Tᵀ * fromBlocks (fromBlocks G₁₁ X Xᵀ (Zᵀ * G * Z)) B₀ᵀ B₀ 0 * T := by
  dsimp only
  have hW : B₁ * (B₁⁻¹ * B₂) = B₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hB), Matrix.one_mul]
  have hWt : B₂ᵀ * (B₁⁻¹ᵀ * B₁ᵀ) = B₂ᵀ := by
    rw [← Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, hW]
  simp only [fromBlocks_transpose, transpose_zero, transpose_one, transpose_fromCols,
    fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks, hW,
    transpose_sub, transpose_mul, hG, transpose_fromRows, transpose_neg,
    fromCols_mul_fromRows, Matrix.mul_neg, Matrix.neg_mul, hWt,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  congr 2 <;> try abel

/-- Equation (10.34) of [benzi2005numerical]. For invertible $B_1$ and $L_2$ and symmetric
$G_{11}$, the Schilders factorization has a pivot block $[D_1,0,I;0,D_2,0;I,0,0]$.
The displayed formula for $D_1$ is grouped with the inverse factors on the outside.

**Correction.** The printed partition lists $G_{12}$ and $G_{21}$ separately. The formula
computes $E$ from $G_{21}$ and uses $E^T$ on the other side, which requires transposed
off-diagonal blocks and symmetric $G_{11}$. With scalar blocks $B_1=L_2=1$,
$B_2=L_1=G_{11}=G_{22}=G_{21}=0$ and $G_{12}=1$, the printed factors reconstruct
$G_{12}=0$. The Lean formula makes the required equalities explicit. -/
theorem schilders_factorization {G₁₁ : Matrix m m R} (G₁₂ : Matrix m k R)
    (G₂₂ : Matrix k k R) {B₁ : Matrix m m R} (B₂ : Matrix m k R)
    (L₁ : Matrix m m R) {L₂ : Matrix k k R}
    (hB : IsUnit B₁) (hL : IsUnit L₂) (hG : G₁₁ᵀ = G₁₁) :
    let D₁ := B₁⁻¹ᵀ * (G₁₁ - L₁ * B₁ - B₁ᵀ * L₁ᵀ) * B₁⁻¹
    let E := G₁₂ᵀ * B₁⁻¹ - B₂ᵀ * D₁ - B₂ᵀ * L₁ᵀ * B₁⁻¹
    let D₂ := L₂⁻¹ * (G₂₂ - B₂ᵀ * D₁ * B₂ - E * B₂ - B₂ᵀ * Eᵀ) * L₂⁻¹ᵀ
    let B := fromCols B₁ B₂
    let L := fromBlocks (fromBlocks B₁ᵀ 0 B₂ᵀ L₂) (fromRows L₁ E) 0 (1 : Matrix m m R)
    let D := fromBlocks (fromBlocks D₁ 0 0 D₂) (fromRows (1 : Matrix m m R) 0)
      (fromCols (1 : Matrix m m R) 0) (0 : Matrix m m R)
    fromBlocks (fromBlocks G₁₁ G₁₂ G₁₂ᵀ G₂₂) Bᵀ B (0 : Matrix m m R) = L * D * Lᵀ := by
  let D₁ := B₁⁻¹ᵀ * (G₁₁ - L₁ * B₁ - B₁ᵀ * L₁ᵀ) * B₁⁻¹
  let E := G₁₂ᵀ * B₁⁻¹ - B₂ᵀ * D₁ - B₂ᵀ * L₁ᵀ * B₁⁻¹
  let D₂ := L₂⁻¹ * (G₂₂ - B₂ᵀ * D₁ * B₂ - E * B₂ - B₂ᵀ * Eᵀ) * L₂⁻¹ᵀ
  have hBi := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hB)
  have hLi := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hL)
  have hBit : B₁ᵀ * B₁⁻¹ᵀ = 1 := by rw [← transpose_mul, hBi, transpose_one]
  have hLit : L₂⁻¹ᵀ * L₂ᵀ = 1 := by rw [← transpose_mul, hLi, transpose_one]
  have hD₁ : B₁ᵀ * D₁ * B₁ = G₁₁ - L₁ * B₁ - B₁ᵀ * L₁ᵀ := by
    dsimp only [D₁]
    simp only [← Matrix.mul_assoc, hBit, Matrix.one_mul]
    simp [Matrix.mul_assoc, hBi]
  have hD₂ : L₂ * D₂ * L₂ᵀ = G₂₂ - B₂ᵀ * D₁ * B₂ - E * B₂ - B₂ᵀ * Eᵀ := by
    change L₂ * (L₂⁻¹ * _ * L₂⁻¹ᵀ) * L₂ᵀ = _
    simp only [← Matrix.mul_assoc, hLi, Matrix.one_mul]
    rw [Matrix.mul_assoc _ L₂⁻¹ᵀ, hLit, Matrix.mul_one]
  have hDs : D₁ᵀ = D₁ := by
    dsimp [D₁]
    simp only [transpose_mul, transpose_sub, transpose_transpose, hG, Matrix.mul_assoc]
    congr 2
    abel
  have hE : E * B₁ = G₁₂ᵀ - B₂ᵀ * D₁ * B₁ - B₂ᵀ * L₁ᵀ := by
    dsimp only [E]
    simp only [Matrix.sub_mul, Matrix.mul_assoc, hBi, Matrix.mul_one]
  have hEt : B₁ᵀ * Eᵀ = G₁₂ - B₁ᵀ * D₁ * B₂ - L₁ * B₂ := by
    simpa only [transpose_mul, transpose_sub, transpose_transpose, hDs, Matrix.mul_assoc] using
      congrArg Matrix.transpose hE
  change fromBlocks _ _ _ _ =
    fromBlocks (fromBlocks B₁ᵀ 0 B₂ᵀ L₂) (fromRows L₁ E) 0 (1 : Matrix m m R) *
      fromBlocks (fromBlocks D₁ 0 0 D₂) (fromRows (1 : Matrix m m R) 0)
        (fromCols (1 : Matrix m m R) 0) 0 *
      (fromBlocks (fromBlocks B₁ᵀ 0 B₂ᵀ L₂) (fromRows L₁ E) 0 (1 : Matrix m m R))ᵀ
  simp only [fromBlocks_transpose, transpose_fromRows, transpose_fromCols, transpose_transpose,
    transpose_zero, transpose_one, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    fromRows_mul_fromCols, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks,
    fromBlocks_add, Matrix.add_mul]
  simp only [hD₁, hD₂, hE, hEt, Matrix.mul_assoc]
  congr 2 <;> abel

omit [DecidableEq n] [DecidableEq m] in
/-- Equation (10.36) of [benzi2005numerical]. If $A=L_{11}L_{11}^T$,
$B=L_{21}L_{11}^T$ and $C+L_{21}L_{21}^T=L_{22}L_{22}^T$, the two displayed
triangular factors multiply to the symmetric saddle-point matrix.

**Generalization.** The identity needs only the prescribed diagonal-block relation for the
supplied factors. -/
theorem signedCholesky_factorization (L₁₁ : Matrix n n R) (L₂₁ : Matrix m n R)
    (L₂₂ C : Matrix m m R) (hC : C + L₂₁ * L₂₁ᵀ = L₂₂ * L₂₂ᵀ) :
    fromBlocks (L₁₁ * L₁₁ᵀ) (L₂₁ * L₁₁ᵀ)ᵀ (L₂₁ * L₁₁ᵀ) (-C) =
      fromBlocks L₁₁ 0 L₂₁ L₂₂ * fromBlocks L₁₁ᵀ L₂₁ᵀ 0 (-L₂₂ᵀ) := by
  simp [fromBlocks_multiply, transpose_mul, ← hC, add_comm]

/-- The signed Cholesky construction exists without pivoting for positive definite $A$,
full row rank $B$ and positive semidefinite $C$. The lower factor is invertible. -/
theorem exists_signedCholesky (A : Matrix n n ℝ) (B : Matrix m n ℝ) (C : Matrix m m ℝ)
    (hA : A.PosDef) (hB : Function.Injective Bᵀ.mulVec) (hC : C.PosSemidef)
    [LinearOrder n] [LinearOrder m] :
    ∃ (L₁₁ : Matrix n n ℝ) (L₂₁ : Matrix m n ℝ) (L₂₂ : Matrix m m ℝ),
      L₁₁.IsLowerTriangular ∧ L₂₂.IsLowerTriangular ∧ IsUnit (fromBlocks L₁₁ 0 L₂₁ L₂₂) ∧
      fromBlocks A Bᵀ B (-C) =
        fromBlocks L₁₁ 0 L₂₁ L₂₂ * fromBlocks L₁₁ᵀ L₂₁ᵀ 0 (-L₂₂ᵀ) := by
  let L₁₁ := cholesky A
  let L₂₁ := B * L₁₁ᵀ⁻¹
  have hAA : L₁₁ * L₁₁ᵀ = A := by
    simpa [L₁₁, conjTranspose_eq_transpose_of_trivial] using
      (isCholesky_cholesky hA).conjTranspose_mul_self
  have hL₁₁ : IsUnit L₁₁ := isUnit_of_mul_isUnit_left (hAA ▸ hA.isUnit)
  have hL₁₁t : IsUnit L₁₁ᵀ := by simpa using hL₁₁
  have hLB : L₂₁ * L₁₁ᵀ = B := by
    simp [L₂₁, Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hL₁₁t)]
  have hGram : L₂₁ * L₂₁ᵀ = B * A⁻¹ * Bᵀ := by
    rw [← hAA, Matrix.mul_inv_rev]
    simp [L₂₁, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc]
  have hGram' : (B * A⁻¹ * Bᵀ).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_inv_mul hB
  have hS : (C + L₂₁ * L₂₁ᵀ).PosDef := by
    rw [hGram]
    exact hGram'.posSemidef_add hC
  let L₂₂ := cholesky (C + L₂₁ * L₂₁ᵀ)
  have hSS : L₂₂ * L₂₂ᵀ = C + L₂₁ * L₂₁ᵀ := by
    simpa [L₂₂, conjTranspose_eq_transpose_of_trivial] using
      (isCholesky_cholesky hS).conjTranspose_mul_self
  have hL₂₂ : IsUnit L₂₂ := isUnit_of_mul_isUnit_left (hSS ▸ hS.isUnit)
  refine ⟨L₁₁, L₂₁, L₂₂, isLowerTriangular_cholesky _, isLowerTriangular_cholesky _,
    isUnit_fromBlocks_zero₁₂.mpr ⟨hL₁₁, hL₂₂⟩, ?_⟩
  simpa [hAA, hLB] using signedCholesky_factorization L₁₁ L₂₁ L₂₂ C hSS.symm

/-- Exact split preconditioning by the signed Cholesky lower factor leaves only the
signature diagonal $\operatorname{diag}(I,-I)$.

**Reading.** The declaration gives the signature matrix obtained by exact congruence with an
invertible factor. -/
theorem signedCholesky_split (L₁₁ : Matrix n n R) (L₂₁ : Matrix m n R)
    (L₂₂ C : Matrix m m R) (hC : C + L₂₁ * L₂₁ᵀ = L₂₂ * L₂₂ᵀ)
    (hL : IsUnit (fromBlocks L₁₁ 0 L₂₁ L₂₂)) :
    let L := fromBlocks L₁₁ 0 L₂₁ L₂₂
    let B := L₂₁ * L₁₁ᵀ
    L⁻¹ * fromBlocks (L₁₁ * L₁₁ᵀ) Bᵀ B (-C) * Lᵀ⁻¹ =
      fromBlocks (1 : Matrix n n R) 0 0 (-1 : Matrix m m R) := by
  let L := fromBlocks L₁₁ 0 L₂₁ L₂₂
  let J := fromBlocks (1 : Matrix n n R) 0 0 (-1 : Matrix m m R)
  have hU : J * Lᵀ = fromBlocks L₁₁ᵀ L₂₁ᵀ 0 (-L₂₂ᵀ) := by
    simp [J, L, fromBlocks_transpose, fromBlocks_multiply]
  have hLt : IsUnit Lᵀ := by simpa only [isUnit_transpose] using hL
  dsimp only
  rw [signedCholesky_factorization L₁₁ L₂₁ L₂₂ C hC, ← hU]
  change L⁻¹ * (L * (J * Lᵀ)) * Lᵀ⁻¹ = J
  rw [← Matrix.mul_assoc L⁻¹, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hL),
    Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hLt),
    Matrix.mul_one]

end BenziGolubLiesen
