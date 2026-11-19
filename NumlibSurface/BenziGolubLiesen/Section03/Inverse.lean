import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Numlib.LinearAlgebra.Matrix.SaddlePoint.NullSpaceReduction
import NumlibSurface.BenziGolubLiesen.Section03.Factorization

/-!
# Benzi, Golub and Liesen, Section 3: Projected solutions and quasidefiniteness

When $C=0$ and the constraint right-hand side vanishes, the primal solution is the complement
of an oblique projection of $A^{-1}f$. With $A$ and $C$ both positive definite, the symmetric
saddle-point matrix and its inverse are quasidefinite.

## Main definitions

* `BenziGolubLiesen.saddleObliqueProjector`: projection onto $\operatorname{range}(A^{-1}B^T)$
  along $\ker B$.
* `BenziGolubLiesen.IsQuasidefinite`: symmetry and opposite definite diagonal blocks.

## Main results

* `BenziGolubLiesen.saddleObliqueProjector_spec`: idempotence, range and kernel.
* `BenziGolubLiesen.saddlePointSolution_zero_constraint`: the projected solution (3.5).
* `BenziGolubLiesen.saddlePointSolution_minWeightedResidual`: multiplier least squares (3.7).
* `BenziGolubLiesen.saddlePointMatrix_inv_eq_of_nullBasis`: the null-space inverse (3.8).
* `BenziGolubLiesen.IsQuasidefinite.inv`: the inverse has the same block definiteness.

## Deviations from the source

* **Section 3.3, oblique projector** (generalization). The range and kernel
  calculation needs nonsingularity of $BA^{-1}B^T$, with no positive definiteness
  hypothesis on $A$. See `BenziGolubLiesen.saddleObliqueProjector_spec`.
* **(3.5)** (correction). The multiplier is $-S^{-1}BA^{-1}f$, in agreement with (3.4).
  See `BenziGolubLiesen.saddlePointSolution_zero_constraint`.
* **(3.5)** (generalization). The solution formula requires invertible $A$ and $BA^{-1}B^T$;
  the source assumes symmetric positive definite $A$. See
  `BenziGolubLiesen.saddlePointSolution_zero_constraint`.
* **Equation (3.8)** (generalization). The inverse formula requires invertibility of
  $Z^TAZ$ directly. The source obtains it from a positive semidefinite symmetric part and
  a kernel-intersection condition. See `BenziGolubLiesen.saddlePointMatrix_inv_eq_of_nullBasis`.
* **After (3.8)** (correction). The projector $I-ZZ^T$ assumes orthonormal columns of $Z$.
  For a general null basis it is $I-Z(Z^TZ)^{-1}Z^T$. See
  `BenziGolubLiesen.saddlePointMatrix_inv_eq_of_nullBasis`.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Section 3.3** of [benzi2005numerical]. The oblique projector for the standard saddle-point
problem is $\Pi=A^{-1}B^T(BA^{-1}B^T)^{-1}B$. -/
noncomputable def saddleObliqueProjector (A : Matrix n n ℝ) (B : Matrix m n ℝ) : Matrix n n ℝ :=
  (A⁻¹ * Bᵀ) * (B * (A⁻¹ * Bᵀ))⁻¹ * B

private theorem projector_constraints (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hH : IsUnit (B * (A⁻¹ * Bᵀ))) :
    B * saddleObliqueProjector A B = B ∧
      saddleObliqueProjector A B * (A⁻¹ * Bᵀ) = A⁻¹ * Bᵀ := by
  let R := A⁻¹ * Bᵀ
  let H := B * R
  have hright : H * H⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hH)
  have hleft : H⁻¹ * H = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hH)
  change B * (R * H⁻¹ * B) = B ∧ R * H⁻¹ * B * R = R
  constructor
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, show B * R = H from rfl,
      hright, Matrix.one_mul]
  · rw [Matrix.mul_assoc (R * H⁻¹), show B * R = H from rfl, Matrix.mul_assoc,
      hleft, Matrix.mul_one]

/-- **Section 3.3** of [benzi2005numerical]. If $BA^{-1}B^T$ is nonsingular, $\Pi$ is
idempotent with range $\operatorname{range}(A^{-1}B^T)$ and kernel $\ker B$.

**Generalization.** The source establishes these properties with $A$ positive
definite. The range and kernel computation only uses the inverse of $BA^{-1}B^T$. -/
theorem saddleObliqueProjector_spec (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hH : IsUnit (B * (A⁻¹ * Bᵀ))) :
    let P := saddleObliqueProjector A B
    P * P = P ∧ LinearMap.range P.mulVecLin = LinearMap.range (A⁻¹ * Bᵀ).mulVecLin ∧
      LinearMap.ker P.mulVecLin = LinearMap.ker B.mulVecLin := by
  intro P
  obtain ⟨hBP, hPR⟩ := projector_constraints A B hH
  change B * P = B at hBP
  change P * (A⁻¹ * Bᵀ) = A⁻¹ * Bᵀ at hPR
  refine ⟨?_, le_antisymm ?_ ?_, ?_⟩
  · calc
      P * P = ((A⁻¹ * Bᵀ) * (B * (A⁻¹ * Bᵀ))⁻¹) * (B * P) := Matrix.mul_assoc _ _ _
      _ = P := by rw [hBP]; rfl
  · rintro z ⟨x, rfl⟩
    refine ⟨(B * (A⁻¹ * Bᵀ))⁻¹ *ᵥ (B *ᵥ x), ?_⟩
    simp only [mulVecLin_apply, P, saddleObliqueProjector, ← mulVec_mulVec]
  · rintro z ⟨x, rfl⟩
    exact ⟨(A⁻¹ * Bᵀ) *ᵥ x, by simp only [mulVecLin_apply, mulVec_mulVec, hPR]⟩
  · ext x
    simp only [LinearMap.mem_ker, mulVecLin_apply]
    constructor
    · intro hx
      simpa only [mulVec_mulVec, hBP, mulVec_zero] using congrArg (B *ᵥ ·) hx
    · intro hx
      simp only [P, saddleObliqueProjector, ← mulVec_mulVec, hx, mulVec_zero]

/-- **Equation (3.5)** of [benzi2005numerical]. With $A$ and $H=BA^{-1}B^T$ nonsingular and
$g=0$, the solution has components $(I-\Pi)A^{-1}f$ and $H^{-1}BA^{-1}f$.

**Correction.** The printed multiplier is $S^{-1}BA^{-1}f$, but $S=-H$. The negative sign
in (3.4) gives the multiplier $-S^{-1}BA^{-1}f$. For $A=B=f=[1]$, the constraint gives
$x=0$ and the top equation gives $y=1$, whereas the printed formula gives $y=-1$.

**Generalization.** The source assumes $A$ is symmetric positive definite. Nonsingularity
of $A$ and $H$ suffices for the block solve. -/
theorem saddlePointSolution_zero_constraint (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) (hH : IsUnit (B * (A⁻¹ * Bᵀ))) (f : n → ℝ) :
    let H := B * (A⁻¹ * Bᵀ)
    let v := A⁻¹ *ᵥ f
    saddlePointMatrix A B B 0 *ᵥ
        Sum.elim ((1 - saddleObliqueProjector A B) *ᵥ v) (H⁻¹ *ᵥ (B *ᵥ v)) = Sum.elim f 0 := by
  intro H v
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA)
  have hv : A *ᵥ v = f := by simp only [v, mulVec_mulVec, hAA, one_mulVec]
  rw [saddlePointMatrix_mulVec_iff, zero_mulVec, sub_zero, sub_mulVec, one_mulVec]
  constructor
  · have hp : saddleObliqueProjector A B *ᵥ v = (A⁻¹ * Bᵀ) *ᵥ (H⁻¹ *ᵥ (B *ᵥ v)) := by
      simp only [saddleObliqueProjector, H, ← mulVec_mulVec]
    rw [mulVec_sub, hv, hp, mulVec_mulVec _ A (A⁻¹ * Bᵀ), ← Matrix.mul_assoc, hAA,
      Matrix.one_mul, sub_add_cancel]
  · rw [mulVec_sub, mulVec_mulVec v B (saddleObliqueProjector A B),
      (projector_constraints A B hH).1, sub_self]

omit [DecidableEq m] in
/-- **Section 3.2** of [benzi2005numerical]. The primal solution is the $A$-orthogonal
projection of $A^{-1}f$ onto $Bx=g$: it is feasible and every feasible displacement
is $A$-orthogonal to $A^{-1}f-x$. -/
theorem saddlePointSolution_A_orthogonal {A : Matrix n n ℝ} (hA : A.PosDef)
    {B : Matrix m n ℝ} {x f : n → ℝ} {y g : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g) :
    B *ᵥ x = g ∧ ∀ z : n → ℝ, B *ᵥ z = g → (z - x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ f - x)) = 0 := by
  have hs := (saddlePointMatrix_mulVec_iff A B B 0 x f y g).mp h
  have hg : B *ᵥ x = g := by simpa using hs.2
  have hinv : A * A⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hr : f - A *ᵥ x = Bᵀ *ᵥ y := by rw [← hs.1]; abel
  refine ⟨hg, fun z hz => ?_⟩
  rw [mulVec_sub, mulVec_mulVec f A A⁻¹, hinv, one_mulVec, hr, dotProduct_transpose_mulVec,
    mulVec_sub, hz, hg, sub_self, dotProduct_zero]

omit [DecidableEq m] in
private theorem inverseWeightedResidual_eq_primal {A : Matrix n n ℝ} (hA : IsUnit A)
    {B : Matrix m n ℝ} {x f : n → ℝ} {y g : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g) :
    A⁻¹ *ᵥ (f - Bᵀ *ᵥ y) = x := by
  have hs := (saddlePointMatrix_mulVec_iff A B B 0 x f y g).mp h
  have hres : f - Bᵀ *ᵥ y = A *ᵥ x := by rw [← hs.1, add_sub_cancel_right]
  have hinv : A⁻¹ * A = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA)
  rw [hres, mulVec_mulVec, hinv, one_mulVec]

omit [DecidableEq m] in
/-- **Equation (3.6)** of [benzi2005numerical]. With zero constraint right-hand side, the
multiplier residual satisfies the normal equation in the $A^{-1}$ inner product. -/
theorem saddlePointSolution_weightedNormalEquation {A : Matrix n n ℝ} (hA : A.PosDef)
    {B : Matrix m n ℝ} {x f : n → ℝ} {y : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f 0) :
    (A⁻¹ * Bᵀ)ᵀ *ᵥ (f - Bᵀ *ᵥ y) = 0 := by
  have hsym : (A⁻¹)ᵀ = A⁻¹ := by simpa using hA.inv.isHermitian.eq
  rw [transpose_mul, transpose_transpose, hsym, ← mulVec_mulVec,
    inverseWeightedResidual_eq_primal hA.isUnit h]
  simpa using ((saddlePointMatrix_mulVec_iff A B B 0 x f y 0).mp h).2

omit [DecidableEq m] in
/-- **Equation (3.7)** of [benzi2005numerical]. With $A$ positive definite and $g=0$,
the saddle-point multiplier minimizes $\|f-B^T u\|_{A^{-1}}$ over all multipliers $u$. -/
theorem saddlePointSolution_minWeightedResidual {A : Matrix n n ℝ} (hA : A.PosDef)
    {B : Matrix m n ℝ} {x f : n → ℝ} {y : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f 0) (u : m → ℝ) :
    Real.sqrt ((f - Bᵀ *ᵥ y) ⬝ᵥ (A⁻¹ *ᵥ (f - Bᵀ *ᵥ y))) ≤
      Real.sqrt ((f - Bᵀ *ᵥ u) ⬝ᵥ (A⁻¹ *ᵥ (f - Bᵀ *ᵥ u))) := by
  let r := f - Bᵀ *ᵥ y
  let d := Bᵀ *ᵥ (y - u)
  have hsum : f - Bᵀ *ᵥ u = r + d := by
    simp only [r, d, mulVec_sub]
    abel
  have hg : B *ᵥ x = 0 := by
    simpa using ((saddlePointMatrix_mulVec_iff A B B 0 x f y 0).mp h).2
  have hc : d ⬝ᵥ (A⁻¹ *ᵥ r) = 0 := by
    change (Bᵀ *ᵥ (y - u)) ⬝ᵥ (A⁻¹ *ᵥ (f - Bᵀ *ᵥ y)) = _
    rw [inverseWeightedResidual_eq_primal hA.isUnit h, dotProduct_comm,
      dotProduct_transpose_mulVec, hg, dotProduct_zero]
  have hsym : (A⁻¹)ᵀ = A⁻¹ := by simpa using hA.inv.isHermitian.eq
  have hc' : r ⬝ᵥ (A⁻¹ *ᵥ d) = 0 := by rw [← hsym, dotProduct_transpose_mulVec, hc]
  have hd : 0 ≤ d ⬝ᵥ (A⁻¹ *ᵥ d) := by simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg d
  rw [hsum]
  apply Real.sqrt_le_sqrt
  simp only [mulVec_add, add_dotProduct, dotProduct_add, hc, hc', add_zero, zero_add]
  exact le_add_of_nonneg_right hd

/-- **Equation (3.8)** of [benzi2005numerical]. A null basis $Z$ for $B$ yields the inverse
without inverting $A$, provided $B$ has full row rank and $Z^T A Z$ is invertible.

**Generalization.** The source infers invertibility of $Z^TAZ$ from a positive semidefinite
symmetric part of $A$ and the kernel condition in Theorem 3.4(i). The inverse formula
requires only invertibility of $Z^TAZ$ itself under the stated rank and basis hypotheses.

**Correction.** The subsequent projector formula uses $I-ZZ^T$ for a general null basis.
That expression requires orthonormal columns. For $B=[1,0]$ and $Z=(0,2)^T$, it gives
$\operatorname{diag}(1,-3)$ instead of the row-space projector $\operatorname{diag}(1,0)$.
For a general null basis the formula is $I-Z(Z^TZ)^{-1}Z^T$. -/
theorem saddlePointMatrix_inv_eq_of_nullBasis {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix n n ℝ) (B : Matrix m n ℝ) (Z : Matrix n k ℝ)
    (hZ : IsNullBasis B Z) (hB : Function.Injective Bᵀ.mulVec) (hK : IsUnit (Zᵀ * A * Z)) :
    let G := B * Bᵀ
    let W := Z * (Zᵀ * A * Z)⁻¹ * Zᵀ
    (saddlePointMatrix A B B 0)⁻¹ =
      fromBlocks W ((1 - W * A) * (Bᵀ * G⁻¹))
        (G⁻¹ * B * (1 - A * W)) (-(G⁻¹ * B * (A - A * W * A) * (Bᵀ * G⁻¹))) := by
  simpa only [saddlePointMatrix, neg_zero] using inv_fromBlocks_transpose_zero_of_nullBasis hZ hB hK

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- **Section 3.3** of [benzi2005numerical]. A real symmetric block matrix is quasidefinite
if its leading block is positive definite and the negative of its trailing block is positive
definite. No rank condition is imposed on its off-diagonal block. -/
def IsQuasidefinite (M : Matrix (n ⊕ m) (n ⊕ m) ℝ) : Prop :=
  M.IsHermitian ∧ M.toBlocks₁₁.PosDef ∧ (-M.toBlocks₂₂).PosDef

omit [Fintype m] [DecidableEq m] in variable [Finite m] in
private theorem posDef_neg_quasidefiniteSchur {M : Matrix (n ⊕ m) (n ⊕ m) ℝ}
    (hM : IsQuasidefinite M) : (-M.schurComplement).PosDef := by
  obtain ⟨hs, hA, hC⟩ := hM
  have hform : M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := (congrArg toBlocks₂₁ hs.eq).symm
  rw [schurComplement_eq, neg_sub, hform, sub_eq_add_neg, add_comm]
  exact hC.add_posSemidef (hA.inv.posSemidef.conjTranspose_mul_mul_same _)

/-- **Section 3.3** of [benzi2005numerical]. Symmetric quasidefinite matrices are nonsingular. -/
theorem IsQuasidefinite.isUnit {M : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hM : IsQuasidefinite M) :
    IsUnit M :=
  (isUnit_schurComplement_iff hM.2.1.isUnit).mp
    ((IsUnit.neg_iff _).mp (posDef_neg_quasidefiniteSchur hM).isUnit)

private theorem posDef_neg_inv_toBlocks₂₂ {M : Matrix (n ⊕ m) (n ⊕ m) ℝ}
    (hM : IsQuasidefinite M) : (-(M⁻¹).toBlocks₂₂).PosDef := by
  have hS := posDef_neg_quasidefiniteSchur hM
  rw [toBlocks₂₂_inv_eq_inv_schurComplement hM.2.1.isUnit hM.isUnit]
  have hneg : (-M.schurComplement)⁻¹ = -M.schurComplement⁻¹ :=
    inv_eq_left_inv (by
      rw [neg_mul_neg, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp
        ((IsUnit.neg_iff _).mp hS.isUnit))])
  exact hneg ▸ hS.inv

/-- **Section 3.3** of [benzi2005numerical]. The inverse is quasidefinite under the same
block partition. Its diagonal blocks are the inverses of the two Schur complements. -/
theorem IsQuasidefinite.inv {M : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hM : IsQuasidefinite M) :
    IsQuasidefinite M⁻¹ := by
  let e : m ⊕ n ≃ n ⊕ m := Equiv.sumComm m n
  have hsym : M⁻¹.IsHermitian := by
    change M⁻¹ᴴ = _
    rw [conjTranspose_nonsing_inv, hM.1.eq]
  refine ⟨hsym, ?_, posDef_neg_inv_toBlocks₂₂ hM⟩
  let T : Matrix (m ⊕ n) (m ⊕ n) ℝ := -(M.submatrix e e)
  have hT : IsQuasidefinite T := by
    refine ⟨((isHermitian_submatrix_equiv e).mpr hM.1).neg, hM.2.2, ?_⟩
    change (-(-M.toBlocks₁₁)).PosDef
    simpa only [neg_neg] using hM.2.1
  have hTinv : T⁻¹ = -(M⁻¹.submatrix e e) := by
    apply inv_eq_left_inv
    rw [show T = -(M.submatrix e e) from rfl, neg_mul_neg, submatrix_mul_equiv]
    rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM.isUnit), submatrix_one_equiv]
  have h := posDef_neg_inv_toBlocks₂₂ hT
  rw [hTinv] at h
  change (-(-(M⁻¹).toBlocks₁₁)).PosDef at h
  simpa only [neg_neg] using h

end BenziGolubLiesen
