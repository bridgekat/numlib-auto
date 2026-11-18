import Numlib.Preconditioner.HermitianSkewSplitting
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real

/-!
# Benzi, Golub and Liesen, Section 10.3: Hermitian/skew-Hermitian preconditioning

The sign-flipped saddle-point matrix splits into its symmetric and skew-symmetric parts.
This module formalizes the HSS splitting and the Schur reduction in [benzi2005numerical].
The correction formula specializes `Numlib.Preconditioner.HermitianSkewSplitting`.

## Main definitions

* Equation (10.23), `BenziGolubLiesen.hssSymmetricBlock` and
  `BenziGolubLiesen.hssSkewBlock`: the two parts of the sign-flipped matrix.

## Main results

* Equation (10.23), `BenziGolubLiesen.hss_saddle_split`: split the saddle-point matrix.
* Equations (10.24)–(10.26), `BenziGolubLiesen.hss_saddle_step`: the two half-steps
  produce one HSS residual correction.
* `BenziGolubLiesen.hss_saddle_spectrum_disk`: strict spectral inclusion in $|z-1|<1$.
* Equations (10.27)–(10.28), `BenziGolubLiesen.hss_saddle_apply`: apply the unnormalized
  preconditioner by two successive solves.
* Equations (10.29)–(10.30), `BenziGolubLiesen.hss_skew_schur`: eliminate the primal block
  of the shifted skew-symmetric system.
* Equation (10.31), `BenziGolubLiesen.hss_skew_schur_zero`: the pressure equation when $K=0$.

## Not formalized

* The optimal shift bound, small-shift spectral clustering, shifted condition-number estimate,
  and the rotation-form sparsity and inverse formulas following (10.32).
* The singular primal Hermitian part. A common-kernel condition alone does not ensure the
  strict disk for these HSS steps; the disk theorem uses positive definiteness of that part.
* Inexact solves and empirical convergence behavior, which depend on the inner solver or
  discretization.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The block diagonal symmetric part in (10.23) of [benzi2005numerical]. -/
noncomputable def hssSymmetricBlock (A : Matrix n n ℝ) (C : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ := fromBlocks ((2 : ℝ)⁻¹ • (A + Aᵀ)) 0 0 C

/-- The skew-symmetric part in (10.23) of [benzi2005numerical], with primal block
$K=(A-A^T)/2$ and off-diagonal blocks $B^T$ and $-B$. -/
noncomputable def hssSkewBlock (A : Matrix n n ℝ) (B : Matrix m n ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ := fromBlocks ((2 : ℝ)⁻¹ • (A - Aᵀ)) Bᵀ (-B) 0

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- Equation (10.23) of [benzi2005numerical]. The sign-flipped system matrix is the sum of
its symmetric block diagonal part and its skew-symmetric part. -/
theorem hss_saddle_split (A : Matrix n n ℝ) (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hC : Cᵀ = C) :
    fromBlocks A Bᵀ (-B) C = hssSymmetricBlock A C + hssSkewBlock A B ∧
      (hssSymmetricBlock A C)ᵀ = hssSymmetricBlock A C ∧
      (hssSkewBlock A B)ᵀ = -hssSkewBlock A B := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hssSymmetricBlock, hssSkewBlock, fromBlocks_add, zero_add, add_zero, ← smul_add]
    rw [show A + Aᵀ + (A - Aᵀ) = (2 : ℝ) • A by rw [two_smul]; abel]
    rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  · simp [hssSymmetricBlock, fromBlocks_transpose, transpose_smul, transpose_add, hC, add_comm]
  · simp [hssSkewBlock, fromBlocks_transpose, fromBlocks_neg, transpose_smul, transpose_sub,
      ← smul_neg, neg_sub]

/-- Equations (10.24)–(10.26) of [benzi2005numerical]. For the sign-flipped saddle system,
the two HSS half-steps produce the normalized preconditioned residual correction. -/
theorem hss_saddle_step {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}
    (hC : Cᵀ = C) {α : ℝ} (hα : 0 < α)
    (hH : IsUnit (hssSymmetricBlock A C + α • 1))
    (hK : IsUnit (hssSkewBlock A B + α • 1)) {u w v b : n ⊕ m → ℝ}
    (hw : (hssSymmetricBlock A C + α • 1) *ᵥ w = (α • 1 - hssSkewBlock A B) *ᵥ u + b)
    (hv : (hssSkewBlock A B + α • 1) *ᵥ v = (α • 1 - hssSymmetricBlock A C) *ᵥ w + b) :
    v = u + (hssPreconditioner (hssSymmetricBlock A C) (hssSkewBlock A B) α)⁻¹ *ᵥ
      (b - fromBlocks A Bᵀ (-B) C *ᵥ u) := by
  rw [(hss_saddle_split A B hC).1]
  exact hssStep_eq (mul_ne_zero (by norm_num) hα.ne') hH hK hw hv

/-- Equations (10.27)–(10.28) of [benzi2005numerical]. Applying the unnormalized HSS
preconditioner means solving first with $H+\alpha I$ and then with $K+\alpha I$. -/
theorem hss_saddle_apply (H K : Matrix (n ⊕ m) (n ⊕ m) ℝ) (α : ℝ) (r : n ⊕ m → ℝ) :
    (((H + α • 1) * (K + α • 1))⁻¹ *ᵥ r) =
      (K + α • 1)⁻¹ *ᵥ ((H + α • 1)⁻¹ *ᵥ r) := by
  rw [Matrix.mul_inv_rev, mulVec_mulVec]

/-- Equations (10.29)–(10.30) of [benzi2005numerical]. Let $Q=I+\alpha^{-1}K$.
Eliminating the primal unknown $x$ from the shifted skew system leaves the pressure
equation $(BQ^{-1}B^T+\alpha^2 I)y=BQ^{-1}f+\alpha g$. -/
theorem hss_skew_schur (K : Matrix n n ℝ) (B : Matrix m n ℝ) {α : ℝ}
    (hα : α ≠ 0) (hQ : IsUnit (1 + α⁻¹ • K)) {x f : n → ℝ} {y g : m → ℝ}
    (hx : (α • 1 + K) *ᵥ x + Bᵀ *ᵥ y = f) (hy : -(B *ᵥ x) + α • y = g) :
    (B * (1 + α⁻¹ • K)⁻¹ * Bᵀ + α ^ 2 • 1) *ᵥ y =
      (B * (1 + α⁻¹ • K)⁻¹) *ᵥ f + α • g := by
  let Q := 1 + α⁻¹ • K
  have hscale : α • Q = α • 1 + K := by
    dsimp only [Q]
    rw [smul_add, smul_smul, mul_inv_cancel₀ hα, one_smul]
  have hQx : Q *ᵥ (α • x) = f - Bᵀ *ᵥ y := by
    rw [mulVec_smul, ← smul_mulVec, hscale]
    exact eq_sub_of_add_eq hx
  have h := congrArg (fun z ↦ B *ᵥ z) (nonsing_inv_mulVec_eq hQ hQx)
  have hh := congrArg (fun z : m → ℝ ↦ α • z) hy
  change B *ᵥ (Q⁻¹ *ᵥ (f - Bᵀ *ᵥ y)) = B *ᵥ (α • x) at h
  simp only [mulVec_sub, mulVec_smul] at h
  simp only [smul_add, smul_neg, smul_smul, ← pow_two] at hh
  change (B * Q⁻¹ * Bᵀ + α ^ 2 • 1) *ᵥ y = _
  simp only [add_mulVec, ← mulVec_mulVec, smul_mulVec, one_mulVec]
  rw [← hh, ← h]
  abel

/-- Equation (10.31) of [benzi2005numerical]. With zero primal skew block, the pressure
equation is the shifted Gram system $(BB^T+\alpha^2 I)y=Bf+\alpha g$. -/
theorem hss_skew_schur_zero (B : Matrix m n ℝ) {α : ℝ} (hα : α ≠ 0)
    {x f : n → ℝ} {y g : m → ℝ} (hx : α • x + Bᵀ *ᵥ y = f)
    (hy : -(B *ᵥ x) + α • y = g) :
    (B * Bᵀ + α ^ 2 • 1) *ᵥ y = B *ᵥ f + α • g := by
  simpa using hss_skew_schur (0 : Matrix n n ℝ) B hα (by simp)
    (x := x) (y := y) (f := f) (g := g) (by simpa [smul_mulVec] using hx) hy


open scoped ComplexOrder in
/-- Under the saddle-point hypotheses of Section 10.3 of [benzi2005numerical], the
normalized HSS-preconditioned eigenvalues lie strictly in the disk $|z-1|<1$.
The primal Hermitian part $H$ is positive definite, $C$ is positive semidefinite,
$K$ is skew-Hermitian, and $B^H$ is injective. The complex formulation also covers
real blocks acting on complex eigenvectors. -/
theorem hss_saddle_spectrum_disk (H K : Matrix n n ℂ) (B : Matrix m n ℂ) (C : Matrix m m ℂ)
    (hH : H.PosDef) (hC : C.PosSemidef) (hK : Kᴴ = -K) (hB : Function.Injective Bᴴ.mulVec)
    {α : ℝ} (hα : 0 < α) {ell : ℂ}
    (hell : ell ∈ spectrum ℂ
      ((hssPreconditioner (fromBlocks H 0 0 C) (fromBlocks K Bᴴ (-B) 0) (α : ℂ))⁻¹ *
        fromBlocks (H + K) Bᴴ (-B) C)) : ‖ell - 1‖ < 1 := by
  let D := fromBlocks H 0 0 C
  let S := fromBlocks K Bᴴ (-B) 0
  have hD : D.PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · simp [D, IsHermitian, fromBlocks_conjTranspose, hH.1.eq, hC.1.eq]
    · intro v
      have heq : star v ⬝ᵥ (D *ᵥ v) =
          star (v ∘ Sum.inl) ⬝ᵥ (H *ᵥ (v ∘ Sum.inl)) +
            star (v ∘ Sum.inr) ⬝ᵥ (C *ᵥ (v ∘ Sum.inr)) := by
        change star v ⬝ᵥ (fromBlocks H 0 0 C *ᵥ v) = _
        rw [dotProduct_block, fromBlocks_mulVec]
        simp
        rfl
      rw [heq]
      exact add_nonneg (hH.posSemidef.dotProduct_mulVec_nonneg _) (hC.dotProduct_mulVec_nonneg _)
  have hS : Sᴴ = -S := by simp [S, fromBlocks_conjTranspose, fromBlocks_neg, hK]
  have hDS : D + S = fromBlocks (H + K) Bᴴ (-B) C := by
    simp [D, S, fromBlocks_add]
  rw [← hDS] at hell
  refine norm_sub_one_lt_one_of_hss hD hS ?_ hα hell
  intro ν v hDv hSv
  have hx : v ∘ Sum.inl = 0 := by
    have heq := congrArg (fun z : n ⊕ m → ℂ ↦ z ∘ Sum.inl) hDv
    have hh : H *ᵥ (v ∘ Sum.inl) = 0 := by
      simpa [D, fromBlocks_mulVec] using heq
    exact (mulVec_injective_iff_isUnit.mpr hH.isUnit) (hh.trans (mulVec_zero _).symm)
  have hy : v ∘ Sum.inr = 0 := by
    have heq := congrArg (fun z : n ⊕ m → ℂ ↦ z ∘ Sum.inl) hSv
    have hsmul : (ν • v) ∘ Sum.inl = ν • (v ∘ Sum.inl) := rfl
    have hh : Bᴴ *ᵥ (v ∘ Sum.inr) = 0 := by
      simpa [S, fromBlocks_mulVec, hsmul, hx] using heq
    exact hB (hh.trans (mulVec_zero _).symm)
  funext i
  cases i with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

omit [DecidableEq n] in
/-- The shifted pressure Gram matrix in (10.31) is positive definite for any
nonzero shift, without a rank assumption on $B$. -/
theorem hss_skew_schur_zero_posDef (B : Matrix m n ℝ) {α : ℝ} (hα : α ≠ 0) :
    (B * Bᵀ + α ^ 2 • 1).PosDef := by
  exact PosDef.posSemidef_add
    (by simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose B)
    (PosDef.one.smul (sq_pos_of_ne_zero hα))

end BenziGolubLiesen
