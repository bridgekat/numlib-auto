/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.SaddlePoint.ScalarDiagonal
import Numlib.LinearAlgebra.Matrix.SaddlePoint.Spectrum
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 3.4: Spectral properties

This module formalizes the spectral results of Section 3.4 of [benzi2005numerical]. Let
$A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. The section compares the symmetric saddle-point matrix with the
sign-flipped matrix (3.10),
$$\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix} \quad \text{and} \quad \begin{bmatrix} A & B^T \\
  -B & C \end{bmatrix}.$$
For symmetric positive definite $A$, the eigenvalues of the first matrix lie in two intervals given
by the extreme eigenvalues of $A$ and the extreme singular values of $B$ (Theorem 3.5). The
eigenvalues of the second matrix have nonnegative real part (Theorem 3.6), and they are real and
positive when $A$ dominates the Schur complement $BA^{-1}B^T$ (Theorem 3.7). When the top block is
$\eta I$, the eigenvalues of both forms (3.13) are given explicitly by the singular values of $B$
(Theorem 3.8). The proofs specialize results in `Numlib.LinearAlgebra.Matrix.SaddlePoint.Spectrum`
and `Numlib.LinearAlgebra.Matrix.SaddlePoint.ScalarDiagonal`.

## Main definitions

* Equation (3.10), `BenziGolubLiesen.signFlippedSaddlePointMatrix`: the matrix with blocks $A$,
  $B^T$, $-B$ and $C$.
* Equation (3.11), `BenziGolubLiesen.saddleSignature`: the signature matrix $J$.
* Equation (3.13), `BenziGolubLiesen.scaledSaddlePointMatrix`: the matrix with blocks $\eta I$,
  $B^T$, $\varepsilon B$ and $0$, where $\varepsilon = \pm 1$.

## Main results

* Theorem 3.5, `BenziGolubLiesen.theorem_3_5`: for symmetric positive definite $A$ and $B$ of rank
  $m$, the eigenvalues of the symmetric matrix are real and lie in the union of two intervals.
* Theorem 3.6, `BenziGolubLiesen.theorem_3_6`: the sign-flipped matrix has a nonnegative quadratic
  form, and its eigenvalues have nonnegative real part, or positive real part when the symmetric
  part of $A$ is positive definite.
* Theorem 3.7, `BenziGolubLiesen.theorem_3_7`: if $\lambda_{\min}(A) \ge 4 \|BA^{-1}B^T\|_2$, all
  eigenvalues of the sign-flipped matrix with $C = 0$ are real and positive.
* Theorem 3.8, `BenziGolubLiesen.theorem_3_8`: the eigenvalues of both matrices (3.13), with
  algebraic multiplicities, are $0$, $\eta$, and a pair of roots for each nonzero singular value of
  $B$.
* Paragraph after Theorem 3.8, `BenziGolubLiesen.signFlipped_roots_re_of_lt`: the nonreal
  eigenvalues of the sign-flipped matrix (3.13) have real part $\eta / 2$.

## Implementation notes

* Eigenvalues are complex: the spectrum of a real matrix $M$ is `spectrum ℂ M.complexify`, and
  "real" is membership in the image of `Complex.ofReal`.
* The extreme eigenvalues of $A$ are the infimum and the supremum of
  `Matrix.IsHermitian.eigenvalues`. The singular values of $B$ are `Matrix.sortedSingularValues`,
  indexed from $0$ in decreasing order.
* The norm $\|\cdot\|_2$ is the operator norm of the scope `Matrix.Norms.L2Operator`.

## Deviations from the source

* **Equation (3.13)** (generalization). The matrix is defined with a real multiplier
  on the lower coupling block, including the printed signs $+1$ and $-1$. See
  `BenziGolubLiesen.scaledSaddlePointMatrix`.
* **Paragraph after Theorem 3.8** (correction). The source calls the nonreal eigenvalues of the
  sign-flipped form purely imaginary. They have real part $\eta / 2$, as the formulas of Theorem 3.8
  give. See `BenziGolubLiesen.signFlipped_roots_re_of_lt`.
-/

namespace BenziGolubLiesen

open Matrix WithLp
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Equation (3.10)** of [benzi2005numerical]. For $A \in \mathbb{R}^{n \times n}$,
$B \in \mathbb{R}^{m \times n}$ and $C \in \mathbb{R}^{m \times m}$, the **sign-flipped
saddle-point matrix** is
$$\begin{bmatrix} A & B^T \\ -B & C \end{bmatrix}.$$
It is obtained from the matrix of (1.1) with $B_1 = B_2 = B$ by changing the sign of the second
block row.

The matrix is `Matrix.fromBlocks A Bᵀ (-B) C`, indexed by `n ⊕ m`. -/
abbrev signFlippedSaddlePointMatrix (A : Matrix n n ℝ) (B : Matrix m n ℝ) (C : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks A Bᵀ (-B) C

/-- **Equation (3.11)** of [benzi2005numerical]. The signature matrix $J$ has diagonal
blocks $I_n$ and $-I_m$. -/
abbrev saddleSignature : Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks 1 0 0 (-1)

/-- **Section 3.4** of [benzi2005numerical]. Changing the sign of the second block row
twice restores the original matrix. -/
theorem saddleSignature_sq : saddleSignature * saddleSignature =
    (1 : Matrix (n ⊕ m) (n ⊕ m) ℝ) := by
  simp [saddleSignature, fromBlocks_multiply, fromBlocks_one]

/-- **Equations (3.10)–(3.11)** of [benzi2005numerical]. Left multiplication by $J$ gives the
sign-flipped saddle-point matrix. -/
theorem signFlippedSaddlePointMatrix_eq_signature_mul (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (C : Matrix m m ℝ) :
    signFlippedSaddlePointMatrix A B C = saddleSignature * saddlePointMatrix A B B C := by
  simp [saddleSignature, saddlePointMatrix, signFlippedSaddlePointMatrix, fromBlocks_multiply]

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (3.10)** of [benzi2005numerical]. Changing the sign of the second block row
and of the second right-hand side component preserves the solution set. -/
theorem signFlippedSaddlePointMatrix_mulVec_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (C : Matrix m m ℝ) (x f : n → ℝ) (y g : m → ℝ) :
    signFlippedSaddlePointMatrix A B C *ᵥ Sum.elim x y = Sum.elim f (-g) ↔
      saddlePointMatrix A B B C *ᵥ Sum.elim x y = Sum.elim f g := by
  classical
  have h (z : n → ℝ) (w : m → ℝ) : saddleSignature *ᵥ Sum.elim z w = Sum.elim z (-w) := by
    simp [saddleSignature, fromBlocks_mulVec, neg_mulVec]
  rw [signFlippedSaddlePointMatrix_eq_signature_mul, ← mulVec_mulVec, ← h]
  have hleft : Function.LeftInverse
      (saddleSignature : Matrix (n ⊕ m) (n ⊕ m) ℝ).mulVec saddleSignature.mulVec := by
    intro z
    rw [mulVec_mulVec, saddleSignature_sq, one_mulVec]
  exact hleft.injective.eq_iff

/-- **Equation (3.12)** of [benzi2005numerical]. The sign-flipped matrix is $J$-symmetric
when $A$ and $C$ are symmetric. -/
theorem saddleSignature_mul_signFlipped_eq {A : Matrix n n ℝ} {C : Matrix m m ℝ}
    (hA : A.IsSymm) (hC : C.IsSymm) (B : Matrix m n ℝ) :
    saddleSignature * signFlippedSaddlePointMatrix A B C =
      (signFlippedSaddlePointMatrix A B C)ᵀ * saddleSignature := by
  simp [saddleSignature, signFlippedSaddlePointMatrix, fromBlocks_multiply, fromBlocks_transpose,
    hA.eq, hC.eq]

omit [DecidableEq n] [DecidableEq m] in
private theorem fullRowRank_mulVec_transpose_injective {B : Matrix m n ℝ}
    (hB : B.rank = Fintype.card m) : Function.Injective Bᵀ.mulVec :=
  Matrix.mulVec_injective_iff_rank_eq_card.mpr (by rwa [Matrix.rank_transpose])

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem map_ofReal_transpose (B : Matrix m n ℝ) :
    Bᵀ.map Complex.ofReal = (B.map Complex.ofReal)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem complexify_signFlippedSaddlePointMatrix
    (A : Matrix n n ℝ) (B : Matrix m n ℝ) (C : Matrix m m ℝ) :
    (signFlippedSaddlePointMatrix A B C).complexify =
      fromBlocks A.complexify (B.map Complex.ofReal)ᴴ (-(B.map Complex.ofReal)) C.complexify := by
  rw [show (signFlippedSaddlePointMatrix A B C).complexify =
    (fromBlocks A Bᵀ (-B) C).map Complex.ofReal from rfl, fromBlocks_map,
    map_ofReal_transpose]
  congr 1
  ext i j
  simp

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem hermitianPart_complexify (A : Matrix n n ℝ) :
    A.complexify.hermitianPart = A.hermitianPart.complexify := by
  rw [hermitianPart, hermitianPart, complexify_smul, complexify_add, complexify_conjTranspose]
  norm_num

omit [Fintype m] [DecidableEq m] in
private theorem iInf_eigenvalues_pos [Nonempty n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < ⨅ i, hA.isHermitian.eigenvalues i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ hA.isHermitian.eigenvalues
    Finset.univ_nonempty
  exact (hA.eigenvalues_pos i).trans_le (le_ciInf fun j => hi j (Finset.mem_univ _))

/-- **Theorem 3.5** of [benzi2005numerical] (Rusten–Winther bounds). Let $n, m \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite with eigenvalues
$\mu_1 \ge \dots \ge \mu_n$, and let $B \in \mathbb{R}^{m \times n}$ have rank $m$ and singular
values $\sigma_1 \ge \dots \ge \sigma_m$. Then every eigenvalue $\lambda$ of
$\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$ is real and
$$\lambda \in \Big[\tfrac{1}{2}\big(\mu_n - \sqrt{\mu_n^2 + 4\sigma_1^2}\big),
  \tfrac{1}{2}\big(\mu_1 - \sqrt{\mu_1^2 + 4\sigma_m^2}\big)\Big] \cup \Big[\mu_n,
  \tfrac{1}{2}\big(\mu_1 + \sqrt{\mu_1^2 + 4\sigma_1^2}\big)\Big].$$

The matrix is `BenziGolubLiesen.saddlePointMatrix A B B 0`, and its eigenvalues are the elements
of the spectrum of its complexification. The numbers $\mu_n$ and $\mu_1$ are the infimum and the
supremum of `Matrix.IsHermitian.eigenvalues`, and $\sigma_1$ and $\sigma_m$ are
`Matrix.sortedSingularValues` at the indices $0$ and $m - 1$. The proof specializes
`Matrix.spectrum_fromBlocks_transpose_zero_subset`. -/
theorem theorem_3_5 [Nonempty n] [Nonempty m] {A : Matrix n n ℝ} {B : Matrix m n ℝ}
    (hA : A.PosDef) (hB : B.rank = Fintype.card m) :
    let μₙ := ⨅ i, hA.isHermitian.eigenvalues i
    let μ₁ := ⨆ i, hA.isHermitian.eigenvalues i
    let σₘ := B.sortedSingularValues (Fintype.card m - 1)
    let σ₁ := B.sortedSingularValues 0
    spectrum ℂ (saddlePointMatrix A B B 0).complexify ⊆ Complex.ofReal ''
      (Set.Icc ((μₙ - Real.sqrt (μₙ ^ 2 + 4 * σ₁ ^ 2)) / 2)
        ((μ₁ - Real.sqrt (μ₁ ^ 2 + 4 * σₘ ^ 2)) / 2) ∪
      Set.Icc μₙ ((μ₁ + Real.sqrt (μ₁ ^ 2 + 4 * σ₁ ^ 2)) / 2)) := by
  dsimp only
  have hM : (saddlePointMatrix A B B 0).IsHermitian := by
    simpa [saddleMatrix, saddlePointMatrix, conjTranspose_eq_transpose_of_trivial] using
      hA.isHermitian.saddleMatrix Bᵀ (isHermitian_zero : (0 : Matrix m m ℝ).IsHermitian)
  have hMc := (isHermitian_complexify_iff _).2 hM
  intro μ hμ
  obtain ⟨a, -, rfl⟩ := hMc.spectrum_eq_image_range ▸ hμ
  refine ⟨a, ?_, rfl⟩
  have ha := (ofReal_mem_spectrum_complexify_iff _ a).1 hμ
  simp only [saddlePointMatrix, neg_zero] at ha
  refine spectrum_fromBlocks_transpose_zero_subset B hA (fullRowRank_mulVec_transpose_injective hB)
    (iInf_eigenvalues_pos hA) (B.sortedSingularValues_nonneg _) ?_ ?_ ?_ ?_ ha
  · exact hA.isHermitian.posSemidef_sub_smul_one_of_le_eigenvalues
      (ciInf_le (Set.finite_range _).bddBelow)
  · exact hA.isHermitian.posSemidef_smul_one_sub_of_eigenvalues_le
      (le_ciSup (Set.finite_range _).bddAbove)
  · intro y
    have hσ : B.sortedSingularValues = Bᵀ.sortedSingularValues := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        (sortedSingularValues_conjTranspose B).symm
    rw [hσ, sortedSingularValues_eq_iInf_colSingularValues]
    exact Bᵀ.iInf_colSingularValues_mul_norm_le (toLp 2 y)
  · intro x
    rw [B.sortedSingularValues_zero_eq_l2_opNorm]
    exact B.l2_opNorm_mulVec (toLp 2 x)

/-- **Theorem 3.6** of [benzi2005numerical]. Let $A \in \mathbb{R}^{n \times n}$ have positive
semidefinite symmetric part $H = \frac{1}{2}(A + A^T)$, let $B \in \mathbb{R}^{m \times n}$ have
rank $m$, let $C \in \mathbb{R}^{m \times m}$ be symmetric positive semidefinite, and assume
$\ker H \cap \ker B = \{0\}$. Let $M = \begin{bmatrix} A & B^T \\ -B & C \end{bmatrix}$. Then:

* $v^T M v \ge 0$ for all $v \in \mathbb{R}^{n + m}$;
* every eigenvalue $\lambda \in \mathbb{C}$ of $M$ has $\operatorname{Re} \lambda \ge 0$;
* if $H$ is positive definite, every eigenvalue $\lambda$ of $M$ has
  $\operatorname{Re} \lambda > 0$.

The matrix $M$ is `BenziGolubLiesen.signFlippedSaddlePointMatrix A B C`, and $H$ is
`Matrix.hermitianPart A`. The proof does not use the hypothesis $\ker H \cap \ker B = \{0\}$.
The rank condition on $B$ is used only for the third conclusion. -/
theorem theorem_3_6 {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}
    (hA : A.hermitianPart.PosSemidef) (hB : B.rank = Fintype.card m)
    (hC : C.PosSemidef)
    (_hker : LinearMap.ker A.hermitianPart.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    let M := signFlippedSaddlePointMatrix A B C
    (∀ v, 0 ≤ v ⬝ᵥ (M *ᵥ v)) ∧
      (∀ μ ∈ spectrum ℂ M.complexify, 0 ≤ μ.re) ∧
      (A.hermitianPart.PosDef → ∀ μ ∈ spectrum ℂ M.complexify, 0 < μ.re) := by
  dsimp only
  refine ⟨dotProduct_fromBlocks_neg_transpose_mulVec_nonneg B hA hC, ?_, ?_⟩
  · intro μ hμ
    rw [complexify_signFlippedSaddlePointMatrix] at hμ
    exact re_nonneg_of_mem_spectrum_fromBlocks_neg_conjTranspose (B.map Complex.ofReal)ᴴ (by
      rw [hermitianPart_complexify]
      exact hA.complexify) hC.complexify (by simpa using hμ)
  · intro hA' μ hμ
    rw [complexify_signFlippedSaddlePointMatrix] at hμ
    exact re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose (by
      rw [hermitianPart_complexify, posDef_complexify_iff]
      exact hA') hC.complexify (Matrix.mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
      (by simpa using hμ)

/-- **Theorem 3.7** of [benzi2005numerical]. Let $n \ge 1$, let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite with smallest eigenvalue $\lambda_{\min}(A)$, and let
$B \in \mathbb{R}^{m \times n}$ have rank $m$. If
$$4 \|BA^{-1}B^T\|_2 \le \lambda_{\min}(A),$$
then every eigenvalue $\lambda$ of $\begin{bmatrix} A & B^T \\ -B & 0 \end{bmatrix}$ is real and
positive: $\operatorname{Im} \lambda = 0$ and $\operatorname{Re} \lambda > 0$.

The matrix is `BenziGolubLiesen.signFlippedSaddlePointMatrix A B 0`. The norm $\|\cdot\|_2$ is
the operator norm induced by the Euclidean norm, and $\lambda_{\min}(A)$ is the infimum of
`Matrix.IsHermitian.eigenvalues`. -/
theorem theorem_3_7 [Nonempty n] {A : Matrix n n ℝ} {B : Matrix m n ℝ}
    (hA : A.PosDef) (hB : B.rank = Fintype.card m)
    (hS : 4 * ‖B * A⁻¹ * Bᵀ‖ ≤ ⨅ i, hA.isHermitian.eigenvalues i) :
    ∀ μ ∈ spectrum ℂ (signFlippedSaddlePointMatrix A B 0).complexify,
      μ.im = 0 ∧ 0 < μ.re := by
  intro μ hμ
  rw [complexify_signFlippedSaddlePointMatrix, complexify_zero] at hμ
  let Bc := B.map Complex.ofReal
  have hBc := Matrix.mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB
  have hAc : A.complexify.PosDef := posDef_complexify_iff.2 hA
  have hmin :
      ∀ x : n → ℂ, (⨅ i, hA.isHermitian.eigenvalues i) * ‖toLp 2 x‖ ^ 2 ≤
        (star x ⬝ᵥ (A.complexify *ᵥ x)).re := by
    let a := ⨅ i, hA.isHermitian.eigenvalues i
    have ha : (A - a • 1).PosSemidef :=
      hA.isHermitian.posSemidef_sub_smul_one_of_le_eigenvalues
        (ciInf_le (Set.finite_range _).bddBelow)
    intro x
    have h := (Complex.nonneg_iff.1 (ha.complexify.dotProduct_mulVec_nonneg x)).1
    rw [complexify_sub, complexify_smul, complexify_one, sub_mulVec, smul_mulVec,
      one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, star_dotProduct_self] at h
    change 0 ≤ (star x ⬝ᵥ (A.complexify *ᵥ x) -
      (a : ℂ) * ((‖toLp 2 x‖ : ℝ) : ℂ) ^ 2).re at h
    rw [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    exact sub_nonneg.mp h
  have hSc : ‖Bc * A.complexify⁻¹ * Bcᴴ‖ = ‖B * A⁻¹ * Bᵀ‖ := by
    rw [← l2_opNorm_complexify]
    congr 1
    have h : (B * A⁻¹ * Bᵀ).map Complex.ofRealHom =
        B.map Complex.ofRealHom * (A⁻¹).map Complex.ofRealHom * Bᵀ.map Complex.ofRealHom := by
      simp only [Matrix.map_mul]
    rw [show (B * A⁻¹ * Bᵀ).complexify =
      Bc * (A⁻¹).complexify * Bᵀ.map Complex.ofReal from h, complexify_inv,
      map_ofReal_transpose]
  refine ⟨im_eq_zero_of_mem_spectrum_fromBlocks_neg_conjTranspose_zero
    hAc hBc hmin (hSc.symm ▸ hS) hμ, ?_⟩
  exact re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose
    (hAc.isHermitian.hermitianPart_eq.symm ▸ hAc) PosSemidef.zero hBc (by simpa using hμ)

section ScalarDiagonal

variable {rows cols : ℕ}

/-- **Equation (3.13)** of [benzi2005numerical]. For $B \in \mathbb{R}^{m \times n}$ and
$\eta, \varepsilon \in \mathbb{R}$, the **scaled saddle-point matrix** is
$$\begin{bmatrix} \eta I_n & B^T \\ \varepsilon B & 0 \end{bmatrix}.$$
The value $\varepsilon = 1$ gives the symmetric form, and $\varepsilon = -1$ gives the
sign-flipped form (3.10).

**Generalization.** The source defines the two signs. Here $\varepsilon$ is any real
scalar. The spectral theorem uses the two printed values.

The dimensions are natural numbers: $m$ is `rows` and $n$ is `cols`, so $B$ is a
`Matrix (Fin rows) (Fin cols) ℝ`, and the block matrix is indexed by `Fin cols ⊕ Fin rows`. -/
abbrev scaledSaddlePointMatrix (B : Matrix (Fin rows) (Fin cols) ℝ) (η ε : ℝ) :
    Matrix (Fin cols ⊕ Fin rows) (Fin cols ⊕ Fin rows) ℝ :=
  fromBlocks (η • 1) Bᵀ (ε • B) 0

/-- The square root of the discriminant for the sign-flipped form in Theorem 3.8 of
[benzi2005numerical]. For $\eta, \sigma \in \mathbb{R}$ it is the complex number
$$d(\eta, \sigma) = \begin{cases} \sqrt{\eta^2 - 4\sigma^2} & \text{if } 2\sigma \le \eta, \\ i
  \sqrt{4\sigma^2 - \eta^2} & \text{if } 2\sigma > \eta, \end{cases}$$
where $\sqrt{\cdot}$ is the real square root `Real.sqrt`. For $\eta > 0$ and $\sigma \ge 0$ it
satisfies $d(\eta, \sigma)^2 = \eta^2 - 4\sigma^2$. -/
noncomputable def signFlippedDiscriminantRoot (η σ : ℝ) : ℂ :=
  if 2 * σ ≤ η then (Real.sqrt (η ^ 2 - 4 * σ ^ 2) : ℂ)
  else Complex.I * (Real.sqrt (4 * σ ^ 2 - η ^ 2) : ℂ)

private theorem signFlippedDiscriminantRoot_sq {η σ : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) :
    signFlippedDiscriminantRoot η σ ^ 2 = (η : ℂ) ^ 2 - 4 * (σ : ℂ) ^ 2 := by
  unfold signFlippedDiscriminantRoot
  split_ifs with h
  · have hnonneg : 0 ≤ η ^ 2 - 4 * σ ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ η - 2 * σ by linarith)
        (show 0 ≤ η + 2 * σ by positivity)]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
    push_cast
    ring
  · have hnonneg : 0 ≤ 4 * σ ^ 2 - η ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * σ - η by linarith)
        (show 0 ≤ η + 2 * σ by positivity)]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
    push_cast
    ring

/-- **Theorem 3.8** of [benzi2005numerical]. Let $m \le n$, let $B \in \mathbb{R}^{m \times n}$ have
rank $r$ and nonzero singular values $\sigma_1 \ge \dots \ge \sigma_r$, and let $\eta > 0$.
Counted with algebraic multiplicity, the eigenvalues of the symmetric form $\begin{bmatrix} \eta
I & B^T \\ B & 0 \end{bmatrix}$ are

* $0$ with multiplicity $m - r$ and $\eta$ with multiplicity $n - r$;
* for each $k = 1, \dots, r$, the two numbers $\frac{1}{2}\big(\eta \pm \sqrt{\eta^2 +
  4\sigma_k^2}\big)$.

The eigenvalues of the sign-flipped form $\begin{bmatrix} \eta I & B^T \\ -B & 0 \end{bmatrix}$
are $0$ and $\eta$ with the same multiplicities, and for each $k = 1, \dots, r$ the two numbers
$\frac{1}{2}\big(\eta \pm d(\eta, \sigma_k)\big)$, where
$d(\eta, \sigma) = \sqrt{\eta^2 - 4\sigma^2}$ if $2\sigma \le \eta$ and
$d(\eta, \sigma) = i\sqrt{4\sigma^2 - \eta^2}$ otherwise. So each $\sigma_k > \eta / 2$ gives a
pair of complex conjugate eigenvalues, and both roots of the pair appear with their
multiplicities.

The two forms are `BenziGolubLiesen.scaledSaddlePointMatrix B η 1` and
`BenziGolubLiesen.scaledSaddlePointMatrix B η (-1)`, and $d$ is
`BenziGolubLiesen.signFlippedDiscriminantRoot`. The statement is an equality of multisets: the
roots of the characteristic polynomial of the complexified matrix equal the multiset of the
listed numbers. The singular value $\sigma_k$ is `Matrix.sortedSingularValues` at the index
$k - 1$. The proof specializes
`Matrix.roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero`. -/
theorem theorem_3_8 (hmn : rows ≤ cols) (B : Matrix (Fin rows) (Fin cols) ℝ)
    {η : ℝ} (hη : 0 < η) :
    let base := (rows - B.rank) • ({0} : Multiset ℂ) +
      (cols - B.rank) • ({(η : ℂ)} : Multiset ℂ)
    let pair (d : ℂ) := ({((η : ℂ) + d) / 2} : Multiset ℂ) + {((η : ℂ) - d) / 2}
    ((scaledSaddlePointMatrix B η 1).complexify.charpoly.roots =
      base + Finset.univ.val.bind (fun i : Fin B.rank =>
        pair (Real.sqrt (4 * B.sortedSingularValues i ^ 2 + η ^ 2) : ℂ))) ∧
    ((scaledSaddlePointMatrix B η (-1)).complexify.charpoly.roots =
      base + Finset.univ.val.bind (fun i : Fin B.rank =>
        pair (signFlippedDiscriminantRoot η (B.sortedSingularValues i)))) := by
  dsimp only
  constructor
  · refine roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero hmn B η 1 _ ?_
    intro i
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  · refine roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero hmn B η (-1) _ ?_
    intro i
    rw [signFlippedDiscriminantRoot_sq hη (B.sortedSingularValues_nonneg _)]
    push_cast
    ring

/-- **Paragraph after Theorem 3.8** of [benzi2005numerical], corrected. Let
$\eta, \sigma \in \mathbb{R}$ with $\eta < 2\sigma$. Then both eigenvalues
$\frac{1}{2}\big(\eta \pm d(\eta, \sigma)\big)$ of the sign-flipped form in Theorem 3.8 have
real part $\eta / 2$:
$$\operatorname{Re} \tfrac{1}{2}\big(\eta + d(\eta, \sigma)\big) = \operatorname{Re}
  \tfrac{1}{2}\big(\eta - d(\eta, \sigma)\big) = \tfrac{\eta}{2}.$$

**Correction.** The source calls these nonreal eigenvalues purely imaginary. For
$\eta < 2\sigma$ the discriminant root is $d(\eta, \sigma) = i\sqrt{4\sigma^2 - \eta^2}$, so the
formulas of Theorem 3.8 give real part $\eta / 2$, which is nonzero for $\eta > 0$.

The discriminant root $d$ is `BenziGolubLiesen.signFlippedDiscriminantRoot`. -/
theorem signFlipped_roots_re_of_lt {η σ : ℝ} (h : η < 2 * σ) :
    (((η : ℂ) + signFlippedDiscriminantRoot η σ) / 2).re = η / 2 ∧
      (((η : ℂ) - signFlippedDiscriminantRoot η σ) / 2).re = η / 2 := by
  simp [signFlippedDiscriminantRoot, not_le.mpr h, Complex.mul_re]

end ScalarDiagonal

end BenziGolubLiesen
