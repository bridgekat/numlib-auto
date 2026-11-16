/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Spectral bounds for saddle-point matrices

This file bounds the eigenvalues of two kinds of saddle-point matrices. The first is the symmetric
matrix
$$\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$$
with $A \in \mathbb{R}^{n \times n}$ symmetric positive definite and $B \in \mathbb{R}^{m \times n}$
of full row rank. If the eigenvalues of $A$ lie in $[a, b]$ with $a > 0$, and
$\sigma_{\min} \|y\| \le \|B^T y\|$ and $\|Bx\| \le \sigma_{\max} \|x\|$ for all vectors $x$ and
$y$, then its spectrum lies in the union of two intervals, one on each side of $0$ (the bounds of
Rusten and Winther). The second is the sign-flipped matrix
$$\begin{bmatrix} A & D \\ -D^H & C \end{bmatrix}$$
with complex blocks. Its Hermitian part is $\operatorname{diag}(H, C)$, where $H = (A + A^H)/2$, so
its eigenvalues have nonnegative real part when $H$ and $C$ are positive semidefinite, and positive
real part when moreover $H$ is positive definite and $D$ is injective. When $C = 0$ and $D = B^H$ is
injective for some $B \in \mathbb{C}^{m \times n}$, $A$ is positive definite, and
$a \|x\|^2 \le x^H A x$ for all $x$ with $a \ge 4 \|B A^{-1} B^H\|_2$, all eigenvalues of the
sign-flipped matrix are real. These results give Theorems 3.5–3.7 of [benzi2005numerical].

## Main results

* `Matrix.hermitianPart_fromBlocks_neg_conjTranspose`: the Hermitian part of the sign-flipped matrix
  is $\operatorname{diag}(H, C)$ when $C$ is Hermitian.
* `Matrix.re_nonneg_of_mem_spectrum_fromBlocks_neg_conjTranspose`: if $H$ and $C$ are positive
  semidefinite, every eigenvalue of the sign-flipped matrix has nonnegative real part.
* `Matrix.re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose`: if moreover $H$ is positive definite
  and $D$ is injective, every eigenvalue has positive real part.
* `Matrix.PosDef.norm_sq_mulVec_le_l2_opNorm_mul_re_dotProduct`:
  $\|Bx\|^2 \le \|B A^{-1} B^H\|_2 \, x^H A x$ for positive definite $A$.
* `Matrix.im_eq_zero_of_mem_spectrum_fromBlocks_neg_conjTranspose_zero`: the spectrum of the
  sign-flipped matrix with $C = 0$ is real under the bound above.
* `Matrix.spectrum_fromBlocks_transpose_zero_subset`: the interval bounds of Rusten and Winther for
  the symmetric matrix.

## Implementation notes

* Block matrices are `Matrix.fromBlocks`, indexed by `n ⊕ m`. The Hermitian part is
  `Matrix.hermitianPart`.
* The norm $\|\cdot\|_2$ of a matrix is the operator norm induced by the Euclidean norm, from the
  scope `Matrix.Norms.L2Operator`. Vector norms are norms in `EuclideanSpace`, written `‖toLp 2 v‖`.
* The bounds on the eigenvalues of $A$ in `Matrix.spectrum_fromBlocks_transpose_zero_subset` are
  stated in the positive semidefinite order, as $A - aI \succeq 0$ and $bI - A \succeq 0$. The
  results `Matrix.IsHermitian.posSemidef_sub_smul_one_of_le_eigenvalues` and
  `Matrix.IsHermitian.posSemidef_smul_one_sub_of_eigenvalues_le` convert bounds on the eigenvalues
  to this form.
-/

open WithLp
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*}

/-- Let $A \in \mathbb{K}^{n \times n}$, $D \in \mathbb{K}^{n \times m}$ and a Hermitian
$C \in \mathbb{K}^{m \times m}$, over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then the
Hermitian part of the sign-flipped block matrix has no off-diagonal blocks:
$$\operatorname{herm}\begin{bmatrix} A & D \\ -D^H & C \end{bmatrix}
  = \begin{bmatrix} \operatorname{herm}(A) & 0 \\ 0 & C \end{bmatrix},$$
where $\operatorname{herm}(M) = (M + M^H)/2$.

The Hermitian part is `Matrix.hermitianPart`. -/
theorem hermitianPart_fromBlocks_neg_conjTranspose {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix n n 𝕜) (D : Matrix n m 𝕜) {C : Matrix m m 𝕜}
    (hC : C.IsHermitian) :
    hermitianPart (fromBlocks A D (-Dᴴ) C) =
      fromBlocks (hermitianPart A) 0 0 C := by
  ext i j
  cases i <;> cases j <;>
    simp [hermitianPart, fromBlocks_conjTranspose, hC.eq, ← two_mul, mul_add]

private theorem star_dotProduct_fromBlocks_diagonal_mulVec {𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [Fintype m] (A : Matrix n n 𝕜) (C : Matrix m m 𝕜) (v : n ⊕ m → 𝕜) :
    star v ⬝ᵥ (fromBlocks A 0 0 C *ᵥ v) =
      star (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl)) +
        star (v ∘ Sum.inr) ⬝ᵥ (C *ᵥ (v ∘ Sum.inr)) := by
  rw [dotProduct_block, fromBlocks_mulVec]
  simp
  rfl

variable [Fintype n] [Fintype m]

private theorem fromBlocks_mulVec_eq_smul_components {K : Type*} [Semiring K]
    {A : Matrix n n K} {D : Matrix n m K} {B : Matrix m n K} {C : Matrix m m K}
    {v : n ⊕ m → K} {μ : K} (hv : fromBlocks A D B C *ᵥ v = μ • v) :
    let x := v ∘ Sum.inl
    let y := v ∘ Sum.inr
    A *ᵥ x + D *ᵥ y = μ • x ∧ B *ᵥ x + C *ᵥ y = μ • y := by
  rw [fromBlocks_mulVec] at hv
  exact ⟨funext fun i => congrFun hv (Sum.inl i), funext fun i => congrFun hv (Sum.inr i)⟩

/-- Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. Suppose that the symmetric part $(A + A^T)/2$ of $A$ and the
matrix $C$ are positive semidefinite. Then for every $v \in \mathbb{R}^{n + m}$,
$$v^T \begin{bmatrix} A & B^T \\ -B & C \end{bmatrix} v \ge 0.$$

The symmetric part is `Matrix.hermitianPart A`. -/
theorem dotProduct_fromBlocks_neg_transpose_mulVec_nonneg
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef) (v : n ⊕ m → ℝ) :
    0 ≤ v ⬝ᵥ (fromBlocks A Bᵀ (-B) C *ᵥ v) := by
  have hB : (Bᵀ)ᴴ = B := by ext i j; rfl
  rw [show fromBlocks A Bᵀ (-B) C = fromBlocks A Bᵀ (-(Bᵀ)ᴴ) C by rw [hB],
    ← dotProduct_mulVec_hermitianPart,
    hermitianPart_fromBlocks_neg_conjTranspose _ _ hC.isHermitian]
  have h := star_dotProduct_fromBlocks_diagonal_mulVec (hermitianPart A) C v
  simp only [star_trivial] at h
  rw [h]
  exact add_nonneg (by simpa using hA.dotProduct_mulVec_nonneg (v ∘ Sum.inl))
    (by simpa using hC.dotProduct_mulVec_nonneg (v ∘ Sum.inr))

private theorem re_mul_norm_sq_eq_star_dotProduct_hermitianPart_mulVec
    (A : Matrix n n ℂ) (v : n → ℂ) {μ : ℂ} (hv : A *ᵥ v = μ • v) :
    μ.re * ‖toLp 2 v‖ ^ 2 = (star v ⬝ᵥ (hermitianPart A *ᵥ v)).re := by
  rw [star_dotProduct_hermitianPart_mulVec, hv, dotProduct_smul, smul_eq_mul,
    star_dotProduct_self]
  change _ = (μ * ((‖toLp 2 v‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

variable [DecidableEq n] [DecidableEq m]

/-- Let $A \in \mathbb{C}^{n \times n}$ have positive semidefinite Hermitian part $(A + A^H)/2$.
Then every eigenvalue $\mu$ of $A$ satisfies $\operatorname{Re} \mu \ge 0$.

For an eigenvector $v$, $\operatorname{Re} \mu \, \|v\|^2 = v^H \operatorname{herm}(A) v$. The
Hermitian part is `Matrix.hermitianPart A`. -/
theorem re_nonneg_of_mem_spectrum_of_posSemidef_hermitianPart
    {A : Matrix n n ℂ} (hA : (hermitianPart A).PosSemidef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    0 ≤ μ.re := by
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).1 hμ
  have h := (Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg v)).1
  rw [← re_mul_norm_sq_eq_star_dotProduct_hermitianPart_mulVec A v hv] at h
  exact nonneg_of_mul_nonneg_left h (pow_pos (norm_pos_iff.2 (by simpa using hv0)) _)

/-- Let $A \in \mathbb{C}^{n \times n}$, $D \in \mathbb{C}^{n \times m}$ and
$C \in \mathbb{C}^{m \times m}$. Suppose that the Hermitian part $(A + A^H)/2$ of $A$ and the
matrix $C$ are positive semidefinite. Then every eigenvalue $\mu$ of
$$\begin{bmatrix} A & D \\ -D^H & C \end{bmatrix}$$
satisfies $\operatorname{Re} \mu \ge 0$.

The Hermitian part of the block matrix is $\operatorname{diag}(\operatorname{herm}(A), C)$ by
`Matrix.hermitianPart_fromBlocks_neg_conjTranspose`, and the result follows from
`Matrix.re_nonneg_of_mem_spectrum_of_posSemidef_hermitianPart`. Positive semidefinite is
`Matrix.PosSemidef`, which includes the condition that $C$ is Hermitian. -/
theorem re_nonneg_of_mem_spectrum_fromBlocks_neg_conjTranspose
    {A : Matrix n n ℂ} (D : Matrix n m ℂ) {C : Matrix m m ℂ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (fromBlocks A D (-Dᴴ) C)) :
    0 ≤ μ.re := by
  refine re_nonneg_of_mem_spectrum_of_posSemidef_hermitianPart ?_ hμ
  rw [hermitianPart_fromBlocks_neg_conjTranspose _ _ hC.isHermitian]
  refine .of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · rw [IsHermitian, fromBlocks_conjTranspose, hA.isHermitian.eq, hC.isHermitian.eq,
      conjTranspose_zero, conjTranspose_zero]
  · rw [star_dotProduct_fromBlocks_diagonal_mulVec]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hC.dotProduct_mulVec_nonneg _)

/-- Let $A \in \mathbb{C}^{n \times n}$, $D \in \mathbb{C}^{n \times m}$ and
$C \in \mathbb{C}^{m \times m}$. Suppose that the Hermitian part $(A + A^H)/2$ of $A$ is
positive definite, that $C$ is positive semidefinite, and that $D$ is injective. Then every
eigenvalue $\mu$ of
$$\begin{bmatrix} A & D \\ -D^H & C \end{bmatrix}$$
satisfies $\operatorname{Re} \mu > 0$.

The Hermitian part is `Matrix.hermitianPart A`. For an eigenvector $(x, y)$, the component $x$
is nonzero, because $x = 0$ gives $Dy = 0$ and then $y = 0$. Hence $\operatorname{Re} \mu \,
\|(x, y)\|^2 = x^H \operatorname{herm}(A) x + y^H C y > 0$. -/
theorem re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose
    {A : Matrix n n ℂ} {D : Matrix n m ℂ} {C : Matrix m m ℂ}
    (hA : (hermitianPart A).PosDef) (hC : C.PosSemidef) (hD : Function.Injective D.mulVec)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (fromBlocks A D (-Dᴴ) C)) : 0 < μ.re := by
  let M := fromBlocks A D (-Dᴴ) C
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul M μ).1 hμ
  let x := v ∘ Sum.inl
  let y := v ∘ Sum.inr
  have hx : x ≠ 0 := by
    intro hx0
    have he : A *ᵥ x + D *ᵥ y = μ • x := (fromBlocks_mulVec_eq_smul_components hv).1
    have hy : y = 0 := hD (by simpa [hx0] using he)
    apply hv0
    ext i
    cases i with
    | inl i => exact congrFun hx0 i
    | inr i => exact congrFun hy i
  have hq := re_mul_norm_sq_eq_star_dotProduct_hermitianPart_mulVec M v hv
  rw [show hermitianPart M = fromBlocks (hermitianPart A) 0 0 C from
    hermitianPart_fromBlocks_neg_conjTranspose _ _ hC.isHermitian,
    star_dotProduct_fromBlocks_diagonal_mulVec, Complex.add_re] at hq
  have h1 := (Complex.pos_iff.1 (hA.dotProduct_mulVec_pos hx)).1
  have h2 := (Complex.nonneg_iff.1 (hC.dotProduct_mulVec_nonneg y)).1
  exact pos_of_mul_pos_left (hq ▸ add_pos_of_pos_of_nonneg h1 h2) (sq_nonneg _)

open scoped MatrixOrder in
/-- Let $A \in \mathbb{C}^{n \times n}$ be Hermitian positive definite and let
$B \in \mathbb{C}^{m \times n}$. Then for every $x \in \mathbb{C}^n$,
$$\|Bx\|^2 \le \|B A^{-1} B^H\|_2 \, \operatorname{Re}(x^H A x).$$

The norm of $B A^{-1} B^H$ is the operator norm induced by the Euclidean norm. Since $A$ is
Hermitian, $x^H A x$ is real, and the statement takes its real part. -/
theorem PosDef.norm_sq_mulVec_le_l2_opNorm_mul_re_dotProduct
    {A : Matrix n n ℂ} (hA : A.PosDef) (B : Matrix m n ℂ) (x : n → ℂ) :
    ‖toLp 2 (B *ᵥ x)‖ ^ 2 ≤ ‖B * A⁻¹ * Bᴴ‖ * (star x ⬝ᵥ (A *ᵥ x)).re := by
  let R := CFC.sqrt A
  have hRs : Rᴴ = R :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian.eq
  have hR : Rᴴ * R = A := by
    rw [hRs, ← pow_two]
    exact CFC.sq_sqrt A hA.posSemidef.nonneg
  have hRu : IsUnit R := isUnit_of_mul_isUnit_right (hR.symm ▸ hA.isUnit)
  let T := B * R⁻¹
  have hTR : T * R = B := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det R).1 hRu), Matrix.mul_one]
  have hTnorm : ‖T‖ ^ 2 = ‖B * A⁻¹ * Bᴴ‖ := by
    calc
      ‖T‖ ^ 2 = ‖T * Tᴴ‖ := by
        have h := l2_opNorm_conjTranspose_mul_self Tᴴ
        rw [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, ← pow_two] at h
        exact h.symm
      _ = ‖B * A⁻¹ * Bᴴ‖ := by
        congr 1
        rw [← hR, mul_inv_rev, ← conjTranspose_nonsing_inv]
        simp [T, conjTranspose_mul, Matrix.mul_assoc]
  have hq : ‖toLp 2 (R *ᵥ x)‖ ^ 2 = (star x ⬝ᵥ (A *ᵥ x)).re := by
    have h := star_dotProduct_self (R *ᵥ x)
    change _ = ((‖toLp 2 (R *ᵥ x)‖ : ℝ) : ℂ) ^ 2 at h
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hR, ← Complex.ofReal_pow] at h
    exact (congrArg Complex.re h).symm
  have hn : ‖toLp 2 (B *ᵥ x)‖ ≤ ‖T‖ * ‖toLp 2 (R *ᵥ x)‖ := by
    rw [← hTR, ← mulVec_mulVec]
    exact l2_opNorm_mulVec T (toLp 2 (R *ᵥ x))
  calc
    ‖toLp 2 (B *ᵥ x)‖ ^ 2 ≤ (‖T‖ * ‖toLp 2 (R *ᵥ x)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by rw [mul_pow, hTnorm, hq]

omit [DecidableEq n] [DecidableEq m] in
private theorem saddlePoint_eigenvector_quadratic {K : Type*} [CommSemiring K]
    {A : Matrix n n K} {D : Matrix n m K} {B : Matrix m n K}
    {x : n → K} {y : m → K} {μ : K}
    (hx : A *ᵥ x + D *ᵥ y = μ • x) (hy : B *ᵥ x = μ • y) :
    μ ^ 2 • x = μ • (A *ᵥ x) + D *ᵥ (B *ᵥ x) := by
  calc
    μ ^ 2 • x = μ • (μ • x) := by rw [smul_smul, pow_two]
    _ = μ • (A *ᵥ x + D *ᵥ y) := by rw [hx]
    _ = μ • (A *ᵥ x) + D *ᵥ (B *ᵥ x) := by rw [smul_add, hy, mulVec_smul]

private theorem im_eq_zero_of_quadratic_of_nonneg_discriminant {μ : ℂ}
    {s q t : ℝ} (hs : 0 < s) (hdisc : 4 * s * t ≤ q ^ 2)
    (hμ : μ ^ 2 * (s : ℂ) - μ * (q : ℂ) + (t : ℂ) = 0) : μ.im = 0 := by
  by_contra him
  have hRe := congrArg Complex.re hμ
  have hIm := congrArg Complex.im hμ
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im, mul_zero, add_zero, zero_add, sub_zero] at hRe hIm
  have hq : q = 2 * μ.re * s := by
    have hfactor : μ.im * (2 * μ.re * s - q) = 0 := by linarith only [hIm]
    exact (sub_eq_zero.1 ((mul_eq_zero.1 hfactor).resolve_left him)).symm
  have ht : t = (μ.re ^ 2 + μ.im ^ 2) * s := by
    rw [hq] at hRe
    linarith only [hRe]
  rw [hq, ht] at hdisc
  have hpos : 0 < 4 * s * s * μ.im ^ 2 := by positivity
  nlinarith only [hpos, hdisc]

/-- Let $A \in \mathbb{C}^{n \times n}$ be Hermitian positive definite and let
$B \in \mathbb{C}^{m \times n}$ have injective conjugate transpose $B^H$. Let $a \in \mathbb{R}$
satisfy $a \|x\|^2 \le \operatorname{Re}(x^H A x)$ for all $x \in \mathbb{C}^n$, and suppose
that
$$4 \|B A^{-1} B^H\|_2 \le a.$$
Then every eigenvalue $\mu$ of
$$\begin{bmatrix} A & B^H \\ -B & 0 \end{bmatrix}$$
is real.

The norm of $B A^{-1} B^H$ is the operator norm induced by the Euclidean norm. The proof shows
that $\mu$ is a root of a real quadratic with nonnegative discriminant, using
`Matrix.PosDef.norm_sq_mulVec_le_l2_opNorm_mul_re_dotProduct`. -/
theorem im_eq_zero_of_mem_spectrum_fromBlocks_neg_conjTranspose_zero
    {A : Matrix n n ℂ} {B : Matrix m n ℂ} (hA : A.PosDef)
    (hB : Function.Injective Bᴴ.mulVec) {a : ℝ}
    (ha : ∀ x : n → ℂ, a * ‖toLp 2 x‖ ^ 2 ≤ (star x ⬝ᵥ (A *ᵥ x)).re)
    (hS : 4 * ‖B * A⁻¹ * Bᴴ‖ ≤ a)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (fromBlocks A Bᴴ (-B) 0)) : μ.im = 0 := by
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).1 hμ
  let x := v ∘ Sum.inl
  let y := v ∘ Sum.inr
  obtain ⟨h₁, h₂⟩ := fromBlocks_mulVec_eq_smul_components hv
  change A *ᵥ x + Bᴴ *ᵥ y = μ • x at h₁
  have h₂ : (-B) *ᵥ x = μ • y := by simpa [x, y] using h₂
  have hx : x ≠ 0 := by
    intro hx0
    have hy : y = 0 := hB (by simpa [hx0] using h₁)
    apply hv0
    ext i
    cases i with
    | inl i => exact congrFun hx0 i
    | inr i => exact congrFun hy i
  let s := ‖toLp 2 x‖ ^ 2
  let q := (star x ⬝ᵥ (A *ᵥ x)).re
  let t := ‖toLp 2 (B *ᵥ x)‖ ^ 2
  have hs : 0 < s := pow_pos (norm_pos_iff.2 (by simpa using hx)) 2
  have hq : 0 ≤ q := (Complex.nonneg_iff.1 (hA.posSemidef.dotProduct_mulVec_nonneg x)).1
  have hqcast : star x ⬝ᵥ (A *ᵥ x) = (q : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hA.isHermitian.im_star_dotProduct_mulVec_self x
  have htcast : star x ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ x)) = (t : ℂ) := by
    rw [dotProduct_mulVec, ← star_mulVec]
    change star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = _
    simpa [t, Complex.ofReal_pow] using star_dotProduct_self (B *ᵥ x)
  have hscast : star x ⬝ᵥ x = (s : ℂ) := by
    simpa [s, Complex.ofReal_pow] using star_dotProduct_self x
  have he := congrArg (fun w => star x ⬝ᵥ w) (saddlePoint_eigenvector_quadratic h₁ h₂)
  simp only [neg_mulVec, mulVec_neg, dotProduct_smul, smul_eq_mul, dotProduct_add,
    dotProduct_neg, hscast, hqcast, htcast] at he
  have hquad : μ ^ 2 * (s : ℂ) - μ * (q : ℂ) + (t : ℂ) = 0 := by linear_combination he
  refine im_eq_zero_of_quadratic_of_nonneg_discriminant hs ?_ hquad
  calc
    4 * s * t ≤ 4 * s * (‖B * A⁻¹ * Bᴴ‖ * q) :=
      mul_le_mul_of_nonneg_left
        (hA.norm_sq_mulVec_le_l2_opNorm_mul_re_dotProduct B x) (by positivity)
    _ = (4 * ‖B * A⁻¹ * Bᴴ‖ * s) * q := by ring
    _ ≤ (a * s) * q := by gcongr
    _ ≤ q ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right (ha x) hq

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric with eigenvalues $\lambda_i$, and let
$c, d \in \mathbb{R}$. If $c \lambda_i + d \ge 0$ for every $i$, then $cA + dI$ is positive
semidefinite.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.posSemidef_smul_add_smul_one {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (c d : ℝ) (h : ∀ i, 0 ≤ c * hA.eigenvalues i + d) :
    (c • A + d • 1).PosSemidef := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal hA.eigenvalues
  have hU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hAD : A = U * D * Uᴴ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.spectral_theorem
  have hscale : U * (c • D + d • 1) * Uᴴ = c • A + d • 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, hU, ← hAD]
  have hdiag : c • D + d • 1 = diagonal (fun i => c * hA.eigenvalues i + d) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  rw [← hscale, hdiag]
  exact (PosSemidef.diagonal h).mul_mul_conjTranspose_same U

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, and let $a \in \mathbb{R}$ be at most every
eigenvalue of $A$. Then $A - aI$ is positive semidefinite.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.posSemidef_sub_smul_one_of_le_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ} (h : ∀ i, a ≤ hA.eigenvalues i) :
    (A - a • 1).PosSemidef := by
  simpa [sub_eq_add_neg, neg_smul] using hA.posSemidef_smul_add_smul_one 1 (-a)
    (fun i => by linarith [h i])

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, and let $b \in \mathbb{R}$ be at least every
eigenvalue of $A$. Then $bI - A$ is positive semidefinite.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.posSemidef_smul_one_sub_of_eigenvalues_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {b : ℝ} (h : ∀ i, hA.eigenvalues i ≤ b) :
    (b • 1 - A).PosSemidef := by
  simpa [sub_eq_add_neg, add_comm] using hA.posSemidef_smul_add_smul_one (-1) b
    (fun i => by linarith [h i])

private theorem lower_energy_bound {A : Matrix n n ℝ} {a : ℝ}
    (hA : (A - a • 1).PosSemidef) (x : n → ℝ) :
    a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have h := hA.dotProduct_mulVec_nonneg x
  simpa [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, sub_nonneg] using h

private theorem upper_energy_bound {A : Matrix n n ℝ} {b : ℝ}
    (hA : (b • 1 - A).PosSemidef) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ b * (x ⬝ᵥ x) := by
  have h := hA.dotProduct_mulVec_nonneg x
  simpa [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, sub_nonneg] using h

omit [DecidableEq m] in
private theorem lower_sq_stretch_of_negative_eigenpair
    {A : Matrix n n ℝ} {B : Matrix m n ℝ} {b smin μ : ℝ}
    (hA : A.PosDef) (hupper : (b • 1 - A).PosSemidef)
    (hB : Function.Injective Bᵀ.mulVec) (hmin : 0 ≤ smin)
    (hBmin : ∀ y : m → ℝ, smin * ‖toLp 2 y‖ ≤ ‖toLp 2 (Bᵀ *ᵥ y)‖)
    (hμ : μ < 0) {x : n → ℝ} {y : m → ℝ} (hy : y ≠ 0)
    (h₁ : A *ᵥ x + Bᵀ *ᵥ y = μ • x) (h₂ : B *ᵥ x = μ • y) :
    smin ^ 2 ≤ μ ^ 2 - b * μ := by
  let N := A - μ • 1
  let z := Bᵀ *ᵥ y
  have hN : N.PosSemidef := by
    simpa [N, sub_eq_add_neg, neg_smul] using hA.posSemidef.add
      ((PosSemidef.one : (1 : Matrix n n ℝ).PosSemidef).smul (neg_nonneg.mpr hμ.le))
  have hz : z ≠ 0 := fun hz => hy (hB (by simpa [z] using hz))
  have hzz : 0 < z ⬝ᵥ z := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 (by simpa using hz)) 2
  have hyy : 0 < y ⬝ᵥ y := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 (by simpa using hy)) 2
  have hNx : N *ᵥ x = -z := by
    simp only [N, sub_mulVec, smul_mulVec, one_mulVec]
    rw [← h₁, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hq : x ⬝ᵥ (N *ᵥ x) = (-μ) * (y ⬝ᵥ y) := by
    rw [hNx, dotProduct_neg, dotProduct_transpose_mulVec, h₂, dotProduct_smul, smul_eq_mul,
      neg_mul]
  have hupper' : z ⬝ᵥ (N *ᵥ z) ≤ (b - μ) * (z ⬝ᵥ z) := by
    simp only [N, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    linarith only [upper_energy_bound hupper z]
  have hsquare : (z ⬝ᵥ z) ^ 2 ≤ (z ⬝ᵥ z) * ((b - μ) * (-μ) * (y ⬝ᵥ y)) := by
    calc
      (z ⬝ᵥ z) ^ 2 = (z ⬝ᵥ (N *ᵥ x)) ^ 2 := by rw [hNx, dotProduct_neg, neg_sq]
      _ ≤ (z ⬝ᵥ (N *ᵥ z)) * (x ⬝ᵥ (N *ᵥ x)) := hN.sq_dotProduct_mulVec_le z x
      _ ≤ ((b - μ) * (z ⬝ᵥ z)) * ((-μ) * (y ⬝ᵥ y)) := by
        rw [hq]
        exact mul_le_mul_of_nonneg_right hupper' (mul_nonneg (neg_nonneg.mpr hμ.le) hyy.le)
      _ = _ := by ring
  rw [pow_two] at hsquare
  have hbound := le_of_mul_le_mul_left hsquare hzz
  have hstretch : smin ^ 2 * (y ⬝ᵥ y) ≤ z ⬝ᵥ z := by
    rw [dotProduct_self_eq_norm_sq, dotProduct_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hmin (norm_nonneg _)) (hBmin y) 2
  have hres := le_of_mul_le_mul_right (hstretch.trans hbound) hyy
  nlinarith only [hres]

/-- The **bounds of Rusten and Winther.** Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive
definite and let $B \in \mathbb{R}^{m \times n}$ have injective transpose $B^T$. Let $a, b,
\sigma_{\min}, \sigma_{\max} \in \mathbb{R}$ with $a > 0$ and $\sigma_{\min} \ge 0$. Suppose
that $A - aI$ and $bI - A$ are positive semidefinite, that $\sigma_{\min} \|y\| \le \|B^T y\|$
for all $y \in \mathbb{R}^m$, and that $\|Bx\| \le \sigma_{\max} \|x\|$ for all
$x \in \mathbb{R}^n$. Then every real eigenvalue of
$$\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$$
lies in
$$\left[\frac{a - \sqrt{a^2 + 4 \sigma_{\max}^2}}{2},
  \frac{b - \sqrt{b^2 + 4 \sigma_{\min}^2}}{2}\right]
  \cup \left[a, \frac{b + \sqrt{b^2 + 4 \sigma_{\max}^2}}{2}\right].$$

The conclusion is about `spectrum ℝ`, the real spectrum of the real matrix; the matrix is
symmetric, so all its eigenvalues are real. This gives Theorem 3.5 of [benzi2005numerical],
where $a$ and $b$ are the extreme eigenvalues of $A$ and $\sigma_{\min}$ and $\sigma_{\max}$ are
the extreme singular values of $B$. -/
theorem spectrum_fromBlocks_transpose_zero_subset
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) (hA : A.PosDef)
    (hB : Function.Injective Bᵀ.mulVec)
    {a b smin smax : ℝ} (ha : 0 < a) (hmin : 0 ≤ smin)
    (hlo : (A - a • 1).PosSemidef) (hhi : (b • 1 - A).PosSemidef)
    (hBmin : ∀ y : m → ℝ, smin * ‖toLp 2 y‖ ≤ ‖toLp 2 (Bᵀ *ᵥ y)‖)
    (hBmax : ∀ x : n → ℝ, ‖toLp 2 (B *ᵥ x)‖ ≤ smax * ‖toLp 2 x‖) :
    spectrum ℝ (fromBlocks A Bᵀ B 0) ⊆
      Set.Icc ((a - Real.sqrt (a ^ 2 + 4 * smax ^ 2)) / 2)
        ((b - Real.sqrt (b ^ 2 + 4 * smin ^ 2)) / 2) ∪
      Set.Icc a ((b + Real.sqrt (b ^ 2 + 4 * smax ^ 2)) / 2) := by
  intro μ hμ
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).1 hμ
  let x := v ∘ Sum.inl
  let y := v ∘ Sum.inr
  obtain ⟨h₁, h₂⟩ := fromBlocks_mulVec_eq_smul_components hv
  change A *ᵥ x + Bᵀ *ᵥ y = μ • x at h₁
  have h₂ : B *ᵥ x = μ • y := by simpa [x, y] using h₂
  have hx : x ≠ 0 := by
    intro hx0
    have hy : y = 0 := hB (by simpa [hx0] using h₁)
    apply hv0
    ext i
    cases i with
    | inl i => exact congrFun hx0 i
    | inr i => exact congrFun hy i
  have hμne : μ ≠ 0 := by
    intro hμ0
    have hU : IsUnit (fromBlocks A Bᵀ B 0) := by
      simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
        isUnit_saddleMatrix_zero hA hB
    exact spectrum.zero_notMem ℝ hU (hμ0 ▸ hμ)
  let xx := x ⬝ᵥ x
  let q := x ⬝ᵥ (A *ᵥ x)
  let tt := (B *ᵥ x) ⬝ᵥ (B *ᵥ x)
  have hxx : 0 < xx := by
    rw [show xx = x ⬝ᵥ x from rfl, dotProduct_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 (by simpa using hx)) 2
  have hqlo : a * xx ≤ q := lower_energy_bound hlo x
  have hqhi : q ≤ b * xx := upper_energy_bound hhi x
  have hb : 0 < b := ha.trans_le (le_of_mul_le_mul_right (hqlo.trans hqhi) hxx)
  have htt : 0 ≤ tt := by
    change 0 ≤ (B *ᵥ x) ⬝ᵥ (B *ᵥ x)
    rw [dotProduct_self_eq_norm_sq]
    positivity
  have httmax : tt ≤ smax ^ 2 * xx := by
    change (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ smax ^ 2 * (x ⬝ᵥ x)
    rw [dotProduct_self_eq_norm_sq, dotProduct_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hBmax x) 2
  have heq : μ ^ 2 * xx = μ * q + tt := by
    have h := congrArg (fun w => x ⬝ᵥ w) (saddlePoint_eigenvector_quadratic h₁ h₂)
    simpa only [dotProduct_smul, smul_eq_mul, dotProduct_add, dotProduct_transpose_mulVec,
      xx, q, tt] using h
  rcases lt_or_gt_of_ne hμne with hneg | hpos
  · have hquad : μ ^ 2 ≤ a * μ + smax ^ 2 := by
      apply le_of_mul_le_mul_right _ hxx
      rw [heq, add_mul]
      have hq' := mul_le_mul_of_nonpos_left hqlo hneg.le
      linarith only [hq', httmax]
    have hy : y ≠ 0 := by
      intro hy0
      have h' : A *ᵥ x = μ • x := by simpa [hy0] using h₁
      have hq' : q = μ * xx := by simp [q, xx, h', dotProduct_smul]
      have ha' := mul_pos ha hxx
      have hneg' := mul_neg_of_neg_of_pos hneg hxx
      linarith only [hqlo, hq', ha', hneg']
    have hquad' := lower_sq_stretch_of_negative_eigenpair hA hhi hB hmin hBmin hneg hy h₁ h₂
    refine Or.inl ⟨?_, ?_⟩
    · have hs : Real.sqrt (a ^ 2 + 4 * smax ^ 2) ^ 2 = a ^ 2 + 4 * smax ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hle : a - 2 * μ ≤ Real.sqrt (a ^ 2 + 4 * smax ^ 2) :=
        le_of_sq_le_sq (by nlinarith only [hs, hquad]) (Real.sqrt_nonneg _)
      linarith only [hle]
    · have hs : Real.sqrt (b ^ 2 + 4 * smin ^ 2) ^ 2 = b ^ 2 + 4 * smin ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hle : Real.sqrt (b ^ 2 + 4 * smin ^ 2) ≤ b - 2 * μ :=
        le_of_sq_le_sq (by nlinarith only [hs, hquad']) (by linarith only [hb, hneg])
      linarith only [hle]
  · have hquad : μ ^ 2 ≤ b * μ + smax ^ 2 := by
      apply le_of_mul_le_mul_right _ hxx
      rw [heq, add_mul]
      have hq' := mul_le_mul_of_nonneg_left hqhi hpos.le
      linarith only [hq', httmax]
    refine Or.inr ⟨?_, ?_⟩
    · apply le_of_mul_le_mul_right _ (mul_pos hpos hxx)
      have hq' := mul_le_mul_of_nonneg_left hqlo hpos.le
      linarith only [hq', heq, htt]
    · have hs : Real.sqrt (b ^ 2 + 4 * smax ^ 2) ^ 2 = b ^ 2 + 4 * smax ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hle : 2 * μ - b ≤ Real.sqrt (b ^ 2 + 4 * smax ^ 2) :=
        le_of_sq_le_sq (by nlinarith only [hs, hquad]) (Real.sqrt_nonneg _)
      linarith only [hle]

end Matrix
