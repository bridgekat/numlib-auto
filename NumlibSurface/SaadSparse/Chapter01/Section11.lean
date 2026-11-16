/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.HermitianPart
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 1.11: Positive-definite matrices

This module formalizes §1.11 of [saad2003iterative]. The book calls a real matrix
$A \in \mathbb{R}^{n \times n}$ **positive definite** when $(Au, u) > 0$ for every nonzero
$u \in \mathbb{R}^n$ (1.48), with no symmetry assumed, and symmetric positive definite (SPD) when it
is moreover symmetric. A matrix splits as $A = H + iS$ with $H = (A + A^H)/2$ and
$S = (A - A^H)/(2i)$ Hermitian (1.49)–(1.52).

The module proves Theorem 1.34, that a positive definite matrix is nonsingular and satisfies
$(Au, u) \ge \alpha \|u\|_2^2$ for some $\alpha > 0$, with the constant $\lambda_{\min}(H)$ of the
book; and Bendixson's Theorem 1.35, that every eigenvalue $\mu$ of a complex matrix satisfies
$\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H)$ and $\lambda_{\min}(S) \le
\operatorname{Im} \mu \le \lambda_{\max}(S)$. It also defines the $B$-inner product
$(x, y)_B = (Bx, y)$ (1.57) and self-adjointness with respect to it, with the examples of Problem
P-1.18. The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.HermitianPart`,
`Numlib.Analysis.InnerProductSpace.Coercive`, `Numlib.Analysis.InnerProductSpace.Energy` and
`Numlib.Eigen.Perturbation`.

## Main definitions

* Equation (1.48), `Matrix.IsPositiveReal`: the positive definite real matrices of the book,
  $(Au, u) > 0$ for $u \neq 0$.
* §1.11, `Matrix.IsSPD`: the symmetric positive definite real matrices.
* Equation (1.57), `Matrix.energyInner`: the $B$-inner product $(x, y)_B = (Bx, y)$.
* §1.11, `Matrix.IsSelfAdjointWrt`: $A$ is self-adjoint for the $B$-inner product.

## Main results

* Theorem 1.34, `SaadSparse.Chapter01.theorem_1_34`: a positive definite real matrix is nonsingular,
  and $(Au, u) \ge \alpha \|u\|_2^2$ for some $\alpha > 0$.
* Theorem 1.34, `SaadSparse.Chapter01.theorem_1_34'`: $(Au, u) \ge \lambda_{\min}(H) \|u\|_2^2$ for
  every real matrix $A$, with $H$ the Hermitian part of $A$.
* Theorem 1.35, `SaadSparse.Chapter01.theorem_1_35_re`: every eigenvalue $\mu$ satisfies
  $\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H)$.
* Theorem 1.35, `SaadSparse.Chapter01.theorem_1_35_im`: every eigenvalue $\mu$ satisfies
  $\lambda_{\min}(S) \le \operatorname{Im} \mu \le \lambda_{\max}(S)$.
* Theorem 1.35, `SaadSparse.Chapter01.theorem_1_35`: every eigenvalue lies in the rectangle
  $[\lambda_{\min}(H), \lambda_{\max}(H)] \times [\lambda_{\min}(S), \lambda_{\max}(S)]$
  (Bendixson's theorem).
* Problem P-1.18, `Matrix.isSelfAdjointWrt_inv_mul` and `Matrix.isSelfAdjointWrt_mul`: for $C$
  symmetric and $B$ SPD, the matrices $B^{-1} C$ and $CB$ are self-adjoint for the $B$-inner
  product.

## Implementation notes

* The decomposition (1.49)–(1.52) is the backbone's `Matrix.hermitianPart` and
  `Matrix.skewHermitianPart` of `Numlib.LinearAlgebra.Matrix.HermitianPart`: (1.50) is
  `Matrix.hermitianPart`, (1.51) is `Matrix.skewHermitianPart`, (1.49) is
  `Matrix.eq_hermitianPart_add_I_smul_skewHermitianPart`, and (1.52) is
  `Matrix.hermitianPart_isHermitian` with `Matrix.skewHermitianPart_isHermitian`.
* The positive definiteness of the book is `Matrix.IsPositiveReal`. Its backbone counterpart is
  `LinearMap.IsCoercive` of `Matrix.toEuclideanLin A`, and the equivalence
  `Matrix.isPositiveReal_iff_isCoercive` carries every result over.
* The numbers $\lambda_{\min}$ and $\lambda_{\max}$ of a Hermitian matrix are `SaadSparse.lambdaMin`
  and `SaadSparse.lambdaMax`, which need $n \ge 1$.
-/

open Matrix Finset

open scoped SaadSparse ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### Positive definite matrices in the sense of the book (1.48) -/

/-- **Equation (1.48)** of [saad2003iterative]. A real matrix $A \in \mathbb{R}^{n \times n}$ is
**positive definite** if
$$(Au, u) > 0 \quad \text{for every nonzero } u \in \mathbb{R}^n.$$
No symmetry is assumed.

The inner product is the dot product `(A *ᵥ u) ⬝ᵥ u` on `Fin n → ℝ`. -/
def IsPositiveReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u : Fin n → ℝ, u ≠ 0 → 0 < (A *ᵥ u) ⬝ᵥ u

/-- **Section 1.11** of [saad2003iterative], symmetric positive definite matrices. A real matrix
$A \in \mathbb{R}^{n \times n}$ is **symmetric positive definite** (SPD) if it is symmetric and
positive definite in the sense of (1.48). -/
def IsSPD (A : Matrix (Fin n) (Fin n) ℝ) : Prop := A.IsSymm ∧ A.IsPositiveReal

/-- A real matrix $A$ is positive definite in the sense of (1.48) if and only if the operator
$u \mapsto Au$ on $\mathbb{R}^n$ is coercive, that is $(Au, u) \ge c \|u\|_2^2$ for some $c > 0$
(`LinearMap.IsCoercive`). -/
theorem isPositiveReal_iff_isCoercive (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsPositiveReal ↔ (toEuclideanLin A).IsCoercive := by
  rw [LinearMap.isCoercive_iff_forall_pos]
  constructor
  · intro h x hx
    have hx' : WithLp.ofLp x ≠ 0 := fun hc => hx (by ext i; exact congrFun hc i)
    simpa [SaadSparse.real_inner_apply_self, RCLike.re_to_real] using h _ hx'
  · intro h u hu
    have hu' : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) ≠ 0 := fun hc =>
      hu (by ext i; exact congrFun (congrArg WithLp.ofLp hc) i)
    have hpos := h _ hu'
    rw [SaadSparse.real_inner_apply_self] at hpos
    simpa [RCLike.re_to_real] using hpos

/-- A real matrix is symmetric positive definite in the sense of the book if and only if it is
positive definite in the sense of Mathlib, `Matrix.PosDef`. -/
theorem isSPD_iff_posDef (A : Matrix (Fin n) (Fin n) ℝ) : A.IsSPD ↔ A.PosDef := by
  rw [posDef_iff_dotProduct_mulVec, IsSPD]
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨isHermitian_iff_isSymm.mpr hs, fun x hx => by simpa [dotProduct_comm] using hp x hx⟩
  · rintro ⟨hh, hp⟩
    exact ⟨isHermitian_iff_isSymm.mp hh, fun x hx => by simpa [dotProduct_comm] using hp hx⟩

/-- If $A$ is symmetric positive definite, the operator $u \mapsto Au$ on $\mathbb{R}^n$ is
symmetric and coercive (`LinearMap.IsSymmetricCoercive`). This combines
`Matrix.isSPD_iff_posDef` and `Matrix.posDef_iff_isSymmetricCoercive`. -/
theorem IsSPD.isSymmetricCoercive {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSPD) :
    (toEuclideanLin A).IsSymmetricCoercive :=
  (posDef_iff_isSymmetricCoercive A).mp ((isSPD_iff_posDef A).mp hA)

/-! ### The energy inner product, or $B$-inner product (1.57) -/

/-- **Equation (1.57)** of [saad2003iterative]. For $B \in \mathbb{K}^{n \times n}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, the **$B$-inner product** of
$x, y \in \mathbb{K}^n$ is
$$(x, y)_B = (Bx, y).$$

The book uses it for a symmetric positive definite $B$; the definition takes any $B$. In the
convention of Mathlib it is `inner 𝕜 y (B ⬝ x)`. -/
noncomputable def energyInner (B : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    𝕜 := inner 𝕜 y (B ⬝ x)

/-- **Section 1.11** of [saad2003iterative], self-adjointness for the $B$-inner product. For
$A, B \in \mathbb{K}^{n \times n}$, the matrix $A$ is **self-adjoint with respect to the
$B$-inner product** if
$$(Ax, y)_B = (x, Ay)_B \quad \text{for all } x, y \in \mathbb{K}^n.$$
-/
def IsSelfAdjointWrt (B A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ x y : EuclideanSpace 𝕜 (Fin n), energyInner B (A ⬝ x) y = energyInner B x (A ⬝ y)

/-- For $B \in \mathbb{K}^{n \times n}$, the $B$-inner product $(x, y)_B$ is the complex conjugate
of the backbone's `energyInner` of the operator of $B$ at $(x, y)$. Over $\mathbb{R}$ the two
agree. -/
theorem energyInner_eq (B : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    energyInner B x y = starRingEnd 𝕜 (_root_.energyInner (toEuclideanLin B) x y) := by
  rw [energyInner, _root_.energyInner, inner_conj_symm]

/-- For $B \in \mathbb{R}^{n \times n}$, the $B$-inner product $(x, y)_B$ equals the backbone's
`energyInner` of the operator of $B$ at $(x, y)$. -/
theorem real_energyInner_eq (B : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B x y = _root_.energyInner (toEuclideanLin B) x y := by
  rw [energyInner_eq]; simp

section BInner

variable {B : Matrix (Fin n) (Fin n) ℝ}

/-- For a symmetric positive definite $B \in \mathbb{R}^{n \times n}$, the $B$-inner product is
symmetric: $(x, y)_B = (y, x)_B$. This is axiom (i) of an inner product in §1.4 over
$\mathbb{R}$. -/
theorem energyInner_comm (hB : B.IsSPD) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B x y = energyInner B y x := by
  rw [energyInner, energyInner, real_inner_comm (B ⬝ x) y,
    hB.isSymmetricCoercive.isSymmetric x y]

/-- For $B \in \mathbb{R}^{n \times n}$, the $B$-inner product is additive in its first argument:
$(x + y, z)_B = (x, z)_B + (y, z)_B$. -/
theorem energyInner_add_left (x y z : EuclideanSpace ℝ (Fin n)) :
    energyInner B (x + y) z = energyInner B x z + energyInner B y z := by
  simp [energyInner, inner_add_right]

/-- For $B \in \mathbb{R}^{n \times n}$, the $B$-inner product is homogeneous in its first argument:
$(cx, y)_B = c (x, y)_B$ for $c \in \mathbb{R}$. -/
theorem energyInner_smul_left (c : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B (c • x) y = c * energyInner B x y := by
  simp [energyInner, inner_smul_right]

/-- For a symmetric positive definite $B \in \mathbb{R}^{n \times n}$, the $B$-inner product is
positive definite: $(x, x)_B > 0$ for $x \neq 0$. -/
theorem energyInner_self_pos (hB : B.IsSPD) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < energyInner B x x := by
  have h := hB.isSymmetricCoercive.isCoercive.inner_self_pos hx
  rw [energyInner, real_inner_comm]
  simpa [RCLike.re_to_real] using h

/-- For a symmetric positive definite $B \in \mathbb{R}^{n \times n}$, $(x, x)_B = 0$ if and only if
$x = 0$. -/
theorem energyInner_self_eq_zero_iff (hB : B.IsSPD) {x : EuclideanSpace ℝ (Fin n)} :
    energyInner B x x = 0 ↔ x = 0 := by
  refine ⟨fun h => by_contra fun hx => ?_, fun h => by simp [h, energyInner]⟩
  exact absurd h (energyInner_self_pos hB hx).ne'

/-! ### Self-adjointness for the $B$-inner product (Problem P-1.18) -/

private theorem mulVec_dotProduct_transpose (M : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- Let $A, B \in \mathbb{R}^{n \times n}$ with $B$ symmetric. If $BA$ is symmetric, then $A$ is
self-adjoint for the $B$-inner product. -/
theorem isSelfAdjointWrt_of_isSymm_mul {A : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (h : (B * A).IsSymm) : B.IsSelfAdjointWrt A := by
  intro x y
  have key : ∀ u v : Fin n → ℝ, (B *ᵥ (A *ᵥ u)) ⬝ᵥ v = (B *ᵥ u) ⬝ᵥ (A *ᵥ v) := by
    intro u v
    rw [mulVec_mulVec, mulVec_dotProduct_transpose, h,
      mulVec_dotProduct_transpose B u (A *ᵥ v), hB, mulVec_mulVec]
  simp only [energyInner, SaadSparse.real_inner_toEuclideanLin', Matrix.ofLp_toEuclideanLin]
  exact key _ _

/-- **Problem P-1.18** of [saad2003iterative], first case. Let $B, C \in \mathbb{R}^{n \times n}$
with $B$ symmetric positive definite and nonsingular, and $C$ symmetric. Then $A = B^{-1} C$ is
self-adjoint for the $B$-inner product.

The nonsingularity of $B$ is a separate hypothesis in the statement, although it follows from
positive definiteness. -/
theorem isSelfAdjointWrt_inv_mul {C : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSPD) (hBu : IsUnit B)
    (hC : C.IsSymm) : B.IsSelfAdjointWrt (B⁻¹ * C) := by
  refine isSelfAdjointWrt_of_isSymm_mul hB.1 ?_
  rw [← mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).mp hBu), one_mul]
  exact hC

/-- **Problem P-1.18** of [saad2003iterative], second case. Let $B, C \in \mathbb{R}^{n \times n}$
be symmetric. Then $A = CB$ is self-adjoint for the $B$-inner product. -/
theorem isSelfAdjointWrt_mul {C : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hC : C.IsSymm) :
    B.IsSelfAdjointWrt (C * B) := by
  refine isSelfAdjointWrt_of_isSymm_mul hB ?_
  change (B * (C * B))ᵀ = B * (C * B)
  rw [transpose_mul, transpose_mul, hB, hC]
  exact mul_assoc B C B

end BInner

end Matrix

namespace SaadSparse.Chapter01

open Matrix

variable {n : ℕ}

/-! ### Theorem 1.34 -/

/-- **Theorem 1.34** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite in the sense of (1.48). Then $A$ is nonsingular, and there is $\alpha > 0$ with
$$(Au, u) \ge \alpha \|u\|_2^2 \quad \text{for every } u \in \mathbb{R}^n.$$
-/
theorem theorem_1_34 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsPositiveReal) :
    IsUnit A ∧ ∃ α > 0, ∀ u : Fin n → ℝ, α * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u := by
  obtain ⟨c, hc, hcA⟩ := (isPositiveReal_iff_isCoercive A).mp hA
  refine ⟨?_, c, hc, fun u => ?_⟩
  · refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hinj : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 v :=
      LinearMap.IsCoercive.injective ⟨c, hc, hcA⟩ (by ext i; exact congrFun huv i)
    ext i
    exact congrFun (congrArg WithLp.ofLp hinj) i
  · have h := hcA (WithLp.toLp 2 u)
    rw [SaadSparse.real_inner_apply_self] at h
    rw [← SaadSparse.real_norm_sq_eq_dotProduct (WithLp.toLp 2 u)]
    simpa [RCLike.re_to_real] using h

/-- **Theorem 1.34** of [saad2003iterative], with the constant of the book. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $H = (A + A^T)/2$ be its Hermitian part.
Then for every $u \in \mathbb{R}^n$,
$$(Au, u) \ge \lambda_{\min}(H) \|u\|_2^2.$$

The statement holds for every real matrix $A$. When $A$ is positive definite,
$\lambda_{\min}(H) > 0$, and this gives the constant $\alpha = \lambda_{\min}(H)$ of the book. -/
theorem theorem_1_34' [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    SaadSparse.lambdaMin (hermitianPart_isHermitian A) * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u := by
  have hb := SaadSparse.isSymmetricBoundedBy_toEuclideanLin (hermitianPart_isHermitian A)
  have h := hb.le_re_inner (WithLp.toLp 2 u)
  rw [SaadSparse.real_inner_apply_self] at h
  rw [mulVec_dotProduct_eq_hermitianPart, ← SaadSparse.real_norm_sq_eq_dotProduct]
  simpa [RCLike.re_to_real] using h

/-- **Theorem 1.34** of [saad2003iterative], in the language of the backbone. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $H$ be its Hermitian part. Then the
operator $u \mapsto Au$ satisfies $(Au, u) \ge \lambda_{\min}(H) \|u\|_2^2$ for all $u$
(`LinearMap.IsCoerciveWith`).

The statement holds for every real matrix $A$; the constant is positive when $A$ is positive
definite. -/
theorem isCoerciveWith_lambdaMin [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    (toEuclideanLin A).IsCoerciveWith (SaadSparse.lambdaMin (hermitianPart_isHermitian A)) := by
  intro x
  have h := theorem_1_34' A (WithLp.ofLp x)
  rw [SaadSparse.real_inner_apply_self]
  simpa [RCLike.re_to_real, SaadSparse.real_norm_sq_eq_dotProduct] using h

/-! ### Theorem 1.35 (Bendixson) -/

/-- **Theorem 1.35** of [saad2003iterative] (Bendixson's theorem), real part. Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$, let $H = (A + A^H)/2$ be its Hermitian part, and
let $\mu$ be an eigenvalue of $A$. Then
$$\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H).$$
-/
theorem theorem_1_35_re [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.re ∈ Set.Icc (SaadSparse.lambdaMin (hermitianPart_isHermitian A))
      (SaadSparse.lambdaMax (hermitianPart_isHermitian A)) :=
  re_hasEigenvalue_mem_Icc_of_symmetricPart
    (SaadSparse.isSymmetricBoundedBy_toEuclideanLin (hermitianPart_isHermitian A))
    (fun x => re_inner_hermitianPart A x) ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)

/-- If $\mu$ is an eigenvalue of $A \in \mathbb{C}^{n \times n}$, then $c\mu$ is an eigenvalue of
$cA$ for every $c \in \mathbb{C}$. -/
private theorem hasEigenvalue_smul {c : ℂ} {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (h : Module.End.HasEigenvalue (toEuclideanLin A) μ) :
    Module.End.HasEigenvalue (toEuclideanLin (c • A)) (c * μ) := by
  obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv0⟩
  rw [Module.End.mem_eigenspace_iff]
  have hAv : toEuclideanLin A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  rw [map_smul, LinearMap.smul_apply, hAv, smul_smul]

/-- **Theorem 1.35** of [saad2003iterative] (Bendixson's theorem), imaginary part. Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$, let $S = (A - A^H)/(2i)$, and let $\mu$ be an
eigenvalue of $A$. Then
$$\lambda_{\min}(S) \le \operatorname{Im} \mu \le \lambda_{\max}(S).$$
-/
theorem theorem_1_35_im [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.im ∈ Set.Icc (SaadSparse.lambdaMin (skewHermitianPart_isHermitian A))
      (SaadSparse.lambdaMax (skewHermitianPart_isHermitian A)) := by
  have hev : Module.End.HasEigenvalue (toEuclideanLin ((-Complex.I) • A)) (-Complex.I * μ) :=
    hasEigenvalue_smul ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)
  have hHA : ∀ x : EuclideanSpace ℂ (Fin n),
      RCLike.re (inner ℂ (skewHermitianPart A ⬝ x) x)
        = RCLike.re (inner ℂ (((-Complex.I) • A) ⬝ x) x) := by
    intro x
    rw [skewHermitianPart_eq_hermitianPart]
    exact re_inner_hermitianPart _ x
  have h := re_hasEigenvalue_mem_Icc_of_symmetricPart
    (SaadSparse.isSymmetricBoundedBy_toEuclideanLin (skewHermitianPart_isHermitian A)) hHA hev
  simpa using h

/-- **Theorem 1.35** of [saad2003iterative] (Bendixson's theorem). Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$, let $H = (A + A^H)/2$ and $S = (A - A^H)/(2i)$,
and let $\mu$ be an eigenvalue of $A$. Then $\mu$ lies in the rectangle
$$[\lambda_{\min}(H), \lambda_{\max}(H)] \times [\lambda_{\min}(S), \lambda_{\max}(S)]$$
of the complex plane: $\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H)$ and
$\lambda_{\min}(S) \le \operatorname{Im} \mu \le \lambda_{\max}(S)$. -/
theorem theorem_1_35 [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    SaadSparse.lambdaMin (hermitianPart_isHermitian A) ≤ μ.re ∧
      μ.re ≤ SaadSparse.lambdaMax (hermitianPart_isHermitian A) ∧
      SaadSparse.lambdaMin (skewHermitianPart_isHermitian A) ≤ μ.im ∧
      μ.im ≤ SaadSparse.lambdaMax (skewHermitianPart_isHermitian A) :=
  ⟨(theorem_1_35_re hμ).1, (theorem_1_35_re hμ).2, (theorem_1_35_im hμ).1, (theorem_1_35_im hμ).2⟩

end SaadSparse.Chapter01
