/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.SpecialFunctions.Log
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# Complexification of real matrices

For a real square matrix $A$, the **complexification** $A_{\mathbb{C}}$ is the complex matrix with
the same entries. This file studies its characteristic polynomial and its spectrum, and it defines
the spectral radius $\rho(A)$ of a real matrix as the spectral radius of $A_{\mathbb{C}}$. This is
the only useful notion for real matrices. The rotation $G = \begin{bmatrix} 0 & -1 \\ 1 & 0
\end{bmatrix}$ has no real eigenvalue, so its spectral radius over $\mathbb{R}$ is $0$, but its
powers do not tend to $0$. So the implication "$\rho_{\mathbb{R}}(G) < 1 \Rightarrow G^k \to 0$" is
false over $\mathbb{R}$. The results on the Gelfand formula in
`Numlib.Analysis.Normed.Algebra.SpectralRadius` are therefore used over $\mathbb{C}$ and transported
to real matrices through the complexification.

The main facts are: $A^k \to 0$ if and only if $\rho(A) < 1$; $\rho(A) \le f(A)$ for every
submultiplicative, absolutely homogeneous and positive definite function $f$ on matrices, in
particular for the usual matrix norms; Gelfand's formula $\|A^k\|^{1/k} \to \rho(A)$; the Neumann
series $\sum_k A^k = (I - A)^{-1}$ when $\rho(A) < 1$ (Theorem 1.5 of [quarteroni2000numerical]);
and the identification of $\rho(G)$ as the worst asymptotic rate of decay of the errors $G^k d_0$ of
a linear stationary iteration.

## Main definitions

* `Matrix.complexify`: the entrywise inclusion of $\mathbb{R}^{n \times n}$ in
  $\mathbb{C}^{n \times n}$.
* `Matrix.complexSpectralRadius`: the spectral radius $\rho(A)$ of $A_{\mathbb{C}}$.
* `Matrix.complexSpectralAbscissa`: the spectral abscissa $\max \{\operatorname{Re} \lambda :
  \lambda \in \sigma(A_{\mathbb{C}})\}$.

## Main results

* `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`: $A^k \to 0$ if and only if $\rho(A) < 1$.
* `Matrix.isUnit_one_sub_of_complexSpectralRadius_lt_one`: if $\rho(A) < 1$, then $I - A$ is
  nonsingular.
* `Matrix.complexSpectralRadius_le_of_norm`: $\rho(A) \le f(A)$ for every submultiplicative,
  absolutely homogeneous and positive definite $f$, with the corollaries for the three scoped matrix
  norms.
* `Matrix.tendsto_pow_of_algebraNorm_lt_one`: $A^k \to 0$ if some algebra norm of $A$ is less than
  $1$.
* `Matrix.l2_opNorm_complexify`, `Matrix.linfty_opNorm_complexify`,
  `Matrix.frobenius_norm_complexify`: complexification changes none of the three matrix norms. This
  transports every statement about $\|A^k\|$ to $\mathbb{C}$.
* `Matrix.tendsto_pow_rpow_complexSpectralRadius`, `Matrix.tendsto_pow_rpow_linfty_opNorm`:
  **Gelfand's formula** for a real matrix, in the spectral norm and in the maximum absolute row sum
  norm.
* `Matrix.limsup_norm_pow_mulVec_rpow_le`, `Matrix.exists_limsup_norm_pow_mulVec_rpow_eq`: the
  spectral radius bounds every specific convergence factor
  $\limsup_k (\|G^k d_0\| / \|d_0\|)^{1/k}$, and some $d_0 \neq 0$ attains the bound.
* `Matrix.star_mem_spectrum_complexify_iff`: the spectrum of a real matrix is closed under complex
  conjugation.
* `Matrix.spectrum_complexify_affine`, `Matrix.complexSpectralRadius_pow`: spectral mapping for
  affine images and for powers.
* `Matrix.complexSpectralRadius_affine_le`: the relaxation estimate $\rho((1 - \omega) I + \omega X)
  \le (1 - \omega) + \omega \rho(X)$ for $0 < \omega \le 1$.
* `Matrix.complexSpectralRadius_diagonal`: $\rho(\operatorname{diag}(d)) = \max_i |d_i|$.
* `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`,
  `Matrix.summable_pow_iff_complexSpectralRadius_lt_one`: the real Neumann series, Theorem 1.5 of
  [quarteroni2000numerical].
* `Matrix.posDef_complexify_iff`: $A_{\mathbb{C}}$ is positive definite if and only if $A$ is.
* `Matrix.tendsto_averageConvergenceRate`: $-\tfrac{1}{m} \log \|G^m\| \to -\log \rho(G)$, (4.5) of
  [quarteroni2000numerical].

## Notation

* $A_{\mathbb{C}}$: the complexification `Matrix.complexify A` of a real matrix $A$.
* $\sigma(A_{\mathbb{C}})$: the spectrum `spectrum ℂ (Matrix.complexify A)`, the set of complex
  eigenvalues of $A$.
* $\rho(A)$: the spectral radius `Matrix.complexSpectralRadius A` of a real matrix $A$.

## Implementation notes

* Complexification is a ring homomorphism. The algebraic lemmas at the start of the file state this
  operation by operation (`Matrix.complexify_add`, `Matrix.complexify_mul`, `Matrix.complexify_inv`,
  and others). Complexification also commutes with the exponential (`Matrix.complexify_exp`), and
  with the diagonal, strictly lower and strictly upper parts of
  `Numlib.LinearAlgebra.Matrix.Triangular` (`Matrix.complexify_diagPart` and the related lemmas). So
  the classical splittings of a real matrix can be formed before or after the passage to
  $\mathbb{C}$.
* The spectral radius $\rho(A)$ is an extended nonnegative real number (`ENNReal`). For an empty
  index type, the spectrum is empty and $\rho(A) = 0$.
* The bound $\rho(A) \le f(A)$ takes the norm as an explicit function $f$, or as an `AlgebraNorm`,
  and not as a class argument such as `[NormedRing (Matrix n n ℝ)]`. The sectioning comment before
  `Matrix.exists_nnnorm_apply_le` explains why the statement with a class argument is false. The
  three scoped norms of `Mathlib.Analysis.Matrix.Normed` and `Mathlib.Analysis.CStarAlgebra.Matrix`
  are corollaries at the end of the file.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace Matrix

variable {n : Type*}

/-- The **complexification** of a real square matrix $A$: the complex matrix $A_{\mathbb{C}}$ with
the entries $a_{ij}$, viewed as complex numbers. In Lean, it is `A.map Complex.ofReal`. -/
def complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

/-- The entry $(i, j)$ of $A_{\mathbb{C}}$ is the real number $a_{ij}$, viewed as a complex number.
-/
@[simp] theorem complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = A i j := rfl

/-- The complexification of the zero matrix is the zero matrix. -/
@[simp] theorem complexify_zero : complexify (0 : Matrix n n ℝ) = 0 := by
  ext i j; simp

/-- Complexification is additive: $(A + B)_{\mathbb{C}} = A_{\mathbb{C}} + B_{\mathbb{C}}$. -/
theorem complexify_add (A B : Matrix n n ℝ) : complexify (A + B) = complexify A + complexify B := by
  ext i j; simp

/-- Complexification commutes with negation: $(-A)_{\mathbb{C}} = -A_{\mathbb{C}}$. -/
theorem complexify_neg (A : Matrix n n ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp

/-- Complexification commutes with subtraction: for real square matrices $A$ and $B$, $(A -
B)_{\mathbb{C}} = A_{\mathbb{C}} - B_{\mathbb{C}}$. -/
theorem complexify_sub (A B : Matrix n n ℝ) : complexify (A - B) = complexify A - complexify B := by
  ext i j; simp

/-- Complexification commutes with multiplication by a real scalar $c$, viewed as a complex number:
$(cA)_{\mathbb{C}} = c A_{\mathbb{C}}$. -/
theorem complexify_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexify (c • A) = (c : ℂ) • complexify A := by
  ext i j; simp

/-- Complexification is injective, because it is the entrywise inclusion of $\mathbb{R}$ in
$\mathbb{C}$. -/
theorem complexify_injective : Function.Injective (complexify (n := n)) := by
  intro A B hAB
  ext i j
  have h : ((A i j : ℝ) : ℂ) = ((B i j : ℝ) : ℂ) := congrFun (congrFun hAB i) j
  exact_mod_cast h

/-- Complexification commutes with transposition: $(A^T)_{\mathbb{C}} = (A_{\mathbb{C}})^T$. -/
theorem complexify_transpose (A : Matrix n n ℝ) : complexify Aᵀ = (complexify A)ᵀ := by
  ext i j; simp

/-- Complexification commutes with conjugate transposition:
$(A^H)_{\mathbb{C}} = (A_{\mathbb{C}})^H$. The entries of $A_{\mathbb{C}}$ are real, so the
conjugation changes nothing. -/
theorem complexify_conjTranspose (A : Matrix n n ℝ) : complexify Aᴴ = (complexify A)ᴴ := by
  ext i j; simp

/-- Let $A$ be a real square matrix. Then $A_{\mathbb{C}}$ is Hermitian if and only if $A$ is
Hermitian, that is, symmetric. -/
@[simp] theorem isHermitian_complexify_iff (A : Matrix n n ℝ) :
    IsHermitian (complexify A) ↔ IsHermitian A := by
  refine ⟨fun h => complexify_injective ?_, fun h => ?_⟩
  · rw [complexify_conjTranspose]
    exact h.eq
  · exact (complexify_conjTranspose A).symm.trans (congrArg complexify h.eq)

/-- Complexification is multiplicative: $(AB)_{\mathbb{C}} = A_{\mathbb{C}} B_{\mathbb{C}}$. -/
theorem complexify_mul [Fintype n] (A B : Matrix n n ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp only [complexify_apply, Matrix.mul_apply]
  push_cast
  rfl

/-- Complexification as an $\mathbb{R}$-linear map, used to compare the topologies of the real and
the complex matrices. -/
private def complexifyₗ : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ where
  toFun := complexify
  map_add' := complexify_add
  map_smul' c A := by ext i j; simp [Complex.real_smul]

/-- Let $A$ be a real square matrix, with the indices in a linear order. Then complexification
commutes with the strictly lower part: the strictly lower part of $A_{\mathbb{C}}$ (the entries
$a_{ij}$ with $j < i$, and $0$ elsewhere, `Matrix.strictLower`) is the complexification of the
strictly lower part of $A$. -/
@[simp]
theorem complexify_strictLower [LinearOrder n] (A : Matrix n n ℝ) :
    complexify (strictLower A) = strictLower (complexify A) := by
  ext i j; by_cases h : j < i <;> simp [complexify, strictLower_apply, h]

/-- Let $A$ be a real square matrix, with the indices in a linear order. Then complexification
commutes with the strictly upper part: the strictly upper part of $A_{\mathbb{C}}$ (the entries
$a_{ij}$ with $i < j$, and $0$ elsewhere, `Matrix.strictUpper`) is the complexification of the
strictly upper part of $A$. -/
@[simp]
theorem complexify_strictUpper [LinearOrder n] (A : Matrix n n ℝ) :
    complexify (strictUpper A) = strictUpper (complexify A) := by
  ext i j; by_cases h : i < j <;> simp [complexify, strictUpper_apply, h]

/-- Let $A$ be a real tridiagonal matrix, with the indices in a linear order. Then $A_{\mathbb{C}}$
is tridiagonal, because complexification keeps the zero entries. -/
theorem IsTridiagonal.complexify [LinearOrder n] {A : Matrix n n ℝ} (hA : A.IsTridiagonal) :
    (Matrix.complexify A).IsTridiagonal := fun i j h => by
  simp [Matrix.complexify, hA i j h]

variable [DecidableEq n]

/-- The complexification of the identity matrix is the identity matrix. -/
@[simp] theorem complexify_one : complexify (1 : Matrix n n ℝ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

/-- Let $A$ be a real square matrix. Then complexification commutes with the diagonal part: the
diagonal part $\operatorname{diag}(a_{11}, \dots, a_{nn})$ of $A_{\mathbb{C}}$
(`Matrix.diagPart`) is the complexification of the diagonal part of $A$.

So the splitting $A = D - E - F$ of the classical stationary iterations can be formed before or
after the passage to $\mathbb{C}$. With `Matrix.complexify_strictLower` and
`Matrix.complexify_strictUpper`, this lets a real iteration matrix be analysed through the
spectral radius of its complexification. -/
@[simp]
theorem complexify_diagPart (A : Matrix n n ℝ) :
    complexify (diagPart A) = diagPart (complexify A) := by
  ext i j; by_cases h : i = j <;> simp [complexify, diagPart_apply, h]

variable [Fintype n]

/-- Complexification commutes with powers: for a real square matrix $A$ and $k \ge 0$,
$(A^k)_{\mathbb{C}} = (A_{\mathbb{C}})^k$. -/
theorem complexify_pow (A : Matrix n n ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, complexify_mul, ih]

/-- Complexification commutes with the determinant: for a real square matrix $A$,
$\det A_{\mathbb{C}}$ is the real number $\det A$, viewed as a complex number. -/
@[simp] theorem det_complexify (A : Matrix n n ℝ) : (complexify A).det = ((A.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

/-- Let $A$ be a real square matrix. Then $A_{\mathbb{C}}$ is nonsingular if and only if $A$ is
nonsingular.

So nonsingularity can be decided after the passage to $\mathbb{C}$.
`Matrix.isUnit_one_sub_of_complexSpectralRadius_lt_one` does this, because only the complex
Neumann series is available there. -/
theorem isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, det_complexify]
  simp [isUnit_iff_ne_zero]

/-- Complexification commutes with inversion: for a real square matrix $A$,
$(A^{-1})_{\mathbb{C}} = (A_{\mathbb{C}})^{-1}$.

When $A$ is singular, both sides are $0$, the value of the matrix inverse at a singular matrix
(`Matrix.isUnit_complexify_iff`). -/
theorem complexify_inv (A : Matrix n n ℝ) : complexify A⁻¹ = (complexify A)⁻¹ := by
  by_cases hA : IsUnit A
  · have h1 : complexify A⁻¹ * complexify A = 1 := by
      rw [← complexify_mul, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), complexify_one]
    exact (inv_eq_left_inv h1).symm
  · have h0 : A⁻¹ = 0 :=
      nonsing_inv_apply_not_isUnit A fun h => hA ((isUnit_iff_isUnit_det A).mpr h)
    have h0' : (complexify A)⁻¹ = 0 :=
      nonsing_inv_apply_not_isUnit _ fun h => hA ((isUnit_complexify_iff A).mp
        ((isUnit_iff_isUnit_det _).mpr h))
    rw [h0, h0', complexify_zero]

/-- **Complexification commutes with the exponential**: for a real square matrix $X$,
$(e^X)_{\mathbb{C}} = e^{X_{\mathbb{C}}}$. The exponential series is mapped term by term. -/
theorem complexify_exp (X : Matrix n n ℝ) :
    complexify (NormedSpace.exp X) = NormedSpace.exp (complexify X) := by
  have hL : Function.LeftInverse (fun M : Matrix n n ℂ => M.map Complex.re)
      (Complex.ofRealHom.mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ) := fun M => by
    ext i j
    simp
  have h := Function.LeftInverse.map_tsum (L := SummationFilter.unconditional ℕ)
    (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • X ^ k)
    (g := (Complex.ofRealHom.mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ))
    (continuous_id.matrix_map Complex.continuous_ofReal)
    (continuous_id.matrix_map Complex.continuous_re) hL
  rw [NormedSpace.exp_eq_tsum_rat, NormedSpace.exp_eq_tsum_rat]
  change Complex.ofRealHom.mapMatrix _ = _
  rw [h]
  congr 1
  funext k
  rw [map_rat_smul, map_pow]
  rfl

/-- Complexification commutes with the iteration operator $I - M^{-1} A$ of a splitting: for real
square matrices $M$ and $A$,
$$(I - M^{-1} A)_{\mathbb{C}} = I - M_{\mathbb{C}}^{-1} A_{\mathbb{C}}.$$

The inverse is `Ring.inverse`, which is $0$ at a singular matrix, as in
`Stationary.Splitting.iterationOperator` of `Numlib.Stationary.Splitting`. -/
theorem complexify_one_sub_inverse_mul (m A : Matrix n n ℝ) :
    complexify (1 - Ring.inverse m * A) = 1 - Ring.inverse (complexify m) * complexify A := by
  rw [complexify_sub, complexify_one, complexify_mul, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, complexify_inv]

/-- Let $A$ be a real square matrix whose diagonal part $D$ is nonsingular. Then the diagonal part
of $A_{\mathbb{C}}$ is nonsingular.

This transfers the hypothesis of a real Jacobi, Gauss–Seidel or SOR splitting to its
complexification. -/
theorem isUnit_diagPart_complexify {A : Matrix n n ℝ} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart (complexify A)) := by
  rw [← complexify_diagPart, isUnit_complexify_iff]
  exact h

/-- Let $A$ be a real square matrix. Then the characteristic polynomial of $A_{\mathbb{C}}$ is the
characteristic polynomial of $A$, with its coefficients viewed as complex numbers.

This is Mathlib's `Matrix.charpoly_map`. -/
theorem charpoly_complexify (A : Matrix n n ℝ) :
    (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
  have h : complexify A = A.map (algebraMap ℝ ℂ) := rfl
  rw [h, Matrix.charpoly_map]

/-- Let $K$ be a field, let $A \in K^{n \times n}$ and let $\mu \in K$. Then $\mu$ is in the
spectrum of $A$ if and only if $\mu$ is an eigenvalue of $A$ with an eigenvector: $Ax = \mu x$
for some $x \neq 0$. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul {K : Type*} [Field K] (A : Matrix n n K) (μ : K) :
    μ ∈ spectrum K A ↔ ∃ x, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  exact exists_congr fun x => and_congr_right' eq_comm

/-- Let $A$ be a real square matrix and let $\mu \in \mathbb{C}$. Then
$\mu \in \sigma(A_{\mathbb{C}})$ if and only if $\mu$ is a root of the characteristic polynomial
of $A$, with its coefficients viewed as complex numbers.

No eigenvalue is lost, as it would be over $\mathbb{R}$. This is the spectrum that controls the
decay of $A^k$: the real characteristic polynomial of a rotation has no root, but the powers of
the rotation keep the norm $1$. -/
theorem mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_complexify]

/-- Let $A$ be a real square matrix and let $\mu \in \mathbb{R}$. Then
$\mu \in \sigma(A_{\mathbb{C}})$ if and only if $\mu$ is in the real spectrum of $A$. So the
real eigenvalues of $A$ are the real points of the complex spectrum. -/
theorem ofReal_mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℝ) :
    (μ : ℂ) ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℝ A := by
  rw [mem_spectrum_complexify_iff, Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
    Polynomial.IsRoot.def, Polynomial.eval_map, ← Complex.coe_algebraMap,
    Polynomial.eval₂_at_apply]
  simp

/-- **The complex eigenvalues of a real matrix come in conjugate pairs**. Let $A$ be a real square
matrix and let $\mu \in \mathbb{C}$. Then
$$\bar{\mu} \in \sigma(A_{\mathbb{C}}) \iff \mu \in \sigma(A_{\mathbb{C}}).$$
This is in §1.7 of [quarteroni2000numerical].

The characteristic polynomial has real coefficients (`Matrix.charpoly_complexify`, with
`Polynomial.aeval_conj`). -/
theorem star_mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℂ) :
    star μ ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℂ (complexify A) := by
  have key : ∀ ν : ℂ, ν ∈ spectrum ℂ (complexify A) → star ν ∈ spectrum ℂ (complexify A) := by
    intro ν hν
    rw [mem_spectrum_complexify_iff, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def] at hν ⊢
    rw [show star ν = starRingEnd ℂ ν from rfl, Polynomial.aeval_conj, hν, map_zero]
  exact ⟨fun h => by simpa using key _ h, key μ⟩

/-- Let $A$ be a real square matrix and let $\mu \in \mathbb{C}$. Then the eigenvalues $\bar{\mu}$
and $\mu$ of $A_{\mathbb{C}}$ have the same algebraic multiplicity: their multiplicities as
roots of the characteristic polynomial of $A_{\mathbb{C}}$ are equal.

The characteristic polynomial does not change under the conjugation of its coefficients, and an
injective ring homomorphism keeps the multiplicities of roots
(`Polynomial.eq_rootMultiplicity_map`). -/
theorem rootMultiplicity_charpoly_complexify_star (A : Matrix n n ℝ) (μ : ℂ) :
    (complexify A).charpoly.rootMultiplicity (star μ)
      = (complexify A).charpoly.rootMultiplicity μ := by
  rw [charpoly_complexify]
  have hmap : (A.charpoly.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ)
      = A.charpoly.map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp
  have h := Polynomial.eq_rootMultiplicity_map (p := A.charpoly.map (algebraMap ℝ ℂ))
    (starRingEnd ℂ).injective μ
  rw [hmap] at h
  exact h.symm

/-- Let $Y$ be a complex square matrix, and let $c, d \in \mathbb{C}$ with $d \neq 0$. Then $\mu$ is
in the spectrum of $cI + dY$ if and only if $(\mu - c)/d$ is in the spectrum of $Y$. -/
theorem mem_spectrum_affine_iff {Y : Matrix n n ℂ} {c d : ℂ} (hd : d ≠ 0) (μ : ℂ) :
    μ ∈ spectrum ℂ (c • 1 + d • Y) ↔ (μ - c) / d ∈ spectrum ℂ Y := by
  have key : algebraMap ℂ (Matrix n n ℂ) μ - (c • 1 + d • Y)
      = d • (algebraMap ℂ (Matrix n n ℂ) ((μ - c) / d) - Y) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul,
      mul_div_cancel₀ _ hd]
    module
  have hu := isUnit_smul_iff (Units.mk0 d hd) (algebraMap ℂ (Matrix n n ℂ) ((μ - c) / d) - Y)
  rw [Units.smul_def, Units.val_mk0] at hu
  rw [spectrum.mem_iff, spectrum.mem_iff, key, hu]

/-- **The spectral radius of a complex matrix is attained**. Let $M$ be a complex square matrix with
a nonempty spectrum. Then there is an eigenvalue $\mu_0$ of $M$ with
$$\rho(M) = |\mu_0| \quad \text{and} \quad |\mu| \le |\mu_0| \text{ for every eigenvalue } \mu
  \text{ of } M.$$

The spectrum is finite, so some eigenvalue has the largest modulus. The spectral radius is
Mathlib's `spectralRadius ℂ M`. -/
theorem exists_norm_eq_spectralRadius (M : Matrix n n ℂ) (hne : (spectrum ℂ M).Nonempty) :
    ∃ μ₀ ∈ spectrum ℂ M, spectralRadius ℂ M = ENNReal.ofReal ‖μ₀‖ ∧
      ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ‖μ₀‖ := by
  classical
  have hfin := M.finite_spectrum
  obtain ⟨μ₁, hμ₁⟩ := hne
  have hne' : hfin.toFinset.Nonempty := ⟨μ₁, hfin.mem_toFinset.mpr hμ₁⟩
  obtain ⟨μ₀, hmem₀, hsup⟩ := Finset.exists_mem_eq_sup' hne' fun μ => ‖μ‖
  have hmem₀' : μ₀ ∈ spectrum ℂ M := hfin.mem_toFinset.mp hmem₀
  have hmax : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ‖μ₀‖ := fun μ hμ => by
    rw [← hsup]
    exact Finset.le_sup' (fun μ => ‖μ‖) (hfin.mem_toFinset.mpr hμ)
  rw [spectralRadius_eq_of_unital]
  refine ⟨μ₀, hmem₀', le_antisymm (iSup₂_le fun μ hμ => ?_)
    (le_iSup₂_of_le μ₀ hmem₀' ?_), hmax⟩
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (hmax μ hμ)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- Let $M$ be a complex square matrix whose eigenvalues all have modulus less than $1$. Then
$\rho(M) < 1$.

This is the form of Mathlib's `spectrum.spectralRadius_lt_of_forall_lt` for a finite spectrum.
It needs no norm on the matrices and no nontriviality. -/
theorem spectralRadius_lt_one_of_forall_norm_lt {M : Matrix n n ℂ}
    (h : ∀ μ ∈ spectrum ℂ M, ‖μ‖ < 1) : spectralRadius ℂ M < 1 := by
  rcases (spectrum ℂ M).eq_empty_or_nonempty with he | hne
  · rw [spectralRadius_eq_of_unital]
    refine lt_of_le_of_lt (iSup₂_le fun k hk => ?_) zero_lt_one
    exact absurd (he ▸ hk) (Set.notMem_empty k)
  · obtain ⟨μ₀, hμ₀, hρ, -⟩ := exists_norm_eq_spectralRadius M hne
    rw [hρ, ENNReal.ofReal_lt_one]
    exact h μ₀ hμ₀

/-- **Spectral mapping for affine images of a real matrix**. Let $X$ be a real square matrix, and
let $c, d \in \mathbb{R}$ with $d \neq 0$. Then
$$\sigma\bigl((cI + dX)_{\mathbb{C}}\bigr) = \{c + d\mu : \mu \in \sigma(X_{\mathbb{C}})\}.$$

Every relaxation argument uses this: the JOR matrix $(1 - \omega) I + \omega B_J$, and the
Richardson matrix $I - \alpha M$. -/
theorem spectrum_complexify_affine (X : Matrix n n ℝ) {c d : ℝ} (hd : d ≠ 0) :
    spectrum ℂ (complexify (c • 1 + d • X))
      = (fun μ : ℂ => c + d * μ) '' spectrum ℂ (complexify X) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  ext μ
  rw [complexify_add, complexify_smul, complexify_smul, complexify_one,
    mem_spectrum_affine_iff hd', Set.mem_image]
  refine ⟨fun h => ⟨_, h, by rw [mul_div_cancel₀ _ hd']; ring⟩, ?_⟩
  rintro ⟨ν, hν, rfl⟩
  have hcancel : ((c : ℂ) + (d : ℂ) * ν - (c : ℂ)) / (d : ℂ) = ν := by
    field_simp
    ring
  rwa [hcancel]

/-- The **spectral radius** $\rho(A)$ of a real square matrix $A$, computed over $\mathbb{C}$: the
spectral radius of $A_{\mathbb{C}}$,
$$\rho(A) = \sup \{|\mu| : \mu \in \sigma(A_{\mathbb{C}})\}.$$

The value is an extended nonnegative real number. It is $0$ when the index type is empty. -/
noncomputable def complexSpectralRadius (A : Matrix n n ℝ) : ENNReal :=
  spectralRadius ℂ (complexify A)

/-- The **spectral abscissa** of a real square matrix $A$, computed over $\mathbb{C}$:
$$\alpha(A) = \sup \{\operatorname{Re} \lambda : \lambda \in \sigma(A_{\mathbb{C}})\}.$$
It is the analogue of `spectralAbscissa` for real matrices, as `Matrix.complexSpectralRadius` is
the analogue of `spectralRadius`.

When the index type is empty, the spectrum is empty and the value is $\sup \emptyset = 0$. -/
noncomputable def complexSpectralAbscissa (A : Matrix n n ℝ) : ℝ :=
  spectralAbscissa (complexify A)

omit [DecidableEq n] in
/-- The spectral radius of the zero matrix is $0$. -/
@[simp] theorem complexSpectralRadius_zero : complexSpectralRadius (0 : Matrix n n ℝ) = 0 := by
  rw [complexSpectralRadius, complexify_zero, spectrum.spectralRadius_zero]

/-- The spectral radius of a real square matrix $A$ is the supremum of the moduli of the complex
eigenvalues: $\rho(A) = \sup_{\mu \in \sigma(A_{\mathbb{C}})} |\mu|$. -/
theorem complexSpectralRadius_eq_iSup (A : Matrix n n ℝ) :
    complexSpectralRadius A = ⨆ μ ∈ spectrum ℂ (complexify A), (‖μ‖₊ : ℝ≥0∞) :=
  spectralRadius_eq_of_unital _

/-- Let $A$ be a real square matrix. Every complex eigenvalue $\mu$ of $A$ satisfies
$|\mu| \le \rho(A)$. -/
theorem nnnorm_le_complexSpectralRadius {A : Matrix n n ℝ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify A)) : (‖μ‖₊ : ℝ≥0∞) ≤ complexSpectralRadius A := by
  rw [complexSpectralRadius_eq_iSup]
  exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ℝ≥0∞)) μ hμ

/-- For $n \ge 1$, the spectral radius of the identity matrix is $\rho(I) = 1$.

This is `spectrum.spectralRadius_one` for the complexification. -/
theorem complexSpectralRadius_one [Nonempty n] : complexSpectralRadius (1 : Matrix n n ℝ) = 1 := by
  rw [complexSpectralRadius, complexify_one, spectrum.spectralRadius_one]

/-- Let $B$ be a real square matrix and let $r \in \mathbb{R}$. If the only complex eigenvalue of
$B$ is $r$, that is, $\mu \in \sigma(B_{\mathbb{C}})$ if and only if $\mu = r$, then
$\rho(B) = |r|$. -/
theorem complexSpectralRadius_eq_of_forall_mem_spectrum_iff {B : Matrix n n ℝ} {r : ℝ}
    (h : ∀ μ : ℂ, μ ∈ spectrum ℂ (complexify B) ↔ μ = r) :
    complexSpectralRadius B = ENNReal.ofReal |r| := by
  have hr : ENNReal.ofReal |r| = ((‖(r : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  rw [complexSpectralRadius_eq_iSup, hr]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · rw [h] at hμ
    subst hμ
    exact le_rfl
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ spectrum ℂ (complexify B)) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞))
      (r : ℂ) ((h _).mpr rfl)

/-- Conjugation by a nonsingular matrix does not change the spectral radius. Let $C$ be a
nonsingular real square matrix and let $B$ be a real square matrix. Then
$$\rho(C^{-1} B C) = \rho(B).$$

The spectrum of $C^{-1} B C$ is the spectrum of $B$. -/
theorem complexSpectralRadius_conj {C : Matrix n n ℝ} (hC : IsUnit C) (B : Matrix n n ℝ) :
    complexSpectralRadius (C⁻¹ * B * C) = complexSpectralRadius B := by
  have hC' : IsUnit (complexify C) := (isUnit_complexify_iff C).2 hC
  simp only [complexSpectralRadius_eq_iSup, complexify_mul, complexify_inv]
  rw [← hC'.unit_spec, ← coe_units_inv, spectrum.units_conjugate']

/-- **The spectral radius of a diagonal matrix** is the largest modulus of a diagonal entry: for
$d \in \mathbb{R}^n$,
$$\rho(\operatorname{diag}(d)) = \sup_i |d_i|.$$

The spectrum of $\operatorname{diag}(d)$ over $\mathbb{C}$ is the set of the entries $d_i$
(Mathlib's `Matrix.spectrum_diagonal`). With `Matrix.complexSpectralRadius_conj`, this gives
$\rho(C^{-1} D C)$ for a diagonalizable matrix. -/
theorem complexSpectralRadius_diagonal (d : n → ℝ) :
    complexSpectralRadius (diagonal d) = ⨆ i, (‖d i‖₊ : ℝ≥0∞) := by
  have hc : complexify (diagonal d) = diagonal fun i => (d i : ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [complexify, h]
  rw [complexSpectralRadius_eq_iSup, hc, spectrum_diagonal, iSup_range]
  simp only [Complex.nnnorm_real]

omit [DecidableEq n] in
/-- A real square matrix $A$ and its transpose have the same spectral radius: $\rho(A^T) = \rho(A)$.

Their characteristic polynomials are equal (Mathlib's `Matrix.spectrum_transpose`). This turns a
Perron eigenvector of $A^T$ into a left Perron eigenvector of $A$ at the same eigenvalue. -/
@[simp] theorem complexSpectralRadius_transpose (A : Matrix n n ℝ) :
    complexSpectralRadius Aᵀ = complexSpectralRadius A := by
  classical
  rw [complexSpectralRadius_eq_iSup, complexSpectralRadius_eq_iSup, complexify_transpose,
    spectrum_transpose]

omit [DecidableEq n] in
/-- The spectral radius is absolutely homogeneous: for $c \in \mathbb{R}$ and a real square matrix
$A$, $\rho(cA) = |c| \, \rho(A)$. -/
theorem complexSpectralRadius_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexSpectralRadius (c • A) = ‖c‖₊ * complexSpectralRadius A := by
  classical
  rw [complexSpectralRadius, complexify_smul, spectralRadius_smul, complexSpectralRadius]
  simp

/-- Let $A$ be a real square matrix and let $k \ge 1$. Then $\rho(A)^k \le \rho(A^k)$.

This is Mathlib's `spectrum.spectralRadius_pow_le`. Equality holds by the spectral mapping
theorem (`Matrix.complexSpectralRadius_pow`), but the arguments for the Gelfand formula need
only the inequality. -/
theorem complexSpectralRadius_pow_le (A : Matrix n n ℝ) {k : ℕ} (hk : k ≠ 0) :
    complexSpectralRadius A ^ k ≤ complexSpectralRadius (A ^ k) := by
  rw [complexSpectralRadius, complexSpectralRadius, complexify_pow]
  exact spectrum.spectralRadius_pow_le _ k hk

/-- Let $A$ be a real square matrix and let $k \ge 1$. Then
$$\rho(A^k) = \rho(A)^k.$$
This is in §1.7 and Exercise 8 of [quarteroni2000numerical].

The proof is the spectral mapping theorem (`spectralRadius_pow_of_nonempty`). The exponent
$k = 0$ is excluded: for an empty index type, the spectrum is empty and $\rho(I) = 0$. -/
theorem complexSpectralRadius_pow (A : Matrix n n ℝ) {k : ℕ} (hk : k ≠ 0) :
    complexSpectralRadius (A ^ k) = complexSpectralRadius A ^ k := by
  rw [complexSpectralRadius, complexSpectralRadius, complexify_pow]
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    simp [hk]
  · exact spectralRadius_pow_of_nonempty
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _) k

/-- **The relaxation estimate**. Let $X$ be a real square matrix and let $0 < \omega \le 1$. Then
$$\rho\bigl((1 - \omega) I + \omega X\bigr) \le (1 - \omega) + \omega \, \rho(X).$$
This is the estimate behind Theorem 4.6 of [quarteroni2000numerical].

Each eigenvalue $(1 - \omega) + \omega\mu$ of the relaxed matrix
(`Matrix.spectrum_complexify_affine`) has modulus at most $(1 - \omega) + \omega |\mu|$. -/
theorem complexSpectralRadius_affine_le (X : Matrix n n ℝ) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    complexSpectralRadius ((1 - ω) • 1 + ω • X)
      ≤ ENNReal.ofReal (1 - ω) + ENNReal.ofReal ω * complexSpectralRadius X := by
  have h1ω : 0 ≤ 1 - ω := by linarith
  have e1 : ENNReal.ofReal (1 - ω) = ‖((1 - ω : ℝ) : ℂ)‖₊ := by
    rw [Complex.nnnorm_real, Real.nnnorm_of_nonneg h1ω, ENNReal.ofReal_eq_coe_nnreal h1ω]
  have e2 : ENNReal.ofReal ω = ‖(ω : ℂ)‖₊ := by
    rw [Complex.nnnorm_real, Real.nnnorm_of_nonneg hω0.le, ENNReal.ofReal_eq_coe_nnreal hω0.le]
  rw [complexSpectralRadius_eq_iSup, spectrum_complexify_affine X hω0.ne', e1, e2]
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨ν, hν, rfl⟩ := hμ
  calc (‖((1 - ω : ℝ) : ℂ) + (ω : ℂ) * ν‖₊ : ℝ≥0∞)
      ≤ ‖((1 - ω : ℝ) : ℂ)‖₊ + ‖(ω : ℂ) * ν‖₊ := by
        rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 (nnnorm_add_le _ _)
    _ = ‖((1 - ω : ℝ) : ℂ)‖₊ + ‖(ω : ℂ)‖₊ * ‖ν‖₊ := by rw [nnnorm_mul, ENNReal.coe_mul]
    _ ≤ ‖((1 - ω : ℝ) : ℂ)‖₊ + ‖(ω : ℂ)‖₊ * complexSpectralRadius X := by
        gcongr
        exact nnnorm_le_complexSpectralRadius hν

/-- Let $X$ be a real square matrix with $\rho(X) < 1$, and let $0 < \omega \le 1$. Then
$\rho\bigl((1 - \omega) I + \omega X\bigr) < 1$.

This is the consequence of `Matrix.complexSpectralRadius_affine_le` that Theorem 4.6 of
[quarteroni2000numerical] uses. -/
theorem complexSpectralRadius_affine_lt_one (X : Matrix n n ℝ) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (hX : complexSpectralRadius X < 1) :
    complexSpectralRadius ((1 - ω) • 1 + ω • X) < 1 := by
  refine (complexSpectralRadius_affine_le X hω0 hω1).trans_lt ?_
  have hω' : ENNReal.ofReal ω ≠ 0 := by simpa using hω0
  calc ENNReal.ofReal (1 - ω) + ENNReal.ofReal ω * complexSpectralRadius X
      < ENNReal.ofReal (1 - ω) + ENNReal.ofReal ω * 1 :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
          (ENNReal.mul_lt_mul_right hω' ENNReal.ofReal_ne_top hX)
    _ = 1 := by
        rw [mul_one, ← ENNReal.ofReal_add (by linarith) hω0.le, sub_add_cancel, ENNReal.ofReal_one]

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix. Then the spectral radius of $A$ over $\mathbb{R}$ is at most
$\rho(A)$.

It can be strictly smaller: a plane rotation has no real eigenvalue. -/
theorem spectralRadius_le_complexSpectralRadius (A : Matrix n n ℝ) :
    spectralRadius ℝ A ≤ complexSpectralRadius A := by
  classical
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun μ hμ => ?_
  have hμ' : (μ : ℂ) ∈ spectrum ℂ (complexify A) :=
    (ofReal_mem_spectrum_complexify_iff A μ).mpr hμ
  calc (‖μ‖₊ : ENNReal) = (‖(μ : ℂ)‖₊ : ENNReal) := by simp
    _ ≤ complexSpectralRadius A := nnnorm_le_complexSpectralRadius hμ'

/-- The map `Matrix.toEuclideanCLM` as a $\mathbb{C}$-linear map, used to compare the product
topology on complex matrices with the operator norm topology. -/
private noncomputable def toEuclideanCLMₗ :
    Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) where
  toFun M := toEuclideanCLM (n := n) (𝕜 := ℂ) M
  map_add' := map_add _
  map_smul' c M := map_smul _ c M

/-- For a complex square matrix $M$, $M^k \to 0$ in the product topology if and only if the powers
of the corresponding operator tend to $0$ in the operator norm. -/
private theorem tendsto_pow_iff_tendsto_pow_toEuclideanCLM (M : Matrix n n ℂ) :
    Tendsto (fun k => M ^ k) atTop (𝓝 0) ↔
      Tendsto (fun k => toEuclideanCLM (n := n) (𝕜 := ℂ) M ^ k) atTop (𝓝 0) := by
  have hinj : Function.Injective (toEuclideanCLMₗ (n := n)) := fun _ _ h =>
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective h
  have hemb : Topology.IsEmbedding (toEuclideanCLMₗ (n := n)) :=
    (LinearMap.isClosedEmbedding_of_injective (f := toEuclideanCLMₗ (n := n))
      (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
  rw [hemb.tendsto_nhds_iff, map_zero]
  simp only [Function.comp_def, toEuclideanCLMₗ, LinearMap.coe_mk, AddHom.coe_mk, map_pow]

omit [DecidableEq n] in
/-- Let $(M_k)$ be a sequence of real square matrices. Then $M_k \to 0$ if and only if $M_k v \to 0$
for every vector $v$.

If $M_k v \to 0$ for every $v$, then every entry $(M_k)_{ij} = (M_k e_j)_i$ tends to $0$, and
convergence of matrices is entrywise. -/
theorem tendsto_zero_iff_forall_mulVec_tendsto_zero {M : ℕ → Matrix n n ℝ} :
    Tendsto M atTop (𝓝 0) ↔ ∀ v, Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0) := by
  classical
  constructor
  · intro h v
    have hc : Continuous fun C : Matrix n n ℝ => C *ᵥ v :=
      Continuous.matrix_mulVec continuous_id continuous_const
    simpa [Function.comp_def] using (hc.tendsto 0).comp h
  · intro h
    have key : Tendsto (fun k => (fun i j => M k i j : n → n → ℝ)) atTop
        (𝓝 (fun _ _ => (0 : ℝ))) := by
      refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
      have hsingle : ∀ k, (M k *ᵥ Pi.single j 1) i = M k i j := fun k => by simp
      simpa only [hsingle, Pi.zero_apply] using tendsto_pi_nhds.mp (h (Pi.single j 1)) i
    exact key

/-- Let $G$ be a real square matrix. Then $G^k \to 0$ if and only if $G^k u_0 \to 0$ for every
vector $u_0$.

This is the case $M_k = G^k$ of `Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero`. -/
theorem tendsto_pow_zero_iff_forall_mulVec (G : Matrix n n ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔
      ∀ u₀, Tendsto (fun k => (G ^ k) *ᵥ u₀) atTop (𝓝 0) :=
  tendsto_zero_iff_forall_mulVec_tendsto_zero

/-- Let $A$ be a real square matrix. Then
$$A^k \to 0 \iff \rho(A) < 1.$$

The proof goes through the complexification and the Gelfand formula. -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ complexSpectralRadius A < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hsubR : Subsingleton (Matrix n n ℝ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    have hsubC : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    have hle : complexSpectralRadius A ≤ 0 := by
      rw [complexSpectralRadius_eq_iSup]
      exact iSup₂_le fun k hk => absurd (isUnit_of_subsingleton _) hk
    have hconv : Tendsto (fun k => A ^ k) atTop (𝓝 0) := by
      have : (fun k => A ^ k) = fun _ : ℕ => (0 : Matrix n n ℝ) :=
        funext fun _ => Subsingleton.elim _ _
      rw [this]
      exact tendsto_const_nhds
    exact iff_of_true hconv (hle.trans_lt zero_lt_one)
  · have hR : Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔
        Tendsto (fun k => complexify A ^ k) atTop (𝓝 0) := by
      have hemb : Topology.IsEmbedding (complexifyₗ (n := n)) :=
        (LinearMap.isClosedEmbedding_of_injective (f := complexifyₗ (n := n))
          (LinearMap.ker_eq_bot.mpr complexify_injective)).isEmbedding
      rw [hemb.tendsto_nhds_iff]
      simp only [Function.comp_def, complexifyₗ, LinearMap.coe_mk, AddHom.coe_mk, complexify_pow,
        map_zero]
    have hspec : spectrum ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A))
        = spectrum ℂ (complexify A) :=
      AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (complexify A)
    have hsr : spectralRadius ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A))
        = complexSpectralRadius A := by
      simp only [spectralRadius_eq_of_unital, complexSpectralRadius_eq_iSup, hspec]
    rw [hR, tendsto_pow_iff_tendsto_pow_toEuclideanCLM,
      ← spectralRadius_lt_one_iff_tendsto_pow, hsr]

/-- Let $A$ be a real square matrix with $\rho(A) < 1$. Then $I - A$ is nonsingular.

The proof is the Neumann series. The complex spectral radius is the right hypothesis: the
spectral radius over $\mathbb{R}$ can be $0$ for a matrix with the complex eigenvalue $1$. -/
theorem isUnit_one_sub_of_complexSpectralRadius_lt_one {A : Matrix n n ℝ}
    (h : complexSpectralRadius A < 1) : IsUnit (1 - A) := by
  rw [← isUnit_complexify_iff, complexify_sub, complexify_one]
  have h' : spectralRadius ℂ (complexify A) < 1 := h
  have h1 : (1 : ℂ) ∈ resolventSet ℂ (complexify A) :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (by simpa using h')
  simpa [resolventSet] using h1

/-!
### The spectral radius is bounded by every matrix norm

The norm is an explicit function $f$ from the real $n \times n$ matrices to $\mathbb{R}_{\ge 0}$,
not a class argument such as `[NormedRing (Matrix n n ℝ)]`. A class argument
`[NormedRing (Matrix n n ℝ)]` carries a ring structure on the type `Matrix n n ℝ` that is unrelated
to `Matrix.instRing`. The statement with the class arguments `[NormedRing (Matrix n n ℝ)]`,
`[NormOneClass (Matrix n n ℝ)]` and `[NormedAlgebra ℝ (Matrix n n ℝ)]` and the conclusion
$\rho(A) \le \|A\|$ is therefore false. A counterexample: for a finite nonempty index type, take a
bijection $e$ from the real $n \times n$ matrices to $\mathbb{R}$ with $e(I) = 1$ and $e(A) = 0$ for
$A = 2I$, and transport the normed field structure of $\mathbb{R}$ along $e$. All three classes hold
(`NormOneClass` is elaborated against `Matrix.one`, which $e$ sends to $1$), but $\|A\| = 0$, while
$\rho(A) = 2$ is computed from the canonical structures. A plain function $f$ keeps every hypothesis
attached to the canonical ring and module structures of the matrices.
-/

section NormBound

variable (f : Matrix n n ℝ → ℝ≥0)

omit [DecidableEq n] in
/-- Let $f$ be a function from the real $n \times n$ matrices to $\mathbb{R}_{\ge 0}$ that is
submultiplicative, absolutely homogeneous and positive definite. Then $f$ bounds the entries of
a matrix up to one constant: there is $c \ge 0$ with $|b_{ij}| \le c \, f(B)$ for every matrix
$B$ and all indices $i$ and $j$.

The constant comes from the matrix units $E_{ij}$ (`Matrix.single i j 1`), for which
$E_{ii} B E_{jj} = b_{ij} E_{ij}$ (Mathlib's `Matrix.single_mul_mul_single`). Positive
definiteness makes $f(E_{ij})$ nonzero, so it can be inverted. -/
theorem exists_nnnorm_apply_le (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (hsmul : ∀ (r : ℝ) (B : Matrix n n ℝ), f (r • B) = ‖r‖₊ * f B)
    (hzero : ∀ B : Matrix n n ℝ, f B = 0 → B = 0) :
    ∃ c : ℝ≥0, ∀ (B : Matrix n n ℝ) (i j : n), ‖B i j‖₊ ≤ c * f B := by
  classical
  have hne : ∀ i j : n, f (single i j (1 : ℝ)) ≠ 0 := by
    intro i j h
    have h0 := hzero _ h
    have h1 : (single i j (1 : ℝ)) i j = 0 := by rw [h0]; simp
    simp at h1
  refine ⟨Finset.univ.sup fun p : n × n =>
    f (single p.1 p.1 (1 : ℝ)) * f (single p.2 p.2 (1 : ℝ)) / f (single p.1 p.2 (1 : ℝ)), ?_⟩
  intro B i j
  have key : single i i (1 : ℝ) * B * single j j (1 : ℝ) = B i j • single i j (1 : ℝ) := by
    rw [single_mul_mul_single, smul_single]
    simp
  have h1 : f (single i i (1 : ℝ) * B * single j j (1 : ℝ))
      ≤ f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ)) :=
    (hmul _ _).trans (by gcongr; exact hmul _ _)
  rw [key, hsmul] at h1
  have h2 : ‖B i j‖₊ ≤ f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ))
      / f (single i j (1 : ℝ)) := by
    rw [le_div_iff₀ (pos_iff_ne_zero.mpr (hne i j))]
    exact h1
  refine h2.trans ?_
  have h3 : f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ)) / f (single i j (1 : ℝ))
      = (f (single i i (1 : ℝ)) * f (single j j (1 : ℝ)) / f (single i j (1 : ℝ))) * f B := by
    ring
  rw [h3]
  gcongr
  exact Finset.le_sup (f := fun p : n × n =>
    f (single p.1 p.1 (1 : ℝ)) * f (single p.2 p.2 (1 : ℝ)) / f (single p.1 p.2 (1 : ℝ)))
    (Finset.mem_univ (i, j))

/-- If $f$ is submultiplicative, then $f(B^{k+1}) \le f(B)^{k+1}$ for every $k \ge 0$; the exponent
starts at $1$ because nothing gives $f(I) \le 1$. -/
private theorem apply_pow_le (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (B : Matrix n n ℝ) (k : ℕ) : f (B ^ (k + 1)) ≤ f B ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (B ^ (k + 1 + 1)) = f (B ^ (k + 1) * B) := by rw [pow_succ]
      _ ≤ f (B ^ (k + 1)) * f B := hmul _ _
      _ ≤ f B ^ (k + 1) * f B := by gcongr
      _ = f B ^ (k + 1 + 1) := (pow_succ _ _).symm

omit [DecidableEq n] in
/-- If $f$ is submultiplicative, bounds the entries up to a constant, and $f(B) < 1$, then
$B^k \to 0$ entrywise, so $\rho(B) < 1$ by
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. -/
private theorem complexSpectralRadius_lt_one_of_lt_one
    (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C) {c : ℝ≥0}
    (hc : ∀ (B : Matrix n n ℝ) (i j : n), ‖B i j‖₊ ≤ c * f B)
    {B : Matrix n n ℝ} (hB : f B < 1) : complexSpectralRadius B < 1 := by
  classical
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  have hg : Tendsto (fun k : ℕ => (c : ℝ) * (f B : ℝ) ^ k) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (f B : ℝ)) (f B).coe_nonneg
      (by exact_mod_cast hB)
    simpa using h.const_mul (c : ℝ)
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [Matrix.zero_apply]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : ‖(B ^ (m + 1)) i j‖₊ ≤ c * f B ^ (m + 1) :=
    (hc _ i j).trans (by gcongr; exact apply_pow_le f hmul B m)
  exact_mod_cast h

omit [DecidableEq n] in
/-- **The spectral radius of a real matrix is at most every submultiplicative matrix norm of it**.
Let $f$ be a function from the real $n \times n$ matrices to $\mathbb{R}_{\ge 0}$ that is
submultiplicative, $f(BC) \le f(B) f(C)$, absolutely homogeneous, $f(rB) = |r| f(B)$ for
$r \in \mathbb{R}$, and positive definite, $f(B) = 0 \Rightarrow B = 0$. Then for every real
square matrix $A$,
$$\rho(A) \le f(A).$$

The triangle inequality is not used, but none of the other three hypotheses can be dropped. For
$n = 2$, the function $B \mapsto |\det B|^{1/2}$ is submultiplicative and absolutely homogeneous
and sends $I$ to $1$, but it vanishes on $\begin{bmatrix} 1 & 0 \\ 0 & 0 \end{bmatrix}$, whose
spectral radius is $1$. Every scoped matrix norm satisfies all three hypotheses, and the
corollaries `Matrix.complexSpectralRadius_le_linfty_opNNNorm`,
`Matrix.complexSpectralRadius_le_frobenius_nnnorm` and
`Matrix.complexSpectralRadius_le_l2_opNNNorm` record the special cases.

For $f(A) < t$, the entries of the powers of $t^{-1} A$ are $O\bigl((f(A)/t)^k\bigr)$ by
`Matrix.exists_nnnorm_apply_le`. So $\rho(t^{-1} A) < 1$ by
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`, and `Matrix.complexSpectralRadius_smul`
undoes the scaling. -/
theorem complexSpectralRadius_le_of_norm (A : Matrix n n ℝ)
    (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (hsmul : ∀ (r : ℝ) (B : Matrix n n ℝ), f (r • B) = ‖r‖₊ * f B)
    (hzero : ∀ B : Matrix n n ℝ, f B = 0 → B = 0) :
    complexSpectralRadius A ≤ f A := by
  classical
  obtain ⟨c, hc⟩ := exists_nnnorm_apply_le f hmul hsmul hzero
  suffices h : ∀ t : ℝ≥0, f A < t → complexSpectralRadius A ≤ (t : ℝ≥0∞) by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    simpa using h (f A + ε) (lt_add_of_pos_right _ hε)
  intro t ht
  have ht0 : (0 : ℝ≥0) < t := zero_le.trans_lt ht
  have htR : (t : ℝ) ≠ 0 := by simpa using ht0.ne'
  have hlt : complexSpectralRadius ((t : ℝ)⁻¹ • A) < 1 := by
    refine complexSpectralRadius_lt_one_of_lt_one f hmul hc ?_
    rw [hsmul]
    have hinv : ‖(t : ℝ)⁻¹‖₊ = t⁻¹ := by rw [nnnorm_inv]; simp
    rw [hinv, inv_mul_eq_div, div_lt_one ht0]
    exact ht
  have hA : (t : ℝ) • ((t : ℝ)⁻¹ • A) = A := by
    rw [smul_smul, mul_inv_cancel₀ htR, one_smul]
  calc complexSpectralRadius A
      = complexSpectralRadius ((t : ℝ) • ((t : ℝ)⁻¹ • A)) := by rw [hA]
    _ = (t : ℝ≥0∞) * complexSpectralRadius ((t : ℝ)⁻¹ • A) := by
        rw [complexSpectralRadius_smul]; norm_num
    _ ≤ (t : ℝ≥0∞) * 1 := by gcongr
    _ = t := mul_one _

end NormBound

/-! ### The scoped matrix norms -/

section Operator

open scoped Matrix.Norms.Operator

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix. Then $\rho(A)$ is at most the maximum absolute row sum norm
$\|A\|_\infty = \max_i \sum_j |a_{ij}|$ (Mathlib's `Matrix.linfty_opNNNorm_def`). -/
theorem complexSpectralRadius_le_linfty_opNNNorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

omit [DecidableEq n] in
/-- The spectral radius $\rho(A)$ of a real square matrix over a finite index type is finite. -/
theorem complexSpectralRadius_ne_top (A : Matrix n n ℝ) : complexSpectralRadius A ≠ ⊤ :=
  ((complexSpectralRadius_le_linfty_opNNNorm A).trans_lt ENNReal.coe_lt_top).ne

/-- Let $A$ be a real square matrix. Then the maximum absolute row sum norm does not change under
complexification: $\|A_{\mathbb{C}}\|_\infty = \|A\|_\infty$.

The norm is computed from the moduli of the entries, and complexification does not change them. -/
theorem linfty_opNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ := by
  simp only [linfty_opNorm_def, complexify, Matrix.map_apply, Complex.nnnorm_real]

/-- **Gelfand's formula in the maximum absolute row sum norm**. Let $A$ be a real square matrix.
Then
$$\|A^k\|_\infty^{1/k} \to \rho(A) \quad \text{as } k \to \infty.$$

The proof is the proof of `Matrix.tendsto_pow_rpow_complexSpectralRadius`, with
`Matrix.linfty_opNorm_complexify` in place of `Matrix.l2_opNorm_complexify`. The limit is the
same, because two norms on a finite-dimensional space differ by a factor $C$, and
$C^{1/k} \to 1$. This norm is the operator norm of $A$ on $\mathbb{R}^n$ with the maximum norm
(`Matrix.linfty_opNorm_eq_opNorm`). The limit is `(Matrix.complexSpectralRadius A).toReal`, the
real number $\rho(A)$. -/
theorem tendsto_pow_rpow_linfty_opNorm (A : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (complexSpectralRadius A).toReal) := by
  have hnorm : ∀ k : ℕ, ‖(complexify A) ^ k‖ = ‖A ^ k‖ := fun k => by
    rw [← complexify_pow, linfty_opNorm_complexify]
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  simp only [hnorm] at hgel
  have h := (ENNReal.tendsto_toReal (complexSpectralRadius_ne_top A)).comp hgel
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

end Operator

section Frobenius

open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix. Then $\rho(A)$ is at most the Frobenius norm $\|A\|_F$ of $A$.
-/
theorem complexSpectralRadius_le_frobenius_nnnorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ := by
  classical
  exact complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

/-- Let $A$ be a real square matrix. Then the Frobenius norm does not change under complexification:
$\|A_{\mathbb{C}}\|_F = \|A\|_F$, because it is computed from the moduli of the entries. -/
theorem frobenius_norm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ :=
  A.frobenius_norm_map_eq Complex.ofReal fun a => by simp

end Frobenius

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- Let $A$ be a real square matrix. Then $\rho(A)$ is at most the spectral norm $\|A\|_2$ of $A$.
-/
theorem complexSpectralRadius_le_l2_opNNNorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

omit [DecidableEq n] in
/-- A complex vector $w$ satisfies $\|w\|^2 = \|\operatorname{Re} w\|^2 + \|\operatorname{Im} w\|^2$
in the Euclidean norm. -/
private theorem norm_sq_toLp_complex (w : n → ℂ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ ^ 2
      = ‖(WithLp.toLp 2 (fun i => (w i).re) : EuclideanSpace ℝ n)‖ ^ 2
        + ‖(WithLp.toLp 2 (fun i => (w i).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

omit [DecidableEq n] in
/-- The real part of $A_{\mathbb{C}} w$ is $A \operatorname{Re} w$. -/
private theorem complexify_mulVec_re (A : Matrix n n ℝ) (w : n → ℂ) (i : n) :
    ((complexify A *ᵥ w) i).re = (A *ᵥ fun j => (w j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

omit [DecidableEq n] in
/-- The imaginary part of $A_{\mathbb{C}} w$ is $A \operatorname{Im} w$. -/
private theorem complexify_mulVec_im (A : Matrix n n ℝ) (w : n → ℂ) (i : n) :
    ((complexify A *ᵥ w) i).im = (A *ᵥ fun j => (w j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

omit [DecidableEq n] in
/-- A real vector has the same Euclidean norm as a complex vector. -/
private theorem norm_toLp_ofReal (x : n → ℝ) :
    ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ n)‖
      = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

/-- **The spectral norm does not change under complexification**. Let $A$ be a real square matrix.
Then $\|A_{\mathbb{C}}\|_2 = \|A\|_2$.

The inequality $\ge$ holds because a real vector is a complex vector of the same norm. The
inequality $\le$ holds because a complex vector is $x + iy$ with real $x$ and $y$, and $\|A(x +
iy)\|^2 = \|Ax\|^2 + \|Ay\|^2 \le \|A\|^2 (\|x\|^2 + \|y\|^2)$. With
`Matrix.linfty_opNorm_complexify` and `Matrix.frobenius_norm_complexify`, which hold because
those norms are computed from the entries, this transports every statement about $\|A^k\|$ to
the complexification, where the Gelfand formula holds. -/
theorem l2_opNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · rw [← l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    set w : n → ℂ := WithLp.ofLp z with hw
    have hz : z = WithLp.toLp 2 w := rfl
    have himg : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2
        = ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
          + ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
      rw [hz, toEuclideanCLM_toLp, norm_sq_toLp_complex]
      simp only [complexify_mulVec_re, complexify_mulVec_im]
    have hnorm : ‖z‖ ^ 2
        = ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
          + ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
      rw [hz, norm_sq_toLp_complex]
    have hre : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖
        ≤ ‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖ := by
      rw [← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
      exact ContinuousLinearMap.le_opNorm _ _
    have him : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖
        ≤ ‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖ := by
      rw [← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
      exact ContinuousLinearMap.le_opNorm _ _
    have hre2 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
        ≤ (‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) hre
    have him2 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2
        ≤ (‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) him
    have hsq : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2 ≤ (‖A‖ * ‖z‖) ^ 2 := by
      rw [himg, mul_pow, hnorm, mul_add]
      rw [mul_pow] at hre2 him2
      linarith
    calc ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖
        = √(‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √((‖A‖ * ‖z‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖A‖ * ‖z‖ := Real.sqrt_sq (by positivity)
  · rw [← l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set v : n → ℝ := WithLp.ofLp x with hv
    have hx : x = WithLp.toLp 2 v := rfl
    have hmul : (fun i => (((A *ᵥ v) i : ℝ) : ℂ)) = complexify A *ᵥ fun j => ((v j : ℝ) : ℂ) := by
      funext i
      simp [mulVec, dotProduct, complexify]
    calc ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖
        = ‖(WithLp.toLp 2 (fun i => (((A *ᵥ v) i : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ := by
          rw [norm_toLp_ofReal, hx, toEuclideanCLM_toLp]
      _ = ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A)
            (WithLp.toLp 2 fun j => ((v j : ℝ) : ℂ))‖ := by rw [hmul, toEuclideanCLM_toLp]
      _ ≤ ‖complexify A‖ * ‖(WithLp.toLp 2 fun j => ((v j : ℝ) : ℂ) : EuclideanSpace ℂ n)‖ := by
          rw [← l2_opNorm_toEuclideanCLM (𝕜 := ℂ)]
          exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖complexify A‖ * ‖x‖ := by rw [norm_toLp_ofReal, hx]

/-- **Gelfand's formula for a real matrix**. Let $A$ be a real square matrix. Then in the spectral
norm,
$$\|A^k\|_2^{1/k} \to \rho(A) \quad \text{as } k \to \infty.$$
This is the general convergence factor of a linear stationary iteration: whatever the norm, the
asymptotic rate of decay of the powers of the iteration matrix is its spectral radius.

The same proof gives the result for the maximum absolute row sum norm and for the Frobenius
norm, with `Matrix.linfty_opNorm_complexify` or `Matrix.frobenius_norm_complexify` in place of
`Matrix.l2_opNorm_complexify`. The limit does not depend on the norm, because two norms on a
finite-dimensional space differ by a factor $C$, and $C^{1/k} \to 1$. The limit is
`(Matrix.complexSpectralRadius A).toReal`, the real number $\rho(A)$. -/
theorem tendsto_pow_rpow_complexSpectralRadius (A : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (complexSpectralRadius A).toReal) := by
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have hnorm : ∀ k : ℕ, ‖(complexify A) ^ k‖ = ‖A ^ k‖ := fun k => by
    rw [← complexify_pow, l2_opNorm_complexify]
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  simp only [hnorm] at hgel
  have h := (ENNReal.tendsto_toReal (complexSpectralRadius_ne_top A)).comp hgel
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- **The real Neumann series**. Let $A$ be a real square matrix with $\rho(A) < 1$. Then the series
$\sum_{k \ge 0} A^k$ converges, with the sum
$$\sum_{k=0}^{\infty} A^k = (I - A)^{-1}.$$
This is the real form of Theorem 1.5 of [quarteroni2000numerical], display (1.25), with only the
hypothesis on the spectral radius.

The summability comes from the geometric decay $\|A^k\| \le C r^k$ of the complexification
(`exists_norm_pow_le_of_spectralRadius_lt`, with `Matrix.l2_opNorm_complexify`). The sum is
identified by $(I - A) \sum_k A^k = I$. -/
theorem hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one {A : Matrix n n ℝ}
    (h : complexSpectralRadius A < 1) : HasSum (fun k => A ^ k) (1 - A)⁻¹ := by
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have _ : CompleteSpace (Matrix n n ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, -, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt (complexify A) hr1
  have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
  have hs : Summable (fun k => A ^ k) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one r.coe_nonneg hrlt).mul_left C)
      fun k => by rw [← l2_opNorm_complexify, complexify_pow]; exact hC k
  rw [Matrix.inv_eq_right_inv hs.one_sub_mul_tsum_pow]
  exact hs.hasSum

/-- **The geometric series of a real matrix converges if and only if $\rho(A) < 1$**. Let $A$ be a
real square matrix. Then the series $\sum_{k \ge 0} A^k$ is summable if and only if
$\rho(A) < 1$. This is Theorem 1.5 of [quarteroni2000numerical]. -/
theorem summable_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) :
    Summable (fun k => A ^ k) ↔ complexSpectralRadius A < 1 :=
  ⟨fun hs => (tendsto_pow_iff_complexSpectralRadius_lt_one A).1 hs.tendsto_atTop_zero,
    fun h => (hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one h).summable⟩

/-- **If $\rho(A) < 1$, then some power of the operator $A$ is a contraction**. Let $A$ be a real
square matrix with $\rho(A) < 1$, and let $T$ be a continuous linear map on the Euclidean space
$\mathbb{R}^n$ whose underlying linear map is $x \mapsto Ax$ (`Matrix.toEuclideanLin A`). Then
$\|T^k\| < 1$ for some $k$, where $\|T^k\|$ is the spectral norm of $A^k$.

This connects the condition $\rho(J_G(x^*)) < 1$ (Property 7.3 of [quarteroni2000numerical], and
the criteria for stationary iterations of its Chapter 4, read on the Euclidean space) to the
Ostrowski theorem in Banach spaces, without a change of the norm on $\mathbb{R}^n$. -/
theorem exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one
    {A : Matrix n n ℝ} (hA : complexSpectralRadius A < 1)
    {T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n}
    (hT : (T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) = toEuclideanLin A) :
    ∃ k, ‖T ^ k‖ < 1 := by
  have hT' : T = toEuclideanCLM (n := n) (𝕜 := ℝ) A :=
    ContinuousLinearMap.coe_injective (hT.trans (coe_toEuclideanCLM_eq_toEuclideanLin A).symm)
  have h := ((tendsto_pow_iff_complexSpectralRadius_lt_one A).2 hA).norm
  rw [norm_zero] at h
  obtain ⟨k, hk⟩ := (h.eventually_lt_const one_pos).exists
  exact ⟨k, by rwa [hT', ← map_pow, l2_opNorm_toEuclideanCLM]⟩

/-- Let $A$ be a real square matrix with $\rho(A) < 1$. Then $\|T^k\| < 1$ for some $k$, where $T$
is the operator `Matrix.toEuclideanCLM A` on the Euclidean space $\mathbb{R}^n$. This is the
form of `Matrix.exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one` for
`Matrix.toEuclideanCLM`. -/
theorem exists_norm_toEuclideanCLM_pow_lt_one_of_complexSpectralRadius_lt_one {A : Matrix n n ℝ}
    (hA : complexSpectralRadius A < 1) :
    ∃ k, ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A ^ k‖ < 1 :=
  exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one hA
    (coe_toEuclideanCLM_eq_toEuclideanLin A)

/-- **The average convergence rate tends to the asymptotic convergence rate**. Let $G$ be a real
square matrix with $\rho(G) \neq 0$. Then in the spectral norm,
$$-\frac{1}{m} \log \|G^m\|_2 \to -\log \rho(G) \quad \text{as } m \to \infty.$$
This is (4.5) of [quarteroni2000numerical].

The proof composes Gelfand's formula `Matrix.tendsto_pow_rpow_complexSpectralRadius` with the
logarithm. The same holds in the maximum absolute row sum norm, through
`Matrix.tendsto_pow_rpow_linfty_opNorm`. -/
theorem tendsto_averageConvergenceRate (G : Matrix n n ℝ) (hG : complexSpectralRadius G ≠ 0) :
    Tendsto (fun m : ℕ => -(1 / m : ℝ) * Real.log ‖G ^ m‖) atTop
      (𝓝 (-Real.log (complexSpectralRadius G).toReal)) := by
  have hρ : 0 < (complexSpectralRadius G).toReal :=
    ENNReal.toReal_pos hG (complexSpectralRadius_ne_top G)
  simpa only [neg_mul] using (tendsto_one_div_mul_log_of_tendsto_rpow_one_div
    (fun m => norm_nonneg _) hρ (tendsto_pow_rpow_complexSpectralRadius G)).neg

/-- For every $k$, the quotient $(\|G^k d_0\| / \|d_0\|)^{1/k}$ is at most $\|G^k\|_2^{1/k}$: the
specific convergence factor is bounded termwise by the general one. -/
private theorem rpow_le_rpow_norm_pow (G : Matrix n n ℝ) (d₀ : n → ℝ) (k : ℕ) :
    (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
      / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ) ≤ ‖G ^ k‖ ^ (1 / k : ℝ) := by
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)) with h | h
  · have hd : (WithLp.toLp 2 d₀ : EuclideanSpace ℝ n) = 0 := by
      rwa [eq_comm, norm_eq_zero] at h
    have hd0 : d₀ = 0 := by
      have hc := congrArg (WithLp.ofLp (p := 2)) hd
      simpa using hc
    simp [hd0]
  · rw [div_le_iff₀ h]
    exact l2_opNorm_mulVec _ (WithLp.toLp 2 d₀)

/-- Let $G$ be a real square matrix and let $d_0 \in \mathbb{R}^n$. Then the **specific convergence
factor** of the initial error $d_0$ is at most the spectral radius:
$$\limsup_{k \to \infty} \left(\frac{\|G^k d_0\|}{\|d_0\|}\right)^{1/k} \le \rho(G),$$
in the Euclidean norm.

With `Matrix.exists_limsup_norm_pow_mulVec_rpow_eq`, which says that some $d_0$ attains the
bound, this identifies the spectral radius as the worst asymptotic rate of a linear stationary
iteration: no initial error decays more slowly, and some initial error decays exactly that
slowly. For $d_0 = 0$ the quotient is $0$ in Lean, and the statement still holds. -/
theorem limsup_norm_pow_mulVec_rpow_le (G : Matrix n n ℝ) (d₀ : n → ℝ) :
    limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
        / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
      ≤ (complexSpectralRadius G).toReal := by
  calc limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
        / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
      ≤ limsup (fun k : ℕ => ‖G ^ k‖ ^ (1 / k : ℝ)) atTop :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall (rpow_le_rpow_norm_pow G d₀))
          (Filter.isCoboundedUnder_le_of_le atTop fun k => Real.rpow_nonneg (by positivity) _)
          (tendsto_pow_rpow_complexSpectralRadius G).isBoundedUnder_le
    _ = (complexSpectralRadius G).toReal :=
        (tendsto_pow_rpow_complexSpectralRadius G).limsup_eq

omit [DecidableEq n] in
/-- **The spectral radius of a real matrix is attained at a complex eigenvalue**, with an
eigenvector. Let $G$ be a real square matrix with $n \ge 1$. Then there are $\mu \in \mathbb{C}$
and a vector $v \neq 0$ in $\mathbb{C}^n$ with
$$G_{\mathbb{C}} v = \mu v \quad \text{and} \quad |\mu| = \rho(G).$$

The complex spectrum is compact and nonempty, so the modulus attains its maximum on it, and an
eigenvalue of a matrix has an eigenvector. -/
theorem exists_eigenvector_norm_eq_complexSpectralRadius [Nonempty n] (G : Matrix n n ℝ) :
    ∃ (μ : ℂ) (v : n → ℂ), v ≠ 0 ∧ complexify G *ᵥ v = μ • v ∧
      ‖μ‖ = (complexSpectralRadius G).toReal := by
  classical
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨μ, hμ, hmax⟩ := (spectrum.isCompact (complexify G)).exists_isMaxOn
    (spectrum.nonempty (complexify G)) continuous_norm.continuousOn
  have hsr : complexSpectralRadius G = (‖μ‖₊ : ℝ≥0∞) := by
    refine le_antisymm ?_ (nnnorm_le_complexSpectralRadius hμ)
    rw [complexSpectralRadius_eq_iSup]
    exact iSup₂_le fun ν hν => mod_cast hmax hν
  have hdet : (algebraMap ℂ (Matrix n n ℂ) μ - complexify G).det = 0 := by
    have h := spectrum.mem_iff.mp hμ
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
    exact not_not.mp h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨μ, v, hv0, ?_, ?_⟩
  · rw [sub_mulVec] at hv
    have halg : algebraMap ℂ (Matrix n n ℂ) μ *ᵥ v = μ • v := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
    rw [halg] at hv
    exact (sub_eq_zero.mp hv).symm
  · rw [hsr]
    simp

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix and let $e \in \mathbb{R}^n$. Then $A_{\mathbb{C}}$ acts on $e$,
viewed as a complex vector, as $A$ does: $A_{\mathbb{C}} e = Ae$. -/
theorem complexify_mulVec_ofReal (A : Matrix n n ℝ) (e : n → ℝ) :
    complexify A *ᵥ (fun i => (e i : ℂ)) = fun i => ((A *ᵥ e) i : ℂ) := by
  ext i
  simp [mulVec, dotProduct, complexify_apply]

/-- Let $X$ be a real square matrix with $n \ge 1$. Then $\rho(X) < 1$ if and only if every complex
eigenvalue $\mu$ of $X$ satisfies $|\mu| < 1$.

The assumption $n \ge 1$ makes the spectrum nonempty, so the spectral radius is attained. -/
theorem complexSpectralRadius_lt_one_iff_forall_norm_lt [Nonempty n] (X : Matrix n n ℝ) :
    complexSpectralRadius X < 1 ↔ ∀ μ ∈ spectrum ℂ (complexify X), ‖μ‖ < 1 := by
  constructor
  · intro h μ hμ
    have : (‖μ‖₊ : ℝ≥0∞) ≤ complexSpectralRadius X := nnnorm_le_complexSpectralRadius hμ
    have h1 := this.trans_lt h
    rwa [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one, coe_nnnorm] at h1
  · intro h
    obtain ⟨μ, v, hv, hμv, hμ⟩ := exists_eigenvector_norm_eq_complexSpectralRadius X
    have hmem : μ ∈ spectrum ℂ (complexify X) :=
      (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμv⟩
    have h1 := h μ hmem
    rw [hμ] at h1
    rwa [← ENNReal.toReal_lt_toReal (complexSpectralRadius_ne_top X) ENNReal.one_ne_top,
      ENNReal.toReal_one]

/-- For $n \ge 1$, some nonzero real vector $d_0$ and some $c > 0$ satisfy
$\|G^k d_0\| \ge c \, \rho(G)^k$ for infinitely many $k$.

The vector is the real or the imaginary part of an eigenvector for an eigenvalue of largest
modulus. Which part works can depend on $k$, but not both parts fail for infinitely many $k$, so
one choice works for infinitely many $k$; the conclusion needs only a `limsup`. -/
private theorem exists_frequently_norm_pow_mulVec_ge [Nonempty n] (G : Matrix n n ℝ) :
    ∃ d₀ : n → ℝ, d₀ ≠ 0 ∧ ∃ c > 0, ∃ᶠ k : ℕ in atTop,
      c * (complexSpectralRadius G).toReal ^ k
        ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ := by
  obtain ⟨μ, v, hv0, heig, hμ⟩ := exists_eigenvector_norm_eq_complexSpectralRadius G
  set ρ := (complexSpectralRadius G).toReal with hρdef
  have hρ0 : 0 ≤ ρ := hμ ▸ norm_nonneg μ
  set x : n → ℝ := fun j => (v j).re with hxdef
  set y : n → ℝ := fun j => (v j).im with hydef
  set P : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ with hPdef
  have hvne : (WithLp.toLp 2 v : EuclideanSpace ℂ n) ≠ 0 := fun h =>
    hv0 (by simpa using congrArg (WithLp.ofLp (p := 2)) h)
  have hP : 0 < P := norm_pos_iff.mpr hvne
  have hsplit : P ^ 2 = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2
      + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ ^ 2 := norm_sq_toLp_complex v
  have hpow : ∀ k : ℕ, complexify (G ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    rw [complexify_pow]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← mulVec_mulVec, heig, mulVec_smul, ih, smul_smul, mul_comm]
  have hpy : ∀ k : ℕ, ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖ ^ 2
      + ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ ^ 2 = (ρ ^ k * P) ^ 2 := by
    intro k
    have h := norm_sq_toLp_complex (complexify (G ^ k) *ᵥ v)
    simp only [complexify_mulVec_re, complexify_mulVec_im] at h
    rw [← h, hpow k]
    have hsm : (WithLp.toLp 2 (μ ^ k • v) : EuclideanSpace ℂ n)
        = μ ^ k • (WithLp.toLp 2 v : EuclideanSpace ℂ n) := rfl
    rw [hsm, norm_smul, norm_pow, hμ]
  have hmaxk : ∀ k : ℕ, ρ ^ k * P / 2
      ≤ max ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
          ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := by
    intro k
    have ha : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hb : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hpk : (0 : ℝ) ≤ ρ ^ k * P := mul_nonneg (pow_nonneg hρ0 k) hP.le
    have h := hpy k
    rcases le_total ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
        ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ with h' | h'
    · rw [max_eq_right h']; nlinarith
    · rw [max_eq_left h']; nlinarith
  -- the degenerate case `ρ = 0`: any nonzero real or imaginary part will do
  rcases eq_or_lt_of_le hρ0 with hρ | hρ
  · have hchoice : ∃ d₀ : n → ℝ, d₀ ≠ 0 := by
      rcases eq_or_ne x 0 with hx0 | hx0
      · refine ⟨y, fun hy0 => ?_⟩
        have h1 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ = 0 := by rw [hx0]; simp
        have h2 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ = 0 := by rw [hy0]; simp
        rw [h1, h2] at hsplit
        nlinarith
      · exact ⟨x, hx0⟩
    obtain ⟨d₀, hd₀⟩ := hchoice
    refine ⟨d₀, hd₀, 1, one_pos, Filter.Eventually.frequently ?_⟩
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← hρ, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  -- the generic case: one of the two parts is frequently large, and is then nonzero
  · have hne : ∀ d : n → ℝ, (∃ᶠ k : ℕ in atTop,
        ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d) : EuclideanSpace ℝ n)‖) → d ≠ 0 := by
      rintro d hd rfl
      obtain ⟨k, hk⟩ := hd.exists
      have hz : ‖(WithLp.toLp 2 (G ^ k *ᵥ (0 : n → ℝ)) : EuclideanSpace ℝ n)‖ = 0 := by simp
      rw [hz] at hk
      nlinarith [pow_pos hρ k, hP]
    by_cases hfx : ∃ᶠ k : ℕ in atTop,
        ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
    · exact ⟨x, hne x hfx, P / 2, by linarith, hfx.mono fun k hk => by linarith [hk]⟩
    · rw [Filter.not_frequently] at hfx
      have hfy : ∃ᶠ k : ℕ in atTop,
          ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := by
        refine Filter.Eventually.frequently ?_
        filter_upwards [hfx] with k hk
        rcases max_cases ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
            ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ with ⟨he, -⟩ | ⟨he, -⟩
        · exact absurd (he ▸ hmaxk k) hk
        · exact he ▸ hmaxk k
      exact ⟨y, hne y hfy, P / 2, by linarith, hfy.mono fun k hk => by linarith [hk]⟩

/-- **The general convergence factor of a real iteration matrix is its spectral radius, and it is
attained**. Let $G$ be a real square matrix with $n \ge 1$. Then there is a nonzero initial
error $d_0 \in \mathbb{R}^n$ whose specific convergence factor equals $\rho(G)$:
$$\limsup_{k \to \infty} \left(\frac{\|G^k d_0\|}{\|d_0\|}\right)^{1/k} = \rho(G),$$
in the Euclidean norm.

With `Matrix.limsup_norm_pow_mulVec_rpow_le`, which bounds every specific convergence factor by
$\rho(G)$, this says that the spectral radius is the exact asymptotic rate of the
slowest-decaying error of a linear stationary iteration. The vector $d_0$ is the real or the
imaginary part of an eigenvector for an eigenvalue of largest modulus. A rotation shows that
neither part works for every $k$, so the statement is about a $\limsup$ and not about a limit. -/
theorem exists_limsup_norm_pow_mulVec_rpow_eq [Nonempty n] (G : Matrix n n ℝ) :
    ∃ d₀ : n → ℝ, d₀ ≠ 0 ∧
      limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
          / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
        = (complexSpectralRadius G).toReal := by
  obtain ⟨d₀, hd₀, c, hc, hfreq⟩ := exists_frequently_norm_pow_mulVec_ge G
  refine ⟨d₀, hd₀, le_antisymm (limsup_norm_pow_mulVec_rpow_le G d₀) ?_⟩
  set ρ := (complexSpectralRadius G).toReal with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  set D : ℝ := ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖ with hDdef
  have hD : 0 < D := norm_pos_iff.mpr fun h =>
    hd₀ (by simpa using congrArg (WithLp.ofLp (p := 2)) h)
  set a : ℕ → ℝ := fun k => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ / D)
    ^ (1 / k : ℝ) with hadef
  have habdd : Filter.IsBoundedUnder (· ≤ ·) atTop a := by
    obtain ⟨B, hB⟩ := (tendsto_pow_rpow_complexSpectralRadius G).isBoundedUnder_le
    rw [Filter.eventually_map] at hB
    refine ⟨B, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hB] with k hk using (rpow_le_rpow_norm_pow G d₀ k).trans hk
  have hfa : ∃ᶠ k : ℕ in atTop, (c / D) ^ (1 / k : ℝ) * ρ ≤ a k := by
    refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro k ⟨hk, hk1⟩
    have hstep : c / D * ρ ^ k ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ / D := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
      exact hk
    calc (c / D) ^ (1 / k : ℝ) * ρ
        = (c / D * ρ ^ k) ^ (1 / k : ℝ) := by
          rw [Real.mul_rpow (by positivity) (pow_nonneg hρ0 k), one_div,
            Real.pow_rpow_inv_natCast hρ0 (by omega)]
      _ ≤ a k := Real.rpow_le_rpow (by positivity) hstep (by positivity)
  have hlim : Tendsto (fun k : ℕ => (c / D) ^ (1 / k : ℝ) * ρ) atTop (𝓝 ρ) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : ContinuousAt (fun t : ℝ => (c / D) ^ t) 0 :=
      Real.continuousAt_const_rpow (by positivity)
    have h3 : Tendsto (fun k : ℕ => (c / D) ^ (1 / k : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using h2.tendsto.comp h1
    simpa using h3.mul_const ρ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h2 : ∀ᶠ k : ℕ in atTop, ρ - ε < (c / D) ^ (1 / k : ℝ) * ρ :=
    hlim.eventually_const_lt (by linarith)
  have h3 : ∃ᶠ k : ℕ in atTop, ρ - ε ≤ a k :=
    (hfa.and_eventually h2).mono fun k hk => le_trans hk.2.le hk.1
  have h4 := Filter.le_limsup_of_frequently_le h3 habdd
  linarith

end L2Operator

section PosDef

open scoped ComplexOrder

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix, and let $z = x + iy$ with $x, y \in \mathbb{R}^n$. Then the
real part of the Hermitian form of $A_{\mathbb{C}}$ at $z$ is the sum of the real bilinear forms
at $x$ and at $y$:
$$\operatorname{Re}(z^H A_{\mathbb{C}} z) = x^T A x + y^T A y.$$
-/
theorem re_star_dotProduct_complexify_mulVec (A : Matrix n n ℝ) (z : n → ℂ) :
    (star z ⬝ᵥ (complexify A *ᵥ z)).re
      = (fun i => (z i).re) ⬝ᵥ (A *ᵥ fun i => (z i).re)
        + (fun i => (z i).im) ⬝ᵥ (A *ᵥ fun i => (z i).im) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, complexify_mulVec_re, complexify_mulVec_im,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq n] in
/-- Let $A$ be a real square matrix, and let $z = x + iy$ with $x, y \in \mathbb{R}^n$. Then the
imaginary part of the Hermitian form of $A_{\mathbb{C}}$ at $z$ is
$$\operatorname{Im}(z^H A_{\mathbb{C}} z) = x^T A y - y^T A x.$$
It vanishes when $A$ is symmetric. -/
theorem im_star_dotProduct_complexify_mulVec (A : Matrix n n ℝ) (z : n → ℂ) :
    (star z ⬝ᵥ (complexify A *ᵥ z)).im
      = (fun i => (z i).re) ⬝ᵥ (A *ᵥ fun i => (z i).im)
        - (fun i => (z i).im) ⬝ᵥ (A *ᵥ fun i => (z i).re) := by
  simp only [dotProduct, Pi.star_apply, Complex.im_sum, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, complexify_mulVec_re, complexify_mulVec_im,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [DecidableEq n] in
/-- **The Hermitian form of the complexification of a symmetric real matrix is real**. Let $A$ be a
real symmetric matrix, and let $z = x + iy$ with $x, y \in \mathbb{R}^n$. Then
$$z^H A_{\mathbb{C}} z = x^T A x + y^T A y,$$
a real number viewed as a complex number. -/
theorem star_dotProduct_complexify_mulVec_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (z : n → ℂ) :
    star z ⬝ᵥ (complexify A *ᵥ z)
      = (((fun i => (z i).re) ⬝ᵥ (A *ᵥ fun i => (z i).re)
        + (fun i => (z i).im) ⬝ᵥ (A *ᵥ fun i => (z i).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, re_star_dotProduct_complexify_mulVec]
  · rw [Complex.ofReal_im, im_star_dotProduct_complexify_mulVec,
      hA.isSymm.dotProduct_mulVec_comm, sub_self]

omit [Fintype n] [DecidableEq n] in
/-- Let $A$ be a real positive semidefinite matrix over a finite index type. Then $A_{\mathbb{C}}$
is positive semidefinite. -/
theorem PosSemidef.complexify [Finite n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.complexify.PosSemidef := by
  let : Fintype n := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg
    ((isHermitian_complexify_iff A).2 hA.isHermitian) fun z => ?_
  rw [star_dotProduct_complexify_mulVec_of_isHermitian hA.isHermitian, Complex.zero_le_real]
  exact add_nonneg (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (z i).re))
    (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (z i).im))

-- `Matrix.PosDef` is stated with finitely supported sums and needs no `Fintype n`, but the proof
-- goes through the `dotProduct` form `Matrix.posDef_iff_dotProduct_mulVec`, which does.
set_option linter.unusedFintypeInType false in
omit [DecidableEq n] in
/-- **A real matrix is positive definite if and only if its complexification is**. Let $A$ be a real
square matrix. Then $A_{\mathbb{C}}$ is positive definite if and only if $A$ is positive
definite.

The complex Hermitian form at $x + iy$ is the sum of the real quadratic forms at $x$ and at $y$
(`Matrix.star_dotProduct_complexify_mulVec_of_isHermitian`), and a real vector is a complex
vector with imaginary part zero. -/
theorem posDef_complexify_iff {A : Matrix n n ℝ} : (complexify A).PosDef ↔ A.PosDef := by
  rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec, isHermitian_complexify_iff]
  simp only [star_trivial]
  constructor
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun x hx => ?_⟩
    have hz : (fun i => (x i : ℂ)) ≠ 0 := fun h0 =>
      hx (funext fun i => by simpa using congrFun h0 i)
    have hpos := h hz
    rw [star_dotProduct_complexify_mulVec_of_isHermitian hA, Complex.zero_lt_real] at hpos
    simpa using hpos
  · rintro ⟨hA, h⟩
    refine ⟨hA, fun z hz => ?_⟩
    rw [star_dotProduct_complexify_mulVec_of_isHermitian hA, Complex.zero_lt_real]
    have hnonneg : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := fun x => by
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · exact (h hx).le
    rcases eq_or_ne (fun i => (z i).re) 0 with hre | hre
    · have him : (fun i => (z i).im) ≠ 0 := fun him =>
        hz (funext fun i => Complex.ext (by simpa using congrFun hre i)
          (by simpa using congrFun him i))
      have := h him
      linarith [hnonneg fun i => (z i).re]
    · have := h hre
      linarith [hnonneg fun i => (z i).im]

end PosDef

/-- **The spectral radius of a real matrix is at most every algebra norm of it**. Let $N$ be an
algebra norm on the real $n \times n$ matrices (`AlgebraNorm ℝ (Matrix n n ℝ)`), and let $A$ be
a real square matrix. Then
$$\rho(A) \le N(A).$$
This is Theorem 1.4 of [quarteroni2000numerical], for a submultiplicative matrix norm.

This is the real form of `spectralRadius_le_algebraNorm`. The norm is a bundled `AlgebraNorm`,
so that its hypotheses are attached to the canonical ring and module structures of the matrices.
A statement with a class argument `[NormedRing (Matrix n n ℝ)]` instead would be false, for the
reason given in the sectioning comment before `Matrix.exists_nnnorm_apply_le`. -/
theorem complexSpectralRadius_le_algebraNorm (N : AlgebraNorm ℝ (Matrix n n ℝ))
    (A : Matrix n n ℝ) : complexSpectralRadius A ≤ ENNReal.ofReal (N A) := by
  have hmono : ∀ B, (0 : ℝ) ≤ N B := fun B => apply_nonneg N B
  refine (complexSpectralRadius_le_of_norm (fun B => (N B).toNNReal) A ?_ ?_ ?_).trans_eq ?_
  · intro B C
    rw [← Real.toNNReal_mul (hmono B)]
    exact Real.toNNReal_mono (map_mul_le_mul N B C)
  · intro r B
    rw [map_smul_eq_mul N, Real.toNNReal_mul (norm_nonneg r)]
    congr 1
    ext
    simp
  · intro B hB
    refine eq_zero_of_map_eq_zero N (le_antisymm ?_ (hmono B))
    simpa [Real.toNNReal_eq_zero] using hB
  · rfl

/-- **The powers of a real matrix tend to zero if some algebra norm of it is less than one**. Let
$N$ be an algebra norm on the real $n \times n$ matrices, and let $A$ be a real square matrix
with $N(A) < 1$. Then $A^k \to 0$. This is the convergence criterion for an arbitrary consistent
norm. -/
theorem tendsto_pow_of_algebraNorm_lt_one (N : AlgebraNorm ℝ (Matrix n n ℝ)) {A : Matrix n n ℝ}
    (h : N A < 1) : Tendsto (fun k => A ^ k) atTop (𝓝 0) :=
  (tendsto_pow_iff_complexSpectralRadius_lt_one A).mpr
    ((complexSpectralRadius_le_algebraNorm N A).trans_lt (ENNReal.ofReal_lt_one.mpr h))

end Matrix
