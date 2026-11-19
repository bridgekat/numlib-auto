/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Golub and Van Loan, Section 7.1: Properties and decompositions

This module formalizes §7.1 of [golub2013matrix], the basic theory of the unsymmetric eigenvalue
problem for $A \in \mathbb{C}^{n \times n}$. It defines the quantities attached to the spectrum
$\lambda(A)$: the spectral radius $\rho(A)$ (7.1.1), the spectral abscissa $\alpha(A)$ (7.1.2), the
numerical radius $r(A)$ (7.1.3) and the numerical range $W(A)$ (7.1.4). It treats invariant
subspaces (§7.1.1) and decoupling (Lemma 7.1.1). The unitary reductions are Lemma 7.1.2, the Schur
decomposition (Theorem 7.1.3) with any order of the eigenvalues on the diagonal, the Schur vectors
(7.1.8), normal matrices (Corollary 7.1.4) and the departure from normality. The nonunitary
reductions are the Sylvester map of Lemma 7.1.5, the block diagonal decomposition (Theorem 7.1.6),
Corollaries 7.1.7 and 7.1.8, and the Jordan decomposition (Theorem 7.1.9) with its uniqueness. The
module also proves that the diagonalizable matrices are dense (§7.1.5) and compares singular values
with eigenvalues (§7.1.6).

The decompositions specialize `Numlib.LinearAlgebra.Matrix.Schur`,
`Numlib.LinearAlgebra.Matrix.Jordan`, `Numlib.LinearAlgebra.Matrix.Similar`,
`Numlib.LinearAlgebra.Matrix.Sylvester` and `Numlib.Eigen.Normal`. The numerical range is
`Numlib.Eigen.NumericalRange`, which proves the Toeplitz–Hausdorff theorem, and the facts about
singular values come from `Numlib.LinearAlgebra.Matrix.SVD`.

## Main definitions

* Equation (7.1.1), `GolubVanLoan.Chapter07.spectralRadius`: $\rho(A) = \max_{\lambda \in
  \lambda(A)} |\lambda|$.
* Equation (7.1.2), `GolubVanLoan.Chapter07.spectralAbscissa`: $\alpha(A) = \max_{\lambda \in
  \lambda(A)} \operatorname{Re}(\lambda)$.
* Equation (7.1.4), `GolubVanLoan.Chapter07.numericalRange`: $W(A) = \{x^H A x : \|x\|_2 = 1\}$.
* Equation (7.1.3), `GolubVanLoan.Chapter07.numericalRadius`:
  $r(A) = \max\{|x^H A x| : \|x\|_2 = 1\}$.
* §7.1.3, `GolubVanLoan.Chapter07.departureFromNormality`: $\Delta(A) = (\|A\|_F^2 - \sum_i
  |\lambda_i|^2)^{1/2}$.
* §7.1.4, `GolubVanLoan.Chapter07.algebraicMultiplicity`: the multiplicity of $\lambda$ as a root of
  the characteristic polynomial.
* §7.1.4, `GolubVanLoan.Chapter07.geometricMultiplicity`: $\dim \operatorname{null}(A - \lambda I)$.
* §7.1.4, `GolubVanLoan.Chapter07.IsSimpleEigenvalue`: the algebraic multiplicity is $1$.
* §7.1.4, `GolubVanLoan.Chapter07.IsDefectiveEigenvalue`: the geometric multiplicity is less than
  the algebraic multiplicity.
* §7.1.4, `GolubVanLoan.Chapter07.IsDefective`: the matrix has a defective eigenvalue.

## Main results

* §7.1.1, `GolubVanLoan.Chapter07.det_eq_prod_eigenvalues`: $\det(A) = \lambda_1 \cdots \lambda_n$
  and $\operatorname{tr}(A) = \lambda_1 + \dots + \lambda_n$.
* §7.1.1, `GolubVanLoan.Chapter07.spectrum_subset_numericalRange`: $\lambda(A) \subseteq W(A)$.
* §7.1.1, `GolubVanLoan.Chapter07.convex_numericalRange`: $W(A)$ is convex.
* §7.1.1, `GolubVanLoan.Chapter07.spectrum_subset_of_mul_eq_mul`: if $AX = XB$, then
  $\operatorname{ran}(X)$ is invariant, and $\lambda(B) \subseteq \lambda(A)$ when $X$ has full
  column rank.
* Lemma 7.1.1, `GolubVanLoan.Chapter07.lemma_7_1_1`: $\lambda(T) = \lambda(T_{11}) \cup
  \lambda(T_{22})$ for a block upper triangular $T$.
* Lemma 7.1.2, `GolubVanLoan.Chapter07.lemma_7_1_2`: an invariant subspace gives a unitary reduction
  to block upper triangular form.
* Theorem 7.1.3, `GolubVanLoan.Chapter07.theorem_7_1_3`: the Schur decomposition $Q^H A Q = D + N$.
* Equation (7.1.8), `GolubVanLoan.Chapter07.equation_7_1_8`: the Schur vectors and the invariant
  subspaces they span.
* Corollary 7.1.4, `GolubVanLoan.Chapter07.corollary_7_1_4`: $A$ is normal if and only if it is
  unitarily diagonalizable.
* §7.1.3, `GolubVanLoan.Chapter07.departureFromNormality_eq`: $\|N\|_F = \Delta(A)$ for every Schur
  decomposition.
* Lemma 7.1.5, `GolubVanLoan.Chapter07.lemma_7_1_5`: the Sylvester map is nonsingular if and only if
  $\lambda(T_{11}) \cap \lambda(T_{22}) = \emptyset$.
* Lemma 7.1.5, `GolubVanLoan.Chapter07.lemma_7_1_5_blockDiagonal`: a solution of $\phi(Z) = -T_{12}$
  block-diagonalizes $T$.
* Theorem 7.1.6, `GolubVanLoan.Chapter07.theorem_7_1_6`: the block diagonal decomposition.
* Corollary 7.1.7, `GolubVanLoan.Chapter07.corollary_7_1_7`: $X^{-1} A X =
  \operatorname{diag}(\lambda_1 I + N_1, \dots, \lambda_q I + N_q)$.
* Corollary 7.1.8, `GolubVanLoan.Chapter07.corollary_7_1_8`: $A$ is nondefective if and only if it
  is diagonalizable.
* §7.1.4, `GolubVanLoan.Chapter07.corollary_7_1_7_multiplicity`: in Corollary 7.1.7, $n_i$ is the
  algebraic and $\dim \operatorname{null}(N_i)$ the geometric multiplicity of $\lambda_i$.
* Theorem 7.1.9, `GolubVanLoan.Chapter07.theorem_7_1_9`: the Jordan decomposition.
* Theorem 7.1.9, `GolubVanLoan.Chapter07.theorem_7_1_9_unique`: the number and the sizes of the
  Jordan blocks of each eigenvalue are unique.
* §7.1.5, `GolubVanLoan.Chapter07.dense_diagonalizable`: the diagonalizable matrices are dense in
  $\mathbb{C}^{n \times n}$.
* §7.1.6, `GolubVanLoan.Chapter07.sigmaMin_le_norm_eigenvalue`: $\sigma_{\min}(A) \le |\lambda| \le
  \sigma_{\max}(A)$ for every eigenvalue $\lambda$.
* Equation (7.1.13), `GolubVanLoan.Chapter07.equation_7_1_13`: the diagonalizing matrices of
  $[1 + \varepsilon\ 1; 0\ 1 - \varepsilon]$ have 2-norm condition of order $1/\varepsilon$.

## Conventions

* Matrices are complex, as in the source, and indices are 0-based: $A$ is
  `A : Matrix (Fin n) (Fin n) ℂ`.
* The spectrum $\lambda(A)$ is Mathlib's `spectrum ℂ A` in the algebra of matrices, which is the set
  of roots of `A.charpoly` (`Matrix.mem_spectrum_iff_isRoot_charpoly`). The eigenvalues
  $\lambda_1, \dots, \lambda_n$ counted with multiplicity are the multiset `A.charpoly.roots`.
* A unitary $Q$ is a member of `Matrix.unitaryGroup (Fin n) ℂ`, and $Q^H$ is `star Q`.
* A block partition $[T_{11}\ T_{12}; 0\ T_{22}]$ is `Matrix.fromBlocks` on `Fin p ⊕ Fin q`,
  reindexed by `finSumFinEquiv` where the source has a single $n \times n$ array.
* A matrix is strictly upper triangular when its entries on and below the diagonal vanish.
* The 2-norm is the scoped `Matrix.Norms.L2Operator` norm, and the Frobenius norm is the scoped
  `Matrix.Norms.Frobenius` norm; each is opened in its own section. The numbers $\sigma_{\min}(A)$
  and $\sigma_{\max}(A)$ are the infimum and the supremum of `Matrix.colSingularValues`.

## Deviations from the source

* **Equations (7.1.1)–(7.1.3)** (reading). The radius and abscissa use suprema and take value
  zero in dimension zero, where the maxima in the source are undefined. See
  `GolubVanLoan.Chapter07.spectralRadius`, `GolubVanLoan.Chapter07.spectralAbscissa` and
  `GolubVanLoan.Chapter07.numericalRadius`.
* **Lemma 7.1.1** (reading). The characteristic polynomial identity gives multiplicities and
  establishes spectral equality without the source's counting argument for sets. See
  `GolubVanLoan.Chapter07.lemma_7_1_1`.
* **Corollary 7.1.7** (reading). The block-size data permit empty blocks. Removing these gives
  the decomposition into eigenvalue blocks. See `GolubVanLoan.Chapter07.corollary_7_1_7`.
* **Equation (7.1.3)** (typo). The source prints the maximum as $\max_{\lambda \in \lambda(A)}$. The
  maximum is over the unit vectors $x$. See `GolubVanLoan.Chapter07.numericalRadius`.
* **Lemma 7.1.5, block diagonalization** (generalization). The source assumes that $\phi$ is
  nonsingular. The statement needs only a solution $Z$ of $\phi(Z) = -T_{12}$. See
  `GolubVanLoan.Chapter07.lemma_7_1_5_blockDiagonal`.
* **Theorem 7.1.6** (generalization). The theorem uses a block upper triangular form whose
  diagonal blocks can be arbitrary square matrices. The source assumes a Schur decomposition.
  See `GolubVanLoan.Chapter07.theorem_7_1_6`.
* **Equation (7.1.13)** (reading). The source says that the diagonalizing matrix has "a 2-norm
  condition of order $1/\varepsilon$". The statement gives the lower bound $1/(2\varepsilon)$ for
  every diagonalizing matrix and the upper bound $1/\varepsilon + 2\varepsilon$ for one of them. See
  `GolubVanLoan.Chapter07.equation_7_1_13`.

## Not formalized

* **The roundoff claims (7.1.14)–(7.1.15)**, $fl(X^{-1} A X) = X^{-1} A X + E$ with
  $\|E\|_2 \approx u\, \kappa_2(X) \|A\|_2$. They name no algorithm for forming $X^{-1} A X$, and
  they are approximate.
* **The remark that $\max |\lambda_i| / |\lambda_j| \ll \kappa_2(A)$ may occur.** It is an
  illustration. Its rigorous half, $|\lambda_i| / |\lambda_j| \le \kappa_2(A)$, is in
  `GolubVanLoan.Chapter07.sigmaMin_le_norm_eigenvalue`.
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.1.1 Eigenvalues and invariant subspaces -/

/-- **Section 7.1.1** of [golub2013matrix], determinant and trace. Let
$A \in \mathbb{C}^{n \times n}$ have the eigenvalues $\lambda_1, \dots, \lambda_n$, counted with
multiplicity. Then $$\det(A) = \lambda_1 \lambda_2 \cdots \lambda_n, \qquad
\operatorname{tr}(A) = \lambda_1 + \dots + \lambda_n.$$

The eigenvalues counted with multiplicity are the roots `A.charpoly.roots` of the characteristic
polynomial. -/
theorem det_eq_prod_eigenvalues (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = A.charpoly.roots.prod ∧ A.trace = A.charpoly.roots.sum :=
  ⟨A.det_eq_prod_roots_charpoly, A.trace_eq_sum_roots_charpoly⟩

/-- **Equation (7.1.1)** of [golub2013matrix]. The **spectral radius** of
$A \in \mathbb{C}^{n \times n}$ is $$\rho(A) = \max_{\lambda \in \lambda(A)} |\lambda|.$$

It is defined as the supremum of the moduli of the eigenvalues. For $n = 0$ the spectrum is
empty and the value is $0$; for $n \ge 1$ the spectrum is finite and nonempty, so the supremum
is a maximum. The agreement with Mathlib's `spectralRadius`, which takes values in `ℝ≥0∞`, is
`GolubVanLoan.Chapter07.spectralRadius_eq`.

**Reading.** Supremum of spectral moduli agrees for positive size, takes zero on empty spectrum.
-/
noncomputable def spectralRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup ((‖·‖) '' spectrum ℂ A)

/-- The spectral radius $\rho(A)$ of (7.1.1) is the real value of Mathlib's spectral radius of $A$
in the algebra of matrices. -/
theorem spectralRadius_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius A = (_root_.spectralRadius ℂ A).toReal := by
  have h : _root_.spectralRadius ℂ A = ⨆ k ∈ spectrum ℂ A, (‖k‖₊ : ENNReal) := by
    rw [_root_.spectralRadius, quasispectrum_eq_spectrum_union_zero, iSup_union]
    simp
  rw [h, iSup_subtype', ENNReal.toReal_iSup fun _ => ENNReal.coe_ne_top, spectralRadius,
    sSup_image']
  simp only [ENNReal.coe_toReal, coe_nnnorm]

/-- **Equation (7.1.2)** of [golub2013matrix]. The **spectral abscissa** of
$A \in \mathbb{C}^{n \times n}$ is $$\alpha(A) = \max_{\lambda \in \lambda(A)}
\operatorname{Re}(\lambda).$$

It is defined as a supremum, which is $0$ for $n = 0$ and is attained for $n \ge 1$
(`GolubVanLoan.Chapter07.spectralAbscissa_mem`). It equals the backbone's `spectralAbscissa` of
$A$ in the algebra of matrices (`GolubVanLoan.Chapter07.spectralAbscissa_eq`).

**Generalization.** Supremum of real components extends empty spectrum by zero.
-/
noncomputable def spectralAbscissa (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ A)

/-- The spectral abscissa $\alpha(A)$ of (7.1.2) is the backbone's `spectralAbscissa` of $A$ in the
algebra of matrices. -/
theorem spectralAbscissa_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralAbscissa A = _root_.spectralAbscissa A := rfl

/-- For $n \ge 1$, the spectral abscissa (7.1.2) is a maximum: some eigenvalue $\lambda$ of $A$ has
$\operatorname{Re}(\lambda) = \alpha(A)$. -/
theorem spectralAbscissa_mem [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ μ ∈ spectrum ℂ A, μ.re = spectralAbscissa A :=
  exists_mem_spectrum_re_eq_spectralAbscissa (Matrix.finite_spectrum A).isCompact
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)

/-- **Equation (7.1.4)** of [golub2013matrix]. The **numerical range**, or field of values, of
$A \in \mathbb{C}^{n \times n}$ is $$W(A) = \{x^H A x : x \in \mathbb{C}^n,\ \|x\|_2 = 1\}.$$

Its agreement with the backbone's numerical range of an operator, which is defined by the
Rayleigh quotients of nonzero vectors, is `GolubVanLoan.Chapter07.numericalRange_eq`. -/
def numericalRange (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : Fin n → ℂ, ‖WithLp.toLp 2 x‖ = 1 ∧ star x ⬝ᵥ (A *ᵥ x) = z}

/-- The quadratic form $x^H A x$ is the inner product $\langle x, Ax \rangle$ in $\mathbb{C}^n$. -/
private theorem star_dotProduct_mulVec_eq_inner (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      inner ℂ (WithLp.toLp 2 x) (toEuclideanLin A (WithLp.toLp 2 x)) := by
  simp only [toLpLin_toLp, EuclideanSpace.inner_toLp_toLp, toLin'_apply, dotProduct_comm]

/-- The numerical range (7.1.4) equals the backbone's numerical range of $A$ as an operator on
$\mathbb{C}^n$, $\{\langle x, Ax \rangle / \langle x, x \rangle : x \neq 0\}$.

The proof normalizes $x$. The backbone set is `LinearMap.numericalRange (toEuclideanLin A)`. -/
theorem numericalRange_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A = LinearMap.numericalRange (toEuclideanLin A) := by
  ext z
  rw [LinearMap.mem_numericalRange]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, fun h => by simp [h] at hx, ?_⟩
    rw [inner_self_eq_norm_sq_to_K, hx, star_dotProduct_mulVec_eq_inner]
    simp
  · rintro ⟨y, hy, rfl⟩
    have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    refine ⟨WithLp.ofLp ((‖y‖⁻¹ : ℂ) • y), ?_, ?_⟩
    · rw [WithLp.toLp_ofLp, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ hy0]
    · rw [star_dotProduct_mulVec_eq_inner, WithLp.toLp_ofLp, map_smul, inner_smul_left,
        inner_smul_right, inner_self_eq_norm_sq_to_K]
      have : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hy0
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
      exact (mul_div_cancel_left₀ _ (pow_ne_zero 2 this)).symm

/-- **Equation (7.1.3)** of [golub2013matrix]. The **numerical radius** of
$A \in \mathbb{C}^{n \times n}$ is $$r(A) = \max\{|x^H A x| : \|x\|_2 = 1\},$$ the supremum of
the moduli of the numerical range $W(A)$.

**Typo.** The source prints the maximum as $\max_{\lambda \in \lambda(A)}$. The maximum is over
the unit vectors $x$.

For $n = 0$ the numerical range is empty and the value is $0$. -/
noncomputable def numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup ((‖·‖) '' numericalRange A)

/-- **Section 7.1.1** of [golub2013matrix]: the numerical range "obviously includes $\lambda(A)$".
For $A \in \mathbb{C}^{n \times n}$, $$\lambda(A) \subseteq W(A).$$

A unit eigenvector $x$ for $\lambda$ gives $x^H A x = \lambda$. -/
theorem spectrum_subset_numericalRange (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro μ hμ
  rw [numericalRange_eq, LinearMap.mem_numericalRange]
  obtain ⟨x, hx0, hx⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1 hμ
  refine ⟨WithLp.toLp 2 x, by simpa using hx0, ?_⟩
  have hne : (inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 x) : ℂ) ≠ 0 :=
    inner_self_ne_zero.2 (by simpa using hx0)
  rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul, inner_smul_right, mul_div_assoc,
    div_self hne, mul_one]

/-- **Section 7.1.1** of [golub2013matrix] (Toeplitz–Hausdorff theorem): "It can be shown that
$W(A)$ is convex." For $A \in \mathbb{C}^{n \times n}$, the numerical range $W(A)$ is a convex
subset of $\mathbb{C}$. -/
theorem convex_numericalRange (A : Matrix (Fin n) (Fin n) ℂ) : Convex ℝ (numericalRange A) := by
  rw [numericalRange_eq]
  exact LinearMap.convex_numericalRange _

/-- If $X \in \mathbb{C}^{m \times k}$ has rank $k$ and $Xy = 0$, then $y = 0$. -/
private theorem eq_zero_of_mulVec_eq_zero {m k : ℕ} {X : Matrix (Fin m) (Fin k) ℂ}
    (hX : X.rank = k) {y : Fin k → ℂ} (hy : X *ᵥ y = 0) : y = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [← Matrix.rank, hX, Module.finrank_fin_fun, add_eq_left,
    Submodule.finrank_eq_zero] at h
  have hmem : y ∈ LinearMap.ker X.mulVecLin := by simpa using hy
  rw [h] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

/-- **Section 7.1.1** of [golub2013matrix], invariant subspaces. Let
$A \in \mathbb{C}^{n \times n}$, $X \in \mathbb{C}^{n \times k}$ and
$B \in \mathbb{C}^{k \times k}$ satisfy $AX = XB$. Then:

* $\operatorname{ran}(X)$ is invariant for $A$;
* if $By = \lambda y$, then $A(Xy) = \lambda (Xy)$;
* if $X$ has full column rank $k$, then $\lambda(B) \subseteq \lambda(A)$;
* for every nonsingular $Y \in \mathbb{C}^{n \times n}$, $\lambda(Y^{-1} A Y) = \lambda(A)$, so
  a similarity preserves the spectrum.

The last part does not use $AX = XB$. The range is that of `Matrix.toLin' X`. -/
theorem spectrum_subset_of_mul_eq_mul {k : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin n) (Fin k) ℂ} {B : Matrix (Fin k) (Fin k) ℂ} (h : A * X = X * B) :
    LinearMap.range (toLin' X) ∈ Module.End.invtSubmodule (toLin' A) ∧
      (∀ (y : Fin k → ℂ) (μ : ℂ), B *ᵥ y = μ • y → A *ᵥ (X *ᵥ y) = μ • (X *ᵥ y)) ∧
      (X.rank = k → spectrum ℂ B ⊆ spectrum ℂ A) ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y → spectrum ℂ (Y⁻¹ * A * Y) = spectrum ℂ A := by
  have hb : ∀ (y : Fin k → ℂ) (μ : ℂ), B *ᵥ y = μ • y → A *ᵥ (X *ᵥ y) = μ • (X *ᵥ y) :=
    fun y μ hy => by rw [mulVec_mulVec, h, ← mulVec_mulVec, hy, mulVec_smul]
  refine ⟨?_, hb, fun hX μ hμ => ?_, fun Y hY => ?_⟩
  · rw [Module.End.mem_invtSubmodule]
    rintro _ ⟨y, rfl⟩
    refine ⟨B *ᵥ y, ?_⟩
    simp only [toLin'_apply]
    rw [mulVec_mulVec, ← h, ← mulVec_mulVec]
  · obtain ⟨y, hy0, hy⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul B μ).1 hμ
    exact (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).2
      ⟨X *ᵥ y, fun h0 => hy0 (eq_zero_of_mulVec_eq_zero hX h0), hb y μ hy⟩
  · exact (IsSimilar.spectrum_eq ⟨Y, hY, rfl⟩).symm

/-! ### §7.1.2 Decoupling -/

/-- **Lemma 7.1.1** of [golub2013matrix]. Let $T_{11} \in \mathbb{C}^{p \times p}$,
$T_{12} \in \mathbb{C}^{p \times q}$ and $T_{22} \in \mathbb{C}^{q \times q}$. If $$T =
\begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix},$$ then $\lambda(T) =
\lambda(T_{11}) \cup \lambda(T_{22})$. With multiplicity, the characteristic polynomial of $T$
is the product of the characteristic polynomials of $T_{11}$ and $T_{22}$.

**Reading.** The source appeals to equal cardinalities of spectral sets to prove the reverse
inclusion. The Lean proof uses the characteristic polynomial product, which establishes the
set equality and also gives the algebraic multiplicities. -/
theorem lemma_7_1_1 {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ) (T₁₂ : Matrix (Fin p) (Fin q) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    spectrum ℂ (fromBlocks T₁₁ T₁₂ 0 T₂₂) = spectrum ℂ T₁₁ ∪ spectrum ℂ T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂).charpoly = T₁₁.charpoly * T₂₂.charpoly := by
  have hc := Matrix.charpoly_fromBlocks_zero₂₁ T₁₁ T₁₂ T₂₂
  refine ⟨?_, hc⟩
  ext μ
  simp only [Set.mem_union, Matrix.mem_spectrum_iff_isRoot_charpoly, hc, Polynomial.IsRoot.def,
    Polynomial.eval_mul, mul_eq_zero]

/-! ### §7.1.3 Basic unitary decompositions -/

/-- **Lemma 7.1.2** of [golub2013matrix]. Let $A \in \mathbb{C}^{(p+q) \times (p+q)}$,
$B \in \mathbb{C}^{p \times p}$ and $X \in \mathbb{C}^{(p+q) \times p}$ satisfy $$AX = XB,
\qquad \operatorname{rank}(X) = p \qquad (7.1.5).$$ Then there is a unitary
$Q \in \mathbb{C}^{(p+q) \times (p+q)}$ such that $$Q^H A Q = T = \begin{bmatrix} T_{11} &
T_{12} \\ 0 & T_{22} \end{bmatrix} \qquad (7.1.6)$$ with $T_{11} \in \mathbb{C}^{p \times p}$,
and $\lambda(T_{11}) = \lambda(A) \cap \lambda(B)$.

The block form is `Matrix.fromBlocks` after reindexing by `finSumFinEquiv`. -/
theorem lemma_7_1_2 {p q : ℕ} {A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    {B : Matrix (Fin p) (Fin p) ℂ} {X : Matrix (Fin (p + q)) (Fin p) ℂ} (hAX : A * X = X * B)
    (hX : X.rank = p) :
    ∃ Q ∈ unitaryGroup (Fin (p + q)) ℂ, ∃ (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
      (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ),
      (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
        fromBlocks T₁₁ T₁₂ 0 T₂₂ ∧ spectrum ℂ T₁₁ = spectrum ℂ A ∩ spectrum ℂ B := by
  obtain ⟨Q, hQ, T₁₁, T₁₂, T₂₂, hT, hsim⟩ := exists_unitary_conj_fromBlocks_of_mul_eq_mul hAX hX
  refine ⟨Q, hQ, T₁₁, T₁₂, T₂₂, hT, ?_⟩
  rw [← IsSimilar.spectrum_eq hsim,
    Set.inter_eq_right.2 ((spectrum_subset_of_mul_eq_mul hAX).2.2.1 hX)]

/-- **Theorem 7.1.3** of [golub2013matrix] (Schur decomposition). If
$A \in \mathbb{C}^{n \times n}$, then there is a unitary $Q \in \mathbb{C}^{n \times n}$ such
that $$Q^H A Q = T = D + N \qquad (7.1.7),$$ where $D = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$ lists the eigenvalues of $A$ with multiplicity and $N$ is strictly upper triangular.
Furthermore, $Q$ can be chosen so that the eigenvalues appear in any prescribed order along the
diagonal: for every list $\mu_1, \dots, \mu_n$ of the eigenvalues with multiplicity, there is a
unitary $Q$ such that $Q^H A Q$ is upper triangular with the diagonal $\mu_1, \dots, \mu_n$.

"The diagonal lists the eigenvalues with multiplicity" is stated as
`A.charpoly = ∏ i, (X - C (d i))`. -/
theorem theorem_7_1_3 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ (d : Fin n → ℂ) (N : Matrix (Fin n) (Fin n) ℂ),
      (∀ i j, j ≤ i → N i j = 0) ∧ star Q * A * Q = diagonal d + N ∧
        A.charpoly = ∏ i, (X - C (d i))) ∧
    ∀ μ : Fin n → ℂ, A.charpoly = ∏ i, (X - C (μ i)) →
      ∃ Q ∈ unitaryGroup (Fin n) ℂ, (star Q * A * Q).IsUpperTriangular ∧
        ∀ i, (star Q * A * Q) i i = μ i := by
  refine ⟨?_, fun μ hμ => exists_unitary_conj_upperTriangular_diag_eq A μ hμ⟩
  obtain ⟨Q, hQ, hT, hchar⟩ := exists_unitary_conj_upperTriangular A
  set T := star Q * A * Q
  refine ⟨Q, hQ, fun i => T i i, T - diagonal fun i => T i i, fun i j hji => ?_, by abel,
    hchar⟩
  rcases hji.lt_or_eq with hlt | rfl
  · simp [Matrix.sub_apply, hT hlt, diagonal_apply_ne _ hlt.ne']
  · simp

/-- If $Q$ is unitary and $T = Q^H A Q$, then $AQ = QT$. -/
private theorem mul_eq_mul_conj {Q A : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) : A * Q = Q * (star Q * A * Q) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ, Matrix.one_mul]

/-- **Equation (7.1.8)** of [golub2013matrix] and the paragraph after it, the Schur vectors. Let
$Q^H A Q = T$ be upper triangular with $Q = [q_1 \mid \dots \mid q_n]$ unitary. Then:

* $A q_k = t_{kk} q_k + \sum_{i=1}^{k-1} t_{ik} q_i$ for each $k$ (7.1.8);
* each subspace $S_k = \operatorname{span}\{q_1, \dots, q_k\}$ is invariant for $A$;
* for $k \le n$ and $Q_k = [q_1 \mid \dots \mid q_k]$, $\lambda(Q_k^H A Q_k) = \{t_{11}, \dots,
  t_{kk}\}$;
* $q_k$ is an eigenvector of $A$ if and only if $t_{ik} = 0$ for all $i < k$, that is, column
  $k$ of the strictly upper triangular part of $T$ vanishes.

The columns are 0-based in the Lean statement: $q_k$ is `Q.col (k - 1)`. -/
theorem equation_7_1_8 {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Q).IsUpperTriangular) :
    (∀ k, A *ᵥ Q.col k = (star Q * A * Q) k k • Q.col k +
      ∑ i ∈ Finset.Iio k, (star Q * A * Q) i k • Q.col i) ∧
    (∀ k, Submodule.span ℂ (Q.col '' Set.Iic k) ∈ Module.End.invtSubmodule (toLin' A)) ∧
    (∀ (k : ℕ) (hk : k ≤ n),
      spectrum ℂ ((Q.submatrix id (Fin.castLE hk))ᴴ * A * Q.submatrix id (Fin.castLE hk)) =
        Set.range fun i : Fin k => (star Q * A * Q) (Fin.castLE hk i) (Fin.castLE hk i)) ∧
    ∀ k, (∃ μ : ℂ, A *ᵥ Q.col k = μ • Q.col k) ↔ ∀ i < k, (star Q * A * Q) i k = 0 := by
  set T := star Q * A * Q with hTdef
  have hAQ : A * Q = Q * T := mul_eq_mul_conj hQ
  have hcol : ∀ k, Q.col k = Q *ᵥ Pi.single k 1 := fun k => by
    rw [mulVec_single_one]
  -- `A q_k = Q (T e_k)`
  have hAq : ∀ k, A *ᵥ Q.col k = Q *ᵥ T.col k := fun k => by
    rw [hcol, mulVec_mulVec, hAQ, ← mulVec_mulVec, mulVec_single_one]
  -- (a)
  have ha : ∀ k, A *ᵥ Q.col k = T k k • Q.col k + ∑ i ∈ Finset.Iio k, T i k • Q.col i := by
    intro k
    rw [hAq]
    ext r
    simp only [mulVec, dotProduct, col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic k)) fun i _ hi => by
      simp only [Finset.mem_Iic, not_le] at hi; rw [hT hi, mul_zero],
      ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp only [mul_comm]
  refine ⟨ha, fun k => ?_, fun k hk => ?_, fun k => ?_⟩
  · -- (b)
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [Submodule.mem_comap, toLin'_apply, SetLike.mem_coe]
    rw [ha j]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩))
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨i, ?_, rfl⟩))
    exact le_trans (Finset.mem_Iio.1 hi).le hj
  · -- (c)
    have hsub : (Q.submatrix id (Fin.castLE hk))ᴴ * A * Q.submatrix id (Fin.castLE hk) =
        T.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      rw [conjTranspose_submatrix, hTdef, star_eq_conjTranspose,
        submatrix_mul _ _ _ id _ Function.bijective_id,
        submatrix_mul _ _ _ id _ Function.bijective_id]
      rfl
    rw [hsub, Matrix.IsUpperTriangular.spectrum_eq]
    · rfl
    · intro i j hij
      have hij' : (j : ℕ) < i := hij
      exact hT (show Fin.castLE hk j < Fin.castLE hk i from Fin.lt_def.2 (by simpa using hij'))
  · -- (d)
    have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
    constructor
    · rintro ⟨μ, hμ⟩ i hi
      have h1 : T.col k = μ • Pi.single k 1 := by
        have h := congrArg (star Q *ᵥ ·) hμ
        rw [hAq, mulVec_mulVec, hQQ, one_mulVec, hcol, mulVec_smul, mulVec_mulVec, hQQ,
          one_mulVec] at h
        exact h
      have h2 := congrFun h1 i
      simpa [col_apply, Pi.single_apply, hi.ne] using h2
    · intro h
      refine ⟨T k k, ?_⟩
      rw [hAq, hcol, ← mulVec_smul]
      congr 1
      ext i
      rcases lt_trichotomy i k with hi | rfl | hi
      · simp [col_apply, h i hi, hi.ne]
      · simp [col_apply]
      · simp [col_apply, hT hi, hi.ne']

/-- **Corollary 7.1.4** of [golub2013matrix]. A matrix $A \in \mathbb{C}^{n \times n}$ is normal,
$A^H A = AA^H$, if and only if there is a unitary $Q \in \mathbb{C}^{n \times n}$ with $$Q^H A
Q = \operatorname{diag}(\lambda_1, \dots, \lambda_n).$$

Normality is `IsStarNormal A`. -/
theorem corollary_7_1_4 (A : Matrix (Fin n) (Fin n) ℂ) :
    IsStarNormal A ↔ ∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ,
      star Q * A * Q = diagonal d := by
  rw [IsStarNormal.spectral_theorem]
  simp only [star_eq_conjTranspose]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 7.1.3** of [golub2013matrix], the **departure from normality** of
$A \in \mathbb{C}^{n \times n}$: $$\Delta(A) = \Big(\|A\|_F^2 - \sum_{i=1}^n
|\lambda_i|^2\Big)^{1/2},$$ where the eigenvalues $\lambda_i$ are counted with multiplicity.

The difference under the root is nonnegative by
`GolubVanLoan.Chapter07.departureFromNormality_eq`. -/
noncomputable def departureFromNormality (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  √(‖A‖ ^ 2 - (A.charpoly.roots.map fun z => ‖z‖ ^ 2).sum)

/-- **Section 7.1.3** of [golub2013matrix]: $\|N\|_F$ does not depend on the Schur decomposition. If
$Q^H A Q = \operatorname{diag}(d) + N$ with $Q$ unitary and $N$ strictly upper triangular, then
$$\|N\|_F^2 = \|A\|_F^2 - \sum_{i=1}^n |d_i|^2 = \Delta(A)^2.$$
-/
theorem departureFromNormality_eq {A Q N : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hN : ∀ i j, j ≤ i → N i j = 0)
    (h : star Q * A * Q = diagonal d + N) :
    ‖N‖ ^ 2 = ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 ∧
      ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 = departureFromNormality A ^ 2 := by
  have hnorm : ‖star Q * A * Q‖ = ‖A‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) A hQ
  have hsplit : ‖diagonal d + N‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 + ‖N‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ‖N i j‖ ^ 2) (Finset.mem_univ i), hN i i le_rfl]
    have hoff : ∀ j ∈ Finset.univ.erase i, ‖(diagonal d + N) i j‖ ^ 2 = ‖N i j‖ ^ 2 :=
      fun j hj => by
        have hij : i ≠ j := fun e => by simp [e] at hj
        simp [diagonal_apply_ne _ hij]
    rw [Finset.sum_congr rfl hoff]
    simp [hN i i le_rfl]
  have h1 : ‖N‖ ^ 2 = ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 := by
    rw [← hnorm, h, hsplit]; ring
  refine ⟨h1, ?_⟩
  -- the diagonal lists the eigenvalues
  have hsim : IsSimilar A (star Q * A * Q) := by
    refine ⟨Q, (Matrix.isUnit_iff_isUnit_det Q).2
      (Matrix.isUnit_det_of_right_inverse (mem_unitaryGroup_iff.1 hQ)), ?_⟩
    rw [Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)]
  have hup : (diagonal d + N).IsUpperTriangular := fun i j hij => by
    have hij' : j < i := hij
    rw [Matrix.add_apply, diagonal_apply_ne d (ne_of_gt hij'), hN i j hij'.le, add_zero]
  have hdiag : ∀ i, (diagonal d + N) i i = d i := fun i => by simp [hN i i le_rfl]
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [hsim.charpoly_eq, h, charpoly_of_isUpperTriangular _ hup]
    simp only [hdiag]
    rw [show (∏ i, (X - C (d i))) = ((Finset.univ.val.map d).map fun a => X - C a).prod by
      rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hsum : ((Finset.univ.val.map d).map fun z => ‖z‖ ^ 2).sum = ∑ i, ‖d i‖ ^ 2 := by
    rw [Multiset.map_map]; rfl
  rw [departureFromNormality, hroots, hsum, Real.sq_sqrt (by rw [← h1]; positivity)]

end Frobenius

/-! ### §7.1.4 Nonunitary reductions -/

/-- **Lemma 7.1.5** of [golub2013matrix], first part. Let $T_{11} \in \mathbb{C}^{p \times p}$ and
$T_{22} \in \mathbb{C}^{q \times q}$. The Sylvester map $\phi : \mathbb{C}^{p \times q} \to
\mathbb{C}^{p \times q}$, $$\phi(X) = T_{11} X - X T_{22},$$ is nonsingular if and only if
$\lambda(T_{11}) \cap \lambda(T_{22}) = \emptyset$.

The source proves that a singular $\phi$ gives a common eigenvalue by an SVD argument; the
backbone uses the characteristic polynomial instead. The map is `Matrix.sylvesterMap`, and
nonsingular means bijective. -/
theorem lemma_7_1_5 {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    Function.Bijective (sylvesterMap T₁₁ T₂₂) ↔ spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅ := by
  rw [sylvesterMap_bijective_iff_disjoint_spectrum, Set.disjoint_iff_inter_eq_empty]

/-- The inverse of the block unit upper triangular matrix $[I\ Z; 0\ I]$ is $[I\ {-Z}; 0\ I]$. -/
private theorem inv_fromBlocks_one {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)⁻¹ = fromBlocks 1 (-Z) 0 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [fromBlocks_multiply]
  simp [fromBlocks_one]

/-- **Lemma 7.1.5** of [golub2013matrix], block diagonalization. Let $$T = \begin{bmatrix} T_{11} &
T_{12} \\ 0 & T_{22} \end{bmatrix}$$ with $T_{11} \in \mathbb{C}^{p \times p}$ and
$T_{22} \in \mathbb{C}^{q \times q}$. If $Z \in \mathbb{C}^{p \times q}$ satisfies
$\phi(Z) = T_{11} Z - Z T_{22} = -T_{12}$ and $Y = [I\ Z; 0\ I]$, then $$Y^{-1} T Y =
\operatorname{diag}(T_{11}, T_{22}).$$

**Generalization.** The source assumes that $\phi$ is nonsingular. That assumption only
guarantees that such a $Z$ exists; the statement needs only the existence of $Z$. -/
theorem lemma_7_1_5_blockDiagonal {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) {Z : Matrix (Fin p) (Fin q) ℂ}
    (hZ : sylvesterMap T₁₁ T₂₂ Z = -T₁₂) :
    (fromBlocks 1 Z 0 1)⁻¹ * fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks 1 Z 0 1 =
      fromBlocks T₁₁ 0 0 T₂₂ := by
  rw [inv_fromBlocks_one, fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one]
  rw [sylvesterMap_apply] at hZ
  rw [hZ, neg_add_cancel]

/-- **Theorem 7.1.6** of [golub2013matrix] (block diagonal decomposition). Let $Q^H A Q = T$ with
$Q \in \mathbb{C}^{n \times n}$ unitary and $T$ block upper triangular, with square diagonal
blocks $T_{11}, \dots, T_{qq}$ (7.1.9). If $\lambda(T_{ii}) \cap \lambda(T_{jj}) = \emptyset$
whenever $i \neq j$, then there is a nonsingular $Y \in \mathbb{C}^{n \times n}$ such that
$$(QY)^{-1} A (QY) = \operatorname{diag}(T_{11}, \dots, T_{qq}) \qquad (7.1.10).$$

**Generalization.** Only block upper triangularity and disjoint spectra of the diagonal blocks
are needed. The source assumes a Schur decomposition and states the same diagonal-block
separation in the original PDF. The OCR incorrectly renders $T_{ii}$ as $T_{ij}$.

The blocks are given by a block index `b : Fin n → Fin q`: $T$ is `Matrix.BlockTriangular b`,
the block $T_{ii}$ is `Matrix.toSquareBlock b i`, and
$\operatorname{diag}(T_{11}, \dots, T_{qq})$ is the matrix that keeps the entries $t_{kl}$ with
`b k = b l` and is zero elsewhere. -/
theorem theorem_7_1_6 {q : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    {b : Fin n → Fin q} (hT : (star Q * A * Q).BlockTriangular b)
    (hdisj : ∀ i j, i ≠ j → spectrum ℂ ((star Q * A * Q).toSquareBlock b i) ∩
      spectrum ℂ ((star Q * A * Q).toSquareBlock b j) = ∅) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y ∧
      (Q * Y)⁻¹ * A * (Q * Y) = of fun i j => if b i = b j then (star Q * A * Q) i j else 0 := by
  obtain ⟨Y, hY, hYT⟩ := exists_isUnit_conj_eq_blockDiagonalPart hT fun i j hij =>
    Set.disjoint_iff_inter_eq_empty.2 (hdisj i j hij)
  rw [blockDiagPart] at hYT
  refine ⟨Y, hY, ?_⟩
  rw [← hYT, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)]
  simp only [Matrix.mul_assoc]

/-- Reindexing each block of a block diagonal matrix by an equivalence of its index type reindexes
the block diagonal matrix. -/
private theorem blockDiagonal'_submatrix_sigmaCongrRight {q : ℕ} {κ κ' : Fin q → Type*}
    (M : ∀ i, Matrix (κ' i) (κ' i) ℂ) (f : ∀ i, κ i ≃ κ' i) :
    (blockDiagonal' M).submatrix (Equiv.sigmaCongrRight f) (Equiv.sigmaCongrRight f) =
      blockDiagonal' fun i => (M i).submatrix (f i) (f i) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  rcases eq_or_ne a b with rfl | hab
  · simp only [submatrix_apply, Equiv.sigmaCongrRight_apply, blockDiagonal'_apply_eq]
  · simp only [submatrix_apply, Equiv.sigmaCongrRight_apply, blockDiagonal'_apply_ne _ _ _ hab]

/-- **Corollary 7.1.7** of [golub2013matrix]. If $A \in \mathbb{C}^{n \times n}$, then there is a
nonsingular $X \in \mathbb{C}^{n \times n}$ such that $$X^{-1} A X =
\operatorname{diag}(\lambda_1 I + N_1, \dots, \lambda_q I + N_q) \qquad (7.1.11),$$ where
$\lambda_1, \dots, \lambda_q$ are distinct, each $N_i \in \mathbb{C}^{n_i \times n_i}$ is
strictly upper triangular, and $n_1 + \dots + n_q = n$.

The blocks are laid out along `Fin n` by an equivalence `σ`. The proof reads off the Jordan form
grouped by eigenvalue (`Matrix.exists_conj_blockDiagonal'_jordanForm`), whose block for
$\lambda_i$ is $\lambda_i I$ plus a direct sum of nilpotent Jordan blocks. This route is shorter
than the proof in the source, which applies Theorem 7.1.6 to an ordered Schur form.

**Reading.** The existence theorem uses natural-number block sizes and permits empty blocks.
These can be removed to obtain the source's partition into blocks associated with eigenvalues. -/
theorem corollary_7_1_7 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (q : ℕ) (μ : Fin q → ℂ) (sz : Fin q → ℕ) (N : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℂ)
      (σ : ((i : Fin q) × Fin (sz i)) ≃ Fin n) (X : Matrix (Fin n) (Fin n) ℂ),
      Function.Injective μ ∧ ∑ i, sz i = n ∧ (∀ i a b, b ≤ a → N i a b = 0) ∧ IsUnit X ∧
        X⁻¹ * A * X = reindex σ σ (blockDiagonal' fun i => μ i • (1 : Matrix _ _ ℂ) + N i) := by
  obtain ⟨q, ν, d, e, σ, P, hinj, -, -, hP, hPA⟩ := exists_conj_blockDiagonal'_jordanForm A
  let f : ∀ i : Fin q, ((j : Fin (d i)) × Fin (e i j)) ≃ Fin (∑ j, e i j) :=
    fun _ => finSigmaFinEquiv
  let N : ∀ i : Fin q, Matrix (Fin (∑ j, e i j)) (Fin (∑ j, e i j)) ℂ :=
    fun i => reindex (f i) (f i) (jordanForm (e i) fun _ => (0 : ℂ))
  let τ := Equiv.sigmaCongrRight f
  refine ⟨q, ν, fun i => ∑ j, e i j, N, τ.symm.trans σ, P, hinj, ?_, ?_, hP, ?_⟩
  · have h := Fintype.card_congr (τ.symm.trans σ)
    simpa [Fintype.card_sigma] using h
  · intro i a b hba
    obtain ⟨⟨j, x⟩, rfl⟩ := (f i).surjective a
    obtain ⟨⟨j', y⟩, rfl⟩ := (f i).surjective b
    simp only [N, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, jordanForm_def]
    rcases eq_or_ne j j' with rfl | hjj
    · rw [blockDiagonal'_apply_eq, jordanBlock_zero_apply]
      split_ifs with hxy
      · exfalso
        rw [Fin.le_def] at hba
        simp only [f, finSigmaFinEquiv_apply] at hba
        omega
      · rfl
    · exact blockDiagonal'_apply_ne _ _ _ hjj
  · have hblk : (blockDiagonal' fun i => ν i • (1 : Matrix _ _ ℂ) + N i).submatrix τ τ =
        blockDiagonal' fun i => jordanForm (e i) fun _ => ν i := by
      rw [blockDiagonal'_submatrix_sigmaCongrRight]
      congr 1
      funext i
      rw [jordanForm_const_eq_add_smul_one, add_comm]
      ext a b
      simp [N, reindex_apply, Matrix.add_apply, Matrix.one_apply]
    rw [hPA, ← hblk]
    ext a b
    simp [reindex_apply, τ]

/-- **Section 7.1.4** of [golub2013matrix], definition of the **algebraic multiplicity**: the
algebraic multiplicity of $\lambda$ as an eigenvalue of $A \in \mathbb{C}^{n \times n}$ is its
multiplicity as a root of the characteristic polynomial of $A$.

The related notions are `GolubVanLoan.Chapter07.geometricMultiplicity`,
`GolubVanLoan.Chapter07.IsSimpleEigenvalue`, `GolubVanLoan.Chapter07.IsDefectiveEigenvalue` and
`GolubVanLoan.Chapter07.IsDefective`. The value is $0$ when $\lambda$ is not an eigenvalue. -/
noncomputable def algebraicMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : ℕ :=
  A.charpoly.rootMultiplicity μ

/-- **Section 7.1.4** of [golub2013matrix], definition of the **geometric multiplicity**: the number
of independent eigenvectors of $A \in \mathbb{C}^{n \times n}$ for $\lambda$, that is,
$\dim \operatorname{null}(A - \lambda I)$. -/
noncomputable def geometricMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ)

/-- **Section 7.1.4** of [golub2013matrix], definition: $\lambda$ is a **simple** eigenvalue of $A$
if its algebraic multiplicity is $1$. -/
def IsSimpleEigenvalue (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : Prop :=
  algebraicMultiplicity A μ = 1

/-- **Section 7.1.4** of [golub2013matrix], definition: $\lambda$ is a **defective** eigenvalue of
$A$ if its algebraic multiplicity exceeds its geometric multiplicity. -/
def IsDefectiveEigenvalue (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : Prop :=
  geometricMultiplicity A μ < algebraicMultiplicity A μ

/-- **Section 7.1.4** of [golub2013matrix], definition: a matrix is **defective** if it has a
defective eigenvalue. Nondefective matrices are called diagonalizable (Corollary 7.1.8). -/
def IsDefective (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ μ, IsDefectiveEigenvalue A μ

/-- **Corollary 7.1.8** of [golub2013matrix] (diagonal form). A matrix
$A \in \mathbb{C}^{n \times n}$ is nondefective if and only if there is a nonsingular
$X \in \mathbb{C}^{n \times n}$ such that $$X^{-1} A X = \operatorname{diag}(\lambda_1, \dots,
\lambda_n) \qquad (7.1.12).$$ In that case, the columns $x_i$ of $X$ are right eigenvectors,
$A x_i = \lambda_i x_i$, and the rows $y_i^T$ of $X^{-1}$ are left eigenvectors,
$y_i^T A = \lambda_i y_i^T$. -/
theorem corollary_7_1_8 (A : Matrix (Fin n) (Fin n) ℂ) :
    (¬ IsDefective A ↔ ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ,
      X⁻¹ * A * X = diagonal d) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ), IsUnit X → X⁻¹ * A * X = diagonal d →
      ∀ i, A *ᵥ X.col i = d i • X.col i ∧ X⁻¹.row i ᵥ* A = d i • X⁻¹.row i := by
  refine ⟨?_, fun X d hX hXA i => ?_⟩
  · have hle : ∀ μ, geometricMultiplicity A μ ≤ algebraicMultiplicity A μ := fun μ =>
      finrank_eigenspace_le_rootMultiplicity_charpoly A μ
    have hiff : ¬ IsDefective A ↔ ∀ μ, geometricMultiplicity A μ = algebraicMultiplicity A μ := by
      simp only [IsDefective, IsDefectiveEigenvalue, not_exists, not_lt]
      exact forall_congr' fun μ => ⟨fun h => le_antisymm (hle μ) h, fun h => h.ge⟩
    rw [hiff]
    unfold geometricMultiplicity algebraicMultiplicity
    rw [← isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity]
    constructor
    · rintro ⟨d, X, hX, hXA⟩
      exact ⟨X, hX, d, hXA.symm⟩
    · rintro ⟨X, hX, d, hXA⟩
      exact ⟨d, X, hX, hXA.symm⟩
  · have hXX : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X ((isUnit_iff_isUnit_det X).1 hX)
    have hXX' : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X ((isUnit_iff_isUnit_det X).1 hX)
    have hAX : A * X = X * diagonal d := by
      rw [← hXA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.one_mul]
    have hXA' : X⁻¹ * A = diagonal d * X⁻¹ := by
      rw [← hXA, Matrix.mul_assoc _ X, hXX, Matrix.mul_one]
    constructor
    · have h : A *ᵥ (X *ᵥ Pi.single i 1) = X *ᵥ (diagonal d *ᵥ Pi.single i 1) := by
        rw [mulVec_mulVec, mulVec_mulVec, hAX]
      rw [diagonal_mulVec_single, mul_one, mulVec_single_one, mulVec_single,
        op_smul_eq_smul] at h
      exact h
    · have h : Pi.single i 1 ᵥ* (X⁻¹ * A) = Pi.single i 1 ᵥ* (diagonal d * X⁻¹) := by
        rw [hXA']
      rw [← vecMul_vecMul, ← vecMul_vecMul, single_one_vecMul, single_vecMul_diagonal, one_mul,
        single_vecMul] at h
      exact h

/-- **Section 7.1.4** of [golub2013matrix], the terms attached to (7.1.11). Let $X^{-1} A X =
\operatorname{diag}(\lambda_1 I + N_1, \dots, \lambda_q I + N_q)$ be a decomposition as in
Corollary 7.1.7, with $X$ nonsingular, $\lambda_1, \dots, \lambda_q$ distinct and each
$N_i \in \mathbb{C}^{n_i \times n_i}$ strictly upper triangular. Then for each $i$, the
algebraic multiplicity of $\lambda_i$ is $n_i$, and its geometric multiplicity is
$\dim \operatorname{null}(N_i)$.

The proof uses that the blocks $(\lambda_j - \lambda_i) I + N_j$ for $j \neq i$ are nonsingular. -/
theorem corollary_7_1_7_multiplicity {A X : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} {μ : Fin q → ℂ}
    {sz : Fin q → ℕ} {N : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℂ}
    {σ : ((i : Fin q) × Fin (sz i)) ≃ Fin n} (hμ : Function.Injective μ)
    (hN : ∀ i a b, b ≤ a → N i a b = 0) (hX : IsUnit X)
    (h : X⁻¹ * A * X = reindex σ σ (blockDiagonal' fun i => μ i • (1 : Matrix _ _ ℂ) + N i))
    (i : Fin q) :
    algebraicMultiplicity A (μ i) = sz i ∧
      geometricMultiplicity A (μ i) = Module.finrank ℂ (LinearMap.ker (N i).mulVecLin) := by
  have hsim : IsSimilar A (X⁻¹ * A * X) := ⟨X, hX, rfl⟩
  have hup : ∀ j (c : ℂ),
      (c • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j).IsUpperTriangular :=
    fun j c a b hab => by
    have hab' : b < a := hab
    rw [Matrix.add_apply, Matrix.smul_apply, one_apply_ne (ne_of_gt hab'), smul_zero,
      hN j a b hab'.le, add_zero]
  have hdiag : ∀ j (c : ℂ) a, (c • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j) a a = c :=
    fun j c a => by simp [hN j a a le_rfl]
  constructor
  · have hchar : A.charpoly = ∏ j, (Polynomial.X - C (μ j)) ^ sz j := by
      rw [hsim.charpoly_eq, h, charpoly_reindex, charpoly_blockDiagonal']
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [charpoly_of_isUpperTriangular _ (hup j (μ j))]
      simp [hdiag]
    have hne : ∀ j : Fin q, ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]) ≠ 0 := fun j =>
      pow_ne_zero _ (X_sub_C_ne_zero _)
    unfold algebraicMultiplicity
    rw [hchar, ← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j _ => hne j),
      show (Finset.univ.val.bind fun j => ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]).roots)
        = ∑ j, ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]).roots from rfl,
      Multiset.count_sum', Finset.sum_eq_single i]
    · rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
    · intro j _ hji
      rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton]
      have hne' : μ i ≠ μ j := fun h' => hji (hμ h').symm
      simp [hne']
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · unfold geometricMultiplicity
    rw [eigenspace_mulVecLin_eq_ker, (hsim.sub_smul_one (μ i)).finrank_ker_mulVecLin_eq, h]
    have hsub : reindex σ σ (blockDiagonal' fun j => μ j • (1 : Matrix _ _ ℂ) + N j) - μ i • 1 =
        reindex σ σ (blockDiagonal' fun j => μ j • (1 : Matrix _ _ ℂ) + N j - μ i • 1) := by
      rw [← blockDiagonal'_sub_smul_one]
      ext a b
      simp [reindex_apply, Matrix.sub_apply, Matrix.one_apply]
    rw [hsub, finrank_ker_mulVecLin_reindex, finrank_ker_mulVecLin_blockDiagonal',
      Finset.sum_eq_single i]
    · rw [add_sub_cancel_left]
    · intro j _ hji
      have heq : μ j • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j - μ i • 1 =
          (μ j - μ i) • 1 + N j := by
        rw [sub_smul]; abel
      rw [heq]
      have hdet : ((μ j - μ i) • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j).det ≠ 0 := by
        rw [det_of_isUpperTriangular (hup j _)]
        simp only [hdiag]
        exact Finset.prod_ne_zero_iff.2 fun _ _ => sub_ne_zero.2 (hμ.ne hji)
      have hu : IsUnit ((μ j - μ i) • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j) :=
        (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      rw [LinearMap.ker_eq_bot.2 (mulVec_injective_iff_isUnit.2 hu), finrank_bot]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-- **Theorem 7.1.9** of [golub2013matrix] (Jordan decomposition). If
$A \in \mathbb{C}^{n \times n}$, then there is a nonsingular $X \in \mathbb{C}^{n \times n}$
such that $$X^{-1} A X = \operatorname{diag}(J_1, \dots, J_q),$$ where
$J_i \in \mathbb{C}^{n_i \times n_i}$ is the Jordan block of size $n_i \ge 1$ for an eigenvalue
$\lambda_i$, with $\lambda_i$ on the diagonal and $1$ on the superdiagonal, and
$n_1 + \dots + n_q = n$.

The blocks are laid out consecutively along the diagonal. The Jordan form is
`Matrix.jordanForm`. -/
theorem theorem_7_1_9 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (q : ℕ) (e : Fin q → ℕ) (μ : Fin q → ℂ) (he : ∑ i, e i = n)
      (X : Matrix (Fin n) (Fin n) ℂ), (∀ i, 0 < e i) ∧ IsUnit X ∧
        X⁻¹ * A * X = reindex (finSigmaFinEquiv.trans (finCongr he))
          (finSigmaFinEquiv.trans (finCongr he)) (jordanForm e μ) :=
  exists_conj_jordanForm A

/-- **Theorem 7.1.9** of [golub2013matrix], the uniqueness remark: "The number and dimensions of the
Jordan blocks associated with each distinct eigenvalue are unique." Let $X^{-1} A X$ and
$X'^{-1} A X'$ be two Jordan forms of $A \in \mathbb{C}^{n \times n}$, with blocks of positive
size laid out along the diagonal in any order. Then for every $c \in \mathbb{C}$ and every $k$,
the two forms have the same number of Jordan blocks of size $k$ for the eigenvalue $c$. -/
theorem theorem_7_1_9_unique {A : Matrix (Fin n) (Fin n) ℂ} {q q' : ℕ} {e : Fin q → ℕ}
    {μ : Fin q → ℂ} {e' : Fin q' → ℕ} {μ' : Fin q' → ℂ} (he : ∀ i, 0 < e i)
    (he' : ∀ i, 0 < e' i) (σ : ((i : Fin q) × Fin (e i)) ≃ Fin n)
    (σ' : ((i : Fin q') × Fin (e' i)) ≃ Fin n) {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (hX' : IsUnit X') (h : X⁻¹ * A * X = reindex σ σ (jordanForm e μ))
    (h' : X'⁻¹ * A * X' = reindex σ' σ' (jordanForm e' μ')) (c : ℂ) (k : ℕ) :
    (Finset.univ.filter fun i => μ i = c ∧ e i = k).card =
      (Finset.univ.filter fun i => μ' i = c ∧ e' i = k).card :=
  card_jordanBlocks_eq_of_isSimilar he he' σ σ' ⟨X, hX, h.symm⟩ ⟨X', hX', h'.symm⟩ c k

/-! ### §7.1.5 Some comments on nonunitary similarity -/

/-- If the characteristic polynomial of $A$ is $\prod_i (x - d_i)$ with distinct $d_i$, then $A$ is
diagonalizable. -/
private theorem exists_diagonal_of_charpoly_eq_prod {A : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℂ} (hd : Function.Injective d)
    (h : A.charpoly = ∏ i, (Polynomial.X - C (d i))) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d' : Fin n → ℂ, X⁻¹ * A * X = diagonal d' := by
  refine (corollary_7_1_8 A).1.1 ?_
  rintro ⟨μ, hμ⟩
  unfold IsDefectiveEigenvalue at hμ
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [h, show (∏ i, (Polynomial.X - C (d i))) =
      ((Finset.univ.val.map d).map fun a => Polynomial.X - C a).prod by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hle : algebraicMultiplicity A μ ≤ 1 := by
    unfold algebraicMultiplicity
    rw [← count_roots, hroots]
    exact Multiset.nodup_iff_count_le_one.1 (Finset.univ.nodup.map hd) μ
  have hpos : 0 < algebraicMultiplicity A μ := lt_of_le_of_lt (Nat.zero_le _) hμ
  have hroot : A.charpoly.IsRoot μ := (rootMultiplicity_pos A.charpoly_monic.ne_zero).1 hpos
  obtain ⟨v, hv0, hv⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1
    (Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot)
  have hgeo : geometricMultiplicity A μ = 0 := by omega
  unfold geometricMultiplicity at hgeo
  have hmem : v ∈ Module.End.eigenspace A.mulVecLin μ := by
    rw [Module.End.mem_eigenspace_iff]; exact hv
  rw [Submodule.finrank_eq_zero.1 hgeo, Submodule.mem_bot] at hmem
  exact hv0 hmem

/-- **Section 7.1.5** of [golub2013matrix]: "The set of $n$-by-$n$ diagonalizable matrices is dense
in $\mathbb{C}^{n \times n}$." The set of $A \in \mathbb{C}^{n \times n}$ with $X^{-1} A X$
diagonal for some nonsingular $X$ is dense.

The source refers to Problem P7.1.5 for the proof. From a Schur form $Q^H A Q = T$, the matrices
$Q (T + t \operatorname{diag}(0, 1, \dots, n - 1)) Q^H$ tend to $A$ as $t \to 0$, and for all
but finitely many $t$ their eigenvalues, the diagonal entries of the triangular matrix, are
distinct. -/
theorem dense_diagonalizable :
    Dense {A : Matrix (Fin n) (Fin n) ℂ |
      ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ, X⁻¹ * A * X = diagonal d} := by
  intro A
  obtain ⟨Q, hQ, hT, -⟩ := exists_unitary_conj_upperTriangular A
  set T := star Q * A * Q
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => ((i : ℕ) : ℂ)
  set F : ℂ → Matrix (Fin n) (Fin n) ℂ := fun t => Q * (T + t • D) * star Q
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hF0 : F 0 = A := by
    simp only [F, T, zero_smul, add_zero, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hcont : Continuous F :=
    (continuous_const.matrix_mul
      (continuous_const.add (continuous_id.smul continuous_const))).matrix_mul continuous_const
  -- the finitely many shifts for which two diagonal entries coincide
  set bad : Set ℂ :=
    Set.range fun p : Fin n × Fin n => (T p.2 p.2 - T p.1 p.1) / ((p.1 : ℕ) - (p.2 : ℕ) : ℂ)
  have hgood : ∀ t, t ∉ bad → F t ∈ {A : Matrix (Fin n) (Fin n) ℂ |
      ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ, X⁻¹ * A * X = diagonal d} := by
    intro t ht
    have hup : (T + t • D).IsUpperTriangular := fun i j hij => by
      have hij' : j < i := hij
      simp [D, hT hij, diagonal_apply_ne _ (ne_of_gt hij')]
    have hinj : Function.Injective fun i => (T + t • D) i i := by
      intro i j hij
      by_contra hne
      apply ht
      refine ⟨(i, j), ?_⟩
      simp only [D, Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul] at hij
      have hsub : ((i : ℕ) : ℂ) - (j : ℕ) ≠ 0 := by
        rw [sub_ne_zero, Ne, Nat.cast_inj]
        exact fun h' => hne (Fin.ext h')
      rw [div_eq_iff hsub]
      linear_combination -hij
    have hsim : IsSimilar (F t) (T + t • D) := by
      refine ⟨Q, (Matrix.isUnit_iff_isUnit_det _).2
        (Matrix.isUnit_det_of_right_inverse hQQ), ?_⟩
      rw [Matrix.inv_eq_left_inv hQQ']
      simp only [F, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
    exact exists_diagonal_of_charpoly_eq_prod hinj
      (by rw [hsim.charpoly_eq, charpoly_of_isUpperTriangular _ hup])
  have hbad : bad.Finite := Set.finite_range _
  have hev : ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, t ∉ bad := by
    have h1 : (bad \ {0})ᶜ ∈ nhds (0 : ℂ) :=
      (hbad.subset Set.sdiff_subset).isClosed.compl_mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
    exact fun hb => ht ⟨hb, ht0⟩
  have hlim : Filter.Tendsto F (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds A) :=
    hF0 ▸ (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim (hev.mono hgood)

/-! ### §7.1.6 Singular values and eigenvalues -/

section L2

open scoped Matrix.Norms.L2Operator

/-- **Section 7.1.6** of [golub2013matrix], singular values and eigenvalues. Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$. Then $$\sigma_{\min}(A) \le |\lambda| \le
\sigma_{\max}(A) = \|A\|_2$$ for every eigenvalue $\lambda$ of $A$. If moreover $A$ is
nonsingular, then $|\lambda_i| / |\lambda_j| \le \kappa_2(A)$ for all eigenvalues $\lambda_i$
and $\lambda_j$.

The last part is the rigorous half of the remark in the source that
$\max |\lambda_i| / |\lambda_j| \ll \kappa_2(A)$ may occur. The numbers $\sigma_{\min}(A)$ and
$\sigma_{\max}(A)$ are the infimum and the supremum of `Matrix.colSingularValues`, and
$\kappa_2(A)$ is `NormedRing.condNumber A` for the 2-norm. -/
theorem sigmaMin_le_norm_eigenvalue [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ μ ∈ spectrum ℂ A, (⨅ i, A.colSingularValues i) ≤ ‖μ‖ ∧ ‖μ‖ ≤ ⨆ i, A.colSingularValues i) ∧
    ‖A‖ = ⨆ i, A.colSingularValues i ∧
    (IsUnit A → ∀ μ ∈ spectrum ℂ A, ∀ ν ∈ spectrum ℂ A,
      ‖μ‖ / ‖ν‖ ≤ NormedRing.condNumber A) := by
  have hbound : ∀ μ ∈ spectrum ℂ A,
      (⨅ i, A.colSingularValues i) ≤ ‖μ‖ ∧ ‖μ‖ ≤ ⨆ i, A.colSingularValues i := by
    intro μ hμ
    obtain ⟨x, hx0, hx⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1 hμ
    set y : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
    have hy0 : ‖y‖ ≠ 0 := by simpa [y] using hx0
    have hAy : ‖toEuclideanLin A y‖ = ‖μ‖ * ‖y‖ := by
      rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul, norm_smul]
    have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    constructor
    · have h := A.iInf_colSingularValues_mul_norm_le y
      rw [hAy] at h
      exact le_of_mul_le_mul_right h hpos
    · have h := A.norm_toEuclideanLin_le_iSup_colSingularValues y
      rw [hAy] at h
      exact le_of_mul_le_mul_right h hpos
  refine ⟨hbound, l2_opNorm_eq_iSup_colSingularValues A, fun hA μ hμ ν hν => ?_⟩
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  -- `σ_min > 0`: otherwise `‖A⁻¹‖ = 0`
  have hmin : 0 < ⨅ i, A.colSingularValues i := by
    refine lt_of_le_of_ne (le_ciInf fun i => A.colSingularValues_nonneg i) fun h0 => ?_
    have hinv := l2_opNorm_inv_eq_inv_iInf_colSingularValues A hdet
    rw [← h0, _root_.inv_zero, norm_eq_zero] at hinv
    have h1 := Matrix.mul_nonsing_inv A hdet
    rw [hinv, Matrix.mul_zero] at h1
    exact zero_ne_one h1
  rw [condNumber_l2_eq_div_colSingularValues A hdet]
  exact div_le_div₀ ((norm_nonneg μ).trans (hbound μ hμ).2) (hbound μ hμ).2 hmin
    (hbound ν hν).1

/-- Every entry of a matrix is bounded in modulus by its 2-norm. -/
private theorem norm_entry_le_lpOpNorm_two {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) (i : Fin m)
    (j : Fin k) : ‖M i j‖ ≤ lpOpNorm 2 M := by
  rw [lpOpNorm_two]
  exact norm_entry_le_l2_opNorm M i j

end L2

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The 2-norm of a matrix is at most its Frobenius norm $\big(\sum_{i,j} |m_{ij}|^2\big)^{1/2}$. -/
private theorem lpOpNorm_two_le_sqrt {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    lpOpNorm 2 M ≤ √(∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]
  exact l2_opNorm_le_frobenius_norm M

end Frobenius

/-- **Equation (7.1.13)** of [golub2013matrix]. Let $\varepsilon > 0$ and $$A = \begin{bmatrix} 1 +
\varepsilon & 1 \\ 0 & 1 - \varepsilon \end{bmatrix}.$$ Then every nonsingular $X$ with
$X^{-1} A X$ diagonal has $\kappa_2(X) \ge 1/(2\varepsilon)$, and some nonsingular $X$ with
$X^{-1} A X$ diagonal has $\kappa_2(X) \le 1/\varepsilon + 2\varepsilon$.

**Reading.** The source says that the diagonalizing matrix has "a 2-norm condition of order
$1/\varepsilon$". The two bounds are the rigorous form of this claim.

If $X^{-1} A X$ is diagonal, the column $x$ of $X$ and the row $y^H$ of $X^{-1}$ for the
eigenvalue $1 + \varepsilon$ are right and left eigenvectors with $y^H x = 1$. The eigenvector
equations force $x = (x_1, 0)$ and $y_1 = 2\varepsilon y_2$, so $2\varepsilon x_1 y_2 = 1$. The
condition number $\kappa_2(X) = \|X\|_2 \|X^{-1}\|_2$ is `Matrix.condNumberLp 2 X`. -/
theorem equation_7_1_13 {ε : ℝ} (hε : 0 < ε) :
    (∀ (X : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ), IsUnit X →
      X⁻¹ * !![1 + (ε : ℂ), 1; 0, 1 - ε] * X = diagonal d → 1 / (2 * ε) ≤ condNumberLp 2 X) ∧
    ∃ X : Matrix (Fin 2) (Fin 2) ℂ, IsUnit X ∧
      (∃ d : Fin 2 → ℂ, X⁻¹ * !![1 + (ε : ℂ), 1; 0, 1 - ε] * X = diagonal d) ∧
      condNumberLp 2 X ≤ 1 / ε + 2 * ε := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![1 + (ε : ℂ), 1; 0, 1 - ε] with hA
  constructor
  · intro X d hX h
    have hdet : IsUnit X.det := (isUnit_iff_isUnit_det X).1 hX
    -- `1 + ε` is an eigenvalue, hence a diagonal entry of `X⁻¹ A X`
    have hmem : (1 + ε : ℂ) ∈ spectrum ℂ A := by
      refine (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A _).2 ⟨![1, 0], ?_, ?_⟩
      · intro h0
        have := congrFun h0 0
        simp at this
      · ext i
        fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
    rw [IsSimilar.spectrum_eq ⟨X, hX, rfl⟩, h, spectrum_diagonal] at hmem
    obtain ⟨k, hk⟩ := hmem
    obtain ⟨hcol, hrow⟩ := (corollary_7_1_8 A).2 X d hX h k
    rw [hk] at hcol hrow
    have h1 : (1 - (ε : ℂ)) * X 1 k = (1 + ε) * X 1 k := by
      have := congrFun hcol 1
      simpa [A, mulVec, dotProduct, Fin.sum_univ_two] using this
    have h2 : X⁻¹ k 0 + X⁻¹ k 1 * (1 - ε) = (1 + ε) * X⁻¹ k 1 := by
      have := congrFun hrow 1
      simpa [A, vecMul, dotProduct, Fin.sum_univ_two, mul_comm] using this
    have h3 : X⁻¹ k 0 * X 0 k + X⁻¹ k 1 * X 1 k = 1 := by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul X hdet) k) k
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have hx : X 1 k = 0 := by
      have h4 : (2 * ε : ℂ) * X 1 k = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd h5 (mul_ne_zero two_ne_zero hε')
      · exact h5
    have h5 : (2 * ε : ℂ) * (X⁻¹ k 1 * X 0 k) = 1 := by
      rw [hx, mul_zero, add_zero] at h3
      linear_combination h3 - X 0 k * h2
    have h6 : ‖X 0 k‖ * ‖X⁻¹ k 1‖ = 1 / (2 * ε) := by
      have h7 := congrArg norm h5
      rw [norm_mul, norm_mul, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le,
        Complex.norm_two] at h7
      field_simp
      linarith
    rw [← h6, condNumberLp]
    exact mul_le_mul (norm_entry_le_lpOpNorm_two X 0 k) (norm_entry_le_lpOpNorm_two X⁻¹ k 1)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_entry_le_lpOpNorm_two X 0 k))
  · set X : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, -(2 * ε : ℂ)] with hXdef
    set Y : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1 / (2 * ε : ℂ); 0, -(1 / (2 * ε : ℂ))] with hYdef
    have hYX : Y * X = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
      · simpa [X, Y, Matrix.mul_apply, Fin.sum_univ_two] using
          (show (1 : ℂ) * 1 + 1 / (2 * ε) * -(2 * ε) = 0 by field_simp; ring)
      · simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
      · simpa [X, Y, Matrix.mul_apply, Fin.sum_univ_two] using
          (show (0 : ℂ) * 1 + -(1 / (2 * ε)) * -(2 * ε) = 1 by field_simp; ring)
    have hinv : X⁻¹ = Y := Matrix.inv_eq_left_inv hYX
    have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 (isUnit_det_of_left_inverse hYX)
    refine ⟨X, hXu, ⟨![1 + ε, 1 - ε], ?_⟩, ?_⟩
    · have hAX : A * X = X * diagonal ![1 + (ε : ℂ), 1 - ε] := by
        ext i j
        fin_cases i <;> fin_cases j
        · simp [X, A, Matrix.mul_apply, Fin.sum_univ_two]
        · simpa [X, A, Matrix.mul_apply, Fin.sum_univ_two] using
            (show (1 + ε : ℂ) * 1 + 1 * -(2 * ε) = 1 * (1 - ε) by ring)
        · simp [X, A, Matrix.mul_apply, Fin.sum_univ_two]
        · simpa [X, A, Matrix.mul_apply, Fin.sum_univ_two] using
            (show (0 : ℂ) * 1 + (1 - ε) * -(2 * ε) = -(2 * ε) * (1 - ε) by ring)
      rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul X ((isUnit_iff_isUnit_det X).1 hXu), Matrix.one_mul]
    · have hXn : lpOpNorm 2 X ≤ √(2 + 4 * ε ^ 2) :=
        (lpOpNorm_two_le_sqrt X).trans_eq (by
          congr 1
          simp [X, Fin.sum_univ_two, mul_pow]
          ring)
      have hYn : lpOpNorm 2 Y ≤ √(1 + 1 / (2 * ε ^ 2)) :=
        (lpOpNorm_two_le_sqrt Y).trans_eq (by
          congr 1
          simp [Y, Fin.sum_univ_two, mul_pow]
          field_simp
          ring)
      rw [condNumberLp, hinv]
      calc lpOpNorm 2 X * lpOpNorm 2 Y ≤ √(2 + 4 * ε ^ 2) * √(1 + 1 / (2 * ε ^ 2)) :=
            mul_le_mul hXn hYn (lpOpNorm_nonneg 2 Y) (Real.sqrt_nonneg _)
        _ = 1 / ε + 2 * ε := by
          rw [← Real.sqrt_mul (by positivity),
            show (2 + 4 * ε ^ 2) * (1 + 1 / (2 * ε ^ 2)) = (1 / ε + 2 * ε) ^ 2 by
              field_simp
              ring,
            Real.sqrt_sq (by positivity)]

end GolubVanLoan.Chapter07
