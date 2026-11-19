/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.Circulant
import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.Direct.FastPoisson
import Numlib.FloatingPoint.Program
import NumlibSurface.GolubVanLoan.Chapter01.Section04

/-!
# Golub and Van Loan, Section 4.8: Circulant and discrete Poisson systems

This module formalizes §4.8 of [golub2013matrix], on linear systems that a fast transform
diagonalizes. If $V^{-1} A V = \Lambda$ is diagonal, then $Au = b$ has the solution
$u = V(\Lambda^{-1}(V^{-1} b))$ (4.8.2). The DFT matrix $F_n$ satisfies
$F_n^{-1} = \frac{1}{n} \bar F_n$, and it diagonalizes every circulant matrix $C(z)$: $F_n^{-1} C(z)
F_n = \operatorname{diag}(\bar F_n z)$ (Theorem 4.8.2). Algorithm 4.8.1 uses this to solve
$C(z) x = y$ with three FFTs. The discretized Poisson equation in one dimension gives the
second-difference matrices $\mathcal{T}^{(DD)}_n$, $\mathcal{T}^{(DN)}_n$, $\mathcal{T}^{(NN)}_n$
and $\mathcal{T}^{(P)}_n$ ((4.8.6)–(4.8.10)). In two dimensions it gives the system $(I_{n_2}
\otimes A_1 + A_2 \otimes I_{n_1}) u = b$, which is equivalent to the matrix equation
$A_1 U + U A_2^T = B$ (4.8.12), and which Algorithm 4.8.2 solves when $A_1$ and $A_2$ have fast
eigenvalue decompositions.

The module also proves the inverses of the DST and DCT matrices (§4.8.5), the action of the
second-difference matrices on the sine and cosine vectors (Lemma 4.8.3), the four fast eigenvalue
decompositions of §4.8.6 by $\mathrm{DST}(n)$, $\mathrm{DST2}(n)$, $\mathrm{DCT}(n)$ and $F_n$
((4.8.22)–(4.8.25)), and the symmetrization of $\mathcal{T}^{(DN)}_n$ (§4.8.7). The proofs
specialize the backbone modules `Numlib.Analysis.Fourier.DFT`, `Numlib.Analysis.Fourier.Circulant`
and `Numlib.Analysis.Fourier.SineCosineTransform` (the DFT, circulant, DST and DCT facts and the
four eigensystems), `Numlib.LinearAlgebra.Matrix.Permutation`,
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, `Numlib.LinearAlgebra.Matrix.KroneckerSum`, and
`Numlib.Direct.FastPoisson` (the solution formula of the fast Poisson framework).

## Main definitions

* Algorithm 4.8.1, `GolubVanLoan.Chapter04.algorithm_4_8_1`: the solution of a circulant system
  $C(z) x = y$ with three FFTs.
* §4.8.4, `GolubVanLoan.Chapter04.fivePointRhs`: the right-hand side of the five-point system.
* Algorithm 4.8.2, `GolubVanLoan.Chapter04.algorithm_4_8_2`: the fast Poisson solver framework.
* §4.8.5, `GolubVanLoan.Chapter04.altSignVecReal`: the alternating vector
  $v = (-1, 1, \dots, (-1)^{m-1})^T$.
* `GolubVanLoan.Chapter04.transformCols`: a vector program applied to every column of a matrix, for
  the transforms of Algorithm 4.8.2.

## Main results

* Equation (4.8.2), `GolubVanLoan.Chapter04.equation_4_8_2`: if
  $V^{-1} A V = \operatorname{diag}(\nu)$ with $V$ nonsingular, then $A^{-1} b = V
  (\operatorname{diag}(\nu)^{-1} (V^{-1} b))$.
* §4.8.1, `GolubVanLoan.Chapter04.map_star_fourierMatrix`,
  `GolubVanLoan.Chapter04.dft_conjTranspose`, `GolubVanLoan.Chapter04.dft_conjTranspose_mul_self`,
  `GolubVanLoan.Chapter04.dft_inv` and `GolubVanLoan.Chapter04.isUnit_fourierMatrix`:
  $F_n^H = \bar F_n$, $F_n^H F_n = \bar F_n F_n = n I_n$, and $F_n$ is nonsingular with
  $F_n^{-1} = \frac{1}{n} \bar F_n$ for $n \ge 1$.
* Equation (4.8.3), `GolubVanLoan.Chapter04.equation_4_8_3`:
  $C(z) = \sum_{k=0}^{n-1} z_k \mathcal{D}_n^k$ and $\mathcal{D}_n^n = I_n$.
* Equation (4.8.4), `GolubVanLoan.Chapter04.equation_4_8_4`: if $V^{-1} \mathcal{D}_n V$ is
  diagonal, then so is $V^{-1} C(z) V$.
* Lemma 4.8.1, `GolubVanLoan.Chapter04.lemma_4_8_1`: $F_n^{-1} \mathcal{D}_n F_n =
  \operatorname{diag}(1, \bar\omega_n, \dots, \bar\omega_n^{n-1})$.
* Theorem 4.8.2, `GolubVanLoan.Chapter04.theorem_4_8_2`: $F_n^{-1} C(z) F_n =
  \operatorname{diag}(\bar F_n z)$.
* Algorithm 4.8.1, `GolubVanLoan.Chapter04.algorithm_4_8_1_spec` and
  `GolubVanLoan.Chapter04.algorithm_4_8_1_fft_spec`: in exact arithmetic, the algorithm solves
  $C(z) x = y$ when $C(z)$ is nonsingular, with any FFT and with Algorithm 1.4.1 for $n = 2^t$.
* Equation (4.8.6), `GolubVanLoan.Chapter04.equation_4_8_6`: the three-point discretization of
  $-u'' = f$ with Dirichlet boundary values is the system $\mathcal{T}^{(DD)}_{m-1} u(1{:}m-1) = h^2
  f(1{:}m-1) + u_\alpha e_1 + u_\beta e_{m-1}$.
* Equations (4.8.8)–(4.8.10), `GolubVanLoan.Chapter04.equation_4_8_8`,
  `GolubVanLoan.Chapter04.equation_4_8_9` and `GolubVanLoan.Chapter04.equation_4_8_10`:
  $\mathcal{T}^{(DN)}_n$, $\mathcal{T}^{(NN)}_n$ and $\mathcal{T}^{(P)}_n$ are
  $\mathcal{T}^{(DD)}_n$ minus one or two matrices $e_p e_q^T$.
* §4.8.4, `GolubVanLoan.Chapter04.one_kronecker_add_kronecker_one`:
  $I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ is the Kronecker sum of $A_2$ and $A_1$.
* §4.8.4, `GolubVanLoan.Chapter04.poisson2D_eq_kroneckerSum`: the five-point equations at the
  interior grid points are the system $(I_{m_2-1} \otimes \mathcal{T}^{(DD)}_{m_1-1} +
  \mathcal{T}^{(DD)}_{m_2-1} \otimes I_{m_1-1}) u = b$.
* Equation (4.8.12), `GolubVanLoan.Chapter04.equation_4_8_12`: $(I_{n_2} \otimes A_1 + A_2 \otimes
  I_{n_1}) \operatorname{vec}(U) = \operatorname{vec}(B)$ if and only if $A_1 U + U A_2^T = B$.
* §4.8.4, `GolubVanLoan.Chapter04.fastPoisson_transformed` and
  `GolubVanLoan.Chapter04.add_ne_zero_of_isUnit_kroneckerSum`: the transformed system
  $D_1 \tilde U + \tilde U D_2 = \tilde B$ and its solution $\tilde u_{ij} = \tilde b_{ij} /
  (\lambda_i + \mu_j)$, and $\lambda_i + \mu_j \neq 0$ when the system matrix is nonsingular.
* Algorithm 4.8.2, `GolubVanLoan.Chapter04.algorithm_4_8_2_spec`: in exact arithmetic, the algorithm
  solves $(I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}) u = b$.
* §4.8.4, `GolubVanLoan.Chapter04.poisson2D_posDef_bandwidth`: the two-dimensional Dirichlet matrix
  is symmetric positive definite with lower and upper bandwidth $n_1$.
* §4.8.5, `GolubVanLoan.Chapter04.dst_inv` and `GolubVanLoan.Chapter04.dct_inv`:
  $\mathrm{DST}(m-1)^{-1} = \frac{2}{m} \mathrm{DST}(m-1)$ and $\mathrm{DCT}(m+1)^{-1} = \frac{2}{m}
  \mathrm{DCT}(m+1)$.
* §4.8.5, `GolubVanLoan.Chapter04.dst_block_identities`: the block identities of
  $\bar F_{2m} F_{2m} = 2m I$, with $2 S_{m-1}^2 = m I$ and $2 C_{m-1}^2 = m I - e e^T - v v^T$.
* Lemma 4.8.3, `GolubVanLoan.Chapter04.lemma_4_8_3`, with its parts (4.8.16)–(4.8.21),
  `GolubVanLoan.Chapter04.equation_4_8_16` to `GolubVanLoan.Chapter04.equation_4_8_21`: each
  second-difference matrix maps $s(\theta)$ or $c(\theta)$ to $4 \sin^2(\theta/2)$ times itself plus
  multiples of $e_1$ and $e_n$.
* §4.8.6, `GolubVanLoan.Chapter04.dd_eigen`, `GolubVanLoan.Chapter04.dn_eigen`,
  `GolubVanLoan.Chapter04.nn_eigen` and `GolubVanLoan.Chapter04.periodic_eigen`: the eigenvalue
  decompositions of $\mathcal{T}^{(DD)}_n$, $\mathcal{T}^{(DN)}_n$, $\mathcal{T}^{(NN)}_n$ and
  $\mathcal{T}^{(P)}_n$ by $\mathrm{DST}(n)$, $\mathrm{DST2}(n)$, a scaled $\mathrm{DCT}(n)$ and
  $F_n$.
* Equation (4.8.22), `GolubVanLoan.Chapter04.equation_4_8_22`: the eigenvalues of
  $\mathcal{T}^{(P)}_n$ satisfy $\lambda_j = \lambda_{n+2-j}$.
* Equation (4.8.23), `GolubVanLoan.Chapter04.equation_4_8_23`: $\bar F_n(:, j) = F_n(:, n+2-j)$.
* Equations (4.8.24)–(4.8.25), `GolubVanLoan.Chapter04.equation_4_8_25`: the real matrix $V^{(P)}_n$
  built from the real and imaginary parts of the columns of $F_n$ has eigenvectors of
  $\mathcal{T}^{(P)}_n$ as columns.
* §4.8.7, `GolubVanLoan.Chapter04.dn_symmetrizable`: $D^{-1} \mathcal{T}^{(DN)}_n D$ is symmetric
  for $D = \operatorname{diag}(I_{n-1}, \sqrt{2})$.

## Conventions

* The DFT matrix $F_n$, with entries $\omega_n^{kj}$ and $\omega_n = e^{-2\pi i/n}$, is
  `GolubVanLoan.Chapter01.fourierMatrix n`, which is `(Matrix.dft n)ᴴ`. Its entrywise conjugate
  $\bar F_n$ is `(fourierMatrix n).map star`, which equals `Matrix.dft n`
  (`GolubVanLoan.Chapter04.map_star_fourierMatrix`).
* The circulant matrix $C(z)$ with first column $z$ is Mathlib's `Matrix.circulant z`, and the
  downshift $\mathcal{D}_n$ is `Matrix.downshift n`.
* The second-difference matrices $\mathcal{T}^{(DD)}_n$, $\mathcal{T}^{(DN)}_n$,
  $\mathcal{T}^{(NN)}_n$ and $\mathcal{T}^{(P)}_n$ are, in this order,
  `Matrix.symmTridiagonalToeplitz n (-1) 2`, `Matrix.secondDifferenceDN n`,
  `Matrix.secondDifferenceNN n` and `Matrix.secondDifferencePeriodic n`.
* The vectors $s(\theta)$ and $c(\theta)$ of (4.8.15) are `Matrix.sinAngleVec n θ` and
  `Matrix.cosAngleVec n θ`. The unit vectors $e_1$ and $e_n$ are `Pi.single ⟨0, _⟩ 1` and
  `Pi.single ⟨n - 1, _⟩ 1`.
* The source's transforms $\mathrm{DST}(n)$, $\mathrm{DST2}(n)$ and $\mathrm{DCT}(m+1)$ are, in
  this order, `Matrix.dst1 n`, `Matrix.dst2 n` and `Matrix.dct1 m`.
* The source's eigenvalue letter $\lambda$ is a Lean keyword, so diagonals are named `ν`, `μ` and
  `Λ`.
* Indices are 0-based: the source's $\lambda_{j+1}$ is entry `j`.
* $\operatorname{reshape}(u, n_1, n_2)$ is Mathlib's column-major `Matrix.vec` read backwards:
  $u = \operatorname{vec}(U)$ with `U : Matrix (Fin n₁) (Fin n₂) ℝ`, and $u$ is indexed by
  `Fin n₂ × Fin n₁`.
* The source's $I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ is written literally,
  `1 ⊗ₖ A₁ + A₂ ⊗ₖ 1`. It is the Kronecker sum `A₂ ⊕ₖ A₁` of the backbone
  (`GolubVanLoan.Chapter04.one_kronecker_add_kronecker_one`).

## Implementation notes

* Algorithms 4.8.1 and 4.8.2 follow the algorithm conventions of `NumlibSurface.GolubVanLoan`: every
  product, sum and quotient passes through the rounding hook `rnd`. Algorithm 4.8.1 is complex, with
  `rnd : ℂ → M ℂ`.
* The fast transforms of the source ("use an FFT") are program parameters, and their specification
  is a hypothesis of the exact-correctness theorem (convention 5 of the library). For Algorithm
  4.8.1 the parameter is any FFT, in particular Algorithm 1.4.1 for $n = 2^t$
  (`GolubVanLoan.Chapter04.algorithm_4_8_1_fft_spec`). For Algorithm 4.8.2 the parameters are the
  abstract transforms $V^{-1} \cdot$, $W^{-1} \cdot$, $V \cdot$ and $W \cdot$, which
  `GolubVanLoan.Chapter04.transformCols` applies to matrices column by column.
* Only the exact semantics of the two algorithms is stated, because the source gives no rounding
  analysis.

## Deviations from the source

* **Generalization.** The diagonalization solve identity extends to the totalized inverse of
  singular matrices. See `GolubVanLoan.Chapter04.equation_4_8_2`.
* **Generalization.** The Fourier and circulant identities include the empty matrix case. See
  `GolubVanLoan.Chapter04.map_star_fourierMatrix`, `GolubVanLoan.Chapter04.dft_conjTranspose`,
  `GolubVanLoan.Chapter04.dft_conjTranspose_mul_self`, `GolubVanLoan.Chapter04.theorem_4_8_2`.
* **Reading.** The circulant program uses one forward FFT interface and totalized division. See
  `GolubVanLoan.Chapter04.algorithm_4_8_1`.
* **Scope.** The circulant solver specification captures correctness for any exact transform. See
  `GolubVanLoan.Chapter04.algorithm_4_8_1_spec`.
* **Reading.** The scalar divided-difference identity uses arbitrary nonzero grid step. See
  `GolubVanLoan.Chapter04.equation_4_8_6`.
* **Reading.** The Poisson program takes transform callbacks and totalizes zero eigenvalue sums. See
  `GolubVanLoan.Chapter04.algorithm_4_8_2`.
* **Generalization.** The exact Poisson solve does not impose a complexity bound on its transforms.
  See `GolubVanLoan.Chapter04.algorithm_4_8_2_spec`.
* **Reading.** The Dirichlet Poisson bandwidth bounds count distances from the main diagonal. See
  `GolubVanLoan.Chapter04.poisson2D_posDef_bandwidth`.
* **Scope.** The periodic real transform theorem proves column eigen-equations. See
  `GolubVanLoan.Chapter04.equation_4_8_25`.
* **Equation (4.8.4)** (typo). The source prints $(V^{-1} \mathcal{D}_n V^{-1})^k$;
  $(V^{-1} \mathcal{D}_n V)^k$ is meant. See `GolubVanLoan.Chapter04.equation_4_8_4`.
* **Lemma 4.8.1** (reading). The formula $\lambda_{j+1} = \bar\omega_n^j$ is read for every
  $n \ge 1$; for $n = 1$ the downshift is $I_1$. See `GolubVanLoan.Chapter04.lemma_4_8_1`.
* **§4.8.6, the Dirichlet–Neumann paragraph** (typo). The source cites a nonexistent "(1.4.13)" for
  $\mathrm{DST2}$; (1.4.12) is meant. See `GolubVanLoan.Chapter04.dn_eigen`.
* **§4.8.6, the Neumann–Neumann paragraph** (typo). The source twice writes $\mathcal{T}^{(DN)}$ and
  $V^{(DN)}$ for $\mathcal{T}^{(NN)}$ and $V^{(NN)}$. See `GolubVanLoan.Chapter04.nn_eigen`.
* **§4.8.6, the periodic matrix** (reading). The statement that $\mathcal{T}^{(P)}_n$ is circulant,
  with first column $(2, -1, 0, \dots, 0, -1)^T$, is read for $n \ge 3$. See
  `GolubVanLoan.Chapter04.periodic_eigen`.

## Not formalized

* **The Problems of §4.8.** Problems are out of scope for the library.
-/

open Complex FloatingPoint Matrix GolubVanLoan.Chapter01
open scoped ComplexConjugate Real Kronecker

namespace GolubVanLoan.Chapter04

/-! ### Equation (4.8.2): solving through an eigenvalue decomposition -/

/-- **Equation (4.8.2)** of [golub2013matrix]. Let $A, V \in \mathbb{C}^{n \times n}$ with $V$
nonsingular, and let $\nu \in \mathbb{C}^n$ with $V^{-1} A V = \operatorname{diag}(\nu_1, \dots,
\nu_n)$, as in (4.8.1). Then for every $b \in \mathbb{C}^n$ $$A^{-1} b = V
\bigl(\operatorname{diag}(\nu)^{-1} (V^{-1} b)\bigr).$$

The source writes $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$ and derives
$u = A^{-1} b = (V \Lambda V^{-1})^{-1} b$. The statement has no hypothesis that $A$ is
nonsingular. The inverse is Mathlib's `Matrix.inv`, which is $0$ at a singular matrix, and $A$
is singular exactly when $\operatorname{diag}(\nu)$ is, so that both sides are then $0$.

**Generalization.** The source uses a nonsingular coefficient matrix to solve the system. Lean
proves the identity for the totalized inverse, which gives zero on both sides when the coefficient
matrix is singular.
-/
theorem equation_4_8_2 {n : ℕ} {A V : Matrix (Fin n) (Fin n) ℂ} {ν : Fin n → ℂ} (hV : IsUnit V)
    (hAV : V⁻¹ * A * V = diagonal ν) (b : Fin n → ℂ) :
    A⁻¹ *ᵥ b = V *ᵥ ((diagonal ν)⁻¹ *ᵥ (V⁻¹ *ᵥ b)) := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).1 hV
  have hA : A = V * diagonal ν * V⁻¹ := by
    rw [← hAV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.mul_one]
  rw [hA, Matrix.mul_inv_rev, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hVd, mulVec_mulVec,
    mulVec_mulVec, Matrix.mul_assoc]

/-! ### §4.8.1 The inverse of the DFT matrix -/

/-- **Section 4.8.1** of [golub2013matrix], the conjugate DFT matrix. For every $n$, the entrywise
complex conjugate $\bar F_n$ of the DFT matrix $F_n$ is the backbone matrix `Matrix.dft n`, with
entries $\bar\omega_n^{kj}$ for $k, j = 0, \dots, n-1$, where $\bar\omega_n = e^{2\pi i/n}$.

**Generalization.** The entry and matrix identities also hold for size zero in Lean. The source
defines the Fourier root using positive size.
-/
theorem map_star_fourierMatrix (n : ℕ) : (fourierMatrix n).map star = dft n := by
  ext i j
  simp [fourierMatrix, conjTranspose_apply, dft_apply_comm]

/-- **Section 4.8.1** of [golub2013matrix]. For every $n$, $F_n^H = \bar F_n$. The source says: "It
is easy to verify that $F_n^H = \bar F_n$".

The identity holds because $F_n$ is symmetric.

**Generalization.** The entry and matrix identities also hold for size zero in Lean. The source
defines the Fourier root using positive size.
-/
theorem dft_conjTranspose (n : ℕ) : (fourierMatrix n)ᴴ = (fourierMatrix n).map star := by
  rw [map_star_fourierMatrix, fourierMatrix, conjTranspose_conjTranspose]

/-- **Section 4.8.1** of [golub2013matrix]. For every $n$, $$F_n^H F_n = n I_n \quad \text{and}
\quad \bar F_n F_n = n I_n.$$

The proof uses the orthogonality sums $\sum_k \omega_n^{k(q-p)} = n \delta_{pq}$.

**Generalization.** The entry and matrix identities also hold for size zero in Lean. The source
defines the Fourier root using positive size.
-/
theorem dft_conjTranspose_mul_self (n : ℕ) :
    (fourierMatrix n)ᴴ * fourierMatrix n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
      (fourierMatrix n).map star * fourierMatrix n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [dft_conjTranspose, map_star_fourierMatrix, fourierMatrix]
  exact ⟨dft_mul_conjTranspose_dft n, dft_mul_conjTranspose_dft n⟩

/-- **Section 4.8.1** of [golub2013matrix]. For $n \ge 1$, "the DFT matrix is a scaled unitary
matrix and" $$F_n^{-1} = \frac{1}{n} \bar F_n.$$
-/
theorem dft_inv (n : ℕ) [NeZero n] :
    (fourierMatrix n)⁻¹ = (n : ℂ)⁻¹ • (fourierMatrix n).map star := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact inv_conjTranspose_dft n

/-- **Section 4.8.1** of [golub2013matrix]. For $n \ge 1$, the DFT matrix $F_n$ is nonsingular. -/
theorem isUnit_fourierMatrix (n : ℕ) [NeZero n] : IsUnit (fourierMatrix n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  refine (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (B := (n : ℂ)⁻¹ • dft n) ?_)
  rw [Matrix.smul_mul, fourierMatrix, dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hn,
    one_smul]

/-! ### §4.8.2 Circulant systems -/

/-- **Equation (4.8.3)** of [golub2013matrix]. Let $n \ge 1$ and $z \in \mathbb{C}^n$. The circulant
matrix $C(z)$ with first column $z$ is a polynomial in the downshift $\mathcal{D}_n$, $$C(z) =
\sum_{k=0}^{n-1} z_k \mathcal{D}_n^k,$$ and $\mathcal{D}_n^n = I_n$.

The entries of $z$ are 0-based, $z = (z_0, \dots, z_{n-1})$. $C(z)$ is `Matrix.circulant z`,
whose entry $(i, j)$ is $z_{i-j}$ with the index taken modulo $n$, and $\mathcal{D}_n$ is the
complex `Matrix.downshift n`. -/
theorem equation_4_8_3 {n : ℕ} [NeZero n] (z : Fin n → ℂ) :
    circulant z = ∑ k : Fin n, z k • (downshift n : Matrix (Fin n) (Fin n) ℂ) ^ (k : ℕ) ∧
      (downshift n : Matrix (Fin n) (Fin n) ℂ) ^ n = 1 :=
  ⟨circulant_eq_sum_downshift_pow z, downshift_pow_card n⟩

/-- **Equation (4.8.4)** of [golub2013matrix]. Let $n \ge 1$, let $V \in \mathbb{C}^{n \times n}$ be
nonsingular, and let $\Lambda \in \mathbb{C}^n$ with $V^{-1} \mathcal{D}_n V =
\operatorname{diag}(\Lambda)$. Then for every $z \in \mathbb{C}^n$ $$V^{-1} C(z) V =
\sum_{k=0}^{n-1} z_k \operatorname{diag}(\Lambda)^k = \operatorname{diag}\Bigl(\sum_{k=0}^{n-1}
z_k \Lambda_i^k\Bigr)_{i},$$ so that $V^{-1} C(z) V$ is diagonal.

**Typo.** The source prints $(V^{-1} \mathcal{D}_n V^{-1})^k$ in the sum. The intended factor is
$(V^{-1} \mathcal{D}_n V)^k = \operatorname{diag}(\Lambda)^k$. -/
theorem equation_4_8_4 {n : ℕ} [NeZero n] {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsUnit V)
    {Λ : Fin n → ℂ} (h : V⁻¹ * (downshift n : Matrix (Fin n) (Fin n) ℂ) * V = diagonal Λ)
    (z : Fin n → ℂ) :
    V⁻¹ * circulant z * V = ∑ k : Fin n, z k • diagonal Λ ^ (k : ℕ) ∧
      V⁻¹ * circulant z * V = diagonal fun i => ∑ k : Fin n, z k * Λ i ^ (k : ℕ) := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).1 hV
  have hpow : ∀ k : ℕ, V⁻¹ * (downshift n : Matrix (Fin n) (Fin n) ℂ) ^ k * V = diagonal Λ ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, nonsing_inv_mul _ hVd]
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih, ← h]
      simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left V _ hVd]
  have h1 : V⁻¹ * circulant z * V = ∑ k : Fin n, z k • diagonal Λ ^ (k : ℕ) := by
    rw [circulant_eq_sum_downshift_pow, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hpow]
  refine ⟨h1, ?_⟩
  rw [h1]
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, diagonal_pow, diagonal_apply, smul_eq_mul, Pi.pow_apply]
  split_ifs with hij <;> simp [hij]

/-- **Theorem 4.8.2** of [golub2013matrix]. Let $z \in \mathbb{C}^n$, $V = F_n$ and
$\lambda = \bar F_n z$. Then $$V^{-1} C(z) V = \operatorname{diag}(\lambda_1, \dots,
\lambda_n).$$

The statement needs no hypothesis on $n$.

**Generalization.** The entry and matrix identities also hold for size zero in Lean. The source
defines the Fourier root using positive size.
-/
theorem theorem_4_8_2 {n : ℕ} (z : Fin n → ℂ) :
    (fourierMatrix n)⁻¹ * circulant z * fourierMatrix n =
      diagonal ((fourierMatrix n).map star *ᵥ z) := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft z

/-- **Lemma 4.8.1** of [golub2013matrix]. Let $n \ge 1$ and $V = F_n$. Then $V^{-1} \mathcal{D}_n
V = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$ with $$\lambda_{j+1} = \bar\omega_n^j =
\cos\Bigl(\frac{2 j \pi}{n}\Bigr) + i \sin\Bigl(\frac{2 j \pi}{n}\Bigr), \qquad j = 0, \dots,
n-1,$$ where $\bar\omega_n = e^{2\pi i/n}$.

**Reading.** The formula is read for every $n \ge 1$. For $n = 1$ the downshift is $I_1$, and
$\lambda_1 = 1$.

Entry $j$ of the Lean diagonal is $\lambda_{j+1}$, written `Complex.exp (2 * π * I / n) ^ j`.
The downshift is the circulant matrix of the source's $e_2$ (`Matrix.downshift_eq_circulant`),
so that Theorem 4.8.2 applies. -/
theorem lemma_4_8_1 (n : ℕ) [NeZero n] :
    (fourierMatrix n)⁻¹ * (downshift n : Matrix (Fin n) (Fin n) ℂ) * fourierMatrix n =
      diagonal fun j : Fin n => Complex.exp (2 * π * I / n) ^ (j : ℕ) := by
  rw [downshift_eq_circulant, theorem_4_8_2, map_star_fourierMatrix]
  congr 1
  funext j
  rw [mulVec_single_one]
  change dft n j 1 = _
  rw [dft_apply]
  congr 1
  by_cases hn : n = 1
  · subst hn
    simp [Subsingleton.elim j 0]
  · rw [Fin.val_one', Nat.one_mod_eq_one.2 hn, Nat.mul_one]

/-! ### Algorithm 4.8.1 -/

/-- A loop over `List.finRange n` whose step $a$ overwrites entry $a$ with $c_a$ ends with the
vector $c$. -/
private theorem foldl_update_finRange_apply {n : ℕ} {β : Type} (c : Fin n → β) (y₀ : Fin n → β)
    (i : Fin n) :
    (List.finRange n).foldl (fun (y : Fin n → β) a => Function.update y a (c a)) y₀ i = c i := by
  rw [List.foldl_update_eq_ite]
  simp

section Programs

variable {M : Type → Type} [Monad M]

/-- A vector program applied to every column. For $X \in K^{m \times p}$ and a program $f$ on $K^m$,
the program computes $X(:, j) \leftarrow f(X(:, j))$ for $j = 1, \dots, p$ in this order, and
returns the matrix of the results. The abstract transforms $V^{-1} \cdot$, $W^{-1} \cdot$,
$V \cdot$ and $W \cdot$ of Algorithm 4.8.2 act on matrices in this way. -/
def transformCols {K : Type} [Zero K] {m p : ℕ} (f : (Fin m → K) → M (Fin m → K))
    (X : Matrix (Fin m) (Fin p) K) : M (Matrix (Fin m) (Fin p) K) := do
  let cols ← (List.finRange p).foldlM (fun (C : Fin p → Fin m → K) (j : Fin p) => do
    let c ← f (fun i => X i j)
    pure (Function.update C j c)) 0
  pure (of fun i j => cols j i)

/-- **Algorithm 4.8.1** of [golub2013matrix]. "If $z \in \mathbb{C}^n$, $y \in \mathbb{C}^n$, and
$C(z)$ is nonsingular, then the following algorithm solves the linear system $C(z) x = y$":
```
Use an FFT to compute c = F̄_n y and d = F̄_n z.
w = c./d
Use an FFT to compute u = F_n w.
x = u/n
```
The program computes $c' = F_n \bar y$ and $d' = F_n \bar z$ with the FFT, then $w_i \leftarrow
\mathrm{fl}(\bar c'_i / \bar d'_i)$, which is $\mathrm{fl}(c_i / d_i)$ because
$\bar F_n y = \overline{F_n \bar y}$. It then computes $u = F_n w$ with the FFT and
$x_i \leftarrow \mathrm{fl}(u_i / n)$ for $i = 1, \dots, n$.

The FFT is the program parameter `fft`, a computation of $x \mapsto F_n x$. For $n = 2^t$ it can
be Algorithm 1.4.1 (`GolubVanLoan.Chapter04.algorithm_4_8_1_fft_spec`). Complex conjugation is
exact (convention 1 of the library). The program has no hypothesis on $z$.

**Reading.** The forward FFT is a parameter. The program implements the conjugate transforms by
conjugating the input and output of that same FFT, then rounds the indicated quotients. The program
totalizes division for singular input.
-/
noncomputable def algorithm_4_8_1 (rnd : ℂ → M ℂ) {n : ℕ} (fft : (Fin n → ℂ) → M (Fin n → ℂ))
    (z y : Fin n → ℂ) : M (Fin n → ℂ) := do
  let c ← fft fun i => star (y i)
  let d ← fft fun i => star (z i)
  let w ← (List.finRange n).foldlM (fun (w : Fin n → ℂ) (i : Fin n) => do
    let q ← rnd (star (c i) / star (d i))
    pure (Function.update w i q)) 0
  let u ← fft w
  (List.finRange n).foldlM (fun (x : Fin n → ℂ) (i : Fin n) => do
    let q ← rnd (u i / n)
    pure (Function.update x i q)) 0

end Programs

/-- The exact semantics of `GolubVanLoan.Chapter04.transformCols`. Let $K$ be a semiring, not
necessarily unital or associative, let $A \in K^{m \times m}$, and let $f$ be a program in exact
arithmetic (the monad `Id`) that computes $x \mapsto A x$. Then for every
$X \in K^{m \times p}$, the program `transformCols f X` computes $A X$. -/
theorem transformCols_id {K : Type} [NonUnitalNonAssocSemiring K] {m p : ℕ}
    {f : (Fin m → K) → Id (Fin m → K)} {A : Matrix (Fin m) (Fin m) K}
    (hf : ∀ x, Id.run (f x) = A *ᵥ x) (X : Matrix (Fin m) (Fin p) K) :
    Id.run (transformCols f X) = A * X := by
  ext i j
  simp only [transformCols, Id.run_bind, Id.run_pure, List.idRun_foldlM, of_apply]
  rw [foldl_update_finRange_apply, hf]
  rfl

/-- For a complex matrix $A$ and a vector $y$, $\bar A y = \overline{A \bar y}$ entrywise. -/
private theorem map_star_mulVec_eq_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ)
    (i : Fin n) : (A.map star *ᵥ y) i = star ((A *ᵥ fun j => star (y j)) i) := by
  simp only [mulVec, dotProduct, map_apply, star_sum, star_mul', star_star]

/-- **Algorithm 4.8.1** of [golub2013matrix], exact correctness. Let $n \ge 1$, let
$z \in \mathbb{C}^n$ with $C(z)$ nonsingular, and let `fft` be a program that computes
$x \mapsto F_n x$ in exact arithmetic. Then for every $y \in \mathbb{C}^n$, the vector $x$ that
Algorithm 4.8.1 returns in exact arithmetic satisfies $C(z) x = y$.

By Theorem 4.8.2, $C(z) F_n = F_n \operatorname{diag}(d)$ with $d = \bar F_n z$. The entries of
$d$ are nonzero because $C(z)$ is nonsingular, and then $C(z) (F_n (c ./ d) / n) = F_n \bar F_n
y / n = y$.

**Reading.** The theorem assumes that the transform implements the exact Fourier matrix action. It
proves the solve under this assumption without tracking transform costs.
-/
theorem algorithm_4_8_1_spec {n : ℕ} [NeZero n] {z : Fin n → ℂ} (hC : IsUnit (circulant z))
    {fft : (Fin n → ℂ) → Id (Fin n → ℂ)} (hfft : ∀ x, Id.run (fft x) = fourierMatrix n *ᵥ x)
    (y : Fin n → ℂ) : circulant z *ᵥ Id.run (algorithm_4_8_1 pure fft z y) = y := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  -- the exact run
  have hrun : Id.run (algorithm_4_8_1 pure fft z y) =
      (n : ℂ)⁻¹ • (fourierMatrix n *ᵥ fun i =>
        ((fourierMatrix n).map star *ᵥ y) i / ((fourierMatrix n).map star *ᵥ z) i) := by
    simp only [algorithm_4_8_1, Id.run_bind, Id.run_pure, pure_bind, List.foldlM_pure, hfft]
    funext i
    rw [foldl_update_finRange_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_inv_mul]
    congr 2
    funext k
    rw [foldl_update_finRange_apply, map_star_mulVec_eq_star, map_star_mulVec_eq_star]
  have hFc : fourierMatrix n *ᵥ ((fourierMatrix n).map star *ᵥ y) = (n : ℂ) • y := by
    rw [mulVec_mulVec, map_star_fourierMatrix, fourierMatrix, conjTranspose_dft_mul_dft,
      smul_mulVec, one_mulVec]
  have hdiag := theorem_4_8_2 z
  have hFu : IsUnit (fourierMatrix n) := isUnit_fourierMatrix n
  rw [hrun]
  generalize (fourierMatrix n).map star *ᵥ y = c at hFc ⊢
  generalize (fourierMatrix n).map star *ᵥ z = d at hdiag ⊢
  generalize fourierMatrix n = F at hFu hdiag hFc ⊢
  have hFd : IsUnit F.det := (isUnit_iff_isUnit_det F).1 hFu
  -- the eigenvalues are nonzero
  have hdne : ∀ i, d i ≠ 0 := by
    have hu : IsUnit (diagonal d) := by
      rw [← hdiag]
      exact ((isUnit_nonsing_inv_iff.2 hFu).mul hC).mul hFu
    exact fun i => (Pi.isUnit_iff.1 (isUnit_diagonal.1 hu) i).ne_zero
  have hCF : circulant z * F = F * diagonal d := by
    rw [← hdiag]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hFd, Matrix.one_mul]
  have hw : diagonal d *ᵥ (fun i => c i / d i) = c := by
    funext i
    rw [mulVec_diagonal, mul_div_cancel₀ _ (hdne i)]
  rw [mulVec_smul, mulVec_mulVec, hCF, ← mulVec_mulVec, hw, hFc, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

/-- **Algorithm 4.8.1** of [golub2013matrix] with the radix-2 FFT. Let $n = 2^t$ and let
$z \in \mathbb{C}^n$ with $C(z)$ nonsingular. Then for every $y \in \mathbb{C}^n$, Algorithm
4.8.1 with Algorithm 1.4.1 (`GolubVanLoan.Chapter01.algorithm_1_4_1`) as its FFT returns in
exact arithmetic a vector $x$ with $C(z) x = y$. -/
theorem algorithm_4_8_1_fft_spec (t : ℕ) {z : Fin (2 ^ t) → ℂ} (hC : IsUnit (circulant z))
    (y : Fin (2 ^ t) → ℂ) :
    circulant z *ᵥ Id.run (algorithm_4_8_1 pure (algorithm_1_4_1 pure t) z y) = y :=
  algorithm_4_8_1_spec hC (algorithm_1_4_1_spec t) y

/-! ### §4.8.3 The discretized Poisson equation in one dimension -/

/-- Row $x$ of $\mathcal{T}^{(DD)}_{N+1}$ applied to the interior values $g_1, \dots, g_{N+1}$ of a
sequence $g$ is $2 g_{x+1} - g_x - g_{x+2}$, plus $g_0$ in the first row and $g_{N+2}$ in the
last row. -/
private theorem symmTridiagonalToeplitz_mulVec_shift_apply (N : ℕ) (g : ℕ → ℝ)
    (x : Fin (N + 1)) :
    (symmTridiagonalToeplitz (N + 1) (-1) 2 *ᵥ fun i : Fin (N + 1) => g ((i : ℕ) + 1)) x =
      2 * g ((x : ℕ) + 1) - g x - g ((x : ℕ) + 2) + (if (x : ℕ) = 0 then g 0 else 0) +
        (if (x : ℕ) = N then g (N + 2) else 0) := by
  rw [symmTridiagonalToeplitz_mulVec_apply']
  obtain ⟨x, hx⟩ := x
  have e1 : x + 1 + 1 = x + 2 := rfl
  by_cases c1 : 0 < x <;> by_cases c2 : x < N
  · have e : x - 1 + 1 = x := by omega
    have d1 : x ≠ 0 := by omega
    have d2 : x ≠ N := by omega
    simp [c1, c2, d1, d2, e, e1]
    ring
  · have e : x - 1 + 1 = x := by omega
    have d1 : x ≠ 0 := by omega
    obtain rfl : x = N := by omega
    simp [c1, d1, e]
    ring
  · obtain rfl : x = 0 := by omega
    have d2 : (0 : ℕ) ≠ N := by omega
    simp [c2, d2]
    ring
  · obtain rfl : x = 0 := by omega
    obtain rfl : N = 0 := by omega
    simp
    ring

/-- **Equation (4.8.6)** of [golub2013matrix] and the Dirichlet–Dirichlet system after it. Let
$N \ge 0$ and $m = N + 2$, let $h \neq 0$ be real, and let $u, f : \mathbb{N} \to \mathbb{R}$.
First, for every $i$, $$\frac{1}{h} \Bigl(\frac{u_{i+1} - u_i}{h} - \frac{u_i -
u_{i-1}}{h}\Bigr) = \frac{u_{i-1} - 2 u_i + u_{i+1}}{h^2}.$$ Second, the equations
$$\frac{u_{i-1} - 2 u_i + u_{i+1}}{h^2} = -f_i, \qquad i = 1, \dots, m-1,$$ hold if and only if
$$\mathcal{T}^{(DD)}_{m-1} u(1{:}m-1) = h^2 f(1{:}m-1) + u_0 e_1 + u_m e_{m-1}.$$

In the source, $h = (\beta - \alpha)/m$ is the grid spacing on $[\alpha, \beta]$, and the
boundary values are $u_0 = u_\alpha$ and $u_m = u_\beta$; the statement holds for every
$h \neq 0$. The sequence $u$ is indexed by $\mathbb{N}$, so that $u_{i-1}$ at $i = 0$ is $u_0$
by truncated subtraction; the first identity holds there too. The matrix
$\mathcal{T}^{(DD)}_{m-1}$ is `Matrix.symmTridiagonalToeplitz (N + 1) (-1) 2`, and the equations
are indexed from $0$ by `Fin (N + 1)`.

**Reading.** The grid step can be any nonzero real number and the matrix form is stated for every
grid with at least one interior point. The first scalar identity also holds at index zero with
truncated natural subtraction.
-/
theorem equation_4_8_6 (N : ℕ) {h : ℝ} (hh : h ≠ 0) (u f : ℕ → ℝ) :
    (∀ i : ℕ, ((u (i + 1) - u i) / h - (u i - u (i - 1)) / h) / h =
      (u (i - 1) - 2 * u i + u (i + 1)) / h ^ 2) ∧
    ((∀ i : Fin (N + 1), (u i - 2 * u ((i : ℕ) + 1) + u ((i : ℕ) + 2)) / h ^ 2 =
        -f ((i : ℕ) + 1)) ↔
      symmTridiagonalToeplitz (N + 1) (-1) 2 *ᵥ (fun i : Fin (N + 1) => u ((i : ℕ) + 1)) =
        (fun i : Fin (N + 1) => h ^ 2 * f ((i : ℕ) + 1)) + u 0 • Pi.single 0 1 +
          u (N + 2) • Pi.single (Fin.last N) 1) := by
  refine ⟨fun i => by field_simp; ring, ?_⟩
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [symmTridiagonalToeplitz_mulVec_shift_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff,
    Fin.val_zero, Fin.val_last, mul_ite, mul_one, mul_zero]
  rw [div_eq_iff (pow_ne_zero 2 hh)]
  constructor <;> intro h' <;> linarith

/-- **Equation (4.8.8)** of [golub2013matrix]. For $n \ge 2$, the Dirichlet–Neumann
second-difference matrix is $$\mathcal{T}^{(DN)}_n = \mathcal{T}^{(DD)}_n - e_n e_{n-1}^T.$$

Its last row is $(0, \dots, 0, -2, 2)$. -/
theorem equation_4_8_8 {n : ℕ} (hn : 2 ≤ n) :
    secondDifferenceDN n = symmTridiagonalToeplitz n (-1) 2 -
      vecMulVec (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) (Pi.single ⟨n - 2, by omega⟩ 1) := by
  ext i j
  rw [secondDifferenceDN, Matrix.sub_apply, Matrix.sub_apply]
  congr 1
  simp only [of_apply, vecMulVec_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-- **Equation (4.8.9)** of [golub2013matrix]. For $n \ge 2$, the Neumann–Neumann second-difference
matrix is $$\mathcal{T}^{(NN)}_n = \mathcal{T}^{(DD)}_n - e_n e_{n-1}^T - e_1 e_2^T.$$
-/
theorem equation_4_8_9 {n : ℕ} (hn : 2 ≤ n) :
    secondDifferenceNN n = symmTridiagonalToeplitz n (-1) 2 -
      vecMulVec (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) (Pi.single ⟨n - 2, by omega⟩ 1) -
      vecMulVec (Pi.single (⟨0, by omega⟩ : Fin n) 1) (Pi.single ⟨1, by omega⟩ 1) := by
  rw [← equation_4_8_8 hn]
  ext i j
  rw [secondDifferenceNN, Matrix.sub_apply, Matrix.sub_apply]
  congr 1
  simp only [of_apply, vecMulVec_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-- **Equation (4.8.10)** of [golub2013matrix]. For $n \ge 2$, the periodic second-difference matrix
is $$\mathcal{T}^{(P)}_n = \mathcal{T}^{(DD)}_n - e_1 e_n^T - e_n e_1^T.$$

For $n = 1$ the two corner positions coincide, and `Matrix.secondDifferencePeriodic 1` is $(1)$,
not the value $(0)$ of the formula. -/
theorem equation_4_8_10 {n : ℕ} (hn : 2 ≤ n) :
    secondDifferencePeriodic n = symmTridiagonalToeplitz n (-1) 2 -
      vecMulVec (Pi.single (⟨0, by omega⟩ : Fin n) 1) (Pi.single ⟨n - 1, by omega⟩ 1) -
      vecMulVec (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) (Pi.single ⟨0, by omega⟩ 1) := by
  ext i j
  rw [secondDifferencePeriodic, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, sub_sub]
  congr 1
  simp only [of_apply, vecMulVec_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-! ### §4.8.4 The discretized Poisson equation in two dimensions -/

/-- **Section 4.8.4** of [golub2013matrix], the Kronecker sum. Let $R$ be a commutative ring,
$A_1 \in R^{n_1 \times n_1}$ and $A_2 \in R^{n_2 \times n_2}$. Then the source's matrix
$I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ is the Kronecker sum `A₂ ⊕ₖ A₁`
$= A_2 \otimes I_{n_1} + I_{n_2} \otimes A_1$ of the backbone. -/
theorem one_kronecker_add_kronecker_one {R : Type*} [CommRing R] {n₁ n₂ : ℕ}
    (A₁ : Matrix (Fin n₁) (Fin n₁) R) (A₂ : Matrix (Fin n₂) (Fin n₂) R) :
    (1 : Matrix (Fin n₂) (Fin n₂) R) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) R) = A₂ ⊕ₖ A₁ := by
  rw [kroneckerSum_def, add_comm]

/-- **Section 4.8.4** of [golub2013matrix], the right-hand side of the five-point system. Let
$N_1, N_2 \ge 0$, $m_1 = N_1 + 2$ and $m_2 = N_2 + 2$, let $h$ be real, and let $F, G :
\mathbb{N} \times \mathbb{N} \to \mathbb{R}$, where $G_{ij}$ stands for the grid value
$u(\alpha_x + i h, \alpha_y + j h)$. The matrix $B \in \mathbb{R}^{(m_1-1) \times (m_2-1)}$ has,
at the interior point $P = (i, j)$ with $1 \le i \le m_1 - 1$ and $1 \le j \le m_2 - 1$, the
entry $$b_{ij} = h^2 F_{ij} + [i = 1] G_{0j} + [i = m_1 - 1] G_{m_1 j} + [j = 1] G_{i0} + [j =
m_2 - 1] G_{i m_2},$$ where $[\cdot]$ is $1$ if the condition holds and $0$ otherwise. This is
$h^2 F(P)$ plus the values of $G$ at the neighbours of $P$ that lie on the boundary.

The grid spacings are equal, $h_x = h_y = h$. Entry $(a, b)$ of the Lean matrix is the point
$(a + 1, b + 1)$. At a corner of the interior, two boundary values are added. -/
def fivePointRhs (N₁ N₂ : ℕ) (h : ℝ) (F G : ℕ → ℕ → ℝ) :
    Matrix (Fin (N₁ + 1)) (Fin (N₂ + 1)) ℝ :=
  of fun a b => h ^ 2 * F ((a : ℕ) + 1) ((b : ℕ) + 1)
    + (if (a : ℕ) = 0 then G 0 ((b : ℕ) + 1) else 0)
    + (if (a : ℕ) = N₁ then G (N₁ + 2) ((b : ℕ) + 1) else 0)
    + (if (b : ℕ) = 0 then G ((a : ℕ) + 1) 0 else 0)
    + (if (b : ℕ) = N₂ then G ((a : ℕ) + 1) (N₂ + 2) else 0)

/-- **Section 4.8.4** of [golub2013matrix], the five-point system. Let $N_1, N_2$, $m_1 = N_1 + 2$,
$m_2 = N_2 + 2$, $h$, $F$ and $G$ be as in `GolubVanLoan.Chapter04.fivePointRhs`, and let $B$ be
the matrix defined there. The equations $$4 G_{ij} - G_{i,j+1} - G_{i+1,j} - G_{i,j-1} -
G_{i-1,j} = h^2 F_{ij}$$ at all interior points $1 \le i \le m_1 - 1$, $1 \le j \le m_2 - 1$
hold if and only if $$\bigl(I_{m_2-1} \otimes \mathcal{T}^{(DD)}_{m_1-1} +
\mathcal{T}^{(DD)}_{m_2-1} \otimes I_{m_1-1}\bigr) \operatorname{vec}(U) =
\operatorname{vec}(B),$$ where $U \in \mathbb{R}^{(m_1-1) \times (m_2-1)}$ is the matrix of
interior values, $U_{ij} = G_{ij}$.

The equations are the source's $4 u(P) - u(N) - u(E) - u(S) - u(W) = h^2 F(P)$ with equal grid
spacings $h$, and the neighbours on the boundary are moved to the right-hand side. The first
index runs along $x$ and along the rows of $U$; `Matrix.vec` stacks the columns of $U$. -/
theorem poisson2D_eq_kroneckerSum (N₁ N₂ : ℕ) (h : ℝ) (F G : ℕ → ℕ → ℝ) :
    (∀ (a : Fin (N₁ + 1)) (b : Fin (N₂ + 1)),
      4 * G ((a : ℕ) + 1) ((b : ℕ) + 1) - G ((a : ℕ) + 1) ((b : ℕ) + 2)
        - G ((a : ℕ) + 2) ((b : ℕ) + 1) - G ((a : ℕ) + 1) b - G a ((b : ℕ) + 1)
        = h ^ 2 * F ((a : ℕ) + 1) ((b : ℕ) + 1)) ↔
    ((1 : Matrix (Fin (N₂ + 1)) (Fin (N₂ + 1)) ℝ) ⊗ₖ symmTridiagonalToeplitz (N₁ + 1) (-1) 2
        + symmTridiagonalToeplitz (N₂ + 1) (-1) 2 ⊗ₖ (1 : Matrix (Fin (N₁ + 1)) (Fin (N₁ + 1)) ℝ))
        *ᵥ vec (of fun (a : Fin (N₁ + 1)) (b : Fin (N₂ + 1)) => G ((a : ℕ) + 1) ((b : ℕ) + 1))
      = vec (fivePointRhs N₁ N₂ h F G) := by
  rw [one_kronecker_add_kronecker_one, kroneckerSum_mulVec_vec, vec_inj, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  have r1 : (symmTridiagonalToeplitz (N₁ + 1) (-1) 2 *
      of fun (a : Fin (N₁ + 1)) (b : Fin (N₂ + 1)) => G ((a : ℕ) + 1) ((b : ℕ) + 1)) a b =
      2 * G ((a : ℕ) + 1) ((b : ℕ) + 1) - G a ((b : ℕ) + 1) - G ((a : ℕ) + 2) ((b : ℕ) + 1) +
        (if (a : ℕ) = 0 then G 0 ((b : ℕ) + 1) else 0) +
        (if (a : ℕ) = N₁ then G (N₁ + 2) ((b : ℕ) + 1) else 0) :=
    symmTridiagonalToeplitz_mulVec_shift_apply N₁ (fun i => G i ((b : ℕ) + 1)) a
  have r2 : ((of fun (a : Fin (N₁ + 1)) (b : Fin (N₂ + 1)) => G ((a : ℕ) + 1) ((b : ℕ) + 1)) *
      (symmTridiagonalToeplitz (N₂ + 1) (-1) 2)ᵀ) a b =
      2 * G ((a : ℕ) + 1) ((b : ℕ) + 1) - G ((a : ℕ) + 1) b - G ((a : ℕ) + 1) ((b : ℕ) + 2) +
        (if (b : ℕ) = 0 then G ((a : ℕ) + 1) 0 else 0) +
        (if (b : ℕ) = N₂ then G ((a : ℕ) + 1) (N₂ + 2) else 0) := by
    rw [← symmTridiagonalToeplitz_mulVec_shift_apply N₂ (fun j => G ((a : ℕ) + 1) j) b,
      Matrix.mul_apply, mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [of_apply, transpose_apply, mul_comm]
  rw [Matrix.add_apply, r1, r2]
  simp only [fivePointRhs, of_apply]
  constructor <;> intro h' <;> linarith

/-- **Equation (4.8.12)** of [golub2013matrix], in matrix form. Let
$A_1 \in \mathbb{R}^{n_1 \times n_1}$, $A_2 \in \mathbb{R}^{n_2 \times n_2}$ and
$U, B \in \mathbb{R}^{n_1 \times n_2}$, and let $u = \operatorname{vec}(U)$ and
$b = \operatorname{vec}(B)$, so that $U = \operatorname{reshape}(u, n_1, n_2)$. Then $$(I_{n_2}
\otimes A_1 + A_2 \otimes I_{n_1}) u = b \iff A_1 U + U A_2^T = B.$$
-/
theorem equation_4_8_12 {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (U B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)) *ᵥ vec U
      = vec B ↔ A₁ * U + U * A₂ᵀ = B := by
  rw [one_kronecker_add_kronecker_one, kroneckerSum_mulVec_vec, vec_inj]

/-- **Section 4.8.4** of [golub2013matrix], the transformed system. Let
$A_1, V \in \mathbb{R}^{n_1 \times n_1}$ and $A_2, W \in \mathbb{R}^{n_2 \times n_2}$ with $V$
and $W$ nonsingular, $V^{-1} A_1 V = D_1 = \operatorname{diag}(\lambda)$ and
$W^{-1} A_2 W = D_2 = \operatorname{diag}(\mu)$, as in (4.8.13)–(4.8.14). Let
$U, B \in \mathbb{R}^{n_1 \times n_2}$, and put $\tilde U = V^{-1} U W^{-T}$ and
$\tilde B = V^{-1} B W^{-T}$. Then $A_1 U + U A_2^T = B$ if and only if
$D_1 \tilde U + \tilde U D_2 = \tilde B$. If moreover $\lambda_i + \mu_j \neq 0$ for all $i$ and
$j$, then $A_1 U + U A_2^T = B$ if and only if $U = V X W^T$, where
$X_{ij} = \tilde b_{ij} / (\lambda_i + \mu_j)$.

The eigenvalues $\lambda_i$ of $A_1$ are `ν i` in Lean. -/
theorem fastPoisson_transformed {n₁ n₂ : ℕ} {A₁ V : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ W : Matrix (Fin n₂) (Fin n₂) ℝ} (hV : IsUnit V) (hW : IsUnit W) {ν : Fin n₁ → ℝ}
    {μ : Fin n₂ → ℝ} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (U B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    (A₁ * U + U * A₂ᵀ = B ↔
      diagonal ν * (V⁻¹ * U * W⁻¹ᵀ) + V⁻¹ * U * W⁻¹ᵀ * diagonal μ = V⁻¹ * B * W⁻¹ᵀ) ∧
    ((∀ i j, ν i + μ j ≠ 0) → (A₁ * U + U * A₂ᵀ = B ↔
      U = V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ)) := by
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).1 hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).1 hW
  have hWW : W⁻¹ᵀ * Wᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv W hWd, transpose_one]
  have hWW' : Wᵀ * W⁻¹ᵀ = 1 := by rw [← transpose_mul, nonsing_inv_mul W hWd, transpose_one]
  refine ⟨?_, fun hνμ => ?_⟩
  · have hA₁' : A₁ = V * diagonal ν * V⁻¹ := by
      rw [← hA₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.one_mul,
        Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.mul_one]
    have hA₂' : A₂ᵀ = W⁻¹ᵀ * diagonal μ * Wᵀ := by
      have : A₂ = W * diagonal μ * W⁻¹ := by
        rw [← hA₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hWd,
          Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hWd, Matrix.mul_one]
      rw [this, transpose_mul, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    have key : V⁻¹ * (A₁ * U + U * A₂ᵀ) * W⁻¹ᵀ =
        diagonal ν * (V⁻¹ * U * W⁻¹ᵀ) + V⁻¹ * U * W⁻¹ᵀ * diagonal μ := by
      rw [hA₁', hA₂']
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [nonsing_inv_mul_cancel_left V _ hVd, hWW', Matrix.mul_one]
    have hcancel : ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ, V * (V⁻¹ * X * W⁻¹ᵀ) * Wᵀ = X := by
      intro X
      calc V * (V⁻¹ * X * W⁻¹ᵀ) * Wᵀ = V * V⁻¹ * X * (W⁻¹ᵀ * Wᵀ) := by
            simp only [Matrix.mul_assoc]
        _ = X := by rw [mul_nonsing_inv _ hVd, hWW, Matrix.one_mul, Matrix.mul_one]
    rw [← key]
    constructor
    · intro h
      rw [h]
    · intro h
      rw [← hcancel (A₁ * U + U * A₂ᵀ), h, hcancel]
  · rw [← equation_4_8_12 A₁ A₂ U B, one_kronecker_add_kronecker_one]
    exact FastPoisson.kroneckerSum_mulVec_vec_eq_iff hV hW hA₁ hA₂ hνμ U B

/-- **Section 4.8.4** of [golub2013matrix]. Let $A_1, V \in \mathbb{R}^{n_1 \times n_1}$ and
$A_2, W \in \mathbb{R}^{n_2 \times n_2}$ with $V$ and $W$ nonsingular,
$V^{-1} A_1 V = \operatorname{diag}(\lambda)$ and $W^{-1} A_2 W = \operatorname{diag}(\mu)$, as
in (4.8.13)–(4.8.14). If $A = I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ is nonsingular, then
$\lambda_i + \mu_j \neq 0$ for all $i$ and $j$. The source says: "For this to be well-defined,
no eigenvalue of $A_1$ can be the negative of an eigenvalue of $A_2$".

If $\lambda_i + \mu_j = 0$, then $U = V e_i e_j^T W^T \neq 0$ has $A \operatorname{vec}(U) = 0$.
The eigenvalues $\lambda_i$ are `ν i` in Lean. The hypothesis on $A$ is stated for the Kronecker
sum `A₂ ⊕ₖ A₁`, which is $A$ by `GolubVanLoan.Chapter04.one_kronecker_add_kronecker_one`. -/
theorem add_ne_zero_of_isUnit_kroneckerSum {n₁ n₂ : ℕ} {A₁ V : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ W : Matrix (Fin n₂) (Fin n₂) ℝ} (hV : IsUnit V) (hW : IsUnit W) {ν : Fin n₁ → ℝ}
    {μ : Fin n₂ → ℝ} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hA : IsUnit (A₂ ⊕ₖ A₁)) (i : Fin n₁) (j : Fin n₂) : ν i + μ j ≠ 0 := by
  intro hij
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det V).1 hV
  have hWd : IsUnit W.det := (isUnit_iff_isUnit_det W).1 hW
  have hWtd : IsUnit Wᵀ.det := by rwa [det_transpose]
  have hAV : A₁ * V = V * diagonal ν := by
    rw [← hA₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.one_mul]
  have hAW : A₂ * W = W * diagonal μ := by
    rw [← hA₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hWd, Matrix.one_mul]
  set E : Matrix (Fin n₁) (Fin n₂) ℝ := Matrix.single i j 1 with hE
  have hE0 : diagonal ν * E + E * diagonal μ = 0 := by
    ext a b
    simp only [hE, Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply,
    Matrix.zero_apply]
    split_ifs with hab
    · obtain ⟨rfl, rfl⟩ := hab
      linear_combination hij
    · ring
  have hzero : (A₂ ⊕ₖ A₁) *ᵥ vec (V * E * Wᵀ) = 0 := by
    rw [kroneckerSum_mulVec_vec]
    have : A₁ * (V * E * Wᵀ) + V * E * Wᵀ * A₂ᵀ = V * (diagonal ν * E + E * diagonal μ) * Wᵀ := by
      calc A₁ * (V * E * Wᵀ) + V * E * Wᵀ * A₂ᵀ = A₁ * V * E * Wᵀ + V * E * (A₂ * W)ᵀ := by
            rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = V * (diagonal ν * E + E * diagonal μ) * Wᵀ := by
            rw [hAV, hAW, transpose_mul, diagonal_transpose]
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [this, hE0, Matrix.mul_zero, Matrix.zero_mul, vec_zero]
  have hinj := mulVec_injective_iff_isUnit.2 hA
  have hU : V * E * Wᵀ = 0 := by
    rw [← vec_inj, vec_zero]
    exact hinj (hzero.trans (mulVec_zero _).symm)
  have hE' : E = 0 := by
    have := congrArg (fun X => V⁻¹ * X * (Wᵀ)⁻¹) hU
    simpa only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left V _ hVd,
      mul_nonsing_inv _ hWtd, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] using this
  have := congrFun (congrFun hE' i) j
  simp [hE] at this

/-- **Algorithm 4.8.2** of [golub2013matrix] (Fast Poisson Solver Framework). "Assume that
$A_1 \in \mathbb{R}^{n_1 \times n_1}$ and $A_2 \in \mathbb{R}^{n_2 \times n_2}$ have fast
eigenvalue decompositions (4.8.13) and (4.8.14) and that the matrix
$A = I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ is nonsingular. The following algorithm solves
the linear system $Au = b$":
```
B̃ = (W⁻¹ (V⁻¹ B)ᵀ)ᵀ where B = reshape(b, n₁, n₂)
for i = 1:n₁, for j = 1:n₂: ũ_ij = b̃_ij / (λ_i + μ_j)
u = reshape(U, n₁n₂, 1) where U = (W (V Ũ)ᵀ)ᵀ
```
The program reads $B = \operatorname{reshape}(b, n_1, n_2)$ and computes $Y = V^{-1} B$ and
$\tilde B^T = W^{-1} Y^T$ column by column. It then computes $\tilde u_{ij} \leftarrow
\mathrm{fl}(\tilde b_{ij} / \mathrm{fl}(\lambda_i + \mu_j))$ for all $i$ and $j$, then
$P = V \tilde U$ and $Q = W P^T$ column by column, and returns $u = \operatorname{vec}(Q^T)$.

The fast transforms $V^{-1} \cdot$, $W^{-1} \cdot$, $V \cdot$ and $W \cdot$ are the program
parameters `applyVinv`, `applyWinv`, `applyV` and `applyW`, computations of $x \mapsto V^{-1} x$
and so on, which `GolubVanLoan.Chapter04.transformCols` applies column by column. The
eigenvalues $\lambda$ and $\mu$ are the parameters `ν` and `μ`, and $b$ is indexed by
`Fin n₂ × Fin n₁` as $\operatorname{vec}(B)$. The program has no hypotheses; those of the source
are hypotheses of `GolubVanLoan.Chapter04.algorithm_4_8_2_spec`.

**Reading.** The eigenvalues and forward and inverse transforms are parameters. The program rounds
the eigenvalue sum and the quotient separately, with totalized division if the computed sum is zero.
-/
noncomputable def algorithm_4_8_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n₁ n₂ : ℕ}
    (applyVinv applyV : (Fin n₁ → ℝ) → M (Fin n₁ → ℝ))
    (applyWinv applyW : (Fin n₂ → ℝ) → M (Fin n₂ → ℝ))
    (ν : Fin n₁ → ℝ) (μ : Fin n₂ → ℝ) (b : Fin n₂ × Fin n₁ → ℝ) : M (Fin n₂ × Fin n₁ → ℝ) := do
  let Y ← transformCols applyVinv (of fun i j => b (j, i))
  let Z ← transformCols applyWinv Yᵀ
  let Ut ← (List.finRange n₁).foldlM (fun (U : Fin n₁ → Fin n₂ → ℝ) (i : Fin n₁) => do
    let r ← (List.finRange n₂).foldlM (fun (r : Fin n₂ → ℝ) (j : Fin n₂) => do
      let s ← rnd (ν i + μ j)
      let q ← rnd (Z j i / s)
      pure (Function.update r j q)) 0
    pure (Function.update U i r)) 0
  let P ← transformCols applyV (of Ut)
  let Q ← transformCols applyW Pᵀ
  pure (vec Qᵀ)

/-- **Algorithm 4.8.2** of [golub2013matrix], exact correctness. Let
$A_1, V \in \mathbb{R}^{n_1 \times n_1}$ and $A_2, W \in \mathbb{R}^{n_2 \times n_2}$ with $V$
and $W$ nonsingular, $V^{-1} A_1 V = \operatorname{diag}(\lambda)$ and
$W^{-1} A_2 W = \operatorname{diag}(\mu)$, and let
$A = I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$ be nonsingular. Let the transform programs
compute $x \mapsto V^{-1} x$, $x \mapsto V x$, $x \mapsto W^{-1} x$ and $x \mapsto W x$ in exact
arithmetic. Then for every $b \in \mathbb{R}^{n_1 n_2}$, the vector $u$ that Algorithm 4.8.2
returns in exact arithmetic satisfies $A u = b$.

The algorithm computes $U = V \tilde U W^T$ with $\tilde u_{ij} = \tilde b_{ij} / (\lambda_i +
\mu_j)$ and $\tilde B = V^{-1} B W^{-T}$, which is the solution of
`FastPoisson.kroneckerSum_mulVec_vec_eq_iff`.

**Generalization.** Any exact transform callbacks suffice for the algebraic solve. The source
hypothesizes fast decompositions and gives a corresponding operation bound.
-/
theorem algorithm_4_8_2_spec {n₁ n₂ : ℕ} {A₁ V : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ W : Matrix (Fin n₂) (Fin n₂) ℝ} (hV : IsUnit V) (hW : IsUnit W) {ν : Fin n₁ → ℝ}
    {μ : Fin n₂ → ℝ} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hA : IsUnit ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ +
      A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)))
    {applyVinv applyV : (Fin n₁ → ℝ) → Id (Fin n₁ → ℝ)}
    {applyWinv applyW : (Fin n₂ → ℝ) → Id (Fin n₂ → ℝ)}
    (hVinv : ∀ x, Id.run (applyVinv x) = V⁻¹ *ᵥ x) (hV' : ∀ x, Id.run (applyV x) = V *ᵥ x)
    (hWinv : ∀ x, Id.run (applyWinv x) = W⁻¹ *ᵥ x) (hW' : ∀ x, Id.run (applyW x) = W *ᵥ x)
    (b : Fin n₂ × Fin n₁ → ℝ) :
    ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)) *ᵥ
      Id.run (algorithm_4_8_2 pure applyVinv applyV applyWinv applyW ν μ b) = b := by
  rw [one_kronecker_add_kronecker_one] at hA ⊢
  have hνμ := add_ne_zero_of_isUnit_kroneckerSum hV hW hA₁ hA₂ hA
  set B : Matrix (Fin n₁) (Fin n₂) ℝ := of fun i j => b (j, i) with hB
  have hBt : (W⁻¹ * (V⁻¹ * B)ᵀ)ᵀ = V⁻¹ * B * W⁻¹ᵀ := by
    rw [transpose_mul, transpose_transpose]
  have hrun : Id.run (algorithm_4_8_2 pure applyVinv applyV applyWinv applyW ν μ b) =
      vec (V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ) := by
    simp only [algorithm_4_8_2, Id.run_bind, Id.run_pure, pure_bind, List.foldlM_pure,
      transformCols_id hVinv, transformCols_id hV', transformCols_id hWinv, transformCols_id hW']
    congr 1
    rw [transpose_mul, transpose_transpose]
    congr 2
    ext i j
    rw [of_apply, foldl_update_finRange_apply, foldl_update_finRange_apply, of_apply, ← hBt,
      transpose_apply]
  rw [hrun, (FastPoisson.kroneckerSum_mulVec_vec_eq_iff hV hW hA₁ hA₂ hνμ _ B).2 rfl]
  rfl

/-- **Section 4.8.4** of [golub2013matrix]. Let $A_1 = \mathcal{T}^{(DD)}_{n_1}$,
$A_2 = \mathcal{T}^{(DD)}_{n_2}$ and $A = I_{n_2} \otimes A_1 + A_2 \otimes I_{n_1}$. Then "$A$
is symmetric positive definite with bandwidth $n_1 + 1$": $A$ is positive definite, and with the
unknowns numbered as in $\operatorname{vec}$, $A$ has lower bandwidth $n_1$ and upper bandwidth
$n_1$.

The source's bandwidth $n_1 + 1$ counts the diagonal. The Lean statement uses
`Matrix.HasLowerBandwidth` and `Matrix.HasUpperBandwidth`, under which the entry $(p, q)$
vanishes for $|p - q| > n_1$. The positional numbering reindexes $A$ by `finProdFinEquiv` from
`Fin n₂ × Fin n₁` to `Fin (n₂ * n₁)`, which puts the pair $(j, i)$ at position $i + n_1 j$.

**Reading.** The text reports bandwidth $n_1+1$. Lean bounds each off-diagonal distance by $n_1$,
which means at most $n_1+1$ diagonals per side when including the main diagonal. The Lean statement
gives support bounds without claiming they are sharp.
-/
theorem poisson2D_posDef_bandwidth (n₁ n₂ : ℕ) :
    ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ symmTridiagonalToeplitz n₁ (-1) 2
      + symmTridiagonalToeplitz n₂ (-1) 2 ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)).PosDef ∧
    (((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ symmTridiagonalToeplitz n₁ (-1) 2
      + symmTridiagonalToeplitz n₂ (-1) 2 ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm).HasLowerBandwidth n₁ ∧
    (((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ symmTridiagonalToeplitz n₁ (-1) 2
      + symmTridiagonalToeplitz n₂ (-1) 2 ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm).HasUpperBandwidth n₁ := by
  rw [one_kronecker_add_kronecker_one]
  exact ⟨posDef_kroneckerSum (posDef_symmTridiagonalToeplitz_neg_one_two n₂)
      (posDef_symmTridiagonalToeplitz_neg_one_two n₁),
    kroneckerSum_hasBandwidth _ (symmTridiagonalToeplitz_isTridiagonal (-1) 2)⟩

/-! ### §4.8.5 The inverse of the DST and DCT matrices -/

/-- **Section 4.8.5** of [golub2013matrix], the inverse of the DST matrix. Let $m \ge 1$ and
$V = \mathrm{DST}(m-1)$. Then $$V^{-1} = \frac{2}{m} \mathrm{DST}(m-1).$$

The identity follows from $2 S_{m-1}^2 = m I$ (`GolubVanLoan.Chapter04.dst_block_identities`).
The matrix $\mathrm{DST}(m-1)$ is `Matrix.dst1 (m - 1)`, with entries $\sin(k j \pi / m)$ for
$k, j = 1, \dots, m-1$. -/
theorem dst_inv {m : ℕ} (hm : 1 ≤ m) : (dst1 (m - 1))⁻¹ = (2 / m : ℝ) • dst1 (m - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by rw [Nat.cast_sub hm]; ring
  refine inv_eq_left_inv ?_
  rw [Matrix.smul_mul, dst1_mul_self, hcast, smul_smul, div_mul_div_comm, mul_comm (2 : ℝ),
    div_self (mul_ne_zero hm' two_ne_zero), one_smul]

/-- **Section 4.8.5** of [golub2013matrix], the inverse of the DCT matrix. Let $m \ge 1$ and
$V = \mathrm{DCT}(m+1)$. Then $$V^{-1} = \frac{2}{m} \mathrm{DCT}(m+1).$$

The matrix $\mathrm{DCT}(m+1)$ is `Matrix.dct1 m`, with entries $c_j \cos(k j \pi / m)$ for
$k, j = 0, \dots, m$, where $c_0 = c_m = 1/2$ and $c_j = 1$ otherwise. -/
theorem dct_inv {m : ℕ} (hm : 0 < m) : (dct1 m)⁻¹ = (2 / m : ℝ) • dct1 m := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  refine inv_eq_left_inv ?_
  rw [Matrix.smul_mul, dct1_mul_self hm, smul_smul, div_mul_div_comm, mul_comm (2 : ℝ),
    div_self (mul_ne_zero hm' two_ne_zero), one_smul]

/-- **Section 4.8.5** of [golub2013matrix]. The real vector $v = (-1, 1, \dots, (-1)^{m-1})^T \in
\mathbb{R}^{m-1}$ of Theorem 1.4.1 and §4.8.5, with $v_j = (-1)^j$ for $j = 1, \dots, m-1$.

In 0-based form, entry $j$ is $(-1)^{j+1}$. The complex form of $v$ is
`GolubVanLoan.Chapter01.altSignVec`. -/
def altSignVecReal (m : ℕ) : Fin (m - 1) → ℝ := fun j => (-1) ^ ((j : ℕ) + 1)

/-- For real $x$, $y$, $x'$ and $y'$, the real part of $(x + iy)(x' - iy')$ is $x x' + y y'$. -/
private theorem re_add_mul_sub (x y x' y' : ℝ) :
    (((x : ℂ) + I * y) * ((x' : ℂ) - I * y')).re = x * x' + y * y' := by
  simp [Complex.mul_re]

private theorem re_sub_mul_add (x y x' y' : ℝ) :
    (((x : ℂ) - I * y) * ((x' : ℂ) + I * y')).re = x * x' + y * y' := by
  simp [Complex.mul_re]

private theorem re_add_mul_add (x y x' y' : ℝ) :
    (((x : ℂ) + I * y) * ((x' : ℂ) + I * y')).re = x * x' - y * y' := by
  simp [Complex.mul_re]

private theorem re_sub_mul_sub (x y x' y' : ℝ) :
    (((x : ℂ) - I * y) * ((x' : ℂ) - I * y')).re = x * x' - y * y' := by
  simp [Complex.mul_re]

private theorem re_add_mul_ofReal (x y z : ℝ) : (((x : ℂ) + I * y) * (z : ℂ)).re = x * z := by
  simp [Complex.mul_re]

private theorem re_sub_mul_ofReal (x y z : ℝ) : (((x : ℂ) - I * y) * (z : ℂ)).re = x * z := by
  simp [Complex.mul_re]

private theorem re_I_mul_ofReal (y : ℝ) : (I * (y : ℂ)).re = 0 := by simp

private theorem re_ofReal_mul_ofReal (x y : ℝ) : ((x : ℂ) * (y : ℂ)).re = x * y := by
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

private theorem star_ofReal_sub_I_mul (x y : ℝ) : star ((x : ℂ) - I * y) = x + I * y := by
  apply Complex.ext <;> simp

private theorem star_ofReal_add_I_mul (x y : ℝ) : star ((x : ℂ) + I * y) = x - I * y := by
  apply Complex.ext <;> simp

private theorem star_ofReal' (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

section DSTBlocks

variable (m : ℕ) [NeZero m]

/-- A sum over the indices $0, \dots, 2m-1$ splits along the index blocks $\{0\}$,
$\{1, \dots, m-1\}$, $\{m\}$ and $\{m+1, \dots, 2m-1\}$ of Theorem 1.4.1. -/
private theorem sum_dftBlocks {R : Type*} [AddCommMonoid R] (f : Fin (2 * m) → R) :
    ∑ k, f k = f (dftBlockIdx₀ m 0) + ∑ t, f (dftBlockIdx₁ m t) + f (dftBlockIdx₂ m 0) +
      ∑ t, f (dftBlockIdx₃ m t) := by
  have hm := NeZero.pos m
  let g : ℕ → R := fun k => if h : k < 2 * m then f ⟨k, h⟩ else 0
  have hfg : ∀ k : Fin (2 * m), f k = g k := fun k => by simp only [g, k.isLt, ↓reduceDIte]
  rw [Finset.sum_congr rfl fun k _ => hfg k, Fin.sum_univ_eq_sum_range g]
  have h2 : 2 * m = 1 + (m - 1) + 1 + (m - 1) := by omega
  conv_lhs => rw [h2, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range, Finset.sum_range]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · have h : 0 < 2 * m := by omega
    simp only [g, h, ↓reduceDIte]
    rfl
  · refine Finset.sum_congr rfl fun t _ => ?_
    have h : 1 + (t : ℕ) < 2 * m := by omega
    simp only [g, h, ↓reduceDIte]
    congr 1
    ext
    simp only [dftBlockIdx₁, Fin.val_mk]
    omega
  · have h : 1 + (m - 1) + 0 < 2 * m := by omega
    simp only [g, h, ↓reduceDIte]
    congr 1
    ext
    simp only [dftBlockIdx₂, Fin.val_mk]
    omega
  · refine Finset.sum_congr rfl fun t _ => ?_
    have h : 1 + (m - 1) + 1 + (t : ℕ) < 2 * m := by omega
    simp only [g, h, ↓reduceDIte]
    congr 1
    ext
    simp only [dftBlockIdx₃, Fin.val_mk]
    omega

/-- Row $a$ of the second block row of $\bar F_{2m} F_{2m} = 2m I$, expanded along the four index
blocks, with the last block in reverse order. -/
private theorem fourierMatrix_row₁_sum (a : Fin (m - 1)) (k : Fin (2 * m)) :
    star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₀ m 0)) *
        fourierMatrix (2 * m) (dftBlockIdx₀ m 0) k +
      ∑ t, star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₁ m t)) *
        fourierMatrix (2 * m) (dftBlockIdx₁ m t) k +
      star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₂ m 0)) *
        fourierMatrix (2 * m) (dftBlockIdx₂ m 0) k +
      ∑ t, star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₃ m (Fin.rev t))) *
        fourierMatrix (2 * m) (dftBlockIdx₃ m (Fin.rev t)) k =
      if dftBlockIdx₁ m a = k then ((2 * m : ℕ) : ℂ) else 0 := by
  have hs := sum_dftBlocks m fun j =>
    star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) j) * fourierMatrix (2 * m) j k
  have hrev : ∑ t, star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₃ m (Fin.rev t))) *
        fourierMatrix (2 * m) (dftBlockIdx₃ m (Fin.rev t)) k =
      ∑ t, star (fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₃ m t)) *
        fourierMatrix (2 * m) (dftBlockIdx₃ m t) k :=
    Fintype.sum_equiv Fin.revPerm _ _ fun t => rfl
  rw [hrev]
  beta_reduce at hs
  rw [← hs]
  have h := congrFun (congrFun (dft_conjTranspose_mul_self (2 * m)).2 (dftBlockIdx₁ m a)) k
  rw [Matrix.mul_apply] at h
  simpa only [map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] using h

/-- **Section 4.8.5** of [golub2013matrix], the block identities. Let $m \ge 1$, let $C = C_{m-1}$
and $S = S_{m-1}$ be the matrices of (1.4.6), and let $e = (1, \dots, 1)^T \in \mathbb{R}^{m-1}$
and $v = (-1, 1, \dots, (-1)^{m-1})^T \in \mathbb{R}^{m-1}$, as in Theorem 1.4.1. Then
$$\begin{aligned}
  0 &= 2 C e + e + v, & 2m I &= 2 C^2 + 2 S^2 + e e^T + v v^T, \\
  0 &= 2 C v + e + (-1)^m v, & 0 &= 2 C^2 - 2 S^2 + e e^T + v v^T,
\end{aligned}$$
and "it follows that $2 S^2 = m I$ and $2 C^2 = m I - e e^T - v v^T$".

The source obtains the first four identities by comparing the $(2,1)$, $(2,2)$, $(2,3)$ and
$(2,4)$ blocks of $2m I = \bar F_{2m} F_{2m}$. The matrix $C$ is `Matrix.cosMatrix (m - 1)`,
with entries $\cos(k j \pi / m)$, and $S$ is `Matrix.dst1 (m - 1)`, with entries
$\sin(k j \pi / m)$, for $k, j = 1, \dots, m-1$. The vector $v$ is
`GolubVanLoan.Chapter04.altSignVecReal m`. -/
theorem dst_block_identities :
    (2 : ℝ) • (cosMatrix (m - 1) *ᵥ fun _ => 1) + (fun _ => 1) + altSignVecReal m = 0 ∧
    (2 : ℝ) • (cosMatrix (m - 1) * cosMatrix (m - 1)) + (2 : ℝ) • (dst1 (m - 1) * dst1 (m - 1)) +
        vecMulVec (fun _ : Fin (m - 1) => (1 : ℝ)) (fun _ => 1) +
        vecMulVec (altSignVecReal m) (altSignVecReal m) = (2 * m : ℝ) • 1 ∧
    (2 : ℝ) • (cosMatrix (m - 1) *ᵥ altSignVecReal m) + (fun _ => 1) +
        (-1 : ℝ) ^ m • altSignVecReal m = 0 ∧
    (2 : ℝ) • (cosMatrix (m - 1) * cosMatrix (m - 1)) - (2 : ℝ) • (dst1 (m - 1) * dst1 (m - 1)) +
        vecMulVec (fun _ : Fin (m - 1) => (1 : ℝ)) (fun _ => 1) +
        vecMulVec (altSignVecReal m) (altSignVecReal m) = 0 ∧
    (2 : ℝ) • (dst1 (m - 1) * dst1 (m - 1)) = (m : ℝ) • 1 ∧
    (2 : ℝ) • (cosMatrix (m - 1) * cosMatrix (m - 1)) =
      (m : ℝ) • 1 - vecMulVec (fun _ : Fin (m - 1) => (1 : ℝ)) (fun _ => 1) -
        vecMulVec (altSignVecReal m) (altSignVecReal m) := by
  have hm := NeZero.pos m
  set C := cosMatrix (m - 1) with hC
  set S := dst1 (m - 1) with hS
  set v := altSignVecReal m with hv
  obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩ :=
    theorem_1_4_1 m
  -- the entries of `F_{2m}` that the second block row of `F̄_{2m} F_{2m}` meets
  have e0 : ∀ k, fourierMatrix (2 * m) (dftBlockIdx₀ m 0) k = 1 := fun k => by
    rw [fourierMatrix_apply]
    simp [dftBlockIdx₀]
  have e10 : ∀ a, fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₀ m 0) = 1 := fun a => by
    simpa using congrFun (congrFun h10 a) 0
  have e11 : ∀ a t, fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₁ m t) =
      (C a t : ℂ) - I * (S a t : ℂ) := fun a t => by
    simpa [hC, hS] using congrFun (congrFun h11 a) t
  have e12 : ∀ a, fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₂ m 0) = (v a : ℂ) :=
    fun a => by simpa [hv, altSignVecReal, altSignVec] using congrFun (congrFun h12 a) 0
  have e13 : ∀ a t, fourierMatrix (2 * m) (dftBlockIdx₁ m a) (dftBlockIdx₃ m t) =
      (C a (Fin.rev t) : ℂ) + I * (S a (Fin.rev t) : ℂ) := fun a t => by
    simpa [hC, hS] using congrFun (congrFun h13 a) t
  have e20 : fourierMatrix (2 * m) (dftBlockIdx₂ m 0) (dftBlockIdx₀ m 0) = 1 := by
    simpa using congrFun (congrFun h20 0) 0
  have e21 : ∀ b, fourierMatrix (2 * m) (dftBlockIdx₂ m 0) (dftBlockIdx₁ m b) = (v b : ℂ) :=
    fun b => by simpa [hv, altSignVecReal, altSignVec] using congrFun (congrFun h21 0) b
  have e22 : fourierMatrix (2 * m) (dftBlockIdx₂ m 0) (dftBlockIdx₂ m 0) =
      (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    simpa using congrFun (congrFun h22 0) 0
  have e23 : ∀ b, fourierMatrix (2 * m) (dftBlockIdx₂ m 0) (dftBlockIdx₃ m b) =
      (v (Fin.rev b) : ℂ) := fun b => by
    simpa [hv, altSignVecReal, altSignVec] using congrFun (congrFun h23 0) b
  have e30 : ∀ t, fourierMatrix (2 * m) (dftBlockIdx₃ m t) (dftBlockIdx₀ m 0) = 1 := fun t => by
    simpa using congrFun (congrFun h30 t) 0
  have e31 : ∀ t b, fourierMatrix (2 * m) (dftBlockIdx₃ m t) (dftBlockIdx₁ m b) =
      (C (Fin.rev t) b : ℂ) + I * (S (Fin.rev t) b : ℂ) := fun t b => by
    simpa [hC, hS] using congrFun (congrFun h31 t) b
  have e32 : ∀ t, fourierMatrix (2 * m) (dftBlockIdx₃ m t) (dftBlockIdx₂ m 0) =
      (v (Fin.rev t) : ℂ) := fun t => by
    simpa [hv, altSignVecReal, altSignVec] using congrFun (congrFun h32 t) 0
  have e33 : ∀ t b, fourierMatrix (2 * m) (dftBlockIdx₃ m t) (dftBlockIdx₃ m b) =
      (C (Fin.rev t) (Fin.rev b) : ℂ) - I * (S (Fin.rev t) (Fin.rev b) : ℂ) := fun t b => by
    simpa [hC, hS] using congrFun (congrFun h33 t) b
  -- the index blocks are disjoint
  have hne0 : ∀ a, dftBlockIdx₁ m a ≠ dftBlockIdx₀ m 0 := fun a h => by
    have := congrArg Fin.val h
    simp [dftBlockIdx₁, dftBlockIdx₀] at this
  have hne2 : ∀ a, dftBlockIdx₁ m a ≠ dftBlockIdx₂ m 0 := fun a h => by
    have := congrArg Fin.val h
    simp only [dftBlockIdx₁, dftBlockIdx₂] at this
    omega
  have hne3 : ∀ a b, dftBlockIdx₁ m a ≠ dftBlockIdx₃ m b := fun a b h => by
    have := congrArg Fin.val h
    simp only [dftBlockIdx₁, dftBlockIdx₃] at this
    omega
  have heq1 : ∀ a b, dftBlockIdx₁ m a = dftBlockIdx₁ m b ↔ a = b := fun a b => by
    constructor
    · intro h
      have := congrArg Fin.val h
      simp only [dftBlockIdx₁] at this
      exact Fin.ext (by omega)
    · rintro rfl
      rfl
  -- the four block rows, real parts
  have fa : ∀ a, 2 * ∑ t, C a t + 1 + v a = 0 := by
    intro a
    have r0 := fourierMatrix_row₁_sum m a (dftBlockIdx₀ m 0)
    simp only [e0, e10, e11, e12, e13, e20, e30, Fin.rev_rev, star_one, star_ofReal',
      star_ofReal_sub_I_mul, star_ofReal_add_I_mul, mul_one] at r0
    have r := congrArg Complex.re r0
    simp only [hne0 a, ↓reduceIte, Complex.add_re, Complex.re_sum, Complex.one_re,
      Complex.zero_re, Complex.ofReal_re, Complex.sub_re, re_I_mul_ofReal, add_zero,
      sub_zero] at r
    linear_combination r
  have fb : ∀ a b, 2 * ∑ t, C a t * C t b + 2 * ∑ t, S a t * S t b + 1 + v a * v b =
      if a = b then 2 * (m : ℝ) else 0 := by
    intro a b
    have r0 := fourierMatrix_row₁_sum m a (dftBlockIdx₁ m b)
    simp only [e0, e10, e11, e12, e13, e21, e31, Fin.rev_rev, star_one, star_ofReal',
      star_ofReal_sub_I_mul, star_ofReal_add_I_mul, mul_one] at r0
    have r := congrArg Complex.re r0
    simp only [heq1, Complex.add_re, Complex.re_sum, Complex.one_re, re_add_mul_sub,
      re_sub_mul_add, re_ofReal_mul_ofReal, Finset.sum_add_distrib] at r
    split_ifs at r ⊢ with hab
    · rw [Complex.natCast_re] at r
      push_cast at r
      linear_combination r
    · rw [Complex.zero_re] at r
      linear_combination r
  have fc : ∀ a, 2 * ∑ t, C a t * v t + 1 + (-1) ^ m * v a = 0 := by
    intro a
    have r0 := fourierMatrix_row₁_sum m a (dftBlockIdx₂ m 0)
    simp only [e0, e10, e11, e12, e13, e22, e32, Fin.rev_rev, star_one, star_ofReal',
      star_ofReal_sub_I_mul, star_ofReal_add_I_mul, mul_one] at r0
    have r := congrArg Complex.re r0
    simp only [hne2 a, ↓reduceIte, Complex.add_re, Complex.re_sum, Complex.one_re,
      Complex.zero_re, re_add_mul_ofReal, re_sub_mul_ofReal, re_ofReal_mul_ofReal] at r
    linear_combination r
  have fd : ∀ a b, 2 * ∑ t, C a t * C t b - 2 * ∑ t, S a t * S t b + 1 + v a * v b = 0 := by
    intro a b
    have r0 := fourierMatrix_row₁_sum m a (dftBlockIdx₃ m (Fin.rev b))
    simp only [e0, e10, e11, e12, e13, e23, e33, Fin.rev_rev, star_one, star_ofReal',
      star_ofReal_sub_I_mul, star_ofReal_add_I_mul, mul_one] at r0
    have r := congrArg Complex.re r0
    simp only [hne3 a, ↓reduceIte, Complex.add_re, Complex.re_sum, Complex.one_re,
      Complex.zero_re, re_add_mul_add, re_sub_mul_sub, re_ofReal_mul_ofReal,
      Finset.sum_sub_distrib] at r
    linear_combination r
  -- the matrix forms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec, dotProduct,
      mul_one]
    linear_combination fa a
  · ext a b
    have h := fb a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, vecMulVec_apply,
      Matrix.one_apply, mul_one, mul_ite, mul_zero]
    split_ifs at h ⊢ <;> linear_combination h
  · funext a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec, dotProduct]
    linear_combination fc a
  · ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      vecMulVec_apply, Matrix.zero_apply, mul_one]
    linear_combination fd a b
  · ext a b
    have h := fb a b
    have h' := fd a b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one,
        mul_zero]
    split_ifs at h ⊢ <;> linear_combination (h - h') / 2
  · ext a b
    have h := fb a b
    have h' := fd a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, vecMulVec_apply]
    split_ifs at h ⊢ <;> linear_combination (h + h') / 2

end DSTBlocks

/-! ### §4.8.6 Four fast eigenvalue decompositions -/

/-- The identity $2 - 2 \cos\theta = 4 \sin^2(\theta/2)$, in the form $2 + 2 \cdot (-1) \cos\theta$
that the Toeplitz lemmas produce. -/
private theorem two_sub_two_mul_cos' (θ : ℝ) :
    2 + 2 * (-1) * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [← Real.two_sub_two_mul_cos]
  ring

/-- **Equation (4.8.16)** of [golub2013matrix]. Let $n \ge 1$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then $$\mathcal{T}^{(DD)}_n s(\theta) = \lambda s(\theta) +
s_{n+1} e_n,$$ where $s(\theta) = (s_1, \dots, s_n)^T$ with $s_k = \sin(k\theta)$ is the sine
vector of (4.8.15). -/
theorem equation_4_8_16 {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    symmTridiagonalToeplitz n (-1) 2 *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
        Real.sin ((n + 1) * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
  rw [symmTridiagonalToeplitz_mulVec_sinAngleVec (-1) 2 hn, two_sub_two_mul_cos', neg_one_mul,
    neg_smul, sub_neg_eq_add]

/-- **Equation (4.8.17)** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then $$\mathcal{T}^{(DD)}_n c(\theta) = \lambda c(\theta) + c_1
e_1 + c_n e_n,$$ where $c(\theta) = (c_0, \dots, c_{n-1})^T$ with $c_k = \cos(k\theta)$ is the
cosine vector of (4.8.15). -/
theorem equation_4_8_17 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    symmTridiagonalToeplitz n (-1) 2 *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        Real.cos θ • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        Real.cos (n * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
  rw [symmTridiagonalToeplitz_mulVec_cosAngleVec (-1) 2 hn, two_sub_two_mul_cos', neg_one_mul,
    neg_one_mul, neg_smul, neg_smul, sub_neg_eq_add, sub_neg_eq_add]

/-- **Equation (4.8.18)** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then, with the sine vector $s(\theta)$ of (4.8.15),
$$\mathcal{T}^{(DN)}_n s(\theta) = \lambda s(\theta) + (s_{n+1} - s_{n-1}) e_n.$$
-/
theorem equation_4_8_18 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferenceDN n *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
        (Real.sin ((n + 1) * θ) - Real.sin ((n - 1) * θ)) •
          Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferenceDN_mulVec_sinAngleVec hn θ

/-- **Equation (4.8.19)** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then, with the cosine vector $c(\theta)$ of (4.8.15),
$$\mathcal{T}^{(NN)}_n c(\theta) = \lambda c(\theta) + (c_n - c_{n-2}) e_n.$$
-/
theorem equation_4_8_19 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferenceNN n *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        (Real.cos (n * θ) - Real.cos ((n - 2) * θ)) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferenceNN_mulVec_cosAngleVec hn θ

/-- **Equation (4.8.20)** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then, with the sine vector $s(\theta)$ of (4.8.15),
$$\mathcal{T}^{(P)}_n s(\theta) = \lambda s(\theta) - s_n e_1 + (s_{n+1} - s_1) e_n.$$
-/
theorem equation_4_8_20 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferencePeriodic n *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ -
        Real.sin (n * θ) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        (Real.sin ((n + 1) * θ) - Real.sin θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferencePeriodic_mulVec_sinAngleVec hn θ

/-- **Equation (4.8.21)** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Then, with the cosine vector $c(\theta)$ of (4.8.15),
$$\mathcal{T}^{(P)}_n c(\theta) = \lambda c(\theta) + (c_1 - c_{n-1}) e_1 + (c_n - 1) e_n.$$
-/
theorem equation_4_8_21 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferencePeriodic n *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        (Real.cos θ - Real.cos ((n - 1) * θ)) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        (Real.cos (n * θ) - 1) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferencePeriodic_mulVec_cosAngleVec hn θ

/-- **Lemma 4.8.3** of [golub2013matrix]. Let $n \ge 2$, let $\theta$ be real, and let
$\lambda = 4 \sin^2(\theta/2)$. Let $s(\theta) = (s_1, \dots, s_n)^T$ and
$c(\theta) = (c_0, \dots, c_{n-1})^T$ be the real vectors of (4.8.15), with
$s_k = \sin(k\theta)$ and $c_k = \cos(k\theta)$. Then the six identities (4.8.16)–(4.8.21) hold:
$$\begin{aligned}
  \mathcal{T}^{(DD)}_n s(\theta) &= \lambda s(\theta) + s_{n+1} e_n, \\
  \mathcal{T}^{(DD)}_n c(\theta) &= \lambda c(\theta) + c_1 e_1 + c_n e_n, \\
  \mathcal{T}^{(DN)}_n s(\theta) &= \lambda s(\theta) + (s_{n+1} - s_{n-1}) e_n, \\
  \mathcal{T}^{(NN)}_n c(\theta) &= \lambda c(\theta) + (c_n - c_{n-2}) e_n, \\
  \mathcal{T}^{(P)}_n s(\theta) &= \lambda s(\theta) - s_n e_1 + (s_{n+1} - s_1) e_n, \\
  \mathcal{T}^{(P)}_n c(\theta) &= \lambda c(\theta) + (c_1 - c_{n-1}) e_1 + (c_n - 1) e_n.
\end{aligned}$$

The vectors $s(\theta)$ and $c(\theta)$ are `Matrix.sinAngleVec n θ` and
`Matrix.cosAngleVec n θ`. -/
theorem lemma_4_8_3 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    symmTridiagonalToeplitz n (-1) 2 *ᵥ sinAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
          Real.sin ((n + 1) * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 ∧
      symmTridiagonalToeplitz n (-1) 2 *ᵥ cosAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
          Real.cos θ • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
          Real.cos (n * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 ∧
      secondDifferenceDN n *ᵥ sinAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
          (Real.sin ((n + 1) * θ) - Real.sin ((n - 1) * θ)) •
            Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 ∧
      secondDifferenceNN n *ᵥ cosAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
          (Real.cos (n * θ) - Real.cos ((n - 2) * θ)) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 ∧
      secondDifferencePeriodic n *ᵥ sinAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ -
          Real.sin (n * θ) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
          (Real.sin ((n + 1) * θ) - Real.sin θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 ∧
      secondDifferencePeriodic n *ᵥ cosAngleVec n θ =
        (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
          (Real.cos θ - Real.cos ((n - 1) * θ)) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
          (Real.cos (n * θ) - 1) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  ⟨equation_4_8_16 (by omega) θ, equation_4_8_17 hn θ, equation_4_8_18 hn θ,
    equation_4_8_19 hn θ, equation_4_8_20 hn θ, equation_4_8_21 hn θ⟩

/-- If $V$ is nonsingular and $A V = V \operatorname{diag}(\gamma)$, then
$V^{-1} A V = \operatorname{diag}(\gamma)$. -/
private theorem inv_mul_mul_eq_diagonal {n : ℕ} {A V : Matrix (Fin n) (Fin n) ℝ} {γ : Fin n → ℝ}
    (hV : IsUnit V) (hAV : A * V = V * diagonal γ) : V⁻¹ * A * V = diagonal γ := by
  rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det V).1 hV), Matrix.one_mul]

/-- A real matrix $V$ with $V^2 = c I$ for some $c \neq 0$ is nonsingular. -/
private theorem isUnit_of_mul_self_eq_smul {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : c ≠ 0) (h : V * V = c • 1) : IsUnit V := by
  refine (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (B := c⁻¹ • V) ?_)
  rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Section 4.8.6** of [golub2013matrix], the Dirichlet–Dirichlet matrix. Let $n \ge 0$ and let
$V = V^{(DD)} = \mathrm{DST}(n)$, with entries $[V]_{kj} = \sin(k j \pi / (n+1))$ for
$k, j = 1, \dots, n$. Then each column of $V$ is an eigenvector of $\mathcal{T}^{(DD)}_n$,
$$\mathcal{T}^{(DD)}_n V(:, j) = 4 \sin^2\Bigl(\frac{j \pi}{2(n+1)}\Bigr) V(:, j), \qquad j = 1,
\dots, n,$$ the matrix $V$ is nonsingular, and $$V^{-1} \mathcal{T}^{(DD)}_n V =
\operatorname{diag}\Bigl(4 \sin^2\Bigl(\frac{j \pi}{2(n+1)}\Bigr)\Bigr)_{j=1}^{n}.$$

Column $j$ of $V$ is $s(\theta_j)$ with $\theta_j = j\pi/(n+1)$, and at $\theta_j$ the residual
$s_{n+1}$ of (4.8.16) vanishes. The matrix $V$ is `Matrix.dst1 n`, and the 0-based column `j` is
the source's column $j + 1$. -/
theorem dd_eigen (n : ℕ) :
    (∀ j : Fin n, symmTridiagonalToeplitz n (-1) 2 *ᵥ (fun k => dst1 n k j) =
        (4 * Real.sin (((j : ℕ) + 1) * π / (2 * (n + 1))) ^ 2) • fun k => dst1 n k j) ∧
      IsUnit (dst1 n) ∧
      (dst1 n)⁻¹ * symmTridiagonalToeplitz n (-1) 2 * dst1 n =
        diagonal fun j : Fin n => 4 * Real.sin (((j : ℕ) + 1) * π / (2 * (n + 1))) ^ 2 := by
  have hcol : ∀ j : Fin n, symmTridiagonalToeplitz n (-1) 2 *ᵥ (fun k => dst1 n k j) =
      (4 * Real.sin (((j : ℕ) + 1) * π / (2 * (n + 1))) ^ 2) • fun k => dst1 n k j := by
    intro j
    have hv : (fun k => dst1 n k j) = sineVec n j := funext fun k => dst1_apply_eq_sineVec k j
    rw [hv, symmTridiagonalToeplitz_mulVec_sineVec, two_sub_two_mul_cos', div_div,
      mul_comm ((n : ℝ) + 1) 2]
  have hu : IsUnit (dst1 n) :=
    isUnit_of_mul_self_eq_smul (by positivity) (dst1_mul_self n)
  exact ⟨hcol, hu, inv_mul_mul_eq_diagonal hu (mul_eq_mul_diagonal_of_forall_mulVec_col hcol)⟩

/-- **Section 4.8.6** of [golub2013matrix], the Dirichlet–Neumann matrix. Let $n \ge 2$ and
$\theta_j = (2j - 1)\pi/(2n)$ for $j = 1, \dots, n$. Then $$\mathcal{T}^{(DN)}_n s(\theta_j) = 4
\sin^2(\theta_j / 2) s(\theta_j),$$ the matrix $V = V^{(DN)}$ with entries
$[V]_{kj} = \sin(k (2j - 1) \pi / (2n))$ is $\mathrm{DST2}(n)$, so that its column $j$ is
$s(\theta_j)$, the matrix $V$ is nonsingular, and $$V^{-1} \mathcal{T}^{(DN)}_n V =
\operatorname{diag}\Bigl(4 \sin^2\Bigl(\frac{(2j - 1) \pi}{4n}\Bigr)\Bigr)_{j=1}^{n}.$$

**Typo.** The source cites "(1.4.13)" for $\mathrm{DST2}(n)$, but there is no such equation;
(1.4.12) is meant.

At $\theta_j$ the residual $s_{n+1} - s_{n-1} = 2 s_1 c_n$ of (4.8.18) vanishes. The matrix $V$
is `Matrix.dst2 n`. In 0-based form, $\theta_j = (2j + 1)\pi/(2n)$ for $j = 0, \dots, n-1$. -/
theorem dn_eigen {n : ℕ} (hn : 2 ≤ n) :
    (∀ j : Fin n, secondDifferenceDN n *ᵥ sinAngleVec n ((2 * (j : ℕ) + 1) * π / (2 * n)) =
        (4 * Real.sin ((2 * (j : ℕ) + 1) * π / (2 * n) / 2) ^ 2) •
          sinAngleVec n ((2 * (j : ℕ) + 1) * π / (2 * n))) ∧
      (∀ j : Fin n, (fun k => dst2 n k j) = sinAngleVec n ((2 * (j : ℕ) + 1) * π / (2 * n))) ∧
      IsUnit (dst2 n) ∧
      (dst2 n)⁻¹ * secondDifferenceDN n * dst2 n =
        diagonal fun j : Fin n => 4 * Real.sin ((2 * (j : ℕ) + 1) * π / (4 * n)) ^ 2 := by
  refine ⟨fun j => ?_, dst2_col_eq_sinAngleVec, isUnit_dst2 n,
    inv_dst2_mul_secondDifferenceDN_mul_dst2 hn⟩
  have h := secondDifferenceDN_mulVec_dst2_col hn j
  rw [dst2_col_eq_sinAngleVec] at h
  rw [h, div_div, show (2 * (n : ℝ) * 2) = 4 * n by ring]

/-- **Section 4.8.6** of [golub2013matrix], the Neumann–Neumann matrix. Let $m \ge 1$, $n = m + 1$,
and $\theta_j = (j - 1)\pi/(n - 1)$ for $j = 1, \dots, n$. Then $$\mathcal{T}^{(NN)}_n
c(\theta_j) = 4 \sin^2(\theta_j / 2) c(\theta_j),$$ the matrix $V = V^{(NN)}$ with entries
$[V]_{kj} = \cos((k - 1)(j - 1) \pi / (n - 1))$ is $\mathrm{DCT}(n) \operatorname{diag}(2,
I_{n-2}, 2)$, the matrix $V$ is nonsingular, and $$V^{-1} \mathcal{T}^{(NN)}_n V =
\operatorname{diag}\Bigl(4 \sin^2\Bigl(\frac{(j - 1) \pi}{2(n - 1)}\Bigr)\Bigr)_{j=1}^{n}.$$

**Typo.** In this paragraph the source twice writes $\mathcal{T}^{(DN)}$ and $V^{(DN)}$ for
$\mathcal{T}^{(NN)}$ and $V^{(NN)}$.

At $\theta_j$ the residual $c_n - c_{n-2} = -2 s_1 s_{n-1}$ of (4.8.19) vanishes. The matrix
$\mathrm{DCT}(n)$ is `Matrix.dct1 m`. In 0-based form, $\theta_j = j\pi/m$ for
$j = 0, \dots, m$. -/
theorem nn_eigen {m : ℕ} (hm : 0 < m) :
    (∀ j : Fin (m + 1), secondDifferenceNN (m + 1) *ᵥ cosAngleVec (m + 1) ((j : ℕ) * π / m) =
        (4 * Real.sin ((j : ℕ) * π / (2 * m)) ^ 2) • cosAngleVec (m + 1) ((j : ℕ) * π / m)) ∧
      (∀ k j : Fin (m + 1),
        (dct1 m * diagonal fun j : Fin (m + 1) =>
          if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1) k j =
          Real.cos ((k : ℕ) * (j : ℕ) * π / m)) ∧
      IsUnit (dct1 m * diagonal fun j : Fin (m + 1) =>
        if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1) ∧
      (dct1 m * diagonal fun j : Fin (m + 1) =>
          if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1)⁻¹ * secondDifferenceNN (m + 1) *
        (dct1 m * diagonal fun j : Fin (m + 1) =>
          if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1) =
        diagonal fun j : Fin (m + 1) => 4 * Real.sin ((j : ℕ) * π / (2 * m)) ^ 2 := by
  have hu : IsUnit (dct1 m * diagonal fun j : Fin (m + 1) =>
      if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1) := by
    refine (isUnit_dct1 hm).mul (isUnit_diagonal.2 (Pi.isUnit_iff.2 fun j => ?_))
    split_ifs <;> norm_num
  refine ⟨secondDifferenceNN_mulVec_cosAngleVec_mul_pi_div hm, fun k j => ?_, hu,
    inv_mul_mul_eq_diagonal hu (secondDifferenceNN_mul_dct1_mul_diagonal hm)⟩
  rw [dct1_mul_diagonal_apply, cosAngleVec_apply]
  congr 1
  ring

/-- **Section 4.8.6** of [golub2013matrix], the periodic matrix. Let $n \ge 3$ and $z = (2, -1, 0,
\dots, 0, -1)^T \in \mathbb{R}^n$. Then $\mathcal{T}^{(P)}_n = C(z)$, so that by Theorem 4.8.2
$$F_n^{-1} \mathcal{T}^{(P)}_n F_n = \operatorname{diag}(\lambda), \qquad \lambda = \bar F_n
z,$$ and "it can be shown that" $\lambda_j = 4 \sin^2((j - 1)\pi/n)$ for $j = 1, \dots, n$.

**Reading.** The source says that $\mathcal{T}^{(P)}_n$ is circulant, and the declaration reads
this for $n \ge 3$. For $n = 2$ the two entries $-1$ of $z$ fall on the same position, and
$\mathcal{T}^{(P)}_2$ is the circulant matrix of $(2, -2)^T$, not of $(2, -1)^T$.

The real matrix $\mathcal{T}^{(P)}_n$ enters the complex products entrywise. In 0-based form the
eigenvalues are $4 \sin^2(j\pi/n)$ for $j = 0, \dots, n-1$. -/
theorem periodic_eigen {n : ℕ} (hn : 3 ≤ n) :
    secondDifferencePeriodic n =
        circulant (fun k : Fin n => if (k : ℕ) = 0 then 2 else
          if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0) ∧
      (fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
          fourierMatrix n =
        diagonal ((fourierMatrix n).map star *ᵥ fun k : Fin n =>
          ((if (k : ℕ) = 0 then 2 else if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0 : ℝ) : ℂ)) ∧
      (fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
          fourierMatrix n =
        diagonal fun j : Fin n => ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) := by
  refine ⟨secondDifferencePeriodic_eq_circulant hn, ?_, ?_⟩
  · rw [secondDifferencePeriodic_eq_circulant hn, map_circulant, theorem_4_8_2]
  · rw [fourierMatrix]
    exact inv_conjTranspose_dft_mul_secondDifferencePeriodic_mul_conjTranspose_dft hn

/-- **Equation (4.8.22)** of [golub2013matrix]. Let $n \ge 3$, and let $\lambda_1, \dots, \lambda_n$
be the diagonal entries of $F_n^{-1} \mathcal{T}^{(P)}_n F_n$. Then $$\lambda_j =
\lambda_{n+2-j}, \qquad j = 2, \dots, n.$$

In 0-based form, the diagonal entries $j$ and $n - j$ agree for $0 < j < n$. -/
theorem equation_4_8_22 {n : ℕ} (hn : 3 ≤ n) (j : Fin n) (hj : 0 < (j : ℕ)) :
    ((fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
        fourierMatrix n) j j =
      ((fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
        fourierMatrix n) ⟨n - j, by omega⟩ ⟨n - j, by omega⟩ := by
  rw [(periodic_eigen hn).2.2, diagonal_apply_eq, diagonal_apply_eq]
  congr 1
  exact secondDifferencePeriodic_eigenvalue_symm j.isLt.le

/-- **Equation (4.8.23)** of [golub2013matrix]. For $j = 2, \dots, n$, $$\bar F_n(:, j) = F_n(:, n +
2 - j),$$ because $\omega_n^{n-k} = \bar\omega_n^k$.

In 0-based form, $\bar F_n(:, j) = F_n(:, n - j)$ for $0 < j < n$. -/
theorem equation_4_8_23 {n : ℕ} (i j : Fin n) (hj : 0 < (j : ℕ)) :
    (fourierMatrix n).map star i j = fourierMatrix n i ⟨n - j, by omega⟩ := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact conj_dft_col_eq i j hj

/-- **Equations (4.8.24)–(4.8.25)** of [golub2013matrix]. Let $n \ge 3$ and
$m = \lceil (n + 1)/2 \rceil$, and let $$V^{(P)}_n = \bigl[\operatorname{Re}(F_n(:, 1{:}m)) \mid
\operatorname{Im}(F_n(:, m+1{:}n))\bigr]$$ as in (4.8.24). Then every column of $V^{(P)}_n$ is
an eigenvector of $\mathcal{T}^{(P)}_n$: $$\mathcal{T}^{(P)}_n V^{(P)}_n(:, j) = \lambda_j
V^{(P)}_n(:, j), \qquad \lambda_j = 4 \sin^2\Bigl(\frac{(j - 1)\pi}{n}\Bigr), \qquad j = 1,
\dots, n.$$

Column $j$ of $V^{(P)}_n$, 0-based, is `Matrix.realDftCol n j`. The first part of the statement
says that it is the real part of $F_n(:, j)$ for $j < m = (n + 2)/2$ (integer division) and the
imaginary part otherwise. In 0-based form the eigenvalue is $4 \sin^2(j\pi/n)$.

**Reading.** Lean gives the real and imaginary column formulas and their eigen-equations. The source
also treats the assembled matrix as an invertible transform. This declaration does not assert that
the columns are nonzero or form a basis.
-/
theorem equation_4_8_25 {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    (∀ k : Fin n, realDftCol n j k = if (j : ℕ) < (n + 2) / 2 then (fourierMatrix n k j).re
      else (fourierMatrix n k j).im) ∧
    secondDifferencePeriodic n *ᵥ realDftCol n j =
      (4 * Real.sin ((j : ℕ) * π / n) ^ 2) • realDftCol n j := by
  refine ⟨fun k => ?_, secondDifferencePeriodic_mulVec_realDftCol hn j⟩
  rw [fourierMatrix, conjTranspose_dft_apply_eq_cos_sub_sin, realDftCol]
  split_ifs <;> simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-! ### §4.8.7 A note on symmetry and boundary conditions -/

/-- **Section 4.8.7** of [golub2013matrix]. Let $D = \operatorname{diag}(I_{n-1}, \sqrt{2}) \in
\mathbb{R}^{n \times n}$. Then "$D^{-1} \mathcal{T}^{(DN)}_n D$ is symmetric".

The statement holds for every $n$. -/
theorem dn_symmetrizable (n : ℕ) :
    ((diagonal fun i : Fin n => if (i : ℕ) + 1 = n then Real.sqrt 2 else 1)⁻¹ *
      secondDifferenceDN n *
      diagonal fun i : Fin n => if (i : ℕ) + 1 = n then Real.sqrt 2 else 1).IsSymm := by
  set d : Fin n → ℝ := fun i => if (i : ℕ) + 1 = n then Real.sqrt 2 else 1 with hd
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hdne : ∀ i, d i ≠ 0 := fun i => by
    simp only [hd]
    split_ifs
    · exact hs
    · exact one_ne_zero
  have hinv : (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hdne i)
  rw [hinv]
  refine IsSymm.ext fun i j => ?_
  simp only [diagonal_mul, mul_diagonal, hd, secondDifferenceDN, Matrix.sub_apply, of_apply,
    symmTridiagonalToeplitz_apply']
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  split_ifs <;> first | (exfalso; omega) | ring1 | (field_simp; nlinarith [h2])

end GolubVanLoan.Chapter04
