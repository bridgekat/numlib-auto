/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.ZMod`, beside the discrete Fourier transform.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.SpecialFunctions.Trigonometric.CosSum
import Numlib.Data.Matrix.Mul
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# The discrete sine and cosine transforms

This module defines the matrices of the discrete sine transforms DST-I and DST-II and of the
discrete cosine transforms DCT-I and DCT-II, following §1.4.2, §4.8.5, §4.8.6 and (12.1.13) of
[golub2013matrix]. It proves that the DST-I and the DCT-I are computed by the discrete Fourier
transform of an odd, respectively even, extension of the input vector. It proves the inversion
formulas $S_r^2 = \frac{r + 1}{2} I$ and $\mathrm{DCT}(m + 1)^2 = \frac{m}{2} I$, which make the
inverse transforms as fast as the forward ones ([golub2013matrix], §4.8.5). It also proves that
these matrices diagonalize second-difference matrices: the DST-II diagonalizes the Dirichlet–Neumann
second difference, the DCT-I the Neumann–Neumann second difference ([golub2013matrix], §4.8.6), and
the DCT-II the corner-modified tridiagonal matrix $Y_{1,1}$ of (12.1.13).

All indices start at $0$, while the matrices of [golub2013matrix] are indexed from $1$. With $k$ the
row index and $j$ the column index, the matrices are:
$$\begin{aligned}
  (S_r)_{kj} &= \sin\bigl((k + 1)(j + 1) \pi / (r + 1)\bigr), & k, j &< r, \\
  \mathrm{DST2}(n)_{kj} &= \sin\bigl((k + 1)(2j + 1) \pi / (2n)\bigr), & k, j &< n, \\
  \mathrm{DCT}(m + 1)_{kj} &= c_j \cos(k j \pi / m), & k, j &\le m, \\
  \mathrm{DCT2}(n)_{kj} &= \cos\bigl(k (2j + 1) \pi / (2n)\bigr), & k, j &< n,
\end{aligned}$$
with $c_0 = c_m = 1/2$ and $c_j = 1$ otherwise. The transform matrix of the numerical literature is
$F_N = (\omega_N^{kj})$ with $\omega_N = e^{-2 \pi i / N}$. The matrix `Matrix.dft N` of
`Numlib.Analysis.Fourier.DFT` uses the opposite root $e^{+2 \pi i / N}$, so that $F_N$ is its
conjugate transpose.

## Main definitions

* `Matrix.dst1`: the DST-I matrix $S_r$ of [golub2013matrix] (1.4.6), also $\mathrm{DST}(r)$ of
  (1.4.8). Its columns are the discrete sine vectors `Matrix.sineVec`.
* `Matrix.dst2`: the DST-II matrix $\mathrm{DST2}(n)$ of [golub2013matrix] §1.4.2, the eigenvector
  matrix of the Dirichlet–Neumann second difference.
* `Matrix.dct1`: the DCT-I matrix $\mathrm{DCT}(m + 1)$ of [golub2013matrix] (1.4.4) and (1.4.10).
* `Matrix.dct2`: the DCT-II matrix. Its rows are the vectors `Matrix.cosineIIVec`, the eigenvectors
  of $Y_{1,1}$ in [golub2013matrix] (12.1.13).
* `Matrix.cosMatrix`: the matrix $C_r = (\cos((k + 1)(j + 1) \pi / (r + 1)))$ of [golub2013matrix]
  (1.4.6), the interior block of $\mathrm{DCT}(r + 2)$.
* `Matrix.oddExtensionVec`: the odd extension $x_{\sin} = [0; x; 0; -Ex]$ of [golub2013matrix]
  (1.4.9), where $E$ reverses the order of the entries.
* `Matrix.evenExtensionVec`: the even extension $x_{\cos} = [x_0; \tilde{x}; x_m; E \tilde{x}]$ of
  [golub2013matrix] (1.4.11).

## Main results

* `Matrix.dst1_mulVec_eq_dft`: $S_r x = \frac{i}{2} (F_{2m} x_{\sin})_{1 : m - 1}$ with $m = r + 1$.
* `Matrix.dct1_mulVec_eq_dft`: $\mathrm{DCT}(m + 1) x = \frac{1}{2} (F_{2m} x_{\cos})_{0 : m}$ for
  $m > 0$.
* `Matrix.dst1_mul_self`: $S_r^2 = \frac{r + 1}{2} I$.
* `Matrix.dct1_mul_self`: $\mathrm{DCT}(m + 1)^2 = \frac{m}{2} I$ for $m > 0$.
* `Matrix.transpose_dst2_mul_dst2`: $\mathrm{DST2}(n)^T \mathrm{DST2}(n) = \frac{n}{2} I +
  \frac{1}{2} v v^T$ with $v = ((-1)^j)_j$, Problem P4.8.11(a) of [golub2013matrix].
* `Matrix.isUnit_dst2`, `Matrix.isUnit_dct1` and `Matrix.isUnit_dct2`: the DST-II, the DCT-I (for
  $m > 0$) and the DCT-II are nonsingular.
* `Matrix.dct2_mul_transpose`: $\mathrm{DCT2}(n) \mathrm{DCT2}(n)^T = \operatorname{diag}(n, n/2,
  \dots, n/2)$.
* `Matrix.dct2_mul_cornerTridiagonal_one_one_mul_inv`: $\mathrm{DCT2}(n) Y_{1,1}
  \mathrm{DCT2}(n)^{-1} = \operatorname{diag}(2 \cos(k \pi / n))$.
* `Matrix.inv_dst2_mul_secondDifferenceDN_mul_dst2`: $\mathrm{DST2}(n)^{-1} \mathcal{T}^{(DN)}_n
  \mathrm{DST2}(n) = \operatorname{diag}(4 \sin^2((2j + 1) \pi / (4n)))$ for $n \ge 2$.
* `Matrix.secondDifferenceNN_mul_dct1_mul_diagonal`: $\mathcal{T}^{(NN)}_{m + 1} V = V
  \operatorname{diag}(4 \sin^2(j \pi / (2m)))$ for $V = \mathrm{DCT}(m + 1) \operatorname{diag}(2,
  1, \dots, 1, 2)$ and $m > 0$.

## Proof outline

The two identities through the discrete Fourier transform pair the terms at $l$ and $2m - l$. The
entries of $F_{2m}$ there are complex conjugates (`Matrix.conjTranspose_dft_apply_sub_eq_conj`), so
the odd extension keeps only the sine parts, doubled, and the even extension keeps only the cosine
parts. With the radix-2 identity `Matrix.dft_radix_two`, they give the $O(m \log m)$ algorithms for
the DST and the DCT, Algorithms 1.4.2 and 1.4.3 of [golub2013matrix]. The inversion formula for
$S_r$ follows from the orthogonality of the sine vectors. The inversion formula for
$\mathrm{DCT}(m + 1)$ follows from the exactness of the trapezoidal rule on trigonometric
polynomials (`Quadrature.sum_exp_angleNode`).

## Implementation notes

* The second-difference matrices $\mathcal{T}^{(DN)}_n$ and $\mathcal{T}^{(NN)}_n$ and the
  corner-modified matrix $Y_{1,1}$ are `Matrix.secondDifferenceDN`, `Matrix.secondDifferenceNN`
  and `Matrix.cornerTridiagonal n 1 1` of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`. The
  periodic second difference and the circulant matrices are in `Numlib.Analysis.Fourier.Circulant`.
* The identities through the discrete Fourier transform are stated entrywise, for the real matrices
  embedded in the complex matrices.
-/

open Finset
open scoped Real ComplexConjugate

namespace Matrix

variable {r n m : ℕ}

/-! ### The transform matrices -/

/-- The **DST-I matrix** $S_r$ of [golub2013matrix] (1.4.6), also written $\mathrm{DST}(r)$ in
(1.4.8), with indices from $0$: the $r \times r$ real matrix with entries
$$(S_r)_{kj} = \sin\Bigl(\frac{(k + 1)(j + 1) \pi}{r + 1}\Bigr).$$
-/
noncomputable def dst1 (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  of fun (k j : Fin r) => Real.sin (((k : ℕ) + 1) * ((j : ℕ) + 1) * π / (r + 1))

/-- The entries of the DST-I matrix: $(S_r)_{kj} = \sin((k + 1)(j + 1) \pi / (r + 1))$. -/
theorem dst1_apply (k j : Fin r) :
    dst1 r k j = Real.sin (((k : ℕ) + 1) * ((j : ℕ) + 1) * π / (r + 1)) := rfl

/-- The DST-I matrix is symmetric: $S_r^T = S_r$. -/
theorem dst1_transpose (r : ℕ) : (dst1 r)ᵀ = dst1 r := by
  ext k j
  rw [transpose_apply, dst1_apply, dst1_apply]
  congr 1
  ring

/-- The columns of the DST-I matrix are the discrete sine vectors, the eigenvectors of the symmetric
tridiagonal Toeplitz matrices: for $k, j < r$, the entry $(S_r)_{kj}$ is entry $k$ of
`Matrix.sineVec r j`. -/
theorem dst1_apply_eq_sineVec (k j : Fin r) : dst1 r k j = sineVec r j k := by
  rw [dst1_apply, sineVec_apply]
  congr 1
  ring

/-- **The DST-I is its own inverse up to a factor**: for every $r \in \mathbb{N}$,
$$S_r^2 = \frac{r + 1}{2} I.$$
In [golub2013matrix], §4.8.5, this is $S_{m - 1}^{-1} = \frac{2}{m} S_{m - 1}$.

Entry $(k, l)$ of $S_r^2$ is the dot product of `Matrix.sineVec r k` and `Matrix.sineVec r l`. -/
theorem dst1_mul_self (r : ℕ) :
    dst1 r * dst1 r = (((r : ℝ) + 1) / 2) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext k l
  have h : (dst1 r * dst1 r) k l = sineVec r k ⬝ᵥ sineVec r l := by
    rw [Matrix.mul_apply, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dst1_apply, dst1_apply, sineVec_apply, sineVec_apply]
    congr 2 <;> ring
  rw [h, dotProduct_sineVec, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The **DST-II matrix** $\mathrm{DST2}(n)$ of [golub2013matrix] §1.4.2, also $V^{(DN)}_n$ of
§4.8.6, with indices from $0$: the $n \times n$ real matrix with entries
$$\mathrm{DST2}(n)_{kj} = \sin\Bigl(\frac{(k + 1)(2j + 1) \pi}{2n}\Bigr).$$
-/
noncomputable def dst2 (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun (k j : Fin n) => Real.sin (((k : ℕ) + 1) * (2 * (j : ℕ) + 1) * π / (2 * n))

/-- The entries of the DST-II matrix: $\mathrm{DST2}(n)_{kj} = \sin((k + 1)(2j + 1) \pi / (2n))$. -/
theorem dst2_apply (k j : Fin n) :
    dst2 n k j = Real.sin (((k : ℕ) + 1) * (2 * (j : ℕ) + 1) * π / (2 * n)) := rfl

/-- Column $j$ of the DST-II matrix is the sine vector $s(\theta_j)$, with entries
$s(\theta)_k = \sin((k + 1) \theta)$, at the angle $\theta_j = (2j + 1) \pi / (2n)$. -/
theorem dst2_col_eq_sinAngleVec (j : Fin n) :
    (fun k => dst2 n k j) = sinAngleVec n ((2 * (j : ℕ) + 1) * π / (2 * n)) := by
  funext k
  rw [dst2_apply, sinAngleVec_apply]
  congr 1
  ring

/-- The **DCT-II matrix** with indices from $0$: the $n \times n$ real matrix with entries
$$\mathrm{DCT2}(n)_{kj} = \cos\Bigl(\frac{k (2j + 1) \pi}{2n}\Bigr).$$

Its rows are the DCT-II vectors `Matrix.cosineIIVec n k`. The matrix $\mathcal{C}_n$ of
[golub2013matrix] (12.1.13) is $\mathrm{DCT2}(n)^T$ with its columns scaled by $\sqrt{2/n}$, and
by $\sqrt{1/n}$ for $k = 0$. -/
noncomputable def dct2 (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun (k j : Fin n) => Real.cos ((k : ℕ) * (2 * (j : ℕ) + 1) * π / (2 * n))

/-- The entries of the DCT-II matrix are those of the DCT-II vectors: $\mathrm{DCT2}(n)_{kj}$ is
entry $j$ of `Matrix.cosineIIVec n k`. -/
theorem dct2_apply (k j : Fin n) : dct2 n k j = cosineIIVec n k j := by
  rw [dct2, of_apply, cosineIIVec_apply]
  congr 1
  ring

/-- The auxiliary matrix $C_r$ of [golub2013matrix] (1.4.6), with indices from $0$: the $r \times r$
real matrix with entries
$$(C_r)_{kj} = \cos\Bigl(\frac{(k + 1)(j + 1) \pi}{r + 1}\Bigr).$$
It is the interior block of the DCT-I matrix $\mathrm{DCT}(r + 2)$. -/
noncomputable def cosMatrix (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  of fun (k j : Fin r) => Real.cos (((k : ℕ) + 1) * ((j : ℕ) + 1) * π / (r + 1))

/-- The entries of $C_r$: $(C_r)_{kj} = \cos((k + 1)(j + 1) \pi / (r + 1))$. -/
theorem cosMatrix_apply (k j : Fin r) :
    cosMatrix r k j = Real.cos (((k : ℕ) + 1) * ((j : ℕ) + 1) * π / (r + 1)) := rfl

/-- The matrix $C_r$ is symmetric: $C_r^T = C_r$. -/
theorem cosMatrix_transpose (r : ℕ) : (cosMatrix r)ᵀ = cosMatrix r := by
  ext k j
  rw [transpose_apply, cosMatrix_apply, cosMatrix_apply]
  congr 1
  ring

/-- The **DCT-I matrix** $\mathrm{DCT}(m + 1)$ of [golub2013matrix] (1.4.10), with indices from $0$:
the $(m + 1) \times (m + 1)$ real matrix with entries
$$\mathrm{DCT}(m + 1)_{kj} = c_j \cos\Bigl(\frac{k j \pi}{m}\Bigr), \qquad c_0 = c_m =
  \frac{1}{2}, \quad c_j = 1 \text{ otherwise}.$$
It is the matrix of the transform (1.4.4)
$$y_k = \frac{x_0}{2} + \sum_{j = 1}^{m - 1} \cos\Bigl(\frac{k j \pi}{m}\Bigr) x_j +
  \frac{(-1)^k x_m}{2}.$$

For $m = 0$ the formula gives the $1 \times 1$ matrix $(1/2)$. -/
noncomputable def dct1 (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  of fun (k j : Fin (m + 1)) =>
    (if (j : ℕ) = 0 ∨ (j : ℕ) = m then 1 / 2 else 1) * Real.cos ((k : ℕ) * (j : ℕ) * π / m)

/-- The entries of the DCT-I matrix: $\mathrm{DCT}(m + 1)_{kj} = c_j \cos(k j \pi / m)$, with
$c_0 = c_m = 1/2$ and $c_j = 1$ otherwise. -/
theorem dct1_apply (k j : Fin (m + 1)) :
    dct1 m k j
      = (if (j : ℕ) = 0 ∨ (j : ℕ) = m then 1 / 2 else 1) * Real.cos ((k : ℕ) * (j : ℕ) * π / m) :=
  rfl

/-- The **odd extension** of $x \in \mathbb{R}^r$ to a vector of length $2(r + 1)$: the vector
$x_{\sin} = [0; x; 0; -Ex]$ of [golub2013matrix] (1.4.9) with $m = r + 1$, where $E$ reverses
the order of the entries. With indices from $0$, entry $l$ is $x_{l - 1}$ for $1 \le l \le r$,
$-x_{2r + 1 - l}$ for $l \ge r + 2$, and $0$ for $l = 0$ and $l = r + 1$. -/
noncomputable def oddExtensionVec (x : Fin r → ℝ) : Fin (2 * (r + 1)) → ℝ := fun l =>
  if h : 0 < (l : ℕ) ∧ (l : ℕ) ≤ r then x ⟨(l : ℕ) - 1, by omega⟩
  else if h' : r + 2 ≤ (l : ℕ) then -x ⟨2 * r + 1 - (l : ℕ), by have := l.isLt; omega⟩ else 0

/-- The **even extension** of $x \in \mathbb{R}^{m + 1}$ to a vector of length $2m$: the vector
$x_{\cos} = [x_0; \tilde{x}; x_m; E \tilde{x}]$ of [golub2013matrix] (1.4.11), where $\tilde{x}$
is the interior of $x$ and $E$ reverses the order of the entries. With indices from $0$, entry
$l$ is $x_l$ for $l \le m$ and $x_{2m - l}$ for $l > m$. -/
noncomputable def evenExtensionVec (x : Fin (m + 1) → ℝ) : Fin (2 * m) → ℝ := fun l =>
  if h : (l : ℕ) ≤ m then x ⟨l, by omega⟩ else x ⟨2 * m - (l : ℕ), by omega⟩

/-! ### Folding a sum over a full period -/

/-- A sum over $0, \dots, 2m + 1$ equals the sum of the unpaired terms at $0$ and $m + 1$ and of the
pairs at $i + 1$ and $2m + 1 - i$ for $i < m$. -/
private theorem sum_range_two_mul_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ l ∈ range (2 * (m + 1)), f l
      = f 0 + f (m + 1) + ∑ i ∈ range m, (f (i + 1) + f (2 * m + 1 - i)) := by
  rw [show 2 * (m + 1) = (m + 2) + m by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Finset.sum_range_succ', Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun i => f (m + 2 + i)) m]
  have h : ∀ i ∈ range m, f (m + 2 + (m - 1 - i)) = f (2 * m + 1 - i) := fun i hi => by
    have := mem_range.mp hi
    congr 1
    omega
  rw [Finset.sum_congr rfl h]
  abel

/-- A sum over $m + 2$ indices equals the sum of its two end terms and of the $m$ interior terms. -/
private theorem sum_fin_succ_succ {M : Type*} [AddCommMonoid M] (f : Fin (m + 2) → M) :
    ∑ j, f j = f 0 + f (Fin.last (m + 1)) + ∑ i : Fin m, f i.castSucc.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
  abel

/-- In row $k$ of $F_{2(m + 1)}$, the entry in column $2(m + 1) - l$ is the complex conjugate of the
entry in column $l$, for $l = i + 1$ with $i < m$. -/
private theorem conjTranspose_dft_apply_reflect {m : ℕ} (k : Fin (2 * (m + 1))) {i : ℕ}
    (hi : i < m) :
    (dft (2 * (m + 1)))ᴴ k ⟨2 * m + 1 - i, by omega⟩
      = conj ((dft (2 * (m + 1)))ᴴ k ⟨i + 1, by omega⟩) := by
  rw [← conjTranspose_dft_apply_sub_eq_conj k ⟨i + 1, by omega⟩ (by simp)]
  congr 2
  simp only
  omega

/-- Entry $(k, l)$ of $F_N$ is $\cos(2 \pi k l / N) - i \sin(2 \pi k l / N)$, for a column $l < N$
given as a natural number. -/
private theorem conjTranspose_dft_apply_eq {N : ℕ} (k : Fin N) {l : ℕ} (hl : l < N) :
    (dft N)ᴴ k ⟨l, hl⟩ = (Real.cos (2 * π * (k : ℕ) * l / N) : ℂ)
      - Complex.I * (Real.sin (2 * π * (k : ℕ) * l / N) : ℂ) :=
  conjTranspose_dft_apply_eq_cos_sub_sin k ⟨l, hl⟩

/-- For real $c$ and $s$, the number $z = c - is$ satisfies $z + \bar{z} = 2c$. -/
private theorem cos_sub_I_mul_sin_add_conj (c s : ℝ) :
    ((c : ℂ) - Complex.I * s) + conj ((c : ℂ) - Complex.I * s) = 2 * c := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem cos_sub_I_mul_sin_sub_conj (c s : ℝ) :
    ((c : ℂ) - Complex.I * s) - conj ((c : ℂ) - Complex.I * s) = -2 * Complex.I * s := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ### The sine and cosine transforms through the discrete Fourier transform -/

/-- **The DST through the DFT**: the discrete sine transform of a vector is a scaled part of the
discrete Fourier transform of its odd extension. Let $x \in \mathbb{R}^r$ and $m = r + 1$. Then,
for $0 \le k < r$,
$$(S_r x)_k = \frac{i}{2} \, (F_{2m} x_{\sin})_{k + 1},$$
that is, $S_r x = \frac{i}{2} (F_{2m} x_{\sin})_{1 : m - 1}$. This is the display after (1.4.9)
in [golub2013matrix], §1.4.2, and the correctness of Algorithm 1.4.2.

The odd extension is `Matrix.oddExtensionVec x`, embedded in the complex vectors. The transform
matrix is `(dft (2 * (r + 1)))ᴴ`. -/
theorem dst1_mulVec_eq_dft (x : Fin r → ℝ) (k : Fin r) :
    (((dst1 r *ᵥ x) k : ℝ) : ℂ) = (Complex.I / 2) * (((dft (2 * (r + 1)))ᴴ *ᵥ
      fun l => (oddExtensionVec x l : ℂ)) ⟨(k : ℕ) + 1, by omega⟩) := by
  set k' : Fin (2 * (r + 1)) := ⟨(k : ℕ) + 1, by omega⟩ with hk'
  set G : ℕ → ℂ := fun l => if h : l < 2 * (r + 1) then
    (dft (2 * (r + 1)))ᴴ k' ⟨l, h⟩ * (oddExtensionVec x ⟨l, h⟩ : ℂ) else 0 with hG
  have hRHS : ((dft (2 * (r + 1)))ᴴ *ᵥ fun l => (oddExtensionVec x l : ℂ)) k'
      = ∑ l ∈ range (2 * (r + 1)), G l := by
    rw [mulVec_apply_eq_sum, Finset.sum_fin_eq_sum_range]
  set θ : ℕ → ℝ := fun l => 2 * π * ((k' : ℕ) : ℝ) * l / ((2 * (r + 1) : ℕ) : ℝ) with hθ
  have hF : ∀ {l : ℕ} (hl : l < 2 * (r + 1)),
      (dft (2 * (r + 1)))ᴴ k' ⟨l, hl⟩ = (Real.cos (θ l) : ℂ) - Complex.I * (Real.sin (θ l) : ℂ) :=
    fun hl => conjTranspose_dft_apply_eq k' hl
  -- the two unpaired terms vanish
  have hG0 : G 0 = 0 := by
    simp only [hG, dite_eq_left (by omega : 0 < 2 * (r + 1))]
    simp [oddExtensionVec]
  have hGm : G (r + 1) = 0 := by
    simp only [hG, dite_eq_left (by omega : r + 1 < 2 * (r + 1))]
    simp [oddExtensionVec]
  -- the pairs `l = i + 1` and `2 m − l` give `−2 i sin` times `x i`
  have hpair : ∀ i : Fin r, G ((i : ℕ) + 1) + G (2 * r + 1 - (i : ℕ))
      = -2 * Complex.I * (Real.sin (θ ((i : ℕ) + 1)) : ℂ) * (x i : ℂ) := by
    intro i
    have hi := i.isLt
    have hx1 : oddExtensionVec x ⟨(i : ℕ) + 1, by omega⟩ = x i := by
      simp only [oddExtensionVec]
      rw [dite_eq_left (by constructor <;> omega)]
      exact congrArg x (Fin.ext (Nat.add_sub_cancel _ _))
    have hx2 : oddExtensionVec x ⟨2 * r + 1 - (i : ℕ), by omega⟩ = -x i := by
      simp only [oddExtensionVec]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      exact congrArg (fun y => -x y) (Fin.ext (by simp only; omega))
    simp only [hG, dite_eq_left (by omega : (i : ℕ) + 1 < 2 * (r + 1)),
      dite_eq_left (by omega : 2 * r + 1 - (i : ℕ) < 2 * (r + 1))]
    rw [hx1, hx2, conjTranspose_dft_apply_reflect k' hi, hF, Complex.ofReal_neg]
    linear_combination (x i : ℂ) * cos_sub_I_mul_sin_sub_conj (Real.cos (θ ((i : ℕ) + 1)))
      (Real.sin (θ ((i : ℕ) + 1)))
  rw [hRHS, sum_range_two_mul_succ, hG0, hGm, zero_add, zero_add,
    Finset.sum_range fun i => G (i + 1) + G (2 * r + 1 - i),
    Finset.sum_congr rfl fun i _ => hpair i, Finset.mul_sum, mulVec_apply_eq_sum,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dst1_apply, Complex.ofReal_mul]
  have hang : θ ((i : ℕ) + 1) = ((k : ℕ) + 1) * ((i : ℕ) + 1) * π / (r + 1) := by
    simp only [hθ, hk']
    push_cast
    field_simp
  rw [hang]
  linear_combination ((Real.sin (((k : ℕ) + 1) * ((i : ℕ) + 1) * π / (r + 1)) : ℂ)
    * (x i : ℂ)) * Complex.I_sq

/-- **The DCT through the DFT**: the discrete cosine transform of a vector is a scaled part of the
discrete Fourier transform of its even extension. Let $m > 0$ and $x \in \mathbb{R}^{m + 1}$.
Then, for $0 \le k \le m$,
$$(\mathrm{DCT}(m + 1) x)_k = \frac{1}{2} \, (F_{2m} x_{\cos})_k,$$
that is, $\mathrm{DCT}(m + 1) x = \frac{1}{2} (F_{2m} x_{\cos})_{0 : m}$. This is the display
after (1.4.11) in [golub2013matrix], §1.4.2, and the correctness of Algorithm 1.4.3.

The even extension is `Matrix.evenExtensionVec x`, embedded in the complex vectors. The
transform matrix is `(dft (2 * m))ᴴ`. -/
theorem dct1_mulVec_eq_dft (hm : 0 < m) (x : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    (((dct1 m *ᵥ x) k : ℝ) : ℂ) = (1 / 2) * (((dft (2 * m))ᴴ *ᵥ
      fun l => (evenExtensionVec x l : ℂ)) ⟨k, by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set k' : Fin (2 * (m + 1)) := ⟨k, by omega⟩ with hk'
  set G : ℕ → ℂ := fun l => if h : l < 2 * (m + 1) then
    (dft (2 * (m + 1)))ᴴ k' ⟨l, h⟩ * (evenExtensionVec x ⟨l, h⟩ : ℂ) else 0 with hG
  have hRHS : ((dft (2 * (m + 1)))ᴴ *ᵥ fun l => (evenExtensionVec x l : ℂ)) k'
      = ∑ l ∈ range (2 * (m + 1)), G l := by
    rw [mulVec_apply_eq_sum, Finset.sum_fin_eq_sum_range]
  set θ : ℕ → ℝ := fun l => 2 * π * ((k' : ℕ) : ℝ) * l / ((2 * (m + 1) : ℕ) : ℝ) with hθ
  have hF : ∀ {l : ℕ} (hl : l < 2 * (m + 1)),
      (dft (2 * (m + 1)))ᴴ k' ⟨l, hl⟩ = (Real.cos (θ l) : ℂ) - Complex.I * (Real.sin (θ l) : ℂ) :=
    fun hl => conjTranspose_dft_apply_eq k' hl
  have hθ0 : θ 0 = 0 := by simp [hθ]
  have hθm : θ (m + 1) = (k : ℕ) * π := by
    simp only [hθ, hk']
    push_cast
    field_simp
  -- the unpaired terms
  have hG0 : G 0 = (x 0 : ℂ) := by
    simp only [hG, dite_eq_left (by omega : 0 < 2 * (m + 1)), hF, hθ0, Real.cos_zero,
      Real.sin_zero, Complex.ofReal_zero, Complex.ofReal_one, mul_zero, sub_zero, one_mul]
    exact congrArg (fun y : ℝ => (y : ℂ)) (dite_eq_left (Nat.zero_le _))
  have hGm : G (m + 1) = (Real.cos ((k : ℕ) * π) : ℂ) * (x (Fin.last (m + 1)) : ℂ) := by
    simp only [hG, dite_eq_left (by omega : m + 1 < 2 * (m + 1)), hF, hθm, Real.sin_nat_mul_pi,
      Complex.ofReal_zero, mul_zero, sub_zero]
    exact congrArg (fun y : ℝ => (Real.cos ((k : ℕ) * π) : ℂ) * (y : ℂ))
      (dite_eq_left (le_refl _))
  -- the pairs `l = i + 1` and `2 m − l` give `2 cos` times `x (i + 1)`
  have hpair : ∀ i : Fin m, G ((i : ℕ) + 1) + G (2 * m + 1 - (i : ℕ))
      = 2 * ((Real.cos (θ ((i : ℕ) + 1)) : ℂ) * (x i.castSucc.succ : ℂ)) := by
    intro i
    have hi := i.isLt
    have hx1 : evenExtensionVec x ⟨(i : ℕ) + 1, by omega⟩ = x i.castSucc.succ :=
      dite_eq_left (by simp only; omega)
    have hx2 : evenExtensionVec x ⟨2 * m + 1 - (i : ℕ), by omega⟩ = x i.castSucc.succ := by
      simp only [evenExtensionVec]
      rw [dite_eq_right (by omega)]
      exact congrArg x (Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
    simp only [hG, dite_eq_left (by omega : (i : ℕ) + 1 < 2 * (m + 1)),
      dite_eq_left (by omega : 2 * m + 1 - (i : ℕ) < 2 * (m + 1))]
    rw [hx1, hx2, conjTranspose_dft_apply_reflect k' hi, hF]
    linear_combination (x i.castSucc.succ : ℂ) * cos_sub_I_mul_sin_add_conj
      (Real.cos (θ ((i : ℕ) + 1))) (Real.sin (θ ((i : ℕ) + 1)))
  -- the three kinds of terms of the cosine transform
  have h0 : dct1 (m + 1) k 0 * x 0 = x 0 / 2 := by
    rw [dct1_apply, ite_eq_left (Or.inl (Fin.val_zero _))]
    simp
    ring
  have hl : dct1 (m + 1) k (Fin.last (m + 1)) * x (Fin.last (m + 1))
      = Real.cos ((k : ℕ) * π) * x (Fin.last (m + 1)) / 2 := by
    rw [dct1_apply, ite_eq_left (Or.inr (Fin.val_last _)), Fin.val_last]
    have hm' : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((k : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ) = (k : ℕ) * π by
      field_simp]
    ring
  have hint : ∀ i : Fin m, dct1 (m + 1) k i.castSucc.succ * x i.castSucc.succ
      = Real.cos (θ ((i : ℕ) + 1)) * x i.castSucc.succ := by
    intro i
    have hi := i.isLt
    rw [dct1_apply, ite_eq_right (by simp only [Fin.val_succ, Fin.val_castSucc]; omega), one_mul]
    congr 2
    simp only [hθ, hk', Fin.val_succ, Fin.val_castSucc]
    push_cast
    field_simp
  rw [hRHS, sum_range_two_mul_succ, hG0, hGm,
    Finset.sum_range fun i => G (i + 1) + G (2 * m + 1 - i),
    Finset.sum_congr rfl fun i _ => hpair i, ← Finset.mul_sum, mulVec_apply_eq_sum,
    sum_fin_succ_succ, h0, hl, Finset.sum_congr rfl fun i _ => hint i]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

/-! ### Inversion -/

/-- The trapezoidal rule over a full period is exact for $\cos(p l \pi / m)$: for $m > 0$ and
$p \in \mathbb{Z}$, $\sum_{l = 0}^{2m - 1} \cos(p l \pi / m)$ is $2m$ if $2m$ divides $p$ and
$0$ otherwise. -/
private theorem sum_range_cos_int_mul (hm : 0 < m) (p : ℤ) :
    ∑ l ∈ range (2 * m), Real.cos (p * l * π / m)
      = if (2 * m : ℤ) ∣ p then (2 * m : ℝ) else 0 := by
  have h := congrArg Complex.re (Quadrature.sum_exp_angleNode (N := 2 * m) (by omega) p)
  rw [Complex.re_sum] at h
  have hterm : ∀ l ∈ range (2 * m),
      (Complex.exp (p * (Quadrature.angleNode (2 * m) l : ℝ) * Complex.I)).re
        = Real.cos (p * l * π / m) := by
    intro l _
    rw [show (p : ℂ) * ((Quadrature.angleNode (2 * m) l : ℝ) : ℂ) * Complex.I
        = ((p * Quadrature.angleNode (2 * m) l : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
    congr 1
    have hm' : (m : ℝ) ≠ 0 := by positivity
    simp only [Quadrature.angleNode]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm] at h
  rw [h]
  push_cast
  split_ifs <;> simp

/-- The trapezoidal rule with the weights $\frac{1}{2}, 1, \dots, 1, \frac{1}{2}$ of the DCT-I is
exact for $\cos(p j \pi / m)$: for $m > 0$ and $p \in \mathbb{Z}$, the weighted sum over
$j = 0, \dots, m$ is $m$ if $2m$ divides $p$ and $0$ otherwise. -/
private theorem sum_dct1Weight_mul_cos (hm : 0 < m) (p : ℤ) :
    ∑ j : Fin (m + 1), (if (j : ℕ) = 0 ∨ (j : ℕ) = m then (1 / 2 : ℝ) else 1)
        * Real.cos (p * (j : ℕ) * π / m) = if (2 * m : ℤ) ∣ p then (m : ℝ) else 0 := by
  have hfull := sum_range_cos_int_mul hm p
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [sum_range_two_mul_succ] at hfull
  -- the reflected terms of the full period repeat the first half
  have hrefl : ∀ i ∈ range m, Real.cos (p * ((2 * m + 1 - i : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ))
      = Real.cos (p * ((i + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ)) := by
    intro i hi
    have hi' := mem_range.mp hi
    rw [Nat.cast_sub (by omega), ← Real.cos_int_mul_two_pi_sub _ p]
    congr 1
    push_cast
    field_simp
    ring
  simp only [Finset.sum_add_distrib] at hfull
  rw [Finset.sum_congr rfl hrefl, ← two_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div,
    Real.cos_zero] at hfull
  rw [sum_fin_succ_succ]
  simp only [Fin.val_zero, Fin.val_last, Fin.val_succ, Fin.val_castSucc, true_or, or_true,
    ite_true, Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero]
  have hint : ∀ i : Fin m, (if (i : ℕ) + 1 = 0 ∨ (i : ℕ) + 1 = m + 1 then (1 / 2 : ℝ) else 1)
      * Real.cos (p * (((i : ℕ) + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ))
      = Real.cos (p * (((i : ℕ) + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ)) := by
    intro i
    have := i.isLt
    rw [ite_eq_right (by omega), one_mul]
  rw [Finset.sum_congr rfl fun i _ => hint i,
    ← Finset.sum_range fun i => Real.cos (p * ((i + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ))]
  have hsplit : ∀ c : ℝ, (if (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ∣ p then c else 0) * 2
      = if (2 * ((m + 1 : ℕ) : ℤ) : ℤ) ∣ p then 2 * c else 0 := by
    intro c
    split_ifs <;> ring
  push_cast at hfull ⊢
  split_ifs at hfull ⊢ <;> linarith

/-- **The DCT-I is its own inverse up to a factor**: for $m > 0$,
$$\mathrm{DCT}(m + 1)^2 = \frac{m}{2} I.$$
In [golub2013matrix], §4.8.5, this is $\mathrm{DCT}(m + 1)^{-1} = \frac{2}{m} \mathrm{DCT}(m +
1)$. It is the counterpart of `Matrix.dst1_mul_self`.

Entry $(k, l)$ is $c_l \sum_j c_j \cos(k j \pi / m) \cos(j l \pi / m)$. The product of the
cosines is half the sum of $\cos((k - l) j \pi / m)$ and $\cos((k + l) j \pi / m)$, and the
weighted sums of these are exact trapezoidal rules. -/
theorem dct1_mul_self (hm : 0 < m) :
    dct1 m * dct1 m = ((m : ℝ) / 2) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
  ext k l
  set w : Fin (m + 1) → ℝ := fun j => if (j : ℕ) = 0 ∨ (j : ℕ) = m then 1 / 2 else 1 with hw
  have hentry : (dct1 m * dct1 m) k l = w l / 2 *
      ((∑ j : Fin (m + 1), w j * Real.cos (((k : ℤ) - l : ℤ) * (j : ℕ) * π / m))
        + ∑ j : Fin (m + 1), w j * Real.cos (((k : ℤ) + l : ℤ) * (j : ℕ) * π / m)) := by
    rw [Matrix.mul_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dct1_apply, dct1_apply]
    have hc : Real.cos ((k : ℕ) * (j : ℕ) * π / m) * Real.cos ((j : ℕ) * (l : ℕ) * π / m)
        = (Real.cos (((k : ℤ) - l : ℤ) * (j : ℕ) * π / m)
          + Real.cos (((k : ℤ) + l : ℤ) * (j : ℕ) * π / m)) / 2 := by
      push_cast
      rw [show ((k : ℕ) - (l : ℕ) : ℝ) * (j : ℕ) * π / m
          = (k : ℕ) * (j : ℕ) * π / m - (j : ℕ) * (l : ℕ) * π / m by ring,
        show ((k : ℕ) + (l : ℕ) : ℝ) * (j : ℕ) * π / m
          = (k : ℕ) * (j : ℕ) * π / m + (j : ℕ) * (l : ℕ) * π / m by ring,
        Real.cos_sub, Real.cos_add]
      ring
    simp only [hw]
    linear_combination (if (j : ℕ) = 0 ∨ (j : ℕ) = m then (1 / 2 : ℝ) else 1)
      * (if (l : ℕ) = 0 ∨ (l : ℕ) = m then (1 / 2 : ℝ) else 1) * hc
  rw [hentry, sum_dct1Weight_mul_cos hm, sum_dct1Weight_mul_cos hm, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hk := k.isLt
  have hl := l.isLt
  -- `2 m ∣ k − l` exactly when `k = l`, and `2 m ∣ k + l` exactly when `k = l ∈ {0, m}`
  have hsub : (2 * m : ℤ) ∣ ((k : ℤ) - l) ↔ k = l := by
    constructor
    · intro h
      have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      exact Fin.ext (by omega)
    · rintro rfl
      simp
  have hadd : (2 * m : ℤ) ∣ ((k : ℤ) + l) ↔ k = l ∧ ((l : ℕ) = 0 ∨ (l : ℕ) = m) := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : 0 ≤ c := by nlinarith
      have hc1 : c ≤ 1 := by nlinarith
      rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · exact ⟨Fin.ext (by omega), Or.inl (by omega)⟩
      · exact ⟨Fin.ext (by omega), Or.inr (by omega)⟩
    · rintro ⟨rfl, h | h⟩
      · exact ⟨0, by omega⟩
      · exact ⟨1, by omega⟩
  by_cases hkl : k = l
  · subst hkl
    by_cases hb : (k : ℕ) = 0 ∨ (k : ℕ) = m
    · rw [ite_eq_left (hsub.2 rfl), ite_eq_left (hadd.2 ⟨rfl, hb⟩), ite_eq_left rfl, hw]
      simp only [ite_eq_left hb]
      ring
    · rw [ite_eq_left (hsub.2 rfl), ite_eq_right fun h => hb (hadd.1 h).2, ite_eq_left rfl, hw]
      simp only [ite_eq_right hb]
      ring
  · rw [ite_eq_right fun h => hkl (hsub.1 h), ite_eq_right fun h => hkl (hadd.1 h).1,
      ite_eq_right hkl]
    ring

/-- For $m > 0$, the DCT-I matrix $\mathrm{DCT}(m + 1)$ is nonsingular, because its square is
$\frac{m}{2} I$. -/
theorem isUnit_dct1 (hm : 0 < m) : IsUnit (dct1 m) := by
  have hm' : (m : ℝ) / 2 ≠ 0 := by positivity
  rw [isUnit_iff_isUnit_det]
  refine isUnit_det_of_right_inverse (B := ((m : ℝ) / 2)⁻¹ • dct1 m) ?_
  rw [Matrix.mul_smul, dct1_mul_self hm, smul_smul, inv_mul_cancel₀ hm', one_smul]

/-- For $0 < a < 2n$,
$$\sum_{k < n} \cos\Bigl(\frac{(k + 1) a \pi}{n}\Bigr) = \frac{(-1)^a - 1}{2}.$$
-/
private theorem sum_cos_succ_mul_nat {a : ℕ} (ha0 : 0 < a) (ha : a < 2 * n) :
    ∑ k ∈ range n, Real.cos (((k : ℝ) + 1) * ((a : ℝ) * π / n)) = ((-1) ^ a - 1) / 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : Real.sin ((a : ℝ) * π / n / 2) ≠ 0 := by
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    have ha' : (a : ℝ) < 2 * n := by exact_mod_cast ha
    refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    rw [div_div, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have h := Real.two_mul_sin_half_mul_sum_range_cos ((a : ℝ) * π / n) n
  rw [show (2 * (n : ℝ) + 1) * ((a : ℝ) * π / n / 2) = (a : ℝ) * π + (a : ℝ) * π / n / 2 by
    field_simp, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hs)
  rw [h]
  ring

/-- For $j, l < n$ with $j \neq l$,
$$\sum_{k < n} \cos\Bigl(\frac{(k + 1)(j - l) \pi}{n}\Bigr) = \frac{(-1)^{j + l} - 1}{2}.$$
-/
private theorem sum_cos_succ_mul_sub {j l : ℕ} (hj : j < n) (hl : l < n) (hjl : j ≠ l) :
    ∑ k ∈ range n, Real.cos (((k : ℝ) + 1) * (((j : ℝ) - l) * π / n))
      = ((-1) ^ (j + l) - 1) / 2 := by
  rcases lt_or_gt_of_ne hjl with h | h
  · have hterm : ∀ k ∈ range n, Real.cos (((k : ℝ) + 1) * (((j : ℝ) - l) * π / n))
        = Real.cos (((k : ℝ) + 1) * (((l - j : ℕ) : ℝ) * π / n)) := by
      intro k _
      rw [Nat.cast_sub h.le, ← Real.cos_neg]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, sum_cos_succ_mul_nat (by omega) (by omega),
      show j + l = (l - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  · have hterm : ∀ k ∈ range n, Real.cos (((k : ℝ) + 1) * (((j : ℝ) - l) * π / n))
        = Real.cos (((k : ℝ) + 1) * (((j - l : ℕ) : ℝ) * π / n)) := by
      intro k _
      rw [Nat.cast_sub h.le]
    rw [Finset.sum_congr rfl hterm, sum_cos_succ_mul_nat (by omega) (by omega),
      show j + l = (j - l) + 2 * l by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **The Gram matrix of the DST-II**: for every $n \in \mathbb{N}$,
$$\mathrm{DST2}(n)^T \mathrm{DST2}(n) = \frac{n}{2} I + \frac{1}{2} v v^T, \qquad v =
  ((-1)^j)_{j < n}.$$
This is Problem P4.8.11(a) of [golub2013matrix], §4.8.6.

Entry $(j, l)$ is
$$\sum_k \sin((k + 1) \theta_j) \sin((k + 1) \theta_l) = \frac{1}{2} \sum_k \bigl(\cos((k +
  1)(\theta_j - \theta_l)) - \cos((k + 1)(\theta_j + \theta_l))\bigr)$$
with $\theta_j = (2j + 1) \pi / (2n)$, and both sums of cosines telescope. -/
theorem transpose_dst2_mul_dst2 (n : ℕ) :
    (dst2 n)ᵀ * dst2 n = ((n : ℝ) / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (1 / 2 : ℝ) • vecMulVec (fun j : Fin n => (-1 : ℝ) ^ (j : ℕ))
        (fun j : Fin n => (-1 : ℝ) ^ (j : ℕ)) := by
  ext j l
  have hn : (0 : ℝ) < n := by exact_mod_cast j.pos
  have hj := j.isLt
  have hl := l.isLt
  have hterm : ∀ k : Fin n, (dst2 n)ᵀ j k * dst2 n k l
      = (Real.cos (((k : ℕ) + 1) * ((((j : ℕ) : ℝ) - (l : ℕ)) * π / n))
        - Real.cos (((k : ℕ) + 1) * ((((j : ℕ) + (l : ℕ) + 1 : ℕ) : ℝ) * π / n))) / 2 := by
    intro k
    rw [transpose_apply, dst2_apply, dst2_apply]
    set A := ((k : ℕ) + 1) * (2 * ((j : ℕ) : ℝ) + 1) * π / (2 * n)
    set B := ((k : ℕ) + 1) * (2 * ((l : ℕ) : ℝ) + 1) * π / (2 * n)
    rw [show ((k : ℕ) + 1) * ((((j : ℕ) : ℝ) - (l : ℕ)) * π / n) = A - B by
        simp only [A, B]; field_simp; ring,
      show ((k : ℕ) + 1) * ((((j : ℕ) + (l : ℕ) + 1 : ℕ) : ℝ) * π / n) = A + B by
        simp only [A, B]; push_cast; field_simp; ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_div,
    Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range (fun k => Real.cos (((k : ℝ) + 1) *
      ((((j : ℕ) : ℝ) - (l : ℕ)) * π / n))) n,
    Fin.sum_univ_eq_sum_range (fun k => Real.cos (((k : ℝ) + 1) *
      ((((j : ℕ) + (l : ℕ) + 1 : ℕ) : ℝ) * π / n))) n,
    sum_cos_succ_mul_nat (by omega) (by omega), Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, smul_eq_mul, smul_eq_mul]
  by_cases hjl : j = l
  · subst hjl
    have hzero : ∀ k ∈ range n, Real.cos (((k : ℝ) + 1) * ((((j : ℕ) : ℝ) - (j : ℕ)) * π / n))
        = 1 := fun k _ => by simp
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ite_eq_left rfl, ← pow_add, show (j : ℕ) + (j : ℕ) + 1 = 2 * (j : ℕ) + 1 by ring,
      pow_succ, pow_mul, neg_one_sq, one_pow, show (j : ℕ) + (j : ℕ) = 2 * (j : ℕ) by ring,
      pow_mul, neg_one_sq, one_pow]
    ring
  · rw [sum_cos_succ_mul_sub hj hl (fun h => hjl (Fin.ext h)), ite_eq_right hjl, ← pow_add,
      show (j : ℕ) + (l : ℕ) + 1 = ((j : ℕ) + (l : ℕ)) + 1 by ring, pow_succ]
    ring

/-- **The DST-II is nonsingular**: for every $n \in \mathbb{N}$, the matrix $\mathrm{DST2}(n)$ is
invertible.

If $\mathrm{DST2}(n) x = 0$, then $0 = x^T \mathrm{DST2}(n)^T \mathrm{DST2}(n) x = \frac{n}{2}
\|x\|^2 + \frac{1}{2} (v \cdot x)^2$, so $x = 0$. -/
theorem isUnit_dst2 (n : ℕ) : IsUnit (dst2 n) := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : dst2 n *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  set z := x - y with hz
  have hG : z ⬝ᵥ (((dst2 n)ᵀ * dst2 n) *ᵥ z) = 0 := by
    rw [← mulVec_mulVec, h0, mulVec_zero, dotProduct_zero]
  rw [transpose_dst2_mul_dst2, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul] at hG
  simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul] at hG
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i
    exact i.elim0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hzz : z ⬝ᵥ z = 0 := by
    have h1 : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
    have h2 : 0 ≤ (fun j : Fin n => (-1 : ℝ) ^ (j : ℕ)) ⬝ᵥ z
        * (z ⬝ᵥ fun j : Fin n => (-1 : ℝ) ^ (j : ℕ)) := by
      rw [dotProduct_comm]
      exact mul_self_nonneg _
    nlinarith
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzz)

/-- **The DCT-II has orthogonal rows**: for every $n \in \mathbb{N}$,
$$\mathrm{DCT2}(n) \, \mathrm{DCT2}(n)^T = \operatorname{diag}(n, n/2, \dots, n/2).$$

The proof is `Matrix.dotProduct_cosineIIVec`. -/
theorem dct2_mul_transpose (n : ℕ) :
    dct2 n * (dct2 n)ᵀ = diagonal fun k : Fin n => if (k : ℕ) = 0 then (n : ℝ) else n / 2 := by
  ext k l
  have h : (dct2 n * (dct2 n)ᵀ) k l = cosineIIVec n k ⬝ᵥ cosineIIVec n l := by
    rw [Matrix.mul_apply, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [transpose_apply, dct2_apply, dct2_apply]
  rw [h, dotProduct_cosineIIVec, diagonal_apply]

/-- For every $n \in \mathbb{N}$, the DCT-II matrix $\mathrm{DCT2}(n)$ is nonsingular. -/
theorem isUnit_dct2 (n : ℕ) : IsUnit (dct2 n) := by
  have hD : IsUnit (diagonal fun k : Fin n => if (k : ℕ) = 0 then (n : ℝ) else n / 2) := by
    rw [isUnit_diagonal, Pi.isUnit_iff]
    intro k
    have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
    split_ifs
    · exact hn.ne'.isUnit
    · exact (by positivity : (n : ℝ) / 2 ≠ 0).isUnit
  rw [← dct2_mul_transpose, isUnit_iff_isUnit_det, det_mul, det_transpose] at hD
  exact (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hD)

/-! ### Eigensystems of the second-difference matrices -/

/-- **The DCT-II diagonalizes $Y_{1,1}$**: for every $n \in \mathbb{N}$,
$$\mathrm{DCT2}(n) \, Y_{1,1} \, \mathrm{DCT2}(n)^{-1} = \operatorname{diag}\bigl(2 \cos(k \pi /
  n)\bigr)_{k < n}.$$
Here $Y_{1,1}$ is the tridiagonal matrix with ones on the two off-diagonals, $1$ at the two
diagonal corners $(0, 0)$ and $(n - 1, n - 1)$ and $0$ elsewhere on the diagonal, as in
[golub2013matrix] (12.1.13). For $n = 1$ the two corners coincide, and $Y_{1,1}$ is the
$1 \times 1$ matrix $(2)$.

The matrix $Y_{1,1}$ is `Matrix.cornerTridiagonal n 1 1`. Row $k$ of $\mathrm{DCT2}(n) Y_{1,1}$
is $(Y_{1,1} q_k)^T = 2 \cos(k \pi / n) q_k^T$, where $q_k$ is row $k$ of $\mathrm{DCT2}(n)$,
because $Y_{1,1}$ is symmetric. -/
theorem dct2_mul_cornerTridiagonal_one_one_mul_inv (n : ℕ) :
    dct2 n * cornerTridiagonal n 1 1 * (dct2 n)⁻¹
      = diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * π / n) := by
  have hrow : dct2 n * cornerTridiagonal n 1 1
      = (diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * π / n)) * dct2 n := by
    refine (diagonal_mul_eq_mul_of_forall_vecMul_row fun k => ?_).symm
    rw [show (dct2 n).row k = cosineIIVec n k from funext (dct2_apply k),
      ← (cornerTridiagonal_isSymm n 1 1).eq, vecMul_transpose]
    exact cornerTridiagonal_one_one_mulVec_cosineIIVec k
  rw [hrow, Matrix.mul_assoc,
    mul_nonsing_inv (dct2 n) ((isUnit_iff_isUnit_det _).mp (isUnit_dct2 n)), Matrix.mul_one]

/-- **The Dirichlet–Neumann eigensystem**: let $n \ge 2$ and $j < n$. Column $j$ of
$\mathrm{DST2}(n)$, the sine vector at $\theta_j = (2j + 1) \pi / (2n)$, is an eigenvector of
the Dirichlet–Neumann second difference $\mathcal{T}^{(DN)}_n$ with the eigenvalue
$4 \sin^2(\theta_j / 2)$:
$$\mathcal{T}^{(DN)}_n \, s(\theta_j) = 4 \sin^2\Bigl(\frac{(2j + 1) \pi}{4n}\Bigr)
  s(\theta_j).$$
This is in [golub2013matrix], §4.8.6.

The matrix $\mathcal{T}^{(DN)}_n$ is `Matrix.secondDifferenceDN n`. The residual $\sin((n + 1)
\theta_j) - \sin((n - 1) \theta_j) = 2 \cos(n \theta_j) \sin \theta_j$ of (4.8.18) vanishes
because $n \theta_j = (2j + 1) \pi / 2$. -/
theorem secondDifferenceDN_mulVec_dst2_col (hn : 2 ≤ n) (j : Fin n) :
    secondDifferenceDN n *ᵥ (fun k => dst2 n k j)
      = (4 * Real.sin ((2 * (j : ℕ) + 1) * π / (4 * n)) ^ 2) • fun k => dst2 n k j := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set θ : ℝ := (2 * (j : ℕ) + 1) * π / (2 * n) with hθ
  have hres : Real.sin (((n : ℝ) + 1) * θ) - Real.sin (((n : ℝ) - 1) * θ) = 0 := by
    have hnθ : (n : ℝ) * θ = (j : ℕ) * π + π / 2 := by
      rw [hθ]
      field_simp
    rw [show ((n : ℝ) + 1) * θ = (n : ℝ) * θ + θ by ring,
      show ((n : ℝ) - 1) * θ = (n : ℝ) * θ - θ by ring, Real.sin_add, Real.sin_sub, hnθ,
      Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
    ring
  rw [dst2_col_eq_sinAngleVec, secondDifferenceDN_mulVec_sinAngleVec hn, ← hθ, hres, zero_smul,
    add_zero, show θ / 2 = (2 * (j : ℕ) + 1) * π / (4 * n) by rw [hθ]; field_simp; ring]

/-- The DST-II diagonalizes the Dirichlet–Neumann second difference: for $n \ge 2$,
$$\mathcal{T}^{(DN)}_n \, \mathrm{DST2}(n) = \mathrm{DST2}(n) \operatorname{diag}\Bigl(4
  \sin^2\Bigl(\frac{(2j + 1) \pi}{4n}\Bigr)\Bigr)_{j < n}.$$
-/
theorem secondDifferenceDN_mul_dst2 (hn : 2 ≤ n) :
    secondDifferenceDN n * dst2 n
      = dst2 n * diagonal fun j : Fin n => 4 * Real.sin ((2 * (j : ℕ) + 1) * π / (4 * n)) ^ 2 :=
  mul_eq_mul_diagonal_of_forall_mulVec_col (secondDifferenceDN_mulVec_dst2_col hn)

/-- **The Dirichlet–Neumann second difference, diagonalized**: for $n \ge 2$,
$$\mathrm{DST2}(n)^{-1} \, \mathcal{T}^{(DN)}_n \, \mathrm{DST2}(n) = \operatorname{diag}\Bigl(4
  \sin^2\Bigl(\frac{(2j + 1) \pi}{4n}\Bigr)\Bigr)_{j < n}.$$
This is in [golub2013matrix], §4.8.6. -/
theorem inv_dst2_mul_secondDifferenceDN_mul_dst2 (hn : 2 ≤ n) :
    (dst2 n)⁻¹ * secondDifferenceDN n * dst2 n
      = diagonal fun j : Fin n => 4 * Real.sin ((2 * (j : ℕ) + 1) * π / (4 * n)) ^ 2 := by
  rw [Matrix.mul_assoc, secondDifferenceDN_mul_dst2 hn, ← Matrix.mul_assoc,
    nonsing_inv_mul (dst2 n) ((isUnit_iff_isUnit_det _).mp (isUnit_dst2 n)), Matrix.one_mul]

/-- **The Neumann–Neumann eigensystem**: let $m > 0$ and $j \le m$. The cosine vector
$c(\theta_j) \in \mathbb{R}^{m + 1}$, with entries $c(\theta)_k = \cos(k \theta)$, at the angle
$\theta_j = j \pi / m$ is an eigenvector of the Neumann–Neumann second difference
$\mathcal{T}^{(NN)}_{m + 1}$ with the eigenvalue $4 \sin^2(j \pi / (2m))$:
$$\mathcal{T}^{(NN)}_{m + 1} \, c(\theta_j) = 4 \sin^2\Bigl(\frac{j \pi}{2m}\Bigr)
  c(\theta_j).$$
This is in [golub2013matrix], §4.8.6, with $n = m + 1$.

The matrix $\mathcal{T}^{(NN)}_{m + 1}$ is `Matrix.secondDifferenceNN (m + 1)`, and $c(\theta)$
is `Matrix.cosAngleVec (m + 1) θ`. The residual $\cos((m + 1) \theta_j) - \cos((m - 1)
\theta_j) = -2 \sin(m \theta_j) \sin \theta_j$ of (4.8.19) vanishes because
$m \theta_j = j \pi$. -/
theorem secondDifferenceNN_mulVec_cosAngleVec_mul_pi_div (hm : 0 < m) (j : Fin (m + 1)) :
    secondDifferenceNN (m + 1) *ᵥ cosAngleVec (m + 1) ((j : ℕ) * π / m)
      = (4 * Real.sin ((j : ℕ) * π / (2 * m)) ^ 2) • cosAngleVec (m + 1) ((j : ℕ) * π / m) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  set θ : ℝ := (j : ℕ) * π / m with hθ
  have hres : Real.cos (((m + 1 : ℕ) : ℝ) * θ) - Real.cos ((((m + 1 : ℕ) : ℝ) - 2) * θ) = 0 := by
    have hmθ : (m : ℝ) * θ = (j : ℕ) * π := by
      rw [hθ]
      field_simp
    rw [show ((m + 1 : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ by push_cast; ring,
      show (((m + 1 : ℕ) : ℝ) - 2) * θ = (m : ℝ) * θ - θ by push_cast; ring, Real.cos_add,
      Real.cos_sub, hmθ, Real.sin_nat_mul_pi]
    ring
  rw [secondDifferenceNN_mulVec_cosAngleVec (by omega), hres, zero_smul, add_zero,
    show θ / 2 = (j : ℕ) * π / (2 * m) by rw [hθ]; field_simp]

/-- The columns of $V = \mathrm{DCT}(m + 1) \operatorname{diag}(2, 1, \dots, 1, 2)$, the matrix
$V^{(NN)}_{m + 1}$ of [golub2013matrix] §4.8.6, are the cosine vectors at the angles
$\theta_j = j \pi / m$: $V_{kj} = \cos(k j \pi / m)$. -/
theorem dct1_mul_diagonal_apply (k j : Fin (m + 1)) :
    (dct1 m * diagonal fun j : Fin (m + 1) => if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ) else 1) k j
      = cosAngleVec (m + 1) ((j : ℕ) * π / m) k := by
  rw [mul_diagonal, dct1_apply, cosAngleVec_apply]
  rw [show ((k : ℕ) : ℝ) * ((j : ℕ) * π / m) = (k : ℕ) * (j : ℕ) * π / m by ring]
  split_ifs <;> ring

/-- **The Neumann–Neumann second difference, diagonalized**: for $m > 0$ and $V =
\mathrm{DCT}(m + 1) \operatorname{diag}(2, 1, \dots, 1, 2)$,
$$\mathcal{T}^{(NN)}_{m + 1} V = V \operatorname{diag}\Bigl(4 \sin^2\Bigl(\frac{j
  \pi}{2m}\Bigr)\Bigr)_{j \le m}.$$
This is in [golub2013matrix], §4.8.6.

The matrix $V$ is nonsingular by `Matrix.isUnit_dct1`, so this is a diagonalization. -/
theorem secondDifferenceNN_mul_dct1_mul_diagonal (hm : 0 < m) :
    secondDifferenceNN (m + 1)
        * (dct1 m * diagonal fun j : Fin (m + 1) => if (j : ℕ) = 0 ∨ (j : ℕ) = m then 2 else 1)
      = (dct1 m * diagonal fun j : Fin (m + 1) => if (j : ℕ) = 0 ∨ (j : ℕ) = m then 2 else 1)
        * diagonal fun j : Fin (m + 1) => 4 * Real.sin ((j : ℕ) * π / (2 * m)) ^ 2 := by
  refine mul_eq_mul_diagonal_of_forall_mulVec_col fun j => ?_
  rw [show (dct1 m * diagonal fun j : Fin (m + 1) => if (j : ℕ) = 0 ∨ (j : ℕ) = m then (2 : ℝ)
      else 1).col j = cosAngleVec (m + 1) ((j : ℕ) * π / m) from
    funext fun k => dct1_mul_diagonal_apply k j]
  exact secondDifferenceNN_mulVec_cosAngleVec_mul_pi_div hm j

end Matrix
