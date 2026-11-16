/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Circulant`, with the discrete Fourier transform.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.DFT
import Numlib.Data.Matrix.Mul
import Numlib.LinearAlgebra.Matrix.Toeplitz

/-!
# The diagonalization of circulant matrices by the discrete Fourier transform

For $z \in \mathbb{C}^n$, the circulant matrix $C(z)$ has the entries $C(z)_{js} = z_{j - s}$, with
indices modulo $n$. Let $\omega = e^{2\pi i/n}$, and let $F_n = (\bar\omega^{jk})_{j,k}$ be the
matrix of the discrete Fourier transform in the convention of [golub2013matrix]. Every circulant
matrix is diagonalized by $F_n$:
$$F_n^{-1} C(z) F_n = \operatorname{diag}(\bar F_n z).$$
So the columns of $F_n$ are eigenvectors of every circulant, and the eigenvalues of $C(z)$ are the
entries of $\bar F_n z$. This is Theorem 4.8.2 of [golub2013matrix] (§4.8.2). The complex conjugate
statement says that the columns of $\bar F_n$ are eigenvectors with the eigenvalues $(F_n z)_k$.
This is the form that the von Neumann stability analysis of `Numlib.FiniteDifference.VonNeumann`
uses, because its Fourier modes are the columns of $\bar F_n$. Both forms rest on one computation,
the character property $\omega^{(j - s)k} = \omega^{jk} \omega^{-sk}$ of the columns.

The periodic second difference $\mathcal{T}^{(P)}_n$ is a circulant, so the same matrix diagonalizes
it. Its eigenvalues are $4 \sin^2(j\pi/n)$, and the real and imaginary parts of the columns of $F_n$
are real eigenvectors ([golub2013matrix], §4.8.6).

## Main results

* `Matrix.dft_apply_sub`: the columns of $\bar F_n$ are characters of $\mathbb{Z}/n\mathbb{Z}$.
* `Matrix.circulant_mulVec_conj_dft_col`: $C(z) F_n(:, k) = (\bar F_n z)_k F_n(:, k)$.
* `Matrix.circulant_mulVec_dft_col`: $C(z) \bar F_n(:, k) = (F_n z)_k \bar F_n(:, k)$.
* `Matrix.inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft`: Theorem 4.8.2 of
  [golub2013matrix], $F_n^{-1} C(z) F_n = \operatorname{diag}(\bar F_n z)$.
* `Matrix.circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft`: $C(z) = n^{-1} \bar F_n
  \operatorname{diag}(F_n z) F_n$.
* `Matrix.inv_conjTranspose_dft_mul_secondDifferencePeriodic_mul_conjTranspose_dft`: for $n \ge 3$,
  $F_n^{-1} \mathcal{T}^{(P)}_n F_n = \operatorname{diag}(4 \sin^2(j\pi/n))$.
* `Matrix.secondDifferencePeriodic_mulVec_realDftCol`: the real eigenvectors of
  $\mathcal{T}^{(P)}_n$.

## Implementation notes

* `Matrix.dft n` of `Numlib.Analysis.Fourier.DFT` is the matrix $(\omega^{jk})$ with
  $\omega = e^{2\pi i/n}$, which is $\bar F_n$. So $F_n$ is `(dft n)ᴴ`, $\bar F_n z$ is
  `dft n *ᵥ z`, and $F_n z$ is `(dft n)ᴴ *ᵥ z`.
* The circulant $C(z)$ is Mathlib's `Matrix.circulant z`. Mathlib has the circulant matrices and
  their algebra, but not their diagonalization.
* Indices are $0$-based, in `Fin n`. The source numbers the eigenvalues from $1$.
-/

open Finset
open scoped Real ComplexConjugate

namespace Matrix

variable {n : ℕ}

/-! ### The character property of the columns -/

/-- The columns of $\bar F_n = (\omega^{jk})$ are characters of $\mathbb{Z}/n\mathbb{Z}$: for
$j, s, k \in \{0, \dots, n-1\}$,
$$\omega^{(j - s)k} = \omega^{jk} \, \omega^{-sk},$$
where $j - s$ is taken modulo $n$.

In Lean, this is `dft n (j - s) k = dft n j k * (dft n)ᴴ k s`, with the subtraction in `Fin n`. -/
theorem dft_apply_sub (j s k : Fin n) : dft n (j - s) k = dft n j k * (dft n)ᴴ k s := by
  set ω := Complex.exp (2 * π * Complex.I / n) with hω
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hωN : ω ^ n = 1 := (Complex.isPrimitiveRoot_exp n k.pos.ne').pow_eq_one
  rw [dft_apply, dft_apply, conjTranspose_dft_apply, ← hω, Nat.mul_comm (k : ℕ) (s : ℕ),
    Fin.val_sub, pow_mul, ← pow_eq_pow_mod _ hωN, pow_add, pow_sub₀ _ hω0 s.isLt.le, hωN,
    one_mul, ← inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm]

/-- The matrix $F_n = $ `(dft n)ᴴ` is symmetric: $(F_n)_{jk} = (F_n)_{kj}$. -/
theorem conjTranspose_dft_apply_comm (j k : Fin n) : (dft n)ᴴ j k = (dft n)ᴴ k j := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm]

/-- The entries of $\bar F_n$ lie on the unit circle: $\bar\omega^{jk} \omega^{jk} = 1$, that is,
$(F_n)_{jk} (\bar F_n)_{kj} = 1$. -/
theorem conjTranspose_dft_apply_mul_dft_apply (j k : Fin n) :
    (dft n)ᴴ j k * dft n k j = 1 := by
  rw [conjTranspose_dft_apply, dft_apply, inv_pow, Nat.mul_comm (k : ℕ) (j : ℕ),
    inv_mul_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]

/-! ### The eigenvectors of a circulant -/

/-- The **columns of $F_n$ are eigenvectors of every circulant** ([golub2013matrix], §4.8.2). For
$z \in \mathbb{C}^n$ and every $k$,
$$C(z) F_n(:, k) = (\bar F_n z)_k \, F_n(:, k).$$

Here $\bar F_n z$ is `dft n *ᵥ z` and $F_n(:, k)$ is the column `fun j => (dft n)ᴴ j k`. The
proof: row $j$ of the left side is $\sum_s z_{j-s} \bar\omega^{sk}$, and the substitution
$t = j - s$ modulo $n$ with the character property `Matrix.dft_apply_sub` turns it into
$\bar\omega^{jk} \sum_t z_t \omega^{tk}$. -/
theorem circulant_mulVec_conj_dft_col (z : Fin n → ℂ) (k : Fin n) :
    circulant z *ᵥ (fun j => (dft n)ᴴ j k) = (dft n *ᵥ z) k • fun j => (dft n)ᴴ j k := by
  rcases n with _ | n
  · exact funext fun j => j.elim0
  funext j
  rw [Pi.smul_apply, smul_eq_mul, mulVec_apply_eq_sum, mulVec_apply_eq_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.subLeft j) _ _ fun s => ?_
  have hunit : (dft (n + 1))ᴴ j k * dft (n + 1) j k = 1 := by
    rw [dft_apply_comm j k]
    exact conjTranspose_dft_apply_mul_dft_apply j k
  have key : (dft (n + 1))ᴴ s k = dft (n + 1) k (j - s) * (dft (n + 1))ᴴ j k := by
    rw [dft_apply_comm k, dft_apply_sub, conjTranspose_dft_apply_comm k s]
    linear_combination (-(dft (n + 1))ᴴ s k) * hunit
  rw [circulant_apply, Equiv.subLeft_apply, key]
  ring

/-- The **columns of $\bar F_n$ are eigenvectors of every circulant**, in the convention opposite to
that of [golub2013matrix]. For $z \in \mathbb{C}^n$ and every $k$,
$$C(z) \bar F_n(:, k) = (F_n z)_k \, \bar F_n(:, k).$$

Here $\bar F_n(:, k)$ is the column `fun j => dft n j k` and $F_n z$ is `(dft n)ᴴ *ᵥ z`. This is
the complex conjugate of `Matrix.circulant_mulVec_conj_dft_col` at $\bar z$. -/
theorem circulant_mulVec_dft_col (z : Fin n → ℂ) (k : Fin n) :
    circulant z *ᵥ (fun j => dft n j k) = ((dft n)ᴴ *ᵥ z) k • fun j => dft n j k := by
  have hmap : (dft n).map (starRingEnd ℂ) = (dft n)ᴴ := by
    rw [conjTranspose, dft_transpose]
    rfl
  have hcol : (starRingEnd ℂ) ∘ (fun j => (dft n)ᴴ j k) = fun j => dft n j k := by
    funext j
    rw [Function.comp_apply, conjTranspose_apply, dft_apply_comm]
    exact Complex.conj_conj _
  have hz : (starRingEnd ℂ) ∘ star z = z := by
    funext i
    exact Complex.conj_conj _
  have hz' : (fun i => (starRingEnd ℂ) (star z i)) = z := by
    funext i
    exact Complex.conj_conj _
  funext j
  have h := congrArg (starRingEnd ℂ) (congrFun (circulant_mulVec_conj_dft_col (star z) k) j)
  rw [RingHom.map_mulVec, map_circulant, Pi.smul_apply, smul_eq_mul, map_mul,
    RingHom.map_mulVec, hmap, hz, hcol, hz'] at h
  rw [Pi.smul_apply, smul_eq_mul, h, conjTranspose_apply, dft_apply_comm k j]
  exact congrArg _ (Complex.conj_conj _)

/-! ### The diagonalization -/

/-- For $z \in \mathbb{C}^n$,
$$C(z) F_n = F_n \operatorname{diag}(\bar F_n z),$$
where $F_n = $ `(dft n)ᴴ`. This is `Matrix.circulant_mulVec_conj_dft_col`, column by column. -/
theorem circulant_mul_conjTranspose_dft (z : Fin n → ℂ) :
    circulant z * (dft n)ᴴ = (dft n)ᴴ * diagonal (dft n *ᵥ z) :=
  mul_eq_mul_diagonal_of_forall_mulVec_col (circulant_mulVec_conj_dft_col z)

/-- For $z \in \mathbb{C}^n$,
$$C(z) \bar F_n = \bar F_n \operatorname{diag}(F_n z),$$
where $\bar F_n = $ `dft n`. This is `Matrix.circulant_mulVec_dft_col`, column by column. -/
theorem circulant_mul_dft (z : Fin n → ℂ) :
    circulant z * dft n = dft n * diagonal ((dft n)ᴴ *ᵥ z) :=
  mul_eq_mul_diagonal_of_forall_mulVec_col (circulant_mulVec_dft_col z)

/-- **Theorem 4.8.2** of [golub2013matrix]. For $z \in \mathbb{C}^n$, the circulant $C(z)$ is
diagonalized by the discrete Fourier transform matrix $F_n$:
$$F_n^{-1} C(z) F_n = \operatorname{diag}(\bar F_n z).$$

Here $\bar F_n z$ is `dft n *ᵥ z` and $F_n$ is `(dft n)ᴴ`. The case $z = e_2$, where $C(z)$ is
the downshift matrix, is Lemma 4.8.1 of [golub2013matrix]. -/
theorem inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft (z : Fin n → ℂ) :
    ((dft n)ᴴ)⁻¹ * circulant z * (dft n)ᴴ = diagonal (dft n *ᵥ z) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Matrix.mul_assoc, circulant_mul_conjTranspose_dft, ← Matrix.mul_assoc,
    inv_conjTranspose_dft, Matrix.smul_mul, dft_mul_conjTranspose_dft, smul_smul,
    inv_mul_cancel₀ hn, one_smul, Matrix.one_mul]

/-- Theorem 4.8.2 of [golub2013matrix] in spectral form: for $z \in \mathbb{C}^n$,
$$C(z) = n^{-1} F_n \operatorname{diag}(\bar F_n z) \bar F_n,$$
where $\bar F_n = $ `dft n` and $F_n = $ `(dft n)ᴴ`. -/
theorem circulant_eq_conjTranspose_dft_mul_diagonal_mul_dft (z : Fin n → ℂ) :
    circulant z = (n : ℂ)⁻¹ • ((dft n)ᴴ * diagonal (dft n *ᵥ z) * dft n) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← circulant_mul_conjTranspose_dft, Matrix.mul_assoc, conjTranspose_dft_mul_dft,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- The spectral form in the convention opposite to that of [golub2013matrix]: for
$z \in \mathbb{C}^n$,
$$C(z) = n^{-1} \bar F_n \operatorname{diag}(F_n z) F_n,$$
where $\bar F_n = $ `dft n` and $F_n = $ `(dft n)ᴴ`. This is the spectral decomposition of a
periodic scheme in the von Neumann stability analysis. -/
theorem circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft (z : Fin n → ℂ) :
    circulant z = (n : ℂ)⁻¹ • (dft n * diagonal ((dft n)ᴴ *ᵥ z) * (dft n)ᴴ) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← circulant_mul_dft, Matrix.mul_assoc, dft_mul_conjTranspose_dft, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-!
### The periodic second difference

The periodic second difference $\mathcal{T}^{(P)}_n$ is the circulant of the vector
$(2, -1, 0, \dots, 0, -1)$, by `Matrix.secondDifferencePeriodic_eq_circulant` of
`Numlib.LinearAlgebra.Matrix.Toeplitz`. So its eigenvalues are
$2 - \omega^j - \omega^{-j} = 4 \sin^2(j\pi/n)$. They are symmetric under $j \mapsto n - j$
((4.8.22) of [golub2013matrix]). The matrix and its eigenvalues are real, so the real and imaginary
parts of the columns of $F_n$ are real eigenvectors ((4.8.24)–(4.8.25) of [golub2013matrix]).
-/

/-- The first column $(2, -1, 0, \dots, 0, -1)$ of the periodic second difference. -/
private noncomputable def periodicColumn (n : ℕ) : Fin n → ℝ := fun k =>
  if (k : ℕ) = 0 then 2 else if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0

/-- For $n \ge 3$, the product of $\bar F_n$ with $(2, -1, 0, \dots, 0, -1)$ has the entries
$2 - \omega^j - \omega^{-j} = 4 \sin^2(j\pi/n)$. -/
private theorem dft_mulVec_periodicColumn (hn : 3 ≤ n) (j : Fin n) :
    (dft n *ᵥ fun k => ((periodicColumn n k : ℝ) : ℂ)) j
      = ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) := by
  have hcol : (fun k : Fin n => ((periodicColumn n k : ℝ) : ℂ))
      = (2 : ℂ) • Pi.single (⟨0, by omega⟩ : Fin n) 1 - Pi.single (⟨1, by omega⟩ : Fin n) 1
        - Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
    funext k
    simp only [periodicColumn, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
      smul_eq_mul]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have h1 := dft_apply_sub_eq_conj j (⟨1, by omega⟩ : Fin n) (by simp)
  have hc := conjTranspose_dft_apply_eq_cos_sub_sin j (⟨1, by omega⟩ : Fin n)
  have hd : dft n j ⟨1, by omega⟩ = conj ((dft n)ᴴ j ⟨1, by omega⟩) := by
    rw [conjTranspose_apply, dft_apply_comm]
    exact (Complex.conj_conj _).symm
  rw [hcol, mulVec_sub, mulVec_sub, mulVec_smul, mulVec_single_one, mulVec_single_one,
    mulVec_single_one]
  simp only [Pi.sub_apply, Pi.smul_apply, col_apply, smul_eq_mul]
  rw [h1, hd, hc]
  have h0 : dft n j ⟨0, by omega⟩ = 1 := by rw [dft_apply]; simp
  rw [h0]
  simp only [map_sub, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  have hx : 2 * π * ((j : ℕ) : ℝ) * (((⟨1, by omega⟩ : Fin n) : ℕ) : ℝ) / n
      = 2 * ((j : ℕ) * π / n) := by
    simp only [Nat.cast_one]
    ring
  rw [hx, ← Real.two_sub_two_mul_cos_two_mul]
  push_cast
  ring

/-- The **eigenvectors of the periodic second difference** ([golub2013matrix], §4.8.6). Let
$n \ge 3$. For every $j \in \{0, \dots, n-1\}$, the column $F_n(:, j)$ is an eigenvector of
$\mathcal{T}^{(P)}_n$ with the eigenvalue $\lambda_j = 4 \sin^2(j\pi/n)$:
$$\mathcal{T}^{(P)}_n F_n(:, j) = 4 \sin^2(j\pi/n) \, F_n(:, j).$$

The real matrix $\mathcal{T}^{(P)}_n$ is `Matrix.secondDifferencePeriodic n`, mapped entrywise
into $\mathbb{C}$, and $F_n(:, j)$ is the column `fun k => (dft n)ᴴ k j`. -/
theorem secondDifferencePeriodic_map_mulVec_conj_dft_col (hn : 3 ≤ n) (j : Fin n) :
    (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun k => (dft n)ᴴ k j)
      = ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) • fun k => (dft n)ᴴ k j := by
  rw [secondDifferencePeriodic_eq_circulant hn, map_circulant]
  rw [← dft_mulVec_periodicColumn hn j]
  exact circulant_mulVec_conj_dft_col _ j

/-- The **diagonalization of the periodic second difference** ([golub2013matrix], §4.8.6). For
$n \ge 3$,
$$F_n^{-1} \mathcal{T}^{(P)}_n F_n = \operatorname{diag}\bigl(4 \sin^2(j\pi/n)\bigr)_{j =
  0}^{n-1}.$$
The eigenvalues are the entries $2 - \omega^j - \omega^{-j}$ of
$\bar F_n (2, -1, 0, \dots, 0, -1)$, as for every circulant.

The index $j$ is $0$-based. In the $1$-based numbering of the source, the eigenvalues are
$\lambda_j = 4 \sin^2((j - 1)\pi/n)$. The matrix $F_n$ is `(dft n)ᴴ`, and $\mathcal{T}^{(P)}_n$
is `Matrix.secondDifferencePeriodic n`, mapped entrywise into $\mathbb{C}$. -/
theorem inv_conjTranspose_dft_mul_secondDifferencePeriodic_mul_conjTranspose_dft (hn : 3 ≤ n) :
    ((dft n)ᴴ)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) * (dft n)ᴴ
      = diagonal fun j : Fin n => ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) := by
  rw [secondDifferencePeriodic_eq_circulant hn, map_circulant,
    inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft]
  congr 1
  funext j
  exact dft_mulVec_periodicColumn hn j

/-- **Equation (4.8.22)** of [golub2013matrix]. The eigenvalues of the periodic second difference
are symmetric: for natural numbers $j \le n$,
$$4 \sin^2(j\pi/n) = 4 \sin^2((n - j)\pi/n),$$
that is, $\lambda_j = \lambda_{n-j}$ with $0$-based indices. -/
theorem secondDifferencePeriodic_eigenvalue_symm {j : ℕ} (hj : j ≤ n) :
    4 * Real.sin ((j : ℕ) * π / n) ^ 2 = 4 * Real.sin (((n - j : ℕ) : ℝ) * π / n) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hj, show ((n : ℝ) - j) * π / n = π - j * π / n by field_simp, Real.sin_pi_sub]

/-- **Equation (4.8.23)** of [golub2013matrix]. The columns of $\bar F_n$ are the columns of $F_n$
in reverse order: for $0 < j < n$,
$$\bar F_n(:, j) = F_n(:, n - j).$$

The indices are $0$-based. The matrix $\bar F_n$ is `dft n` and $F_n$ is `(dft n)ᴴ`. -/
theorem conj_dft_col_eq (i j : Fin n) (hj : 0 < (j : ℕ)) :
    dft n i j = (dft n)ᴴ i ⟨n - j, by omega⟩ := by
  rw [conjTranspose_apply, dft_apply_comm _ i, dft_apply_sub_eq_conj i j hj]
  exact (Complex.conj_conj _).symm

/-- The real eigenvector matrix $V^{(P)}_n$ of the periodic second difference ((4.8.24) of
[golub2013matrix]). Let $m = \lceil (n + 1)/2 \rceil$. Column $j$ of $V^{(P)}_n$ is the real
part $(\cos(2\pi k j/n))_k$ of the column $F_n(:, j)$ if $j < m$, and its imaginary part
$(-\sin(2\pi k j/n))_k$ if $j \ge m$.

The number $m$ is written `(n + 2) / 2` with natural-number division, which is equal to
$\lceil (n + 1)/2 \rceil$. The indices are $0$-based. -/
noncomputable def realDftCol (n : ℕ) (j : Fin n) : Fin n → ℝ :=
  if (j : ℕ) < (n + 2) / 2 then fun k => Real.cos (2 * π * (k : ℕ) * (j : ℕ) / n)
  else fun k => -Real.sin (2 * π * (k : ℕ) * (j : ℕ) / n)

/-- **Equation (4.8.25)** of [golub2013matrix], the **real eigenvectors of the periodic second
difference**. For $n \ge 3$ and every $j \in \{0, \dots, n-1\}$,
$$\mathcal{T}^{(P)}_n V^{(P)}_n(:, j) = \lambda_j V^{(P)}_n(:, j), \qquad \lambda_j = 4
  \sin^2(j\pi/n).$$

The column $V^{(P)}_n(:, j)$ is `Matrix.realDftCol n j`. The proof takes the real and the
imaginary parts of the complex eigenvector equation, which is possible because the matrix and
the eigenvalue are real. -/
theorem secondDifferencePeriodic_mulVec_realDftCol (hn : 3 ≤ n) (j : Fin n) :
    secondDifferencePeriodic n *ᵥ realDftCol n j
      = (4 * Real.sin ((j : ℕ) * π / n) ^ 2) • realDftCol n j := by
  have h := secondDifferencePeriodic_map_mulVec_conj_dft_col hn j
  have hre : ∀ k, (secondDifferencePeriodic n *ᵥ fun l : Fin n =>
      Real.cos (2 * π * (l : ℕ) * (j : ℕ) / n)) k
        = 4 * Real.sin ((j : ℕ) * π / n) ^ 2 * Real.cos (2 * π * (k : ℕ) * (j : ℕ) / n) := by
    intro k
    have hk := congrArg Complex.re (congrFun h k)
    simp only [mulVec_apply_eq_sum, map_apply, Pi.smul_apply, smul_eq_mul,
      conjTranspose_dft_apply_eq_cos_sub_sin, Complex.re_sum, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, sub_self] at hk
    rw [mulVec_apply_eq_sum]
    exact hk
  have him : ∀ k, (secondDifferencePeriodic n *ᵥ fun l : Fin n =>
      -Real.sin (2 * π * (l : ℕ) * (j : ℕ) / n)) k
        = 4 * Real.sin ((j : ℕ) * π / n) ^ 2 * -Real.sin (2 * π * (k : ℕ) * (j : ℕ) / n) := by
    intro k
    have hk := congrArg Complex.im (congrFun h k)
    simp only [mulVec_apply_eq_sum, map_apply, Pi.smul_apply, smul_eq_mul,
      conjTranspose_dft_apply_eq_cos_sub_sin, Complex.im_sum, Complex.sub_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, mul_zero,
      add_zero, zero_add, zero_sub] at hk
    rw [mulVec_apply_eq_sum]
    simpa only [mul_neg] using hk
  funext k
  rw [Pi.smul_apply, smul_eq_mul]
  unfold realDftCol
  split_ifs
  · exact hre k
  · exact him k

end Matrix
