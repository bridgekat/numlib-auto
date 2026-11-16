/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.ZMod`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RootsOfUnity.Complex
import Numlib.Algebra.Field.GeomSum
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.TrapezoidExactness

/-!
# The discrete Fourier transform in matrix form

Let $n \ge 1$, let $\omega = e^{2\pi i/n}$, and let $F_n = (\omega^{jk})_{j,k = 0}^{n-1}$. The
discrete Fourier transform of a vector $y \in \mathbb{C}^n$ is $\hat y = F_n^H y$, with the entries
$\hat y_k = \sum_j \omega^{-jk} y_j$. The classical statements are about this matrix, and not about
the transform of a function on $\mathbb{Z}/n\mathbb{Z}$, which is the form that Mathlib has
(`ZMod.dft`, with the inversion formula `ZMod.dft_dft`). This file defines $F_n$ as `Matrix.dft` and
proves that the two forms agree. It proves the orthogonality relation $F_n^H F_n = n I$ with the
inversion formula $y = n^{-1} F_n \hat y$, the entries of $F_n^H$ in real form with two index
symmetries, and the radix-2 identity on which the fast Fourier transform rests. The presentation
follows [han2009theoretical], §4.3: the matrix is in Section 4.3, the inversion formula is Theorem
4.3.2, and the radix-2 identity is (4.3.8)–(4.3.9). The radix-2 identity says that a transform of
length $2n$ is assembled from the two transforms $E$ and $O$ of length $n$ of the even-indexed and
the odd-indexed halves of $y$, at the cost of one multiplication for each entry: with
$\omega = e^{2\pi i/(2n)}$,
$$\hat y_k = E_k + \omega^{-k} O_k, \qquad \hat y_{k+n} = E_k - \omega^{-k} O_k, \qquad k < n.$$

The second half of the file treats the transform of a $2\pi$-periodic function
$f : \mathbb{R} \to \mathbb{C}$. Its discrete Fourier coefficients on $N$ equispaced nodes are the
trapezoidal approximations of its Fourier coefficients. The discrete Fourier series with these
coefficients interpolates $f$ at the nodes, and the coefficients are the matrix transform of
modulated samples of $f$. For a continuous $f$ with an absolutely summable Fourier series, each
discrete coefficient is the sum of the exact Fourier coefficients over a residue class of
frequencies modulo $N$ (aliasing).

## Main definitions

* `Matrix.dft`: the matrix $F_n = (\omega^{jk})$ with $\omega = e^{2\pi i/n}$.
* `DFT.coeff`: the discrete Fourier coefficients of a function over a window of $N$ consecutive
  frequencies.
* `DFT.interp`: the discrete Fourier series, the trigonometric polynomial with these coefficients.

## Main results

* `Matrix.dft_eq_zmodDft`: the transform $F_n^H y$ is Mathlib's `ZMod.dft`, transported from
  `ZMod n` to `Fin n`.
* `Matrix.conjTranspose_dft_mul_dft`: $F_n^H F_n = n I$.
* `Matrix.inv_conjTranspose_dft`: $(F_n^H)^{-1} = n^{-1} F_n$ for $n \ge 1$.
* `Matrix.dft_radix_two` and `Matrix.dft_radix_two_add`: the radix-2 (Cooley–Tukey) identity.
* `Matrix.conjTranspose_dft_apply_eq_cos_sub_sin`: $(F_n^H)_{kj} = \cos(2\pi kj/n) - i \sin(2\pi
  kj/n)$.
* `DFT.interp_angleNode`: the discrete Fourier series interpolates $f$ at the nodes.
* `DFT.coeff_eq_dft_mulVec`: the discrete Fourier coefficients are the matrix transform of the
  modulated samples.
* `DFT.coeff_eq_tsum_fourierCoeff`: the aliasing identity.

## Notation

* $F_n$: the matrix `Matrix.dft n` $= (\omega^{jk})$, with $\omega = e^{2\pi i/n}$. The transform
  matrix is its conjugate transpose $F_n^H$ = `(dft n)ᴴ`. Note that [golub2013matrix] and
  `Numlib.Analysis.Fourier.Circulant` write $F_n$ for the conjugate matrix $(\bar\omega^{jk})$,
  which is `(dft n)ᴴ`.
* $x_j = 2\pi j/N$: the equispaced nodes on one period, `Quadrature.angleNode N j` of
  `Numlib.Approximation.TrapezoidExactness`.

## Implementation notes

* Indices are $0$-based, in `Fin n`.
* The fast Fourier transform as an algorithm, and its operation count, are not formalized. The
  theorem content is the radix-2 identity alone.
* Mathlib has the orthogonality and the inversion formula in the form of `ZMod.dft`. It does not
  have the radix-2 identity, the entries in real form, or the index symmetries.
* The entries in real form and the two index symmetries (the reflection $j \mapsto n - j$
  conjugates, and the half shift $j \mapsto j + n/2$ multiplies by $(-1)^k$) are the facts from
  which the block structure of $F_{2m}$ (Theorem 1.4.1 of [golub2013matrix]) and the identities of
  the sine and cosine transforms of `Numlib.Analysis.Fourier.SineCosineTransform` are proved.
* The window of frequencies $m, m + 1, \dots, m + N - 1$ of `DFT.coeff` is a parameter
  $m \in \mathbb{Z}$, because the classical transform without shift is $m = 0$, while
  [quarteroni2000numerical], §10.9, uses $m = -N/2$ for even $N$ in (10.52)–(10.55) and Lemma 10.1.
-/

open Complex

open scoped ComplexConjugate Real

namespace Matrix

/-- The **discrete Fourier transform matrix** $F_n$ of order $n$, with the entries
$$(F_n)_{jk} = \omega^{jk}, \qquad \omega = e^{2\pi i/n},$$
for $j, k \in \{0, \dots, n-1\}$. Here $\omega$ is the standard primitive $n$-th root of unity.
The discrete Fourier transform of $y \in \mathbb{C}^n$ is $F_n^H y$ = `(dft n)ᴴ *ᵥ y`, whose
entry $k$ is $\sum_j \omega^{-jk} y_j$. -/
noncomputable def dft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun j k => Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))

/-- The entries of $F_n$: $(F_n)_{jk} = \omega^{jk}$ with $\omega = e^{2\pi i/n}$. -/
theorem dft_apply {n : ℕ} (j k : Fin n) :
    dft n j k = Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ)) :=
  rfl

/-- The discrete Fourier transform matrix is symmetric: $F_n^T = F_n$. -/
@[simp]
theorem dft_transpose (n : ℕ) : (dft n)ᵀ = dft n := by
  ext j k
  simp [dft_apply, Matrix.transpose_apply, Nat.mul_comm]

/-! ### The root of unity -/

private theorem norm_expRoot (n : ℕ) : ‖Complex.exp (2 * π * I / n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private theorem inv_expRoot (n : ℕ) :
    (Complex.exp (2 * π * I / n))⁻¹ = conj (Complex.exp (2 * π * I / n)) :=
  Complex.inv_eq_conj (norm_expRoot n)

private theorem expRoot_pow (n m : ℕ) :
    Complex.exp (2 * π * I / n) ^ m = Complex.exp (2 * π * I * m / n) := by
  rw [← Complex.exp_nat_mul]
  ring_nf

private theorem inv_expRoot_pow (n m : ℕ) :
    (Complex.exp (2 * π * I / n))⁻¹ ^ m = Complex.exp (-(2 * π * I * m) / n) := by
  rw [inv_pow, expRoot_pow, ← Complex.exp_neg]
  ring_nf

/-- The entries of the transform matrix $F_n^H$: $(F_n^H)_{jk} = \omega^{-jk}$, written as
$(\omega^{-1})^{jk}$. -/
theorem conjTranspose_dft_apply {n : ℕ} (j k : Fin n) :
    (dft n)ᴴ j k = (Complex.exp (2 * π * I / n))⁻¹ ^ ((j : ℕ) * (k : ℕ)) := by
  rw [Matrix.conjTranspose_apply, dft_apply, inv_expRoot, ← map_pow,
    Nat.mul_comm (j : ℕ) (k : ℕ)]
  rfl

/-- The discrete Fourier transform of $y \in \mathbb{C}^n$ as an explicit sum:
$$(F_n^H y)_k = \sum_{j=0}^{n-1} \omega^{-jk} y_j.$$
-/
theorem conjTranspose_dft_mulVec_apply {n : ℕ} (y : Fin n → ℂ) (k : Fin n) :
    ((dft n)ᴴ *ᵥ y) k
      = ∑ j : Fin n, (Complex.exp (2 * π * I / n))⁻¹ ^ ((j : ℕ) * (k : ℕ)) * y j := by
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [conjTranspose_dft_apply, Nat.mul_comm]

/-! ### The entries in real form, and two index symmetries -/

/-- The entries of $F_n$ are symmetric in the two indices: $(F_n)_{jk} = (F_n)_{kj}$. -/
theorem dft_apply_comm {n : ℕ} (j k : Fin n) : dft n j k = dft n k j := by
  rw [dft_apply, dft_apply, Nat.mul_comm]

/-- The entries of the transform matrix $F_n^H$ in real form: for $k, j \in \{0, \dots, n-1\}$,
$$(F_n^H)_{kj} = \cos(2\pi kj/n) - i \sin(2\pi kj/n).$$
This is (1.4.5) of [golub2013matrix], where $n = 2m$ and the angle is written $kj\pi/m$. -/
theorem conjTranspose_dft_apply_eq_cos_sub_sin {n : ℕ} (k j : Fin n) :
    (dft n)ᴴ k j = (Real.cos (2 * π * (k : ℕ) * (j : ℕ) / n) : ℂ)
      - I * (Real.sin (2 * π * (k : ℕ) * (j : ℕ) / n) : ℂ) := by
  rw [conjTranspose_dft_apply, inv_expRoot_pow]
  have h : -(2 * π * I * (((k : ℕ) * (j : ℕ) : ℕ) : ℂ)) / n
      = ((-(2 * π * (k : ℕ) * (j : ℕ) / n) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

/-- **Reflection of an index conjugates.** For $k, j \in \{0, \dots, n-1\}$ with $0 < j$,
$$(F_n)_{k, n-j} = \overline{(F_n)_{kj}}.$$
The reason is that $\omega^{k(n-j)} = \omega^{-kj}$ because $\omega^n = 1$, and
$\omega^{-1} = \bar\omega$ because $|\omega| = 1$. -/
theorem dft_apply_sub_eq_conj {n : ℕ} (k j : Fin n) (hj : 0 < (j : ℕ)) :
    dft n k ⟨n - j, by omega⟩ = conj (dft n k j) := by
  have hω : Complex.exp (2 * π * I / n) ^ n = 1 :=
    (Complex.isPrimitiveRoot_exp n k.pos.ne').pow_eq_one
  rw [dft_apply, dft_apply, map_pow, ← inv_expRoot, inv_pow]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel j.isLt.le, Nat.mul_comm, pow_mul, hω, one_pow]

/-- Reflection of an index conjugates the entries of the transform matrix as well: for $0 < j$,
$(F_n^H)_{k, n-j} = \overline{(F_n^H)_{kj}}$. -/
theorem conjTranspose_dft_apply_sub_eq_conj {n : ℕ} (k j : Fin n) (hj : 0 < (j : ℕ)) :
    (dft n)ᴴ k ⟨n - j, by omega⟩ = conj ((dft n)ᴴ k j) := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm _ k, dft_apply_comm _ k,
    dft_apply_sub_eq_conj k j hj]
  rfl

/-- For $m \ne 0$, the $m$-th power of the root of unity $e^{2\pi i/(2m)}$ is $-1$. -/
private theorem expRoot_two_mul_pow_self {m : ℕ} (hm : m ≠ 0) :
    Complex.exp (2 * π * I / ((2 * m : ℕ) : ℂ)) ^ m = -1 := by
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show (m : ℂ) * (2 * π * I / ((2 * m : ℕ) : ℂ)) = π * I by push_cast; field_simp]
  exact Complex.exp_pi_mul_I

/-- **The half shift multiplies by a sign.** For $k \in \{0, \dots, 2m-1\}$ and
$j \in \{0, \dots, m-1\}$,
$$(F_{2m})_{k, m+j} = (-1)^k (F_{2m})_{kj}.$$
The reason is that $\omega^m = -1$ for the root of unity $\omega = e^{2\pi i/(2m)}$. -/
theorem dft_two_mul_apply_add {m : ℕ} (k : Fin (2 * m)) (j : Fin m) :
    dft (2 * m) k ⟨m + j, by omega⟩ = (-1) ^ (k : ℕ) * dft (2 * m) k ⟨j, by omega⟩ := by
  have hm : m ≠ 0 := by rintro rfl; exact j.elim0
  rw [dft_apply, dft_apply, Nat.mul_add, pow_add, Nat.mul_comm (k : ℕ) m, pow_mul,
    expRoot_two_mul_pow_self hm]

/-- The half shift multiplies the entries of the transform matrix by the same sign:
$(F_{2m}^H)_{k, m+j} = (-1)^k (F_{2m}^H)_{kj}$ for $j < m$. -/
theorem conjTranspose_dft_two_mul_apply_add {m : ℕ} (k : Fin (2 * m)) (j : Fin m) :
    (dft (2 * m))ᴴ k ⟨m + j, by omega⟩ = (-1) ^ (k : ℕ) * (dft (2 * m))ᴴ k ⟨j, by omega⟩ := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm _ k, dft_apply_comm _ k,
    dft_two_mul_apply_add, star_mul', star_pow, star_neg, star_one]

/-! ### The relation to `ZMod.dft` -/

/-- The bijection from `ZMod n` to `Fin n` given by `ZMod.val`, for $n \ge 1$; unlike
`(ZMod.finEquiv n).symm`, its forward map evaluates to `⟨j.val, _⟩` by `rfl` for a variable $n$. -/
private def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun l := ((l : ℕ) : ZMod n)
  left_inv j := ZMod.natCast_rightInverse j
  right_inv l := by ext; simpa using ZMod.val_cast_of_lt l.isLt

/-- The matrix form of the transform agrees with Mathlib's transform on $\mathbb{Z}/n\mathbb{Z}$.
For $n \ge 1$, $y \in \mathbb{C}^n$ and $k \in \{0, \dots, n-1\}$,
$$(F_n^H y)_k = \hat\Phi(k), \qquad \Phi(j) = y_{j \bmod n},$$
where $\hat\Phi$ is `ZMod.dft Φ`. So every lemma about `ZMod.dft` applies to the matrix form.

The function $\Phi$ on `ZMod n` is `fun j => y ⟨j.val, _⟩`, and $k$ is cast to `ZMod n`. -/
theorem dft_eq_zmodDft {n : ℕ} [NeZero n] (y : Fin n → ℂ) (k : Fin n) :
    ((dft n)ᴴ *ᵥ y) k = ZMod.dft (fun j : ZMod n => y ⟨j.val, j.val_lt⟩) ((k : ℕ) : ZMod n) := by
  rw [conjTranspose_dft_mulVec_apply, ZMod.dft_apply]
  refine (Fintype.sum_equiv (zmodFinEquiv n) _ _ fun j => ?_).symm
  have hval : ((zmodFinEquiv n j : Fin n) : ℕ) = j.val := rfl
  rw [smul_eq_mul, hval]
  congr 1
  have hj : ((j.val : ℕ) : ZMod n) = j := ZMod.natCast_rightInverse j
  have hcast : -(j * ((k : ℕ) : ZMod n)) = ((-((j.val * (k : ℕ) : ℕ) : ℤ) : ℤ) : ZMod n) := by
    push_cast
    rw [hj]
  rw [hcast, ZMod.stdAddChar_coe, inv_expRoot_pow]
  congr 1
  push_cast
  ring

/-! ### Orthogonality and inversion -/

private theorem inv_pow_mul_pow (a : ℂ) (i j l : ℕ) :
    a⁻¹ ^ (i * l) * a ^ (l * j) = (a⁻¹ ^ i * a ^ j) ^ l := by
  rw [pow_mul, Nat.mul_comm l j, pow_mul, ← mul_pow]

private theorem inv_pow_mul_pow_pow_eq_one {a : ℂ} {n : ℕ} (h : a ^ n = 1) (i j : ℕ) :
    (a⁻¹ ^ i * a ^ j) ^ n = 1 := by
  have h1 : a⁻¹ ^ n = 1 := by rw [inv_pow, h, inv_one]
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm i n, Nat.mul_comm j n, pow_mul, pow_mul, h1, h,
    one_pow, one_pow, one_mul]

/-- **The columns of the discrete Fourier transform matrix are orthogonal**: for every $n$,
$$F_n^H F_n = n I.$$
This is the content of the inversion formula for the discrete Fourier transform (Theorem 4.3.2
of [han2009theoretical]). -/
theorem conjTranspose_dft_mul_dft (n : ℕ) :
    (dft n)ᴴ * dft n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext j; exact j.elim0
  have hprim : IsPrimitiveRoot (Complex.exp (2 * π * I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  have hne : Complex.exp (2 * π * I / n) ≠ 0 := Complex.exp_ne_zero _
  ext j k
  have hsum : ((dft n)ᴴ * dft n) j k
      = ∑ l ∈ Finset.range n, ((Complex.exp (2 * π * I / n))⁻¹ ^ (j : ℕ)
          * Complex.exp (2 * π * I / n) ^ (k : ℕ)) ^ l := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun l _ => by
      rw [conjTranspose_dft_apply, dft_apply, inv_pow_mul_pow]
  have hiff : (Complex.exp (2 * π * I / n))⁻¹ ^ (j : ℕ)
      * Complex.exp (2 * π * I / n) ^ (k : ℕ) = 1 ↔ j = k := by
    rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hne)]
    exact ⟨fun h => (Fin.val_inj).mp (hprim.pow_inj j.isLt k.isLt h), fun h => by rw [h]⟩
  rw [hsum,
    geom_sum_eq_ite_of_pow_eq_one (inv_pow_mul_pow_pow_eq_one hprim.pow_eq_one (j : ℕ) (k : ℕ)),
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hjk : j = k
  · rw [ite_eq_left (hiff.mpr hjk), ite_eq_left hjk, mul_one]
  · rw [ite_eq_right fun h => hjk (hiff.mp h), ite_eq_right hjk, mul_zero]

/-- The rows of the discrete Fourier transform matrix are orthogonal: for every $n$,
$F_n F_n^H = n I$. This is the transposed form of `Matrix.conjTranspose_dft_mul_dft`. -/
theorem dft_mul_conjTranspose_dft (n : ℕ) :
    dft n * (dft n)ᴴ = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext j; exact j.elim0
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hleft : ((n : ℂ)⁻¹ • (dft n)ᴴ) * dft n = 1 := by
    rw [Matrix.smul_mul, conjTranspose_dft_mul_dft, smul_smul, inv_mul_cancel₀ hn', one_smul]
  have hinv : (dft n)⁻¹ = (n : ℂ)⁻¹ • (dft n)ᴴ := Matrix.inv_eq_left_inv hleft
  have hunit : IsUnit (dft n).det := Matrix.isUnit_det_of_left_inverse hleft
  have hright := Matrix.mul_nonsing_inv (dft n) hunit
  rw [hinv, Matrix.mul_smul] at hright
  rw [← hright, smul_smul, mul_inv_cancel₀ hn', one_smul]

/-- The inverse of the transform matrix ((4.3.3) of [han2009theoretical]): for $n \ge 1$,
$$(F_n^H)^{-1} = n^{-1} F_n.$$
-/
theorem inv_conjTranspose_dft (n : ℕ) [NeZero n] :
    ((dft n)ᴴ)⁻¹ = (n : ℂ)⁻¹ • dft n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, conjTranspose_dft_mul_dft, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- **The inverse discrete Fourier transform** ((4.3.4) of [han2009theoretical]). For
$y \in \mathbb{C}^n$ with transform $\hat y = F_n^H y$,
$$F_n \hat y = n y, \qquad \text{that is,} \qquad y_j = \frac{1}{n} \sum_{k=0}^{n-1} \omega^{jk}
  \hat y_k \quad (n \ge 1).$$

The Lean statement is the form $F_n F_n^H y = n y$, which needs no hypothesis on $n$. -/
theorem dft_mulVec_conjTranspose_dft_mulVec {n : ℕ} (y : Fin n → ℂ) :
    dft n *ᵥ ((dft n)ᴴ *ᵥ y) = (n : ℂ) • y := by
  rw [Matrix.mulVec_mulVec, dft_mul_conjTranspose_dft, Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ### The radix-2 identity -/

/-- The bijection $\{0, \dots, n-1\} \times \{0, 1\} \to \{0, \dots, 2n-1\}$,
$(m, r) \mapsto 2m + r$, which is Mathlib's `finProdFinEquiv` with the target `Fin (2 * n)` in
place of `Fin (n * 2)`. -/
private def finTwoMulEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) where
  toFun p := ⟨2 * (p.1 : ℕ) + (p.2 : ℕ), by omega⟩
  invFun l := (⟨(l : ℕ) / 2, by omega⟩, ⟨(l : ℕ) % 2, by omega⟩)
  left_inv := by rintro ⟨m, r⟩; ext <;> simp <;> omega
  right_inv := by rintro l; ext; simp; omega

private theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] {n : ℕ} (g : Fin (2 * n) → M) :
    ∑ l : Fin (2 * n), g l
      = ∑ m : Fin n, (g ⟨2 * (m : ℕ), by omega⟩ + g ⟨2 * (m : ℕ) + 1, by omega⟩) := by
  rw [← Equiv.sum_comp (finTwoMulEquiv n) g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_two]
  rfl

/-- Both halves of the radix-2 identity at once: for $l \in \{0, \dots, 2n-1\}$ with
$l \equiv k \pmod n$, the transform of length $2n$ at $l$ is $E_k + \omega^{-l} O_k$, where $E$
and $O$ are the transforms of length $n$ of the even-indexed and the odd-indexed halves of $y$,
and $\omega = e^{2\pi i/(2n)}$. -/
private theorem conjTranspose_dft_mulVec_two_mul {n : ℕ} (y : Fin (2 * n) → ℂ) (l : Fin (2 * n))
    (k : Fin n) (hlk : (l : ℕ) % n = (k : ℕ)) :
    ((dft (2 * n))ᴴ *ᵥ y) l
      = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
        + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (l : ℕ)
          * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k := by
  have hn : n ≠ 0 := by rintro rfl; exact absurd k.isLt (Nat.not_lt_zero _)
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hprim : IsPrimitiveRoot (Complex.exp (2 * π * I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn
  have hsq : (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ 2 = (Complex.exp (2 * π * I / n))⁻¹ := by
    rw [inv_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    field_simp
  have hone : ((Complex.exp (2 * π * I / n))⁻¹) ^ n = 1 := by
    rw [inv_pow, hprim.pow_eq_one, inv_one]
  have hpow : ∀ m : Fin n, (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (2 * (m : ℕ) * (l : ℕ))
      = (Complex.exp (2 * π * I / n))⁻¹ ^ ((m : ℕ) * (k : ℕ)) := by
    intro m
    have hsplit : (m : ℕ) * (l : ℕ) = (m : ℕ) * (k : ℕ) + n * ((m : ℕ) * ((l : ℕ) / n)) := by
      conv_lhs => rw [← Nat.mod_add_div (l : ℕ) n]
      rw [hlk]
      ring
    rw [show 2 * (m : ℕ) * (l : ℕ) = 2 * ((m : ℕ) * (l : ℕ)) from by ring, pow_mul, hsq, hsplit,
      pow_add, pow_mul ((Complex.exp (2 * π * I / n))⁻¹) n ((m : ℕ) * ((l : ℕ) / n)), hone,
      one_pow, mul_one]
  rw [conjTranspose_dft_mulVec_apply, sum_fin_two_mul, conjTranspose_dft_mulVec_apply,
    conjTranspose_dft_mulVec_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only
  rw [show (2 * (m : ℕ) + 1) * (l : ℕ) = 2 * (m : ℕ) * (l : ℕ) + (l : ℕ) from by ring, pow_add]
  push_cast
  rw [hpow m]
  ring

/-- **The radix-2 (Cooley–Tukey) identity**, first half ((4.3.8) of [han2009theoretical]). Let
$y \in \mathbb{C}^{2n}$, and let
$$E = F_n^H (y_0, y_2, \dots, y_{2n-2}), \qquad O = F_n^H (y_1, y_3, \dots, y_{2n-1})$$
be the transforms of length $n$ of the even-indexed and the odd-indexed halves of $y$. With
$\omega = e^{2\pi i/(2n)}$, for $k \in \{0, \dots, n-1\}$,
$$(F_{2n}^H y)_k = E_k + \omega^{-k} O_k.$$

This is the correctness statement of the fast Fourier transform. The factor $\omega^{-k}$ is
written `(Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ k`. -/
theorem dft_radix_two {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
      = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
        + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
          * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  conjTranspose_dft_mulVec_two_mul y _ k (Nat.mod_eq_of_lt k.isLt)

/-- **The radix-2 (Cooley–Tukey) identity**, second half ((4.3.9) of [han2009theoretical]). Let
$y \in \mathbb{C}^{2n}$, and let $E$ and $O$ be the transforms of length $n$ of the even-indexed
and the odd-indexed halves of $y$, as in `Matrix.dft_radix_two`. With
$\omega = e^{2\pi i/(2n)}$, for $k \in \{0, \dots, n-1\}$,
$$(F_{2n}^H y)_{k+n} = E_k - \omega^{-k} O_k.$$
So the last $n$ entries of the transform use the same two transforms of length $n$ and the same
factor $\omega^{-k}$ as the first $n$ entries, with a minus sign. -/
theorem dft_radix_two_add {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ) + n, by omega⟩
      = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
        - (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
          * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k := by
  have hn : n ≠ 0 := by rintro rfl; exact absurd k.isLt (Nat.not_lt_zero _)
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmod : ((⟨(k : ℕ) + n, by omega⟩ : Fin (2 * n)) : ℕ) % n = (k : ℕ) := by
    change ((k : ℕ) + n) % n = (k : ℕ)
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt k.isLt
  have hpi : Complex.exp (2 * π * I / (2 * n)) ^ n = -1 := by
    rw [← Complex.exp_nat_mul, show (n : ℂ) * (2 * π * I / (2 * n)) = π * I from by
      field_simp]
    exact Complex.exp_pi_mul_I
  have hzn : (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ n = -1 := by
    rw [inv_pow, hpi]
    norm_num
  rw [conjTranspose_dft_mulVec_two_mul y _ k hmod,
    show ((⟨(k : ℕ) + n, by omega⟩ : Fin (2 * n)) : ℕ) = (k : ℕ) + n from rfl, pow_add, hzn]
  ring

end Matrix

/-!
### The discrete Fourier coefficients of a periodic function

This section treats the transform of a function $f : \mathbb{R} \to \mathbb{C}$, not of a vector.
Let $x_j = 2\pi j/N$ be $N$ equispaced nodes of a period, and let $m, m + 1, \dots, m + N - 1$ be a
window of integer frequencies. The discrete Fourier coefficients
$$c_k = N^{-1} \sum_{j=0}^{N-1} f(x_j) e^{-i(k+m)x_j}, \qquad k < N,$$
are the trapezoidal approximations of the Fourier coefficients $(2\pi)^{-1} \int_0^{2\pi} f(x)
e^{-i(k+m)x} \, dx$. The discrete Fourier series $\sum_{k<N} c_k e^{i(k+m)x}$ is the trigonometric
polynomial with these coefficients. It interpolates $f$ at the nodes, by the discrete orthogonality
of the characters. Its coefficients are the matrix transform of the modulated samples
$\omega^{-mj} f(x_j)$, so the matrix $F_N$ and its inverse give the transform and its inverse for
every window.
-/

namespace DFT

open Finset Matrix Quadrature

/-- The **discrete Fourier coefficients** of $f : \mathbb{R} \to \mathbb{C}$ on the $N$ equispaced
nodes $x_j = 2\pi j/N$, over the window $m, m + 1, \dots, m + N - 1$ of integer frequencies
($m \in \mathbb{Z}$):
$$c_k = N^{-1} \sum_{j=0}^{N-1} f(x_j) \, e^{-i(k+m)x_j}.$$
The definition is for every natural number $k$, and it is meaningful for $k < N$. Each
coefficient is the trapezoidal approximation of the Fourier coefficient $(2\pi)^{-1}
\int_0^{2\pi} f(x) e^{-i(k+m)x} \, dx$.

The classical transform without shift is $m = 0$. The shifted window of (10.52) of
[quarteroni2000numerical] is $m = -N/2$ for even $N$. The node $x_j$ is
`Quadrature.angleNode N j`. For $N = 0$ the coefficients are $0$, because $0^{-1} = 0$ in Lean. -/
noncomputable def coeff (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ range N,
    f (angleNode N j) * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I))

/-- The defining formula of `DFT.coeff`: $c_k = N^{-1} \sum_{j<N} f(x_j) e^{-i(k+m)x_j}$. -/
theorem coeff_def (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (k : ℕ) :
    coeff N m f k = (N : ℂ)⁻¹ * ∑ j ∈ range N,
      f (angleNode N j) * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)) :=
  rfl

/-- The **discrete Fourier series** of order $N$ of $f$ over the window that starts at $m$:
$$I_N f(x) = \sum_{k=0}^{N-1} c_k \, e^{i(k+m)x},$$
where $c_k$ are the discrete Fourier coefficients `DFT.coeff N m f k`. It is a trigonometric
polynomial with frequencies in the window ((10.53) of [quarteroni2000numerical]), and it
interpolates $f$ at the nodes by `DFT.interp_angleNode`. -/
noncomputable def interp (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ range N, coeff N m f k * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * x * I)

/-- The defining formula of `DFT.interp`: $I_N f(x) = \sum_{k<N} c_k e^{i(k+m)x}$. -/
theorem interp_def (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    interp N m f x
      = ∑ k ∈ range N, coeff N m f k * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * x * I) :=
  rfl

/-- **Discrete orthogonality of the characters** at two nodes. For $N \ge 1$ and natural numbers
$j, l < N$,
$$\sum_{k=0}^{N-1} e^{i(j - l)x_k} = \begin{cases} N & \text{if } j = l, \\ 0 &
  \text{otherwise.} \end{cases}$$

This is `Quadrature.sum_exp_angleNode` at $p = j - l$: the condition $N \mid j - l$ forces
$j = l$ because $|j - l| < N$. -/
theorem sum_exp_sub_angleNode {N : ℕ} (hN : 0 < N) {j l : ℕ} (hj : j < N) (hl : l < N) :
    ∑ k ∈ range N, Complex.exp ((((j : ℤ) - l : ℤ) : ℂ) * (angleNode N k : ℝ) * I)
      = if j = l then (N : ℂ) else 0 := by
  rw [sum_exp_angleNode hN]
  by_cases h : j = l
  · rw [ite_eq_left (by simp [h]), ite_eq_left h]
  · rw [ite_eq_right fun hh => h ((Nat.modEq_iff_dvd.2 hh).eq_of_lt_of_lt hl hj).symm,
      ite_eq_right h]

/-- **Lemma 10.1** of [quarteroni2000numerical], equation (10.54): **discrete orthogonality of the
exponentials**. For $N \ge 1$, $h = 2\pi/N$ and natural numbers $j, l < N$,
$$h \sum_{k=0}^{N-1} e^{-i(l - j)x_k} = 2\pi \delta_{jl}.$$
The left side is the discrete scalar product $(\varphi_l, \varphi_j)_N$ of the characters
$\varphi_l(x) = e^{ilx}$. -/
theorem sum_exp_neg_sub {N : ℕ} (hN : 0 < N) {j l : ℕ} (hj : j < N) (hl : l < N) :
    ((2 * π / N : ℝ) : ℂ) * ∑ k ∈ range N,
        Complex.exp (-((((l : ℤ) - j : ℤ) : ℂ) * (angleNode N k : ℝ) * I))
      = if j = l then (2 * π : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ k : ℕ, Complex.exp (-((((l : ℤ) - j : ℤ) : ℂ) * (angleNode N k : ℝ) * I))
      = Complex.exp ((((j : ℤ) - l : ℤ) : ℂ) * (angleNode N k : ℝ) * I) := by
    intro k
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, sum_exp_sub_angleNode hN hj hl]
  by_cases h : j = l
  · rw [ite_eq_left h, ite_eq_left h]
    push_cast
    field_simp
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- The product of the modulations at the nodes $x_j$ and $x_l$ for the frequency $k + m$ is
$e^{i(k+m)x_j} e^{-i(k+m)x_l} = e^{im(x_j - x_l)} e^{i(j - l)x_k}$. -/
private theorem exp_mul_exp_neg_eq {N : ℕ} (m : ℤ) (k j l : ℕ) :
    Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)
        * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N l : ℝ) * I))
      = Complex.exp ((m : ℂ) * ((angleNode N j : ℝ) - (angleNode N l : ℝ)) * I)
        * Complex.exp ((((j : ℤ) - l : ℤ) : ℂ) * (angleNode N k : ℝ) * I) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [angleNode]
  push_cast
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
    ring

/-- For $N \ge 1$ and $j, l < N$, the sum over the window of the products
$e^{i(k+m)x_j} e^{-i(k+m)x_l}$ is $N \delta_{jl}$. -/
private theorem sum_exp_mul_exp_neg {N : ℕ} (hN : 0 < N) (m : ℤ) {j l : ℕ} (hj : j < N)
    (hl : l < N) :
    ∑ k ∈ range N, Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)
        * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N l : ℝ) * I))
      = if j = l then (N : ℂ) else 0 := by
  rw [Finset.sum_congr rfl fun k _ => exp_mul_exp_neg_eq m k j l, ← Finset.mul_sum,
    sum_exp_sub_angleNode hN hj hl]
  by_cases h : j = l
  · rw [ite_eq_left h, h, sub_self, mul_zero, zero_mul, Complex.exp_zero, one_mul]
  · rw [ite_eq_right h, mul_zero]

/-- **Equation (10.55)** of [quarteroni2000numerical]: **the discrete Fourier series interpolates at
the nodes**. For $N \ge 1$, every window start $m \in \mathbb{Z}$, every
$f : \mathbb{R} \to \mathbb{C}$ and every natural number $j < N$,
$$I_N f(x_j) = f(x_j).$$

The idea of the proof: substitute the coefficients and exchange the two finite sums. The inner
sum over the window is the discrete orthogonality relation, in which the offset $m$ cancels. -/
theorem interp_angleNode {N : ℕ} (hN : 0 < N) (m : ℤ) (f : ℝ → ℂ) {j : ℕ} (hj : j < N) :
    interp N m f (angleNode N j) = f (angleNode N j) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [interp_def, coeff_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ l ∈ range N,
      ∑ k ∈ range N, (N : ℂ)⁻¹ * (f (angleNode N l)
          * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N l : ℝ) * I)))
        * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)
      = if j = l then f (angleNode N l) else 0 := by
    intro l hl
    have hl' : l < N := Finset.mem_range.mp hl
    have : ∀ k ∈ range N, (N : ℂ)⁻¹ * (f (angleNode N l)
          * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N l : ℝ) * I)))
        * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)
        = ((N : ℂ)⁻¹ * f (angleNode N l)) *
          (Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)
            * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N l : ℝ) * I))) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_exp_mul_exp_neg hN m hj hl']
    by_cases h : j = l
    · rw [ite_eq_left h, ite_eq_left h]
      field_simp
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hj)]

/-- **The matrix form of the windowed transform.** Let $\omega = e^{2\pi i/N}$. For
$f : \mathbb{R} \to \mathbb{C}$, $m \in \mathbb{Z}$ and $k \in \{0, \dots, N-1\}$, the discrete
Fourier coefficients over the window that starts at $m$ are
$$c_k = N^{-1} \bigl(F_N^H g\bigr)_k, \qquad g_j = \omega^{-mj} f(x_j).$$
For $m = -N/2$ the modulation $\omega^{-mj}$ is $(-1)^j$.

So the transform matrix $T = N^{-1} (\omega^{-(k+m)j})_{k,j}$ of [quarteroni2000numerical]
(after (10.55)) is $N^{-1} F_N^H \operatorname{diag}(\omega^{-mj})$, and its inverse
$C = (\omega^{(j+m)k})_{j,k}$ follows from `Matrix.inv_conjTranspose_dft`. The power
$\omega^{-mj}$ is an integer power, `Complex.exp (2 * π * I / N) ^ (-(m * j))`. -/
theorem coeff_eq_dft_mulVec {N : ℕ} (m : ℤ) (f : ℝ → ℂ) (k : Fin N) :
    coeff N m f k = (N : ℂ)⁻¹ *
      ((dft N)ᴴ *ᵥ fun j : Fin N =>
        Complex.exp (2 * π * I / N) ^ (-(m * (j : ℕ))) * f (angleNode N j)) k := by
  rw [conjTranspose_dft_mulVec_apply, coeff_def, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inv_pow, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_neg, ← mul_assoc,
    ← Complex.exp_add, mul_comm (f _)]
  congr 1
  simp only [angleNode]
  push_cast
  field_simp
  ring_nf

/-- The character $x \mapsto e^{ipx}$ is the Fourier monomial of frequency $p \in \mathbb{Z}$ on the
circle $\mathbb{R}/2\pi\mathbb{Z}$: for every $x \in \mathbb{R}$, `fourier p` at the class of
$x$ is $e^{ipx}$. -/
theorem fourier_coe_two_pi (p : ℤ) (x : ℝ) :
    (fourier p (x : AddCircle (2 * π)) : ℂ) = Complex.exp ((p : ℂ) * x * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  push_cast
  field_simp

/-- **The aliasing identity.** Let $N \ge 1$, $m \in \mathbb{Z}$, and let $f$ be a continuous
function on the circle $\mathbb{R}/2\pi\mathbb{Z}$ whose Fourier coefficients $\hat f(p)$ are
absolutely summable. Then for every natural number $k$, the discrete Fourier coefficient of $f$
over the window that starts at $m$ is the sum of the exact Fourier coefficients at all
frequencies congruent to $k + m$ modulo $N$:
$$c_k = \sum_{j \in \mathbb{Z}} \hat f(k + m + jN).$$

The function $f$ is `f : C(AddCircle (2 * π), ℂ)`, read on $\mathbb{R}$ through the projection
$\mathbb{R} \to \mathbb{R}/2\pi\mathbb{Z}$, and $\hat f$ is Mathlib's `fourierCoeff f`. The
summability hypothesis is `Summable (fourierCoeff f)`. The idea of the proof: the samples are
values of the uniformly convergent Fourier series
(`has_pointwise_sum_fourier_series_of_summable`), and after the finite sum over the nodes is
exchanged with the series, the discrete orthogonality `Quadrature.sum_exp_angleNode` at
$p - (k + m)$ keeps exactly the frequencies $p \equiv k + m \pmod N$. This identity is behind
the estimates of the interpolation error in [quarteroni2000numerical], §10.9, and behind the
aliasing error of the trapezoidal rule. -/
theorem coeff_eq_tsum_fourierCoeff {N : ℕ} (hN : 0 < N) (m : ℤ) {f : C(AddCircle (2 * π), ℂ)}
    (hf : Summable (fourierCoeff f)) (k : ℕ) :
    coeff N m (fun x : ℝ => f x) k = ∑' j : ℤ, fourierCoeff f ((k : ℤ) + m + j * N) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set q : ℤ := (k : ℤ) + m with hq
  -- the term of the double sum, and its summability in `p`
  set G : ℕ → ℤ → ℂ := fun j p => fourierCoeff f p *
    (Complex.exp ((p : ℂ) * (angleNode N j : ℝ) * I)
      * Complex.exp (-((q : ℂ) * (angleNode N j : ℝ) * I))) with hG
  have hnorm : ∀ j p, ‖G j p‖ = ‖fourierCoeff f p‖ := by
    intro j p
    simp only [hG, norm_mul, Complex.norm_exp]
    simp
  have hsumm : ∀ j, Summable (G j) := fun j =>
    Summable.of_norm_bounded hf.norm fun p => (hnorm j p).le
  -- the samples as Fourier series
  have hsample : ∀ j : ℕ, (f (angleNode N j : ℝ) : ℂ)
      * Complex.exp (-((q : ℂ) * (angleNode N j : ℝ) * I)) = ∑' p, G j p := by
    intro j
    have h := (has_pointwise_sum_fourier_series_of_summable hf
      ((angleNode N j : ℝ) : AddCircle (2 * π))).tsum_eq
    rw [← h, ← tsum_mul_right]
    refine tsum_congr fun p => ?_
    rw [hG]
    simp only
    rw [fourier_coe_two_pi, smul_eq_mul, mul_assoc]
  -- exchange the sums
  have hcoeff : coeff N m (fun x : ℝ => f x) k = (N : ℂ)⁻¹ * ∑' p, ∑ j ∈ range N, G j p := by
    rw [coeff_def, Summable.tsum_finsetSum fun j _ => hsumm j]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hsample j
  -- the inner finite sum is the discrete orthogonality
  have hinner : ∀ p : ℤ, ∑ j ∈ range N, G j p
      = fourierCoeff f p * (if (N : ℤ) ∣ p - q then (N : ℂ) else 0) := by
    intro p
    rw [← sum_exp_angleNode hN (p - q), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG]
    simp only
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hF : ∀ p : ℤ, (N : ℂ)⁻¹ * (fourierCoeff f p * (if (N : ℤ) ∣ p - q then (N : ℂ) else 0))
      = if (N : ℤ) ∣ p - q then fourierCoeff f p else 0 := by
    intro p
    split_ifs
    · field_simp
    · simp
  rw [hcoeff, ← tsum_mul_left]
  simp only [hinner, hF]
  -- reindex the surviving frequencies `q + j N`
  have hinj : Function.Injective fun j : ℤ => q + j * N := by
    intro a b hab
    have : (a : ℤ) * N = b * N := by simpa using hab
    exact mul_right_cancel₀ (by exact_mod_cast hN.ne') this
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun j => ?_
    have hdvd : (N : ℤ) ∣ q + j * N - q := ⟨j, by ring⟩
    exact ite_eq_left hdvd
  · intro p hp
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hp
    obtain ⟨⟨j, hj⟩, -⟩ := hp
    exact ⟨j, by simp only; linear_combination -hj⟩

end DFT
