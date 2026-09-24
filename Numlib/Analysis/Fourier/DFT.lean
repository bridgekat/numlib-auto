/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.ZMod`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RootsOfUnity.Complex
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.TrapezoidExactness

/-!
# The discrete Fourier transform in matrix form

The discrete Fourier transform of a vector `y : Fin n → ℂ` is classically written as the product of
`y` with the conjugate transpose of the matrix

`F_n = (ω ^ (j k))_{j,k}`, `ω = exp (2 π i / n)`,

and it is that matrix, rather than the transform of a function on `ℤ / n ℤ`, that the classical
statements are about. Mathlib has the transform in the second form, `ZMod.dft`, with the inversion
formula `ZMod.dft_dft`. This file adds the matrix `F_n` as `Matrix.dft`, the bridge
`Matrix.dft_eq_zmodDft` between the two, the orthogonality relation
`Matrix.conjTranspose_dft_mul_dft` with the inversion formula that follows from it, and the radix-2
identity `Matrix.dft_radix_two` on which the fast Fourier transform rests.

The radix-2 identity is the only statement here that Mathlib does not already contain in some form.
It says that a transform of length `2 n` is assembled from the two transforms of length `n` of the
even- and odd-indexed halves of the input, at the cost of one multiplication per output entry: with
`E` and `O` those two transforms and `ω = exp (2 π i / (2 n))`,

`ŷ k = E k + ω⁻ᵏ * O k` and `ŷ (k + n) = E k - ω⁻ᵏ * O k` for `k < n`.

An implementation of the fast Fourier transform and its operation count are algorithmic and are not
formalized here; the theorem content is exactly the identity above.

The entries of the transform matrix `(dft n)ᴴ` in real form, `cos (2 π k j / n) − i sin (2 π k j /
n)` (`Matrix.conjTranspose_dft_apply_eq_cos_sub_sin`, [golub2013matrix] (1.4.5)), and its two index
symmetries — the reflection `j ↦ n − j` conjugates (`Matrix.dft_apply_sub_eq_conj`), the half shift
`j ↦ j + n / 2` multiplies by `(−1) ^ k` (`Matrix.dft_two_mul_apply_add`) — are what the block
structure of `F_{2m}` ([golub2013matrix] Theorem 1.4.1) and the sine and cosine transform identities
of `Numlib.Analysis.Fourier.SineCosineTransform` are proved from. The diagonalization of circulant
matrices by `(dft n)ᴴ` is in `Numlib.Analysis.Fourier.Circulant`.

[han2009theoretical] state the matrix in Section 4.3, the inversion formula as Theorem 4.3.2 and the
radix-2 identity as (4.3.8)–(4.3.9).

## The discrete Fourier coefficients of a periodic function

The second half of the file is the transform of a *function* rather than of a vector: for
`f : ℝ → ℂ`, `N` equispaced nodes `x_j = 2 π j / N` of a period (`Quadrature.angleNode N j` of
`Numlib/Approximation/TrapezoidExactness`) and a window `m, m + 1, …, m + N − 1` of integer
frequencies, the **discrete Fourier coefficients**

`DFT.coeff N m f k = N⁻¹ ∑_{j < N} f (x_j) exp (−i (k + m) x_j)`, `k < N`,

are the trapezoidal approximations of the Fourier coefficients `(2π)⁻¹ ∫_0^{2π} f e^{−i (k + m) x}`,
and the **discrete Fourier series** `DFT.interp N m f x = ∑_{k < N} coeff k · exp (i (k + m) x)` is
the trigonometric polynomial with those coefficients. Its two properties are the ones every
textbook records: it *interpolates* `f` at the nodes (`DFT.interp_angleNode`, from the discrete
orthogonality `DFT.sum_exp_neg_sub` of the characters), and its coefficients are the matrix
transform of the modulated samples `ω^{−m j} f (x_j)` (`DFT.coeff_eq_dft_mulVec`), so that the
matrix `F_N` above and its inverse are the transform and its inverse for every window. The
**aliasing identity** `DFT.coeff_eq_tsum_fourierCoeff` says what the discrete coefficient of a
continuous periodic function with absolutely summable Fourier series computes: the sum of the exact
coefficients over all frequencies congruent to `k + m` modulo `N`. The window is a parameter
because the classical unshifted transform is `m = 0` while [quarteroni2000numerical] §10.9 uses
`m = −N/2` for even `N`, (10.52)–(10.55) and Lemma 10.1 there.
-/

open Complex

open scoped ComplexConjugate Real

namespace Matrix

/-- The discrete Fourier transform matrix `F_n` of order `n`, with entries `ω ^ (j k)` for `ω = exp
(2 π i / n)` the standard primitive `n`-th root of unity. The discrete Fourier transform of `y : Fin
n → ℂ` is `(dft n)ᴴ *ᵥ y`, whose `k`-th entry is `∑ j, ω ^ (-(j k)) * y j`. -/
noncomputable def dft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun j k => Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))

/-- The entries of the discrete Fourier transform matrix. -/
theorem dft_apply {n : ℕ} (j k : Fin n) :
    dft n j k = Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ)) :=
  rfl

/-- The discrete Fourier transform matrix is symmetric. -/
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

/-- The entries of the conjugate transpose of `dft n`, which is the matrix of the transform. -/
theorem conjTranspose_dft_apply {n : ℕ} (j k : Fin n) :
    (dft n)ᴴ j k = (Complex.exp (2 * π * I / n))⁻¹ ^ ((j : ℕ) * (k : ℕ)) := by
  rw [Matrix.conjTranspose_apply, dft_apply, inv_expRoot, ← map_pow,
    Nat.mul_comm (j : ℕ) (k : ℕ)]
  rfl

/-- The discrete Fourier transform of `y` as an explicit sum: `((dft n)ᴴ *ᵥ y) k = ∑ j, ω ^ (-(j k))
* y j`. -/
theorem conjTranspose_dft_mulVec_apply {n : ℕ} (y : Fin n → ℂ) (k : Fin n) :
    ((dft n)ᴴ *ᵥ y) k
      = ∑ j : Fin n, (Complex.exp (2 * π * I / n))⁻¹ ^ ((j : ℕ) * (k : ℕ)) * y j := by
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [conjTranspose_dft_apply, Nat.mul_comm]

/-! ### The entries in real form, and two index symmetries -/

/-- The entries of `dft n` are symmetric in the two indices. -/
theorem dft_apply_comm {n : ℕ} (j k : Fin n) : dft n j k = dft n k j := by
  rw [dft_apply, dft_apply, Nat.mul_comm]

/-- The entries of the transform matrix `(dft n)ᴴ` in real form: `(dft n)ᴴ k j = cos (2 π k j / n)
- i sin (2 π k j / n)` ([golub2013matrix] (1.4.5), where `n = 2 m` and the angle is `k j π / m`). -/
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

/-- **Reflection of an index conjugates**: for `0 < j`, `dft n k (n - j) = conj (dft n k j)`, since
`ω ^ (k (n - j)) = ω ^ (- k j)` by `ω ^ n = 1`, and `ω⁻¹ = conj ω` on the unit circle. -/
theorem dft_apply_sub_eq_conj {n : ℕ} (k j : Fin n) (hj : 0 < (j : ℕ)) :
    dft n k ⟨n - j, by omega⟩ = conj (dft n k j) := by
  have hω : Complex.exp (2 * π * I / n) ^ n = 1 :=
    (Complex.isPrimitiveRoot_exp n k.pos.ne').pow_eq_one
  rw [dft_apply, dft_apply, map_pow, ← inv_expRoot, inv_pow]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel j.isLt.le, Nat.mul_comm, pow_mul, hω, one_pow]

/-- Reflection of an index conjugates the entries of the transform matrix `(dft n)ᴴ` as well. -/
theorem conjTranspose_dft_apply_sub_eq_conj {n : ℕ} (k j : Fin n) (hj : 0 < (j : ℕ)) :
    (dft n)ᴴ k ⟨n - j, by omega⟩ = conj ((dft n)ᴴ k j) := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm _ k, dft_apply_comm _ k,
    dft_apply_sub_eq_conj k j hj]
  rfl

/-- The `m`-th power of the root of unity of order `2 m` is `-1`. -/
private theorem expRoot_two_mul_pow_self {m : ℕ} (hm : m ≠ 0) :
    Complex.exp (2 * π * I / ((2 * m : ℕ) : ℂ)) ^ m = -1 := by
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show (m : ℂ) * (2 * π * I / ((2 * m : ℕ) : ℂ)) = π * I by push_cast; field_simp]
  exact Complex.exp_pi_mul_I

/-- **The half shift multiplies by a sign**: `dft (2 m) k (m + j) = (-1) ^ k * dft (2 m) k j`, since
`ω ^ m = -1` for the root of unity `ω` of order `2 m`. -/
theorem dft_two_mul_apply_add {m : ℕ} (k : Fin (2 * m)) (j : Fin m) :
    dft (2 * m) k ⟨m + j, by omega⟩ = (-1) ^ (k : ℕ) * dft (2 * m) k ⟨j, by omega⟩ := by
  have hm : m ≠ 0 := by rintro rfl; exact j.elim0
  rw [dft_apply, dft_apply, Nat.mul_add, pow_add, Nat.mul_comm (k : ℕ) m, pow_mul,
    expRoot_two_mul_pow_self hm]

/-- The half shift multiplies the entries of the transform matrix `(dft (2 m))ᴴ` by the same
sign. -/
theorem conjTranspose_dft_two_mul_apply_add {m : ℕ} (k : Fin (2 * m)) (j : Fin m) :
    (dft (2 * m))ᴴ k ⟨m + j, by omega⟩ = (-1) ^ (k : ℕ) * (dft (2 * m))ᴴ k ⟨j, by omega⟩ := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm _ k, dft_apply_comm _ k,
    dft_two_mul_apply_add, star_mul', star_pow, star_neg, star_one]

/-! ### The bridge to `ZMod.dft` -/

/-- `ZMod n ≃ Fin n` through `ZMod.val`. This is `(ZMod.finEquiv n).symm` up to definitional
unfolding, but the direct form is stated for a variable `n`, so that the value of the forward map is
`⟨j.val, _⟩` by `rfl` rather than only after `n` is known to be a successor. -/
private def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun l := ((l : ℕ) : ZMod n)
  left_inv j := ZMod.natCast_rightInverse j
  right_inv l := by ext; simpa using ZMod.val_cast_of_lt l.isLt

/-- The bridge to Mathlib's transform on `ZMod n`: the matrix form is `ZMod.dft` transported along
`ZMod n ≃ Fin n`, so every lemma about `ZMod.dft` applies to it. -/
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

private theorem geom_sum_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hζ : ζ ^ n = 1) :
    ∑ l ∈ Finset.range n, ζ ^ l = if ζ = 1 then (n : ℂ) else 0 := by
  rcases eq_or_ne ζ 1 with rfl | h
  · simp
  · rw [ite_eq_right h, geom_sum_eq h, hζ, sub_self, zero_div]

/-- **The columns of the discrete Fourier transform matrix are orthogonal**: `(dft n)ᴴ * dft n` is
`n` times the identity. This is the content of the inversion formula for the discrete Fourier
transform ([han2009theoretical], Theorem 4.3.2). -/
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
  rw [hsum, geom_sum_of_pow_eq_one (inv_pow_mul_pow_pow_eq_one hprim.pow_eq_one (j : ℕ) (k : ℕ)),
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hjk : j = k
  · rw [ite_eq_left (hiff.mpr hjk), ite_eq_left hjk, mul_one]
  · rw [ite_eq_right fun h => hjk (hiff.mp h), ite_eq_right hjk, mul_zero]

/-- The rows of the discrete Fourier transform matrix are orthogonal: `dft n * (dft n)ᴴ` is `n`
times the identity. The transposed form of `conjTranspose_dft_mul_dft`. -/
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

/-- The inverse of the matrix of the discrete Fourier transform ([han2009theoretical], (4.3.3)). -/
theorem inv_conjTranspose_dft (n : ℕ) [NeZero n] :
    ((dft n)ᴴ)⁻¹ = (n : ℂ)⁻¹ • dft n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, conjTranspose_dft_mul_dft, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- **The inverse discrete Fourier transform** ([han2009theoretical], (4.3.4)): `y j = (1/n) * ∑ k,
ω ^ (j k) * ŷ k`. -/
theorem dft_mulVec_conjTranspose_dft_mulVec {n : ℕ} (y : Fin n → ℂ) :
    dft n *ᵥ ((dft n)ᴴ *ᵥ y) = (n : ℂ) • y := by
  rw [Matrix.mulVec_mulVec, dft_mul_conjTranspose_dft, Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ### The radix-2 identity -/

/-- `Fin n × Fin 2 ≃ Fin (2 n)` by `(m, r) ↦ 2 m + r`, the even-odd splitting of an index of length
`2 n`. Mathlib's `finProdFinEquiv` is the same map into `Fin (n * 2)`; the form here avoids
transporting along `Nat.mul_comm` in every use. -/
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

/-- Both halves of the radix-2 splitting at once: for `l : Fin (2 n)` with residue `k` modulo `n`,
the length-`2 n` transform at `l` is `E k + ω⁻ˡ * O k`, where `E` and `O` are the length-`n`
transforms of the even- and odd-indexed halves of `y`. -/
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

/-- **The radix-2 (Cooley–Tukey) identity**, first half ([han2009theoretical], (4.3.8)): the first
`n` entries of a transform of length `2 n` are `E k + ω⁻ᵏ * O k`, with `E` and `O` the length-`n`
transforms of the even- and odd-indexed halves of the input and `ω = exp (2 π i / (2 n))`. This is
the correctness statement of the fast Fourier transform. -/
theorem dft_radix_two {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
      = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
        + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
          * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  conjTranspose_dft_mulVec_two_mul y _ k (Nat.mod_eq_of_lt k.isLt)

/-- **The radix-2 (Cooley–Tukey) identity**, second half ([han2009theoretical], (4.3.9)): the last
`n` entries of a transform of length `2 n` reuse the same two length-`n` transforms and the same
twiddle factor, with a minus sign. -/
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

/-! ### The discrete Fourier coefficients of a periodic function -/

namespace DFT

open Finset Matrix Quadrature

/-- The **discrete Fourier coefficients** of `f : ℝ → ℂ` on the `N` equispaced nodes
`x_j = 2 π j / N` (`Quadrature.angleNode N j`) over the window `m, m + 1, …, m + N − 1` of integer
frequencies (`m : ℤ`):

`coeff N m f k = N⁻¹ ∑_{j < N} f (x_j) exp (−i (k + m) x_j)`,

for `k : ℕ`, meaningful for `k < N`. The classical unshifted transform is `m = 0`; the shifted
window of [quarteroni2000numerical] (10.52) is `m = −N/2` for even `N`. Each coefficient is the
trapezoidal approximation of the Fourier coefficient `(2π)⁻¹ ∫_0^{2π} f (x) e^{−i (k + m) x} dx`. -/
noncomputable def coeff (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ range N,
    f (angleNode N j) * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I))

theorem coeff_def (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (k : ℕ) :
    coeff N m f k = (N : ℂ)⁻¹ * ∑ j ∈ range N,
      f (angleNode N j) * Complex.exp (-((((k : ℤ) + m : ℤ) : ℂ) * (angleNode N j : ℝ) * I)) :=
  rfl

/-- The **discrete Fourier series** of order `N` of `f` over the window starting at `m`,

`interp N m f x = ∑_{k < N} coeff N m f k · exp (i (k + m) x)`,

a trigonometric polynomial with frequencies in the window ([quarteroni2000numerical] (10.53)),
which interpolates `f` at the nodes by `interp_angleNode`. -/
noncomputable def interp (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ range N, coeff N m f k * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * x * I)

theorem interp_def (N : ℕ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    interp N m f x
      = ∑ k ∈ range N, coeff N m f k * Complex.exp ((((k : ℤ) + m : ℤ) : ℂ) * x * I) :=
  rfl

/-- `N ∣ j − l ↔ j = l` for `j, l < N`. -/
private theorem natCast_dvd_sub_iff {N j l : ℕ} (hj : j < N) (hl : l < N) :
    (N : ℤ) ∣ ((j : ℤ) - l) ↔ j = l := by
  constructor
  · intro h
    have habs : |((j : ℤ) - l)| < (N : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h habs
    omega
  · rintro rfl
    simp

/-- **Discrete orthogonality of the characters** at two nodes: `∑_{k < N} exp (i (j − l) x_k)` is
`N` when `j = l` and `0` otherwise, for `j, l < N`. This is `Quadrature.sum_exp_angleNode` at
`p = j − l`, where `N ∣ j − l` forces `j = l` because `|j − l| < N`. -/
theorem sum_exp_sub_angleNode {N : ℕ} (hN : 0 < N) {j l : ℕ} (hj : j < N) (hl : l < N) :
    ∑ k ∈ range N, Complex.exp ((((j : ℤ) - l : ℤ) : ℂ) * (angleNode N k : ℝ) * I)
      = if j = l then (N : ℂ) else 0 := by
  rw [sum_exp_angleNode hN]
  by_cases h : j = l
  · rw [ite_eq_left ((natCast_dvd_sub_iff hj hl).mpr h), ite_eq_left h]
  · rw [ite_eq_right fun hh => h ((natCast_dvd_sub_iff hj hl).mp hh), ite_eq_right h]

/-- **Discrete orthogonality of the exponentials** in the textbook's normalization
([quarteroni2000numerical] Lemma 10.1, (10.54)): with `h = 2 π / N`, for `0 ≤ j, l < N`,

`h ∑_{k < N} exp (−i (l − j) x_k) = 2 π δ_{jl}`,

the discrete scalar product `(φ_l, φ_j)_N` of the characters `φ_l = e^{i l x}`. -/
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

/-- The product of the modulations at the nodes `x_j` and `x_l` for the window frequency `k + m`
is the modulation `exp (i m (x_j − x_l))` times the character `exp (i (j − l) x_k)`. -/
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

/-- The inner sum of the interpolation property: summed over the window, the products of the
modulations at two nodes give `N δ_{jl}`. -/
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

/-- **The discrete Fourier series interpolates at the nodes** ([quarteroni2000numerical] (10.55)):
for `0 < N`, every window `m`, every `f` and every `j < N`, `interp N m f (x_j) = f (x_j)`.
Substituting the coefficients and exchanging the two finite sums, the inner sum over the window
is the discrete orthogonality relation, in which the window offset `m` cancels. -/
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

/-- **The matrix form of the windowed transform**: with `ω = exp (2 π i / N)`, the coefficients over
the window starting at `m` are `N⁻¹` times the transform `(dft N)ᴴ *ᵥ ·` of the modulated samples
`ω^{−m j} f (x_j)`; for `m = −N/2` the modulation is `(−1)^j`. So the textbook's transform matrix
`T = N⁻¹ (ω^{−(k + m) j})_{k, j}` is `N⁻¹ (dft N)ᴴ · diag (ω^{−m j})`, and its inverse
`C = (ω^{(j + m) k})_{j, k}` follows from `Matrix.inv_conjTranspose_dft`
([quarteroni2000numerical], the matrices `T` and `C` after (10.55)). -/
theorem coeff_eq_dft_mulVec {N : ℕ} (m : ℤ) (f : ℝ → ℂ) (k : Fin N) :
    coeff N m f k = (N : ℂ)⁻¹ *
      ((dft N)ᴴ *ᵥ fun j : Fin N =>
        Complex.exp (2 * π * I / N) ^ (-(m * (j : ℕ))) * f (angleNode N j)) k := by
  have hN : 0 < N := k.pos
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
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

/-- The character `exp (i p x)` is the Fourier monomial `fourier p` of Mathlib's circle of
circumference `2 π`, evaluated at the class of `x`. -/
private theorem fourier_coe_eq_exp (p : ℤ) (x : ℝ) :
    (fourier p (x : AddCircle (2 * π)) : ℂ) = Complex.exp ((p : ℂ) * x * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  push_cast
  field_simp

/-- **Aliasing.** For a continuous `2 π`-periodic function — a continuous `f` on the circle
`AddCircle (2 π)`, composed with the projection `ℝ → AddCircle (2 π)` — whose Fourier coefficients
`fourierCoeff f : ℤ → ℂ` are absolutely summable, the discrete coefficient over the window starting
at `m` is the sum of the exact coefficients at all frequencies congruent to `k + m` modulo `N`:

`coeff N m f k = ∑' j : ℤ, fourierCoeff f (k + m + j N)`.

The samples are the values of the uniformly convergent Fourier series
(`has_pointwise_sum_fourier_series_of_summable`); exchanging the finite sum over the nodes with
the series, the discrete orthogonality `Quadrature.sum_exp_angleNode` at `p − (k + m)` keeps
exactly the frequencies `p ≡ k + m (mod N)`. This is the identity behind the interpolation-error
estimates of [quarteroni2000numerical] §10.9 and the aliasing error of the trapezoidal rule. -/
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
    rw [fourier_coe_eq_exp, smul_eq_mul, mul_assoc]
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
