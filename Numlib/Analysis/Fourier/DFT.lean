/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.ZMod`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RootsOfUnity.Complex

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
formalised here; the theorem content is exactly the identity above.

Atkinson and Han[^atkinson-han] state the matrix in Section 4.3, the inversion formula as
Theorem 4.3.2 and the radix-2 identity as (4.3.8)-(4.3.9).

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Complex Finset

open scoped ComplexConjugate Real

namespace Matrix

/-- The discrete Fourier transform matrix `F_n` of order `n`, with entries `ω ^ (j k)` for
`ω = exp (2 π i / n)` the standard primitive `n`-th root of unity. The discrete Fourier transform
of `y : Fin n → ℂ` is `(dft n)ᴴ *ᵥ y`, whose `k`-th entry is `∑ j, ω ^ (-(j k)) * y j`. -/
noncomputable def dft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun j k => Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))

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

theorem conjTranspose_dft_mulVec_apply {n : ℕ} (y : Fin n → ℂ) (k : Fin n) :
    ((dft n)ᴴ *ᵥ y) k
      = ∑ j : Fin n, (Complex.exp (2 * π * I / n))⁻¹ ^ ((j : ℕ) * (k : ℕ)) * y j := by
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [conjTranspose_dft_apply, Nat.mul_comm]

/-! ### The bridge to `ZMod.dft` -/

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
transform (Atkinson and Han, *Theoretical Numerical Analysis*, Theorem 4.3.2). -/
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

/-- The inverse of the matrix of the discrete Fourier transform (Atkinson and Han, *Theoretical
Numerical Analysis*, (4.3.3)). -/
theorem inv_conjTranspose_dft (n : ℕ) [NeZero n] :
    ((dft n)ᴴ)⁻¹ = (n : ℂ)⁻¹ • dft n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, conjTranspose_dft_mul_dft, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- **The inverse discrete Fourier transform** (Atkinson and Han, *Theoretical Numerical Analysis*,
(4.3.4)): `y j = (1/n) * ∑ k, ω ^ (j k) * ŷ k`. -/
theorem dft_mulVec_conjTranspose_dft_mulVec {n : ℕ} (y : Fin n → ℂ) :
    dft n *ᵥ ((dft n)ᴴ *ᵥ y) = (n : ℂ) • y := by
  rw [Matrix.mulVec_mulVec, dft_mul_conjTranspose_dft, Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ### The radix-2 identity -/

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

/-- **The radix-2 (Cooley-Tukey) identity**, first half (Atkinson and Han, *Theoretical Numerical
Analysis*, (4.3.8)): the first `n` entries of a transform of length `2 n` are `E k + ω⁻ᵏ * O k`,
with `E` and `O` the length-`n` transforms of the even- and odd-indexed halves of the input and
`ω = exp (2 π i / (2 n))`. This is the correctness statement of the fast Fourier transform. -/
theorem dft_radix_two {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
      = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
        + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
          * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  conjTranspose_dft_mulVec_two_mul y _ k (Nat.mod_eq_of_lt k.isLt)

/-- **The radix-2 (Cooley-Tukey) identity**, second half (Atkinson and Han, *Theoretical Numerical
Analysis*, (4.3.9)): the last `n` entries of a transform of length `2 n` reuse the same two
length-`n` transforms and the same twiddle factor, with a minus sign. -/
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
