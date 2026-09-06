import Numlib.Analysis.Fourier.DFT

/-!
# Atkinson–Han §4.3: the discrete Fourier transform

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §4.3.

The book's matrix `F_n` of (4.3.2), with entries `ω_n^{jk}` for `ω_n = e^{2πi/n}`, is the backbone
`Matrix.dft` (`Numlib/Analysis/Fourier/DFT`), and the book's transform `ŷ = conj(F_n) y` — the
matrix `F_n` being symmetric — is `(Matrix.dft n)ᴴ *ᵥ y`. Everything of the section is a
specialization of that module, which is itself Mathlib's `ZMod.dft` in matrix form.

## Main results

* `definition_4_3_1` — (4.3.1)–(4.3.2): the entries of `F_n`, and the transform
  `ŷ_k = ∑_j ω_n^{-kj} y_j`.
* `exercise_4_3_1` — the summation formula (4.3.5), `∑_k ω_n^{kl} ω_n^{-kj} = n δ_{jl}`.
* `theorem_4_3_2` — (4.3.3)–(4.3.4): `conj(F_n)⁻¹ = F_n / n`, and the inversion formula.
* `equation_4_3_9` — (4.3.6)–(4.3.9), the radix-2 splitting on which the fast Fourier transform
  is built.

## Not formalized here

The fast Fourier transform algorithm itself and its `O(n log n)` operation count. There is no
theorem there: the book's derivation is (4.3.8)–(4.3.9), which is `equation_4_3_9`, plus a cost
recursion, and a recursive implementation with a complexity bound is out of scope for this project
by the same rule that excludes storage formats and parallelisation.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open Complex Matrix

open scoped Real

namespace AtkinsonHan.Ch04

/-- **Definition 4.3.1**, (4.3.1)–(4.3.2). The book's matrix `F_n` has entries `ω_n^{jk}` for
`ω_n = e^{2πi/n}`, and the discrete Fourier transform of `y` is `ŷ = conj(F_n) y`, whose entries
are `ŷ_k = ∑_j ω_n^{-kj} y_j`. Here `F_n` is the backbone `Matrix.dft n`, and `conj(F_n)` is its
conjugate transpose, the two agreeing because `F_n` is symmetric. -/
theorem definition_4_3_1 {n : ℕ} (y : Fin n → ℂ) :
    (∀ j k : Fin n, dft n j k = Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))) ∧
      ∀ k : Fin n, ((dft n)ᴴ *ᵥ y) k
        = ∑ j : Fin n, (Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (j : ℕ)))⁻¹ * y j := by
  refine ⟨fun j k => dft_apply j k, fun k => ?_⟩
  rw [conjTranspose_dft_mulVec_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [inv_pow, Nat.mul_comm (k : ℕ) (j : ℕ)]

/-- **Exercise 4.3.1**, the summation formula (4.3.5): `∑_k ω_n^{kl} ω_n^{-kj} = n` when `j = l`
and `0` otherwise. It is the orthogonality of the columns of `F_n`, from which the inversion
formula of Theorem 4.3.2 follows. -/
theorem exercise_4_3_1 (n : ℕ) (j l : Fin n) :
    ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (l : ℕ))
        * (Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (j : ℕ)))⁻¹
      = if j = l then (n : ℂ) else 0 := by
  have h := congrFun₂ (conjTranspose_dft_mul_dft n) j l
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have hgoal : (if j = l then (n : ℂ) else 0) = (n : ℂ) * (if j = l then 1 else 0) := by
    split_ifs <;> ring
  rw [hgoal, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_dft_apply, dft_apply, inv_pow, Nat.mul_comm (j : ℕ) (k : ℕ)]
  exact mul_comm _ _

/-- **Theorem 4.3.2**, (4.3.3)–(4.3.4). The matrix `conj(F_n)` of the discrete Fourier transform is
invertible with `conj(F_n)⁻¹ = F_n / n`, so the transform is inverted by
`y_j = n⁻¹ ∑_k ω_n^{jk} ŷ_k`. -/
theorem theorem_4_3_2 {n : ℕ} [NeZero n] :
    ((dft n)ᴴ)⁻¹ = (n : ℂ)⁻¹ • dft n ∧
      ∀ (y : Fin n → ℂ) (j : Fin n), y j = (n : ℂ)⁻¹
        * ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ)) * ((dft n)ᴴ *ᵥ y) k := by
  refine ⟨inv_conjTranspose_dft n, fun y j => ?_⟩
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := congrFun (dft_mulVec_conjTranspose_dft_mulVec y) j
  rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum] at h
  have hsum : ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))
      * ((dft n)ᴴ *ᵥ y) k = ∑ k : Fin n, dft n j k * ((dft n)ᴴ *ᵥ y) k :=
    Finset.sum_congr rfl fun k _ => by rw [dft_apply]
  rw [hsum, h, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- **(4.3.6)–(4.3.9)**, the radix-2 splitting on which the fast Fourier transform is built: for
`y` of length `2n`, the transform is assembled from the two length-`n` transforms `E` and `O` of
the even- and odd-indexed halves of `y` as `ŷ_k = E_k + ω_{2n}^{-k} O_k` and
`ŷ_{k+n} = E_k - ω_{2n}^{-k} O_k` for `k < n`, at the cost of one multiplication per output
entry. -/
theorem equation_4_3_9 {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
        = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
          + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
            * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k ∧
      ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ) + n, by omega⟩
        = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
          - (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
            * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  ⟨dft_radix_two y k, dft_radix_two_add y k⟩

end AtkinsonHan.Ch04
