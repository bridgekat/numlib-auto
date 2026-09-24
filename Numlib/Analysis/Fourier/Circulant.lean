/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Circulant`, with the discrete Fourier transform.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Fourier.DFT
import Numlib.LinearAlgebra.Matrix.Toeplitz

/-!
# The diagonalization of circulant matrices by the discrete Fourier transform

Every circulant matrix `C(z) = Matrix.circulant z` is diagonalized by the discrete Fourier
transform ([golub2013matrix] §4.8.2, Theorem 4.8.2), and so is the periodic second difference, a
circulant ([golub2013matrix] §4.8.6).

## Conventions

`Matrix.dft n` of `Numlib.Analysis.Fourier.DFT` is `(ω^{jk})` with `ω = exp (2 π i / n)`. The
transform matrix of the numerical literature is `F_n = (ω̄^{jk}) = (dft n)ᴴ`, and Golub–Van Loan's
theorem reads `F_n⁻¹ C(z) F_n = diag (F̄_n z)`: the columns of `(dft n)ᴴ` are eigenvectors of every
circulant, with eigenvalues the entries of `dft n *ᵥ z`
(`Matrix.circulant_mulVec_conj_dft_col`,
`Matrix.inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft`).
The opposite convention, in which the columns of `dft n` are the eigenvectors with eigenvalues the
entries of `(dft n)ᴴ *ᵥ z` (`Matrix.circulant_mulVec_dft_col`,
`Matrix.circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft`), is its complex conjugate; it is the
form of the von Neumann stability analysis of `Numlib.FiniteDifference.VonNeumann`, whose Fourier
modes are the columns of `dft n`. Both rest on one computation, the character property
`ω^{(j - s) k} = ω^{jk} ω^{-sk}` of the columns (`Matrix.dft_apply_sub`).

## The periodic second difference

`𝒯^{(P)}_n` is the circulant of `(2, −1, 0, …, 0, −1)`
(`Matrix.secondDifferencePeriodic_eq_circulant` of `Numlib.LinearAlgebra.Matrix.Toeplitz`), so its
eigenvalues are `2 − ω^j − ω^{−j} = 4 sin² (j π / n)`
(`Matrix.inv_conjTranspose_dft_mul_secondDifferencePeriodic_mul_conjTranspose_dft`), symmetric
under `j ↦ n − j` ([golub2013matrix] (4.8.22)), and because the matrix and its eigenvalues
are real, the real and imaginary parts of the columns of `F_n` are real eigenvectors
([golub2013matrix] (4.8.24)–(4.8.25), `Matrix.secondDifferencePeriodic_mulVec_realDftCol`).

Mathlib has `Matrix.circulant` and its algebra but no diagonalization.
-/

open Finset
open scoped Real ComplexConjugate

namespace Matrix

variable {n : ℕ}

/-! ### The character property of the columns -/

/-- The columns of `dft n` are characters of `Fin n`: `ω^{(j - s) k} = ω^{jk} ω^{-sk}`, i.e.
`dft n (j - s) k = dft n j k * (dft n)ᴴ k s` (subtraction in `Fin n`). -/
theorem dft_apply_sub (j s k : Fin n) : dft n (j - s) k = dft n j k * (dft n)ᴴ k s := by
  set ω := Complex.exp (2 * π * Complex.I / n) with hω
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hωN : ω ^ n = 1 := (Complex.isPrimitiveRoot_exp n k.pos.ne').pow_eq_one
  rw [dft_apply, dft_apply, conjTranspose_dft_apply, ← hω, Nat.mul_comm (k : ℕ) (s : ℕ),
    Fin.val_sub, pow_mul, ← pow_eq_pow_mod _ hωN, pow_add, pow_sub₀ _ hω0 s.isLt.le, hωN,
    one_mul, ← inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm]

/-- The entries of `(dft n)ᴴ` are symmetric in the two indices. -/
theorem conjTranspose_dft_apply_comm (j k : Fin n) : (dft n)ᴴ j k = (dft n)ᴴ k j := by
  rw [conjTranspose_apply, conjTranspose_apply, dft_apply_comm]

/-- The entries of `dft n` lie on the unit circle: `ω̄^{jk} ω^{jk} = 1`. -/
theorem conjTranspose_dft_apply_mul_dft_apply (j k : Fin n) :
    (dft n)ᴴ j k * dft n k j = 1 := by
  rw [conjTranspose_dft_apply, dft_apply, inv_pow, Nat.mul_comm (k : ℕ) (j : ℕ),
    inv_mul_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]

/-! ### The eigenvectors of a circulant -/

/-- **The columns of `F_n = (dft n)ᴴ` are eigenvectors of every circulant** ([golub2013matrix]
§4.8.2): `C(z) F_n(:, k) = (F̄_n z)_k F_n(:, k)`. Row `j`:
`∑_s z_{j-s} ω̄^{sk} = ω̄^{jk} ∑_t z_t ω^{tk}`, by the substitution `t = j - s` in `Fin n` and the
character property `Matrix.dft_apply_sub`. -/
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

/-- **The columns of `dft n` are eigenvectors of every circulant**, in the convention opposite to
Golub–Van Loan's: `C(z) (dft n)(:, k) = ((dft n)ᴴ z)_k (dft n)(:, k)`. The complex conjugate of
`circulant_mulVec_conj_dft_col` at `z̄`. -/
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

/-- A matrix whose action on each column of `V` is multiplication by `γ k` satisfies
`A V = V diag (γ)`. -/
theorem mul_eq_mul_diagonal_of_forall_mulVec_col {R ι : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] {A V : Matrix ι ι R} {γ : ι → R}
    (h : ∀ k, A *ᵥ (fun j => V j k) = γ k • fun j => V j k) : A * V = V * diagonal γ := by
  ext j k
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [mul_diagonal, mul_comm (V j k), ← hk]
  rfl

/-- `C(z) F_n = F_n diag (F̄_n z)`, column by column from `circulant_mulVec_conj_dft_col`. -/
theorem circulant_mul_conjTranspose_dft (z : Fin n → ℂ) :
    circulant z * (dft n)ᴴ = (dft n)ᴴ * diagonal (dft n *ᵥ z) :=
  mul_eq_mul_diagonal_of_forall_mulVec_col (circulant_mulVec_conj_dft_col z)

/-- `C(z) F̄_n = F̄_n diag (F_n z)`, column by column from `circulant_mulVec_dft_col`. -/
theorem circulant_mul_dft (z : Fin n → ℂ) :
    circulant z * dft n = dft n * diagonal ((dft n)ᴴ *ᵥ z) :=
  mul_eq_mul_diagonal_of_forall_mulVec_col (circulant_mulVec_dft_col z)

/-- **Golub–Van Loan Theorem 4.8.2** ([golub2013matrix]): `F_n⁻¹ C(z) F_n = diag (F̄_n z)` with
`F_n = (dft n)ᴴ` and `F̄_n z = dft n *ᵥ z`. The case `z = e_2` is Lemma 4.8.1, the diagonalization
of the downshift. -/
theorem inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft (z : Fin n → ℂ) :
    ((dft n)ᴴ)⁻¹ * circulant z * (dft n)ᴴ = diagonal (dft n *ᵥ z) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Matrix.mul_assoc, circulant_mul_conjTranspose_dft, ← Matrix.mul_assoc,
    inv_conjTranspose_dft, Matrix.smul_mul, dft_mul_conjTranspose_dft, smul_smul,
    inv_mul_cancel₀ hn, one_smul, Matrix.one_mul]

/-- Golub–Van Loan Theorem 4.8.2, spectral form: `C(z) = n⁻¹ F_n diag (F̄_n z) F̄_n`. -/
theorem circulant_eq_conjTranspose_dft_mul_diagonal_mul_dft (z : Fin n → ℂ) :
    circulant z = (n : ℂ)⁻¹ • ((dft n)ᴴ * diagonal (dft n *ᵥ z) * dft n) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← circulant_mul_conjTranspose_dft, Matrix.mul_assoc, conjTranspose_dft_mul_dft,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- The spectral form in the opposite convention: `C(z) = n⁻¹ F̄_n diag (F_n z) F_n`, with
`F̄_n = dft n` — the spectral decomposition of a periodic scheme in the von Neumann analysis. -/
theorem circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft (z : Fin n → ℂ) :
    circulant z = (n : ℂ)⁻¹ • (dft n * diagonal ((dft n)ᴴ *ᵥ z) * (dft n)ᴴ) := by
  rcases n with _ | n
  · exact Subsingleton.elim _ _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← circulant_mul_dft, Matrix.mul_assoc, dft_mul_conjTranspose_dft, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-! ### The periodic second difference -/

/-- The first column `(2, −1, 0, …, 0, −1)` of the periodic second difference. -/
private noncomputable def periodicColumn (n : ℕ) : Fin n → ℝ := fun k =>
  if (k : ℕ) = 0 then 2 else if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0

/-- `2 − 2 cos (2 x) = 4 sin² x`. -/
private theorem two_sub_two_mul_cos_two_mul (x : ℝ) :
    2 - 2 * Real.cos (2 * x) = 4 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination (-4) * Real.cos_sq_add_sin_sq x

/-- The eigenvalues of the periodic second difference: `F̄_n (2, −1, 0, …, 0, −1) =
(2 − ω^j − ω^{−j})_j = (4 sin² (j π / n))_j` for `3 ≤ n`. -/
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
  rw [hx, ← two_sub_two_mul_cos_two_mul]
  push_cast
  ring

/-- **The eigensystem of the periodic second difference** ([golub2013matrix] §4.8.6): for `3 ≤ n`,
the columns of `F_n = (dft n)ᴴ` are eigenvectors of `𝒯^{(P)}_n` with the eigenvalues
`λ_j = 4 sin² (j π / n)`. -/
theorem secondDifferencePeriodic_map_mulVec_conj_dft_col (hn : 3 ≤ n) (j : Fin n) :
    (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun k => (dft n)ᴴ k j)
      = ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) • fun k => (dft n)ᴴ k j := by
  rw [secondDifferencePeriodic_eq_circulant hn, map_circulant]
  rw [← dft_mulVec_periodicColumn hn j]
  exact circulant_mulVec_conj_dft_col _ j

/-- **The periodic second difference, diagonalized** ([golub2013matrix] §4.8.6): for `3 ≤ n`,
`F_n⁻¹ 𝒯^{(P)}_n F_n = diag (4 sin² (j π / n))` (1-based `λ_j = 4 sin² ((j − 1) π / n)`), the
eigenvalues `F̄_n (2, −1, 0, …, 0, −1) = 2 − ω^j − ω^{−j}` of the circulant. -/
theorem inv_conjTranspose_dft_mul_secondDifferencePeriodic_mul_conjTranspose_dft (hn : 3 ≤ n) :
    ((dft n)ᴴ)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) * (dft n)ᴴ
      = diagonal fun j : Fin n => ((4 * Real.sin ((j : ℕ) * π / n) ^ 2 : ℝ) : ℂ) := by
  rw [secondDifferencePeriodic_eq_circulant hn, map_circulant,
    inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft]
  congr 1
  funext j
  exact dft_mulVec_periodicColumn hn j

/-- [golub2013matrix] (4.8.22): the eigenvalues of the periodic second difference are symmetric,
`λ_j = λ_{n−j}` (`0`-based). -/
theorem secondDifferencePeriodic_eigenvalue_symm {j : ℕ} (hj : j ≤ n) :
    4 * Real.sin ((j : ℕ) * π / n) ^ 2 = 4 * Real.sin (((n - j : ℕ) : ℝ) * π / n) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hj, show ((n : ℝ) - j) * π / n = π - j * π / n by field_simp, Real.sin_pi_sub]

/-- [golub2013matrix] (4.8.23): the columns of `F̄_n` are columns of `F_n` read backwards,
`F̄_n(:, j) = F_n(:, n − j)` (`0`-based, `0 < j`). -/
theorem conj_dft_col_eq (i j : Fin n) (hj : 0 < (j : ℕ)) :
    dft n i j = (dft n)ᴴ i ⟨n - j, by omega⟩ := by
  rw [conjTranspose_apply, dft_apply_comm _ i, dft_apply_sub_eq_conj i j hj]
  exact (Complex.conj_conj _).symm

/-- The real eigenvector matrix `V^{(P)}_n` of the periodic second difference ([golub2013matrix]
(4.8.24)), column `j`: the real part `(cos (2 π k j / n))_k` of the column `F_n(:, j)` for `j < m`,
its imaginary part `(− sin (2 π k j / n))_k` for `j ≥ m`, where
`m = ⌈(n + 1) / 2⌉ = (n + 2) / 2`. -/
noncomputable def realDftCol (n : ℕ) (j : Fin n) : Fin n → ℝ :=
  if (j : ℕ) < (n + 2) / 2 then fun k => Real.cos (2 * π * (k : ℕ) * (j : ℕ) / n)
  else fun k => -Real.sin (2 * π * (k : ℕ) * (j : ℕ) / n)

/-- **Real eigenvectors of the periodic second difference** ([golub2013matrix] (4.8.25)): for
`3 ≤ n`, `𝒯^{(P)}_n V^{(P)}_n(:, j) = λ_j V^{(P)}_n(:, j)` for every `j`. The real and imaginary
parts of the complex eigenvector equation, since the matrix and the eigenvalue `4 sin² (j π / n)`
are real. -/
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
