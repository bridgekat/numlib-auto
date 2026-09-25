import Numlib.Analysis.Fourier.Circulant
import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.Direct.FastPoisson
import Numlib.FloatingPoint.Program
import NumlibSurface.GolubVanLoan.Chapter01.Section04

/-!
# Golub–Van Loan §4.8: circulant and discrete Poisson systems

Surface file for [golub2013matrix] §4.8: solving through an eigenvalue decomposition (4.8.2), the
inverse of the DFT matrix (§4.8.1), circulant matrices and their diagonalization by the DFT
((4.8.3)–(4.8.4), Lemma 4.8.1, Theorem 4.8.2, Algorithm 4.8.1), the one- and two-dimensional
discrete Poisson problems ((4.8.6)–(4.8.12)), the fast Poisson solver framework (Algorithm 4.8.2),
the inverses of the DST and DCT (§4.8.5), the sine and cosine vectors under the second-difference
matrices (Lemma 4.8.3, (4.8.16)–(4.8.21)), the four fast eigenvalue decompositions
((4.8.22)–(4.8.25)) and the symmetrization of `𝒯^{(DN)}` (§4.8.7).

## Conventions

The book's DFT matrix `F_n` (`ω_n = e^{−2πi/n}`) is chapter 1's
`GolubVanLoan.Chapter01.fourierMatrix n = (Matrix.dft n)ᴴ`, and its entrywise conjugate `F̄_n` is
`(fourierMatrix n).map star = Matrix.dft n` (`map_star_fourierMatrix`). The book's circulant `C(z)`
(first column `z`) is Mathlib's `Matrix.circulant z`, the downshift `𝒟_n` is `Matrix.downshift n`.
The second-difference matrices are `𝒯^{(DD)}_n = Matrix.symmTridiagonalToeplitz n (-1) 2` and
`Matrix.secondDifferenceDN/NN/Periodic n`; the vectors `s(θ)`, `c(θ)` of (4.8.15) are
`Matrix.sinAngleVec n θ`, `Matrix.cosAngleVec n θ`; `e_1`, `e_n` are `Pi.single ⟨0, _⟩ 1`,
`Pi.single ⟨n − 1, _⟩ 1`. The transforms are `Matrix.dst1` (the book's `DST(n)`), `Matrix.dst2`
(`DST2(n)`) and `Matrix.dct1 m` (`DCT(m + 1)`). The book's eigenvalue letter `λ` is a Lean
keyword; diagonals are named `ν`, `μ`, `Λ`. Indices are 0-based: the book's `λ_{j+1}` is entry `j`.

`reshape(u, n₁, n₂)` is Mathlib's column-major `Matrix.vec` read backwards: `u = vec U` with
`U : Matrix (Fin n₁) (Fin n₂) ℝ` and `u` indexed by `Fin n₂ × Fin n₁`. The book's
`I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}` is written literally, `1 ⊗ₖ A₁ + A₂ ⊗ₖ 1`, and is the Kronecker sum
`A₂ ⊕ₖ A₁` of the backbone (`one_kronecker_add_kronecker_one`).

Algorithms 4.8.1 and 4.8.2 follow the algorithm conventions of `NumlibSurface/GolubVanLoan`: every
product, sum and quotient passes through the hook `rnd`; the book's fast transforms ("use an FFT")
are any evaluation of the matrix–vector products, written here as row-by-row dot products
(`mulVecAccum`, `mulMatAccum`). Only the exact semantics is stated (the book gives no rounding
analysis); Algorithm 4.8.1 is complex, `rnd : ℂ → M ℂ`.

## Sources

Backbone `Numlib/Analysis/Fourier/{DFT,Circulant,SineCosineTransform}` (the DFT, circulant, DST and
DCT facts and the four eigensystems), `Numlib/LinearAlgebra/Matrix/{Permutation,TridiagonalToeplitz,
KroneckerSum}` and `Numlib/Direct/FastPoisson` (the solution formula of the fast Poisson framework).

## Readings and errata

(4.8.4) prints `(V⁻¹ 𝒟_n V⁻¹)^k`; `(V⁻¹ 𝒟_n V)^k` is meant. In §4.8.6 the Neumann–Neumann paragraph
twice writes `𝒯^{(DN)}`/`V^{(DN)}` for `𝒯^{(NN)}`/`V^{(NN)}`, and the Dirichlet–Neumann paragraph
cites a nonexistent "(1.4.13)" for `DST2`, meaning (1.4.12). "`𝒯^{(P)}_n` is circulant" needs
`n ≥ 3`.
Lemma 4.8.1's `λ_{j+1} = ω̄_n^j` is read for every `n ≥ 1` (for `n = 1` the downshift is `I_1`).
-/

open Complex FloatingPoint Matrix GolubVanLoan.Chapter01
open scoped ComplexConjugate Real Kronecker

namespace GolubVanLoan.Chapter04

/-! ### (4.8.2): solving through an eigenvalue decomposition -/

/-- **(4.8.2).** If `V⁻¹ A V = Λ = diag(λ₁, …, λ_n)` (4.8.1) with `V` nonsingular, then
`u = A⁻¹ b = (V Λ V⁻¹)⁻¹ b = V (Λ⁻¹ (V⁻¹ b))`. -/
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

/-- The entrywise conjugate `F̄_n` of the DFT matrix is the backbone's `Matrix.dft n`. -/
theorem map_star_fourierMatrix (n : ℕ) : (fourierMatrix n).map star = dft n := by
  ext i j
  simp [fourierMatrix, conjTranspose_apply, dft_apply_comm]

/-- **§4.8.1**: "It is easy to verify that `F_nᴴ = F̄_n`" (`F_n` is symmetric). -/
theorem dft_conjTranspose (n : ℕ) : (fourierMatrix n)ᴴ = (fourierMatrix n).map star := by
  rw [map_star_fourierMatrix, fourierMatrix, conjTranspose_conjTranspose]

/-- **§4.8.1**: `n I_n = F_nᴴ F_n = F̄_n F_n`, from the orthogonality sums
`∑_k ω_n^{k(q−p)} = n δ_{pq}`. -/
theorem dft_conjTranspose_mul_self (n : ℕ) :
    (fourierMatrix n)ᴴ * fourierMatrix n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
      (fourierMatrix n).map star * fourierMatrix n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [dft_conjTranspose, map_star_fourierMatrix, fourierMatrix]
  exact ⟨dft_mul_conjTranspose_dft n, dft_mul_conjTranspose_dft n⟩

/-- **§4.8.1**: "the DFT matrix is a scaled unitary matrix and `F_n⁻¹ = (1/n) F̄_n`". -/
theorem dft_inv (n : ℕ) [NeZero n] :
    (fourierMatrix n)⁻¹ = (n : ℂ)⁻¹ • (fourierMatrix n).map star := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact inv_conjTranspose_dft n

/-- `F_n` is nonsingular (`n ≥ 1`). -/
theorem isUnit_fourierMatrix (n : ℕ) [NeZero n] : IsUnit (fourierMatrix n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  refine (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (B := (n : ℂ)⁻¹ • dft n) ?_)
  rw [Matrix.smul_mul, fourierMatrix, dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hn,
    one_smul]

/-! ### §4.8.2 Circulant systems -/

/-- **(4.8.3)**: `C(z) = ∑_{k=0}^{n−1} z_k 𝒟_n^k`, and `𝒟_n^n = I_n`. -/
theorem equation_4_8_3 {n : ℕ} [NeZero n] (z : Fin n → ℂ) :
    circulant z = ∑ k : Fin n, z k • (downshift n : Matrix (Fin n) (Fin n) ℂ) ^ (k : ℕ) ∧
      (downshift n : Matrix (Fin n) (Fin n) ℂ) ^ n = 1 :=
  ⟨circulant_eq_sum_downshift_pow z, downshift_pow_card n⟩

/-- **(4.8.4)**: if `V⁻¹ 𝒟_n V = Λ` is diagonal, then
`V⁻¹ C(z) V = ∑_{k=0}^{n−1} z_k Λ^k` is diagonal (the book prints `(V⁻¹ 𝒟_n V⁻¹)^k`, a misprint for
`(V⁻¹ 𝒟_n V)^k`). -/
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

/-- **Theorem 4.8.2.** For `z ∈ ℂⁿ`, `V = F_n` and `λ = F̄_n z`: `V⁻¹ C(z) V = diag(λ₁, …, λ_n)`. -/
theorem theorem_4_8_2 {n : ℕ} (z : Fin n → ℂ) :
    (fourierMatrix n)⁻¹ * circulant z * fourierMatrix n =
      diagonal ((fourierMatrix n).map star *ᵥ z) := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact inv_conjTranspose_dft_mul_circulant_mul_conjTranspose_dft z

/-- **Lemma 4.8.1.** If `V = F_n`, then `V⁻¹ 𝒟_n V = diag(λ₁, …, λ_n)` with
`λ_{j+1} = ω̄_n^j = cos(2jπ/n) + i sin(2jπ/n)`, `ω̄_n = e^{2πi/n}`. The downshift is the circulant
of the book's `e₂` (`Matrix.downshift_eq_circulant`), and Theorem 4.8.2 applies. -/
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

/-- Entry `i` of a loop writing each entry of its list once, from a value independent of the state.
-/
private theorem foldl_update_apply {ι β : Type} [DecidableEq ι] (c : ι → β) (l : List ι)
    (y₀ : ι → β) (i : ι) :
    l.foldl (fun (y : ι → β) a => Function.update y a (c a)) y₀ i =
      if i ∈ l then c i else y₀ i := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    by_cases hl : i ∈ l
    · simp [hl]
    · by_cases hia : i = a
      · subst hia
        simp [hl]
      · simp [hl, hia]

/-- A loop over `List.finRange n` whose step `a` writes entry `a` with `c a` ends with `c`. -/
private theorem foldl_update_finRange_apply {n : ℕ} {β : Type} (c : Fin n → β) (y₀ : Fin n → β)
    (i : Fin n) :
    (List.finRange n).foldl (fun (y : Fin n → β) a => Function.update y a (c a)) y₀ i = c i := by
  rw [foldl_update_apply]
  simp

section Programs

variable {M : Type → Type} [Monad M]

/-- **The matrix–vector product with a rounding hook**: `y = A x`, row by row, each entry an inner
product from `0` (`FloatingPoint.dotAccum`, Algorithm 1.1.1): the evaluation of the transforms
`F_n x`, `F̄_n x`, `V x`, `V⁻¹ x` of §4.8 in the programs of this section. -/
def mulVecAccum {K : Type} [NonUnitalNonAssocSemiring K] {m n : ℕ} (rnd : K → M K)
    (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) : M (Fin m → K) :=
  (List.finRange m).foldlM (fun (y : Fin m → K) (i : Fin m) => do
    let c ← dotAccum rnd (List.finRange n) (A i) x 0
    pure (Function.update y i c)) 0

/-- **The matrix product with a rounding hook**: `C = A X`, column by column by `mulVecAccum`. -/
def mulMatAccum {K : Type} [NonUnitalNonAssocSemiring K] {m k p : ℕ} (rnd : K → M K)
    (A : Matrix (Fin m) (Fin k) K) (X : Matrix (Fin k) (Fin p) K) :
    M (Matrix (Fin m) (Fin p) K) := do
  let cols ← (List.finRange p).foldlM (fun (C : Fin p → Fin m → K) (j : Fin p) => do
    let c ← mulVecAccum rnd A (fun i => X i j)
    pure (Function.update C j c)) 0
  pure (of fun i j => cols j i)

/-- **Algorithm 4.8.1.** "If `z ∈ ℂⁿ`, `y ∈ ℂⁿ`, and `C(z)` is nonsingular, then the following
algorithm solves the linear system `C(z) x = y`":
```
Use an FFT to compute c = F̄_n y and d = F̄_n z.
w = c./d
Use an FFT to compute u = F_n w.
x = u/n
```
The transforms are evaluated by `mulVecAccum` (any evaluation of `F̄_n ·` has the same exact
result; for `n = 2^t` chapter 1's FFT `GolubVanLoan.Chapter01.algorithm_1_4_1` is one). -/
noncomputable def algorithm_4_8_1 (rnd : ℂ → M ℂ) {n : ℕ} (z y : Fin n → ℂ) : M (Fin n → ℂ) := do
  let c ← mulVecAccum rnd ((fourierMatrix n).map star) y
  let d ← mulVecAccum rnd ((fourierMatrix n).map star) z
  let w ← (List.finRange n).foldlM (fun (w : Fin n → ℂ) (i : Fin n) => do
    let q ← rnd (c i / d i)
    pure (Function.update w i q)) 0
  let u ← mulVecAccum rnd (fourierMatrix n) w
  (List.finRange n).foldlM (fun (x : Fin n → ℂ) (i : Fin n) => do
    let q ← rnd (u i / n)
    pure (Function.update x i q)) 0

end Programs

/-- With the hook `pure`, `mulVecAccum` is the exact product `A x`. -/
theorem mulVecAccum_pure {M : Type → Type} [Monad M] [LawfulMonad M] {K : Type}
    [NonUnitalNonAssocSemiring K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    mulVecAccum (M := M) pure A x = pure (A *ᵥ x) := by
  unfold mulVecAccum
  simp only [dotAccum_pure, pure_bind, List.foldlM_pure]
  congr 1
  funext i
  rw [foldl_update_finRange_apply, zero_add, mulVec, dotProduct,
    Fin.sum_univ_def]

/-- With the hook `pure`, `mulMatAccum` is the exact product `A X`. -/
theorem mulMatAccum_pure {M : Type → Type} [Monad M] [LawfulMonad M] {K : Type}
    [NonUnitalNonAssocSemiring K] {m k p : ℕ} (A : Matrix (Fin m) (Fin k) K)
    (X : Matrix (Fin k) (Fin p) K) : mulMatAccum (M := M) pure A X = pure (A * X) := by
  unfold mulMatAccum
  simp only [mulVecAccum_pure, pure_bind, List.foldlM_pure]
  congr 1
  ext i j
  rw [of_apply, foldl_update_finRange_apply, mul_apply, mulVec,
    dotProduct]

/-- **Exact correctness of Algorithm 4.8.1**: if `C(z)` is nonsingular (`n ≥ 1`), the exact run
solves `C(z) x = y`. By Theorem 4.8.2, `C(z) F_n = F_n diag(d)` with `d = F̄_n z`, whose entries
are nonzero because `C(z)` is nonsingular; then `C(z) (F_n (c ./ d)/n) = F_n F̄_n y / n = y`. -/
theorem algorithm_4_8_1_spec {n : ℕ} [NeZero n] {z : Fin n → ℂ} (hC : IsUnit (circulant z))
    (y : Fin n → ℂ) : circulant z *ᵥ Id.run (algorithm_4_8_1 pure z y) = y := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  -- the exact run
  have hrun : Id.run (algorithm_4_8_1 pure z y) =
      (n : ℂ)⁻¹ • (fourierMatrix n *ᵥ fun i =>
        ((fourierMatrix n).map star *ᵥ y) i / ((fourierMatrix n).map star *ᵥ z) i) := by
    simp only [algorithm_4_8_1, mulVecAccum_pure, pure_bind, List.foldlM_pure, Id.run_pure]
    funext i
    rw [foldl_update_finRange_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_inv_mul]
    congr 2
    funext k
    rw [foldl_update_finRange_apply]
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

/-! ### §4.8.3 The discretized Poisson equation in one dimension -/

/-- A row of `𝒯^{(DD)}_{N+1}` applied to the interior values `g_1, …, g_{N+1}` of a grid function
`g`: the second difference `2 g_{x+1} − g_x − g_{x+2}` with the boundary values `g_0`, `g_{N+2}`
added back in the first and last rows. -/
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

/-- **(4.8.6)** and the Dirichlet–Dirichlet system after it. With `h = (β − α)/m`,
`m = N + 2`, the divided difference is
`((u_{i+1} − u_i)/h − (u_i − u_{i−1})/h)/h = (u_{i−1} − 2u_i + u_{i+1})/h²`, and for `h ≠ 0` the
equations `(u_{i−1} − 2u_i + u_{i+1})/h² = −f_i`, `i = 1 : m − 1`, with the boundary values
`u_0 = u_α`, `u_m = u_β` are the system
`𝒯^{(DD)}_{m−1} u(1:m−1) = h² f(1:m−1) + u_α e_1 + u_β e_{m−1}`. -/
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

/-- **(4.8.8)**: `𝒯^{(DN)}_n = 𝒯^{(DD)}_n − e_n e_{n−1}ᵀ` (`2 ≤ n`). -/
theorem equation_4_8_8 {n : ℕ} (hn : 2 ≤ n) :
    secondDifferenceDN n = symmTridiagonalToeplitz n (-1) 2 -
      vecMulVec (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) (Pi.single ⟨n - 2, by omega⟩ 1) := by
  ext i j
  rw [secondDifferenceDN, Matrix.sub_apply, Matrix.sub_apply]
  congr 1
  simp only [of_apply, vecMulVec_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-- **(4.8.9)**: `𝒯^{(NN)}_n = 𝒯^{(DD)}_n − e_n e_{n−1}ᵀ − e_1 e_2ᵀ` (`2 ≤ n`). -/
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

/-- **(4.8.10)**: `𝒯^{(P)}_n = 𝒯^{(DD)}_n − e_1 e_nᵀ − e_n e_1ᵀ` (`2 ≤ n`). -/
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

/-- The book's `I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}` is the backbone's Kronecker sum `A₂ ⊕ₖ A₁`. -/
theorem one_kronecker_add_kronecker_one {R : Type*} [CommRing R] {n₁ n₂ : ℕ}
    (A₁ : Matrix (Fin n₁) (Fin n₁) R) (A₂ : Matrix (Fin n₂) (Fin n₂) R) :
    (1 : Matrix (Fin n₂) (Fin n₂) R) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) R) = A₂ ⊕ₖ A₁ := by
  rw [kroneckerSum_def, add_comm]

/-- The right-hand side `B` of the five-point system (§4.8.4, with `h_x = h_y = h`,
`m₁ = N₁ + 2`, `m₂ = N₂ + 2`): at the interior point `P = (a + 1, b + 1)` of the grid, `h² F(P)`
plus the values of `u` at the neighbours of `P` that lie on the boundary. The grid values are
`G i j ≈ u(α_x + i h, α_y + j h)`. -/
def fivePointRhs (N₁ N₂ : ℕ) (h : ℝ) (F G : ℕ → ℕ → ℝ) :
    Matrix (Fin (N₁ + 1)) (Fin (N₂ + 1)) ℝ :=
  of fun a b => h ^ 2 * F ((a : ℕ) + 1) ((b : ℕ) + 1)
    + (if (a : ℕ) = 0 then G 0 ((b : ℕ) + 1) else 0)
    + (if (a : ℕ) = N₁ then G (N₁ + 2) ((b : ℕ) + 1) else 0)
    + (if (b : ℕ) = 0 then G ((a : ℕ) + 1) 0 else 0)
    + (if (b : ℕ) = N₂ then G ((a : ℕ) + 1) (N₂ + 2) else 0)

/-- **§4.8.4, the five-point system.** With equal grid spacings `h`, the equations
`4u(P) − u(N) − u(E) − u(S) − u(W) = h² F(P)` at the interior grid points, the neighbours on the
boundary moved to the right-hand side (`fivePointRhs`), are the linear system
`(I_{m₂−1} ⊗ 𝒯^{(DD)}_{m₁−1} + 𝒯^{(DD)}_{m₂−1} ⊗ I_{m₁−1}) u = b` with `u = vec U` the interior
values (`U a b = u(a + 1, b + 1)`, `x` along the rows of `U`). -/
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
      mul_apply, mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [of_apply, transpose_apply, mul_comm]
  rw [Matrix.add_apply, r1, r2]
  simp only [fivePointRhs, of_apply]
  constructor <;> intro h' <;> linarith

/-- **(4.8.12)** reshaped: `(I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}) u = b` with `u = vec U`, `b = vec B`
(`U = reshape(u, n₁, n₂)`) iff `A₁ U + U A₂ᵀ = B`. -/
theorem equation_4_8_12 {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (U B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)) *ᵥ vec U
      = vec B ↔ A₁ * U + U * A₂ᵀ = B := by
  rw [one_kronecker_add_kronecker_one, kroneckerSum_mulVec_vec, vec_inj]

/-- **§4.8.4, the transformed system.** Under (4.8.13)–(4.8.14), `V⁻¹ A₁ V = D₁ = diag(ν)` and
`W⁻¹ A₂ W = D₂ = diag(μ)`, `A₁ U + U A₂ᵀ = B` iff `D₁ Ũ + Ũ D₂ = B̃` with `Ũ = V⁻¹ U W⁻ᵀ`,
`B̃ = V⁻¹ B W⁻ᵀ`; and when no `λ_i + μ_j` vanishes the unique solution is
`ũ_ij = b̃_ij / (λ_i + μ_j)`, i.e. `U = V Ũ Wᵀ`. -/
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

/-- In the setting of (4.8.13)–(4.8.14), if `A = I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}` is nonsingular then no
`λ_i + μ_j` vanishes ("For this to be well-defined, no eigenvalue of `A₁` can be the negative of an
eigenvalue of `A₂`"): otherwise `U = V e_i e_jᵀ Wᵀ ≠ 0` has `A vec U = 0`. -/
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

/-- **Algorithm 4.8.2 (Fast Poisson Solver Framework).** "Assume that `A₁ ∈ ℝ^{n₁×n₁}` and
`A₂ ∈ ℝ^{n₂×n₂}` have fast eigenvalue decompositions (4.8.13) and (4.8.14) and that the matrix
`A = I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}` is nonsingular. The following algorithm solves the linear system
`Au = b`":
```
B̃ = (W⁻¹ (V⁻¹ B)ᵀ)ᵀ where B = reshape(b, n₁, n₂)
for i = 1:n₁, for j = 1:n₂: ũ_ij = b̃_ij / (λ_i + μ_j)
u = reshape(U, n₁n₂, 1) where U = (W (V Ũ)ᵀ)ᵀ
```
The fast transforms are given as the matrices `V⁻¹`, `W⁻¹`, `V`, `W` (inputs `Vinv`, `Winv`, `V`,
`W`) applied by rounded products (`mulMatAccum`); `b` is indexed as `vec B`. -/
noncomputable def algorithm_4_8_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n₁ n₂ : ℕ}
    (Vinv V : Matrix (Fin n₁) (Fin n₁) ℝ) (Winv W : Matrix (Fin n₂) (Fin n₂) ℝ)
    (ν : Fin n₁ → ℝ) (μ : Fin n₂ → ℝ) (b : Fin n₂ × Fin n₁ → ℝ) : M (Fin n₂ × Fin n₁ → ℝ) := do
  let Y ← mulMatAccum rnd Vinv (of fun i j => b (j, i))
  let Z ← mulMatAccum rnd Winv Yᵀ
  let Ut ← (List.finRange n₁).foldlM (fun (U : Fin n₁ → Fin n₂ → ℝ) (i : Fin n₁) => do
    let r ← (List.finRange n₂).foldlM (fun (r : Fin n₂ → ℝ) (j : Fin n₂) => do
      let s ← rnd (ν i + μ j)
      let q ← rnd (Z j i / s)
      pure (Function.update r j q)) 0
    pure (Function.update U i r)) 0
  let P ← mulMatAccum rnd V (of Ut)
  let Q ← mulMatAccum rnd W Pᵀ
  pure (vec Qᵀ)

/-- **Exact correctness of Algorithm 4.8.2**: if `V⁻¹ A₁ V = diag(λ)`, `W⁻¹ A₂ W = diag(μ)`, the
transform inputs are the true inverses and `A = I_{n₂} ⊗ A₁ + A₂ ⊗ I_{n₁}` is nonsingular, the
exact run solves `A u = b`: it computes `U = V Ũ Wᵀ` with `ũ_ij = b̃_ij / (λ_i + μ_j)`,
`B̃ = V⁻¹ B W⁻ᵀ`, the solution of `FastPoisson.kroneckerSum_mulVec_vec_eq_iff`. -/
theorem algorithm_4_8_2_spec {n₁ n₂ : ℕ} {A₁ V : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ W : Matrix (Fin n₂) (Fin n₂) ℝ} (hV : IsUnit V) (hW : IsUnit W) {ν : Fin n₁ → ℝ}
    {μ : Fin n₂ → ℝ} (hA₁ : V⁻¹ * A₁ * V = diagonal ν) (hA₂ : W⁻¹ * A₂ * W = diagonal μ)
    (hA : IsUnit ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ +
      A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)))
    (b : Fin n₂ × Fin n₁ → ℝ) :
    ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) ⊗ₖ A₁ + A₂ ⊗ₖ (1 : Matrix (Fin n₁) (Fin n₁) ℝ)) *ᵥ
      Id.run (algorithm_4_8_2 pure V⁻¹ V W⁻¹ W ν μ b) = b := by
  rw [one_kronecker_add_kronecker_one] at hA ⊢
  have hνμ := add_ne_zero_of_isUnit_kroneckerSum hV hW hA₁ hA₂ hA
  set B : Matrix (Fin n₁) (Fin n₂) ℝ := of fun i j => b (j, i) with hB
  have hBt : (W⁻¹ * (V⁻¹ * B)ᵀ)ᵀ = V⁻¹ * B * W⁻¹ᵀ := by
    rw [transpose_mul, transpose_transpose]
  have hrun : Id.run (algorithm_4_8_2 pure V⁻¹ V W⁻¹ W ν μ b) =
      vec (V * (of fun i j => (V⁻¹ * B * W⁻¹ᵀ) i j / (ν i + μ j)) * Wᵀ) := by
    simp only [algorithm_4_8_2, mulMatAccum_pure, pure_bind, List.foldlM_pure, Id.run_pure]
    congr 1
    rw [transpose_mul, transpose_transpose]
    congr 2
    ext i j
    rw [of_apply, foldl_update_finRange_apply, foldl_update_finRange_apply, of_apply, ← hBt,
      transpose_apply]
  rw [hrun, (FastPoisson.kroneckerSum_mulVec_vec_eq_iff hV hW hA₁ hA₂ hνμ _ B).2 rfl]
  rfl

/-- **§4.8.4**: for `A₁ = 𝒯^{(DD)}_{n₁}`, `A₂ = 𝒯^{(DD)}_{n₂}`, "`A` is symmetric positive definite
with bandwidth `n₁ + 1`": lower and upper bandwidth `n₁` in the positional layout `Fin (n₂ n₁)`
(the book's bandwidth counts the diagonal). -/
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

/-- **§4.8.5**: `V = DST(m − 1) ⇒ V⁻¹ = (2/m) DST(m − 1)` (`m ≥ 1`), from `2 S_{m−1}² = m I`. -/
theorem dst_inv {m : ℕ} (hm : 1 ≤ m) : (dst1 (m - 1))⁻¹ = (2 / m : ℝ) • dst1 (m - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by rw [Nat.cast_sub hm]; ring
  refine inv_eq_left_inv ?_
  rw [Matrix.smul_mul, dst1_mul_self, hcast, smul_smul, div_mul_div_comm, mul_comm (2 : ℝ),
    div_self (mul_ne_zero hm' two_ne_zero), one_smul]

/-- **§4.8.5**: `V = DCT(m + 1) ⇒ V⁻¹ = (2/m) DCT(m + 1)` (`m ≥ 1`). -/
theorem dct_inv {m : ℕ} (hm : 0 < m) : (dct1 m)⁻¹ = (2 / m : ℝ) • dct1 m := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  refine inv_eq_left_inv ?_
  rw [Matrix.smul_mul, dct1_mul_self hm, smul_smul, div_mul_div_comm, mul_comm (2 : ℝ),
    div_self (mul_ne_zero hm' two_ne_zero), one_smul]

/-- The book's real vector `v = (−1, 1, …, (−1)^{m−1})` of Theorem 1.4.1 and §4.8.5, 0-based
`v_j = (−1)^{j+1}` (chapter 1's `altSignVec m` is its complex form). -/
def altSignVecReal (m : ℕ) : Fin (m - 1) → ℝ := fun j => (-1) ^ ((j : ℕ) + 1)

/-- Real parts of the products of `x ± i y` met in the block identities. -/
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

/-- A sum over `Fin (2m)` split along the index blocks `0`, `1 : m − 1`, `m`, `m + 1 : 2m − 1` of
Theorem 1.4.1. -/
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

/-- Row `a` of the second block row of `F̄_{2m} F_{2m} = 2m I`, expanded along the index blocks
(the last block reindexed by `t ↦ rev t`). -/
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
  rw [mul_apply] at h
  simpa only [map_apply, Matrix.smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] using h

/-- **§4.8.5, the block identities.** With `C = C_{m−1}`, `S = S_{m−1}`, `e = (1, …, 1)` and
`v = (−1, 1, …, (−1)^{m−1})` as in Theorem 1.4.1, comparing the `(2,1)`, `(2,2)`, `(2,3)` and
`(2,4)` blocks of `2m I = F̄_{2m} F_{2m}` gives `0 = 2Ce + e + v`,
`2m I = 2C² + 2S² + eeᵀ + vvᵀ`, `0 = 2Cv + e + (−1)^m v`, `0 = 2C² − 2S² + eeᵀ + vvᵀ`; "it follows
that `2S² = m I` and `2C² = m I − eeᵀ − vvᵀ`". -/
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
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, vecMulVec_apply,
      one_apply, mul_one, mul_ite, mul_zero]
    split_ifs at h ⊢ <;> linear_combination h
  · funext a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec, dotProduct]
    linear_combination fc a
  · ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_apply,
      vecMulVec_apply, Matrix.zero_apply, mul_one]
    linear_combination fd a b
  · ext a b
    have h := fb a b
    have h' := fd a b
    simp only [Matrix.smul_apply, smul_eq_mul, mul_apply, one_apply, mul_ite, mul_one, mul_zero]
    split_ifs at h ⊢ <;> linear_combination (h - h') / 2
  · ext a b
    have h := fb a b
    have h' := fd a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, one_apply, mul_ite,
      mul_one, mul_zero, vecMulVec_apply]
    split_ifs at h ⊢ <;> linear_combination (h + h') / 2

end DSTBlocks

/-! ### §4.8.6 Four fast eigenvalue decompositions -/

/-- `2 − 2 cos θ = 4 sin² (θ / 2)`. -/
private theorem two_sub_two_mul_cos' (θ : ℝ) :
    2 + 2 * (-1) * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h2 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
  rw [h2, Real.cos_two_mul]
  linear_combination (-4) * Real.cos_sq_add_sin_sq (θ / 2)

/-- **(4.8.16)**: `𝒯^{(DD)}_n s(θ) = λ s(θ) + s_{n+1} e_n`, `λ = 4 sin²(θ/2)`. -/
theorem equation_4_8_16 {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    symmTridiagonalToeplitz n (-1) 2 *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
        Real.sin ((n + 1) * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
  rw [symmTridiagonalToeplitz_mulVec_sinAngleVec (-1) 2 hn, two_sub_two_mul_cos', neg_one_mul,
    neg_smul, sub_neg_eq_add]

/-- **(4.8.17)**: `𝒯^{(DD)}_n c(θ) = λ c(θ) + c_1 e_1 + c_n e_n` (`2 ≤ n`). -/
theorem equation_4_8_17 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    symmTridiagonalToeplitz n (-1) 2 *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        Real.cos θ • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        Real.cos (n * θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 := by
  rw [symmTridiagonalToeplitz_mulVec_cosAngleVec (-1) 2 hn, two_sub_two_mul_cos', neg_one_mul,
    neg_one_mul, neg_smul, neg_smul, sub_neg_eq_add, sub_neg_eq_add]

/-- **(4.8.18)**: `𝒯^{(DN)}_n s(θ) = λ s(θ) + (s_{n+1} − s_{n−1}) e_n` (`2 ≤ n`). -/
theorem equation_4_8_18 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferenceDN n *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ +
        (Real.sin ((n + 1) * θ) - Real.sin ((n - 1) * θ)) •
          Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferenceDN_mulVec_sinAngleVec hn θ

/-- **(4.8.19)**: `𝒯^{(NN)}_n c(θ) = λ c(θ) + (c_n − c_{n−2}) e_n` (`2 ≤ n`). -/
theorem equation_4_8_19 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferenceNN n *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        (Real.cos (n * θ) - Real.cos ((n - 2) * θ)) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferenceNN_mulVec_cosAngleVec hn θ

/-- **(4.8.20)**: `𝒯^{(P)}_n s(θ) = λ s(θ) − s_n e_1 + (s_{n+1} − s_1) e_n` (`2 ≤ n`). -/
theorem equation_4_8_20 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferencePeriodic n *ᵥ sinAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • sinAngleVec n θ -
        Real.sin (n * θ) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        (Real.sin ((n + 1) * θ) - Real.sin θ) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferencePeriodic_mulVec_sinAngleVec hn θ

/-- **(4.8.21)**: `𝒯^{(P)}_n c(θ) = λ c(θ) + (c_1 − c_{n−1}) e_1 + (c_n − 1) e_n` (`2 ≤ n`). -/
theorem equation_4_8_21 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    secondDifferencePeriodic n *ᵥ cosAngleVec n θ =
      (4 * Real.sin (θ / 2) ^ 2) • cosAngleVec n θ +
        (Real.cos θ - Real.cos ((n - 1) * θ)) • Pi.single (⟨0, by omega⟩ : Fin n) 1 +
        (Real.cos (n * θ) - 1) • Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 :=
  secondDifferencePeriodic_mulVec_cosAngleVec hn θ

/-- **Lemma 4.8.3.** For the real `n`-vectors `s(θ)`, `c(θ)` of (4.8.15), `s_k = sin(kθ)`,
`c_k = cos(kθ)`, and `λ = 4 sin²(θ/2)`, the six identities (4.8.16)–(4.8.21) hold (`2 ≤ n`). -/
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

/-- A nonsingular `V` whose columns are eigenvectors of `A` diagonalizes it. -/
private theorem inv_mul_mul_eq_diagonal {n : ℕ} {A V : Matrix (Fin n) (Fin n) ℝ} {γ : Fin n → ℝ}
    (hV : IsUnit V) (hAV : A * V = V * diagonal γ) : V⁻¹ * A * V = diagonal γ := by
  rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det V).1 hV), Matrix.one_mul]

/-- A matrix whose square is a nonzero multiple of the identity is nonsingular. -/
private theorem isUnit_of_mul_self_eq_smul {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : c ≠ 0) (h : V * V = c • 1) : IsUnit V := by
  refine (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (B := c⁻¹ • V) ?_)
  rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **§4.8.6, the Dirichlet–Dirichlet matrix.** For `θ_j = jπ/(n + 1)` the residual `s_{n+1}`
vanishes and `𝒯^{(DD)}_n s(θ_j) = 4 sin²(θ_j/2) s(θ_j)`; the eigenvector matrix
`[V^{(DD)}]_{kj} = sin(kjπ/(n+1))` is `DST(n)`, nonsingular, and
`V⁻¹ 𝒯^{(DD)}_n V = diag(4 sin²(jπ/(2(n+1))))` (0-based `j + 1` for the book's `j`). -/
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

/-- **§4.8.6, the Dirichlet–Neumann matrix.** For `θ_j = (2j − 1)π/(2n)` (0-based `(2j + 1)π/(2n)`)
the residual `s_{n+1} − s_{n−1} = 2 s_1 c_n` vanishes and `𝒯^{(DN)}_n s(θ_j) = 4 sin²(θ_j/2)
s(θ_j)`;
the eigenvector matrix `[V^{(DN)}]_{kj} = sin(k(2j − 1)π/(2n))` is `DST2(n)`, nonsingular, and
`V⁻¹ 𝒯^{(DN)}_n V = diag(4 sin²((2j − 1)π/(4n)))` (`2 ≤ n`; the book's pointer "(1.4.13)" is
(1.4.12)). -/
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

/-- **§4.8.6, the Neumann–Neumann matrix** (`n = m + 1`). For `θ_j = (j − 1)π/(n − 1)` (0-based
`jπ/m`) the residual `c_n − c_{n−2} = −2 s_1 s_{n−1}` vanishes and
`𝒯^{(NN)}_n c(θ_j) = 4 sin²(θ_j/2) c(θ_j)`; the eigenvector matrix
`[V^{(NN)}]_{kj} = cos((k − 1)(j − 1)π/(n − 1))` is `DCT(n) · diag(2, I_{n−2}, 2)`, nonsingular, and
`V⁻¹ 𝒯^{(NN)}_n V = diag(4 sin²((j − 1)π/(2(n − 1))))`. (The book twice writes `𝒯^{(DN)}`,
`V^{(DN)}`
for `𝒯^{(NN)}`, `V^{(NN)}` in this paragraph.) -/
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
  refine ⟨secondDifferenceNN_mulVec_dct1_col hm, fun k j => ?_, hu,
    inv_mul_mul_eq_diagonal hu (secondDifferenceNN_mul_dct1_mul_diagonal hm)⟩
  rw [dct1_mul_diagonal_apply, cosAngleVec_apply]
  congr 1
  ring

/-- **§4.8.6, the periodic matrix** (`n ≥ 3`). `𝒯^{(P)}_n` is the circulant of `(2, −1, 0, …, 0,
−1)`,
so by Theorem 4.8.2 `F_n⁻¹ 𝒯^{(P)}_n F_n = diag(λ)` with `λ = F̄_n (2, −1, 0, …, 0, −1)ᵀ`, and "it
can
be shown that" `λ_j = 4 sin²((j − 1)π/n)` (0-based `4 sin²(jπ/n)`). -/
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

/-- **(4.8.22)**: the eigenvalues of `𝒯^{(P)}_n` satisfy `λ_j = λ_{n+2−j}` for `j = 2:n`
(0-based: the `j`-th and `(n − j)`-th diagonal entries of `F_n⁻¹ 𝒯^{(P)}_n F_n` agree, `0 < j`). -/
theorem equation_4_8_22 {n : ℕ} (hn : 3 ≤ n) (j : Fin n) (hj : 0 < (j : ℕ)) :
    ((fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
        fourierMatrix n) j j =
      ((fourierMatrix n)⁻¹ * (secondDifferencePeriodic n).map (fun x : ℝ => (x : ℂ)) *
        fourierMatrix n) ⟨n - j, by omega⟩ ⟨n - j, by omega⟩ := by
  rw [(periodic_eigen hn).2.2, diagonal_apply_eq, diagonal_apply_eq]
  congr 1
  exact secondDifferencePeriodic_eigenvalue_symm j.isLt.le

/-- **(4.8.23)**: `F̄_n(:, j) = F_n(:, n + 2 − j)` for `j = 2:n` (0-based `F̄_n(:, j) = F_n(:, n −
j)`,
`0 < j`), since `ω_n^{n−k} = ω̄_n^k`. -/
theorem equation_4_8_23 {n : ℕ} (i j : Fin n) (hj : 0 < (j : ℕ)) :
    (fourierMatrix n).map star i j = fourierMatrix n i ⟨n - j, by omega⟩ := by
  rw [map_star_fourierMatrix, fourierMatrix]
  exact conj_dft_col_eq i j hj

/-- **(4.8.24)–(4.8.25)** (`n ≥ 3`): with `m = ⌈(n + 1)/2⌉` and
`V^{(P)}_n = [Re(F_n(:, 1:m)) | Im(F_n(:, m+1:n))]` (`Matrix.realDftCol`, 0-based columns `j < m`
real parts), `𝒯^{(P)}_n V^{(P)}_n(:, j) = λ_j V^{(P)}_n(:, j)` for every `j`. -/
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

/-- **§4.8.7**: "if `D = diag(I_{n−1}, √2)`, then `D⁻¹ 𝒯^{(DN)}_n D` is symmetric"
(for every `n`). -/
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
