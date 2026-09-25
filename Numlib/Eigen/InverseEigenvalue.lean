/-
Copyright (c) 2026 Numlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.QR

/-!
# The first-row resolvent and the eigenvector–eigenvalue identity

For a matrix diagonalized by a unitary `Q`, `Qᴴ A Q = diag(d)`, every entry of the resolvent is a
partial-fraction sum over the rows of `Q`, and every entry of the adjugate of `A - λ` is the
corresponding polynomial:

* `Matrix.inv_sub_smul_one_apply_eq_sum`: `((A - λ)⁻¹) j k = ∑ i, Q j i conj(Q k i) / (d i - λ)`,
  the book's (8.4.10) at `j = k = 0` ([golub2013matrix] §8.4.6), with its Hermitian form
  `Matrix.IsHermitian.inv_sub_apply_eq_sum`;
* `Matrix.inv_sub_apply_zero_zero_eq_det_div`: Cramer's rule at the corner,
  `((A - λ)⁻¹) 0 0 = det (A(2:n, 2:n) - λ) / det (A - λ)`;
* `Matrix.mul_star_mul_prod_eq_det_submatrix`: the two combined without a division, which holds at
  every `λ` and so may be evaluated at an eigenvalue: `Q 0 i conj(Q 0 i) ∏_{j ≠ i} (d j - d i)` is
  `det (A(2:n, 2:n) - d i)`. With the eigenvalues `μ` of the trailing block this is the
  **eigenvector–eigenvalue identity** `Matrix.IsHermitian.norm_sq_eigenvector_mul_prod_eq`,
  `|Q 0 i|² ∏_{j ≠ i} (λ_j - λ_i) = ∏_j (μ_j - λ_i)` (Denton, Parke, Tao and Zhang call it by that
  name; it is [golub2013matrix] (8.4.12) read in reverse);
* `Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`: for strictly interlacing data
  `λ_1 > μ_1 > λ_2 > ⋯ > μ_{n-1} > λ_n` the right-hand sides of (8.4.12) are positive and sum to
  `1` ([golub2013matrix] P8.4.7), so they are the squares of the entries of a unit vector.

The last fact is what the inverse tridiagonal eigenproblem of [golub2013matrix] §8.4.6 (G. H.
Golub, "Some modified matrix eigenvalue problems", SIAM Review 15 (1973)) rests on: given strictly
interlacing `λ` and `μ`, a symmetric tridiagonal matrix with eigenvalues `λ` whose trailing
principal submatrix has eigenvalues `μ` is obtained by tridiagonalizing `W Λ Wᵀ` for an orthogonal
`W` with first row `d`. This is `Matrix.exists_isTridiagonal_eigenvalues_eq_of_strictInterlace`,
with `W` from `Matrix.exists_mem_unitaryGroup_mulVec_single_eq` (a unitary with a prescribed
column, a scaled Householder reflector) and the tridiagonalization `Matrix.hessenbergReduce`, whose
unitary fixes `e₀` (`Matrix.hessenbergQ_apply_zero`).

## Implementation notes

The book indexes the first *column* of `Q` in `Qᵀ Λ Q = T`; with `T = Qᵀ Λ Q` the eigenvectors of
`T` are the rows of `Q`, so the book's `Q(:, 1)` is the first row of the eigenvector matrix of `T`.
The statements here are phrased on the eigenvector matrix of `A` itself, whose first row is
`fun i => Q 0 i`.

The route through the adjugate (`Matrix.adjugate_mul_distrib`, `Matrix.adjugate_diagonal`) gives
the eigenvector–eigenvalue identity as an identity of polynomials in `λ` evaluated directly at
`λ = λ_i`, with no limiting or polynomial-interpolation argument; the positivity and the sum rule
of the interlacing ratios are Lagrange interpolation (`Lagrange.leadingCoeff_eq_sum`).
-/

open Finset Polynomial

namespace Matrix

section Unitary

variable {K : Type*} [Field K] [StarRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse of a unitary conjugate is the unitary conjugate of the inverse:
`(Q M Qᴴ)⁻¹ = Q M⁻¹ Qᴴ` for `Q` unitary. `Matrix.mul_inv_rev` holds without invertibility, and
`Q⁻¹ = Qᴴ`. -/
theorem inv_mul_mul_star_of_mem_unitaryGroup {Q : Matrix n n K} (hQ : Q ∈ unitaryGroup n K)
    (M : Matrix n n K) : (Q * M * star Q)⁻¹ = Q * M⁻¹ * star Q := by
  have h1 : Q⁻¹ = star Q := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hQ)
  have h2 : (star Q)⁻¹ = Q := inv_eq_left_inv (mem_unitaryGroup_iff.mp hQ)
  rw [mul_inv_rev, mul_inv_rev, h1, h2, Matrix.mul_assoc]

/-- The adjugate of a unitary conjugate is the unitary conjugate of the adjugate:
`adj(Q M Qᴴ) = Q adj(M) Qᴴ` for `Q` unitary. `Matrix.adjugate_mul_distrib`, with
`adj Q = det Q • Qᴴ`, `adj Qᴴ = det Qᴴ • Q` and `det Qᴴ det Q = 1`. -/
theorem adjugate_mul_mul_star_of_mem_unitaryGroup {Q : Matrix n n K}
    (hQ : Q ∈ unitaryGroup n K) (M : Matrix n n K) :
    adjugate (Q * M * star Q) = Q * adjugate M * star Q := by
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  have hdet : det Q * det (star Q) = 1 := by rw [← det_mul, hQQ', det_one]
  have hadjQ : adjugate Q = det Q • star Q :=
    calc adjugate Q = star Q * Q * adjugate Q := by rw [hQQ, Matrix.one_mul]
      _ = det Q • star Q := by rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul,
          Matrix.mul_one]
  have hadjQ' : adjugate (star Q) = det (star Q) • Q :=
    calc adjugate (star Q) = Q * star Q * adjugate (star Q) := by rw [hQQ', Matrix.one_mul]
      _ = det (star Q) • Q := by rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul,
          Matrix.mul_one]
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hadjQ, hadjQ']
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hdet, one_smul, Matrix.mul_assoc]

variable {A Q : Matrix n n K} {d : n → K}

/-- A matrix diagonalized by a unitary `Q`, `Qᴴ A Q = diag(d)`, is `Q diag(d) Qᴴ`, and its shift by
`λ` is `Q diag(d - λ) Qᴴ`. -/
theorem sub_smul_one_eq_mul_diagonal_mul_star (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) (c : K) :
    A - c • 1 = Q * diagonal (fun i => d i - c) * star Q := by
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  have hA : A = Q * diagonal d * star Q := by
    rw [← hQA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc,
      hQQ', Matrix.mul_one]
  have hD : diagonal (fun i => d i - c) = diagonal d - c • 1 := by
    rw [smul_one_eq_diagonal, diagonal_sub]
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, ← hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hQQ']

/-- **The resolvent through an eigenbasis**: if `Qᴴ A Q = diag(d)` with `Q` unitary and `λ` is not
a `d i`, then `((A - λ)⁻¹) j k = ∑ i, Q j i conj(Q k i) / (d i - λ)`. At `j = k` this is the
partial-fraction expansion `∑ i, |Q j i|² / (d i - λ)` of [golub2013matrix] (8.4.10). -/
theorem inv_sub_smul_one_apply_eq_sum (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) {c : K} (hc : ∀ i, d i ≠ c) (j k : n) :
    (A - c • 1)⁻¹ j k = ∑ i, Q j i * star (Q k i) / (d i - c) := by
  have hinv : (diagonal fun i => d i - c)⁻¹ = diagonal fun i => (d i - c)⁻¹ :=
    inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hc i))))
  rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQA, inv_mul_mul_star_of_mem_unitaryGroup hQ,
    hinv, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, star_apply, div_eq_mul_inv]
  ring

/-- **The adjugate through an eigenbasis**: if `Qᴴ A Q = diag(d)` with `Q` unitary then, for every
`λ`, `adj(A - λ) j k = ∑ i, Q j i conj(Q k i) ∏_{l ≠ i} (d l - λ)`. The polynomial form of
`Matrix.inv_sub_smul_one_apply_eq_sum`, valid at the eigenvalues too. -/
theorem adjugate_sub_smul_one_apply_eq_sum (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) (c : K) (j k : n) :
    adjugate (A - c • 1) j k = ∑ i, Q j i * star (Q k i) * ∏ l ∈ univ.erase i, (d l - c) := by
  rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQA, adjugate_mul_mul_star_of_mem_unitaryGroup hQ,
    adjugate_diagonal, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, star_apply]
  ring

end Unitary

section Cramer

variable {K : Type*} [Field K] {N : ℕ}

/-- The trailing principal submatrix of a shift is the shift of the trailing principal submatrix. -/
theorem submatrix_succ_sub_smul_one (A : Matrix (Fin (N + 1)) (Fin (N + 1)) K) (c : K) :
    (A - c • 1).submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ - c • 1 := by
  ext i j
  simp [one_apply, Fin.succ_inj]

/-- **Cramer's rule at the corner** ([golub2013matrix] §8.4.6): the `(0, 0)` entry of the resolvent
is a ratio of characteristic determinants,
`((A - λ)⁻¹) 0 0 = det (A(2:n, 2:n) - λ) / det (A - λ)`. No hypothesis is needed: at an
eigenvalue both sides are `0` (`Matrix.inv_def` and `x / 0 = 0`). The `(0, 0)` cofactor is the
trailing principal minor (`Matrix.adjugate_fin_succ_eq_det_submatrix`). -/
theorem inv_sub_apply_zero_zero_eq_det_div (A : Matrix (Fin (N + 1)) (Fin (N + 1)) K) (c : K) :
    (A - c • 1)⁻¹ 0 0 = det (A.submatrix Fin.succ Fin.succ - c • 1) / det (A - c • 1) := by
  rw [inv_def, smul_apply, adjugate_fin_succ_eq_det_submatrix, Ring.inverse_eq_inv',
    Fin.succAbove_zero, submatrix_succ_sub_smul_one, smul_eq_mul, div_eq_inv_mul]
  simp

end Cramer

section EigenvectorEigenvalue

variable {K : Type*} [Field K] [StarRing K] {N : ℕ} {A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
  {d : Fin (N + 1) → K}

/-- **The eigenvector–eigenvalue identity**, determinant form: if `Qᴴ A Q = diag(d)` with `Q`
unitary, then for every `i`,
`Q 0 i conj(Q 0 i) ∏_{j ≠ i} (d j - d i) = det (A(2:n, 2:n) - d i)`. The `(0, 0)` entry of
`adj(A - d i)` computed twice: through the eigenbasis
(`Matrix.adjugate_sub_smul_one_apply_eq_sum`, where every term but the `i`-th carries the factor
`d i - d i = 0`) and as the trailing principal minor
(`Matrix.adjugate_fin_succ_eq_det_submatrix`). -/
theorem mul_star_mul_prod_eq_det_submatrix (hQ : Q ∈ unitaryGroup (Fin (N + 1)) K)
    (hQA : star Q * A * Q = diagonal d) (i : Fin (N + 1)) :
    Q 0 i * star (Q 0 i) * ∏ j ∈ univ.erase i, (d j - d i) =
      det (A.submatrix Fin.succ Fin.succ - d i • 1) := by
  have h := adjugate_sub_smul_one_apply_eq_sum hQ hQA (d i) 0 0
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, submatrix_succ_sub_smul_one] at h
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul] at h
  rw [h, Finset.sum_eq_single i]
  · intro k _ hk
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hk, Finset.mem_univ i⟩) (sub_self _),
      mul_zero]
  · simp

end EigenvectorEigenvalue

namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The determinant of a shifted Hermitian matrix is the product of its shifted eigenvalues,
`det (M - c) = ∏ (λ_i - c)`: the characteristic polynomial `∏ (X - λ_i)` (Mathlib's
`Matrix.IsHermitian.charpoly_eq`) evaluated at `c`, up to the sign `(-1)^n` of
`M - c = -(c - M)`. -/
theorem det_sub_smul_one_eq_prod {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) (c : 𝕜) : det (M - c • 1) = ∏ i, ((hM.eigenvalues i : 𝕜) - c) := by
  have h := congrArg (Polynomial.eval c) hM.charpoly_eq
  rw [eval_charpoly, eval_prod] at h
  simp only [eval_sub, eval_X, eval_C] at h
  have hneg : M - c • 1 = -(scalar n c - M) := by
    rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
  rw [hneg, det_neg, h, ← Finset.card_univ, ← Finset.prod_neg]
  simp [neg_sub]

/-- The Hermitian form of `Matrix.inv_sub_smul_one_apply_eq_sum`, in Mathlib's eigenbasis: for a
Hermitian `A` and a real `λ` that is not an eigenvalue,
`((A - λ)⁻¹) j k = ∑ i, U j i conj(U k i) / (λ_i - λ)` with `U = hA.eigenvectorUnitary`
([golub2013matrix] (8.4.10)). -/
theorem inv_sub_apply_eq_sum {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, hA.eigenvalues i ≠ c) (j k : n) :
    (A - (c : 𝕜) • 1)⁻¹ j k = ∑ i, (hA.eigenvectorUnitary : Matrix n n 𝕜) j i *
      star ((hA.eigenvectorUnitary : Matrix n n 𝕜) k i) / ((hA.eigenvalues i : 𝕜) - c) := by
  refine inv_sub_smul_one_apply_eq_sum hA.eigenvectorUnitary.2 ?_ (fun i h => hc i ?_) j k
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at this
    exact this
  · exact_mod_cast h

/-- **The eigenvector–eigenvalue identity** ([golub2013matrix] (8.4.12) read in reverse; Denton,
Parke, Tao and Zhang): for a Hermitian `A` of order `N + 1` diagonalized by a unitary `Q`,
`Qᴴ A Q = diag(l)`, and `μ` the eigenvalues of the trailing principal submatrix `A(2:n, 2:n)`,
`|Q 0 i|² ∏_{j ≠ i} (l j - l i) = ∏_j (μ_j - l i)` for every `i`. The determinant form
`Matrix.mul_star_mul_prod_eq_det_submatrix` with `det (A' - c) = ∏ (μ_j - c)`
(`Matrix.IsHermitian.det_sub_smul_one_eq_prod`). -/
theorem norm_sq_eigenvector_mul_prod_eq {N : ℕ} {A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜}
    (hA : A.IsHermitian) (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜) {l : Fin (N + 1) → ℝ}
    (hQA : star Q * A * Q = diagonal fun i => (l i : 𝕜)) (i : Fin (N + 1)) :
    ‖Q 0 i‖ ^ 2 * ∏ j ∈ univ.erase i, (l j - l i) =
      ∏ j, ((hA.submatrix Fin.succ).eigenvalues j - l i) := by
  have h := mul_star_mul_prod_eq_det_submatrix hQ hQA i
  rw [(hA.submatrix Fin.succ).det_sub_smul_one_eq_prod, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

end IsHermitian

/-- **The interlacing ratios are positive and sum to one** ([golub2013matrix] P8.4.7): for
strictly interlacing `l : Fin (N + 1) → ℝ` and `μ : Fin N → ℝ`,
`l 0 > μ 0 > l 1 > ⋯ > μ (N - 1) > l N` (the book's (8.4.7)), each
`r k = ∏_j (μ_j - l_k) / ∏_{j ≠ k} (l_j - l_k)` is positive and `∑ r k = 1`. Positivity: pairing
the `j`-th factor of the numerator with the factor of `l (k.succAbove j)` in the denominator, each
quotient is a ratio of two positive numbers (`j < k`) or of two negative ones (`j ≥ k`). The sum
is the leading coefficient `1` of `∏ (X - μ_j)` by Lagrange interpolation at the `l k`
(`Lagrange.leadingCoeff_eq_sum`). -/
theorem prod_sub_div_prod_sub_pos_of_strictInterlace {N : ℕ} {l : Fin (N + 1) → ℝ}
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    (∀ k, 0 < (∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k)) ∧
      ∑ k, (∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k) = 1 := by
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  have herase : ∀ k : Fin (N + 1), ∀ f : Fin (N + 1) → ℝ,
      ∏ j ∈ univ.erase k, f j = ∏ j : Fin N, f (k.succAbove j) := fun k f => by
    rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
      Finset.prod_image fun a _ b _ h => Fin.succAbove_right_injective h]
  refine ⟨fun k => ?_, ?_⟩
  · rw [herase, ← Finset.prod_div_distrib]
    refine Finset.prod_pos fun j _ => ?_
    rcases lt_or_ge j.castSucc k with hjk | hjk
    · rw [Fin.succAbove_of_castSucc_lt _ _ hjk]
      have hsk : j.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hjk
      exact div_pos (by linarith [h₂ j, hl.antitone hsk]) (by linarith [hl hjk])
    · rw [Fin.succAbove_of_le_castSucc _ _ hjk]
      exact div_pos_of_neg_of_neg (by linarith [h₁ j, hl.antitone hjk])
        (by linarith [hl (lt_of_le_of_lt hjk Fin.castSucc_lt_succ)])
  · have hP : (∏ j, (X - C (μ j))).leadingCoeff = 1 := (monic_prod_X_sub_C μ univ).leadingCoeff
    have hdeg : ((#(univ : Finset (Fin (N + 1))) : ℕ) : WithBot ℕ) =
        (∏ j, (X - C (μ j))).degree + 1 := by
      rw [degree_eq_natDegree (monic_prod_X_sub_C μ univ).ne_zero,
        natDegree_finsetProd_X_sub_C_eq_card]
      simp
    rw [Lagrange.leadingCoeff_eq_sum (hl.injective.injOn) hdeg] at hP
    rw [← hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    have hnum : ∏ j, (μ j - l k) = (-1) ^ N * ∏ j, (l k - μ j) := by
      have := Finset.prod_neg (s := univ) (fun j => l k - μ j)
      simpa only [neg_sub, card_univ, Fintype.card_fin] using this
    have hden : ∏ j ∈ univ.erase k, (l j - l k) = (-1) ^ N * ∏ j ∈ univ.erase k, (l k - l j) := by
      have := Finset.prod_neg (s := univ.erase k) (fun j => l k - l j)
      simpa only [neg_sub, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
        add_tsub_cancel_right] using this
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

section InverseProblem

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A unitary matrix with a prescribed column**: every unit vector `x` is the `i`-th column of a
unitary matrix, the multiple `-α P` of the reflector `P` that sends `x` to `-α eᵢ`, where
`α = phase (x i)` has modulus one (`Matrix.householder_mulVec_eq_smul_single`). -/
theorem exists_mem_unitaryGroup_mulVec_single_eq {x : n → 𝕜}
    (hx : ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ = 1) (i : n) :
    ∃ U ∈ unitaryGroup n 𝕜, U *ᵥ Pi.single i 1 = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hPx : householder (householderVec x i) *ᵥ x = (-phase (x i)) • Pi.single i 1 := by
    rw [householder_mulVec_eq_smul_single hx0, hx, RCLike.ofReal_one, mul_one]
  have hPP : householder (householderVec x i) * householder (householderVec x i) = 1 :=
    householder_mul_self (star_dotProduct_householderVec_self hx0 i)
  have hstar : star (householder (householderVec x i)) = householder (householderVec x i) :=
    (isHermitian_householder _).eq
  have hαα : star (-phase (x i)) * (-phase (x i)) = 1 := by
    rw [star_neg, neg_mul_neg, RCLike.star_def, RCLike.conj_mul, norm_phase]
    simp
  refine ⟨(-phase (x i)) • householder (householderVec x i), ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_smul, hstar, smul_mul_smul_comm, hαα, one_smul, hPP]
  · rw [smul_mulVec, ← mulVec_smul, ← hPx, mulVec_mulVec, hPP, one_mulVec]

end InverseProblem

/-- The unit vector of square roots of the interlacing ratios: under strict interlacing
([golub2013matrix] (8.4.7)), `d k = √(∏_j (μ_j - l_k) / ∏_{j ≠ k} (l_j - l_k))` has Euclidean
length one (`Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`). -/
private theorem norm_sqrt_interlaceRatio {N : ℕ} {l : Fin (N + 1) → ℝ} {μ : Fin N → ℝ}
    (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ‖(WithLp.toLp 2 (fun k => √((∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k))) :
      EuclideanSpace ℝ (Fin (N + 1)))‖ = 1 := by
  obtain ⟨hpos, hsum⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, ← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hpos k).le]

/-- **Golub's inverse tridiagonal eigenproblem** ([golub2013matrix] §8.4.6, (8.4.7)–(8.4.9);
G. H. Golub, "Some modified matrix eigenvalue problems", SIAM Review 15 (1973)): for strictly
interlacing `l 0 > μ 0 > l 1 > ⋯ > μ (N - 1) > l N` there is a real symmetric tridiagonal `T` with
characteristic polynomial `∏ (X - l i)` whose trailing principal submatrix `T(2:n, 2:n)` has
characteristic polynomial `∏ (X - μ j)`.

The construction is the book's: `d` with `d k² = ∏_j (μ_j - l_k) / ∏_{j ≠ k} (l_j - l_k)` is a
unit vector (`Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`); `W` orthogonal with first row
`d` (`Matrix.exists_mem_unitaryGroup_mulVec_single_eq`); `T = Q₁ᵀ (W Λ Wᵀ) Q₁` the Householder
tridiagonalization, whose `Q₁` fixes `e₀` (`Matrix.hessenbergQ_apply_zero`). Then `Q = Q₁ᵀ W`
diagonalizes `T` with first row `d`, and the eigenvector–eigenvalue identity
(`Matrix.mul_star_mul_prod_eq_det_submatrix`) gives `det (T(2:n, 2:n) - l k) = ∏_j (μ_j - l_k)` at
the `N + 1` distinct points `l k`, which determines the degree-`N` characteristic polynomial. -/
theorem exists_isTridiagonal_eigenvalues_eq_of_strictInterlace {N : ℕ} {l : Fin (N + 1) → ℝ}
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, T.IsSymm ∧ T.IsTridiagonal ∧
      T.charpoly = ∏ i, (X - C (l i)) ∧
        (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j)) := by
  obtain ⟨hpos, -⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  obtain ⟨U, hU, hUd⟩ := exists_mem_unitaryGroup_mulVec_single_eq (norm_sqrt_interlaceRatio h₁ h₂) 0
  obtain ⟨W, hW, hWU⟩ : ∃ W, W ∈ unitaryGroup (Fin (N + 1)) ℝ ∧ W = star U :=
    ⟨_, Unitary.star_mem hU, rfl⟩
  have hW0 : ∀ i, W 0 i = √((∏ j, (μ j - l i)) / ∏ j ∈ univ.erase i, (l j - l i)) := fun i => by
    have h := congrFun hUd i
    simp only [mulVec_single_one, col_apply] at h
    rw [hWU, star_apply, star_trivial, h]
  obtain ⟨A, hA⟩ : ∃ A, A = W * diagonal l * star W := ⟨_, rfl⟩
  have hAh : A.IsHermitian := by
    rw [hA, star_eq_conjTranspose]
    exact isHermitian_mul_mul_conjTranspose _ (isHermitian_diagonal l)
  have hQ₁ := hessenbergQ_mem_unitaryGroup A
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = star (hessenbergQ A) * W := ⟨_, rfl⟩
  have hQu : Q ∈ unitaryGroup (Fin (N + 1)) ℝ := hQ ▸ mul_mem (Unitary.star_mem hQ₁) hW
  have hQ₁' : ∀ M, hessenbergQ A * (star (hessenbergQ A) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hQ₁, Matrix.one_mul]
  have hW' : ∀ M, star W * (W * M) = M := fun M => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hW, Matrix.one_mul]
  have hWA : star W * (A * W) = diagonal l := by
    rw [hA]
    simp only [Matrix.mul_assoc, hW', mem_unitaryGroup_iff'.mp hW, Matrix.mul_one]
  have hQT : star Q * hessenbergReduce A * Q = diagonal l := by
    rw [hessenbergReduce_eq_conj, hQ, star_mul, star_star, ← star_eq_conjTranspose]
    simp only [Matrix.mul_assoc, hQ₁', hWA]
  have hQ0 : ∀ i, Q 0 i = W 0 i := fun i => by
    rw [hQ, mul_apply, Finset.sum_eq_single 0]
    · rw [star_apply, hessenbergQ_apply_zero, one_apply_eq, star_one, one_mul]
    · intro k _ hk
      rw [star_apply, hessenbergQ_apply_zero, one_apply_ne hk, star_zero, zero_mul]
    · simp
  have hAs : A.IsSymm := by
    have h := hAh
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨hessenbergReduce A, isSymm_hessenbergReduce hAs,
    isTridiagonal_hessenbergReduce_of_isHermitian A hAh, ?_, ?_⟩
  · rw [← charpoly_diagonal, ← hQT, charpoly_mul_comm, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.mp hQu, Matrix.one_mul]
  have hkey : ∀ k, eval (l k) ((hessenbergReduce A).submatrix Fin.succ Fin.succ).charpoly =
      eval (l k) (∏ j, (X - C (μ j))) := fun k => by
    have hne : ∏ j ∈ univ.erase k, (l j - l k) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hl.injective.ne (ne_of_mem_erase hj))
    have h := mul_star_mul_prod_eq_det_submatrix hQu hQT k
    rw [hQ0, hW0, star_trivial, Real.mul_self_sqrt (hpos k).le, div_mul_cancel₀ _ hne] at h
    have hneg : scalar (Fin N) (l k) - (hessenbergReduce A).submatrix Fin.succ Fin.succ =
        -((hessenbergReduce A).submatrix Fin.succ Fin.succ - l k • 1) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [eval_charpoly, hneg, det_neg, ← h, eval_prod, Fintype.card_fin]
    simp only [eval_sub, eval_X, eval_C]
    rw [show ∏ j, (μ j - l k) = ∏ j, -(l k - μ j) by simp only [neg_sub], Finset.prod_neg,
      card_univ, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨N, rfl⟩, one_mul]
  have hcard : (#(univ : Finset (Fin (N + 1))) : WithBot ℕ) = N + 1 := by simp
  refine eq_of_degrees_lt_of_eval_index_eq (s := univ) (v := l) hl.injective.injOn ?_ ?_
    fun k _ => hkey k
  · rw [charpoly_degree_eq_dim, Fintype.card_fin, hcard]
    exact_mod_cast Nat.lt_succ_self N
  · rw [degree_eq_natDegree (monic_prod_X_sub_C μ univ).ne_zero,
      natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin, hcard]
    exact_mod_cast Nat.lt_succ_self N

end Matrix
