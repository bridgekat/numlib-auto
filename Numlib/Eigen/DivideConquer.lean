/-
Copyright (c) 2026 Numlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Tuple.Sort
import Numlib.Eigen.InverseEigenvalue
import Numlib.LinearAlgebra.Matrix.PlaneRotation

/-!
# Diagonal plus rank-one matrices and the secular equation

The eigenproblem of a diagonal-plus-rank-one Hermitian matrix `D + ρ z zᴴ`, the secular equation,
and the merge step of the divide-and-conquer method for symmetric tridiagonal matrices
([golub2013matrix] §8.4.3–8.4.4; Dongarra and Sorensen 1987; Barlow 1993).

Setting: `d : n → ℝ`, `ρ : ℝ`, `z : n → 𝕜` over `[RCLike 𝕜]`, and the matrix
`M = diagonal (fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)`. The **secular function**
`Matrix.secularFunction d ρ z λ = 1 + ρ ∑ i, |z i|² / (d i - λ)` is the book's
`f(λ) = 1 + ρ zᵀ (D - λ I)⁻¹ z`.

## Main results

* `Matrix.isUnit_diagonal_sub_of_hasEigenvector_add_rankOne` ([golub2013matrix] Lemma 8.4.2):
  when the `d i` are distinct, `ρ ≠ 0` and no `z i` vanishes, an eigenvector `v` of `M` has
  `zᴴ v ≠ 0` and its eigenvalue is no `d i`.
* `Matrix.hasEigenvalue_iff_secularFunction_eq_zero` ([golub2013matrix] Theorem 8.4.3(a)): under
  the same hypotheses the real eigenvalues of `M` are the zeros of the secular function, and
  `Matrix.hasEigenvector_diagonal_add_rankOne_resolvent` (Theorem 8.4.3(c)): the eigenvectors are
  the multiples of `(D - λ)⁻¹ z`.
* `Matrix.hasDerivAt_secularFunction`, `Matrix.secularFunction_strictMonoOn`: the secular function
  is monotone between its poles.
* `Matrix.eigenvalues₀_diagonal_add_rankOne_strictInterlace` ([golub2013matrix] Theorem 8.4.3(b)):
  for strictly decreasing `d` the eigenvalues of `M` strictly interlace the `d i`,
  `λ_1 > d_1 > λ_2 > ⋯ > λ_n > d_n` for `ρ > 0` and `d_1 > λ_1 > d_2 > ⋯ > d_n > λ_n` for `ρ < 0`.
  The weak inequalities are the rank-one case of the low-rank interlacing of `Numlib/Eigen/MinMax`
  (`LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le`, [golub2013matrix]
  Theorem 8.1.8), and Lemma 8.4.2 makes them strict: no eigenvalue of `M` is a `d i`. The book's
  argument through the poles of the secular function and the intermediate value theorem is not
  needed.
* `Matrix.exists_orthogonal_deflation` ([golub2013matrix] Theorem 8.4.4): rotations in the planes
  of repeated `d i` and a permutation reduce an arbitrary `(d, z)` to the generic case, the nonzero
  entries of `z` first with strictly decreasing `d`.
* `Matrix.conj_fromBlocks_add_rankOne_eq`: the merge step of divide and conquer, a block-diagonal
  orthogonal similarity turning `diag(T₁, T₂) + ρ v vᵀ` into a diagonal-plus-rank-one matrix.
* `Matrix.borderedSecularFunction` ([golub2013matrix] §4.7.7, Cybenko and Van Loan 1986): the
  secular function `1 - λ - rᵀ (B - λ)⁻¹ r` of a bordered symmetric matrix `[1 rᵀ; r B]`, with its
  zero at an eigenvalue and its bridge to `Matrix.secularFunction` in an eigenbasis of `B`.

## Implementation notes

At a pole `λ = d i` the Lean value of the secular function is junk (`x / 0 = 0`); every statement
assumes `λ ∉ Set.range d`. Eigenvalues are sorted decreasingly, as everywhere in the backbone
(`Matrix.IsHermitian.sortedEigenvalues`).
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The **secular function** of `D + ρ z zᴴ` ([golub2013matrix] Theorem 8.4.3(a)):
`f(λ) = 1 + ρ ∑ i, |z i|² / (d i - λ)`, the book's `1 + ρ zᵀ (D - λ I)⁻¹ z`. At a pole `λ = d i`
the value is junk; the statements about it assume `λ ∉ Set.range d`. -/
noncomputable def secularFunction (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) (t : ℝ) : ℝ :=
  1 + ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t)

/-- The secular function in the book's resolvent form: for `λ` not a `d i`,
`f(λ) = 1 + ρ re (zᴴ (D - λ)⁻¹ z)`. -/
theorem secularFunction_eq_inner_resolvent [DecidableEq n] (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) {t : ℝ}
    (ht : t ∉ Set.range d) :
    secularFunction d ρ z t =
      1 + ρ * RCLike.re (star z ⬝ᵥ (diagonal fun i => ((d i - t : ℝ) : 𝕜))⁻¹ *ᵥ z) := by
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht ⟨i, (sub_eq_zero.mp h)⟩
  have hinv : (diagonal fun i => ((d i - t : ℝ) : 𝕜))⁻¹ =
      diagonal fun i => ((d i - t : ℝ) : 𝕜)⁻¹ :=
    inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (by exact_mod_cast hne i)))
  rw [secularFunction, hinv, dotProduct, map_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, Pi.star_apply, RCLike.star_def, mul_left_comm, RCLike.conj_mul,
    ← RCLike.ofReal_inv, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re,
    div_eq_inv_mul]

/-- **The derivative of the secular function** ([golub2013matrix] §8.4.3, proof of Theorem 8.4.3):
away from the poles, `f'(λ) = ρ ∑ i, |z i|² / (d i - λ)²`. -/
theorem hasDerivAt_secularFunction (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) {t : ℝ}
    (ht : t ∉ Set.range d) :
    HasDerivAt (secularFunction d ρ z) (ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) ^ 2) t := by
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht ⟨i, (sub_eq_zero.mp h)⟩
  have hterm : ∀ i, HasDerivAt (fun μ => ‖z i‖ ^ 2 / (d i - μ)) (‖z i‖ ^ 2 / (d i - t) ^ 2) t :=
    fun i => by
      have h := (hasDerivAt_const t (‖z i‖ ^ 2)).div
        ((hasDerivAt_const t (d i)).sub (hasDerivAt_id' t)) (hne i)
      convert h using 1
      simp only [Pi.sub_apply]
      ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
  exact (hsum.const_mul ρ).const_add 1

/-- **The secular function is strictly increasing between consecutive poles** for `ρ > 0` (and
some `z i ≠ 0`): on any interval free of the `d i`, `f' = ρ ∑ |z i|² / (d i - λ)² > 0`. -/
theorem secularFunction_strictMonoOn (d : n → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : n → 𝕜)
    (hz : ∃ i, z i ≠ 0) {a b : ℝ} (hab : ∀ i, d i ∉ Set.Ioo a b) :
    StrictMonoOn (secularFunction d ρ z) (Set.Ioo a b) := by
  have ht : ∀ t ∈ Set.Ioo a b, t ∉ Set.range d := by
    rintro t ht ⟨i, rfl⟩; exact hab i ht
  refine strictMonoOn_of_deriv_pos (convex_Ioo a b)
    (fun t htab => (hasDerivAt_secularFunction d ρ z (ht t htab)).continuousAt.continuousWithinAt)
    fun t htab => ?_
  rw [interior_Ioo] at htab
  rw [(hasDerivAt_secularFunction d ρ z (ht t htab)).deriv]
  obtain ⟨j, hj⟩ := hz
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht t htab ⟨i, (sub_eq_zero.mp h)⟩
  refine mul_pos hρ (Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩)
  exact div_pos (pow_pos (norm_pos_iff.mpr hj) 2)
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hne j))))

variable [DecidableEq n] {d : n → ℝ} {ρ : ℝ} {z : n → 𝕜}

omit [DecidableEq n] in
/-- The rank-one matrix `z zᴴ` applied to `v` is `(zᴴ v) z`, row by row. -/
theorem vecMulVec_star_mulVec_apply (z v : n → 𝕜) (i : n) :
    (vecMulVec z (star z) *ᵥ v) i = z i * (star z ⬝ᵥ v) := by
  simp only [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

/-- The rows of `(D + ρ z zᴴ) v`: `d i v i + ρ (zᴴ v) z i`. -/
theorem diagonal_add_rankOne_mulVec_apply (v : n → 𝕜) (i : n) :
    (((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v) i =
      d i * v i + ρ * (star z ⬝ᵥ v) * z i := by
  rw [add_mulVec, Pi.add_apply, mulVec_diagonal, smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [vecMulVec_star_mulVec_apply]
  ring

/-- The eigen-equation of `D + ρ z zᴴ` row by row: `(d i - λ) v i = -ρ (zᴴ v) z i`
([golub2013matrix] (8.4.4)). -/
theorem diagonal_add_rankOne_mulVec_eq_iff {v : n → 𝕜} {t : 𝕜} :
    ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v ↔
      ∀ i, ((d i : 𝕜) - t) * v i = -(ρ * (star z ⬝ᵥ v) * z i) := by
  refine ⟨fun h i => ?_, fun h => funext fun i => ?_⟩
  · have := congrFun h i
    rw [diagonal_add_rankOne_mulVec_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  · rw [diagonal_add_rankOne_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h i

/-- **[golub2013matrix] Lemma 8.4.2**: if the `d i` are distinct, `ρ ≠ 0`, no `z i` vanishes and
`(D + ρ z zᴴ) v = λ v` with `v ≠ 0`, then `zᴴ v ≠ 0` and `λ` is no `d i` (so `D - λ` is
invertible). If `λ = d i`, row `i` of (8.4.4) forces `zᴴ v = 0`; then `D v = λ v`, so `v` is a
multiple of `e_i` (distinct `d`), and `zᴴ v = conj (z i) v i ≠ 0`. -/
theorem isUnit_diagonal_sub_of_hasEigenvector_add_rankOne (hd : Function.Injective d)
    (hρ : ρ ≠ 0) (hz : ∀ i, z i ≠ 0) {v : n → 𝕜} (hv : v ≠ 0) {t : 𝕜}
    (h : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v) :
    star z ⬝ᵥ v ≠ 0 ∧ ∀ i, (d i : 𝕜) ≠ t := by
  rw [diagonal_add_rankOne_mulVec_eq_iff] at h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h0; exact hv (funext h0)
  have hw : star z ⬝ᵥ v ≠ 0 := by
    intro hw
    have hdj : (d j : 𝕜) = t := by
      have := h j
      rw [hw, mul_zero, zero_mul, neg_zero] at this
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hj)
    have hvi : ∀ i, i ≠ j → v i = 0 := fun i hij => by
      have := h i
      rw [hw, mul_zero, zero_mul, neg_zero, ← hdj] at this
      refine (mul_eq_zero.mp this).resolve_left fun hd' => hij (hd ?_)
      exact_mod_cast sub_eq_zero.mp hd'
    refine absurd hw ?_
    rw [dotProduct, Finset.sum_eq_single j (fun i _ hij => by rw [hvi i hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    exact mul_ne_zero (by simpa using hz j) hj
  refine ⟨hw, fun i hi => ?_⟩
  have := h i
  rw [hi, sub_self, zero_mul, eq_comm, neg_eq_zero] at this
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ) hw) (hz i) this

/-- **[golub2013matrix] Theorem 8.4.3(a)**: under the hypotheses of Lemma 8.4.2 (distinct `d i`,
`ρ ≠ 0`, no `z i = 0`), a real `λ` is an eigenvalue of `D + ρ z zᴴ` iff it is no `d i` and a zero
of the secular function. (⇒) apply `zᴴ (D - λ)⁻¹` to (8.4.4) and cancel `zᴴ v ≠ 0`; (⇐)
`v = (D - λ)⁻¹ z` is an eigenvector, the rows of `(D + ρ z zᴴ - λ) v` being `f(λ) z i`. -/
theorem hasEigenvalue_iff_secularFunction_eq_zero (hd : Function.Injective d) (hρ : ρ ≠ 0)
    (hz : ∀ i, z i ≠ 0) (t : ℝ) :
    Module.End.HasEigenvalue
        (toLin' ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z))) (t : 𝕜) ↔
      t ∉ Set.range d ∧ secularFunction d ρ z t = 0 := by
  constructor
  · intro hev
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hMv : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v =
        (t : 𝕜) • v := by
      have := Module.End.mem_eigenspace_iff.mp hv.1
      rwa [toLin'_apply] at this
    obtain ⟨hw, ht⟩ := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd hρ hz hv.2 hMv
    have ht' : t ∉ Set.range d := by
      rintro ⟨i, hi⟩; exact ht i (by rw [hi])
    refine ⟨ht', ?_⟩
    rw [diagonal_add_rankOne_mulVec_eq_iff] at hMv
    have hne : ∀ i, ((d i : 𝕜) - t) ≠ 0 := fun i h => ht i (sub_eq_zero.mp h)
    have hvi : ∀ i, v i = -(ρ * (star z ⬝ᵥ v)) * z i / ((d i : 𝕜) - t) := fun i => by
      rw [eq_div_iff (hne i), mul_comm (v i), hMv i]; ring
    have key : star z ⬝ᵥ v = (star z ⬝ᵥ v) * (-(ρ : 𝕜) *
        ∑ i, ((‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜)) := by
      conv_lhs => rw [dotProduct]
      simp_rw [hvi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.star_apply, RCLike.star_def]
      push_cast
      rw [← RCLike.mul_conj]
      ring
    have h1 : (1 : 𝕜) = -(ρ : 𝕜) * ∑ i, ((‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) := by
      have := mul_left_cancel₀ hw (key.symm.trans (mul_one _).symm)
      exact this.symm
    have h2 : (1 : ℝ) = -ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) := by exact_mod_cast h1
    rw [secularFunction]
    linarith
  · rintro ⟨ht, hf⟩
    have hne : ∀ i, ((d i : 𝕜) - t) ≠ 0 := fun i h =>
      ht ⟨i, by exact_mod_cast sub_eq_zero.mp h⟩
    set v : n → 𝕜 := fun i => z i / ((d i : 𝕜) - t)
    have hv : v ≠ 0 := by
      intro h0
      obtain ⟨j⟩ : Nonempty n := by
        by_contra hn
        rw [not_nonempty_iff] at hn
        simp [secularFunction] at hf
      exact div_ne_zero (hz j) (hne j) (congrFun h0 j)
    have hzv : star z ⬝ᵥ v = ((∑ i, ‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) := by
      simp only [dotProduct, v, Pi.star_apply, RCLike.star_def]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← RCLike.mul_conj]
      ring
    have hsum : (ρ : 𝕜) * ((∑ i, ‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) = -1 := by
      have : ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) = -1 := by rw [secularFunction] at hf; linarith
      exact_mod_cast this
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, diagonal_add_rankOne_mulVec_eq_iff]
    intro i
    rw [hzv, hsum]
    simp only [v]
    rw [mul_div_cancel₀ _ (hne i)]
    ring

/-- **[golub2013matrix] Theorem 8.4.3(c)**: under the hypotheses of Lemma 8.4.2, every eigenvector
`v` of `D + ρ z zᴴ` for `λ` is a nonzero multiple of `(D - λ)⁻¹ z`, from (8.4.4) with `D - λ`
invertible. -/
theorem hasEigenvector_diagonal_add_rankOne_resolvent (hd : Function.Injective d) (hρ : ρ ≠ 0)
    (hz : ∀ i, z i ≠ 0) {v : n → 𝕜} (hv : v ≠ 0) {t : 𝕜}
    (h : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v) :
    ∃ c : 𝕜, c ≠ 0 ∧ v = c • fun i => z i / ((d i : 𝕜) - t) := by
  obtain ⟨hw, ht⟩ := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd hρ hz hv h
  rw [diagonal_add_rankOne_mulVec_eq_iff] at h
  refine ⟨-(ρ * (star z ⬝ᵥ v)), neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hρ) hw),
    funext fun i => ?_⟩
  have hne : ((d i : 𝕜) - t) ≠ 0 := sub_ne_zero.mpr (ht i)
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc', eq_div_iff hne, mul_comm (v i), h i]
  ring


/-! ### Strict interlacing -/

section Interlacing

variable {N : ℕ}

/-- The sorted eigenvalues of a real diagonal matrix with decreasing entries are its entries: both
lists are sorted, and they are permutations of each other (the roots of `∏ (X - d i)`,
`Matrix.IsHermitian.roots_charpoly_eq_sortedEigenvalues`). -/
theorem IsHermitian.sortedEigenvalues_diagonal {d : Fin N → ℝ} (hd : Antitone d)
    (hD : (diagonal fun i => (d i : 𝕜)).IsHermitian) : hD.sortedEigenvalues = d := by
  have h1 := hD.roots_charpoly_eq_sortedEigenvalues
  have h2 : (diagonal fun i => (d i : 𝕜)).charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val := by
    rw [charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [h1, ← Multiset.map_map, ← Multiset.map_map] at h2
  have hm := Multiset.map_injective RCLike.ofReal_injective h2
  rw [Fin.univ_val_map, Fin.univ_val_map] at hm
  exact List.ofFn_injective ((Multiset.coe_eq_coe.mp hm).eq_of_sortedGE
    (List.sortedGE_ofFn_iff.mpr hD.sortedEigenvalues_antitone) (List.sortedGE_ofFn_iff.mpr hd))

/-- Every sorted eigenvalue of a Hermitian matrix has an eigenvector. -/
theorem IsHermitian.exists_mulVec_eq_sortedEigenvalues_smul {M : Matrix (Fin N) (Fin N) 𝕜}
    (hM : M.IsHermitian) (k : Fin N) :
    ∃ v : Fin N → 𝕜, v ≠ 0 ∧ M *ᵥ v = (hM.sortedEigenvalues k : 𝕜) • v := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hM
  set b := hT.eigenvectorBasis finrank_euclideanSpace (Fin.cast (Fintype.card_fin N).symm k)
  refine ⟨WithLp.ofLp b, fun h0 => ?_, ?_⟩
  · have hb := (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.ne_zero
      (Fin.cast (Fintype.card_fin N).symm k)
    exact hb ((WithLp.ofLp_eq_zero 2).mp h0)
  · rw [← ofLp_toEuclideanLin, hT.apply_eigenvectorBasis, WithLp.ofLp_smul]
    rfl

/-- The quadratic form of the rank-one matrix `c z zᴴ` (`c` real):
`re ⟪c z zᴴ x, x⟫ = c |zᴴ x|²`. -/
theorem re_inner_toEuclideanLin_smul_vecMulVec (c : ℝ) (z : n → 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (toEuclideanLin ((c : 𝕜) • vecMulVec z (star z)) x) x) =
      c * ‖star z ⬝ᵥ WithLp.ofLp x‖ ^ 2 := by
  have hmv : ((c : 𝕜) • vecMulVec z (star z)) *ᵥ WithLp.ofLp x =
      ((c : 𝕜) * (star z ⬝ᵥ WithLp.ofLp x)) • z := by
    ext i
    rw [smul_mulVec, Pi.smul_apply, vecMulVec_star_mulVec_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, hmv, star_smul,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (WithLp.ofLp x) (star z),
    star_mul', RCLike.star_def, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- The rank-one matrix `c z zᴴ` has rank at most one: its range is in the span of `z`. -/
theorem finrank_range_toEuclideanLin_smul_vecMulVec_le (c : 𝕜) (z : n → 𝕜) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin (c • vecMulVec z (star z)))) ≤ 1 := by
  have hle : LinearMap.range (toEuclideanLin (c • vecMulVec z (star z))) ≤
      Submodule.span 𝕜 {WithLp.toLp 2 z} := by
    rintro _ ⟨x, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨c * (star z ⬝ᵥ WithLp.ofLp x), ?_⟩
    apply (WithLp.ofLp_injective 2)
    rw [ofLp_toEuclideanLin, WithLp.ofLp_smul]
    ext i
    simp only [smul_mulVec, Pi.smul_apply, vecMulVec_star_mulVec_apply, smul_eq_mul]
    ring
  refine (Submodule.finrank_mono hle).trans ?_
  simpa using finrank_span_le_card ({WithLp.toLp 2 z} : Set (EuclideanSpace 𝕜 n))

/-- **[golub2013matrix] Theorem 8.4.3(b), strict interlacing**: for strictly decreasing `d`,
`ρ ≠ 0` and no `z i = 0`, the sorted eigenvalues `λ` of `D + ρ z zᴴ` satisfy
`λ_1 > d_1 > λ_2 > ⋯ > λ_n > d_n` if `ρ > 0` and `d_1 > λ_1 > d_2 > ⋯ > d_n > λ_n` if `ρ < 0`.
The weak inequalities are the rank-one interlacing
`LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le` (the sorted
eigenvalues of `D` being `d`, `Matrix.IsHermitian.sortedEigenvalues_diagonal`), and they are
strict because no eigenvalue of `D + ρ z zᴴ` is a `d i`
(`Matrix.isUnit_diagonal_sub_of_hasEigenvector_add_rankOne`, Lemma 8.4.2). -/
theorem eigenvalues₀_diagonal_add_rankOne_strictInterlace {d : Fin N → ℝ} (hd : StrictAnti d)
    {ρ : ℝ} (hρ : ρ ≠ 0) {z : Fin N → 𝕜} (hz : ∀ i, z i ≠ 0)
    (hM : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)).IsHermitian) :
    (0 < ρ → (∀ i, d i < hM.sortedEigenvalues i) ∧
        ∀ i j : Fin N, (j : ℕ) = i + 1 → hM.sortedEigenvalues j < d i) ∧
      (ρ < 0 → (∀ i, hM.sortedEigenvalues i < d i) ∧
        ∀ i j : Fin N, (j : ℕ) = i + 1 → d j < hM.sortedEigenvalues i) := by
  set D : Matrix (Fin N) (Fin N) 𝕜 := diagonal fun i => (d i : 𝕜)
  set P : Matrix (Fin N) (Fin N) 𝕜 := (ρ : 𝕜) • vecMulVec z (star z)
  have hD : D.IsHermitian := isHermitian_diagonal_iff.mpr fun i => by
    simp [IsSelfAdjoint, RCLike.star_def, RCLike.conj_ofReal]
  have hDsort := hD.sortedEigenvalues_diagonal hd.antitone
  -- no eigenvalue of `D + P` is a `d j`
  have hne : ∀ k j, hM.sortedEigenvalues k ≠ d j := fun k j h => by
    obtain ⟨v, hv, hMv⟩ := hM.exists_mulVec_eq_sortedEigenvalues_smul k
    exact (isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd.injective hρ hz hv hMv).2 j
      (by rw [h])
  have hTD := isSymmetric_toEuclideanLin_iff.mpr hD
  have hTM := isSymmetric_toEuclideanLin_iff.mpr hM
  have hsub : toEuclideanLin (D + P) - toEuclideanLin D = toEuclideanLin P := by
    rw [map_add, add_sub_cancel_left]
  have hrk : Module.finrank 𝕜 (LinearMap.range (toEuclideanLin P)) ≤ 1 :=
    finrank_range_toEuclideanLin_smul_vecMulVec_le _ z
  have hrk' : Module.finrank 𝕜 (LinearMap.range (-toEuclideanLin P)) ≤ 1 := by
    rw [LinearMap.range_neg]; exact hrk
  have hq := re_inner_toEuclideanLin_smul_vecMulVec ρ z
  -- the eigenvalue indices in `Fin (Fintype.card (Fin N))`
  have hidx : ∀ i j : Fin N, (hij : (j : ℕ) = i + 1) →
      (⟨(Fin.cast (Fintype.card_fin N).symm i : ℕ) + 1, by have := j.isLt; simp; omega⟩ :
        Fin (Fintype.card (Fin N))) = Fin.cast (Fintype.card_fin N).symm j := fun i j hij => by
    ext; simp [hij]
  have hsD : ∀ k : Fin N, hTD.eigenvalues finrank_euclideanSpace
      (Fin.cast (Fintype.card_fin N).symm k) = d k := fun k => congrFun hDsort k
  refine ⟨fun hρ0 => ⟨fun i => ?_, fun i j hij => ?_⟩, fun hρ0 => ⟨fun i => ?_, fun i j hij => ?_⟩⟩
  · -- `d i ≤ λ i`
    have h := hTD.eigenvalues_le_of_re_inner_le hTM finrank_euclideanSpace (fun x => by
      rw [map_add, LinearMap.add_apply, inner_add_left, map_add, hq x]
      nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]) (Fin.cast (Fintype.card_fin N).symm i)
    rw [hsD] at h
    exact lt_of_le_of_ne h (hne i i).symm
  · have hpos : (toEuclideanLin (D + P) - toEuclideanLin D).IsPositive :=
      ⟨hTM.sub hTD, fun x => by rw [hsub, hq x]; positivity⟩
    have h := (hTD.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTM
      finrank_euclideanSpace hpos (r := 1) (by rwa [hsub])
      (Fin.cast (Fintype.card_fin N).symm i) (by have := j.isLt; simp; omega)).1
    rw [hidx i j hij, hsD] at h
    exact lt_of_le_of_ne h (hne j i)
  · have h := hTM.eigenvalues_le_of_re_inner_le hTD finrank_euclideanSpace (fun x => by
      rw [map_add, LinearMap.add_apply, inner_add_left, map_add, hq x]
      nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]) (Fin.cast (Fintype.card_fin N).symm i)
    rw [hsD] at h
    exact lt_of_le_of_ne h (hne i i)
  · have hsub' : toEuclideanLin D - toEuclideanLin (D + P) = -toEuclideanLin P := by
      rw [← neg_sub, hsub]
    have hpos : (toEuclideanLin D - toEuclideanLin (D + P)).IsPositive :=
      ⟨hTD.sub hTM, fun x => by
        rw [hsub', LinearMap.neg_apply, inner_neg_left, map_neg, hq x]
        nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]⟩
    have h := (hTM.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTD
      finrank_euclideanSpace hpos (r := 1) (by rwa [hsub'])
      (Fin.cast (Fintype.card_fin N).symm i) (by have := j.isLt; simp; omega)).1
    rw [hidx i j hij, hsD] at h
    exact lt_of_le_of_ne h (hne i j).symm

end Interlacing

/-! ### Deflation to the generic case -/

section Deflation

variable {N : ℕ}

/-- A plane rotation in the plane of two equal diagonal entries commutes with the diagonal matrix:
on that plane the diagonal matrix is a scalar. -/
private theorem planeRotation_mul_diagonal_comm {d : Fin N → ℝ} {j k : Fin N} (hjk : j ≠ k)
    (hd : d j = d k) (c s : ℝ) :
    planeRotation j k c s * diagonal d = diagonal d * planeRotation j k c s := by
  ext p q
  rw [mul_diagonal, diagonal_mul, planeRotation_apply hjk]
  split_ifs <;> subst_vars <;>
    first | ring1 | (rw [hd]; try ring1)

/-- The conjugation `Pᵀ M P` by the permutation matrix `P i j = [i = σ j]` permutes rows and
columns by `σ`. -/
private theorem transpose_permMatrix_mul_mul (σ : Fin N ≃ Fin N) (M : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix.of fun i j => if i = σ j then (1 : ℝ) else 0)ᵀ * M *
        Matrix.of (fun i j => if i = σ j then (1 : ℝ) else 0) =
      M.submatrix σ σ := by
  ext a b
  simp [mul_apply, transpose_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The transpose of the permutation matrix `P i j = [i = σ j]` permutes the entries of a vector by
`σ`. -/
private theorem transpose_permMatrix_mulVec (σ : Fin N ≃ Fin N) (w : Fin N → ℝ) :
    (Matrix.of fun i j => if i = σ j then (1 : ℝ) else 0)ᵀ *ᵥ w = w ∘ σ := by
  ext a
  simp [mulVec, dotProduct, transpose_apply, ite_mul, Finset.sum_ite_eq']

/-- The first move of [golub2013matrix] Theorem 8.4.4, repeated: rotations in the planes of
repeated diagonal entries leave `D` alone and, applied to `z`, leave at most one nonzero entry of
`V₁ᵀ z` for each value of `d`. By strong induction on the number of nonzero entries: a rotation in
the plane of two nonzero entries with equal `d` (`Matrix.transpose_planeRotation_givensPair_mulVec`)
zeroes one of them and changes no other entry but its partner. -/
private theorem exists_orthogonal_distinct_of_ne_zero (d : Fin N → ℝ) :
    ∀ (m : ℕ) (z : Fin N → ℝ), (Finset.univ.filter fun i => z i ≠ 0).card = m →
      ∃ V ∈ orthogonalGroup (Fin N) ℝ, Vᵀ * diagonal d * V = diagonal d ∧
        ∀ i j, i ≠ j → d i = d j → (Vᵀ *ᵥ z) i ≠ 0 → (Vᵀ *ᵥ z) j = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro z hm
  by_cases hgood : ∀ i j, i ≠ j → d i = d j → z i ≠ 0 → z j = 0
  · exact ⟨1, one_mem _, by simp, by simpa using hgood⟩
  push Not at hgood
  obtain ⟨i, j, hij, hd, hzi, hzj⟩ := hgood
  set G := planeRotation i j (givensPair (z i) (z j)).1 (givensPair (z i) (z j)).2 with hG
  obtain ⟨hz'j, -, hz'q⟩ := transpose_planeRotation_givensPair_mulVec hij z
  set z' := Gᵀ *ᵥ z with hz'
  have hsub : (Finset.univ.filter fun q => z' q ≠ 0) ⊆
      (Finset.univ.filter fun q => z q ≠ 0).erase j := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hq ⊢
    refine ⟨fun h => hq (h ▸ hz'j), ?_⟩
    by_cases hqi : q = i
    · exact hqi ▸ hzi
    · by_cases hqj : q = j
      · exact absurd (hqj ▸ hz'j) hq
      · rwa [hz'q q hqi hqj] at hq
  have hlt : (Finset.univ.filter fun q => z' q ≠ 0).card < m := by
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simpa using hzj), hm] at this
    have : 0 < m := hm ▸ Finset.card_pos.mpr ⟨j, by simpa using hzj⟩
    omega
  obtain ⟨V, hV, hVD, hVz⟩ := ih _ hlt z' rfl
  have hGo : G ∈ orthogonalGroup (Fin N) ℝ :=
    planeRotation_mem_orthogonalGroup hij (givensPair_sq_add_sq _ _)
  have hGG : Gᵀ * G = 1 := transpose_planeRotation_mul_self hij (givensPair_sq_add_sq _ _)
  have hGD : Gᵀ * diagonal d * G = diagonal d := by
    rw [Matrix.mul_assoc, ← planeRotation_mul_diagonal_comm hij hd, ← Matrix.mul_assoc, hGG,
      Matrix.one_mul]
  refine ⟨G * V, mul_mem hGo hV, ?_, ?_⟩
  · rw [transpose_mul, show Vᵀ * Gᵀ * diagonal d * (G * V) = Vᵀ * (Gᵀ * diagonal d * G) * V by
      simp only [Matrix.mul_assoc], hGD, hVD]
  · rw [transpose_mul, ← mulVec_mulVec]
    exact hVz

/-- **Deflation to the generic case** ([golub2013matrix] Theorem 8.4.4): for `d z : Fin N → ℝ`
there are an orthogonal `V₁`, `μ` and `r ≤ N` with `V₁ᵀ diag(d) V₁ = diag(μ)`, `μ` strictly
decreasing on the first `r` indices and decreasing on the others, and `w = V₁ᵀ z` nonzero exactly on
the first `r` indices. Rotations in the planes of repeated `d i` zero all but one entry of `z` per
value of `d`; a permutation then sorts the nonzero entries to the front by decreasing `μ`, and the
others behind them by decreasing `μ`.

The book states the ordering as `μ_1 > ⋯ > μ_r ≥ μ_{r+1} ≥ ⋯ ≥ μ_n`; across the boundary this is
false in general (`d = (2, 1)`, `z = (0, 1)`: the only nonzero `w` sits at the eigenvalue `1`, so
`μ_1 = 1 < μ_2 = 2`), and only the two separate orderings are claimed. -/
theorem exists_orthogonal_deflation (d z : Fin N → ℝ) :
    ∃ V₁ ∈ orthogonalGroup (Fin N) ℝ, ∃ μ : Fin N → ℝ, ∃ r ≤ N,
      V₁ᵀ * diagonal d * V₁ = diagonal μ ∧
      (∀ i j : Fin N, i < j → (j : ℕ) < r → μ j < μ i) ∧
      (∀ i j : Fin N, r ≤ (i : ℕ) → i ≤ j → μ j ≤ μ i) ∧
      ∀ i, (V₁ᵀ *ᵥ z) i ≠ 0 ↔ (i : ℕ) < r := by
  classical
  obtain ⟨V, hV, hVD, hVz⟩ := exists_orthogonal_distinct_of_ne_zero d _ z rfl
  set w := Vᵀ *ᵥ z
  -- sort by (inactive, decreasing `d`)
  set key : Fin N → Lex (ℕ × ℝ) := fun i => toLex ((if w i ≠ 0 then 0 else 1), -d i) with hkey
  set σ : Fin N ≃ Fin N := Tuple.sort key
  have hmono : Monotone (key ∘ σ) := Tuple.monotone_sort key
  set r := (Finset.univ.filter fun i => w i ≠ 0).card
  have hr : r ≤ N := (Finset.card_filter_le _ _).trans (by simp)
  have hcount : (Finset.univ.filter fun i => w (σ i) ≠ 0).card = r := by
    exact Finset.card_bij (fun i _ => σ i) (fun a ha => by simpa using ha)
      (fun _ _ _ _ h => σ.injective h) (fun b hb => ⟨σ.symm b, by simpa using hb, by simp⟩)
  -- the first component of the key is monotone along `σ`
  have hfst : ∀ a b : Fin N, a ≤ b → w (σ b) ≠ 0 → w (σ a) ≠ 0 := by
    intro a b hab hb ha
    have h := hmono hab
    simp only [Function.comp_apply, hkey, ha, hb, ne_eq, not_true_eq_false, not_false_eq_true,
      ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨h, -⟩ <;> omega
  have hactive : ∀ i : Fin N, w (σ i) ≠ 0 ↔ (i : ℕ) < r := by
    intro i
    constructor
    · intro hi
      by_contra hri
      push Not at hri
      have hsub : Finset.Iic i ⊆ Finset.univ.filter fun a => w (σ a) ≠ 0 := fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at ha ⊢
        exact hfst a i ha hi
      have h1 := Finset.card_le_card hsub
      rw [hcount, Fin.card_Iic] at h1
      omega
    · intro hri
      by_contra hi
      have hsub : Finset.univ.filter (fun a => w (σ a) ≠ 0) ⊆ Finset.Iio i := fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at ha ⊢
        by_contra hai
        exact (hfst i a (not_lt.mp hai) ha) hi
      have h1 := Finset.card_le_card hsub
      rw [hcount, Fin.card_Iio] at h1
      omega
  -- the permutation matrix
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin N) (Fin N) ℝ,
      P = Matrix.of fun i j => if i = σ j then 1 else 0 := ⟨_, rfl⟩
  have hPP : Pᵀ * P = 1 := by
    have := transpose_permMatrix_mul_mul σ 1
    rw [Matrix.mul_one, submatrix_one_equiv, ← hP] at this
    exact this
  have hPo : P ∈ orthogonalGroup (Fin N) ℝ := (mem_orthogonalGroup_iff' (Fin N) ℝ).2 hPP
  refine ⟨V * P, mul_mem hV hPo, d ∘ σ, r, hr, ?_, fun i j hij hjr => ?_, fun i j hri hij => ?_,
    fun i => ?_⟩
  · rw [transpose_mul, show Pᵀ * Vᵀ * diagonal d * (V * P) = Pᵀ * (Vᵀ * diagonal d * V) * P by
      simp only [Matrix.mul_assoc], hVD, hP, transpose_permMatrix_mul_mul, submatrix_diagonal_equiv]
  · -- two active indices: equal first components, decreasing `d`, and distinct values
    have hj := (hactive j).mpr hjr
    have hi := (hactive i).mpr (lt_trans (Fin.lt_def.mp hij) hjr)
    have h := hmono hij.le
    simp only [Function.comp_apply, hkey, hi, hj, ne_eq, not_false_eq_true, ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    have hle : d (σ j) ≤ d (σ i) := by
      rcases h with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · linarith
    refine lt_of_le_of_ne hle fun heq => ?_
    exact hj (hVz (σ i) (σ j) (σ.injective.ne hij.ne) heq.symm hi)
  · -- two inactive indices: equal first components and decreasing `d`
    have hi : w (σ i) = 0 := by
      by_contra h
      have := (hactive i).mp h
      omega
    have hj : w (σ j) = 0 := by
      by_contra h
      have := (hactive j).mp h
      have : (i : ℕ) ≤ j := hij
      omega
    have h := hmono hij
    simp only [Function.comp_apply, hkey, hi, hj, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · simp only [Function.comp_apply]
      linarith
  · rw [transpose_mul, ← mulVec_mulVec, hP, transpose_permMatrix_mulVec, Function.comp_apply]
    exact hactive i

end Deflation

/-! ### The merge step of divide and conquer -/

/-- **The merge step of divide and conquer** ([golub2013matrix] §8.4.4): if orthogonal `Q₁`, `Q₂`
diagonalize `T₁`, `T₂`, then the block-diagonal orthogonal `U = diag(Q₁, Q₂)` turns
`diag(T₁, T₂) + ρ v vᵀ` into the diagonal-plus-rank-one matrix
`diag(d₁, d₂) + ρ z zᵀ` with `z = Uᵀ v`. -/
theorem conj_fromBlocks_add_rankOne_eq {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] {T₁ Q₁ : Matrix m₁ m₁ ℝ} {T₂ Q₂ : Matrix m₂ m₂ ℝ}
    (hQ₁ : Q₁ ∈ orthogonalGroup m₁ ℝ) (hQ₂ : Q₂ ∈ orthogonalGroup m₂ ℝ) {d₁ : m₁ → ℝ}
    {d₂ : m₂ → ℝ} (h₁ : Q₁ᵀ * T₁ * Q₁ = diagonal d₁) (h₂ : Q₂ᵀ * T₂ * Q₂ = diagonal d₂) (ρ : ℝ)
    (v : m₁ ⊕ m₂ → ℝ) :
    fromBlocks Q₁ 0 0 Q₂ ∈ orthogonalGroup (m₁ ⊕ m₂) ℝ ∧
      (fromBlocks Q₁ 0 0 Q₂)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * fromBlocks Q₁ 0 0 Q₂ =
        diagonal (Sum.elim d₁ d₂) +
          ρ • vecMulVec ((fromBlocks Q₁ 0 0 Q₂)ᵀ *ᵥ v) ((fromBlocks Q₁ 0 0 Q₂)ᵀ *ᵥ v) := by
  set U : Matrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) ℝ := fromBlocks Q₁ 0 0 Q₂
  have hUt : Uᵀ = fromBlocks Q₁ᵀ 0 0 Q₂ᵀ := by
    rw [fromBlocks_transpose, transpose_zero, transpose_zero]
  have hQ₁' : Q₁ * Q₁ᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ₁
  have hQ₂' : Q₂ * Q₂ᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ₂
  refine ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, hUt, fromBlocks_multiply]
    simp [hQ₁', hQ₂', fromBlocks_one]
  · have hconj : Uᵀ * fromBlocks T₁ 0 0 T₂ * U = diagonal (Sum.elim d₁ d₂) := by
      rw [hUt, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal, ← h₁, ← h₂]
      simp
    have hrank : Uᵀ * vecMulVec v v * U = vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) := by
      rw [mul_vecMulVec, vecMulVec_mul, mulVec_transpose]
    rw [Matrix.mul_add, Matrix.add_mul, hconj, Matrix.mul_smul, Matrix.smul_mul, hrank]

/-! ### The bordered secular function -/

section Bordered

variable {m : ℕ}

/-- The **bordered secular function** of `T = [1 rᵀ; r B]` ([golub2013matrix] §4.7.7, Cybenko and
Van Loan 1986): `f(λ) = 1 - λ - rᵀ (B - λ)⁻¹ r`, whose zero below the spectrum of `B` is the
smallest eigenvalue of `T` (under (4.7.8)). Only the unit corner is used, not the Toeplitz
structure. The bordered sibling of `Matrix.secularFunction`
(`Matrix.borderedSecularFunction_eq_secularFunction_sub`). -/
noncomputable def borderedSecularFunction (r : Fin m → ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) : ℝ :=
  1 - t - r ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r)

/-- **An eigenvalue of the bordered matrix is a zero of the bordered secular function**
([golub2013matrix] §4.7.7): if `[1 rᵀ; r B] [α; y] = λ [α; y]` with `[α; y] ≠ 0` and `B - λ`
invertible, then `α ≠ 0`, `y = -α (B - λ)⁻¹ r` (the second block row), and `f(λ) = 0` (the first
block row divided by `α`). -/
theorem borderedSecularFunction_eq_zero_of_mulVec_eq {r : Fin m → ℝ}
    {B : Matrix (Fin m) (Fin m) ℝ} {t α : ℝ} {y : Fin m → ℝ} (hB : IsUnit (B - t • 1))
    (hne : Sum.elim (fun _ : Fin 1 => α) y ≠ 0)
    (h : fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (replicateRow (Fin 1) r)
        (replicateCol (Fin 1) r) B *ᵥ Sum.elim (fun _ => α) y = t • Sum.elim (fun _ => α) y) :
    α ≠ 0 ∧ y = -α • ((B - t • 1)⁻¹ *ᵥ r) ∧ borderedSecularFunction r B t = 0 := by
  have hrow : ∀ i, (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (replicateRow (Fin 1) r)
      (replicateCol (Fin 1) r) B *ᵥ Sum.elim (fun _ => α) y) i =
        t * Sum.elim (fun _ => α) y i := fun i => by rw [h]; rfl
  have h1' : α + r ⬝ᵥ y = t * α := by
    have := hrow (Sum.inl 0)
    rw [fromBlocks_mulVec, Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply,
      one_mulVec, Sum.elim_inl] at this
    rw [← this]
    rfl
  have h2' : (B - t • 1) *ᵥ y = -α • r := by
    ext i
    have := hrow (Sum.inr i)
    rw [fromBlocks_mulVec, Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply,
      Sum.elim_inr] at this
    have hc : (replicateCol (Fin 1) r *ᵥ fun _ => α) i = r i * α := by
      simp [mulVec, dotProduct, replicateCol_apply]
    rw [hc] at this
    rw [sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    linarith
  have hy : y = -α • ((B - t • 1)⁻¹ *ᵥ r) := by
    have hdet := (isUnit_iff_isUnit_det _).mp hB
    rw [← mulVec_smul, ← h2', mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hα : α ≠ 0 := by
    rintro rfl
    apply hne
    rw [hy, neg_zero, zero_smul]
    ext i; cases i <;> rfl
  refine ⟨hα, hy, ?_⟩
  rw [hy, dotProduct_smul, smul_eq_mul] at h1'
  have : α * borderedSecularFunction r B t = 0 := by
    rw [borderedSecularFunction]; linear_combination h1'
  exact (mul_eq_zero.mp this).resolve_left hα

/-- **Powers of the resolvent in an eigenbasis**: if the orthogonal `Q` diagonalizes `B`,
`Qᵀ B Q = diag(d)`, and `λ` is not a `d i`, then `rᵀ (B - λ)⁻ᵏ r = ∑ i, (Qᵀ r)_i² / (d i - λ)^k`. -/
theorem dotProduct_inv_sub_smul_one_pow_mulVec {r : Fin m → ℝ}
    {B Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) {d : Fin m → ℝ}
    (hQB : Qᵀ * B * Q = diagonal d) {t : ℝ} (ht : t ∉ Set.range d) (k : ℕ) :
    r ⬝ᵥ ((B - t • 1)⁻¹ ^ k *ᵥ r) = ∑ i, (Qᵀ *ᵥ r) i ^ 2 / (d i - t) ^ k := by
  have hQB' : star Q * B * Q = diagonal d := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hc : ∀ i, d i ≠ t := fun i h => ht ⟨i, h⟩
  have hQQ : Qᵀ * Q = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * Qᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ
  set f : Fin m → ℝ := fun i => (d i - t)⁻¹
  have hinv : (B - t • 1)⁻¹ = Q * diagonal f * Qᵀ := by
    rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQB' t, inv_mul_mul_star_of_mem_unitaryGroup hQ,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    congr 2
    exact inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hc i))))
  have hpow : ∀ k : ℕ, (Q * diagonal f * Qᵀ) ^ k = Q * diagonal (fun i => f i ^ k) * Qᵀ := by
    intro k
    induction k with
    | zero => simp [hQQ']
    | succ k ih =>
      calc (Q * diagonal f * Qᵀ) ^ (k + 1)
          = Q * (diagonal (fun i => f i ^ k) * (Qᵀ * Q) * diagonal f) * Qᵀ := by
            rw [pow_succ, ih]; simp only [Matrix.mul_assoc]
        _ = Q * diagonal (fun i => f i ^ (k + 1)) * Qᵀ := by
            rw [hQQ, Matrix.mul_one, diagonal_mul_diagonal]; simp only [← pow_succ]
  rw [hinv, hpow, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, inv_pow, div_eq_mul_inv]
  ring

/-- **The bordered secular function in an eigenbasis of the border block**: if the orthogonal `Q`
diagonalizes `B`, `Qᵀ B Q = diag(d)`, and `λ` is not a `d i`, then
`f(λ) = 1 - λ - ∑ i, (Qᵀ r)_i² / (d i - λ)`, that is the rank-one secular function
`Matrix.secularFunction d (-1) (Qᵀ r)` minus `λ`. It connects the Newton iteration of §4.7.7 for
`λ_min` of a bordered matrix with the pole structure of §8.4.3 (one root below `min d`, the others
interlacing the `d i`). -/
theorem borderedSecularFunction_eq_secularFunction_sub {r : Fin m → ℝ}
    {B Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) {d : Fin m → ℝ}
    (hQB : Qᵀ * B * Q = diagonal d) {t : ℝ} (ht : t ∉ Set.range d) :
    borderedSecularFunction r B t = secularFunction d (-1) (Qᵀ *ᵥ r) t - t := by
  have key := dotProduct_inv_sub_smul_one_pow_mulVec (r := r) hQ hQB ht 1
  simp only [pow_one] at key
  rw [borderedSecularFunction, secularFunction, key]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-- An orthogonal eigenbasis of a real symmetric matrix, with Mathlib's eigenvalues. -/
private theorem IsHermitian.exists_orthogonal_transpose_mul_mul_eq {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Qᵀ * B * Q = diagonal hB.eigenvalues := by
  have hU := hB.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at hU
  refine ⟨hB.eigenvectorUnitary, hB.eigenvectorUnitary.2, ?_⟩
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, hU]
  simp [RCLike.ofReal_real_eq_id]

/-- **The derivatives of the bordered secular function** ([golub2013matrix] §4.7.7): for a real
symmetric `B` and `λ` not an eigenvalue of `B`, `f'(λ) = -1 - ‖(B - λ)⁻¹ r‖²` and
`f''(λ) = -2 rᵀ (B - λ)⁻³ r`. Away from the eigenvalues `f` agrees with the rational function
`1 - λ - ∑ (Qᵀ r)_i² / (d i - λ)` in an eigenbasis of `B`
(`Matrix.borderedSecularFunction_eq_secularFunction_sub`), which is differentiated termwise; the
sums are read back through `Matrix.dotProduct_inv_sub_smul_one_pow_mulVec`. -/
theorem hasDerivAt_borderedSecularFunction {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, hB.eigenvalues i ≠ t) :
    HasDerivAt (borderedSecularFunction r B)
        (-1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r)) t ∧
      HasDerivAt (deriv (borderedSecularFunction r B))
        (-2 * (r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r))) t := by
  obtain ⟨Q, hQ, hQB⟩ := hB.exists_orthogonal_transpose_mul_mul_eq
  set d := hB.eigenvalues
  set w := Qᵀ *ᵥ r
  have hopen : (Set.range d)ᶜ ∈ nhds t :=
    (Set.finite_range d).isClosed.isOpen_compl.mem_nhds fun ⟨i, hi⟩ => ht i hi
  -- the first derivative at every non-pole
  have hd1 : ∀ s ∉ Set.range d, HasDerivAt (borderedSecularFunction r B)
      (-1 - ∑ i, w i ^ 2 / (d i - s) ^ 2) s := fun s hs => by
    have hev : borderedSecularFunction r B =ᶠ[nhds s] fun u => secularFunction d (-1) w u - u := by
      filter_upwards [(Set.finite_range d).isClosed.isOpen_compl.mem_nhds hs] with u hu
      exact borderedSecularFunction_eq_secularFunction_sub hQ hQB hu
    have h := (hasDerivAt_secularFunction d (-1) w hs).sub (hasDerivAt_id' s)
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  -- the resolvent is symmetric, so `‖(B - λ)⁻¹ r‖² = rᵀ (B - λ)⁻² r`
  have hsymm : ((B - t • 1)⁻¹)ᵀ = (B - t • 1)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_sub, transpose_smul, transpose_one,
      ← conjTranspose_eq_transpose_of_trivial, hB.eq]
  have hvv : ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) = r ⬝ᵥ ((B - t • 1)⁻¹ ^ 2 *ᵥ r) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, mulVec_mulVec, dotProduct_comm, sq]
  have htd : t ∉ Set.range d := fun ⟨i, hi⟩ => ht i hi
  refine ⟨?_, ?_⟩
  · rw [hvv, dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 2]
    exact hd1 t htd
  · have hev : deriv (borderedSecularFunction r B) =ᶠ[nhds t]
        fun s => -1 - ∑ i, w i ^ 2 / (d i - s) ^ 2 := by
      filter_upwards [hopen] with s hs
      exact (hd1 s hs).deriv
    have hterm : ∀ i, HasDerivAt (fun s => w i ^ 2 / (d i - s) ^ 2)
        (2 * (w i ^ 2 / (d i - t) ^ 3)) t := fun i => by
      have hne : d i - t ≠ 0 := sub_ne_zero.mpr (ht i)
      have h := (hasDerivAt_const t (w i ^ 2)).div
        (((hasDerivAt_const t (d i)).sub (hasDerivAt_id' t)).pow 2) (pow_ne_zero 2 hne)
      convert h using 1
      simp only [Pi.sub_apply, Pi.pow_apply]
      field_simp
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
    refine (((hasDerivAt_const t (-1 : ℝ)).sub hsum).congr_of_eventuallyEq hev).congr_deriv ?_
    rw [dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 3, ← Finset.mul_sum]
    ring

/-- **The signs of the derivatives below the spectrum of `B`** ([golub2013matrix] §4.7.7): if `λ`
is below every eigenvalue of the symmetric `B`, then `f'(λ) = -1 - ‖(B - λ)⁻¹ r‖² ≤ -1` and
`f''(λ) = -2 rᵀ (B - λ)⁻³ r ≤ 0`; so `f` is strictly decreasing and concave there, which is what
makes the Newton iteration (4.7.10) converge monotonically. -/
theorem borderedSecularFunction_deriv_nonpos {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i) :
    -1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) ≤ -1 ∧
      -2 * (r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r)) ≤ 0 := by
  obtain ⟨Q, hQ, hQB⟩ := hB.exists_orthogonal_transpose_mul_mul_eq
  have htd : t ∉ Set.range hB.eigenvalues := fun ⟨i, hi⟩ => (ht i).ne' hi
  refine ⟨?_, ?_⟩
  · have : 0 ≤ ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  · rw [dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 3]
    have : 0 ≤ ∑ i, (Qᵀ *ᵥ r) i ^ 2 / (hB.eigenvalues i - t) ^ 3 :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (pow_nonneg (by linarith [ht i]) 3)
    linarith

end Bordered

end Matrix
