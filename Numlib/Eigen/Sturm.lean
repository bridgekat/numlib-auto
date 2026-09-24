import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Topology.Algebra.Polynomial

/-!
# Sturm sequences and Givens' bisection method

The eigenvalues of a real symmetric tridiagonal matrix can be located one at a time by bisection,
because the characteristic polynomials of its leading principal submatrices form a **Sturm
sequence** whose sign changes count the eigenvalues below any given point
([quarteroni2000numerical] §5.10.2; Wilkinson, *The Algebraic Eigenvalue Problem*, Ch. 5 §§36–39;
[golub1989matrix] §8.5.2; [kress1998numerical] §7.4).

## Main definitions

* `Matrix.symmTridiagonalOf d b n`: the symmetric tridiagonal matrix of order `n` with diagonal
  `d 0, …, d (n-1)` and off-diagonal `b 0, …, b (n-2)`, built from `ℕ`-indexed data so that the
  leading principal submatrix of order `i` is the same construction at `i`
  (`Matrix.symmTridiagonalOf_submatrix_castSucc`).
* `Sturm.seq d b`: the Sturm sequence `p_0 = 1`, `p_1 = d_0 - X`,
  `p_{i+2} = (d_{i+1} - X) p_{i+1} - b_i² p_i` ([quarteroni2000numerical] (5.65)), which is
  `det (T_i - X)` (`Sturm.seq_eq_det`), that is, `(-1)^i` times the characteristic polynomial of
  the leading principal submatrix of order `i` (`Sturm.seq_eq_charpoly`).
* `Sturm.eigenvalues d b n`: the eigenvalues of `T_n` sorted decreasingly and indexed by `Fin n`,
  the backbone's `Matrix.IsHermitian.sortedEigenvalues`.
* `Sturm.sign d b μ`, `Sturm.signChanges d b n μ`: the signs of `p_0(μ), …, p_n(μ)` with the
  convention that a vanishing `p_i(μ)` takes the sign opposite to `p_{i-1}(μ)`, and the number
  `s(μ)` of sign changes among them.
* `Sturm.bisectionStep`, `Sturm.bisectionIterate`: Givens' bisection for the `idx`-th largest
  eigenvalue, driven by `s(μ)`.

## Main results

* `Sturm.eval_ne_zero_or_eval_ne_zero`: for an unreduced matrix consecutive members of the
  sequence have no common root.
* `Sturm.eigenvalues_strictInterlace`: **strict interlacing** ([quarteroni2000numerical]
  Property 5.11): the eigenvalues of `T_i` strictly separate those of `T_{i+1}`. It is Cauchy's
  weak interlacing for a principal submatrix (`Matrix.IsHermitian.eigenvalues₀_submatrix_interlace`)
  sharpened by the absence of common roots; `Sturm.eigenvalues_simple` (the eigenvalues of an
  unreduced matrix are simple) is a corollary.
* `Sturm.signChanges_eq_countRootsIn`: **the Sturm count** ([quarteroni2000numerical]
  Property 5.11): `s(μ)` is the number of eigenvalues of `T_n` that are `≤ μ`. The book says
  "strictly less than `μ`", which is the same off the spectrum; at an eigenvalue its own convention
  counts `μ` (for `n = 1`, `μ = d_0`, the sequence `1, 0` has one sign change). The proof is the
  invariant `sign_i(μ) = (-1)^{N_i(μ)}`, `N_i(μ)` the number of eigenvalues of `T_i` at most `μ`:
  off the roots it is the sign of `∏ (λ_k - μ)`, and at a root of `p_{i+1}` strict interlacing
  places exactly one more eigenvalue of `T_{i+1}` than of `T_i` below `μ`.
* `Sturm.eigenvalues_mem_bisectionIterate`: Givens' bisection keeps the `idx`-th largest
  eigenvalue in an interval that halves at each step (`Sturm.bisectionIterate_length`), starting
  from any interval `(a, b']` with `s(a) ≤ n - idx < s(b')`, which the Gershgorin interval of
  `Sturm.spectrum_subset_Icc` provides.

## Implementation notes

*Unreduced* is the hypothesis `∀ j, j + 1 < n → b j ≠ 0` on the off-diagonal entries that actually
occur in `T_n`; a statement about `T_i` and `T_{i+1}` takes it at order `i + 1`. Nothing is assumed
about the entries `b j` with `j + 1 ≥ n`, which `symmTridiagonalOf d b n` does not read.

The sorted eigenvalues of Mathlib, `Matrix.IsHermitian.eigenvalues₀`, are indexed by
`Fin (Fintype.card (Fin i))`; `Sturm.eigenvalues d b i` is `Matrix.IsHermitian.sortedEigenvalues`
(`Numlib/Eigen/MinMax`), which reindexes them along `Fintype.card_fin` so that the interlacing and
counting statements read on `Fin i` and `Fin (i + 1)` with `Fin.succ` and `Fin.castSucc`. All
counting is done through `Finset.card` of index sets of these sorted lists, which
`Polynomial.countRootsIn` reaches by `Matrix.IsHermitian.roots_charpoly_eq_sortedEigenvalues`.
-/

open Polynomial Finset

namespace Matrix

/-! ### The symmetric tridiagonal matrix of a diagonal and an off-diagonal -/

/-- The symmetric tridiagonal matrix `tridiag(b, d, b)` of order `n`, built from `ℕ`-indexed data:
`d i` on the diagonal, `b i` at `(i, i + 1)` and `(i + 1, i)`, zero elsewhere. Its leading principal
submatrix of order `i` is `symmTridiagonalOf d b i`. -/
def symmTridiagonalOf {R : Type*} [Zero R] (d b : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d i
    else if (i : ℕ) + 1 = j then b i
    else if (j : ℕ) + 1 = i then b j
    else 0

variable {R : Type*} [Zero R] (d b : ℕ → R)

/-- Entrywise description of `symmTridiagonalOf`. -/
theorem symmTridiagonalOf_apply {n : ℕ} (i j : Fin n) :
    symmTridiagonalOf d b n i j =
      if (i : ℕ) = j then d i
      else if (i : ℕ) + 1 = j then b i
      else if (j : ℕ) + 1 = i then b j
      else 0 := rfl

/-- The leading principal submatrix of `symmTridiagonalOf d b (n + 1)` is
`symmTridiagonalOf d b n`. -/
theorem symmTridiagonalOf_submatrix_castSucc (n : ℕ) :
    (symmTridiagonalOf d b (n + 1)).submatrix Fin.castSucc Fin.castSucc
      = symmTridiagonalOf d b n := by
  ext i j
  simp [symmTridiagonalOf_apply]

/-- `symmTridiagonalOf` is tridiagonal. -/
theorem isTridiagonal_symmTridiagonalOf (n : ℕ) : (symmTridiagonalOf d b n).IsTridiagonal := by
  intro i j hij
  rw [symmTridiagonalOf_apply]
  have hij' : (∃ k : ℕ, j < k ∧ k < i) ∨ (∃ k : ℕ, i < k ∧ k < j) := by
    rcases hij with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩
    · exact Or.inl ⟨k, h1, h2⟩
    · exact Or.inr ⟨k, h1, h2⟩
  have h1 : (i : ℕ) ≠ j := by omega
  have h2 : (i : ℕ) + 1 ≠ j := by omega
  have h3 : (j : ℕ) + 1 ≠ i := by omega
  simp [h1, h2, h3]

/-- `symmTridiagonalOf` is symmetric. -/
theorem isSymm_symmTridiagonalOf (n : ℕ) : (symmTridiagonalOf d b n).IsSymm := by
  ext i j
  simp only [transpose_apply, symmTridiagonalOf_apply]
  by_cases h1 : (i : ℕ) = j
  · simp [h1]
  · have h1' : (j : ℕ) ≠ i := fun h => h1 h.symm
    simp only [h1, h1', ite_false]
    by_cases h2 : (i : ℕ) + 1 = j
    · have h3 : ¬ (j : ℕ) + 1 = i := by omega
      simp [h2, h3]
    · simp [h2]

/-- A real `symmTridiagonalOf` is Hermitian. -/
theorem isHermitian_symmTridiagonalOf (d b : ℕ → ℝ) (n : ℕ) :
    (symmTridiagonalOf d b n).IsHermitian :=
  isHermitian_iff_isSymm.mpr (isSymm_symmTridiagonalOf d b n)

end Matrix

namespace Sturm

variable (d b : ℕ → ℝ)

/-! ### The Sturm sequence -/

/-- **The Sturm sequence** of `symmTridiagonalOf d b`, [quarteroni2000numerical] (5.65),
`0`-based: `p_0 = 1`, `p_1 = d_0 - X`, `p_{i+2} = (d_{i+1} - X) p_{i+1} - b_i² p_i`. -/
noncomputable def seq : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (d 0) - X
  | (i + 2) => (C (d (i + 1)) - X) * seq (i + 1) - C (b i) ^ 2 * seq i

@[simp] theorem seq_zero : seq d b 0 = 1 := rfl

@[simp] theorem seq_one : seq d b 1 = C (d 0) - X := rfl

/-- The three-term recurrence of the Sturm sequence. -/
theorem seq_add_two (i : ℕ) :
    seq d b (i + 2) = (C (d (i + 1)) - X) * seq d b (i + 1) - C (b i) ^ 2 * seq d b i := rfl

/-- The characteristic matrix `T_n - X` of `symmTridiagonalOf d b n`, sign convention of the
Sturm sequence. -/
private noncomputable def charMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  (Matrix.symmTridiagonalOf d b n).map C - (X : ℝ[X]) • 1

private theorem charMat_apply {n : ℕ} (i j : Fin n) :
    charMat d b n i j = C (Matrix.symmTridiagonalOf d b n i j) - if i = j then X else 0 := by
  simp [charMat, Matrix.one_apply]

private theorem charMat_submatrix_castSucc (n : ℕ) :
    (charMat d b (n + 1)).submatrix Fin.castSucc Fin.castSucc = charMat d b n := by
  ext i j
  simp [charMat_apply, Matrix.symmTridiagonalOf_apply]

private theorem seq_eq_det_charMat (i : ℕ) : seq d b i = (charMat d b i).det := by
  induction i using Nat.twoStepInduction with
  | zero => simp [charMat]
  | one =>
    rw [seq_one, Matrix.det_fin_one, charMat_apply]
    simp [Matrix.symmTridiagonalOf_apply]
  | more i ih1 ih2 =>
    rw [seq_add_two, ih1, ih2, Matrix.det_succ_row _ (Fin.last (i + 1)), Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    have hzero : ∀ j : Fin i, charMat d b (i + 2) (Fin.last (i + 1)) j.castSucc.castSucc = 0 := by
      intro j
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      have hj := j.isLt
      simp only [Fin.val_last, Fin.val_castSucc]
      have h1 : ¬ (i + 1 = (j : ℕ)) := by omega
      have h2 : ¬ (i + 1 + 1 = (j : ℕ)) := by omega
      have h3 : (j : ℕ) ≠ i := by omega
      have h4 : ¬ (Fin.last (i + 1) = j.castSucc.castSucc) := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [h1, h2, h3, h4]
    rw [Finset.sum_eq_zero fun j _ => by rw [hzero j]; ring, zero_add]
    -- the two surviving terms
    have hdiag : charMat d b (i + 2) (Fin.last (i + 1)) (Fin.last (i + 1)) = C (d (i + 1)) - X := by
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      simp
    have hoff : charMat d b (i + 2) (Fin.last (i + 1)) (Fin.last i).castSucc = C (b i) := by
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      have h1 : ¬ (i + 1 + 1 = i) := by omega
      have h2 : ¬ (Fin.last (i + 1) = (Fin.last i).castSucc) := by
        intro h; have := congrArg Fin.val h; simp at this
      simp [h1, h2]
    have hsub1 : (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
        (Fin.last (i + 1)).succAbove = charMat d b (i + 1) := by
      rw [Fin.succAbove_last, charMat_submatrix_castSucc]
    -- the minor at `(last, last - 1)`: expand along its last column
    have hsub2 : ((charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
        (Fin.last i).castSucc.succAbove).det = C (b i) * (charMat d b i).det := by
      rw [Matrix.det_succ_column _ (Fin.last i), Fin.sum_univ_castSucc]
      have hz : ∀ r : Fin i, (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove r.castSucc (Fin.last i) = 0 := by
        intro r
        rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_castSucc_self, charMat_apply,
          Matrix.symmTridiagonalOf_apply]
        have hr := r.isLt
        have h4 : ¬ (r.castSucc.castSucc = (Fin.last i).succ) := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, h4, ite_false, sub_zero]
        have h1 : ¬ ((r : ℕ) = i + 1) := by omega
        have h2 : (r : ℕ) ≠ i := by omega
        have h3 : ¬ (i + 1 + 1 = (r : ℕ)) := by omega
        simp [h1, h2, h3]
      rw [Finset.sum_eq_zero fun r _ => by rw [hz r]; ring, zero_add]
      have hlast : (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove (Fin.last i) (Fin.last i) = C (b i) := by
        rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_castSucc_self, charMat_apply,
          Matrix.symmTridiagonalOf_apply]
        have h4 : ¬ ((Fin.last i).castSucc = (Fin.last i).succ) := by
          intro h; have := congrArg Fin.val h; simp at this
        simp
      have hmin : ((charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove).submatrix (Fin.last i).succAbove (Fin.last i).succAbove
          = charMat d b i := by
        rw [Matrix.submatrix_submatrix, Fin.succAbove_last, Fin.succAbove_last]
        ext r c
        rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
          Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]), charMat_apply, charMat_apply,
          Matrix.symmTridiagonalOf_apply, Matrix.symmTridiagonalOf_apply]
        simp [Fin.ext_iff]
      rw [hlast, hmin]
      simp
    rw [hdiag, hoff, hsub1, hsub2]
    simp only [Fin.val_last, Fin.val_castSucc]
    have hs1 : ((-1 : ℝ[X]) ^ (i + 1 + (i + 1))) = 1 := Even.neg_one_pow ⟨i + 1, rfl⟩
    have hs2 : ((-1 : ℝ[X]) ^ (i + 1 + i)) = -1 := Odd.neg_one_pow ⟨i, by ring⟩
    rw [hs1, hs2]
    ring

/-- `p_i = det (T_i - X)`, by Laplace expansion of the tridiagonal determinant along its last row
and then along the last column of the remaining minor. -/
theorem seq_eq_det (i : ℕ) :
    seq d b i = ((Matrix.symmTridiagonalOf d b i).map C - (X : ℝ[X]) • 1).det :=
  seq_eq_det_charMat d b i

/-- `p_i` is `(-1)^i` times the characteristic polynomial of the leading principal submatrix of
order `i`. -/
theorem seq_eq_charpoly (i : ℕ) :
    seq d b i = (-1) ^ i * (Matrix.symmTridiagonalOf d b i).charpoly := by
  have h : charMat d b i = -(Matrix.symmTridiagonalOf d b i).charmatrix := by
    ext r c
    simp [charMat_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply]
  rw [seq_eq_det_charMat, h, Matrix.det_neg, Fintype.card_fin, Matrix.charpoly]

/-- `p_i` has degree `i`. -/
theorem natDegree_seq (i : ℕ) : (seq d b i).natDegree = i := by
  rw [seq_eq_charpoly, natDegree_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Matrix.charpoly_monic _).ne_zero, natDegree_pow, natDegree_neg, natDegree_one, mul_zero,
    zero_add, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- `p_i` has leading coefficient `(-1)^i`. -/
theorem leadingCoeff_seq (i : ℕ) : (seq d b i).leadingCoeff = (-1) ^ i := by
  rw [seq_eq_charpoly, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_neg, leadingCoeff_one,
    (Matrix.charpoly_monic _).leadingCoeff, mul_one]

/-- No member of the Sturm sequence is the zero polynomial. -/
theorem seq_ne_zero (i : ℕ) : seq d b i ≠ 0 := by
  intro h
  have := leadingCoeff_seq d b i
  rw [h, leadingCoeff_zero] at this
  exact pow_ne_zero i (neg_ne_zero.mpr one_ne_zero) this.symm

/-- **Consecutive members of the Sturm sequence have no common root** when the off-diagonal
does not vanish: a common root of `p_{i+1}` and `p_{i+2}` is a root of `p_i` by the recurrence,
and so on down to `p_0 = 1`. -/
theorem eval_ne_zero_or_eval_ne_zero (i : ℕ) (hb : ∀ j, j + 1 < i + 1 → b j ≠ 0) (μ : ℝ) :
    (seq d b i).eval μ ≠ 0 ∨ (seq d b (i + 1)).eval μ ≠ 0 := by
  induction i with
  | zero => exact Or.inl (by simp)
  | succ i ih =>
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have h3 : (seq d b i).eval μ = 0 := by
      rw [seq_add_two, eval_sub, eval_mul, eval_mul, eval_pow, eval_C, h1, mul_zero, zero_sub,
        neg_eq_zero, mul_eq_zero, pow_eq_zero_iff two_ne_zero] at h2
      exact h2.resolve_left (hb i (by omega))
    rcases ih (fun j hj => hb j (by omega)) with h | h
    · exact h h3
    · exact h h1

/-- At a root of `p_{i+1}` the neighbours `p_i` and `p_{i+2}` have opposite signs, since then
`p_{i+2}(μ) = -b_i² p_i(μ)` with `p_i(μ) ≠ 0`. This is the lemma behind the sign convention for a
vanishing member. -/
theorem eval_seq_add_two_mul_eval_seq_neg (i : ℕ) (hb : ∀ j, j + 1 < i + 2 → b j ≠ 0) {μ : ℝ}
    (h : (seq d b (i + 1)).eval μ = 0) :
    (seq d b (i + 2)).eval μ * (seq d b i).eval μ < 0 := by
  have hne : (seq d b i).eval μ ≠ 0 :=
    (eval_ne_zero_or_eval_ne_zero d b i (fun j hj => hb j (by omega)) μ).resolve_right
      (by simpa using h)
  rw [seq_add_two, eval_sub, eval_mul, eval_mul, eval_pow, eval_C, h, mul_zero, zero_sub,
    neg_mul, neg_lt_zero, mul_assoc]
  exact mul_pos ((even_two).pow_pos (hb i (by omega))) (mul_self_pos.mpr hne)

/-! ### The sorted eigenvalues -/

/-- The eigenvalues of `symmTridiagonalOf d b n`, sorted decreasingly and indexed by `Fin n`:
the backbone's `Matrix.IsHermitian.sortedEigenvalues`. -/
noncomputable def eigenvalues (n : ℕ) : Fin n → ℝ :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).sortedEigenvalues

/-- The sorted eigenvalues, in terms of `Matrix.IsHermitian.sortedEigenvalues` for any proof of
Hermitianness. -/
theorem eigenvalues_eq_sortedEigenvalues {n : ℕ}
    (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian) :
    eigenvalues d b n = hT.sortedEigenvalues :=
  rfl

/-- The sorted eigenvalues, in terms of `Matrix.IsHermitian.eigenvalues₀` for any proof of
Hermitianness. -/
theorem eigenvalues_eq_eigenvalues₀ {n : ℕ} (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian)
    (k : Fin n) : eigenvalues d b n k = hT.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) :=
  rfl

/-- The sorted eigenvalues decrease. -/
theorem antitone_eigenvalues (n : ℕ) : Antitone (eigenvalues d b n) :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).sortedEigenvalues_antitone

/-- The roots of the characteristic polynomial of `T_n` are the sorted eigenvalues. -/
theorem roots_charpoly_eq (n : ℕ) :
    (Matrix.symmTridiagonalOf d b n).charpoly.roots
      = Multiset.map (eigenvalues d b n) univ.val :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).roots_charpoly_eq_sortedEigenvalues

/-- The characteristic polynomial of `T_n` splits as `∏ (X - λ_k)` over the sorted eigenvalues. -/
theorem charpoly_eq_prod (n : ℕ) :
    (Matrix.symmTridiagonalOf d b n).charpoly = ∏ k, (X - C (eigenvalues d b n k)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun k => X - C (eigenvalues d b n k)) univ.val)
      = Multiset.map (fun a => X - C a) (Multiset.map (eigenvalues d b n) univ.val) by
        rw [Multiset.map_map]; rfl, ← roots_charpoly_eq]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _)
    (Matrix.isHermitian_symmTridiagonalOf d b n).splits_charpoly.natDegree_eq_card_roots.symm).symm

/-- `p_n(μ) = ∏ (λ_k - μ)` over the sorted eigenvalues of `T_n`. -/
theorem eval_seq_eq_prod (n : ℕ) (μ : ℝ) :
    (seq d b n).eval μ = ∏ k, (eigenvalues d b n k - μ) := by
  rw [seq_eq_charpoly, charpoly_eq_prod, eval_mul, eval_pow, eval_neg, eval_one, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [show ∏ k, (eigenvalues d b n k - μ) = ∏ k, -(μ - eigenvalues d b n k) by
    simp only [neg_sub], Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

/-- The sorted eigenvalues are roots of `p_n`. -/
theorem eval_seq_eigenvalues (n : ℕ) (k : Fin n) : (seq d b n).eval (eigenvalues d b n k) = 0 := by
  rw [eval_seq_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

/-- Roots of `p_n` are sorted eigenvalues. -/
theorem exists_eigenvalues_eq_of_eval_eq_zero {n : ℕ} {μ : ℝ} (h : (seq d b n).eval μ = 0) :
    ∃ k, eigenvalues d b n k = μ := by
  rw [eval_seq_eq_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, sub_eq_zero.mp hk⟩

/-! ### Interlacing -/

/-- **Weak (Cauchy) interlacing** for the leading principal submatrix:
`λ_{k+1}(T_{i+1}) ≤ λ_k(T_i) ≤ λ_k(T_{i+1})`. -/
theorem eigenvalues_interlace (i : ℕ) (k : Fin i) :
    eigenvalues d b (i + 1) k.succ ≤ eigenvalues d b i k ∧
      eigenvalues d b i k ≤ eigenvalues d b (i + 1) k.castSucc := by
  have hsub := Matrix.symmTridiagonalOf_submatrix_castSucc d b i
  have hB : ((Matrix.symmTridiagonalOf d b (i + 1)).submatrix Fin.castSucc
      Fin.castSucc).IsHermitian :=
    hsub ▸ Matrix.isHermitian_symmTridiagonalOf d b i
  have h := Matrix.IsHermitian.sortedEigenvalues_submatrix_castSucc_interlace
    (Matrix.isHermitian_symmTridiagonalOf d b (i + 1)) hB k
  rw [Matrix.IsHermitian.sortedEigenvalues_congr hsub hB
    (Matrix.isHermitian_symmTridiagonalOf d b i)] at h
  exact h

/-- **Strict interlacing** ([quarteroni2000numerical] Property 5.11), lower half: for an
unreduced matrix, `λ_{k+1}(T_{i+1}) < λ_k(T_i)`. Equality would make `λ_k(T_i)` a common root of
`p_i` and `p_{i+1}`. -/
theorem eigenvalues_succ_lt (i : ℕ) (hb : ∀ j, j + 1 < i + 1 → b j ≠ 0) (k : Fin i) :
    eigenvalues d b (i + 1) k.succ < eigenvalues d b i k := by
  refine lt_of_le_of_ne (eigenvalues_interlace d b i k).1 fun h => ?_
  have h1 := eval_seq_eigenvalues d b (i + 1) k.succ
  have h2 := eval_seq_eigenvalues d b i k
  rw [h] at h1
  rcases eval_ne_zero_or_eval_ne_zero d b i hb (eigenvalues d b i k) with h' | h'
  · exact h' h2
  · exact h' h1

/-- **Strict interlacing** ([quarteroni2000numerical] Property 5.11), upper half: for an
unreduced matrix, `λ_k(T_i) < λ_k(T_{i+1})`. -/
theorem eigenvalues_lt_castSucc (i : ℕ) (hb : ∀ j, j + 1 < i + 1 → b j ≠ 0) (k : Fin i) :
    eigenvalues d b i k < eigenvalues d b (i + 1) k.castSucc := by
  refine lt_of_le_of_ne (eigenvalues_interlace d b i k).2 fun h => ?_
  have h1 := eval_seq_eigenvalues d b (i + 1) k.castSucc
  have h2 := eval_seq_eigenvalues d b i k
  rw [← h] at h1
  rcases eval_ne_zero_or_eval_ne_zero d b i hb (eigenvalues d b i k) with h' | h'
  · exact h' h2
  · exact h' h1

/-- **Strict interlacing** ([quarteroni2000numerical] Property 5.11) in the form of Mathlib's
sorted `Matrix.IsHermitian.eigenvalues₀`: for an unreduced matrix the eigenvalues of `T_i`
strictly separate those of `T_{i+1}`, `λ_{k+1}(T_{i+1}) < λ_k(T_i) < λ_k(T_{i+1})`. -/
theorem eigenvalues_strictInterlace (i : ℕ) (hb : ∀ j, j + 1 < i + 1 → b j ≠ 0)
    (hT : (Matrix.symmTridiagonalOf d b (i + 1)).IsHermitian)
    (hT' : (Matrix.symmTridiagonalOf d b i).IsHermitian) (k : Fin i) :
    hT.eigenvalues₀ ⟨k + 1, by simp⟩ < hT'.eigenvalues₀ ⟨k, by simp⟩ ∧
      hT'.eigenvalues₀ ⟨k, by simp⟩ < hT.eigenvalues₀ ⟨k, by simp⟩ := by
  have h1 := eigenvalues_succ_lt d b i hb k
  have h2 := eigenvalues_lt_castSucc d b i hb k
  rw [eigenvalues_eq_eigenvalues₀ d b hT, eigenvalues_eq_eigenvalues₀ d b hT'] at h1 h2
  exact ⟨h1, h2⟩

/-- The eigenvalues of an unreduced symmetric tridiagonal matrix are **simple**: the sorted list
strictly decreases. -/
theorem strictAnti_eigenvalues (n : ℕ) (hb : ∀ j, j + 1 < n → b j ≠ 0) :
    StrictAnti (eigenvalues d b n) := by
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro k
    exact (eigenvalues_succ_lt d b n hb k).trans (eigenvalues_lt_castSucc d b n hb k)

/-- **The eigenvalues of an unreduced symmetric tridiagonal matrix are simple**: the roots of its
characteristic polynomial have no repetition ([quarteroni2000numerical] Property 5.11). -/
theorem eigenvalues_simple (n : ℕ) (hb : ∀ j, j + 1 < n → b j ≠ 0) :
    (Matrix.symmTridiagonalOf d b n).charpoly.roots.Nodup := by
  rw [roots_charpoly_eq]
  exact (Finset.univ.nodup).map_on fun x _ y _ h => (strictAnti_eigenvalues d b n hb).injective h

/-! ### The Sturm count -/

/-- `N_n(μ)`: the number of eigenvalues of `T_n` that are at most `μ`, counted through the sorted
list `Sturm.eigenvalues d b n`. -/
noncomputable def count (n : ℕ) (μ : ℝ) : ℕ :=
  (univ.filter fun k => eigenvalues d b n k ≤ μ).card

/-- The count is the number of roots of the characteristic polynomial in `(-∞, μ]`. -/
theorem countRootsIn_Iic_eq_count (n : ℕ) (μ : ℝ) :
    (Matrix.symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) = count d b n μ := by
  classical
  rw [countRootsIn, roots_charpoly_eq, Multiset.filter_map, Multiset.card_map, count]
  congr 1

/-- The count as a sum of indicators over the sorted eigenvalues. -/
theorem count_eq_sum (n : ℕ) (μ : ℝ) :
    count d b n μ = ∑ k, if eigenvalues d b n k ≤ μ then 1 else 0 :=
  Finset.card_filter _ _

@[simp] theorem count_zero (μ : ℝ) : count d b 0 μ = 0 := by simp [count]

/-- At most `n` eigenvalues. -/
theorem count_le (n : ℕ) (μ : ℝ) : count d b n μ ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The count is monotone in `μ`. -/
theorem count_mono (n : ℕ) : Monotone (count d b n) := fun μ ν hμν =>
  Finset.card_le_card fun k hk => by
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.trans hμν

/-- The count at the `k`-th sorted eigenvalue of an unreduced matrix is `n - k`: the eigenvalues
at most `λ_k` are `λ_k, …, λ_{n-1}`. -/
theorem count_eigenvalues {n : ℕ} (hb : ∀ j, j + 1 < n → b j ≠ 0) (k : Fin n) :
    count d b n (eigenvalues d b n k) = n - k := by
  have : (univ.filter fun j => eigenvalues d b n j ≤ eigenvalues d b n k) = Finset.Ici k := by
    ext j
    simp [(strictAnti_eigenvalues d b n hb).le_iff_ge]
  rw [count, this, Fin.card_Ici]

/-- The count of `T_i` at the `k`-th sorted eigenvalue of `T_{i+1}` is `i - k`: by strict
interlacing the eigenvalues of `T_i` at most `λ_k(T_{i+1})` are `θ_k, …, θ_{i-1}`. -/
theorem count_eigenvalues_succ {i : ℕ} (hb : ∀ j, j + 1 < i + 1 → b j ≠ 0) (k : Fin (i + 1)) :
    count d b i (eigenvalues d b (i + 1) k) = i - k := by
  have hset : (univ.filter fun j : Fin i => eigenvalues d b i j ≤ eigenvalues d b (i + 1) k)
      = univ.filter fun j : Fin i => (k : ℕ) ≤ j := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      have h1 := eigenvalues_succ_lt d b i hb j
      have h2 := antitone_eigenvalues d b (i + 1)
        (show j.succ ≤ k by rw [Fin.le_def, Fin.val_succ]; omega)
      linarith
    · intro h
      have h1 := (eigenvalues_lt_castSucc d b i hb j).le
      have h2 := antitone_eigenvalues d b (i + 1)
        (show k ≤ j.castSucc by rw [Fin.le_def, Fin.val_castSucc]; exact h)
      linarith
  rw [count, hset]
  rcases lt_or_ge (k : ℕ) i with hk | hk
  · have : (univ.filter fun j : Fin i => (k : ℕ) ≤ j) = Finset.Ici (⟨k, hk⟩ : Fin i) := by
      ext j
      simp [Fin.le_def]
    rw [this, Fin.card_Ici]
  · have : (univ.filter fun j : Fin i => (k : ℕ) ≤ j) = ∅ := by
      ext j
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
      exact lt_of_lt_of_le j.isLt hk
    rw [this, Finset.card_empty]
    omega

/-- Passing from `T_i` to `T_{i+1}` never loses an eigenvalue below `μ`: weak interlacing. -/
theorem count_le_count_succ (i : ℕ) (μ : ℝ) : count d b i μ ≤ count d b (i + 1) μ := by
  rw [count_eq_sum, count_eq_sum, Fin.sum_univ_succ]
  refine le_add_of_nonneg_of_le (by positivity) (Finset.sum_le_sum fun k _ => ?_)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ((eigenvalues_interlace d b i k).1.trans h1) h2
  · exact zero_le_one
  · exact le_rfl

/-- Passing from `T_i` to `T_{i+1}` adds at most one eigenvalue below `μ`: weak interlacing. -/
theorem count_succ_le (i : ℕ) (μ : ℝ) : count d b (i + 1) μ ≤ count d b i μ + 1 := by
  rw [count_eq_sum, count_eq_sum, Fin.sum_univ_castSucc]
  refine add_le_add (Finset.sum_le_sum fun k _ => ?_) (by split_ifs <;> simp)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ((eigenvalues_interlace d b i k).2.trans h1) h2
  · exact zero_le_one
  · exact le_rfl

/-! ### The sign convention and the sign changes -/

/-- The sign attached to `p_i(μ)` by the convention of [quarteroni2000numerical] Property 5.11:
the sign of `p_i(μ)` when it is nonzero, and the opposite of the sign attached to `p_{i-1}(μ)`
when it vanishes. -/
noncomputable def sign (μ : ℝ) : ℕ → ℝ
  | 0 => 1
  | (i + 1) =>
    if (seq d b (i + 1)).eval μ = 0 then -sign μ i
    else if 0 < (seq d b (i + 1)).eval μ then 1 else -1

@[simp] theorem sign_zero (μ : ℝ) : sign d b μ 0 = 1 := rfl

/-- The sign convention, unfolded one step. -/
theorem sign_succ (μ : ℝ) (i : ℕ) :
    sign d b μ (i + 1) =
      if (seq d b (i + 1)).eval μ = 0 then -sign d b μ i
      else if 0 < (seq d b (i + 1)).eval μ then 1 else -1 := rfl

/-- The number `s(μ)` of sign changes in `p_0(μ), …, p_n(μ)`, with the convention `Sturm.sign`
for vanishing members. -/
noncomputable def signChanges (n : ℕ) (μ : ℝ) : ℕ :=
  ((range n).filter fun i => sign d b μ (i + 1) ≠ sign d b μ i).card

@[simp] theorem signChanges_zero (μ : ℝ) : signChanges d b 0 μ = 0 := by simp [signChanges]

/-- Extending the sequence by one member adds one sign change or none. -/
theorem signChanges_succ (n : ℕ) (μ : ℝ) :
    signChanges d b (n + 1) μ =
      signChanges d b n μ + if sign d b μ (n + 1) ≠ sign d b μ n then 1 else 0 := by
  rw [signChanges, signChanges, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- Off the spectrum of `T_n`, `p_n(μ)` is positive exactly when an even number of eigenvalues lie
below `μ`: `p_n(μ) = ∏ (λ_k - μ)` has one negative factor per eigenvalue below `μ`. -/
theorem eval_seq_pos_iff {n : ℕ} {μ : ℝ} (hμ : ∀ k, eigenvalues d b n k ≠ μ) :
    0 < (seq d b n).eval μ ↔ Even (count d b n μ) := by
  have hfac : ∀ k, eigenvalues d b n k - μ
      = (if eigenvalues d b n k ≤ μ then (-1 : ℝ) else 1) * |eigenvalues d b n k - μ| := by
    intro k
    split_ifs with h
    · rw [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne h (hμ k)))]
      ring
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge h)), one_mul]
  have hpos : 0 < ∏ k, |eigenvalues d b n k - μ| :=
    Finset.prod_pos fun k _ => abs_pos.mpr (sub_ne_zero.mpr (hμ k))
  rw [eval_seq_eq_prod, Finset.prod_congr rfl fun k _ => hfac k, Finset.prod_mul_distrib,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← count]
  rcases Nat.even_or_odd (count d b n μ) with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun _ => h, fun _ => hpos⟩
  · rw [h.neg_one_pow, neg_one_mul, neg_pos]
    exact ⟨fun h' => absurd (h'.trans hpos) (lt_irrefl _),
      fun h' => absurd h' (Nat.not_even_iff_odd.mpr h)⟩

/-- **The sign invariant**: with the convention for vanishing members, the sign attached to
`p_i(μ)` is `(-1)^{N_i(μ)}`, `N_i(μ)` the number of eigenvalues of `T_i` at most `μ`. Off the
roots this is `Sturm.eval_seq_pos_iff`; at a root of `p_{i+1}` strict interlacing places exactly
one more eigenvalue of `T_{i+1}` than of `T_i` at or below `μ`. -/
theorem sign_eq_neg_one_pow (μ : ℝ) (i : ℕ) (hb : ∀ j, j + 1 < i → b j ≠ 0) :
    sign d b μ i = (-1) ^ count d b i μ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sign_succ]
    by_cases h0 : (seq d b (i + 1)).eval μ = 0
    · rw [ite_eq_left h0, ih (fun j hj => hb j (by omega))]
      obtain ⟨k, hk⟩ := exists_eigenvalues_eq_of_eval_eq_zero d b h0
      rw [← hk, count_eigenvalues d b hb k, count_eigenvalues_succ d b hb k,
        show i + 1 - (k : ℕ) = (i - k) + 1 by have := k.isLt; omega, pow_succ]
      ring
    · rw [ite_eq_right h0]
      have hμ : ∀ k, eigenvalues d b (i + 1) k ≠ μ := fun k hk =>
        h0 (hk ▸ eval_seq_eigenvalues d b (i + 1) k)
      rcases Nat.even_or_odd (count d b (i + 1) μ) with h | h
      · rw [ite_eq_left ((eval_seq_pos_iff d b hμ).mpr h), h.neg_one_pow]
      · rw [ite_eq_right fun h' => Nat.not_even_iff_odd.mpr h ((eval_seq_pos_iff d b hμ).mp h'),
          h.neg_one_pow]

/-- **The Sturm count** ([quarteroni2000numerical] Property 5.11; Wilkinson Ch. 5 §37;
[golub1989matrix] Theorem 8.5.1): for an unreduced symmetric tridiagonal matrix, the number of sign
changes in `p_0(μ), …, p_n(μ)` — with a vanishing member taking the sign opposite to its
predecessor — is the number of eigenvalues of `T_n` that are at most `μ`. The book says "strictly
less than `μ`", which agrees off the spectrum; at an eigenvalue its own convention counts `μ`. -/
theorem signChanges_eq_count (n : ℕ) (hb : ∀ j, j + 1 < n → b j ≠ 0) (μ : ℝ) :
    signChanges d b n μ = count d b n μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [signChanges_succ, ih (fun j hj => hb j (by omega)), sign_eq_neg_one_pow d b μ (n + 1) hb,
      sign_eq_neg_one_pow d b μ n (fun j hj => hb j (by omega))]
    have h1 := count_le_count_succ d b n μ
    have h2 := count_succ_le d b n μ
    rcases Nat.lt_or_ge (count d b n μ) (count d b (n + 1) μ) with h | h
    · have heq : count d b (n + 1) μ = count d b n μ + 1 := by omega
      rw [heq, pow_succ, ite_eq_left]
      intro h'
      have : (-1 : ℝ) ^ count d b n μ ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [mul_neg_one] at h'
      exact this (by linarith)
    · have heq : count d b (n + 1) μ = count d b n μ := le_antisymm h h1
      rw [heq, ite_eq_right (by simp), add_zero]

/-- **The Sturm count** in terms of `Polynomial.countRootsIn`: `s(μ)` is the number of roots of
the characteristic polynomial of `T_n` in `(-∞, μ]`, with multiplicity (all simple, by
`Sturm.eigenvalues_simple`). -/
theorem signChanges_eq_countRootsIn (n : ℕ) (hb : ∀ j, j + 1 < n → b j ≠ 0) (μ : ℝ) :
    signChanges d b n μ =
      (Matrix.symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) := by
  rw [signChanges_eq_count d b n hb, countRootsIn_Iic_eq_count]

/-- The Sturm count is monotone in `μ`. -/
theorem signChanges_monotone (n : ℕ) (hb : ∀ j, j + 1 < n → b j ≠ 0) :
    Monotone (signChanges d b n) := by
  intro μ ν h
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb]
  exact count_mono d b n h

/-! ### The Gershgorin interval -/

/-- The Gershgorin radius of row `i` of `symmTridiagonalOf d b n`: `|b (i-1)| + |b i|`, with the
boundary terms dropped in the first and the last row. -/
noncomputable def gershgorinRadius (n : ℕ) (i : Fin n) : ℝ :=
  (if 0 < (i : ℕ) then |b (i - 1)| else 0) + if (i : ℕ) + 1 < n then |b i| else 0

/-- The off-diagonal row sum of `symmTridiagonalOf d b n` is its Gershgorin radius. -/
theorem sum_erase_abs_eq_gershgorinRadius (n : ℕ) (i : Fin n) :
    ∑ j ∈ univ.erase i, |Matrix.symmTridiagonalOf d b n i j| = gershgorinRadius b n i := by
  have hsplit : ∀ j ∈ univ.erase i, |Matrix.symmTridiagonalOf d b n i j|
      = (if (j : ℕ) + 1 = i then |b j| else 0) + if (i : ℕ) + 1 = j then |b i| else 0 := by
    intro j hj
    have hji : (j : ℕ) ≠ i := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    rw [Matrix.symmTridiagonalOf_apply, ite_eq_right (Ne.symm hji)]
    by_cases h1 : (i : ℕ) + 1 = j
    · have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
      simp [h1, h2]
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, gershgorinRadius]
  congr 1
  · by_cases hi : 0 < (i : ℕ)
    · rw [ite_eq_left hi]
      have hmem : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) ∈ univ.erase i := by
        simp [Fin.ext_iff]
        omega
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · have : ((i : ℕ) - 1) + 1 = i := by omega
        simp [this]
      · intro j _ hj
        have : ¬ ((j : ℕ) + 1 = i) := fun h => hj (Fin.ext (by simp; omega))
        simp [this]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ ((j : ℕ) + 1 = i) := by omega
      simp [this]
  · by_cases hi : (i : ℕ) + 1 < n
    · rw [ite_eq_left hi]
      have hmem : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ∈ univ.erase i := by
        simp [Fin.ext_iff]
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · simp
      · intro j _ hj
        have : ¬ ((i : ℕ) + 1 = j) := fun h => hj (Fin.ext h.symm)
        simp [this]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ ((i : ℕ) + 1 = j) := fun h => hi (h ▸ j.isLt)
      simp [this]

/-- **Gershgorin for the tridiagonal matrix** (the interval of Program 44 in
[quarteroni2000numerical] §5.10.2): every real eigenvalue lies within the Gershgorin radius of some
diagonal entry. -/
theorem exists_abs_sub_le_of_mem_spectrum {n : ℕ} {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (Matrix.symmTridiagonalOf d b n)) :
    ∃ i : Fin n, |μ - d i| ≤ gershgorinRadius b n i := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ
  refine ⟨i, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  simp only [Real.norm_eq_abs] at hi
  rw [sum_erase_abs_eq_gershgorinRadius] at hi
  have hd : Matrix.symmTridiagonalOf d b n i i = d i := by simp [Matrix.symmTridiagonalOf_apply]
  rwa [hd] at hi

/-- `p_n` and the characteristic polynomial of `T_n` have the same roots. -/
theorem eval_seq_eq_zero_iff (n : ℕ) (μ : ℝ) :
    (seq d b n).eval μ = 0 ↔ (Matrix.symmTridiagonalOf d b n).charpoly.eval μ = 0 := by
  rw [seq_eq_charpoly, eval_mul, eval_pow, eval_neg, eval_one, mul_eq_zero,
    or_iff_right (pow_ne_zero _ (by norm_num))]

/-- The sorted eigenvalues are eigenvalues. -/
theorem eigenvalues_mem_spectrum (n : ℕ) (k : Fin n) :
    eigenvalues d b n k ∈ spectrum ℝ (Matrix.symmTridiagonalOf d b n) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, ← eval_seq_eq_zero_iff]
  exact eval_seq_eigenvalues d b n k

/-- **The Gershgorin interval encloses the spectrum** ([quarteroni2000numerical] §5.10.2, the
`[α, β]` of Givens' method): every real eigenvalue of `symmTridiagonalOf d b n` lies in
`[⨅ (d i - r i), ⨆ (d i + r i)]` with `r` the Gershgorin radii. -/
theorem spectrum_subset_Icc (n : ℕ) :
    spectrum ℝ (Matrix.symmTridiagonalOf d b n) ⊆
      Set.Icc (⨅ i : Fin n, (d i - gershgorinRadius b n i))
        (⨆ i : Fin n, (d i + gershgorinRadius b n i)) := by
  intro μ hμ
  obtain ⟨i, hi⟩ := exists_abs_sub_le_of_mem_spectrum d b hμ
  rw [abs_le] at hi
  have h1 : (⨅ j : Fin n, (d j - gershgorinRadius b n j)) ≤ d i - gershgorinRadius b n i :=
    ciInf_le (f := fun j : Fin n => d j - gershgorinRadius b n j) (Set.finite_range _).bddBelow i
  have h2 : d i + gershgorinRadius b n i ≤ ⨆ j : Fin n, (d j + gershgorinRadius b n j) :=
    le_ciSup (f := fun j : Fin n => d j + gershgorinRadius b n j) (Set.finite_range _).bddAbove i
  constructor <;> linarith [hi.1, hi.2]

/-- The sorted eigenvalues lie in the Gershgorin interval. -/
theorem eigenvalues_mem_Icc (n : ℕ) (k : Fin n) :
    eigenvalues d b n k ∈ Set.Icc (⨅ i : Fin n, (d i - gershgorinRadius b n i))
      (⨆ i : Fin n, (d i + gershgorinRadius b n i)) :=
  spectrum_subset_Icc d b n (eigenvalues_mem_spectrum d b n k)

/-- Below the Gershgorin interval no eigenvalue is counted. -/
theorem count_eq_zero_of_lt {n : ℕ} {a : ℝ}
    (ha : a < ⨅ i : Fin n, (d i - gershgorinRadius b n i)) : count d b n a = 0 := by
  rw [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  exact not_le.mpr (lt_of_lt_of_le ha (eigenvalues_mem_Icc d b n k).1)

/-- At or above the Gershgorin interval every eigenvalue is counted. -/
theorem count_eq_of_le {n : ℕ} {b' : ℝ}
    (hb' : (⨆ i : Fin n, (d i + gershgorinRadius b n i)) ≤ b') : count d b n b' = n := by
  rw [count, Finset.filter_true_of_mem fun k _ => (eigenvalues_mem_Icc d b n k).2.trans hb',
    Finset.card_univ, Fintype.card_fin]

/-! ### Givens' bisection -/

/-- One step of **Givens' bisection** for the `idx`-th largest eigenvalue (`1`-based, as in
[quarteroni2000numerical] Program 42): with `c` the midpoint of `(a, b')`, keep `(a, c)` if more
than `n - idx` eigenvalues are at most `c`, and `(c, b')` otherwise. -/
noncomputable def bisectionStep (n idx : ℕ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if n - idx < signChanges d b n ((ab.1 + ab.2) / 2) then (ab.1, (ab.1 + ab.2) / 2)
  else ((ab.1 + ab.2) / 2, ab.2)

/-- `r` steps of Givens' bisection from the interval `ab`. -/
noncomputable def bisectionIterate (n idx : ℕ) (ab : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => ab
  | (r + 1) => bisectionStep d b n idx (bisectionIterate n idx ab r)

@[simp] theorem bisectionIterate_zero (n idx : ℕ) (ab : ℝ × ℝ) :
    bisectionIterate d b n idx ab 0 = ab := rfl

/-- One more bisection step. -/
theorem bisectionIterate_succ (n idx : ℕ) (ab : ℝ × ℝ) (r : ℕ) :
    bisectionIterate d b n idx ab (r + 1)
      = bisectionStep d b n idx (bisectionIterate d b n idx ab r) :=
  rfl

/-- Each bisection step halves the interval. -/
theorem bisectionStep_length (n idx : ℕ) (ab : ℝ × ℝ) :
    (bisectionStep d b n idx ab).2 - (bisectionStep d b n idx ab).1 = (ab.2 - ab.1) / 2 := by
  rw [bisectionStep]
  split_ifs <;> simp only <;> ring

/-- After `r` steps the interval has length `(b' - a) / 2 ^ r`. -/
theorem bisectionIterate_length (n idx : ℕ) (ab : ℝ × ℝ) (r : ℕ) :
    (bisectionIterate d b n idx ab r).2 - (bisectionIterate d b n idx ab r).1
      = (ab.2 - ab.1) / 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [bisectionIterate_succ, bisectionStep_length, ih, pow_succ, div_div]

/-- The bracketing invariant `s(a) ≤ n - idx < s(b')` is preserved by a bisection step. -/
theorem bisectionStep_invariant (n idx : ℕ) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) :
    signChanges d b n (bisectionStep d b n idx ab).1 ≤ n - idx ∧
      n - idx < signChanges d b n (bisectionStep d b n idx ab).2 := by
  rw [bisectionStep]
  split_ifs with hc
  · exact ⟨h.1, hc⟩
  · exact ⟨not_lt.mp hc, h.2⟩

/-- The bracketing invariant holds along the whole iteration. -/
theorem bisectionIterate_invariant (n idx : ℕ) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    signChanges d b n (bisectionIterate d b n idx ab r).1 ≤ n - idx ∧
      n - idx < signChanges d b n (bisectionIterate d b n idx ab r).2 := by
  induction r with
  | zero => exact h
  | succ r ih => exact bisectionStep_invariant d b n idx ih

/-- The `idx`-th largest eigenvalue lies in `(a, b']` exactly when at most `n - idx` eigenvalues
are at most `a` and more than `n - idx` are at most `b'`. -/
theorem eigenvalues_mem_Ioc_of_count {n idx : ℕ} (hb : ∀ j, j + 1 < n → b j ≠ 0) (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) {a b' : ℝ} (ha : count d b n a ≤ n - idx) (hb' : n - idx < count d b n b') :
    eigenvalues d b n ⟨idx - 1, by omega⟩ ∈ Set.Ioc a b' := by
  set k : Fin n := ⟨idx - 1, by omega⟩ with hk
  constructor
  · by_contra hle
    push Not at hle
    have : count d b n (eigenvalues d b n k) ≤ count d b n a := count_mono d b n hle
    rw [count_eigenvalues d b hb k] at this
    simp only [hk] at this
    omega
  · by_contra hlt
    push Not at hlt
    -- every eigenvalue at most `b'` has index above `k`
    have hsub : (univ.filter fun j => eigenvalues d b n j ≤ b') ⊆ Finset.Ioi k := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [Finset.mem_Ioi]
      by_contra hjk
      push Not at hjk
      have := antitone_eigenvalues d b n hjk
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    simp only [hk] at this
    rw [count] at hb'
    omega

/-- **Givens' bisection converges** ([quarteroni2000numerical] §5.10.2): for an unreduced matrix,
`1 ≤ idx ≤ n`, and a starting interval `(a, b']` with `s(a) ≤ n - idx < s(b')`, the `idx`-th largest
eigenvalue lies in the `r`-th bisection interval for every `r`, whose length is `(b' - a) / 2^r`
(`Sturm.bisectionIterate_length`); the midpoint is therefore within `(b' - a) / 2^(r+1)` of it. The
Gershgorin interval supplies a starting bracket (`Sturm.signChanges_gershgorin`). -/
theorem eigenvalues_mem_bisectionIterate {n idx : ℕ} (hb : ∀ j, j + 1 < n → b j ≠ 0)
    (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    eigenvalues d b n ⟨idx - 1, by omega⟩ ∈
      Set.Ioc (bisectionIterate d b n idx ab r).1 (bisectionIterate d b n idx ab r).2 := by
  have hinv := bisectionIterate_invariant d b n idx h r
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb] at hinv
  exact eigenvalues_mem_Ioc_of_count d b hb hidx hidxn hinv.1 hinv.2

/-- `Sturm.eigenvalues_mem_bisectionIterate` for Mathlib's sorted `Matrix.IsHermitian.eigenvalues₀`:
the `idx`-th largest eigenvalue `hT.eigenvalues₀ ⟨idx - 1, _⟩` stays in the bisection interval. -/
theorem eigenvalues₀_mem_bisectionIterate {n idx : ℕ} (hb : ∀ j, j + 1 < n → b j ≠ 0)
    (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    hT.eigenvalues₀ ⟨idx - 1, by simp; omega⟩ ∈
      Set.Ioc (bisectionIterate d b n idx ab r).1 (bisectionIterate d b n idx ab r).2 :=
  eigenvalues_mem_bisectionIterate d b hb hidx hidxn h r

/-- The Gershgorin interval brackets every eigenvalue: a point `a` below it and a point `b'` at or
above it satisfy `s(a) = 0 ≤ n - idx < n = s(b')` for `1 ≤ idx ≤ n`. -/
theorem signChanges_gershgorin {n idx : ℕ} (hb : ∀ j, j + 1 < n → b j ≠ 0) (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n)
    {a b' : ℝ} (ha : a < ⨅ i : Fin n, (d i - gershgorinRadius b n i))
    (hb' : (⨆ i : Fin n, (d i + gershgorinRadius b n i)) ≤ b') :
    signChanges d b n a ≤ n - idx ∧ n - idx < signChanges d b n b' := by
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb, count_eq_zero_of_lt d b ha,
    count_eq_of_le d b hb']
  omega

end Sturm
