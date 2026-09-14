/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Charpoly.Companion`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The companion matrix of a polynomial

For a monic polynomial `p = Xⁿ + a_{n-1} X^{n-1} + … + a₀` over a commutative ring, the
**companion** (Frobenius) matrix `Matrix.companion p n : Matrix (Fin n) (Fin n) R` has first row
`(-a_{n-1}, …, -a₀)` and ones on the subdiagonal, in the layout of [quarteroni2000numerical]
(5.72). Its characteristic polynomial is `p` (`Matrix.charpoly_companion`), so over a field its
spectrum is the set of roots of `p` (`Matrix.spectrum_companion`): the roots of a polynomial are
the eigenvalues of a matrix. This is the observation behind [quarteroni2000numerical] Exercise 5.8
and §5.4 — by Abel's theorem there is no finite direct method for the eigenvalues of a general
`n × n` matrix, `n ≥ 5` — and behind root finders that diagonalize the companion matrix.

The matrix is defined for every `p` and every size `n`, reading the coefficients `a_{n-1}, …, a₀`
off `p`; the identity `charpoly = p` holds when `p` is monic of degree `n`. A polynomial with
leading coefficient `a_n ≠ 1` is normalized first, `companion (C a_n⁻¹ * p) n`.

## Implementation notes

`Matrix.charpoly_companion` is proved by induction on `n`, expanding `det (X I - C)` along the
last column: the two nonzero entries of that column are `a₀` in the first row, whose minor is
upper triangular with `-1` on the diagonal, and `X` in the last row, whose minor is the
characteristic matrix of the companion matrix of `p.divX = (p - a₀) / X`.
-/

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The **companion matrix** of `p`, of size `n`: the first row carries `-p.coeff (n - 1 - j)`,
the subdiagonal carries ones, everything else vanishes. For `p` monic of degree `n` this is the
matrix `C` of [quarteroni2000numerical] (5.72), with `a_n = 1`. -/
def companion (p : R[X]) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i j => if (i : ℕ) = 0 then -p.coeff (n - 1 - j) else if (i : ℕ) = j + 1 then 1 else 0

variable (p : R[X]) {n : ℕ}

/-- The entries of the companion matrix. -/
theorem companion_apply (i j : Fin n) :
    companion p n i j
      = if (i : ℕ) = 0 then -p.coeff (n - 1 - j) else if (i : ℕ) = j + 1 then 1 else 0 := rfl

/-- The first row of the companion matrix carries the negated coefficients, highest first. -/
theorem companion_zero_apply (j : Fin (n + 1)) : companion p (n + 1) 0 j = -p.coeff (n - j) := by
  simp [companion_apply]

/-- The subdiagonal of the companion matrix carries ones. -/
theorem companion_succ_castSucc (i : Fin n) : companion p (n + 1) i.succ i.castSucc = 1 := by
  simp [companion_apply]

/-- Below the first row, the companion matrix vanishes off the subdiagonal. -/
theorem companion_succ_apply_of_ne {i : Fin n} {j : Fin (n + 1)} (h : (i : ℕ) ≠ j) :
    companion p (n + 1) i.succ j = 0 := by
  simp [companion_apply, h]

/-- Deleting the last row and column of the companion matrix of `p` leaves the companion matrix
of `p.divX = (p - a₀) / X`. -/
theorem companion_submatrix_castSucc :
    (companion p (n + 1)).submatrix Fin.castSucc Fin.castSucc = companion p.divX n := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [submatrix_apply, companion_apply, Fin.val_castSucc, coeff_divX]
  by_cases h0 : i = 0
  · simp only [h0, ite_true]
    congr 2
    omega
  · simp [h0]

/-- The characteristic matrix of a principal submatrix is the principal submatrix of the
characteristic matrix. -/
private theorem charmatrix_submatrix_castSucc (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    charmatrix (A.submatrix Fin.castSucc Fin.castSucc)
      = (charmatrix A).submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  rw [submatrix_apply, charmatrix_apply, charmatrix_apply, submatrix_apply]
  rcases eq_or_ne i j with rfl | h
  · rw [diagonal_apply_eq, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (Fin.castSucc_injective _ |>.ne h)]

/-- The minor of the characteristic matrix of the companion matrix obtained by deleting the first
row and the last column: `-1` on the diagonal, `X` just above it, `0` elsewhere. -/
private theorem charmatrix_companion_submatrix_succ_castSucc (i j : Fin n) :
    (charmatrix (companion p (n + 1))).submatrix Fin.succ Fin.castSucc i j
      = if i = j then -1 else if (i : ℕ) + 1 = j then X else 0 := by
  rw [submatrix_apply, charmatrix_apply, diagonal_apply]
  rcases eq_or_ne i j with rfl | hij
  · have h : ¬ (i.succ = i.castSucc) := by simp [Fin.ext_iff]
    rw [ite_eq_right h, ite_eq_left rfl, companion_succ_castSucc, map_one, zero_sub]
  · have hij' : (i : ℕ) ≠ j := Fin.val_ne_iff.2 hij
    rw [ite_eq_right hij, companion_succ_apply_of_ne _ (by simpa using hij'), map_zero, sub_zero]
    by_cases h : (i : ℕ) + 1 = j
    · have h' : i.succ = j.castSucc := Fin.ext (by simpa using h)
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ (i.succ = j.castSucc) := fun e => h (by simpa using congrArg Fin.val e)
      rw [ite_eq_right h, ite_eq_right h']

/-- That minor has determinant `(-1)^n`: it is upper triangular. -/
private theorem det_charmatrix_companion_submatrix_succ_castSucc :
    ((charmatrix (companion p (n + 1))).submatrix Fin.succ Fin.castSucc).det = (-1) ^ n := by
  rw [det_of_isUpperTriangular]
  · rw [Finset.prod_congr rfl fun i _ => charmatrix_companion_submatrix_succ_castSucc p i i]
    simp
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    rw [charmatrix_companion_submatrix_succ_castSucc,
      ite_eq_right (fun h : i = j => absurd h (ne_of_gt hji)), ite_eq_right (by omega)]

/-- **The characteristic polynomial of the companion matrix is the polynomial itself**
([quarteroni2000numerical] Exercise 5.8): for `p` monic of degree `n`,
`(companion p n).charpoly = p`. By induction on `n`, expanding `det (X I - C)` along the last
column. -/
theorem charpoly_companion {p : R[X]} (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n) :
    (companion p n).charpoly = p := by
  induction n generalizing p with
  | zero =>
    rw [charpoly_isEmpty]
    exact (eq_one_of_monic_natDegree_zero hp hn).symm
  | succ k ih =>
    -- the polynomial without its constant term, divided by `X`
    have hq : p.divX.Monic := by
      rw [Monic, leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, hn, Nat.add_sub_cancel,
        coeff_divX, ← hn]
      exact hp
    have hqdeg : p.divX.natDegree = k := by
      rw [natDegree_divX_eq_natDegree_tsub_one, hn, Nat.add_sub_cancel]
    have hrec := ih hq hqdeg
    rw [charpoly, det_succ_column _ (Fin.last k)]
    -- the last column has two nonzero entries: `a₀` in the first row and `X` in the last one
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- a `1 × 1` matrix
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [show (default : Fin 1) = 0 from rfl]
      simp only [Fin.last_zero, Fin.val_zero, add_zero, pow_zero, one_mul, charmatrix_apply_eq,
        companion_zero_apply, Nat.sub_self, det_fin_zero, mul_one, map_neg, sub_neg_eq_add]
      conv_rhs => rw [← divX_mul_X_add p]
      rw [eq_one_of_monic_natDegree_zero hq hqdeg, one_mul, add_comm]
    have h0l : (0 : Fin (k + 1)) ≠ Fin.last k := Fin.ne_of_val_ne (by simpa using hk.ne)
    rw [Finset.sum_eq_add 0 (Fin.last k) h0l]
    · rw [Fin.succAbove_last, Fin.succAbove_zero, det_charmatrix_companion_submatrix_succ_castSucc,
        ← charmatrix_submatrix_castSucc, companion_submatrix_castSucc, ← charpoly, hrec,
        charmatrix_apply_ne _ _ _ h0l,
        charmatrix_apply_eq, companion_zero_apply, Fin.val_last, Nat.sub_self, map_neg, neg_neg,
        show companion p (k + 1) (Fin.last k) (Fin.last k) = 0 by
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [← Fin.succ_last]
          exact companion_succ_apply_of_ne p (by simp)]
      simp only [Fin.val_zero, zero_add, map_zero, sub_zero]
      rw [mul_comm ((-1 : R[X]) ^ k) (C (p.coeff 0)), mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, mul_one, one_mul, mul_comm X, add_comm, divX_mul_X_add]
    · intro i _ ⟨hi0, hil⟩
      have hi : ∃ j : Fin k, i = j.succ := ⟨i.pred hi0, (Fin.succ_pred i hi0).symm⟩
      obtain ⟨j, rfl⟩ := hi
      rw [charmatrix_apply_ne _ _ _ hil, companion_succ_apply_of_ne _ (by
        have := Fin.val_ne_iff.2 hil; simp at this ⊢; omega), map_zero, neg_zero, mul_zero,
        zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
    · exact fun h => absurd (Finset.mem_univ _) h

/-- **The eigenvalues of the companion matrix are the roots of the polynomial**
([quarteroni2000numerical] Exercise 5.8): over a field, for `p` monic of degree `n`,
`spectrum K (companion p n) = p.rootSet K`. -/
theorem spectrum_companion {K : Type*} [Field K] {p : K[X]} (hp : p.Monic) {n : ℕ}
    (hn : p.natDegree = n) : spectrum K (companion p n) = p.rootSet K := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_companion hp hn, mem_rootSet_of_ne hp.ne_zero,
    aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id, IsRoot.def]

end Matrix
