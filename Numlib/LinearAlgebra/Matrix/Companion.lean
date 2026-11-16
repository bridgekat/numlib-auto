/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $R$ be a commutative ring, and let $p = X^n + a_{n-1} X^{n-1} + \dots + a_0$ be a monic
polynomial over $R$. The **companion matrix** (Frobenius matrix) of $p$ is the $n \times n$ matrix
$$C = \begin{bmatrix} -a_{n-1} & -a_{n-2} & \cdots & -a_1 & -a_0 \\ 1 & 0 & \cdots & 0 & 0 \\ 0 & 1
  & \cdots & 0 & 0 \\ \vdots & & \ddots & & \vdots \\ 0 & 0 & \cdots & 1 & 0 \end{bmatrix},$$
in the layout of (5.72) of [quarteroni2000numerical]. Its characteristic polynomial is $p$, so over
a field its spectrum is the set of roots of $p$: the roots of a polynomial are the eigenvalues of a
matrix. This is the observation behind Exercise 5.8 and §5.4 of [quarteroni2000numerical]. By Abel's
theorem, there is therefore no finite direct method for the eigenvalues of a general $n \times n$
matrix with $n \ge 5$. The observation is also behind root finders that compute the eigenvalues of
the companion matrix.

## Main definitions

* `Matrix.companion`: the companion matrix of a polynomial, of a given size $n$.

## Main results

* `Matrix.charpoly_companion`: for $p$ monic of degree $n$, the characteristic polynomial of the
  companion matrix is $p$.
* `Matrix.spectrum_companion`: over a field, for $p$ monic of degree $n$, the spectrum of the
  companion matrix is the set of roots of $p$.

## Implementation notes

* The matrix `Matrix.companion p n` is defined for every polynomial $p$ and every size $n$. It reads
  the coefficients $a_{n-1}, \dots, a_0$ off $p$. The identity $\det(XI - C) = p$ holds when $p$ is
  monic of degree $n$. For a polynomial with the leading coefficient $a_n \neq 1$, normalize first:
  `Matrix.companion (C p.leadingCoeff⁻¹ * p) n`.
* `Matrix.charpoly_companion` is proved by induction on $n$, with the expansion of $\det(XI - C)$
  along the last column. The two nonzero entries of that column are $a_0$ in the first row, whose
  minor is upper triangular with $-1$ on the diagonal, and $X$ in the last row, whose minor is the
  characteristic matrix of the companion matrix of $(p - a_0)/X$ (`Polynomial.divX`).
-/

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The **companion matrix** of a polynomial $p = \sum_k a_k X^k$ over a commutative ring, of size
$n$, with the indices $0, \dots, n - 1$. Its entries are
$$c_{ij} = \begin{cases} -a_{n-1-j} & \text{if } i = 0, \\ 1 & \text{if } i = j + 1, \\ 0 &
  \text{otherwise.} \end{cases}$$
So the first row is $(-a_{n-1}, \dots, -a_0)$, the subdiagonal has ones, and every other entry
is $0$. For $p$ monic of degree $n$, this is the matrix $C$ of (5.72) of
[quarteroni2000numerical], with $a_n = 1$.

The definition does not assume that $p$ is monic or of degree $n$; it uses only the coefficients
$a_0, \dots, a_{n-1}$ of $p$. -/
def companion (p : R[X]) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  of fun i j => if (i : ℕ) = 0 then -p.coeff (n - 1 - j) else if (i : ℕ) = j + 1 then 1 else 0

variable (p : R[X]) {n : ℕ}

/-- The entries of the companion matrix of $p = \sum_k a_k X^k$ of size $n$: the entry $(i, j)$ is
$-a_{n-1-j}$ if $i = 0$, $1$ if $i = j + 1$, and $0$ otherwise. -/
theorem companion_apply (i j : Fin n) :
    companion p n i j
      = if (i : ℕ) = 0 then -p.coeff (n - 1 - j) else if (i : ℕ) = j + 1 then 1 else 0 := rfl

/-- The first row of the companion matrix of $p = \sum_k a_k X^k$ of size $n + 1$ has the negated
coefficients, the highest first: the entry $(0, j)$ is $-a_{n-j}$. -/
theorem companion_zero_apply (j : Fin (n + 1)) : companion p (n + 1) 0 j = -p.coeff (n - j) := by
  simp [companion_apply]

/-- The subdiagonal of the companion matrix of size $n + 1$ has ones: the entry $(i + 1, i)$ is $1$
for every $i < n$. -/
theorem companion_succ_castSucc (i : Fin n) : companion p (n + 1) i.succ i.castSucc = 1 := by
  simp [companion_apply]

/-- Below the first row, the companion matrix of size $n + 1$ is zero off the subdiagonal: the entry
$(i + 1, j)$ is $0$ for $i \neq j$. -/
theorem companion_succ_apply_of_ne {i : Fin n} {j : Fin (n + 1)} (h : (i : ℕ) ≠ j) :
    companion p (n + 1) i.succ j = 0 := by
  simp [companion_apply, h]

/-- Let $p = \sum_k a_k X^k$. If the last row and the last column of the companion matrix of $p$ of
size $n + 1$ are deleted, the result is the companion matrix of size $n$ of the polynomial
$(p - a_0)/X$ (`Polynomial.divX p`). -/
theorem companion_submatrix_castSucc :
    (companion p (n + 1)).submatrix Fin.castSucc Fin.castSucc = companion p.divX n := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [submatrix_apply, companion_apply, Fin.val_castSucc, coeff_divX]
  by_cases h0 : i = 0
  · simp only [h0, ite_true]
    congr 2
    omega
  · simp [h0]

/-- Let $A$ be a square matrix over a commutative ring, and let $f$ be an injective map of index
sets. Then the characteristic matrix $XI - A(f, f)$ of the principal submatrix $A(f, f)$ along
$f$ is the principal submatrix along $f$ of the characteristic matrix $XI - A$.

For an equivalence $f$, this is Mathlib's `Matrix.charmatrix_reindex`. -/
theorem charmatrix_submatrix {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]
    [DecidableEq l] (A : Matrix l l R) {f : m → l} (hf : Function.Injective f) :
    charmatrix (A.submatrix f f) = (charmatrix A).submatrix f f := by
  ext i j
  rw [submatrix_apply, charmatrix_apply, charmatrix_apply, submatrix_apply]
  rcases eq_or_ne i j with rfl | h
  · rw [diagonal_apply_eq, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (hf.ne h)]

/-- The minor of the characteristic matrix of the companion matrix of size $n + 1$ without the first
row and the last column has the entries $-1$ on the diagonal, $X$ just above the diagonal, and
$0$ elsewhere. -/
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

/-- The minor of the characteristic matrix of the companion matrix of size $n + 1$ without the first
row and the last column has the determinant $(-1)^n$, because it is upper triangular. -/
private theorem det_charmatrix_companion_submatrix_succ_castSucc :
    ((charmatrix (companion p (n + 1))).submatrix Fin.succ Fin.castSucc).det = (-1) ^ n := by
  rw [det_of_isUpperTriangular]
  · rw [Finset.prod_congr rfl fun i _ => charmatrix_companion_submatrix_succ_castSucc p i i]
    simp
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    rw [charmatrix_companion_submatrix_succ_castSucc,
      ite_eq_right (fun h : i = j => absurd h (ne_of_gt hji)), ite_eq_right (by omega)]

/-- **The characteristic polynomial of the companion matrix is the polynomial itself**. Let $R$ be a
commutative ring, and let $p \in R[X]$ be monic of degree $n$. Then the companion matrix $C$ of
$p$ of size $n$ satisfies
$$\det(XI - C) = p.$$
This is Exercise 5.8 of [quarteroni2000numerical].

The proof is an induction on $n$, with the expansion of $\det(XI - C)$ along the last column. -/
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
        ← charmatrix_submatrix _ (Fin.castSucc_injective _), companion_submatrix_castSucc,
        ← charpoly, hrec, charmatrix_apply_ne _ _ _ h0l,
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
      rw [charmatrix_apply_ne _ _ _ hil, companion_succ_apply_of_ne _ (by simp; omega), map_zero,
        neg_zero, mul_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
    · exact fun h => absurd (Finset.mem_univ _) h

/-- **The eigenvalues of the companion matrix are the roots of the polynomial**. Let $K$ be a field,
and let $p \in K[X]$ be monic of degree $n$. Then the spectrum of the companion matrix of $p$ of
size $n$ is the set of roots of $p$ in $K$. This is Exercise 5.8 of [quarteroni2000numerical].

The spectrum is Mathlib's `spectrum K`, and the set of roots is `Polynomial.rootSet p K`. -/
theorem spectrum_companion {K : Type*} [Field K] {p : K[X]} (hp : p.Monic) {n : ℕ}
    (hn : p.natDegree = n) : spectrum K (companion p n) = p.rootSet K := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_companion hp hn, mem_rootSet_of_ne hp.ne_zero,
    aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id, IsRoot.def]

end Matrix
