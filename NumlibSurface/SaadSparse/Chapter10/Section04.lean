/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Preconditioner.ILU

/-!
# Saad, Section 10.4: Threshold strategies and ILUT

This module formalizes Sections 10.4.1 and 10.4.2 of [saad2003iterative]: the incomplete
factorization ILUT, whose zero pattern is chosen during the elimination by dropping small entries,
and its existence theorem. An $\hat{M}$ matrix (10.25)–(10.27) has positive diagonal entries except
possibly in the last row, nonpositive off-diagonal entries, and in every row but the last a strictly
negative sum of the entries to the right of the diagonal. Theorem 10.8 states that if $A$ is a
diagonally dominant $\hat{M}$ matrix, then the rows produced by the elimination with dropping keep
the sign pattern of an $\hat{M}$ matrix, have nondecreasing nonnegative row sums and positive
pivots, provided that the entry of largest modulus to the right of the diagonal is never dropped. So
ILUT, with this modification of the drop strategy, never meets a zero pivot. The proofs specialize
`Numlib.Preconditioner.ILU`.

## Main definitions

* Section 10.4.1, `SaadSparse.Chapter10.rowSum`: the row sum $\mathrm{rs}(h_{i,*}) = \sum_j h_{ij}$.

## Main results

* Equations (10.25)–(10.27), `SaadSparse.Chapter10.isMHat_iff`: the conditions of an $\hat{M}$
  matrix, written out.
* Section 10.4.1, `SaadSparse.Chapter10.isDiagDominant_iff`: a diagonally dominant $\hat{M}$ matrix
  is an $\hat{M}$ matrix with nonnegative row sums.
* Theorem 10.8, `SaadSparse.Chapter10.theorem_10_8`: the rows of the elimination with dropping
  satisfy (10.28)–(10.30).

## Conventions

* The matrix has order $n + 1$ and is indexed by `Fin (n + 1)`, from $0$. The book's last row, row
  $n$, is `Fin.last n`, and the book's "row $i$ with $i < n$" is `i ≠ Fin.last n`; the backbone
  states this as `¬ IsMax i`.

## Implementation notes

* An $\hat{M}$ matrix is `Matrix.IsMHat`, and a diagonally dominant $\hat{M}$ matrix is
  `Matrix.IsMHat.IsDiagDominant`. This class is weaker than the M-matrices of Definition 1.30: it
  asks nothing about nonsingularity or about the sign of the inverse.
* Theorem 10.8 is a statement about the rows produced by the elimination with dropping, not about a
  factorization, and it is stated in that form. The working row $u^k$ of (10.23), the pivot rows,
  the multipliers $l_{ik}$ and the dropped rows $r^k$ are arbitrary sequences, and the hypotheses
  describe one elimination step. Algorithm 10.6 is not written down: it would add a selection rule
  based on a heap, and Theorem 10.8 uses none of it.

## Deviations from the source

* **Reading.** The ILUT row invariants use an abstract recurrence with explicit pivot, sign and drop
  hypotheses. See `SaadSparse.Chapter10.theorem_10_8`.

## Not formalized

* **Algorithm 10.6.** Its data structures and selection rule have no mathematical content.
* **Sections 10.4.3–10.4.6** (the implementation of ILUT, the column pivoting of ILUTP, ILUS and
  Crout ILU). They are implementations and dropping heuristics.
-/

open Matrix

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The row sum, and `M̂` matrices (10.25)–(10.27) -/

/-- **Section 10.4.1** of [saad2003iterative]. For $H \in \mathbb{R}^{n \times n}$ and a row index
$i$, the **row sum** of row $i$ is
$$\mathrm{rs}(h_{i,*}) = h_{i,*} e = \sum_j h_{ij},$$
where $e$ is the vector of ones. -/
def rowSum (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, H i j

/-- The row sums of $H$ are the entries of $He$, where $e$ is the vector of ones. -/
theorem rowSum_eq_mulVec_one (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowSum H i = (H *ᵥ (1 : Fin n → ℝ)) i := by
  simp [rowSum, Matrix.mulVec, dotProduct]

/-- On `Fin (n + 1)`, an index is maximal if and only if it is the last index $n$. -/
private theorem isMax_iff_eq_last {i : Fin (n + 1)} : IsMax i ↔ i = Fin.last n := by
  rw [isMax_iff_eq_top, Fin.top_eq_last]

/-- **Equations (10.25)–(10.27)** of [saad2003iterative]. A matrix
$H \in \mathbb{R}^{(n+1) \times (n+1)}$, indexed from $0$ to $n$, is an **$\hat{M}$ matrix** if
and only if

* $h_{ii} > 0$ for $i \neq n$ and $h_{nn} \ge 0$;
* $h_{ij} \le 0$ for $i \neq j$;
* $\sum_{j > i} h_{ij} < 0$ for $i \neq n$.

The last condition says that every row except the last has a nonzero entry to the right of the
diagonal. The definition is `Matrix.IsMHat`. -/
theorem isMHat_iff (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    H.IsMHat ↔
      ((∀ i, i ≠ Fin.last n → 0 < H i i) ∧ 0 ≤ H (Fin.last n) (Fin.last n)) ∧
        (∀ i j, i ≠ j → H i j ≤ 0) ∧
        ∀ i, i ≠ Fin.last n → ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j < 0 := by
  constructor
  · intro h
    refine ⟨⟨fun i hi => h.diag_pos i fun hm => hi (isMax_iff_eq_last.1 hm),
      h.diag_nonneg_of_isMax _ (isMax_iff_eq_last.2 rfl)⟩, h.offDiag_nonpos, fun i hi => ?_⟩
    exact h.sum_gt_neg i fun hm => hi (isMax_iff_eq_last.1 hm)
  · rintro ⟨⟨hpos, hlast⟩, hoff, hgt⟩
    refine ⟨fun i hi => hpos i fun he => hi (isMax_iff_eq_last.2 he), fun i hi => ?_, hoff,
      fun i hi => hgt i fun he => hi (isMax_iff_eq_last.2 he)⟩
    rw [isMax_iff_eq_last.1 hi]
    exact hlast

/-- **Section 10.4.1** of [saad2003iterative]. A matrix $H \in \mathbb{R}^{n \times n}$ is a
**diagonally dominant $\hat{M}$ matrix** if and only if it is an $\hat{M}$ matrix and every row
sum is nonnegative, $\mathrm{rs}(h_{i,*}) \ge 0$ for all $i$. This is the hypothesis of Theorem
10.8. -/
theorem isDiagDominant_iff (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.IsMHat.IsDiagDominant H ↔ H.IsMHat ∧ ∀ i, 0 ≤ rowSum H i :=
  ⟨fun h => ⟨h.toIsMHat, h.rowSum_nonneg⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### Theorem 10.8, the existence result for `ILUT` -/

/-- **Theorem 10.8** of [saad2003iterative]. Let $A \in \mathbb{R}^{(n+1) \times (n+1)}$, indexed
from $0$ to $n$, be a diagonally dominant $\hat{M}$ matrix, and fix a row index $i$. Let
$u^k, w^k, r^k \in \mathbb{R}^{n+1}$, $l_k \in \mathbb{R}$ and $p_k \in \{0, \dots, n\}$ for
$k \in \mathbb{N}$, and assume:

* $u^0 = 0$ and $u^1 = a_{i,*}$;
* $u^{k+1} = u^k - l_k w^k - r^k$ for $k \ge 1$, as in (10.23);
* for $k \ge 1$, the pivot row $w^k$ satisfies $w^k_j \le 0$ for $j \neq p_k$ and
  $\sum_j w^k_j \ge 0$, and its pivot index satisfies $p_k < i$;
* for $k \ge 1$, the multiplier satisfies $l_k \le 0$ and $l_k w^k_{p_k} = u^k_{p_k}$;
* for $k \ge 1$ and every $j$, either $r^k_j = 0$ or $r^k_j = u^k_j - l_k w^k_j$, and
  $r^k_i = 0$;
* if $i \neq n$, then for every $k \ge 1$ there is a $j_0 > i$ with $r^k_{j_0} = 0$ and
  $u^k_{j_0} - l_k w^k_{j_0} \le u^k_j - l_k w^k_j$ for all $j > i$.

Then for every $k \ge 1$:

* (10.28) $u^k_j \le 0$ for $j \neq i$;
* (10.29) $0 \le \mathrm{rs}(u^{k-1}) \le \mathrm{rs}(u^k)$;
* (10.30) $u^k_i > 0$ if $i \neq n$, and $u^k_i \ge 0$ in every case.

So the threshold factorization ILUT, run with the modification of the drop strategy of Section
10.4.2, never meets a zero pivot.

The hypotheses describe the elimination step. The pivot row $w^k = u_{p_k,*}$ has the sign
pattern and the nonnegative row sum of an $\hat{M}$ matrix, and its pivot index lies strictly to
the left of $i$. The multiplier is nonpositive and eliminates the pivot entry. Each entry is
either kept whole or dropped whole, and the diagonal entry is never dropped. The last hypothesis
is the modification of Section 10.4.2: some position $j_0$ to the right of the diagonal at which
the computed value is smallest, that is, of largest modulus, is never dropped. This hypothesis
is available only away from the last row, where there is no position to the right of the
diagonal, and (10.27) is vacuous there for the same reason; that is why the last row gets only
$u^k_n \ge 0$.

**Reading.** The finite ILUT inner loop is represented by an abstract row recurrence with explicit
pivot cancellation, sign and row-sum hypotheses at every positive index. The retained most-negative
entry can be chosen anew at each step, while the printed drop modification protects a fixed position
from the original row. The statement proves the row invariants and does not construct the
factorization or the drop rule.
-/
theorem theorem_10_8 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsMHat.IsDiagDominant A) (i : Fin (n + 1))
    (u w : ℕ → Fin (n + 1) → ℝ) (l : ℕ → ℝ) (r : ℕ → Fin (n + 1) → ℝ) (p : ℕ → Fin (n + 1))
    (hu0 : u 0 = 0) (hu1 : u 1 = A i)
    (hrec : ∀ k, 1 ≤ k → u (k + 1) = u k - l k • w k - r k)
    (hw : ∀ k, 1 ≤ k → ∀ j, j ≠ p k → w k j ≤ 0) (hwsum : ∀ k, 1 ≤ k → 0 ≤ ∑ j, w k j)
    (hl : ∀ k, 1 ≤ k → l k ≤ 0) (hp : ∀ k, 1 ≤ k → p k < i)
    (hpivot : ∀ k, 1 ≤ k → l k * w k (p k) = u k (p k))
    (hdrop : ∀ k, 1 ≤ k → ∀ j, r k j = 0 ∨ r k j = u k j - l k * w k j)
    (hdropDiag : ∀ k, 1 ≤ k → r k i = 0)
    (hkeep : i ≠ Fin.last n → ∀ k, 1 ≤ k → ∃ j₀, i < j₀ ∧ r k j₀ = 0 ∧
      ∀ j, i < j → u k j₀ - l k * w k j₀ ≤ u k j - l k * w k j)
    {k : ℕ} (hk : 1 ≤ k) :
    (∀ j, j ≠ i → u k j ≤ 0) ∧
      (0 ≤ ∑ j, u (k - 1) j ∧ ∑ j, u (k - 1) j ≤ ∑ j, u k j) ∧
      (i ≠ Fin.last n → 0 < u k i) ∧ 0 ≤ u k i := by
  -- shift the index by one, so that the book's `u^1 = a_{i,*}` is the backbone's `u 0 = A i`
  set u' : ℕ → Fin (n + 1) → ℝ := fun m => u (m + 1)
  have hu0' : u' 0 = A i := hu1
  have hrec' : ∀ m, u' (m + 1) = u' m - l (m + 1) • w (m + 1) - r (m + 1) :=
    fun m => hrec (m + 1) (Nat.le_add_left 1 m)
  have hw' : ∀ m j, j ≠ p (m + 1) → w (m + 1) j ≤ 0 := fun m => hw (m + 1) (Nat.le_add_left 1 m)
  have hwsum' : ∀ m, 0 ≤ ∑ j, w (m + 1) j := fun m => hwsum (m + 1) (Nat.le_add_left 1 m)
  have hl' : ∀ m, l (m + 1) ≤ 0 := fun m => hl (m + 1) (Nat.le_add_left 1 m)
  have hpivot' : ∀ m, l (m + 1) * w (m + 1) (p (m + 1)) = u' m (p (m + 1)) :=
    fun m => hpivot (m + 1) (Nat.le_add_left 1 m)
  have hdrop' : ∀ m j, r (m + 1) j = 0 ∨ r (m + 1) j = u' m j - l (m + 1) * w (m + 1) j :=
    fun m => hdrop (m + 1) (Nat.le_add_left 1 m)
  have hdropDiag' : ∀ m, r (m + 1) i = 0 := fun m => hdropDiag (m + 1) (Nat.le_add_left 1 m)
  have hnonpos : ∀ m, (∀ j, j ≠ i → u' m j ≤ 0) ∧ 0 ≤ ∑ j, u' m j ∧
      ∑ j, u' m j ≤ ∑ j, u' (m + 1) j := fun m =>
    Matrix.IsMHat.ilut_rows_nonpos hA i u' (fun m => w (m + 1)) (fun m => l (m + 1))
      (fun m => r (m + 1)) (fun m => p (m + 1)) hu0' hrec' hw' hwsum' hl' hpivot' hdrop'
      hdropDiag' m
  have hdiag : ∀ m, 0 ≤ u' m i := fun m =>
    Matrix.IsMHat.ilut_rows_diag_nonneg hA i u' (fun m => w (m + 1)) (fun m => l (m + 1))
      (fun m => r (m + 1)) (fun m => p (m + 1)) hu0' hrec' hw' hwsum' hl' hpivot' hdrop'
      hdropDiag' m
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  refine ⟨(hnonpos m).1, ⟨?_, ?_⟩, fun hi => ?_, hdiag m⟩
  · rcases m with - | m
    · simp [hu0]
    · exact (hnonpos m).2.1
  · rcases m with - | m
    · simpa [hu0] using (hnonpos 0).2.1
    · exact (hnonpos m).2.2
  · have hmax : ¬ IsMax i := fun hm => hi (isMax_iff_eq_last.1 hm)
    exact (Matrix.IsMHat.ilut_rows hA hmax u' (fun m => w (m + 1)) (fun m => l (m + 1))
      (fun m => r (m + 1)) (fun m => p (m + 1)) hu0' hrec' hw' hwsum' hl'
      (fun m => hp (m + 1) (Nat.le_add_left 1 m)) hpivot' hdrop' hdropDiag'
      (fun m => hkeep hi (m + 1) (Nat.le_add_left 1 m)) m).2.2.2

end SaadSparse.Chapter10
