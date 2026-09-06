import Numlib.LinearSolve.Preconditioner.ILU

/-!
# Saad §10.4: threshold strategies and `ILUT`

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §10.4.1–10.4.2: the incomplete factorization whose zero pattern is chosen dynamically, by
dropping the entries that are small, and its existence theorem.

Only Theorem 10.8 has mathematical content in this section. §10.4.3–10.4.6 — the data structures of
Algorithm 10.6, the column pivoting of `ILUTP`, `ILUS` and Crout `ILU` — are implementations and
dropping heuristics, and get no declarations.

Theorem 10.8 is a statement about the *rows* produced by the elimination with dropping, not about a
factorization, and it is stated that way: the working row `u^k` of (10.23), the pivot rows `u_{k,*}`
used at each step, the multipliers `l_{ik}`, the dropped rows `r^k`, and — as a hypothesis — the
drop-strategy modification of §10.4.2, that the entry of largest modulus to the right of the
diagonal is never dropped. Writing Algorithm 10.6 down instead would add a heap-based selection rule
with no mathematical content, and Theorem 10.8 uses none of it.

Saad's `M̂` matrix (10.25)–(10.27) is `Matrix.IsMHat` of
`Numlib/LinearSolve/Preconditioner/ILU.lean`, and his "diagonally dominant `M̂` matrix" is
`Matrix.IsMHat.IsDiagDominant`. It is genuinely weaker than his M-matrix of Definition 1.30: nothing
is assumed about nonsingularity or about the sign of the inverse. The book's "row `i` with `i < n`"
is `i ≠ Fin.last n`, and the backbone states it order-theoretically as `¬ IsMax i`.
-/

open Matrix

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The row sum, and `M̂` matrices (10.25)–(10.27) -/

/-- **Saad's `rs`**: the row sum `rs(h_{i,*}) = h_{i,*} e = ∑_j h_{ij}` of the `i`-th row. -/
def rowSum (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, H i j

/-- The row sums are the entries of `H e`, for `e` the vector of ones. -/
theorem rowSum_eq_mulVec_one (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowSum H i = (H *ᵥ (1 : Fin n → ℝ)) i := by
  simp [rowSum, Matrix.mulVec, dotProduct]

/-- `IsMax` on `Fin (n + 1)` is being the last index, which is the book's `i = n`. -/
private theorem isMax_iff_eq_last {i : Fin (n + 1)} : IsMax i ↔ i = Fin.last n := by
  rw [isMax_iff_eq_top, Fin.top_eq_last]

/-- **Saad's `M̂` matrix**, (10.25)–(10.27) written out: the diagonal entries are positive except in
the last row, where only nonnegativity is asked; the off-diagonal entries are nonpositive; and in
every row but the last, the entries strictly to the right of the diagonal sum to a strictly negative
number — so each such row has a nonzero entry to the right of its diagonal. -/
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

/-- **Saad's diagonally dominant `M̂` matrix** (§10.4.1): an `M̂` matrix every one of whose rows has
a nonnegative row sum. This is the hypothesis of Theorem 10.8. -/
theorem isDiagDominant_iff (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.IsMHat.IsDiagDominant H ↔ H.IsMHat ∧ ∀ i, 0 ≤ rowSum H i :=
  ⟨fun h => ⟨h.toIsMHat, h.rowSum_nonneg⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### Theorem 10.8, the existence result for `ILUT` -/

/-- **Saad Theorem 10.8**: if `A` is a diagonally dominant `M̂` matrix, then the rows `u^k` of
(10.23) — starting from `u^0 = 0` and `u^1 = a_{i,*}`, and updated by
`u^{k+1} = u^k - l_{ik} u_{k,*} - r^k` — satisfy, for every `k ≥ 1`:

* (10.28) `u^k_j ≤ 0` for `j ≠ i`;
* (10.29) `rs(u^k) ≥ rs(u^{k-1}) ≥ 0`;
* (10.30) `u^k_i > 0` when `i ≠ n`, and `u^k_n ≥ 0` in the last row.

So the threshold factorization `ILUT`, run with the drop-strategy modification of §10.4.2, never
meets a zero pivot.

The hypotheses transcribe the elimination step: the pivot row `w k = u_{p k, *}` has the sign
pattern and the nonnegative row sum of an `M̂` matrix, and its pivot index `p k` lies strictly to
the left of `i`; the multiplier `l k` is nonpositive and annihilates the pivot entry; each entry
is either kept whole or dropped whole (`hdrop`), the diagonal entry is never dropped, and — the
modification of §10.4.2 — some position `j₀` strictly to the right of the diagonal, at which the
computed value is smallest, is never dropped either. That last hypothesis is available only away
from the last row, where there is no position to the right of the diagonal, and (10.27) is vacuous
there for the same reason; that is why the last row keeps only `0 ≤ u^k_n`. -/
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
