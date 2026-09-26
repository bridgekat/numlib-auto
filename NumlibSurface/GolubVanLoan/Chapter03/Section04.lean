import NumlibSurface.GolubVanLoan.Chapter03.Section03

/-!
# Golub–Van Loan §3.4: pivoting

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.4:
interchange permutations and the `piv` encoding (§3.4.1), partial pivoting ((3.4.1)–(3.4.3)) and
the outer product LU with partial pivoting, Algorithm 3.4.1, with its rounding bridge and the
solve that follows it; the backward error (3.4.6).

## Design

A row permutation `σ` acts as `A.submatrix σ id = σ.permMatrix ℝ * A`; the book's
`P = Π_{n-1} ⋯ Π_1` encoded by `piv` is `(pivPerm piv).permMatrix ℝ`, with
`pivPerm piv = swap 0 (piv 0) * ⋯ * swap (n-1) (piv (n-1))` (`Matrix.permMatrix_mul` reverses the
order). The `piv` vector has `n` entries; the book's last step `k = n` is a trivial interchange.

The pivot search of Algorithm 3.4.1 is the backbone's `Matrix.partialPivotRow`, the first row at
or below `k` maximizing `|a_ik|`: it compares exact absolute values of the entries the program
holds (convention 1: `|·|` and comparisons are exact), so it is a pure step of the program. The
book's guard `if A(k,k) ≠ 0` is kept.

The rounding bridge `algorithm_3_4_1_rounds` follows the invariant of Algorithm 3.2.1
(`GolubVanLoan.Chapter03.LUStageInv`) for the matrix with its rows permuted by the interchanges so
far: an interchange at step `k` permutes rows at or after `k` only, which moves the finished
multipliers of those rows and their trailing entries together (`luStageInv_submatrix`). The guard
is taken whenever the returned pivot is nonzero, which the bridge assumes (convention 9); in the
exact model a zero pivot comes with a zero column, and the skipped update is then an update, so
the exact specification holds for every `A` and is read off the same invariant.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Interchange permutations and the `piv` encoding (§3.4.1) -/

section Piv

variable {n : ℕ}

/-- §3.4.1, the interchange permutation `Π`: the identity with rows `k` and `l` swapped.
`Π A` is `A` with rows `k`, `l` interchanged and `A Π` is `A` with columns `k`, `l` swapped. -/
noncomputable def interchange (k l : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (Equiv.swap k l).permMatrix ℝ

/-- The permutation of the first `k` interchanges encoded by `piv`: `swap 0 (piv 0) * ⋯ *
swap (k-1) (piv (k-1))`. -/
def pivPermUpTo (piv : Fin n → Fin n) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | k + 1 =>
    if h : k < n then pivPermUpTo piv k * Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else pivPermUpTo piv k

/-- §3.4.1, "if `P = Π_m ⋯ Π_1` and each `Π_k` is the identity with rows `k` and `piv(k)`
interchanged, then `piv(1:m)` encodes `P`": `(pivPerm piv).permMatrix ℝ = Π_n ⋯ Π_1`. -/
def pivPerm (piv : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  pivPermUpTo piv n

/-- The permutation of the first `k` interchanges depends only on the first `k` entries of `piv`.
-/
theorem pivPermUpTo_congr {piv piv' : Fin n → Fin n} {k : ℕ}
    (h : ∀ j : Fin n, (j : ℕ) < k → piv j = piv' j) : pivPermUpTo piv k = pivPermUpTo piv' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pivPermUpTo]
    split_ifs with hk
    · rw [ih fun j hj => h j (by omega), h ⟨k, hk⟩ (by simp)]
    · exact ih fun j hj => h j (by omega)

/-- One more interchange. -/
theorem pivPermUpTo_succ {piv : Fin n → Fin n} (k : Fin n) :
    pivPermUpTo piv (k + 1) = pivPermUpTo piv k * Equiv.swap k (piv k) := by
  simp [pivPermUpTo, k.2]

/-- §3.4.1, the loop "`for k = 1:m, x(k) ↔ x(piv(k))`", which overwrites `x` with `P x`. -/
def applyPiv (piv : Fin n → Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  (List.finRange n).foldl (fun x k => x ∘ Equiv.swap k (piv k)) x

/-- §3.4.1, the loop "`for k = m:-1:1, x(k) ↔ x(piv(k))`", which overwrites `x` with `Pᵀ x`. -/
def applyPivRev (piv : Fin n → Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  (List.finRange n).reverse.foldl (fun x k => x ∘ Equiv.swap k (piv k)) x

/-- A fold over `List.finRange n` is a fold over `List.range n`. -/
theorem foldl_finRange_eq_foldl_range {β : Type*} (f : β → Fin n → β) (b : β) :
    (List.finRange n).foldl f b =
      (List.range n).foldl (fun b k => if h : k < n then f b ⟨k, h⟩ else b) b := by
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext b k
  simp [k.2]

/-- A right fold over `List.finRange n` is a right fold over `List.range n`. -/
theorem foldr_finRange_eq_foldr_range {β : Type*} (f : Fin n → β → β) (b : β) :
    (List.finRange n).foldr f b =
      (List.range n).foldr (fun k b => if h : k < n then f ⟨k, h⟩ b else b) b := by
  rw [← List.map_coe_finRange_eq_range, List.foldr_map]
  congr 1
  funext k b
  simp [k.2]

/-- **§3.4.1**: the forward loop overwrites `x` with `P x`, and — each `Π_k` being symmetric — the
reverse loop overwrites `x` with `Pᵀ x = Π_1 ⋯ Π_m x`. -/
theorem applyPiv_eq (piv : Fin n → Fin n) (x : Fin n → ℝ) :
    applyPiv piv x = (pivPerm piv).permMatrix ℝ *ᵥ x ∧
      applyPivRev piv x = ((pivPerm piv).permMatrix ℝ)ᵀ *ᵥ x := by
  have hfwd : ∀ k ≤ n, ∀ y : Fin n → ℝ, (List.range k).foldl
      (fun y k => if h : k < n then y ∘ Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else y) y =
      y ∘ pivPermUpTo piv k := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      simp only [show k < n by omega, ↓reduceDIte, pivPermUpTo, Equiv.Perm.coe_mul]
      rfl
  have hrev : ∀ k ≤ n, ∀ y : Fin n → ℝ, (List.range k).foldr
      (fun k y => if h : k < n then y ∘ Equiv.swap ⟨k, h⟩ (piv ⟨k, h⟩) else y) y =
      y ∘ ⇑(pivPermUpTo piv k)⁻¹ := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih (by omega)]
      simp only [show k < n by omega, ↓reduceDIte, pivPermUpTo, _root_.mul_inv_rev,
        Equiv.swap_inv, Equiv.Perm.coe_mul]
      rfl
  refine ⟨?_, ?_⟩
  · rw [applyPiv, foldl_finRange_eq_foldl_range, hfwd n le_rfl, permMatrix_mulVec]
    rfl
  · rw [applyPivRev, List.foldl_reverse, foldr_finRange_eq_foldr_range, hrev n le_rfl,
      mulVec_transpose, vecMul_permMatrix]
    rfl

end Piv

/-! ### Partial pivoting (§3.4.2–3.4.3) -/

section Partial

variable {n : ℕ}

/-- (3.4.1), partial pivoting as a sequence of matrices: after `k` steps, the book's
`M_k Π_k ⋯ M_1 Π_1 A` is the backbone's pivoted stage
`(Matrix.gemPivotStage A Matrix.partialPivotRow k).1`. -/
noncomputable abbrev partialPivotStage (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (gemPivotStage A partialPivotRow k).1

/-- **(3.4.1)–(3.4.2)**: each step of partial pivoting is `A ← M_k Π_k A`, with `Π_k` the
interchange of `k` and the row of the largest `|a_ik|`, `i ≥ k`, and `M_k` the Gauss transformation
of the interchanged matrix; after the last step, `M_{n-1} Π_{n-1} ⋯ M_1 Π_1 A = U` is upper
triangular — for every `A` (a zero pivot comes with a zero column, and then `M_k = I`). -/
theorem equation_3_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ k : Fin n, partialPivotStage A (k + 1) =
      gaussTransformation (gaussVector
          (fun i => (interchange k (partialPivotRow (partialPivotStage A k) k) *
            partialPivotStage A k) i k) k) k *
        (interchange k (partialPivotRow (partialPivotStage A k) k) * partialPivotStage A k)) ∧
      (partialPivotStage A n).IsUpperTriangular := by
  refine ⟨fun k => ?_, (gemPivotStage_partialPivotRow_permMatrix_mul_isLU A).isUpperTriangular⟩
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact gemPivotStage_succ_fst_eq_gaussTransform_mul A partialPivotRow k.2

/-- **(3.4.3)**: partial pivoting computes `P A = L U` with `P = Π_{n-1} ⋯ Π_1`, `U` upper
triangular and `L` unit lower triangular with `|ℓ_ij| ≤ 1` — for every `A`. -/
theorem equation_3_4_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A)
        (gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A))
        (partialPivotStage A n) ∧
      ∀ i j, |gemLower ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) i j| ≤ 1 :=
  ⟨gemPivotStage_partialPivotRow_permMatrix_mul_isLU A,
    fun i j => gemPivotStage_partialPivotRow_norm_gemLower_le_one A i j⟩

end Partial

/-! ### The invariant of elimination under row interchanges -/

section Invariant

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- A finished multiplier of partial pivoting: a lower entry of the Doolittle recurrence whose
running difference `t` is dominated by its pivot, `|t| ≤ |u_jj|`. -/
def LULowerEntryDom (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ) (t : ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) t ∧ |t| ≤ |S j j| ∧
    fp.Rounds (t / S j j) (S i j)

/-- The invariant of elimination with partial pivoting after `k` steps: the invariant of Algorithm
3.2.1 with dominated multipliers. -/
def PivStageInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  LUStageInv fp A k S ∧ ∀ i j : Fin n, (j : ℕ) < k → j < i → LULowerEntryDom fp A S i j

/-- **Interchanging rows at or after `k`** keeps the invariant after `k` steps, for the matrix with
the same rows interchanged: the finished rows do not move, and a row at or after `k` carries its
multipliers and its trailing entries along. -/
theorem pivStageInv_submatrix {A S : Matrix (Fin n) (Fin n) ℝ} {k : ℕ} {τ : Equiv.Perm (Fin n)}
    (hfix : ∀ r : Fin n, (r : ℕ) < k → τ r = r) (hmap : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (τ i : ℕ))
    (h : PivStageInv fp A k S) :
    PivStageInv fp (A.submatrix τ id) k (S.submatrix τ id) := by
  obtain ⟨hS, hD⟩ := h
  -- the row `τ i` sits above column `j < k` exactly when `i` does
  have hlt : ∀ (i j : Fin n), (j : ℕ) < k → j < i → j < τ i := fun i j hj hji => by
    by_cases hi : (i : ℕ) < k
    · rw [hfix i hi]; exact hji
    · exact Fin.lt_def.2 (lt_of_lt_of_le hj (hmap i (not_lt.1 hi)))
  refine ⟨fun i j => ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩,
    fun i j hj hji => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 hi hij
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix i hi, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix i hi]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS (τ i) j).2.1 hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix j hj]
      exact hx
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS (τ i) j).2.2 (hmap i hi) hj
    refine ⟨o, p, hnd, ho, fun r hr => ?_, hsum⟩
    simp only [submatrix_apply, id, hfix r ((ho r).1 hr)]
    exact hp r hr
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hdom, hx⟩ := hD (τ i) j hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, id, hfix r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, id, hfix j hj]
      exact hdom
    · simp only [submatrix_apply, id, hfix j hj]
      exact hx

/-- **One elimination step** keeps the invariant, when the pivot dominates its column below and
every entry of the step is rounded as in `mem_run_outerProductStep`. -/
theorem pivStageInv_step {A S S' : Matrix (Fin n) (Fin n) ℝ} (k : Fin n)
    (hS : PivStageInv fp A k S) (hdom : ∀ i : Fin n, k ≤ i → |S i k| ≤ |S k k|)
    (hunch : ∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j)
    (hdiv : ∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k))
    (hupd : ∀ i j, k < i → k < j →
      ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j)) :
    PivStageInv fp A (k + 1) S' := by
  obtain ⟨hS₁, hS₂⟩ := hS
  refine ⟨luStageInv_step A k hS₁ hunch hdiv hupd, fun i j hj hji => ?_⟩
  have hrow : ∀ i j : Fin n, (i : ℕ) ≤ k → S' i j = S i j := fun i j hi =>
    hunch i j fun h => absurd (Fin.lt_def.1 h.1) (not_lt.2 hi)
  have hcol : ∀ i j : Fin n, (j : ℕ) < k → S' i j = S i j := fun i j hj =>
    hunch i j fun h => h.2.elim (fun h' => absurd (h' ▸ hj) (lt_irrefl _))
      fun h' => absurd (Fin.lt_def.1 h') (not_lt.2 hj.le)
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hd, hx⟩ := hS₂ i j hj hji
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_, ?_⟩
    · have hrj := Fin.lt_def.1 ((ho r).1 hr)
      rw [hcol i r (by omega), hcol r j hj]
      exact hp r hr
    · rw [hcol j j hj]
      exact hd
    · rw [hcol i j hj, hcol j j hj]
      exact hx
  · have hjk : j = k := Fin.ext hj
    subst hjk
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS₁ i j).2.2 (Fin.le_def.1 hji.le) le_rfl
    refine ⟨o, p, S i j, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, hsum, ?_,
      ?_⟩
    · have hrj := (ho r).1 hr
      rw [hcol i r hrj, hrow r j hrj.le]
      exact hp r hr
    · rw [hrow j j le_rfl]
      exact hdom i hji.le
    · rw [hrow j j le_rfl]
      exact hdiv i hji

/-- A zero pivot whose column vanishes below it, in a model that rounds every value to itself
(the exact model): the skipped update is an update. -/
theorem pivStageInv_step_of_zero {A S : Matrix (Fin n) (Fin n) ℝ} (k : Fin n)
    (hS : PivStageInv fp A k S) (hdom : ∀ i : Fin n, k ≤ i → |S i k| ≤ |S k k|)
    (hzero : S k k = 0) (hrefl : (∀ x, fp.Rounds x x) ∨ ¬ (k : ℕ) + 1 < n) :
    PivStageInv fp A (k + 1) S := by
  have hcol : ∀ i : Fin n, k ≤ i → S i k = 0 := fun i hi => by
    have := hdom i hi
    rw [hzero, abs_zero] at this
    exact abs_nonpos_iff.1 this
  refine pivStageInv_step k hS hdom (fun _ _ _ => rfl) (fun i hi => ?_) (fun i j hi _ => ?_)
  · rcases hrefl with hrefl | hrefl
    · rw [hcol i hi.le, hzero, zero_div]
      exact hrefl 0
    · exact absurd (by have := Fin.lt_def.1 hi; omega) hrefl
  · rcases hrefl with hrefl | hrefl
    · refine ⟨S i k * S k j, hrefl _, ?_⟩
      rw [hcol i hi.le, zero_mul, sub_zero]
      exact hrefl _
    · exact absurd (by have := Fin.lt_def.1 hi; omega) hrefl

end Invariant

/-! ### Algorithm 3.4.1 (Outer Product LU with Partial Pivoting) -/

section Algorithm341

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.4.1 (Outer Product LU with Partial Pivoting).** "This algorithm computes the
factorization `PA = LU` where `P` is a permutation matrix encoded by `piv(1:n-1)`, `L` is unit
lower triangular with `|ℓ_ij| ≤ 1`, and `U` is upper triangular. For `i = 1:n`, `A(i,i:n)` is
overwritten by `U(i,i:n)` and `A(i+1:n,i)` is overwritten by `L(i+1:n,i)`."
```
for k = 1:n-1
    Determine μ with k ≤ μ ≤ n so |A(μ,k)| = ‖A(k:n,k)‖_∞
    piv(k) = μ
    A(k,:) ↔ A(μ,:)
    if A(k,k) ≠ 0
        ρ = k+1:n
        A(ρ,k) = A(ρ,k)/A(k,k)
        A(ρ,ρ) = A(ρ,ρ) - A(ρ,k) A(k,ρ)
    end
end
```
The search is `Matrix.partialPivotRow` (the first maximizing row, exact comparisons); the updates
are `outerProductStep` (Algorithm 3.2.1's step). The state is `(A, piv)`, `piv` initially the
identity; the last step `k = n` is a trivial interchange with empty updates. -/
noncomputable def algorithm_3_4_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) k =>
    if st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id k k ≠ 0 then do
      let A ← outerProductStep rnd k (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id)
      pure (A, Function.update st.2 k (partialPivotRow st.1 k))
    else
      pure (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id,
        Function.update st.2 k (partialPivotRow st.1 k))) (A, fun k => k)

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- The invariant of Algorithm 3.4.1 after `k` steps: the invariant of elimination for `A` with
its rows permuted by the first `k` interchanges, or — only in a model that does not round every
value to itself — a zero pivot already returned. -/
def Alg341Inv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) : Prop :=
  PivStageInv fp (A.submatrix (pivPermUpTo st.2 k) id) k st.1 ∨
    ((∃ j : Fin n, (j : ℕ) < k ∧ (j : ℕ) + 1 < n ∧ st.1 j j = 0) ∧ ¬ ∀ x, fp.Rounds x x)

/-- One step of Algorithm 3.4.1 keeps its invariant. -/
theorem alg341Inv_step (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) (hst : Alg341Inv fp A k st)
    (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n))
    (hst' : st' ∈ (if st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id k k ≠ 0 then do
      let A ← outerProductStep fp.round k
        (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id)
      pure (A, Function.update st.2 k (partialPivotRow st.1 k))
    else
      pure (st.1.submatrix (Equiv.swap k (partialPivotRow st.1 k)) id,
        Function.update st.2 k (partialPivotRow st.1 k)) : SetM _).run) :
    Alg341Inv fp A (k + 1) st' := by
  obtain ⟨S, piv⟩ := st
  dsimp only at hst hst'
  set μ := partialPivotRow S k with hμ
  set S₀ := S.submatrix (Equiv.swap k μ) id with hS₀
  have hkμ : k ≤ μ := le_partialPivotRow S k
  have hfix : ∀ r : Fin n, (r : ℕ) < k → Equiv.swap k μ r = r := fun r hr =>
    Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hr; exact lt_irrefl _ hr)
      fun h => by rw [h] at hr; exact absurd (Fin.le_def.1 hkμ) (not_le.2 hr)
  have hmap : ∀ i : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ (Equiv.swap k μ i : ℕ) := fun i hi => by
    rcases eq_or_ne i k with rfl | hik
    · rw [Equiv.swap_apply_left]; exact hkμ
    rcases eq_or_ne i μ with rfl | hiμ
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hik hiμ]; exact hi
  -- the permutation after the step
  have hperm : pivPermUpTo (Function.update piv k μ) (k + 1) =
      pivPermUpTo piv k * Equiv.swap k μ := by
    rw [pivPermUpTo_succ, Function.update_self,
      pivPermUpTo_congr (piv := Function.update piv k μ) (piv' := piv) (k := k)
        fun j hj => Function.update_of_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj) _ _]
  have hsub : (A.submatrix (pivPermUpTo piv k) id).submatrix (Equiv.swap k μ) id =
      A.submatrix (pivPermUpTo (Function.update piv k μ) (k + 1)) id := by
    rw [hperm, submatrix_submatrix, Equiv.Perm.coe_mul]
    rfl
  -- the interchanged pivot dominates its column
  have hdom : ∀ i : Fin n, k ≤ i → |S₀ i k| ≤ |S₀ k k| := fun i hi => by
    simp only [hS₀, submatrix_apply, id, Equiv.swap_apply_left]
    have := norm_apply_le_partialPivotRow S k (r := Equiv.swap k μ i)
      (Fin.le_def.2 (hmap i (Fin.le_def.1 hi)))
    simpa only [Real.norm_eq_abs] using this
  -- rows before `k` are not touched
  have hrows : ∀ S' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S₀ i j) →
      ∀ j : Fin n, (j : ℕ) < k → S' j j = S j j := fun S' hS' j hj => by
    rw [hS' j j fun h => absurd (Fin.lt_def.1 h.1) (by omega), hS₀, submatrix_apply, id,
      hfix j hj]
  rcases hst with hgood | ⟨⟨j, hj, hjn, hj0⟩, hnrefl⟩
  · have hgood₀ : PivStageInv fp (A.submatrix (pivPermUpTo (Function.update piv k μ) (k + 1)) id)
        k S₀ := hsub ▸ pivStageInv_submatrix hfix hmap hgood
    split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨S', hS', hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
      exact Or.inl (pivStageInv_step k hgood₀ hdom h₁ h₂ h₃)
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      have h0' : S₀ k k = 0 := not_not.1 h0
      by_cases hc : (∀ x, fp.Rounds x x) ∨ ¬ (k : ℕ) + 1 < n
      · exact Or.inl (pivStageInv_step_of_zero k hgood₀ hdom h0' hc)
      · obtain ⟨hc₁, hc₂⟩ := not_or.1 hc
        exact Or.inr ⟨⟨k, by simp, not_not.1 hc₂, h0'⟩, hc₁⟩
  · refine Or.inr ⟨⟨j, by omega, hjn, ?_⟩, hnrefl⟩
    split_ifs at hst' with h0
    · rw [SetM.mem_run_bind] at hst'
      obtain ⟨S', hS', hst'⟩ := hst'
      rw [SetM.mem_run_pure] at hst'
      subst hst'
      change S' j j = 0
      rw [hrows S' (mem_run_outerProductStep k hS').1 j hj]
      exact hj0
    · rw [SetM.mem_run_pure] at hst'
      subst hst'
      change S₀ j j = 0
      rw [hrows S₀ (fun _ _ _ => rfl) j hj]
      exact hj0

/-- The invariant after all steps. -/
theorem alg341Inv_of_mem_run (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, Alg341Inv fp A n out :=
  SetM.forall_mem_run_foldlM_finRange (Alg341Inv fp A)
    (Or.inl ⟨luStageInv_zero _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun k st hst st' hst' => alg341Inv_step A k st hst st' hst'

/-- A dominated multiplier is at most `1 + u` in absolute value. -/
theorem abs_le_one_add_of_lowerEntryDom {A S : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}
    (h : LULowerEntryDom fp A S i j) : |S i j| ≤ 1 + fp.u := by
  obtain ⟨-, -, t, -, -, -, -, hd, hx⟩ := h
  have h1 : |t / S j j| ≤ 1 := abs_div_le_one_of_abs_le hd
  have h2 := fp.abs_sub_le hx
  have h3 : |S i j| ≤ |S i j - t / S j j| + |t / S j j| := by
    simpa using abs_add_le (S i j - t / S j j) (t / S j j)
  nlinarith [fp.u_nonneg, abs_nonneg (t / S j j)]

/-- **The bridge of Algorithm 3.4.1**: every run `(F, piv)` whose returned pivots `F j j`,
`j + 1 < n`, are nonzero is an admissible computed LU factorization of the permuted matrix `P A`,
`FloatingPoint.RoundsLU fp (P A) L̂ Û` with `L̂ = packedL F`, `Û = packedU F`, and its computed
multipliers are at most `1 + u` in absolute value ([higham2002accuracy] §9.3: the computed factors
of partial pivoting are the computed factors of elimination without pivoting on `P A`). The
relational model bounds a rounded quotient of modulus at most one by `1 + u`, not `1`. -/
theorem algorithm_3_4_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → out.1 j j ≠ 0) →
      RoundsLU fp (A.submatrix (pivPerm out.2) id) (packedL out.1) (packedU out.1) ∧
        ∀ i j, |packedL out.1 i j| ≤ 1 + fp.u := by
  intro out hout hpiv
  rcases alg341Inv_of_mem_run A out hout with ⟨hS, hD⟩ | ⟨⟨j, -, hjn, hj0⟩, -⟩
  · refine ⟨roundsLU_of_luStageInv hS, fun i j => ?_⟩
    rcases lt_trichotomy j i with hji | rfl | hij
    · rw [packedL_apply_of_lt _ hji]
      exact abs_le_one_add_of_lowerEntryDom (hD i j j.2 hji)
    · rw [packedL_apply_self, abs_one]
      linarith [fp.u_nonneg]
    · rw [packedL_apply_of_lt' _ hij, abs_zero]
      linarith [fp.u_nonneg]
  · exact absurd hj0 (hpiv j hjn)

/-- Over a total model the run set of Algorithm 3.4.1 is nonempty, so its bridge and the bounds
built on it are not vacuous: every step is binds of `fp.round` and `pure`. -/
theorem algorithm_3_4_1_run_nonempty (hfp : fp.IsTotal) (A : Matrix (Fin n) (Fin n) ℝ) :
    (algorithm_3_4_1 fp.round A).run.Nonempty := by
  have hstep : ∀ (k : Fin n) (B : Matrix (Fin n) (Fin n) ℝ),
      (outerProductStep fp.round k B).run.Nonempty := fun k B => by
    refine SetM.run_bind_nonempty (SetM.run_foldlM_nonempty (fun _ _ _ =>
      SetM.run_bind_nonempty (RoundingModel.run_round_nonempty hfp _) fun _ _ =>
        ⟨_, SetM.mem_run_pure.2 rfl⟩) _) fun _ _ => SetM.run_foldlM_nonempty (fun _ _ _ =>
      SetM.run_foldlM_nonempty (fun _ _ _ => SetM.run_bind_nonempty
        (RoundingModel.run_round_nonempty hfp _) fun _ _ => SetM.run_bind_nonempty
          (RoundingModel.run_round_nonempty hfp _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩) _) _
  refine SetM.run_foldlM_nonempty (fun st k _ => ?_) _
  split_ifs
  · exact SetM.run_bind_nonempty (hstep k _) fun _ _ => ⟨_, SetM.mem_run_pure.2 rfl⟩
  · exact ⟨_, SetM.mem_run_pure.2 rfl⟩

/-- The exact run of Algorithm 3.4.1 is a run of the exact model. -/
private theorem algorithm_3_4_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_4_1 pure A) ∈ (algorithm_3_4_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_4_1, outerProductStep, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- **The exact factors of a finished invariant**: in the exact model, the packed matrix is an LU
factorization of `A` with multipliers of modulus at most one (a zero pivot has a zero numerator). -/
theorem isLU_of_pivStageInv_exact {A F : Matrix (Fin n) (Fin n) ℝ}
    (h : PivStageInv (RoundingModel.exact ℝ) A n F) :
    IsLU A (packedL F) (packedU F) ∧ ∀ i j, |packedL F i j| ≤ 1 := by
  obtain ⟨hS, hD⟩ := h
  have hR := roundsLU_of_luStageInv hS
  -- the entries of the product
  have hU : ∀ i j : Fin n, i ≤ j →
      F i j = A i j - ∑ r ∈ Finset.univ.filter (· < i), F i r * F r j := by
    intro i j hij
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 i.2 hij
    have hset : o.toFinset = Finset.univ.filter (· < i) := by ext r; simp [ho]
    rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hsum, hset]
    congr 1
    exact Finset.sum_congr rfl fun r hr => hp r ((ho r).2 (Finset.mem_filter.1 hr).2)
  have hL : ∀ i j : Fin n, j < i →
      F i j * F j j = A i j - ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j ∧ |F i j| ≤ 1 := by
    intro i j hji
    obtain ⟨o, p, t, hnd, ho, hp, hsum, hd, hx⟩ := hD i j j.2 hji
    have hset : o.toFinset = Finset.univ.filter (· < j) := by ext r; simp [ho]
    have ht : t = A i j - ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j := by
      rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hsum, hset]
      congr 1
      exact Finset.sum_congr rfl fun r hr => hp r ((ho r).2 (Finset.mem_filter.1 hr).2)
    rw [RoundingModel.exact_rounds_iff] at hx
    refine ⟨?_, by rw [hx]; exact abs_div_le_one_of_abs_le hd⟩
    rw [← ht, hx]
    rcases eq_or_ne (F j j) 0 with h0 | h0
    · rw [h0, abs_zero] at hd
      rw [h0, mul_zero, abs_nonpos_iff.1 hd]
    · exact div_mul_cancel₀ _ h0
  refine ⟨⟨hR.isLU_mul.isUnitLowerTriangular, hR.isLU_mul.isUpperTriangular, ?_⟩,
    fun i j => ?_⟩
  · ext i j
    rw [hR.isLU_mul.apply_eq_sum]
    rcases le_or_gt i j with hij | hji
    · have hsum : ∑ r ∈ Finset.univ.filter (· < i), packedL F i r * packedU F r j =
          ∑ r ∈ Finset.univ.filter (· < i), F i r * F r j :=
        Finset.sum_congr rfl fun r hr => by
          have hr' := (Finset.mem_filter.1 hr).2
          rw [packedL_apply_of_lt _ hr', packedU_apply_of_le _ (hr'.le.trans hij)]
      rw [min_eq_left hij, Matrix.sum_filter_le_eq_add, packedL_apply_self, one_mul,
        packedU_apply_of_le _ hij, hsum, hU i j hij]
      ring
    · have hsum : ∑ r ∈ Finset.univ.filter (· < j), packedL F i r * packedU F r j =
          ∑ r ∈ Finset.univ.filter (· < j), F i r * F r j :=
        Finset.sum_congr rfl fun r hr => by
          have hr' := (Finset.mem_filter.1 hr).2
          rw [packedL_apply_of_lt _ (hr'.trans hji), packedU_apply_of_le _ hr'.le]
      rw [min_eq_right hji.le, Matrix.sum_filter_le_eq_add, packedL_apply_of_lt _ hji,
        packedU_apply_of_le _ le_rfl, hsum, (hL i j hji).1]
      ring
  · rcases lt_trichotomy j i with hji | rfl | hij
    · rw [packedL_apply_of_lt _ hji]
      exact (hL i j hji).2
    · rw [packedL_apply_self, abs_one]
    · rw [packedL_apply_of_lt' _ hij, abs_zero]
      exact zero_le_one

/-- **Exact correctness of Algorithm 3.4.1**: "this algorithm computes the factorization
`PA = LU` where `P` is a permutation matrix encoded by `piv`, `L` is unit lower triangular with
`|ℓ_ij| ≤ 1`, and `U` is upper triangular" — for every `A` ("Algorithm 3.4.1 always runs to
completion"). Read off the invariant of the bridge at the exact model. -/
theorem algorithm_3_4_1_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((pivPerm (Id.run (algorithm_3_4_1 pure A)).2).permMatrix ℝ * A)
        (packedL (Id.run (algorithm_3_4_1 pure A)).1)
        (packedU (Id.run (algorithm_3_4_1 pure A)).1) ∧
      ∀ i j, |packedL (Id.run (algorithm_3_4_1 pure A)).1 i j| ≤ 1 := by
  rcases alg341Inv_of_mem_run A _ (algorithm_3_4_1_mem_exact A) with h | ⟨-, hn⟩
  · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    exact isLU_of_pivStageInv_exact h
  · exact absurd (fun x => rfl) hn

end Algorithm341

/-! ### Solving after Algorithm 3.4.1 (§3.4.3) and the LU mentality (§3.4.9) -/

section Solve

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- §3.4.3, "to compute the solution to `Ax = b` after invoking Algorithm 3.4.1, we solve
`Ly = Pb` for `y` and `Ux = y` for `x`": `b` is overwritten by `P b` through the `piv` loop
(`applyPiv`, no arithmetic), then the row-oriented substitutions of §3.1 (Algorithms 3.1.1 and
3.1.2) with the packed factors — the solves of Theorem 3.3.2. The division by the unit diagonal of
`L` is performed by Algorithm 3.1.1 as the book writes it. -/
noncomputable def solvePLU {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let y ← algorithm_3_1_1 rnd (packedL F) (applyPiv piv b)
  algorithm_3_1_2 rnd (packedU F) y

/-- Gaussian elimination with partial pivoting, then the solve: Algorithm 3.4.1 followed by
`solvePLU`. -/
noncomputable def solveGEPP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  solvePLU rnd out.1 out.2 b

/-- (3.4.12), the multiple right-hand side problem `AX = B`: "compute `PA = LU`; for `k = 1:p`,
solve `Ly = Pb_k` and then `Ux_k = y`". With `B = I` the output approximates `A⁻¹`. -/
noncomputable def solveMultipleRHS {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : M (Matrix (Fin n) (Fin p) ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  (List.finRange p).foldlM (fun (X : Matrix (Fin n) (Fin p) ℝ) k => do
    let x ← solvePLU rnd out.1 out.2 (fun i => B i k)
    pure (X.updateCol k x)) B

/-- (3.4.13), solving `A^k x = b` without forming `A^k`: "compute `PA = LU`; for `j = 1:k`,
overwrite `b` with the solution to `Ly = Pb`, then overwrite `b` with the solution to `Ux = b`". -/
noncomputable def solvePowerSystem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let out ← algorithm_3_4_1 rnd A
  (List.range k).foldlM (fun b _ => solvePLU rnd out.1 out.2 b) b

variable {n : ℕ}

/-- The exact solve with the exact factors of a nonsingular `A` solves `A x = b`. -/
theorem solvePLU_id_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solvePLU pure (Id.run (algorithm_3_4_1 pure A)).1
      (Id.run (algorithm_3_4_1 pure A)).2 b) = b := by
  obtain ⟨hLU, -⟩ := algorithm_3_4_1_spec A
  set out := Id.run (algorithm_3_4_1 pure A)
  have hd : ∀ i, packedU out.1 i i ≠ 0 := by
    have hPA : IsUnit ((pivPerm out.2).permMatrix ℝ * A) := (isUnit_permMatrix _).mul hA
    intro i hi
    have hdet : ((pivPerm out.2).permMatrix ℝ * A).det = 0 := by
      rw [hLU.det_eq_prod_diag]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    exact ((isUnit_iff_isUnit_det _).1 hPA).ne_zero hdet
  have h := mulVec_luSolve_permMatrix b hLU hd
  change A *ᵥ Id.run (algorithm_3_1_2 pure (packedU out.1)
    (Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2 b)))) = b
  rw [algorithm_3_1_1_eq_forwardSubst, algorithm_3_1_2_eq_backSubst, (applyPiv_eq _ _).1]
  exact h

/-- **Exact correctness of the solve after Algorithm 3.4.1**: for nonsingular `A`, Gaussian
elimination with partial pivoting followed by `Ly = Pb`, `Ux = y` solves `Ax = b`. -/
theorem solvePLU_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solveGEPP pure A b) = b :=
  solvePLU_id_eq hA b

/-- A loop writing column `k` with a fixed vector `g k` sets the listed columns. -/
theorem foldl_updateCol_apply {p : ℕ}
    (u : Matrix (Fin n) (Fin p) ℝ → Fin p → Matrix (Fin n) (Fin p) ℝ)
    (g : Fin p → Fin n → ℝ) (hu : ∀ X k, u X k = X.updateCol k (g k)) (l : List (Fin p))
    (X₀ : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (k : Fin p) :
    l.foldl u X₀ i k = if k ∈ l then g k i else X₀ i k := by
  induction l generalizing X₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, hu]
    by_cases hk : k ∈ l <;> by_cases hka : k = a <;> simp [hk, hka]

/-- **(3.4.12)** solves `AX = B`: for nonsingular `A` the exact output `X` of the multiple
right-hand side procedure satisfies `AX = B`, and with `B = I` it is `A⁻¹`. -/
theorem equation_3_4_12 {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    A * Id.run (solveMultipleRHS pure A B) = B ∧
      Id.run (solveMultipleRHS pure A (1 : Matrix (Fin n) (Fin n) ℝ)) = A⁻¹ := by
  have key : ∀ {p : ℕ} (B : Matrix (Fin n) (Fin p) ℝ),
      A * Id.run (solveMultipleRHS pure A B) = B := by
    intro p B
    set out := Id.run (algorithm_3_4_1 pure A)
    change A * Id.run ((List.finRange p).foldlM (fun (X : Matrix (Fin n) (Fin p) ℝ) k => do
      let x ← solvePLU pure out.1 out.2 (fun i => B i k)
      pure (X.updateCol k x)) B) = B
    rw [List.idRun_foldlM]
    ext i k
    rw [mul_apply]
    have hcol : ∀ j, (List.finRange p).foldl (fun X k => Id.run (do
        let x ← solvePLU pure out.1 out.2 (fun i => B i k)
        pure (X.updateCol k x) : Id _)) B j k =
        Id.run (solvePLU pure out.1 out.2 (fun i => B i k)) j := fun j => by
      have h := foldl_updateCol_apply (fun X k => Id.run (do
          let x ← solvePLU pure out.1 out.2 (fun i => B i k)
          pure (X.updateCol k x) : Id _))
        (fun k => Id.run (solvePLU pure out.1 out.2 (fun i => B i k))) (fun _ _ => rfl)
        (List.finRange p) B j k
      rw [h]
      simp
    simp only [hcol]
    exact congrFun (solvePLU_id_eq hA (fun i => B i k)) i
  exact ⟨key B, (inv_eq_right_inv (key 1)).symm⟩

/-- **(3.4.13)** solves `A^k x = b`: for nonsingular `A`, the exact output of `solvePowerSystem`
satisfies `A^k x = b`. -/
theorem equation_3_4_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (k : ℕ) (b : Fin n → ℝ) :
    A ^ k *ᵥ Id.run (solvePowerSystem pure A k b) = b := by
  set out := Id.run (algorithm_3_4_1 pure A)
  have hstep : ∀ c : Fin n → ℝ, A *ᵥ Id.run (solvePLU pure out.1 out.2 c) = c :=
    fun c => solvePLU_id_eq hA c
  change A ^ k *ᵥ Id.run ((List.range k).foldlM (fun b _ => solvePLU pure out.1 out.2 b) b) = b
  rw [List.idRun_foldlM]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ,
      ← mulVec_mulVec, hstep, ih]

end Solve

/-! ### The backward error of the solve (§3.4.5) -/

section Backward

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **(3.4.6)**, rigorous form: every run `(F, piv)` of Algorithm 3.4.1 with nonzero returned
pivots, followed by every run of the solve `Ly = Pb`, `Ux = y`, gives `(A + E) x̂ = b` with
`|E| ≤ γ_{3n} Pᵀ |L̂| |Û|` entrywise (`Pᵀ M` is `M` with its rows permuted back,
`M.submatrix σ⁻¹ id`; no rounding in the permutation). Theorem 3.3.2's bound for the system
`(PA) x = Pb` ([higham2002accuracy] Theorem 9.4); the book's `nu(2|A| + 4Pᵀ|L̂||Û|) + O(u²)` is
implied to first order. -/
theorem equation_3_4_6 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ E.abs ≤ₑ gamma fp.u (3 * n) •
          ((packedL out.1).abs * (packedU out.1).abs).submatrix (pivPerm out.2).symm id := by
  intro out hout hpiv x hx
  obtain ⟨hR, -⟩ := algorithm_3_4_1_rounds A out hout fun j _ => hpiv j
  rw [solvePLU, SetM.mem_run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨E', hE', hAx⟩ := exists_roundsLU_solveDot_eq hu (by simpa using hn) hR
    (fun j => by rw [packedU_apply_of_le _ le_rfl]; exact hpiv j)
    (algorithm_3_1_1_rounds fp _ _ y hy) (algorithm_3_1_2_rounds fp _ y x hx)
  set σ := pivPerm out.2
  have hPb : applyPiv out.2 b = b ∘ σ := by rw [(applyPiv_eq _ _).1, permMatrix_mulVec]
  rw [hPb] at hAx
  refine ⟨E'.submatrix σ.symm id, funext fun i => ?_, fun i j => ?_⟩
  · have h := congrFun hAx (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    simp only [mulVec, dotProduct, Matrix.add_apply, submatrix_apply, id, Equiv.apply_symm_apply]
  · simpa [Matrix.abs, smul_eq_mul] using hE' (σ.symm i) j

end Backward

/-! ### Complete pivoting (§3.4.6) -/

section Complete

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **Interchanging rows and columns at or after `k`** keeps the invariant after `k` steps, for the
matrix with the same rows and columns interchanged. -/
theorem pivStageInv_submatrix₂ {A S : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    {τ ρ : Equiv.Perm (Fin n)}
    (hfix : ∀ r : Fin n, (r : ℕ) < k → τ r = r) (hmap : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (τ i : ℕ))
    (hfix' : ∀ r : Fin n, (r : ℕ) < k → ρ r = r)
    (hmap' : ∀ i : Fin n, k ≤ (i : ℕ) → k ≤ (ρ i : ℕ))
    (h : PivStageInv fp A k S) :
    PivStageInv fp (A.submatrix τ ρ) k (S.submatrix τ ρ) := by
  obtain ⟨hS, hD⟩ := h
  have hlt : ∀ (i j : Fin n), (j : ℕ) < k → j < i → j < τ i := fun i j hj hji => by
    by_cases hi : (i : ℕ) < k
    · rw [hfix i hi]; exact hji
    · exact Fin.lt_def.2 (lt_of_lt_of_le hj (hmap i (not_lt.1 hi)))
  have hle : ∀ (i j : Fin n), (i : ℕ) < k → i ≤ j → i ≤ ρ j := fun i j hi hij => by
    by_cases hj : (j : ℕ) < k
    · rw [hfix' j hj]; exact hij
    · exact Fin.le_def.2 (le_trans hi.le (hmap' j (not_lt.1 hj)))
  refine ⟨fun i j => ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩,
    fun i j hj hji => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i (ρ j)).1 hi (hle i j hi hij)
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix i hi, hfix r (by omega), hfix' r (by omega)]
      exact hp r hr
    · simp only [submatrix_apply, hfix i hi]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS (τ i) j).2.1 hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix r (by omega), hfix' r (by omega), hfix' j hj]
      exact hp r hr
    · simp only [submatrix_apply, hfix' j hj]
      exact hsum
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hx
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS (τ i) (ρ j)).2.2 (hmap i hi) (hmap' j hj)
    refine ⟨o, p, hnd, ho, fun r hr => ?_, hsum⟩
    simp only [submatrix_apply, hfix r ((ho r).1 hr), hfix' r ((ho r).1 hr)]
    exact hp r hr
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hdom, hx⟩ := hD (τ i) j hj (hlt i j hj hji)
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, ?_, ?_, ?_⟩
    · have hr' := Fin.lt_def.1 ((ho r).1 hr)
      simp only [submatrix_apply, hfix r (by omega), hfix' r (by omega), hfix' j hj]
      exact hp r hr
    · simp only [submatrix_apply, hfix' j hj]
      exact hsum
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hdom
    · simp only [submatrix_apply, hfix j hj, hfix' j hj]
      exact hx

/-- The rows of `U` finished by complete pivoting are dominated by their diagonal entry. -/
def RowDom (k : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < k → i ≤ j → |S i j| ≤ |S i i|

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step of Algorithm 3.4.3: the search for an entry of maximal modulus in the trailing block
(`Matrix.completePivotEntry`, exact comparisons), the row and column interchanges, and, if the
pivot is nonzero, the updates of Algorithm 3.2.1. -/
noncomputable def completePivotingStep {n : ℕ} (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :=
  if st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
      (Equiv.swap k (completePivotEntry st.1 k).2) k k ≠ 0 then do
    let S ← outerProductStep rnd k (st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
      (Equiv.swap k (completePivotEntry st.1 k).2))
    pure (S, Function.update st.2.1 k (completePivotEntry st.1 k).1,
      Function.update st.2.2 k (completePivotEntry st.1 k).2)
  else
    pure (st.1.submatrix (Equiv.swap k (completePivotEntry st.1 k).1)
        (Equiv.swap k (completePivotEntry st.1 k).2),
      Function.update st.2.1 k (completePivotEntry st.1 k).1,
      Function.update st.2.2 k (completePivotEntry st.1 k).2)

/-- **Algorithm 3.4.3 (Outer Product LU with Complete Pivoting).** "This algorithm computes the
factorization `PAQᵀ = LU` where `P` is a permutation matrix encoded by `rowpiv(1:n-1)`, `Q` is a
permutation matrix encoded by `colpiv(1:n-1)`, `L` is unit lower triangular with `|ℓ_ij| ≤ 1`, and
`U` is upper triangular."
```
for k = 1:n-1
    Determine μ with k ≤ μ ≤ n and λ with k ≤ λ ≤ n so
        |A(μ,λ)| = max{|A(i,j)| : i = k:n, j = k:n}
    rowpiv(k) = μ;  A(k,1:n) ↔ A(μ,1:n)
    colpiv(k) = λ;  A(1:n,k) ↔ A(1:n,λ)
    if A(k,k) ≠ 0
        ρ = k+1:n
        A(ρ,k) = A(ρ,k)/A(k,k)
        A(ρ,ρ) = A(ρ,ρ) - A(ρ,k) A(k,ρ)
    end
end
```
The state is `(A, rowpiv, colpiv)`, both `piv` vectors initially the identity. -/
noncomputable def algorithm_3_4_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) :=
  (List.finRange n).foldlM (fun st k => completePivotingStep rnd k st) (A, fun k => k, fun k => k)

/-- The invariant of Algorithm 3.4.3 after `k` steps, in a model that rounds every value to
itself. -/
def Alg343Inv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n)) : Prop :=
  PivStageInv fp (A.submatrix (pivPermUpTo st.2.1 k) (pivPermUpTo st.2.2 k)) k st.1 ∧
    RowDom k st.1

/-- The interchange of `k` with an index at or after `k` fixes the indices before `k` and maps
the indices from `k` on among themselves. -/
theorem swap_fix_and_map {k μ : Fin n} (hkμ : k ≤ μ) :
    (∀ r : Fin n, (r : ℕ) < k → Equiv.swap k μ r = r) ∧
      ∀ i : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ (Equiv.swap k μ i : ℕ) := by
  refine ⟨fun r hr => Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hr; exact lt_irrefl _ hr)
      fun h => by rw [h] at hr; exact absurd (Fin.le_def.1 hkμ) (not_le.2 hr), fun i hi => ?_⟩
  rcases eq_or_ne i k with rfl | hik
  · rw [Equiv.swap_apply_left]; exact hkμ
  rcases eq_or_ne i μ with rfl | hiμ
  · rw [Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne hik hiμ]; exact hi

/-- The permutation after one more interchange. -/
theorem pivPermUpTo_update (piv : Fin n → Fin n) (k μ : Fin n) :
    pivPermUpTo (Function.update piv k μ) (k + 1) = pivPermUpTo piv k * Equiv.swap k μ := by
  rw [pivPermUpTo_succ, Function.update_self,
    pivPermUpTo_congr (piv := Function.update piv k μ) (piv' := piv) (k := k)
      fun j hj => Function.update_of_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj) _ _]

/-- One step of Algorithm 3.4.3 keeps its invariant. -/
theorem alg343Inv_step (hrefl : ∀ x, fp.Rounds x x) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst : Alg343Inv fp A k st) (st' : Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n) × (Fin n → Fin n))
    (hst' : st' ∈ (completePivotingStep fp.round k st).run) :
    Alg343Inv fp A (k + 1) st' := by
  obtain ⟨S, rp, cp⟩ := st
  obtain ⟨hgood, hrow⟩ := hst
  rw [completePivotingStep] at hst'
  dsimp only at hst' hgood hrow
  have hpiv := isCompletePivot_completePivotEntry S k
  set μ := (completePivotEntry S k).1 with hμ
  set ν := (completePivotEntry S k).2 with hν
  set S₀ := S.submatrix (Equiv.swap k μ) (Equiv.swap k ν) with hS₀
  obtain ⟨hfix, hmap⟩ := swap_fix_and_map (k := k) hpiv.1
  obtain ⟨hfix', hmap'⟩ := swap_fix_and_map (k := k) hpiv.2.1
  have hsub : (A.submatrix (pivPermUpTo rp k) (pivPermUpTo cp k)).submatrix (Equiv.swap k μ)
      (Equiv.swap k ν) = A.submatrix (pivPermUpTo (Function.update rp k μ) (k + 1))
        (pivPermUpTo (Function.update cp k ν) (k + 1)) := by
    rw [pivPermUpTo_update, pivPermUpTo_update, submatrix_submatrix, Equiv.Perm.coe_mul,
      Equiv.Perm.coe_mul]
  have hgood₀ : PivStageInv fp (A.submatrix (pivPermUpTo (Function.update rp k μ) (k + 1))
      (pivPermUpTo (Function.update cp k ν) (k + 1))) k S₀ :=
    hsub ▸ pivStageInv_submatrix₂ hfix hmap hfix' hmap' hgood
  -- the interchanged pivot dominates the trailing block
  have hmax : ∀ i j : Fin n, k ≤ i → k ≤ j → |S₀ i j| ≤ |S₀ k k| := fun i j hi hj => by
    simp only [hS₀, submatrix_apply, Equiv.swap_apply_left]
    have := hpiv.2.2 (Equiv.swap k μ i) (Equiv.swap k ν j)
      (Fin.le_def.2 (hmap i (Fin.le_def.1 hi))) (Fin.le_def.2 (hmap' j (Fin.le_def.1 hj)))
    simpa only [Real.norm_eq_abs] using this
  have hdom : ∀ i : Fin n, k ≤ i → |S₀ i k| ≤ |S₀ k k| := fun i hi => hmax i k hi le_rfl
  have hrow₀ : RowDom k S₀ := fun i j hi hij => by
    simp only [hS₀, submatrix_apply, hfix i hi]
    rw [hfix' i hi]
    refine hrow i _ hi ?_
    by_cases hj : (j : ℕ) < k
    · rw [hfix' j hj]; exact hij
    · exact Fin.le_def.2 (le_trans hi.le (hmap' j (not_lt.1 hj)))
  -- the new row `k` and the old rows are unchanged by the step
  have hrow' : ∀ S' : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S₀ i j) → RowDom (k + 1) S' :=
    fun S' hS' i j hi hij => by
      have hi' : ¬ (k < i) := fun h => by have := Fin.lt_def.1 h; omega
      rw [hS' i j fun h => hi' h.1, hS' i i fun h => hi' h.1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact hrow₀ i j hi hij
      · have hik : i = k := Fin.ext hi
        subst hik
        exact hmax i j le_rfl hij
  split_ifs at hst' with h0
  · rw [SetM.mem_run_bind] at hst'
    obtain ⟨S', hS', hst'⟩ := hst'
    rw [SetM.mem_run_pure] at hst'
    subst hst'
    obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
    exact ⟨pivStageInv_step k hgood₀ hdom h₁ h₂ h₃, hrow' S' h₁⟩
  · rw [SetM.mem_run_pure] at hst'
    subst hst'
    exact ⟨pivStageInv_step_of_zero k hgood₀ hdom (not_not.1 h0) (Or.inl hrefl),
      hrow' S₀ fun _ _ _ => rfl⟩

/-- The exact run of Algorithm 3.4.3 is a run of the exact model. -/
private theorem algorithm_3_4_3_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_4_3 pure A) ∈ (algorithm_3_4_3 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_4_3, completePivotingStep, outerProductStep, pure_bind, ite_pure,
    List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Exact correctness of Algorithm 3.4.3**: with `(F, rowpiv, colpiv)` its output,
`P A Qᵀ = L U` with `P = (pivPerm rowpiv).permMatrix ℝ`, `Qᵀ = ((pivPerm colpiv)⁻¹).permMatrix ℝ`
(the book writes `PAQᵀ` in Algorithm 3.4.3 and `PAQ` in §3.4.7), `L = packedL F` unit lower
triangular with `|ℓ_ij| ≤ 1` and `U = packedU F` upper triangular with `|u_ij| ≤ |u_ii|`
(P3.4.2) — for every `A`. -/
theorem algorithm_3_4_3_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    IsLU ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.1).permMatrix ℝ * A *
          ((pivPerm (Id.run (algorithm_3_4_3 pure A)).2.2)⁻¹).permMatrix ℝ)
        (packedL (Id.run (algorithm_3_4_3 pure A)).1)
        (packedU (Id.run (algorithm_3_4_3 pure A)).1) ∧
      (∀ i j, |packedL (Id.run (algorithm_3_4_3 pure A)).1 i j| ≤ 1) ∧
      ∀ i j, |packedU (Id.run (algorithm_3_4_3 pure A)).1 i j| ≤
        |packedU (Id.run (algorithm_3_4_3 pure A)).1 i i| := by
  have hinv := SetM.forall_mem_run_foldlM_finRange (Alg343Inv (RoundingModel.exact ℝ) A)
    ⟨⟨luStageInv_zero _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun k st hst st' hst' => alg343Inv_step (fun _ => rfl) A k st hst st' hst') _
    (algorithm_3_4_3_mem_exact A)
  obtain ⟨hgood, hrow⟩ := hinv
  obtain ⟨hLU, hL⟩ := isLU_of_pivStageInv_exact hgood
  refine ⟨by rw [permMatrix_mul_mul_permMatrix]; exact hLU, hL, fun i j => ?_⟩
  rcases le_or_gt i j with hij | hji
  · rw [packedU_apply_of_le _ hij, packedU_apply_of_le _ le_rfl]
    exact hrow i j i.2 hij
  · rw [packedU_apply_of_lt _ hji, abs_zero]
    exact abs_nonneg _

/-- §3.4.6, Steps 1–3 after Algorithm 3.4.3: "Step 1. Solve `Lz = Pb` for `z`. Step 2. Solve
`Uy = z` for `y`. Step 3. Set `x = Qᵀy`." With the row-oriented substitutions of §3.1 and the
`piv` loops (`applyPiv`, `applyPivRev`). -/
noncomputable def solvePLUQ {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (rowpiv colpiv : Fin n → Fin n)
    (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let z ← algorithm_3_1_1 rnd (packedL F) (applyPiv rowpiv b)
  let y ← algorithm_3_1_2 rnd (packedU F) z
  pure (applyPivRev colpiv y)

/-- Gaussian elimination with complete pivoting, then the solve. -/
noncomputable def solveGECP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let out ← algorithm_3_4_3 rnd A
  solvePLUQ rnd out.1 out.2.1 out.2.2 b

/-- **Exact correctness of the GECP solve**: for nonsingular `A`, complete pivoting followed by
Steps 1–3 solves `Ax = b`. -/
theorem solvePLUQ_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b : Fin n → ℝ) :
    A *ᵥ Id.run (solveGECP pure A b) = b := by
  obtain ⟨hLU, -, -⟩ := algorithm_3_4_3_spec A
  set out := Id.run (algorithm_3_4_3 pure A)
  set σ := pivPerm out.2.1
  set ρ := pivPerm out.2.2
  rw [permMatrix_mul_mul_permMatrix] at hLU
  have hB : IsUnit (A.submatrix σ ρ) := by
    rw [← permMatrix_mul_mul_permMatrix]
    exact ((isUnit_permMatrix _).mul hA).mul (isUnit_permMatrix _)
  have hd : ∀ i, packedU out.1 i i ≠ 0 := by
    intro i hi
    have hdet : (A.submatrix σ ρ).det = 0 := by
      rw [hLU.det_eq_prod_diag]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    exact ((isUnit_iff_isUnit_det _).1 hB).ne_zero hdet
  have hLd : ∀ i, packedL out.1 i i ≠ 0 := fun i => by
    rw [hLU.isUnitLowerTriangular.diag_eq_one]; exact one_ne_zero
  change A *ᵥ applyPivRev out.2.2 (Id.run (algorithm_3_1_2 pure (packedU out.1)
    (Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2.1 b))))) = b
  set z := Id.run (algorithm_3_1_1 pure (packedL out.1) (applyPiv out.2.1 b))
  set y := Id.run (algorithm_3_1_2 pure (packedU out.1) z)
  have hz : packedL out.1 *ᵥ z = b ∘ σ := by
    rw [algorithm_3_1_1_spec hLU.isUnitLowerTriangular.isLowerTriangular hLd,
      (applyPiv_eq _ _).1, permMatrix_mulVec]
  have hy : packedU out.1 *ᵥ y = z := algorithm_3_1_2_spec hLU.isUpperTriangular hd z
  have hBy : A.submatrix σ ρ *ᵥ y = b ∘ σ := by
    rw [← hLU.mul_eq, ← mulVec_mulVec, hy, hz]
  rw [(applyPiv_eq _ _).2, mulVec_transpose, vecMul_permMatrix]
  funext i
  have := congrFun hBy (σ.symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  rw [← this]
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.apply_symm_apply]
  exact (Fintype.sum_equiv ρ _ _ fun j => by simp [ρ]).symm

/-- **(3.4.10)**, Wilkinson's bound for complete pivoting in exact arithmetic, with the index
corrected: the entries of the trailing block of `A^{(k)}`, the matrix after `k` steps of complete
pivoting, satisfy `|a_ij^{(k)}| ≤ (k+1)^{1/2} (2 · 3^{1/2} ⋯ (k+1)^{1/k})^{1/2} max |a_ij|`
(`Matrix.wilkinsonGrowthBound (k + 1) * supAbs A`). The book prints the bound with `k` in place of
`k + 1`, which is false for `k = 1` (`!![1, 1; 1, -1]` produces `-2 > 1 = f(1)`); with the (3.2.3)
indexing (`A^{(k)}` after `k - 1` steps) the printed form is right. -/
theorem equation_3_4_10 (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : k < n) {i j : Fin n}
    (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) :
    |(gemFullPivotStage A completePivotEntry k).1 i j| ≤ wilkinsonGrowthBound (k + 1) * A.supAbs :=
  abs_gemFullPivotStage_le_wilkinson A isCompletePivot_completePivotEntry hk hi hj

/-- §3.4.6, rank revelation: "suppose `rank(A) = r < n`. It follows that at the beginning of step
`r + 1`, `A(r+1:n, r+1:n) = 0`", and the first `r` pivots are nonzero. -/
theorem completePivoting_rank (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} (hr : A.rank = r) :
    (∀ i j : Fin n, r ≤ (i : ℕ) → r ≤ (j : ℕ) →
        (gemFullPivotStage A completePivotEntry r).1 i j = 0) ∧
      ∀ (k : ℕ) (hk : k < n), k < r →
        (gemFullPivotStage A completePivotEntry k).1
          (completePivotEntry (gemFullPivotStage A completePivotEntry k).1 ⟨k, hk⟩).1
          (completePivotEntry (gemFullPivotStage A completePivotEntry k).1 ⟨k, hk⟩).2 ≠ 0 :=
  gemFullPivotStage_trailing_eq_zero_of_rank A isCompletePivot_completePivotEntry hr

end Complete

/-! ### The growth factor (§3.4.5) -/

section Growth

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- **(3.4.8)**, the growth factor as printed, `ρ = max_{i,j,k} |a_ij^{(k)}| / ‖A‖_∞`, over the
stages `A^{(k)} = M_k Π_k ⋯ M_1 Π_1 A` of partial pivoting (`k = 0, …, n`). The stages are the
exact ones (the book writes the computed `Â^{(k)}`; only exact stages admit bounds,
[higham2002accuracy] after Theorem 9.5), and the denominator is the book's `‖A‖_∞`, where
Wilkinson's (and the backbone's `Matrix.growthFactor`) is `max |a_ij|`. -/
noncomputable def growthFactorStages (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (⨆ k : Fin (n + 1), (partialPivotStage A k).supAbs) / ‖A‖

/-- **(3.4.8) against the backbone's growth factor**: `ρ = growthFactor(PA) · max|a_ij| / ‖A‖_∞`
with `P` the partial-pivoting permutation — the stages of elimination without pivoting on `PA` are
the pivoted stages with their rows permuted — hence `ρ ≤ growthFactor(PA)`. -/
theorem growthFactorStages_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    growthFactorStages A = growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) *
        A.supAbs / ‖A‖ ∧
      growthFactorStages A ≤
        growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) := by
  set B := (gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A with hB
  have hpiv : ∀ (M : Matrix (Fin n) (Fin n) ℝ) k, k ≤ partialPivotRow M k :=
    fun M k => le_partialPivotRow M k
  -- the stages of `B` are the pivoted stages with permuted rows
  have hstage : ∀ k : ℕ, (gemStage B k).supAbs = (partialPivotStage A k).supAbs := fun k => by
    rw [hB, gemStage_permMatrix_mul_eq_submatrix_gemPivotStage A partialPivotRow hpiv k,
      supAbs_submatrix_equiv]
  have hBA : B.supAbs = A.supAbs := by
    rw [hB, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, supAbs_submatrix_equiv]
  set X := ⨆ k : Fin (n + 1), (partialPivotStage A k).supAbs with hX
  set Y := ⨆ p : Fin n × Fin n × Fin n, |gemStage B p.1 p.2.1 p.2.2| with hY
  have hXnn : 0 ≤ X := Real.iSup_nonneg fun k => supAbs_nonneg _
  have hYnn : 0 ≤ Y := Real.iSup_nonneg fun _ => abs_nonneg _
  have hbddX : BddAbove (Set.range fun k : Fin (n + 1) => (partialPivotStage A k).supAbs) :=
    (Set.finite_range _).bddAbove
  have hbddY : BddAbove (Set.range fun p : Fin n × Fin n × Fin n =>
      |gemStage B p.1 p.2.1 p.2.2|) := (Set.finite_range _).bddAbove
  have hXY : X = Y := by
    refine le_antisymm (ciSup_le fun k => ?_) ?_
    · rw [← hstage]
      refine supAbs_le hYnn fun i j => ?_
      rcases lt_or_ge (k : ℕ) n with hk | hk
      · exact le_ciSup hbddY (⟨k, hk⟩, i, j)
      · rw [gemStage_apply_of_le B (le_refl (i : ℕ)) (i.2.le.trans hk)]
        exact le_ciSup hbddY (i, i, j)
    · rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · rw [hY, Real.iSup_of_isEmpty]
        exact hXnn
      refine ciSup_le fun p => ?_
      refine (abs_apply_le_supAbs _ _ _).trans ?_
      rw [hstage]
      exact le_ciSup hbddX (⟨p.1, by omega⟩ : Fin (n + 1))
  have heq : growthFactorStages A = growthFactor B * A.supAbs / ‖A‖ := by
    rw [growthFactorStages, ← hX, hXY]
    rcases eq_or_ne A.supAbs 0 with h0 | h0
    · have hA : A = 0 := supAbs_eq_zero_iff.1 h0
      have hB0 : B = 0 := by rw [hB, hA, Matrix.mul_zero]
      have hY0 : Y = 0 := by
        rw [hY]
        simp [hB0, gemStage_zero_matrix]
      rw [hY0, h0, mul_zero]
    · rw [growthFactor, hBA, div_mul_cancel₀ _ h0]
  refine ⟨heq, ?_⟩
  rw [heq]
  rcases eq_or_ne ‖A‖ 0 with hA | hA
  · rw [hA, div_zero]
    exact growthFactor_nonneg _
  · rw [mul_div_assoc]
    refine mul_le_of_le_one_right (growthFactor_nonneg _) ?_
    exact div_le_one_of_le₀ (supAbs_le_linfty_opNorm A) (norm_nonneg _)

/-- §3.4.5, "`ρ` can be as large as `2^{n-1}`", the upper half: with partial pivoting the growth is
at most `2^{n-1}` (P3.4.1's argument), `growthFactor(PA) ≤ 2^{n-1}`, and so the printed
`ρ ≤ 2^{n-1}`. -/
theorem growthFactor_le_two_pow (A : Matrix (Fin n) (Fin n) ℝ) :
    growthFactor ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 ^ (n - 1) ∧
      growthFactorStages A ≤ 2 ^ (n - 1) :=
  ⟨growthFactor_le_two_pow_of_partialPivotRow A,
    (growthFactorStages_eq A).2.trans (growthFactor_le_two_pow_of_partialPivotRow A)⟩

end Growth

/-! ### Normwise backward errors (§3.4.5) -/

section Normwise

open scoped Matrix.Norms.Operator

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- A matrix bounded entrywise by `γ` times a row permutation of a nonnegative `B` has
`‖E‖_∞ ≤ γ ‖B‖_∞`. -/
theorem linfty_opNorm_le_of_abs_le_smul_submatrix {E B : Matrix (Fin n) (Fin n) ℝ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hB : ∀ i j, 0 ≤ B i j) (e : Fin n → Fin n)
    (h : E.abs ≤ₑ γ • B.submatrix e id) : ‖E‖ ≤ γ * ‖B‖ := by
  refine linfty_opNorm_le_of_forall_sum_le (mul_nonneg hγ (norm_nonneg _)) fun i => ?_
  calc ∑ j, |E i j| ≤ ∑ j, γ * |B (e i) j| := Finset.sum_le_sum fun j _ => by
        have := h i j
        simp only [Matrix.abs_apply, Matrix.smul_apply, submatrix_apply, id, smul_eq_mul] at this
        rwa [abs_of_nonneg (hB _ _)]
    _ = γ * ∑ j, |B (e i) j| := by rw [Finset.mul_sum]
    _ ≤ γ * ‖B‖ := mul_le_mul_of_nonneg_left (sum_abs_apply_le_linfty_opNorm B (e i)) hγ

/-- The `∞`-norm of a matrix whose entries are bounded by `c` is at most `n c`. -/
theorem linfty_opNorm_le_card_mul_of_abs_le {B : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : ∀ i j, |B i j| ≤ c) (hc : 0 ≤ c) : ‖B‖ ≤ n * c :=
  linfty_opNorm_le_of_forall_sum_le (by positivity) fun i =>
    (Finset.sum_le_sum fun j _ => h i j).trans (by simp)

/-- The backward error (3.4.6) in norm: `‖E‖_∞ ≤ γ_{3n} ‖L̂‖_∞ ‖Û‖_∞`. -/
theorem linfty_opNorm_le_of_equation_3_4_6 {E L U : Matrix (Fin n) (Fin n) ℝ}
    {σ : Equiv.Perm (Fin n)} {γ : ℝ} (hγ : 0 ≤ γ)
    (hE : E.abs ≤ₑ γ • (L.abs * U.abs).submatrix σ.symm id) : ‖E‖ ≤ γ * (‖L‖ * ‖U‖) := by
  have hnn : ∀ i j, 0 ≤ (L.abs * U.abs) i j := fun i j =>
    ((entrywiseNonneg_abs L).mul (entrywiseNonneg_abs U)).apply i j
  refine (linfty_opNorm_le_of_abs_le_smul_submatrix hγ hnn _ hE).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hγ
  calc ‖L.abs * U.abs‖ ≤ ‖L.abs‖ * ‖U.abs‖ := linfty_opNorm_mul _ _
    _ = ‖L‖ * ‖U‖ := by rw [linfty_opNorm_abs, linfty_opNorm_abs]

/-- **(3.4.7)**, rigorous form: under the hypotheses of (3.4.6), `‖E‖_∞ ≤ n (1 + u) γ_{3n} ‖Û‖_∞` —
the computed multipliers are at most `1 + u` in absolute value, so `‖L̂‖_∞ ≤ n (1 + u)`. The book's
`nu(2‖A‖_∞ + 4n‖Û‖_∞) + O(u²)` is implied to first order. -/
theorem equation_3_4_7 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ n * (1 + fp.u) * gamma fp.u (3 * n) * ‖packedU out.1‖ := by
  intro out hout hpiv x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6 hu hn A b out hout hpiv x hx
  have hγ : 0 ≤ gamma fp.u (3 * n) := gamma_nonneg fp.u_nonneg hn
  have hL : ‖packedL out.1‖ ≤ n * (1 + fp.u) :=
    linfty_opNorm_le_card_mul_of_abs_le (algorithm_3_4_1_rounds A out hout fun j _ => hpiv j).2
      (by linarith [fp.u_nonneg])
  refine ⟨E, hAx, (linfty_opNorm_le_of_equation_3_4_6 hγ hE).trans ?_⟩
  calc gamma fp.u (3 * n) * (‖packedL out.1‖ * ‖packedU out.1‖)
      ≤ gamma fp.u (3 * n) * ((n * (1 + fp.u)) * ‖packedU out.1‖) := by gcongr
    _ = n * (1 + fp.u) * gamma fp.u (3 * n) * ‖packedU out.1‖ := by ring

/-- **(3.4.9)**, its rigorous conditional form (Higham's "illicit manoeuvre" made a hypothesis):
under the hypotheses of (3.4.6), if the computed `Û` satisfies `|û_ij| ≤ ρ ‖A‖_∞`, then
`‖E‖_∞ ≤ n² (1 + u) γ_{3n} ρ ‖A‖_∞`. With `ρ` the growth factor (3.4.8) this is the book's
`6 n³ ρ ‖A‖_∞ u + O(u²)` with the better constant `3` (`n² γ_{3n} = 3 n³ u + O(u²)`). -/
theorem equation_3_4_9 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      (∀ i j, |packedU out.1 i j| ≤ ρ * ‖A‖) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        (A + E) *ᵥ x = b ∧ ‖E‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ := by
  intro out hout hpiv hU x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_6 hu hn A b out hout hpiv x hx
  have hγ : 0 ≤ gamma fp.u (3 * n) := gamma_nonneg fp.u_nonneg hn
  have hL : ‖packedL out.1‖ ≤ n * (1 + fp.u) :=
    linfty_opNorm_le_card_mul_of_abs_le (algorithm_3_4_1_rounds A out hout fun j _ => hpiv j).2
      (by linarith [fp.u_nonneg])
  have hU' : ‖packedU out.1‖ ≤ n * (ρ * ‖A‖) :=
    linfty_opNorm_le_card_mul_of_abs_le hU (mul_nonneg hρ (norm_nonneg _))
  refine ⟨E, hAx, (linfty_opNorm_le_of_equation_3_4_6 hγ hE).trans ?_⟩
  calc gamma fp.u (3 * n) * (‖packedL out.1‖ * ‖packedU out.1‖)
      ≤ gamma fp.u (3 * n) * ((n * (1 + fp.u)) * (n * (ρ * ‖A‖))) := by
        gcongr
        exact (norm_nonneg _).trans hL
    _ = (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ := by ring

end Normwise

/-! ### The gaxpy version with pivoting (§3.4.4), the growth example, rook pivoting (§3.4.7) -/

section MorePivoting

variable {n : ℕ}

/-- The first index `i ≥ k` maximizing `|v i|` (exact comparisons): `Matrix.partialPivotRow` of
the matrix whose every column is `v`. -/
noncomputable def firstMaxIndex (v : Fin n → ℝ) (k : Fin n) : Fin n :=
  partialPivotRow (of fun i (_ : Fin n) => v i) k

/-- The first maximizing index lies at or after `k` and maximizes `|v i|` over `i ≥ k`. -/
theorem firstMaxIndex_spec (v : Fin n → ℝ) (k : Fin n) :
    k ≤ firstMaxIndex v k ∧ ∀ i, k ≤ i → |v i| ≤ |v (firstMaxIndex v k)| := by
  refine ⟨le_partialPivotRow _ k, fun i hi => ?_⟩
  have := norm_apply_le_partialPivotRow (of fun i (_ : Fin n) => v i) k hi
  simp only [of_apply, Real.norm_eq_abs] at this
  exact this

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.4.2 (Gaxpy LU with Partial Pivoting).** "Initialize `L` to the identity and `U`
to the zero matrix."
```
for j = 1:n
    if j = 1
        v = A(:,1)
    else
        ã = Π_{j-1} ⋯ Π_1 A(:,j)
        Solve L(1:j-1,1:j-1) z = ã(1:j-1) for z ∈ ℝ^{j-1}
        U(1:j-1,j) = z,  v(j:n) = ã(j:n) - L(j:n,1:j-1) · z
    end
    Determine μ with j ≤ μ ≤ n so |v(μ)| = ‖v(j:n)‖_∞ and set piv(j) = μ
    v(j) ↔ v(μ),  L(j,1:j-1) ↔ L(μ,1:j-1),  U(j,j) = v(j)
    if v(j) ≠ 0
        L(j+1:n,j) = v(j+1:n)/v(j)
    end
end
```
The interchanges recorded so far are applied to `A(:,j)` by the `piv` loop (`applyPiv`, the
entries at and after `j` still the identity); the triangular solve and the gaxpy are the row
loop of running differences of Algorithm 3.2.2. The state is `(L, U, piv)`. -/
noncomputable def algorithm_3_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) :=
  (List.finRange n).foldlM
    (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × (Fin n → Fin n)) j => do
      let v ← (List.finRange n).foldlM (fun (v : Fin n → ℝ) i => do
        let vi ← ((List.finRange n).filter (fun r => r < i ∧ r < j)).foldlM (fun (c : ℝ) r => do
          let p ← rnd (st.1 i r * v r)
          rnd (c - p)) (applyPiv st.2.2 (fun i => A i j) i)
        pure (Function.update v i vi)) (applyPiv st.2.2 fun i => A i j)
      if v (Equiv.swap j (firstMaxIndex v j) j) ≠ 0 then do
        let L ← ((List.finRange n).filter (j < ·)).foldlM
          (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
            let l ← rnd (v (Equiv.swap j (firstMaxIndex v j) i) /
              v (Equiv.swap j (firstMaxIndex v j) j))
            pure (L.updateRow i (Function.update (L i) j l)))
          (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c)
        pure (L, st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i)
          else 0), Function.update st.2.2 j (firstMaxIndex v j))
      else
        pure (of fun i c => if c < j then st.1 (Equiv.swap j (firstMaxIndex v j) i) c else st.1 i c,
          st.2.1.updateCol j (fun i => if i ≤ j then v (Equiv.swap j (firstMaxIndex v j) i) else 0),
          Function.update st.2.2 j (firstMaxIndex v j))) (1, 0, fun k => k)

/-- §3.4.5, the matrix of the `2^{n-1}` example: `a_ij = 1` if `i = j` or `j = n`, `-1` if
`i > j`, `0` otherwise (0-based, `j = n - 1`). -/
noncomputable def growthExample (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j ∨ (j : ℕ) = n - 1 then 1 else if j < i then -1 else 0

/-- §3.4.7, the rook scan:
```
μ = k, λ = k, τ = |a_μλ|, s = 0
while τ < ‖A(k:n,λ)‖_∞ ∨ τ < ‖A(μ,k:n)‖_∞
    if mod(s,2) = 0
        Update μ so that |a_μλ| = ‖A(k:n,λ)‖_∞ with k ≤ μ ≤ n.
    else
        Update λ so that |a_μλ| = ‖A(μ,k:n)‖_∞ with k ≤ λ ≤ n.
    end
    s = s + 1
end
```
The `while` loop is a loop over `List.range fuel` with a `done` flag (convention 3); the updates
choose the first maximizing index (`firstMaxIndex`); comparisons are exact, and nothing is
rounded. Returns `(μ, λ)`. -/
noncomputable def rookPivotSearch (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (fuel : ℕ) :
    Fin n × Fin n :=
  let st := (List.range fuel).foldl (fun (st : Fin n × Fin n × ℕ × Bool) _ =>
    if st.2.2.2 then st
    else if |A st.1 st.2.1| < |A (firstMaxIndex (fun i => A i st.2.1) k) st.2.1| ∨
        |A st.1 st.2.1| < |A st.1 (firstMaxIndex (fun j => A st.1 j) k)| then
      if st.2.2.1 % 2 = 0 then (firstMaxIndex (fun i => A i st.2.1) k, st.2.1, st.2.2.1 + 1, false)
      else (st.1, firstMaxIndex (fun j => A st.1 j) k, st.2.2.1 + 1, false)
    else (st.1, st.2.1, st.2.2.1, true)) (k, k, 0, false)
  (st.1, st.2.1)

end MorePivoting

/-! ### The factorization of the growth example (§3.4.5) -/

section GrowthExample

variable {n : ℕ}

/-- The unit lower factor of the growth example: `-1` below the diagonal. -/
noncomputable def growthExampleL (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j then 1 else if j < i then -1 else 0

/-- The upper factor of the growth example: the identity except the last column
`u_in = 2^i` (0-based). -/
noncomputable def growthExampleU (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) = n - 1 then 2 ^ (i : ℕ) else if i = j then 1 else 0

/-- `∑_{r < i} 2^r = 2^i - 1` over `Fin n`. -/
private theorem sum_filter_lt_two_pow (i : Fin n) :
    ∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) = 2 ^ (i : ℕ) - 1 := by
  have h : (Finset.univ.filter (· < i)).map Fin.valEmbedding = Finset.range i := by
    ext t
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr
    · intro ht; exact ⟨⟨t, by omega⟩, Fin.lt_def.2 ht, rfl⟩
  have := Finset.sum_map (Finset.univ.filter (· < i)) Fin.valEmbedding fun t => (2 : ℝ) ^ t
  rw [h] at this
  rw [show ∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) =
    ∑ t ∈ Finset.range i, (2 : ℝ) ^ t from this.symm, geom_sum_eq (by norm_num)]
  ring

/-- **§3.4.5, the `2^{n-1}` example**: "`A = LU` and it can be shown that `u_nn = 2^{n-1}`" —
the growth example is `L U` with `L` unit lower triangular with `-1` below the diagonal and `U`
the identity except its last column `u_in = 2^i` (0-based), so `u_nn = 2^{n-1}`. -/
theorem growthExample_isLU :
    IsLU (growthExample n) (growthExampleL n) (growthExampleU n) ∧
      ∀ h : 0 < n, growthExampleU n ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 2 ^ (n - 1) := by
  refine ⟨⟨⟨fun i j hij => ?_, fun i => by simp [growthExampleL]⟩, fun i j hij => ?_, ?_⟩,
    fun h => by simp [growthExampleU]⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [growthExampleL, hij'.ne, not_lt.2 hij'.le]
  · dsimp only [id] at hij
    have hjn : (j : ℕ) ≠ n - 1 := by have := Fin.lt_def.1 hij; have := i.2; omega
    simp [growthExampleU, hjn, (ne_of_lt hij).symm]
  · ext i j
    rw [mul_apply]
    by_cases hj : (j : ℕ) = n - 1
    · have hA : growthExample n i j = 1 := by simp [growthExample, hj]
      rw [hA]
      simp only [growthExampleL, growthExampleU, of_apply, hj, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true, one_mul]
      have hrest : ∑ r ∈ Finset.univ.erase i,
          (if i = r then (1 : ℝ) else if r < i then -1 else 0) * 2 ^ (r : ℕ) =
          -∑ r ∈ Finset.univ.filter (· < i), (2 : ℝ) ^ (r : ℕ) := by
        rw [← Finset.sum_neg_distrib]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (· < i)]
        have h1 : (Finset.univ.erase i).filter (· < i) = Finset.univ.filter (· < i) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
          exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
        rw [h1, Finset.sum_eq_zero (s := (Finset.univ.erase i).filter fun r => ¬ r < i), add_zero]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hr' := (Finset.mem_filter.1 hr).2
          simp [hr'.ne', hr']
        · intro r hr
          obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.1 hr
          have hri : i ≠ r := fun h => (Finset.mem_erase.1 hr₁).1 h.symm
          simp [hri, hr₂]
      rw [hrest, sum_filter_lt_two_pow]
      ring
    · have hA : growthExample n i j = growthExampleL n i j := by
        simp [growthExample, growthExampleL, hj]
      rw [hA]
      simp only [growthExampleU, of_apply, hj, ↓reduceIte, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp

end GrowthExample

/-! ### Underdetermined systems (§3.4.8) -/

section Underdetermined

variable {m p : ℕ}

/-- `[U₁ | U₂]` applied to `[z₁; z₂]` is `U₁ z₁ + U₂ z₂`. -/
theorem fromCols_submatrix_mulVec_append (U₁ : Matrix (Fin m) (Fin m) ℝ)
    (U₂ : Matrix (Fin m) (Fin p) ℝ) (z₁ : Fin m → ℝ) (z₂ : Fin p → ℝ) :
    (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm *ᵥ Fin.append z₁ z₂ =
      U₁ *ᵥ z₁ + U₂ *ᵥ z₂ := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id, Fin.sum_univ_add, Pi.add_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl,
    fromCols_apply_inr, Fin.append_left, Fin.append_right]

/-- **(3.4.11)**: "if `A ∈ ℝ^{m×n}` with `m < n`, `rank(A) = m`, … it is possible to compute an LU
factorization of the form `PAQᵀ = L[U₁ | U₂]` where `P` and `Q` are permutations, `L ∈ ℝ^{m×m}` is
unit lower triangular, and `U₁ ∈ ℝ^{m×m}` is nonsingular and upper triangular" (`n = m + p`,
`PAQᵀ = A.submatrix σ ρ`). Proof at the level of the specification: `m` independent columns are
moved first, and their square block has a pivoted LU factorization. -/
theorem equation_3_4_11 (A : Matrix (Fin m) (Fin (m + p)) ℝ) (hA : A.rank = m) :
    ∃ (σ : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin (m + p))) (L U₁ : Matrix (Fin m) (Fin m) ℝ)
      (U₂ : Matrix (Fin m) (Fin p) ℝ), L.IsUnitLowerTriangular ∧ U₁.IsUpperTriangular ∧
        IsUnit U₁ ∧ A.submatrix σ ρ = L * (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm := by
  classical
  obtain ⟨c, hc⟩ := exists_linearIndependent_col A hA
  have hinj : Function.Injective c := hc.injective.of_comp
  let e : {x // x ∈ Set.range (Fin.castAdd p : Fin m → Fin (m + p))} ≃ {x // x ∈ Set.range c} :=
    (Equiv.ofInjective _ (Fin.castAdd_injective m p)).symm.trans (Equiv.ofInjective c hinj)
  let ρ : Equiv.Perm (Fin (m + p)) := e.extendSubtype
  have hρ : ∀ k, ρ (Fin.castAdd p k) = c k := fun k => by
    have h := e.extendSubtype_apply_of_mem (Fin.castAdd p k) ⟨k, rfl⟩
    rw [h]
    simp [e, Equiv.ofInjective_symm_apply]
  let B : Matrix (Fin m) (Fin m) ℝ := of fun i k => A i (c k)
  have hcol : B.col = A.col ∘ c := by funext k i; rfl
  have hB : IsUnit B := linearIndependent_cols_iff_isUnit.1 (hcol ▸ hc)
  obtain ⟨σ, L, U₁, hLU, -⟩ := exists_permMatrix_mul_isLU B
  have hU₁ : IsUnit U₁ := by
    have hPB : IsUnit (L * U₁) := hLU.mul_eq ▸ (isUnit_permMatrix σ).mul hB
    rw [isUnit_iff_isUnit_det] at hPB ⊢
    rw [det_mul] at hPB
    exact isUnit_of_mul_isUnit_right hPB
  have hLu : IsUnit L := hLU.isUnitLowerTriangular.isUnit
  have hLd : IsUnit L.det := (isUnit_iff_isUnit_det _).1 hLu
  refine ⟨σ, ρ, L, U₁, L⁻¹ * of fun i k => A (σ i) (ρ (Fin.natAdd m k)),
    hLU.isUnitLowerTriangular, hLU.isUpperTriangular, hU₁, ?_⟩
  ext i j
  induction j using Fin.addCases with
  | left k =>
    have h := congrFun (congrFun hLU.mul_eq i) k
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at h
    simp only [submatrix_apply, id, hρ, mul_apply, finSumFinEquiv_symm_apply_castAdd,
      fromCols_apply_inl]
    rw [← mul_apply, h]
    rfl
  | right k =>
    have hX : L * (L⁻¹ * of fun i k => A (σ i) (ρ (Fin.natAdd m k))) =
        of fun i k => A (σ i) (ρ (Fin.natAdd m k)) := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hLd, Matrix.one_mul]
    have h := congrFun (congrFun hX i) k
    simp only [submatrix_apply, id, mul_apply, finSumFinEquiv_symm_apply_natAdd,
      fromCols_apply_inr]
    simp only [mul_apply] at h
    rw [h]
    rfl

/-- **§3.4.8, Steps 1–3**: with the factorization (3.4.11), "`Ax = b ⇔ L(U₁z₁ + U₂z₂) = c`" where
`c = Pb` and `[z₁; z₂] = Qx`, so for every choice of `z₂` the vector `x = Qᵀ[z₁; z₂]` with `Ly = Pb`
and `U₁z₁ = y - U₂z₂` solves `Ax = b` ("setting `z₂ = 0` is a natural choice"). -/
theorem underdetermined_solve {A : Matrix (Fin m) (Fin (m + p)) ℝ} {σ : Equiv.Perm (Fin m)}
    {ρ : Equiv.Perm (Fin (m + p))} {L U₁ : Matrix (Fin m) (Fin m) ℝ} {U₂ : Matrix (Fin m) (Fin p) ℝ}
    (hL : L.IsUnitLowerTriangular) (hU₁ : IsUnit U₁)
    (hA : A.submatrix σ ρ = L * (fromCols U₁ U₂).submatrix id finSumFinEquiv.symm)
    (b : Fin m → ℝ) (z₂ : Fin p → ℝ) :
    A *ᵥ (Fin.append (U₁⁻¹ *ᵥ (L⁻¹ *ᵥ (b ∘ σ) - U₂ *ᵥ z₂)) z₂ ∘ ρ.symm) = b := by
  have hLd : IsUnit L.det := (isUnit_iff_isUnit_det _).1 hL.isUnit
  have hUd : IsUnit U₁.det := (isUnit_iff_isUnit_det _).1 hU₁
  set z := Fin.append (U₁⁻¹ *ᵥ (L⁻¹ *ᵥ (b ∘ σ) - U₂ *ᵥ z₂)) z₂
  have hz : A.submatrix σ ρ *ᵥ z = b ∘ σ := by
    rw [hA, ← mulVec_mulVec, fromCols_submatrix_mulVec_append, mulVec_mulVec,
      mul_nonsing_inv _ hUd, one_mulVec, sub_add_cancel, mulVec_mulVec, mul_nonsing_inv _ hLd,
      one_mulVec]
  funext i
  have h := congrFun hz (σ.symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  rw [← h]
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.apply_symm_apply, Function.comp_apply]
  exact (Fintype.sum_equiv ρ _ _ fun j => by simp).symm

end Underdetermined

/-! ### Where is `L`? (§3.4.3) -/

section WhereIsL

variable {n : ℕ}

/-- Conjugating a Gauss transformation by a permutation fixing the indices up to `k` gives the
Gauss transformation of the permuted Gauss vector: `P (I - τ e_kᵀ) Pᵀ = I - (Pτ) e_kᵀ`. -/
theorem permMatrix_mul_gaussTransformation_mul_transpose {ρ : Equiv.Perm (Fin n)} {k : Fin n}
    (hρ : ∀ r, r ≤ k → ρ r = r) (τ : Fin n → ℝ) :
    ρ.permMatrix ℝ * gaussTransformation τ k * (ρ.permMatrix ℝ)ᵀ =
      gaussTransformation (ρ.permMatrix ℝ *ᵥ τ) k := by
  have hk : ∀ j, ρ j = k ↔ j = k := fun j =>
    ⟨fun h => ρ.injective (h.trans (hρ k le_rfl).symm), fun h => h ▸ hρ k le_rfl⟩
  rw [transpose_permMatrix, permMatrix_mul_mul_permMatrix, permMatrix_mulVec]
  ext i j
  simp only [submatrix_apply, gaussTransformation_apply, one_apply, EmbeddingLike.apply_eq_iff_eq,
    hk j, Function.comp_apply]

/-- **(3.4.5)**: with `P' = Π_{n-1} ⋯ Π_{k+1}` the interchanges of partial pivoting after step `k`
(`σ_{k+1}⁻¹ σ_n`, which fix the indices up to `k`), `M̃_k = P' M_k P'ᵀ` is a Gauss transformation,
`M̃_k = I - τ̃ e_kᵀ` with `τ̃ = P' τ`, for every Gauss vector `τ` of step `k` — in particular for
the multipliers of `M_k`. -/
theorem equation_3_4_5 (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (τ : Fin n → ℝ)
    (hτ : ∀ i, i ≤ k → τ i = 0) :
    IsGaussTransformation (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
        (gemPivotStage A partialPivotRow n).2).permMatrix ℝ * gaussTransformation τ k *
        (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ)ᵀ) k ∧
      ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ * gaussTransformation τ k *
          (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
            (gemPivotStage A partialPivotRow n).2).permMatrix ℝ)ᵀ =
        gaussTransformation (((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
          (gemPivotStage A partialPivotRow n).2).permMatrix ℝ *ᵥ τ) k := by
  have hfix : ∀ r, r ≤ k → ((gemPivotStage A partialPivotRow ((k : ℕ) + 1)).2⁻¹ *
      (gemPivotStage A partialPivotRow n).2) r = r := fun r hr =>
    gemPivotStage_snd_inv_mul_apply A partialPivotRow (fun M k => le_partialPivotRow M k)
      (Nat.succ_le_of_lt k.2) (Nat.lt_succ_of_le (Fin.le_def.1 hr))
  have heq := permMatrix_mul_gaussTransformation_mul_transpose hfix τ
  refine ⟨⟨_, fun i hi => ?_, heq⟩, heq⟩
  rw [permMatrix_mulVec, Function.comp_apply, hfix i hi]
  exact hτ i hi

end WhereIsL

end GolubVanLoan.Chapter03
