import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.Band
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LU.Pivoting
import Numlib.LinearAlgebra.Matrix.Rank
import NumlibSurface.GolubVanLoan.Chapter04.Section02

/-!
# Golub–Van Loan §4.3: banded systems

Surface file for [golub2013matrix] §4.3: the band preservation of the LU factorization (Theorem
4.3.1), band Gaussian elimination and band triangular substitution (Algorithms 4.3.1–4.3.3), band
Gaussian elimination with partial pivoting (Theorem 4.3.2), Hessenberg LU (Algorithm 4.3.4), band
Cholesky (Algorithm 4.3.5), the symmetric positive definite tridiagonal solver (§4.3.6, Algorithm
4.3.6), and the rank structure of the inverse of a band matrix (Theorem 4.3.3).

## Conventions

Real square matrices `A : Matrix (Fin n) (Fin n) ℝ`, 0-based. "Upper bandwidth `q`" is
`Matrix.HasUpperBandwidth A q` and "lower bandwidth `p`" is `Matrix.HasLowerBandwidth A p`
(`a_ij = 0` whenever `j > i + q`, resp. `i > j + p`, by `Matrix.hasUpperBandwidth_iff_fin`); the
book's loop bounds `min(k + p, n)` and `max(1, j − q)` are guards on the index in the filtered
index lists of the programs (algorithm convention 10). "`A(1:k, 1:k)` nonsingular for `k = 1:n−1`"
is `∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)`. The packed LU output is read as chapter 3
reads it (`Chapter03.packedL F = 1 + F.strictLower`, `Chapter03.packedU F = F − F.strictLower`).
Tridiagonal matrices are the backbone's `Matrix.tridiagonalOf` (diagonal `d`, sub- and
superdiagonal) and, for the Thomas recurrences, `Matrix.tridiagonalOfNat` of `ℕ`-indexed
sequences.

The algorithms follow the algorithm conventions of `NumlibSurface/GolubVanLoan` (every product,
difference, quotient and square root through the rounding hook `rnd`; comparisons exact). Their
exact specifications are proved at `M := Id`, `rnd := pure` by loop invariants on the folds
(`foldl_finRange_induction`, `foldl_update_of_nodup`); the book gives no rounding analysis here.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/{Band,LU,LU/Pivoting,Cholesky,Rank}` (Theorems 4.3.1–4.3.3,
the Thomas algorithm), `Numlib/Direct/Substitution`. Theorem 4.3.3 is proved through the nullity
theorem (`Matrix.rank_inv_toBlocks₂₁`), which also gives the equality of ranks the book attributes
to Strang and Nguyen, so the book's limit argument (P4.3.11) is not needed.

## Readings and errata

* Theorem 4.3.1 is false for `L` without the nonsingularity of the leading principal submatrices
  (the book's proof divides by `α`): `[0 1; 0 2] = [1 0; β 1][0 1; 0 2 − β]` for every `β`, and
  this matrix is upper triangular. The lower half carries the hypothesis.
* Algorithm 4.3.6 prints `b(k) = b(k) − β(k−1) · β(k−1)` in its second loop; the forward solve
  `L y = b` it implements is `b(k) = b(k) − β(k−1) · b(k−1)`, which is what the program does.
* Theorem 4.3.2 does not need the nonsingularity of `A`.

## Not formalized here

§4.3.7 (vectorization), §4.3.9 (banded inverses: "assuming `N` is not too big"), band storage,
the flop counts, and the band `L D Lᵀ` ("left to the reader").
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### Loop lemmas in exact arithmetic -/

/-- **The Hoare rule of a `finRange` fold**: an invariant indexed by the step count that holds
initially and is kept by every step holds at the end. -/
theorem foldl_finRange_induction {β : Type} (f : β → Fin n → β) (a : β) (I : ℕ → β → Prop)
    (h0 : I 0 a) (hs : ∀ (k : Fin n) (c : β), I k c → I (k + 1) (f c k)) :
    I n ((List.finRange n).foldl f a) := by
  have := SetM.forall_mem_run_foldlM_finRange (f := fun b k => (pure (f b k) : SetM β)) I h0
    (fun k c hc c' hc' => by rw [SetM.mem_run_pure] at hc'; subst hc'; exact hs k c hc)
  exact this _ (by rw [List.foldlM_pure]; exact SetM.mem_run_pure.2 rfl)

/-- **One entry per step, in exact arithmetic.** Over a duplicate-free list `l`, a fold whose step
`i` replaces entry `i` by `g i y`, a value that reads only entry `i` and the entries outside `l`,
replaces every entry `i ∈ l` by `g i` of the initial state. -/
theorem foldl_update_of_nodup {ι β : Type} [DecidableEq ι] {l : List ι} (hl : l.Nodup)
    (g : ι → (ι → β) → β)
    (hg : ∀ i ∈ l, ∀ y y' : ι → β, (∀ r, r ∉ l → y r = y' r) → y i = y' i → g i y = g i y')
    (y : ι → β) :
    l.foldl (fun y i => Function.update y i (g i y)) y = fun r => if r ∈ l then g r y else y r := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, ih hl' (fun i hi z z' hz hzi => hg i (List.mem_cons_of_mem _ hi) z z'
      (fun r hr => hz r fun h => hr (List.mem_cons_of_mem _ h)) hzi)]
    funext r
    by_cases hr : r ∈ l
    · have hra : r ≠ a := fun h => ha (h ▸ hr)
      rw [ite_eq_left hr, ite_eq_left (List.mem_cons_of_mem _ hr)]
      refine hg r (List.mem_cons_of_mem _ hr) _ _ (fun r' hr' => ?_) ?_
      · rw [Function.update_of_ne fun h => hr' (by rw [h]; exact List.mem_cons_self)]
      · rw [Function.update_of_ne hra]
    · rw [ite_eq_right hr]
      by_cases hra : r = a
      · subst hra
        rw [Function.update_self, ite_eq_left List.mem_cons_self]
      · rw [Function.update_of_ne hra, ite_eq_right fun h => (List.mem_cons.1 h).elim hra hr]

/-- A sum over the indices below `j + 1` (and below `i`) splits off the term `j`. -/
private theorem sum_filter_val_lt_succ (f : Fin n → ℝ) (i j : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < j + 1 ∧ k < i), f k =
      ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < j ∧ k < i), f k + if j < i then f j else 0 := by
  have hterm : (if j < i then f j else 0) =
      ∑ k : Fin n, if k = j then (if j < i then f j else 0) else 0 := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hterm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    by_cases hki : k < i <;> simp [hki]
  · have hk' : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    have : ((k : ℕ) < j + 1) ↔ (k : ℕ) < j := by omega
    simp [this, hk]

/-- A sum over the indices from `j` on (and above `i`) splits off the term `j`. -/
private theorem sum_filter_le_val_split (f : Fin n → ℝ) (i j : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => (j : ℕ) ≤ k ∧ i < k), f k =
      ∑ k ∈ univ.filter (fun k : Fin n => (j : ℕ) + 1 ≤ k ∧ i < k), f k +
        if i < j then f j else 0 := by
  have hterm : (if i < j then f j else 0) =
      ∑ k : Fin n, if k = j then (if i < j then f j else 0) else 0 := by simp
  rw [Finset.sum_filter, Finset.sum_filter, hterm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    by_cases hki : i < k <;> simp [hki]
  · have hk' : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    have : ((j : ℕ) ≤ k) ↔ (j : ℕ) + 1 ≤ k := by omega
    simp [this, hk]

/-! ### §4.3.1 Band LU factorization -/

/-- **Theorem 4.3.1, the upper factor.** "Suppose `A` has an LU factorization `A = LU`. If `A` has
upper bandwidth `q` …, then `U` has upper bandwidth `q`." No further hypothesis is needed. -/
theorem theorem_4_3_1_a {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) {q : ℕ}
    (hq : A.HasUpperBandwidth q) : U.HasUpperBandwidth q :=
  h.hasUpperBandwidth hq

/-- **Theorem 4.3.1, the lower factor.** "If `A` has … lower bandwidth `p`, then … `L` has lower
bandwidth `p`", under the nonsingularity of `A(1:k, 1:k)`, `k = 1:n−1`, which the book's proof
uses and which is necessary: `[0 1; 0 2] = [1 0; β 1][0 1; 0 2 − β]` for every `β`. -/
theorem theorem_4_3_1_b {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p : ℕ}
    (hp : A.HasLowerBandwidth p) : L.HasLowerBandwidth p :=
  h.hasLowerBandwidth hA hp

/-- **Theorem 4.3.1.** "Suppose `A ∈ ℝⁿˣⁿ` has an LU factorization `A = LU`. If `A` has upper
bandwidth `q` and lower bandwidth `p`, then `U` has upper bandwidth `q` and `L` has lower bandwidth
`p`" — with the nonsingularity of `A(1:k, 1:k)`, `k = 1:n−1`, added (see `theorem_4_3_1_b`). -/
theorem theorem_4_3_1 {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) {p q : ℕ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q) :
    U.HasUpperBandwidth q ∧ L.HasLowerBandwidth p :=
  ⟨theorem_4_3_1_a h hq, theorem_4_3_1_b h hA hp⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.3.1 (Band Gaussian Elimination).** "Given `A ∈ ℝⁿˣⁿ` with upper bandwidth `q`
and lower bandwidth `p`, the following algorithm computes the factorization `A = LU`, assuming it
exists. `A(i, j)` is overwritten by `L(i, j)` if `i > j` and by `U(i, j)` otherwise":
```
for k = 1:n−1
    for i = k+1:min{k+p, n}
        A(i, k) = A(i, k)/A(k, k)
    end
    for j = k+1:min{k+q, n}
        for i = k+1:min{k+p, n}
            A(i, j) = A(i, j) − A(i, k) · A(k, j)
        end
    end
end
```
The last pass `k = n` of the fold does nothing (its index lists are empty). -/
noncomputable def algorithm_4_3_1 (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) => do
    let A ← ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let l ← rnd (A i k / A k k)
        pure (A.updateRow i (Function.update (A i) k l))) A
    ((List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldlM
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
            let t ← rnd (A i k * A k j)
            let a ← rnd (A i j - t)
            pure (A.updateRow i (Function.update (A i) j a))) A) A) A

/-- **Algorithm 4.3.2 (Band Forward Substitution).** "Let `L ∈ ℝⁿˣⁿ` be a unit lower triangular
matrix with lower bandwidth `p`. Given `b ∈ ℝⁿ`, the following algorithm overwrites `b` with the
solution to `Lx = b`":
```
for j = 1:n
    for i = j+1:min{j+p, n}
        b(i) = b(i) − L(i, j) · b(j)
    end
end
```
(the column-oriented Algorithm 3.1.3 on the band; no division, `L` being unit). -/
def algorithm_4_3_2 (p : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (b : Fin n → ℝ) (j : Fin n) =>
    ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (b : Fin n → ℝ) (i : Fin n) => do
        let t ← rnd (L i j * b j)
        let v ← rnd (b i - t)
        pure (Function.update b i v)) b) b

/-- **Algorithm 4.3.3 (Band Back Substitution).** "Let `U ∈ ℝⁿˣⁿ` be a nonsingular upper
triangular matrix with upper bandwidth `q`. Given `b ∈ ℝⁿ`, the following algorithm overwrites `b`
with the solution to `Ux = b`":
```
for j = n:−1:1
    b(j) = b(j)/U(j, j)
    for i = max{1, j−q}:j−1
        b(i) = b(i) − U(i, j) · b(j)
    end
end
```
-/
noncomputable def algorithm_4_3_3 (q : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).reverse.foldlM (fun (b : Fin n → ℝ) (j : Fin n) => do
    let v ← rnd (b j / U j j)
    ((List.finRange n).filter (fun i : Fin n => i < j ∧ (j : ℕ) ≤ i + q)).foldlM
      (fun (b : Fin n → ℝ) (i : Fin n) => do
        let t ← rnd (U i j * b j)
        let w ← rnd (b i - t)
        pure (Function.update b i w)) (Function.update b j v)) b

/-- **Algorithm 4.3.5 (Band Cholesky).** "Given a symmetric positive definite `A ∈ ℝⁿˣⁿ` with
bandwidth `p`, the following algorithm computes a lower triangular matrix `G` with lower bandwidth
`p` such that `A = GGᵀ`. For all `i ≥ j`, `G(i, j)` overwrites `A(i, j)`":
```
for j = 1:n
    for k = max(1, j−p):j−1
        λ = min(k+p, n)
        A(j:λ, j) = A(j:λ, j) − A(j, k) · A(j:λ, k)
    end
    λ = min(j+p, n)
    A(j:λ, j) = A(j:λ, j)/sqrt(A(j, j))
end
```
The square root is computed once per column and rounded, and the whole column `A(j:λ, j)`,
diagonal included, is divided by it (the operation order of Algorithm 4.2.1). -/
noncomputable def algorithm_4_3_5 (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let A ← ((List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldlM
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
            let t ← rnd (A j k * A i k)
            let a ← rnd (A i j - t)
            pure (A.updateRow i (Function.update (A i) j a))) A) A
    let s ← rnd (Real.sqrt (A j j))
    ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ j + p)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
        let g ← rnd (A i j / s)
        pure (A.updateRow i (Function.update (A i) j g))) A) A

end Programs

/-! ### §4.3.2 Band triangular system solving -/

/-- The exact run of Algorithm 4.3.2 as a fold. -/
private theorem algorithm_4_3_2_id (p : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_4_3_2 pure p L b) =
      (List.finRange n).foldl (fun (b : Fin n → ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldl
          (fun (b : Fin n → ℝ) (i : Fin n) => Function.update b i (b i - L i j * b j)) b) b := by
  simp only [algorithm_4_3_2, pure_bind, List.foldlM_pure]
  rfl

/-- **Exact correctness of Algorithm 4.3.2**: for a unit lower triangular `L` of lower bandwidth
`p`, the exact run solves `Lx = b`. The skipped updates of the full forward substitution are
products with the zero entries `ℓ_ij`, `i > j + p`. -/
theorem algorithm_4_3_2_spec {p : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsUnitLowerTriangular) (hp : L.HasLowerBandwidth p) (b : Fin n → ℝ) :
    L *ᵥ Id.run (algorithm_4_3_2 pure p L b) = b := by
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  rw [algorithm_4_3_2_id]
  have key := foldl_finRange_induction (fun (b : Fin n → ℝ) (j : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p)).foldl
          (fun (b : Fin n → ℝ) (i : Fin n) => Function.update b i (b i - L i j * b j)) b) b
    (fun c s => ∀ i, s i = b i - ∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < c ∧ k < i),
      L i k * s k)
    (fun i => by simp)
    (fun j s hs i => by
      set l := (List.finRange n).filter (fun i : Fin n => j < i ∧ (i : ℕ) ≤ j + p) with hl
      have hmem : ∀ r, r ∈ l ↔ j < r ∧ (r : ℕ) ≤ j + p := fun r => by simp [hl]
      have hjl : j ∉ l := fun h => lt_irrefl _ ((hmem j).1 h).1
      rw [foldl_update_of_nodup ((List.nodup_finRange n).filter _)
        (fun i y => y i - L i j * y j) (fun i _ y y' hy hyi => by rw [hyi, hy j hjl]) s]
      simp only
      have hs' : ∀ k : Fin n, (k : ℕ) < j + 1 →
          (if k ∈ l then s k - L k j * s j else s k) = s k := fun k hk => by
        rw [ite_eq_right fun h => absurd ((hmem k).1 h).1 (not_lt.2 (Fin.le_def.2 (by omega)))]
      rw [Finset.sum_congr rfl fun k hk => by rw [hs' k (mem_filter.1 hk).2.1],
        sum_filter_val_lt_succ, hs i]
      by_cases hi : i ∈ l
      · rw [ite_eq_left hi, ite_eq_left ((hmem i).1 hi).1]
        ring
      · rw [ite_eq_right hi]
        by_cases hji : j < i
        · have hL0 : L i j = 0 := hp' i j (by
            by_contra h
            exact hi ((hmem i).2 ⟨hji, by omega⟩))
          rw [ite_eq_left hji, hL0, zero_mul, add_zero]
        · rw [ite_eq_right hji, add_zero])
  ext i
  rw [mulVec_apply_of_isLowerTriangular hL.isLowerTriangular, hL.diag_eq_one, one_mul, key i]
  have : univ.filter (fun k : Fin n => (k : ℕ) < n ∧ k < i) = univ.filter (· < i) := by
    ext k; simp
  rw [this]
  ring

/-- The exact run of Algorithm 4.3.3 as a fold along the reversed indices. -/
private theorem algorithm_4_3_3_id (q : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_4_3_3 pure q U b) =
      (List.finRange n).foldl (fun (b : Fin n → ℝ) (c : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => i < c.rev ∧ (c.rev : ℕ) ≤ i + q)).foldl
          (fun (b' : Fin n → ℝ) (i : Fin n) =>
            Function.update b' i (b' i - U i c.rev * b' c.rev))
          (Function.update b c.rev (b c.rev / U c.rev c.rev))) b := by
  simp only [algorithm_4_3_3, pure_bind, List.foldlM_pure, List.finRange_reverse,
    List.foldlM_map]
  rfl

/-- **Exact correctness of Algorithm 4.3.3**: for a nonsingular upper triangular `U` of upper
bandwidth `q`, the exact run solves `Ux = b`. -/
theorem algorithm_4_3_3_spec {q : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (hq : U.HasUpperBandwidth q)
    (b : Fin n → ℝ) : U *ᵥ Id.run (algorithm_4_3_3 pure q U b) = b := by
  have hq' := hasUpperBandwidth_iff_fin.1 hq
  rw [algorithm_4_3_3_id]
  have key := foldl_finRange_induction (fun (b : Fin n → ℝ) (c : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => i < c.rev ∧ (c.rev : ℕ) ≤ i + q)).foldl
          (fun (b' : Fin n → ℝ) (i : Fin n) =>
            Function.update b' i (b' i - U i c.rev * b' c.rev))
          (Function.update b c.rev (b c.rev / U c.rev c.rev))) b
    (fun c s => ∀ i : Fin n, (if n - c ≤ (i : ℕ) then U i i * s i else s i) =
      b i - ∑ k ∈ univ.filter (fun k : Fin n => n - c ≤ (k : ℕ) ∧ i < k), U i k * s k)
    (fun i => by
      have : univ.filter (fun k : Fin n => n - 0 ≤ (k : ℕ) ∧ i < k) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun k _ h => by have := k.isLt; omega
      rw [ite_eq_right (by omega), this, Finset.sum_empty, sub_zero])
    (fun c s hs i => by
      have hc := c.isLt
      set j := c.rev with hj
      have hjv : (j : ℕ) = n - (c + 1) := by rw [hj, Fin.val_rev]
      set l := (List.finRange n).filter (fun i : Fin n => i < j ∧ (j : ℕ) ≤ i + q) with hl
      have hmem : ∀ r, r ∈ l ↔ r < j ∧ (j : ℕ) ≤ r + q := fun r => by simp [hl]
      have hjl : j ∉ l := fun h => lt_irrefl _ ((hmem j).1 h).1
      set s₁ := Function.update s j (s j / U j j) with hs₁
      rw [foldl_update_of_nodup ((List.nodup_finRange n).filter _)
        (fun i y => y i - U i j * y j) (fun i _ y y' hy hyi => by rw [hyi, hy j hjl]) s₁]
      simp only
      -- entries from `j` on are not rewritten by the saxpy
      have hfin : ∀ k : Fin n, (j : ℕ) ≤ k →
          (if k ∈ l then s₁ k - U k j * s₁ j else s₁ k) = s₁ k := fun k hk => by
        rw [ite_eq_right fun h => absurd ((hmem k).1 h).1 (not_lt.2 (Fin.le_def.2 hk))]
      have hsum : ∑ k ∈ univ.filter (fun k : Fin n => n - (c + 1) ≤ (k : ℕ) ∧ i < k),
          U i k * (if k ∈ l then s₁ k - U k j * s₁ j else s₁ k) =
          ∑ k ∈ univ.filter (fun k : Fin n => n - c ≤ (k : ℕ) ∧ i < k), U i k * s k +
            if i < j then U i j * (s j / U j j) else 0 := by
        rw [Finset.sum_congr rfl fun k hk => by
          rw [hfin k (by rw [hjv]; exact (mem_filter.1 hk).2.1)]]
        rw [← hjv, sum_filter_le_val_split]
        congr 1
        · refine Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun k hk => ?_
          have hkj : k ≠ j := fun h => by
            rw [h] at hk; have := (mem_filter.1 hk).2.1; omega
          rw [hs₁, Function.update_of_ne hkj]
        · rw [hs₁, Function.update_self]
      rw [hsum]
      by_cases hij : i = j
      · -- the entry just finished
        subst hij
        have hle : n - (c + 1) ≤ (j : ℕ) := by omega
        have hlt : ¬ n - c ≤ (j : ℕ) := by omega
        rw [ite_eq_left hle, hfin j le_rfl, hs₁, Function.update_self, mul_div_cancel₀ _ (hd j),
          ite_eq_right (lt_irrefl j), add_zero]
        have := hs j
        rwa [ite_eq_right hlt] at this
      · rcases lt_or_gt_of_ne hij with hij | hij
        · -- an entry above: updated by the saxpy
          have hle : ¬ n - (c + 1) ≤ (i : ℕ) := by
            have := Fin.lt_def.1 hij; omega
          have hlt : ¬ n - c ≤ (i : ℕ) := by omega
          rw [ite_eq_right hle, ite_eq_left hij, hs₁, Function.update_of_ne hij.ne]
          have := hs i
          rw [ite_eq_right hlt] at this
          by_cases hi : i ∈ l
          · rw [ite_eq_left hi, Function.update_self, this]
            ring
          · rw [ite_eq_right hi, this]
            have hU0 : U i j = 0 := hq' i j (by
              by_contra h
              exact hi ((hmem i).2 ⟨hij, by omega⟩))
            rw [hU0, zero_mul, add_zero]
        · -- an entry below: finished before
          have hle : n - (c + 1) ≤ (i : ℕ) := by have := Fin.lt_def.1 hij; omega
          have hlt : n - c ≤ (i : ℕ) := by have := Fin.lt_def.1 hij; omega
          rw [ite_eq_left hle, hfin i (Fin.le_def.1 hij.le), hs₁, Function.update_of_ne hij.ne',
            ite_eq_right (not_lt.2 hij.le), add_zero]
          have := hs i
          rwa [ite_eq_left hlt] at this)
  ext i
  rw [mulVec_apply_of_isUpperTriangular hU]
  have h := key i
  rw [ite_eq_left (by omega)] at h
  have : univ.filter (fun k : Fin n => n - n ≤ (k : ℕ) ∧ i < k) = univ.filter (i < ·) := by
    ext k; simp
  rw [this] at h
  rw [h]
  ring

/-! ### §4.3.6 Tridiagonal system solving -/

/-- **§4.3.6, the `L D Lᵀ` factorization of a symmetric tridiagonal matrix.** For the symmetric
tridiagonal matrix with diagonal `a` and off-diagonal `e` (`e k` at `(k + 1, k)` and `(k, k + 1)`),
"we deduce from the equation `A = LDLᵀ` that `d_1 = a_11`, `ℓ_{k−1} = a_{k,k−1}/d_{k−1}`,
`d_k = a_kk − ℓ_{k−1} a_{k,k−1}`": these are the Thomas recurrences `Matrix.thomasAlpha` (the
`d_k`) and `Matrix.thomasBeta` (the `ℓ_k`) with equal off-diagonals, and whenever the pivots used
as divisors are nonzero, `A = L D Lᵀ` with `L` the unit lower bidiagonal `Matrix.thomasLower` and
`D = diag(d)`. -/
theorem tridiagonal_ldlt (a e : ℕ → ℝ) (m : ℕ)
    (hd : ∀ i, i + 1 < m → thomasAlpha a (fun i => e (i - 1)) e i ≠ 0) :
    IsLDM (tridiagonalOfNat a (fun i => e (i - 1)) e m) (thomasLower a (fun i => e (i - 1)) e m)
      (diagonal fun i => thomasAlpha a (fun i => e (i - 1)) e i)
      (thomasLower a (fun i => e (i - 1)) e m) := by
  have h := isLU_tridiagonal_thomas a (fun i => e (i - 1)) e hd
  have hU : diagonal (fun i : Fin m => thomasAlpha a (fun i => e (i - 1)) e i) *
      (thomasLower a (fun i => e (i - 1)) e m)ᵀ = thomasUpper a (fun i => e (i - 1)) e m := by
    ext i j
    rw [diagonal_mul, transpose_apply]
    simp only [thomasLower, thomasUpper, of_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
      by_cases h1 : (i : ℕ) + 1 = j
      · rw [ite_eq_left h1, ite_eq_left h1, ← h1, thomasBeta_succ, Nat.add_sub_cancel,
          mul_div_cancel₀ _ (hd i (by omega))]
      · rw [ite_eq_right h1, ite_eq_right h1, mul_zero]
  exact ⟨h.isUnitLowerTriangular, isDiag_diagonal _, h.isUnitLowerTriangular,
    by rw [Matrix.mul_assoc, hU, h.mul_eq]⟩

/-- The pivots `d_k` of a positive definite symmetric tridiagonal matrix are positive: the leading
blocks are positive definite and are `L D Lᵀ` with the leading pivots (`tridiagonal_ldlt`). -/
theorem thomasAlpha_pos_of_posDef (a e : ℕ → ℝ) (m : ℕ)
    (hA : (tridiagonalOfNat a (fun i => e (i - 1)) e m).PosDef) :
    ∀ i, i < m → 0 < thomasAlpha a (fun i => e (i - 1)) e i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hsub : tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1) =
      (tridiagonalOfNat a (fun i => e (i - 1)) e m).submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext r c
    simp [tridiagonalOfNat]
  have hP : (tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1)).PosDef := by
    rw [hsub]
    exact hA.submatrix (Fin.castLE_injective hi)
  have hL := tridiagonal_ldlt a e (i + 1) fun j hj => (ih j (by omega) (by omega)).ne'
  have hL' : IsLDM (tridiagonalOfNat a (fun i => e (i - 1)) e (i + 1))
      (thomasLower a (fun i => e (i - 1)) e (i + 1))
      (diagonal fun i : Fin (i + 1) => thomasAlpha a (fun i => e (i - 1)) e i)
      (thomasLower a (fun i => e (i - 1)) e (i + 1))ᴴᵀ := by
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  have := hL'.posDef_iff.1 hP (Fin.last i)
  simpa using this

/-- The `ℕ`-indexed sequence of a vector, zero past its end. -/
private def natSeq {N : ℕ} (v : Fin N → ℝ) : ℕ → ℝ := fun i => if h : i < N then v ⟨i, h⟩ else 0

@[simp]
private theorem natSeq_val {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : natSeq v i = v i := by
  simp [natSeq]

/-- The unit lower bidiagonal factor on a vector: `(L x)_0 = x_0`,
`(L x)_{k+1} = x_{k+1} + ℓ_k x_k`. -/
private theorem thomasLower_mulVec_zero {N : ℕ} (a b c : ℕ → ℝ) (x : Fin (N + 1) → ℝ) :
    (thomasLower a b c (N + 1) *ᵥ x) 0 = x 0 := by
  rw [mulVec, dotProduct, Finset.sum_eq_single 0 (fun r _ hr => ?_) (by simp)]
  · simp [thomasLower]
  · simp [thomasLower, Ne.symm hr]

private theorem thomasLower_mulVec_succ {N : ℕ} (a b c : ℕ → ℝ) (x : Fin (N + 1) → ℝ)
    (k : Fin N) :
    (thomasLower a b c (N + 1) *ᵥ x) k.succ =
      x k.succ + thomasBeta a b c (k + 1) * x k.castSucc := by
  rw [mulVec, dotProduct, Fintype.sum_eq_add k.succ k.castSucc (Fin.castSucc_lt_succ (i := k)).ne'
    (fun r hr => ?_)]
  · simp [thomasLower, (Fin.castSucc_lt_succ (i := k)).ne']
  · have h2 : (r : ℕ) ≠ k := fun h => hr.2 (Fin.ext (by simp [h]))
    simp [thomasLower, Ne.symm hr.1, h2]

/-- The transposed factor on a vector: `(Lᵀ x)_n = x_n`, `(Lᵀ x)_k = x_k + ℓ_k x_{k+1}`. -/
private theorem thomasLower_transpose_mulVec_last {N : ℕ} (a b c : ℕ → ℝ)
    (x : Fin (N + 1) → ℝ) : ((thomasLower a b c (N + 1))ᵀ *ᵥ x) (Fin.last N) = x (Fin.last N) := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (Fin.last N) (fun r _ hr => ?_) (by simp)]
  · simp [thomasLower]
  · have : ¬ ((N : ℕ) + 1 = r) := by omega
    simp [thomasLower, hr, this]

private theorem thomasLower_transpose_mulVec_castSucc {N : ℕ} (a b c : ℕ → ℝ)
    (x : Fin (N + 1) → ℝ) (k : Fin N) :
    ((thomasLower a b c (N + 1))ᵀ *ᵥ x) k.castSucc =
      x k.castSucc + thomasBeta a b c (k + 1) * x k.succ := by
  rw [mulVec, dotProduct, Fintype.sum_eq_add k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).ne
    (fun r hr => ?_)]
  · simp [thomasLower, (Fin.castSucc_lt_succ (i := k)).ne']
  · have h1 : ¬ (k : ℕ) + 1 = r := fun h => hr.2 (Fin.ext (by simp; omega))
    simp [thomasLower, hr.1, h1]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.3.6 (Symmetric, Tridiagonal, Positive Definite System Solver).** "Given an
`n`-by-`n` symmetric, tridiagonal, positive definite matrix `A` and `b ∈ ℝⁿ`, the following
algorithm overwrites `b` with the solution to `Ax = b`. It is assumed that the diagonal of `A` is
stored in `α(1:n)` and the superdiagonal in `β(1:n−1)`":
```
for k = 2:n
    t = β(k−1), β(k−1) = t/α(k−1), α(k) = α(k) − t · β(k−1)
end
for k = 2:n
    b(k) = b(k) − β(k−1) · b(k−1)
end
b(n) = b(n)/α(n)
for k = n−1:−1:1
    b(k) = b(k)/α(k) − β(k) · b(k+1)
end
```
With `n = N + 1`, the diagonal is `α : Fin (N + 1) → ℝ` and the superdiagonal `β : Fin N → ℝ`. The
book prints the second loop as `b(k) = b(k) − β(k−1) · β(k−1)`, a misprint for the forward solve
`b(k) = b(k) − β(k−1) · b(k−1)`, which the program follows. -/
noncomputable def algorithm_4_3_6 {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (b : Fin (N + 1) → ℝ) : M (Fin (N + 1) → ℝ) := do
  let s ← (List.finRange N).foldlM
    (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) => do
      let l ← rnd (s.2 k / s.1 k.castSucc)
      let t ← rnd (s.2 k * l)
      let d ← rnd (s.1 k.succ - t)
      pure (Function.update s.1 k.succ d, Function.update s.2 k l)) (α, β)
  let y ← (List.finRange N).foldlM (fun (y : Fin (N + 1) → ℝ) (k : Fin N) => do
      let t ← rnd (s.2 k * y k.castSucc)
      let v ← rnd (y k.succ - t)
      pure (Function.update y k.succ v)) b
  let z ← rnd (y (Fin.last N) / s.1 (Fin.last N))
  (List.finRange N).reverse.foldlM (fun (x : Fin (N + 1) → ℝ) (k : Fin N) => do
      let q ← rnd (x k.castSucc / s.1 k.castSucc)
      let t ← rnd (s.2 k * x k.succ)
      let v ← rnd (q - t)
      pure (Function.update x k.castSucc v)) (Function.update y (Fin.last N) z)

end Programs

/-- The exact run of Algorithm 4.3.6 as three folds. -/
private theorem algorithm_4_3_6_id {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (b : Fin (N + 1) → ℝ) :
    Id.run (algorithm_4_3_6 pure α β b) =
      (fun s : (Fin (N + 1) → ℝ) × (Fin N → ℝ) =>
        (fun y : Fin (N + 1) → ℝ =>
          (List.finRange N).foldl (fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
            Function.update x c.rev.castSucc
              (x c.rev.castSucc / s.1 c.rev.castSucc - s.2 c.rev * x c.rev.succ))
            (Function.update y (Fin.last N) (y (Fin.last N) / s.1 (Fin.last N))))
        ((List.finRange N).foldl (fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
          Function.update y k.succ (y k.succ - s.2 k * y k.castSucc)) b))
      ((List.finRange N).foldl (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
        (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
          Function.update s.2 k (s.2 k / s.1 k.castSucc))) (α, β)) := by
  simp only [algorithm_4_3_6, pure_bind, List.foldlM_pure, List.finRange_reverse,
    List.foldlM_map]
  rfl

/-- **Exact correctness of Algorithm 4.3.6**: if the symmetric tridiagonal matrix
`A = tridiag(β, α, β)` is positive definite, the exact run solves `Ax = b`. The first loop computes
the `d_k` and `ℓ_k` of `tridiagonal_ldlt`, the second solves `L y = b`, the last two solve
`D Lᵀ x = y` in the combined form `x_k = y_k/d_k − ℓ_k x_{k+1}`; then `ldlt_solve`. -/
theorem algorithm_4_3_6_spec {N : ℕ} (α : Fin (N + 1) → ℝ) (β : Fin N → ℝ)
    (hA : (tridiagonalOf β α β).PosDef) (b : Fin (N + 1) → ℝ) :
    tridiagonalOf β α β *ᵥ Id.run (algorithm_4_3_6 pure α β b) = b := by
  set a := natSeq α with ha
  set e := natSeq β with he
  have hT : tridiagonalOf β α β = tridiagonalOfNat a (fun i => e (i - 1)) e (N + 1) := by
    rw [tridiagonalOfNat_eq_tridiagonalOf]
    congr 1 <;> funext i <;> simp [ha, he]
  set d : Fin (N + 1) → ℝ := fun i => thomasAlpha a (fun i => e (i - 1)) e i with hd
  set ℓ : Fin N → ℝ := fun k => thomasBeta a (fun i => e (i - 1)) e (k + 1) with hℓ
  have hpos : ∀ i, 0 < d i := fun i =>
    thomasAlpha_pos_of_posDef a e (N + 1) (hT ▸ hA) i i.isLt
  have hℓ' : ∀ k : Fin N, ℓ k = β k / d k.castSucc := fun k => by
    simp [hℓ, hd, thomasBeta_succ, he]
  -- the first loop computes the pivots and the multipliers
  have h1 := foldl_finRange_induction (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
      (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
        Function.update s.2 k (s.2 k / s.1 k.castSucc))) (α, β)
    (fun c s => (∀ i : Fin (N + 1), s.1 i = if (i : ℕ) ≤ c then d i else α i) ∧
      ∀ k : Fin N, s.2 k = if (k : ℕ) < c then ℓ k else β k)
    ⟨fun i => by
      change α i = if (i : ℕ) ≤ 0 then d i else α i
      rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
      · have : i = 0 := Fin.ext hi
        subst this
        simp [hd, ha, natSeq]
      · rw [ite_eq_right (by omega)],
     fun k => by simp⟩
    (fun k s hs => by
      obtain ⟨hs1, hs2⟩ := hs
      have hk2 : s.2 k = β k := by rw [hs2, ite_eq_right (lt_irrefl _)]
      have hk1 : s.1 k.castSucc = d k.castSucc := by rw [hs1, ite_eq_left (by simp)]
      have hk1' : s.1 k.succ = α k.succ := by rw [hs1, ite_eq_right (by simp)]
      refine ⟨fun i => ?_, fun k' => ?_⟩
      · dsimp only
        by_cases hik : i = k.succ
        · subst hik
          rw [Function.update_self, ite_eq_left (by simp), hk1', hk2, hk1]
          have ha1 : a ((k : ℕ) + 1) = α k.succ := by
            simp only [ha, natSeq, dite_eq_left (Nat.succ_lt_succ k.isLt)]
            rfl
          have he1 : e (k : ℕ) = β k := by rw [he, natSeq_val]
          simp only [hd, Fin.val_succ, Fin.val_castSucc, thomasAlpha_succ, thomasBeta_succ,
            Nat.add_sub_cancel, ha1, he1]
          ring
        · rw [Function.update_of_ne hik, hs1]
          have : (i : ℕ) ≠ k + 1 := fun h => hik (Fin.ext (by simp [h]))
          by_cases hi : (i : ℕ) ≤ k
          · rw [ite_eq_left hi, ite_eq_left (by omega)]
          · rw [ite_eq_right hi, ite_eq_right (by omega)]
      · dsimp only
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self, ite_eq_left (by omega), hk2, hk1, hℓ']
        · rw [Function.update_of_ne hk, hs2]
          have : (k' : ℕ) ≠ k := fun h => hk (Fin.ext h)
          by_cases hk' : (k' : ℕ) < k
          · rw [ite_eq_left hk', ite_eq_left (by omega)]
          · rw [ite_eq_right hk', ite_eq_right (by omega)])
  have hs : (List.finRange N).foldl (fun (s : (Fin (N + 1) → ℝ) × (Fin N → ℝ)) (k : Fin N) =>
      (Function.update s.1 k.succ (s.1 k.succ - s.2 k * (s.2 k / s.1 k.castSucc)),
        Function.update s.2 k (s.2 k / s.1 k.castSucc))) (α, β) = (d, ℓ) := by
    refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
    · rw [h1.1 i, ite_eq_left (by omega)]
    · rw [h1.2 k, ite_eq_left k.isLt]
  rw [algorithm_4_3_6_id, hs]
  dsimp only
  -- the second loop solves `L y = b`
  set y := (List.finRange N).foldl (fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
    Function.update y k.succ (y k.succ - ℓ k * y k.castSucc)) b with hy
  have h2 := foldl_finRange_induction (fun (y : Fin (N + 1) → ℝ) (k : Fin N) =>
      Function.update y k.succ (y k.succ - ℓ k * y k.castSucc)) b
    (fun c y => y 0 = b 0 ∧ (∀ k : Fin N, (k : ℕ) < c → y k.succ + ℓ k * y k.castSucc = b k.succ) ∧
      ∀ k : Fin N, c ≤ (k : ℕ) → y k.succ = b k.succ)
    ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl⟩
    (fun k y hy => by
      obtain ⟨hy0, hy1, hy2⟩ := hy
      refine ⟨by rw [Function.update_of_ne (Fin.succ_ne_zero k).symm]; exact hy0,
        fun k' hk' => ?_, fun k' hk' => ?_⟩
      · by_cases hkk : k' = k
        · subst hkk
          rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ (i := k')).ne,
            hy2 k' le_rfl]
          ring
        · have hlt : (k' : ℕ) < k := by
            have : (k' : ℕ) ≠ k := fun h => hkk (Fin.ext h); omega
          rw [Function.update_of_ne (fun h => hkk (Fin.succ_injective _ h)),
            Function.update_of_ne (fun h => by
              have := congrArg Fin.val h; simp at this; omega)]
          exact hy1 k' hlt
      · have hkk : k' ≠ k := fun h => by rw [h] at hk'; omega
        rw [Function.update_of_ne (fun h => hkk (Fin.succ_injective _ h))]
        exact hy2 k' (by omega))
  have hLy : thomasLower a (fun i => e (i - 1)) e (N + 1) *ᵥ y = b := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [thomasLower_mulVec_zero]; exact h2.1
    · rw [thomasLower_mulVec_succ]; exact h2.2.1 k k.isLt
  -- the last two loops solve `D Lᵀ x = y`
  have h3 := foldl_finRange_induction (fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
      Function.update x c.rev.castSucc
        (x c.rev.castSucc / d c.rev.castSucc - ℓ c.rev * x c.rev.succ))
    (Function.update y (Fin.last N) (y (Fin.last N) / d (Fin.last N)))
    (fun c x => x (Fin.last N) = y (Fin.last N) / d (Fin.last N) ∧
      (∀ k : Fin N, N - c ≤ (k : ℕ) →
        x k.castSucc = y k.castSucc / d k.castSucc - ℓ k * x k.succ) ∧
      ∀ k : Fin N, (k : ℕ) < N - c → x k.castSucc = y k.castSucc)
    ⟨by rw [Function.update_self], fun k hk => absurd k.isLt (by omega),
      fun k _ => by rw [Function.update_of_ne (Fin.castSucc_lt_last k).ne]⟩
    (fun c x hx => by
      obtain ⟨hx0, hx1, hx2⟩ := hx
      have hcv : (c.rev : ℕ) = N - 1 - c := by rw [Fin.val_rev]; omega
      refine ⟨by rw [Function.update_of_ne (Fin.castSucc_lt_last _).ne']; exact hx0,
        fun k hk => ?_, fun k hk => ?_⟩
      · by_cases hkk : k = c.rev
        · subst hkk
          rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_succ).ne',
            hx2 _ (by omega)]
        · have hk' : N - c ≤ (k : ℕ) := by
            have : (k : ℕ) ≠ c.rev := fun h => hkk (Fin.ext h); omega
          rw [Function.update_of_ne (fun h => hkk (Fin.castSucc_injective _ h)),
            Function.update_of_ne (fun h => by
              have := congrArg Fin.val h; simp at this; omega)]
          exact hx1 k hk'
      · have hkk : k ≠ c.rev := fun h => by rw [h] at hk; omega
        rw [Function.update_of_ne (fun h => hkk (Fin.castSucc_injective _ h))]
        exact hx2 k (by omega))
  set x := (List.finRange N).foldl (fun (x : Fin (N + 1) → ℝ) (c : Fin N) =>
      Function.update x c.rev.castSucc
        (x c.rev.castSucc / d c.rev.castSucc - ℓ c.rev * x c.rev.succ))
    (Function.update y (Fin.last N) (y (Fin.last N) / d (Fin.last N))) with hx
  have hLx : (thomasLower a (fun i => e (i - 1)) e (N + 1))ᵀ *ᵥ x = fun i => y i / d i := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [thomasLower_transpose_mulVec_last]; exact h3.1
    · rw [thomasLower_transpose_mulVec_castSucc, h3.2.1 k (by omega)]
      simp only [hℓ]
      ring
  have hDy : diagonal d *ᵥ (fun i => y i / d i) = y := by
    funext i
    rw [mulVec_diagonal, mul_div_cancel₀ _ (hpos i).ne']
  rw [hT]
  exact ldlt_solve (tridiagonal_ldlt a e (N + 1) fun i hi => (hpos ⟨i, by omega⟩).ne') hLy hDy hLx

/-! ### §4.3.3 Band Gaussian elimination with pivoting -/

/-- **Theorem 4.3.2.** "Suppose `A ∈ ℝⁿˣⁿ` … has upper and lower bandwidths `q` and `p`,
respectively. If Gaussian elimination with partial pivoting is used to compute Gauss
transformations `M_j = I − α^{(j)} e_jᵀ` and permutations `P_1, …, P_{n−1}` such that
`M_{n−1} P_{n−1} ⋯ M_1 P_1 A = U` is upper triangular, then `U` has upper bandwidth `p + q` and
`α^{(j)}_i = 0` whenever `i ≤ j` or `i > j + p`." Gaussian elimination with partial pivoting is the
backbone's `Matrix.gemPivotStage A Matrix.partialPivotRow`, and the Gauss vector of stage `k` is
column `k` of `Matrix.elimMultipliers` of the interchanged stage-`k` matrix. The book's
nonsingularity of `A` is not needed. -/
theorem theorem_4_3_2 {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ} (hp : A.HasLowerBandwidth p)
    (hq : A.HasUpperBandwidth q) :
    (gemPivotStage A partialPivotRow n).1.HasUpperBandwidth (p + q) ∧
      ∀ (k : ℕ) (hk : k < n) (i : Fin n), (i : ℕ) ≤ k ∨ k + p < i → ∀ j,
        elimMultipliers ((gemPivotStage A partialPivotRow k).1.submatrix
          (gemPivotSwap A partialPivotRow k hk) id) ⟨k, hk⟩ i j = 0 :=
  ⟨gemPivotStage_partialPivotRow_hasUpperBandwidth hp hq,
    fun _ hk _ hi j => gemPivotStage_partialPivotRow_multiplier_eq_zero hp hq hk hi j⟩

/-! ### §4.3.4 Hessenberg LU -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **One pass `k` of Algorithm 4.3.4** on the state `(H, piv)`: for `k + 1 < n`,
```
if |H(k, k)| < |H(k+1, k)|
    piv(k) = 1; H(k, k:n) ↔ H(k+1, k:n)
else
    piv(k) = 0
end
if H(k, k) ≠ 0
    τ = H(k+1, k)/H(k, k)
    H(k+1, k+1:n) = H(k+1, k+1:n) − τ · H(k, k+1:n)
    H(k+1, k) = τ
end
```
The interchange of the two row segments and the comparisons are exact; the last pass `k = n`
does nothing. -/
noncomputable def hessenbergLUStep (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) (k : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) :=
  if h : (k : ℕ) + 1 < n then
    let k₁ : Fin n := ⟨k + 1, h⟩
    let s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ) :=
      if |s.1 k k| < |s.1 k₁ k| then
        (Matrix.of fun i j => if k ≤ j ∧ i = k then s.1 k₁ j
          else if k ≤ j ∧ i = k₁ then s.1 k j else s.1 i j, Function.update s.2 k 1)
      else (s.1, Function.update s.2 k 0)
    if s.1 k k ≠ 0 then do
      let τ ← rnd (s.1 k₁ k / s.1 k k)
      let r ← ((List.finRange n).filter (k < ·)).foldlM
        (fun (r : Fin n → ℝ) (j : Fin n) => do
          let t ← rnd (τ * s.1 k j)
          let v ← rnd (r j - t)
          pure (Function.update r j v)) (s.1 k₁)
      pure (s.1.updateRow k₁ (Function.update r k τ), s.2)
    else pure s
  else pure s

/-- **Algorithm 4.3.4 (Hessenberg LU).** "Given an upper Hessenberg matrix `H ∈ ℝⁿˣⁿ`, the
following algorithm computes the upper triangular matrix `M_{n−1} P_{n−1} ⋯ M_1 P_1 H = U` where
each `P_k` is a permutation and each `M_k` is a Gauss transformation whose entries are bounded by
unity. `H(i, k)` is overwritten with `U(i, k)` if `i ≤ k` and by `−[M_k]_{k+1,k}` if `i = k + 1`.
An integer vector `piv(1:n−1)` encodes the permutations. If `P_k = I`, then `piv(k) = 0`. If `P_k`
interchanges rows `k` and `k + 1`, then `piv(k) = 1`": the passes `hessenbergLUStep` for
`k = 1:n−1`, on the state `(H, piv)` with `piv` initially `0`. -/
noncomputable def algorithm_4_3_4 (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) :=
  (List.finRange n).foldlM (hessenbergLUStep rnd) (H, 0)

end Programs

/-- The loop invariant of Algorithm 4.3.4 after `c` passes: on and above the diagonal and in the
columns from `c` on, the state is the matrix of stage `c` of Gaussian elimination with partial
pivoting; the stored multipliers of the passes before `c` are bounded by one; the recorded
interchanges are those of partial pivoting. -/
private def HessInv (H : Matrix (Fin n) (Fin n) ℝ) (c : ℕ)
    (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) : Prop :=
  (∀ i j : Fin n, (c ≤ (j : ℕ) ∨ i ≤ j) → s.1 i j = (gemPivotStage H partialPivotRow c).1 i j) ∧
  (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n), (k : ℕ) < c → |s.1 ⟨k + 1, hk⟩ k| ≤ 1) ∧
  (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n), (k : ℕ) < c →
    (s.2 k = 1 ↔ partialPivotRow (gemPivotStage H partialPivotRow k).1 k = ⟨k + 1, hk⟩))

/-- Stage `k + 1` of partial pivoting at a pivot index `k : Fin n`. -/
private theorem gemPivotStage_succ_fin (H : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 =
      elimStep ((gemPivotStage H partialPivotRow k).1.submatrix
        (Equiv.swap k (partialPivotRow (gemPivotStage H partialPivotRow k).1 k)) id) k := by
  rw [gemPivotStage_succ_of_lt H partialPivotRow k.isLt]
  rfl

/-- One pass of Algorithm 4.3.4 keeps the invariant. -/
private theorem hessInv_step {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg)
    (k : Fin n) (s : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ)) (hs : HessInv H k s) :
    HessInv H (k + 1) (Id.run (hessenbergLUStep pure s k)) := by
  obtain ⟨S, piv⟩ := s
  obtain ⟨hS, hmul, hpiv⟩ := hs
  simp only at hS hmul hpiv
  set G := (gemPivotStage H partialPivotRow k).1 with hG
  have hG' := gemPivotStage_succ_fin H k
  rw [← hG] at hG'
  set r := partialPivotRow G k with hr
  have hkr : k ≤ r := le_partialPivotRow G k
  -- below the subdiagonal the pivot column of stage `k` is still that of `H`
  have hcol : ∀ i : Fin n, (k : ℕ) + 1 < i → G i k = 0 := fun i hi => by
    rw [hG, (gemPivotStage_partialPivotRow_isUpperHessenberg_invariant hH k).1 i k (by omega)]
    exact hH i k ⟨⟨k + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩
  have hrle : (r : ℕ) ≤ k + 1 := partialPivotRow_le_succ G k hcol
  unfold hessenbergLUStep
  by_cases hk : (k : ℕ) + 1 < n
  swap
  · -- the last pass does nothing, and neither does the last stage
    rw [dite_eq_right hk]
    have hrk : r = k := le_antisymm (Fin.le_def.2 (by have := r.isLt; omega)) hkr
    have hGk : (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 = G := by
      ext i j
      rw [hG', hrk, Equiv.swap_self, Equiv.coe_refl, submatrix_id_id,
        elimStep_apply_of_not_lt _ fun h => by have := Fin.lt_def.1 h; omega]
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_⟩
    · rw [hGk]
      exact hS i j (hij.imp (fun h => by have := j.isLt; omega) id)
    · exact hmul k' hk' (by omega)
    · exact hpiv k' hk' (by omega)
  rw [dite_eq_left hk]
  set k₁ : Fin n := ⟨k + 1, hk⟩ with hk₁
  have hkk₁ : k < k₁ := Fin.lt_def.2 (by simp [hk₁])
  have hSk : S k k = G k k := hS k k (Or.inr le_rfl)
  have hSk₁ : S k₁ k = G k₁ k := hS k₁ k (Or.inl le_rfl)
  -- the pivot row of partial pivoting is `k₁` exactly when the book interchanges
  have hswap_iff : r = k₁ ↔ |G k k| < |G k₁ k| := by
    constructor
    · intro hrk₁
      by_contra hle
      have hmax : ∀ r', k ≤ r' → ‖G r' k‖ ≤ ‖G k k‖ := fun r' hr' => by
        rcases eq_or_lt_of_le hr' with rfl | hr'
        · exact le_rfl
        · rcases eq_or_lt_of_le (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hr')) :
            k₁ ≤ r') with rfl | hr''
          · simpa [Real.norm_eq_abs] using not_lt.1 hle
          · rw [hcol r' (Fin.lt_def.1 hr''), norm_zero]
            exact norm_nonneg _
      have := partialPivotRow_le G k le_rfl hmax
      rw [← hr, hrk₁] at this
      exact absurd this (not_le.2 hkk₁)
    · intro hlt
      refine Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (lt_of_le_of_ne (Fin.le_def.1 hkr)
        fun h => ?_)))
      have hrk : r = k := Fin.ext h.symm
      have := norm_apply_le_partialPivotRow G k hkk₁.le
      rw [← hr, hrk, Real.norm_eq_abs, Real.norm_eq_abs] at this
      exact absurd hlt (not_lt.2 this)
  -- the interchanged matrix of stage `k`
  set Mx := G.submatrix (Equiv.swap k r) id with hMx
  have hMk : |Mx k₁ k| ≤ |Mx k k| := by
    have h1 := norm_apply_le_partialPivotRow G k hkk₁.le
    have h2 := norm_apply_le_partialPivotRow G k (le_refl k)
    rw [← hr, Real.norm_eq_abs, Real.norm_eq_abs] at h1 h2
    simp only [hMx, submatrix_apply, id, Equiv.swap_apply_left]
    rcases (show r = k ∨ r = k₁ from by
      rcases eq_or_lt_of_le hkr with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (Fin.lt_def.1 h)))))
      with h | h
    · rw [h, Equiv.swap_self, Equiv.refl_apply]
      rw [h] at h1
      exact h1
    · rw [h, Equiv.swap_apply_right]
      rw [h] at h2
      exact h2
  -- the row interchange of the program realizes `Mx` on the relevant entries
  set s₁ : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℕ) :=
    if |S k k| < |S k₁ k| then
      (Matrix.of fun i j => if k ≤ j ∧ i = k then S k₁ j
        else if k ≤ j ∧ i = k₁ then S k j else S i j, Function.update piv k 1)
    else (S, Function.update piv k 0) with hs₁
  have hS₁ : ∀ i j : Fin n, ((k : ℕ) ≤ j ∨ i ≤ j) → s₁.1 i j = Mx i j := by
    intro i j hij
    by_cases hsw : |S k k| < |S k₁ k|
    · have hrk₁ : r = k₁ := hswap_iff.2 (by rwa [← hSk, ← hSk₁])
      simp only [hs₁, ite_eq_left hsw, of_apply, hMx, submatrix_apply, id, hrk₁]
      by_cases hik : i = k
      · subst i
        have hkj : k ≤ j := hij.elim Fin.le_def.2 id
        rw [ite_eq_left ⟨hkj, rfl⟩, Equiv.swap_apply_left]
        exact hS _ _ (Or.inl (Fin.le_def.1 hkj))
      · by_cases hik₁ : i = k₁
        · subst hik₁
          have hkj : k ≤ j := hij.elim Fin.le_def.2 fun h => hkk₁.le.trans h
          rw [ite_eq_right fun h => hik h.2, ite_eq_left ⟨hkj, rfl⟩, Equiv.swap_apply_right]
          exact hS _ _ (Or.inl (Fin.le_def.1 hkj))
        · rw [ite_eq_right fun h => hik h.2, ite_eq_right fun h => hik₁ h.2,
            Equiv.swap_apply_of_ne_of_ne hik hik₁]
          exact hS i j (hij.imp id id)
    · have hrk : r = k := by
        by_contra h
        exact hsw (by rw [hSk, hSk₁]; exact hswap_iff.1 (by
          rcases eq_or_lt_of_le hkr with h' | h'
          · exact absurd h'.symm h
          · exact Fin.ext (le_antisymm hrle (Nat.succ_le_of_lt (Fin.lt_def.1 h')))))
      simp only [hs₁, ite_eq_right hsw, hMx, submatrix_apply, id, hrk, Equiv.swap_self,
        Equiv.refl_apply]
      exact hS i j hij
  have hpiv₁ : s₁.2 = Function.update piv k (if r = k₁ then 1 else 0) := by
    by_cases hsw : |S k k| < |S k₁ k|
    · rw [hs₁, ite_eq_left hsw, ite_eq_left (hswap_iff.2 (by rwa [← hSk, ← hSk₁]))]
    · rw [hs₁, ite_eq_right hsw, ite_eq_right fun h => hsw (by rw [hSk, hSk₁]; exact hswap_iff.1 h)]
  have hlow₁ : ∀ i j : Fin n, j < k → s₁.1 i j = S i j := fun i j hj => by
    by_cases hsw : |S k k| < |S k₁ k|
    · simp only [hs₁, ite_eq_left hsw, of_apply]
      rw [ite_eq_right fun h => absurd h.1 (not_le.2 hj),
        ite_eq_right fun h => absurd h.1 (not_le.2 hj)]
    · simp only [hs₁, ite_eq_right hsw]
  -- the new stage
  have hG'apply : ∀ i j : Fin n,
      (gemPivotStage H partialPivotRow ((k : ℕ) + 1)).1 i j =
        Mx i j - if k < i then Mx i k * (Mx k k)⁻¹ * Mx k j else 0 := fun i j => by
    rw [hG', elimStep_apply]
  have hMcol : ∀ i : Fin n, k < i → i ≠ k₁ → Mx i k = 0 := fun i hki hik₁ => by
    have hi : (k : ℕ) + 1 < i := by
      have h1 := Fin.lt_def.1 hki
      have h2 : (i : ℕ) ≠ k + 1 := fun h => hik₁ (Fin.ext (by simp [hk₁, h]))
      omega
    simp only [hMx, submatrix_apply, id]
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hki) (fun h => by
      have := Fin.le_def.1 (h ▸ le_refl i); rw [h] at hi; omega), hcol i hi]
  have hmulk : ∀ (k' : Fin n) (hk' : (k' : ℕ) + 1 < n), (k' : ℕ) < k →
      (⟨(k' : ℕ) + 1, hk'⟩ : Fin n) ≠ k₁ := fun k' hk' hlt h => by
    have := congrArg Fin.val h
    simp [hk₁] at this
    omega
  dsimp only
  rw [← hs₁]
  by_cases hp : s₁.1 k k ≠ 0
  · rw [ite_eq_left hp]
    simp only [pure_bind, List.foldlM_pure, Id.run_pure]
    rw [foldl_update_of_nodup ((List.nodup_finRange n).filter _)
      (fun j y => y j - s₁.1 k₁ k / s₁.1 k k * s₁.1 k j) (fun j _ y y' _ hyj => by rw [hyj])]
    set τ := s₁.1 k₁ k / s₁.1 k k with hτ
    have hmem : ∀ j, j ∈ (List.finRange n).filter (k < ·) ↔ k < j := fun j => by simp
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_⟩
    · rw [hG'apply]
      by_cases hik₁ : i = k₁
      · subst hik₁
        have hkj : k < j := by
          rcases hij with h | h
          · exact Fin.lt_def.2 (by omega)
          · exact lt_of_lt_of_le hkk₁ h
        simp only [updateRow_self]
        rw [Function.update_of_ne (ne_of_gt hkj), ite_eq_left ((hmem j).2 hkj), ite_eq_left hkk₁,
          hτ, hS₁ _ _ (Or.inl (Fin.le_def.1 hkj.le)), hS₁ _ _ (Or.inl (Fin.le_def.1 hkj.le)),
          hS₁ _ _ (Or.inl le_rfl), hS₁ _ _ (Or.inl le_rfl)]
        ring
      · simp only [updateRow_ne hik₁]
        rw [hS₁ i j (hij.imp (fun h => by omega) id)]
        by_cases hki : k < i
        · rw [ite_eq_left hki, hMcol i hki hik₁]
          ring
        · rw [ite_eq_right hki, sub_zero]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · simp only [updateRow_ne (hmulk k' hk' hlt)]
        rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hmul k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [show (⟨(k : ℕ) + 1, hk'⟩ : Fin n) = k₁ from rfl]
        dsimp only
        rw [updateRow_self, Function.update_self, hτ, abs_div, hS₁ k₁ k (Or.inl le_rfl),
          hS₁ k k (Or.inl le_rfl)]
        exact div_le_one_of_le₀ hMk (abs_nonneg _)
    · rw [hpiv₁]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [Function.update_of_ne (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
        exact hpiv k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [Function.update_self, ← hr]
        by_cases h : r = k₁ <;> simp [h, hk₁]
  · rw [ite_eq_right hp]
    simp only [Id.run_pure]
    push Not at hp
    have hMkk : Mx k k = 0 := by rw [← hS₁ _ _ (Or.inl le_rfl), hp]
    refine ⟨fun i j hij => ?_, fun k' hk' hlt => ?_, fun k' hk' hlt => ?_⟩
    · rw [hG'apply, hMkk, _root_.inv_zero, hS₁ i j (hij.imp (fun h => by omega) id)]
      simp
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [hlow₁ _ _ (Fin.lt_def.2 hlt)]
        exact hmul k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [hS₁ _ _ (Or.inl le_rfl)]
        rw [hMkk, abs_zero] at hMk
        linarith
    · rw [hpiv₁]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · rw [Function.update_of_ne (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
        exact hpiv k' hk' hlt
      · have hk'k : k' = k := Fin.ext heq
        subst k'
        rw [Function.update_self, ← hr]
        by_cases h : r = k₁ <;> simp [h, hk₁]

/-- **Exact correctness of Algorithm 4.3.4**: for an upper Hessenberg `H`, with `(F, piv)` the
exact run, the upper triangle of `F` is the upper factor `U` of Gaussian elimination with partial
pivoting (`Matrix.gemPivotStage H Matrix.partialPivotRow n`), `piv(k) = 1` exactly when partial
pivoting interchanges the rows `k` and `k + 1` at stage `k`, and the stored multipliers
`F(k+1, k)` are bounded by unity. -/
theorem algorithm_4_3_4_spec {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg) :
    (∀ i j : Fin n, i ≤ j →
      (Id.run (algorithm_4_3_4 pure H)).1 i j = (gemPivotStage H partialPivotRow n).1 i j) ∧
    (∀ (k : Fin n) (hk : (k : ℕ) + 1 < n),
      ((Id.run (algorithm_4_3_4 pure H)).2 k = 1 ↔
        partialPivotRow (gemPivotStage H partialPivotRow k).1 k = ⟨k + 1, hk⟩)) ∧
    ∀ (k : Fin n) (hk : (k : ℕ) + 1 < n),
      |(Id.run (algorithm_4_3_4 pure H)).1 ⟨k + 1, hk⟩ k| ≤ 1 := by
  have key := foldl_finRange_induction (fun s k => Id.run (hessenbergLUStep pure s k)) (H, 0)
    (HessInv H) ⟨fun _ _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩ (fun k s hs => hessInv_step hH k s hs)
  rw [algorithm_4_3_4, List.idRun_foldlM]
  obtain ⟨h1, h2, h3⟩ := key
  exact ⟨fun i j hij => h1 i j (Or.inr hij), fun k hk => h3 k hk k.isLt,
    fun k hk => h2 k hk k.isLt⟩

/-! ### §4.3.5 Band Cholesky -/

/-- **A loop writing column `j` of a matrix, one row per step, in exact arithmetic.** Over a
duplicate-free list `l` of rows, a fold whose step `i` replaces the entry `(i, j)` by `h i A`, a
value that reads only the entry `(i, j)` and the entries outside the written ones, replaces every
entry `(i, j)`, `i ∈ l`, by `h i` of the initial matrix. -/
theorem foldl_updateRow_col {l : List (Fin n)} (hl : l.Nodup) (j : Fin n)
    (h : Fin n → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hh : ∀ i ∈ l, ∀ A A' : Matrix (Fin n) (Fin n) ℝ,
      (∀ r c, ¬ (c = j ∧ r ∈ l) → A r c = A' r c) → A i j = A' i j → h i A = h i A')
    (A : Matrix (Fin n) (Fin n) ℝ) :
    l.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (h i A))) A =
      of fun r c => if c = j ∧ r ∈ l then h r A else A r c := by
  induction l generalizing A with
  | nil => ext r c; simp
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, ih hl' fun i hi B B' hB hBi => hh i (List.mem_cons_of_mem _ hi) B B'
      (fun r c hrc => hB r c fun h' => hrc ⟨h'.1, List.mem_cons_of_mem _ h'.2⟩) hBi]
    have hoff : ∀ r' c', ¬ (c' = j ∧ r' ∈ a :: l) →
        (A.updateRow a (Function.update (A a) j (h a A))) r' c' = A r' c' := by
      intro r' c' hc'
      by_cases hr' : r' = a
      · subst r'
        have hcj : c' ≠ j := fun e => hc' ⟨e, List.mem_cons_self⟩
        simp [updateRow_self, Function.update_of_ne hcj]
      · simp [updateRow_ne hr']
    ext r c
    simp only [of_apply]
    by_cases hc : c = j
    · subst c
      by_cases hr : r ∈ l
      · have hra : r ≠ a := fun e => ha (e ▸ hr)
        rw [ite_eq_left ⟨rfl, hr⟩, ite_eq_left ⟨rfl, List.mem_cons_of_mem _ hr⟩]
        exact hh r (List.mem_cons_of_mem _ hr) _ _ hoff (by simp [updateRow_ne hra])
      · rw [ite_eq_right fun h' => hr h'.2]
        by_cases hra : r = a
        · subst r
          rw [ite_eq_left ⟨rfl, List.mem_cons_self⟩]
          simp [updateRow_self]
        · rw [ite_eq_right fun h' => (List.mem_cons.1 h'.2).elim hra hr]
          simp [updateRow_ne hra]
    · rw [ite_eq_right fun h' => hc h'.1, ite_eq_right fun h' => hc h'.1]
      exact hoff r c fun h' => hc h'.1

/-- The first phase of column `j` of Algorithm 4.3.5, in exact arithmetic: the updates
`A(j:λ, j) = A(j:λ, j) − A(j, k) · A(j:λ, k)` over the columns `k` of a duplicate-free list not
containing `j` subtract from each entry `(r, j)`, `r ≥ j`, the products of the columns `k` with
`r ≤ k + p`. -/
private theorem bandChol_phase1 (j : Fin n) (p : ℕ) :
    ∀ (K : List (Fin n)), K.Nodup → (∀ k ∈ K, k ≠ j) → ∀ S : Matrix (Fin n) (Fin n) ℝ,
    K.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
            A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) A) S =
      of fun r c => if c = j ∧ j ≤ r then
        S r j - ∑ k ∈ K.toFinset, (if (r : ℕ) ≤ k + p then S j k * S r k else 0) else S r c := by
  intro K
  induction K with
  | nil =>
    intro _ _ S
    ext r c
    simp only [List.foldl_nil, of_apply, List.toFinset_nil, Finset.sum_empty, sub_zero]
    split_ifs with h
    · rw [h.1]
    · rfl
  | cons k K ih =>
    intro hnd hK S
    rcases List.nodup_cons.1 hnd with ⟨hkK, hnd'⟩
    have hkj : k ≠ j := hK k List.mem_cons_self
    have hmem : ∀ r, r ∈ (List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p) ↔
        j ≤ r ∧ (r : ℕ) ≤ k + p := fun r => by simp
    rw [List.foldl_cons]
    set S₁ := ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) S with hS₁
    have h1 := foldl_updateRow_col
      (l := (List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p))
      ((List.nodup_finRange n).filter _) j
      (fun i A => A i j - A j k * A i k)
      (fun i _ A A' hA hij => by
        rw [hij, hA j k fun h => hkj h.1, hA i k fun h => hkj h.1]) S
    rw [← hS₁] at h1
    have hS₁c : ∀ r c, ¬ (c = j ∧ j ≤ r) → S₁ r c = S r c := fun r c h => by
      rw [h1, of_apply, ite_eq_right fun h' => h ⟨h'.1, ((hmem r).1 h'.2).1⟩]
    have hS₁j : ∀ r, j ≤ r →
        S₁ r j = S r j - if (r : ℕ) ≤ k + p then S j k * S r k else 0 := fun r hjr => by
      rw [h1, of_apply]
      by_cases hrk : (r : ℕ) ≤ k + p
      · rw [ite_eq_left ⟨rfl, (hmem r).2 ⟨hjr, hrk⟩⟩, ite_eq_left hrk]
      · rw [ite_eq_right fun h' => hrk ((hmem r).1 h'.2).2, ite_eq_right hrk, sub_zero]
    rw [ih hnd' (fun k' hk' => hK k' (List.mem_cons_of_mem _ hk'))]
    ext r c
    simp only [of_apply]
    by_cases hc : c = j ∧ j ≤ r
    · rw [ite_eq_left hc, ite_eq_left hc]
      rw [Finset.sum_congr rfl fun k' hk' => by
        have hk'j : k' ≠ j := hK k' (List.mem_cons_of_mem _ (List.mem_toFinset.1 hk'))
        rw [hS₁c j k' fun h => hk'j h.1, hS₁c r k' fun h => hk'j h.1]]
      rw [List.toFinset_cons, Finset.sum_insert fun h => hkK (List.mem_toFinset.1 h),
        hS₁j r hc.2]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc, hS₁c r c hc]

/-- One column step of Algorithm 4.3.5 in exact arithmetic. -/
private noncomputable def bandCholStepId (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (fun B : Matrix (Fin n) (Fin n) ℝ =>
      ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ j + p)).foldl
        (fun (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
          C.updateRow i (Function.update (C i) j (C i j / Real.sqrt (B j j)))) B)
    (((List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) =>
        ((List.finRange n).filter (fun i : Fin n => j ≤ i ∧ (i : ℕ) ≤ k + p)).foldl
          (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
            A.updateRow i (Function.update (A i) j (A i j - A j k * A i k))) A) A)

/-- The exact run of Algorithm 4.3.5 as a fold of its column steps. -/
private theorem algorithm_4_3_5_id (p : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_3_5 pure p A) = (List.finRange n).foldl (bandCholStepId p) A := by
  simp only [algorithm_4_3_5, pure_bind, List.foldlM_pure]
  rfl

/-- **Exact correctness of Algorithm 4.3.5**: for a symmetric positive definite `A` with lower
bandwidth `p`, the lower triangle of the exact run is the Cholesky factor `G = cholesky A`, which
"has the same lower bandwidth as `A`" (Theorem 4.3.1), and `A = GGᵀ`. The band loops skip only
products with a zero factor `g_jk` (`j > k + p`) or `g_rk` (`r > k + p`), so each column obeys the
Cholesky recurrence (4.2.9). -/
theorem algorithm_4_3_5_spec {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hp : A.HasLowerBandwidth p) :
    Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper =
        cholesky A ∧ (cholesky A).HasLowerBandwidth p ∧
      A = (Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper) *
        (Id.run (algorithm_4_3_5 pure p A) - (Id.run (algorithm_4_3_5 pure p A)).strictUpper)ᵀ := by
  have hGp := cholesky_hasLowerBandwidth hA hp
  have hGb := hasLowerBandwidth_iff_fin.1 hGp
  have hAb := hasLowerBandwidth_iff_fin.1 hp
  set G := cholesky A with hG
  have key := foldl_finRange_induction (bandCholStepId p) A
    (fun c S => (∀ i j : Fin n, c ≤ (j : ℕ) → S i j = A i j) ∧
      ∀ i j : Fin n, (j : ℕ) < c → j ≤ i → S i j = G i j)
    ⟨fun _ _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun j S hS => by
      obtain ⟨hSA, hSG⟩ := hS
      unfold bandCholStepId
      set K := (List.finRange n).filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p) with hK
      have hKmem : ∀ k, k ∈ K ↔ k < j ∧ (j : ℕ) ≤ k + p := fun k => by simp [hK]
      rw [bandChol_phase1 j p K ((List.nodup_finRange n).filter _)
        (fun k hk => ne_of_lt ((hKmem k).1 hk).1) S]
      set B := of fun r c => if c = j ∧ j ≤ r then
        S r j - ∑ k ∈ K.toFinset, (if (r : ℕ) ≤ k + p then S j k * S r k else 0) else S r c
        with hB
      beta_reduce
      rw [foldl_updateRow_col ((List.nodup_finRange n).filter _) j
        (fun i C => C i j / Real.sqrt (B j j)) (fun i _ C C' _ hij => by rw [hij]) B]
      -- the entries of column `j` before the division
      have hBr : ∀ r : Fin n, j ≤ r →
          B r j = A r j - ∑ k ∈ univ.filter (· < j), G r k * G j k := by
        intro r hjr
        rw [hB, of_apply, ite_eq_left ⟨rfl, hjr⟩, hSA r j le_rfl]
        congr 1
        have hKf : K.toFinset = univ.filter (fun k : Fin n => k < j ∧ (j : ℕ) ≤ k + p) := by
          ext k; simp [hKmem]
        rw [hKf, Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hkj : k < j
        · rw [hSG j k hkj hkj.le, hSG r k hkj (hkj.le.trans hjr)]
          by_cases hjk : (j : ℕ) ≤ k + p
          · rw [ite_eq_left ⟨hkj, hjk⟩, ite_eq_left hkj]
            by_cases hrk : (r : ℕ) ≤ k + p
            · rw [ite_eq_left hrk, mul_comm]
            · rw [ite_eq_right hrk, hGb r k (by omega), zero_mul]
          · rw [ite_eq_right fun h => hjk h.2, ite_eq_left hkj, hGb j k (by omega), mul_zero]
        · rw [ite_eq_right fun h => hkj h.1, ite_eq_right hkj]
      have hGjj : G j j = Real.sqrt (B j j) := by
        rw [hG, cholesky_apply_self, hBr j le_rfl]
        simp [Real.norm_eq_abs, sq, hG]
      refine ⟨fun i c hc => ?_, fun i c hc hci => ?_⟩
      · have hcj : c ≠ j := fun h => by rw [h] at hc; omega
        rw [of_apply, ite_eq_right fun h => hcj h.1, hB, of_apply, ite_eq_right fun h => hcj h.1]
        exact hSA i c (by omega)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
        · have hcj : c ≠ j := fun h => by rw [h] at hc; omega
          rw [of_apply, ite_eq_right fun h => hcj h.1, hB, of_apply,
            ite_eq_right fun h => hcj h.1]
          exact hSG i c hc hci
        · have hcj : c = j := Fin.ext hc
          subst c
          rw [of_apply]
          by_cases hij : (i : ℕ) ≤ j + p
          · rw [ite_eq_left ⟨rfl, by simp [hci, hij]⟩]
            rcases eq_or_lt_of_le hci with rfl | hji
            · rw [Real.div_sqrt, hGjj]
            · rw [hG, cholesky_apply_of_lt A hji, ← hG, hGjj, hBr i hci]
              simp
          · rw [ite_eq_right fun h => hij (of_decide_eq_true (List.mem_filter.1 h.2).2).2,
              hBr i hci, hAb i j (by omega), hGb i j (by omega)]
            rw [Finset.sum_eq_zero fun k hk => by
              rw [hGb i k (by have := Fin.lt_def.1 (mem_filter.1 hk).2; omega), zero_mul]]
            ring)
  have hlow : (List.finRange n).foldl (bandCholStepId p) A -
      ((List.finRange n).foldl (bandCholStepId p) A).strictUpper = G := by
    ext i k
    rw [Matrix.sub_apply]
    rcases le_or_gt k i with hki | hik
    · rw [key.2 i k k.isLt hki]
      simp [strictUpper, not_lt.2 hki]
    · simp [strictUpper, hik, hG, cholesky_apply_of_gt A hik]
  rw [algorithm_4_3_5_id, hlow]
  exact ⟨rfl, hGp, (cholesky_mul_transpose hA).symm⟩

/-! ### Exact correctness of band Gaussian elimination -/

/-- One pass `k` of Algorithm 4.3.1 in exact arithmetic. -/
private noncomputable def bandGEStepId (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q)).foldl
    (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      ((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldl
        (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
          A.updateRow i (Function.update (A i) j (A i j - A i k * A k j))) A)
    (((List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p)).foldl
      (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) k (A i k / A k k))) A)

/-- The exact run of Algorithm 4.3.1 as a fold of its passes. -/
private theorem algorithm_4_3_1_id (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_3_1 pure p q A) = (List.finRange n).foldl (bandGEStepId p q) A := by
  simp only [algorithm_4_3_1, pure_bind, List.foldlM_pure]
  rfl

/-- The rank-one update of a pass of Algorithm 4.3.1, over the columns `J` and the rows `I`
(neither containing the pivot index `k`), in exact arithmetic. -/
private theorem bandGE_update (k : Fin n) {I : List (Fin n)} (hI : I.Nodup) (hkI : k ∉ I) :
    ∀ (J : List (Fin n)), J.Nodup → k ∉ J → ∀ S : Matrix (Fin n) (Fin n) ℝ,
    J.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
      I.foldl (fun (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        A.updateRow i (Function.update (A i) j (A i j - A i k * A k j))) A) S =
      of fun r c => if c ∈ J ∧ r ∈ I then S r c - S r k * S k c else S r c := by
  intro J
  induction J with
  | nil => intro _ _ S; ext r c; simp
  | cons j J ih =>
    intro hJ hkJ S
    rcases List.nodup_cons.1 hJ with ⟨hjJ, hJ'⟩
    have hkj : k ≠ j := fun e => hkJ (e ▸ List.mem_cons_self)
    rw [List.foldl_cons, foldl_updateRow_col hI j (fun i A => A i j - A i k * A k j)
      (fun i _ A A' hA hij => by
        rw [hij, hA i k fun h => hkj h.1, hA k j fun h => hkI h.2]) S,
      ih hJ' (fun h => hkJ (List.mem_cons_of_mem _ h))]
    ext r c
    simp only [of_apply]
    have e1 : ∀ r', (if k = j ∧ r' ∈ I then S r' j - S r' k * S k j else S r' k) = S r' k :=
      fun r' => by rw [ite_eq_right fun h => hkj h.1]
    have e2 : ∀ c', (if c' = j ∧ k ∈ I then S k j - S k k * S k j else S k c') = S k c' :=
      fun c' => by rw [ite_eq_right fun h => hkI h.2]
    simp only [e1, e2]
    by_cases hcj : c = j <;> by_cases hr : r ∈ I <;> simp [hcj, hr, hjJ]

/-- **The band structure of the stages of Gaussian elimination** (the induction of the proof of
Theorem 4.3.1): with nonzero pivots, every stage keeps the lower bandwidth `p` and the upper
bandwidth `q` of `A`. -/
private theorem gemStage_band {A : Matrix (Fin n) (Fin n) ℝ} {p q : ℕ}
    (hpiv : ∀ (m : ℕ) (hm : m < n), m + 1 < n → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0)
    (hp : ∀ i j : Fin n, (j : ℕ) + p < i → A i j = 0)
    (hq : ∀ i j : Fin n, (i : ℕ) + q < j → A i j = 0) (k : ℕ) :
    (∀ i j : Fin n, (j : ℕ) + p < i → gemStage A k i j = 0) ∧
      ∀ i j : Fin n, (i : ℕ) + q < j → gemStage A k i j = 0 := by
  induction k with
  | zero => exact ⟨hp, hq⟩
  | succ k ih =>
    obtain ⟨ihp, ihq⟩ := ih
    by_cases hk : k < n
    swap
    · rw [gemStage_succ_of_le A (not_lt.1 hk)]
      exact ⟨ihp, ihq⟩
    rw [gemStage_succ_of_lt A hk]
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [elimStep_apply, ihp i j hij, zero_sub, neg_eq_zero]
      split_ifs with hki
      · by_cases hik : k + p < (i : ℕ)
        · rw [ihp i ⟨k, hk⟩ hik, zero_mul, zero_mul]
        · have hjk : (j : ℕ) < k := by omega
          rw [gemStage_apply_eq_zero_of_lt A (fun m hm _ hmn => hpiv m hm hmn) hjk
            (Fin.lt_def.2 hjk), mul_zero]
      · rfl
    · rw [elimStep_apply, ihq i j hij, zero_sub, neg_eq_zero]
      split_ifs with hki
      · rw [ihq ⟨k, hk⟩ j (by have := Fin.lt_def.1 hki; simp only at this ⊢; omega), mul_zero]
      · rfl

/-- **Exact correctness of Algorithm 4.3.1**: if `A` has lower bandwidth `p`, upper bandwidth `q`
and `A(1:k, 1:k)` is nonsingular for `k = 1:n−1` ("assuming it exists"), the exact run `F` holds
the LU factorization: `L = Chapter03.packedL F` and `U = Chapter03.packedU F`. The band loops
perform exactly the operations of Gaussian elimination on the entries that can be nonzero: by the
band structure of its stages (`gemStage_band`), the skipped multipliers and updates are zero; the
result is the multiplier matrix `Matrix.gemLower A` and the last stage `Matrix.gemStage A n`. -/
theorem algorithm_4_3_1_spec {p q : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLU A (Chapter03.packedL (Id.run (algorithm_4_3_1 pure p q A)))
      (Chapter03.packedU (Id.run (algorithm_4_3_1 pure p q A))) := by
  have hpiv := (gemStage_pivots_ne_zero_iff A).2 hA
  have hb := gemStage_band hpiv (hasLowerBandwidth_iff_fin.1 hp) (hasUpperBandwidth_iff_fin.1 hq)
  have hz : ∀ (k : ℕ) (i j : Fin n), (j : ℕ) < k → j < i → gemStage A k i j = 0 :=
    fun k i j hjk hji =>
      gemStage_apply_eq_zero_of_lt A (fun m hm _ hmn => hpiv m hm hmn) hjk hji
  have key := foldl_finRange_induction (bandGEStepId p q) A
    (fun c S => ∀ i j : Fin n, S i j =
      if j < i ∧ (j : ℕ) < c then gemStage A j i j / gemStage A j j j else gemStage A c i j)
    (fun i j => by simp)
    (fun k S hS i j => by
      unfold bandGEStepId
      set I := (List.finRange n).filter (fun i : Fin n => k < i ∧ (i : ℕ) ≤ k + p) with hI
      set J := (List.finRange n).filter (fun j : Fin n => k < j ∧ (j : ℕ) ≤ k + q) with hJ
      have hImem : ∀ r, r ∈ I ↔ k < r ∧ (r : ℕ) ≤ k + p := fun r => by simp [hI]
      have hJmem : ∀ r, r ∈ J ↔ k < r ∧ (r : ℕ) ≤ k + q := fun r => by simp [hJ]
      have hIn : I.Nodup := (List.nodup_finRange n).filter _
      have hJn : J.Nodup := (List.nodup_finRange n).filter _
      have hkI : k ∉ I := fun h => lt_irrefl _ ((hImem k).1 h).1
      have hkJ : k ∉ J := fun h => lt_irrefl _ ((hJmem k).1 h).1
      rw [foldl_updateRow_col hIn k (fun i A => A i k / A k k)
        (fun i _ A A' hA' hik => by rw [hik, hA' k k fun h => hkI h.2]) S]
      generalize hS₁ : (of fun r c => if c = k ∧ r ∈ I then S r k / S k k else S r c :
        Matrix (Fin n) (Fin n) ℝ) = S₁
      rw [bandGE_update k hIn hkI J hJn hkJ S₁, of_apply]
      have hS₁k : ∀ r, S₁ r k = if r ∈ I then S r k / S k k else S r k := fun r => by
        rw [← hS₁, of_apply]
        by_cases hr : r ∈ I
        · rw [ite_eq_left (show k = k ∧ r ∈ I from ⟨rfl, hr⟩), ite_eq_left hr]
        · rw [ite_eq_right (show ¬ (k = k ∧ r ∈ I) from fun h => hr h.2), ite_eq_right hr]
      have hS₁c : ∀ r c, c ≠ k → S₁ r c = S r c := fun r c hc => by
        rw [← hS₁, of_apply, ite_eq_right (show ¬ (c = k ∧ r ∈ I) from fun h => hc h.1)]
      have hSG : ∀ r c : Fin n, ¬ (c < r ∧ (c : ℕ) < k) → S r c = gemStage A k r c :=
        fun r c h => by rw [hS r c, ite_eq_right h]
      have hSkk : S k k = gemStage A k k k := hSG k k fun h => lt_irrefl _ h.1
      have hSik : ∀ r, S r k = gemStage A k r k := fun r => hSG r k fun h => lt_irrefl _ h.2
      have hG' : gemStage A ((k : ℕ) + 1) i j =
          gemStage A k i j - if k < i then
            gemStage A k i k * (gemStage A k k k)⁻¹ * gemStage A k k j else 0 := by
        rw [gemStage_succ_of_lt A k.isLt, elimStep_apply]
      rcases lt_trichotomy j k with hjk | hjk | hkj
      · -- a finished column
        have hjJ : j ∉ J := fun h => absurd ((hJmem j).1 h).1 (not_lt.2 hjk.le)
        have h1 : (j : ℕ) < k := Fin.lt_def.1 hjk
        rw [ite_eq_right (show ¬ (j ∈ J ∧ i ∈ I) from fun h => hjJ h.1),
          hS₁c i j (ne_of_lt hjk), hS i j]
        by_cases hji : j < i
        · rw [ite_eq_left (show j < i ∧ (j : ℕ) < k from ⟨hji, h1⟩),
            ite_eq_left (show j < i ∧ (j : ℕ) < k + 1 from ⟨hji, by omega⟩)]
        · rw [ite_eq_right (show ¬ (j < i ∧ (j : ℕ) < k) from fun h => hji h.1),
            ite_eq_right (show ¬ (j < i ∧ (j : ℕ) < k + 1) from fun h => hji h.1), hG',
            hz k k j h1 hjk, mul_zero]
          simp
      · -- the pivot column
        subst j
        rw [ite_eq_right (show ¬ (k ∈ J ∧ i ∈ I) from fun h => hkJ h.1), hS₁k i]
        by_cases hki : k < i
        · rw [ite_eq_left (show k < i ∧ (k : ℕ) < k + 1 from ⟨hki, Nat.lt_succ_self _⟩)]
          by_cases hi : i ∈ I
          · rw [ite_eq_left hi, hSik, hSkk]
          · have hip : (k : ℕ) + p < i := by
              have := (hImem i).not.1 hi
              have := Fin.lt_def.1 hki
              omega
            rw [ite_eq_right hi, hSik, (hb k).1 i k hip, zero_div]
        · have hi : i ∉ I := fun h => hki ((hImem i).1 h).1
          rw [ite_eq_right (show ¬ (k < i ∧ (k : ℕ) < k + 1) from fun h => hki h.1),
            ite_eq_right hi, hSik, hG', ite_eq_right hki, sub_zero]
      · -- a column to the right
        have hjk' : j ≠ k := ne_of_gt hkj
        have hno : ¬ (j < i ∧ (j : ℕ) < k + 1) := fun h => by
          have := Fin.lt_def.1 hkj; omega
        have hSij : S i j = gemStage A k i j :=
          hSG i j fun h => absurd h.2 (by have := Fin.lt_def.1 hkj; omega)
        have hSkj : S k j = gemStage A k k j := hSG k j fun h => absurd h.1 (not_lt.2 hkj.le)
        rw [ite_eq_right hno, hG']
        by_cases hij : j ∈ J ∧ i ∈ I
        · have hki : k < i := ((hImem i).1 hij.2).1
          rw [ite_eq_left hij, hS₁c i j hjk', hS₁k i, ite_eq_left hij.2, hS₁c k j hjk', hSik,
            hSkk, hSkj, hSij, ite_eq_left hki]
          ring
        · rw [ite_eq_right hij, hS₁c i j hjk', hSij]
          by_cases hki : k < i
          · rw [ite_eq_left hki]
            by_cases hi : i ∈ I
            · have hjq : (k : ℕ) + q < j := by
                have := (hJmem j).not.1 fun h => hij ⟨h, hi⟩
                have := Fin.lt_def.1 hkj
                omega
              rw [(hb k).2 k j hjq, mul_zero, sub_zero]
            · have hip : (k : ℕ) + p < i := by
                have := (hImem i).not.1 hi
                have := Fin.lt_def.1 hki
                omega
              rw [(hb k).1 i k hip, zero_mul, zero_mul, sub_zero]
          · rw [ite_eq_right hki, sub_zero])
  rw [Chapter03.packedL, Chapter03.packedU, algorithm_4_3_1_id]
  have hL : 1 + ((List.finRange n).foldl (bandGEStepId p q) A).strictLower = gemLower A := by
    ext i j
    by_cases hji : j < i
    · simp [strictLower, gemLower, hji, key i j, one_apply_ne (ne_of_gt hji)]
    · simp [strictLower, gemLower, hji, one_apply]
  have hU : (List.finRange n).foldl (bandGEStepId p q) A -
      ((List.finRange n).foldl (bandGEStepId p q) A).strictLower = gemStage A n := by
    ext i j
    by_cases hji : j < i
    · simp only [Matrix.sub_apply, strictLower, of_apply, ite_eq_left hji, sub_self]
      exact (hz n i j j.isLt hji).symm
    · simp [strictLower, hji, key i j]
  rw [hL, hU]
  exact isLU_gemLower_gemStage A hpiv

/-! ### §4.3.8 The inverse of a band matrix -/

/-- The partition `Fin k ⊕ Fin (n − k) ≃ Fin n` of the indices of an `n × n` matrix into square
diagonal blocks of sizes `k` and `n − k`. -/
def blockSplit {k : ℕ} (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

@[simp]
private theorem blockSplit_inl {k : ℕ} (hk : k ≤ n) (a : Fin k) :
    ((blockSplit hk (Sum.inl a) : Fin n) : ℕ) = a := by
  simp [blockSplit]

@[simp]
private theorem blockSplit_inr {k : ℕ} (hk : k ≤ n) (a : Fin (n - k)) :
    ((blockSplit hk (Sum.inr a) : Fin n) : ℕ) = k + a := by
  simp [blockSplit]

/-- A matrix whose rows from `p` on vanish has rank at most `p`. -/
private theorem rank_le_of_rows_eq_zero {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (p : ℕ)
    (h : ∀ i : Fin m, p ≤ (i : ℕ) → ∀ j, B i j = 0) : B.rank ≤ p := by
  classical
  have hB : B = diagonal (fun i : Fin m => if (i : ℕ) < p then (1 : ℝ) else 0) * B := by
    ext i j
    rw [diagonal_mul]
    split_ifs with hi
    · rw [one_mul]
    · rw [zero_mul, h i (not_lt.1 hi)]
  rw [hB]
  refine (rank_mul_le_left _ _).trans ?_
  rw [rank_diagonal]
  calc Fintype.card {i : Fin m // (if (i : ℕ) < p then (1 : ℝ) else 0) ≠ 0}
      ≤ Fintype.card (Fin p) := by
        refine Fintype.card_le_of_injective (fun i => ⟨i.1, ?_⟩) fun a b hab => ?_
        · by_contra h'
          exact i.2 (ite_eq_right h')
        · exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hab))
    _ = p := Fintype.card_fin p

/-- A matrix whose columns from `q` on vanish has rank at most `q`. -/
private theorem rank_le_of_cols_eq_zero {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (q : ℕ)
    (h : ∀ j : Fin k, q ≤ (j : ℕ) → ∀ i, B i j = 0) : B.rank ≤ q := by
  rw [← rank_transpose]
  exact rank_le_of_rows_eq_zero Bᵀ q fun j hj i => h j hj i

/-- **Theorem 4.3.3**, (4.3.1)–(4.3.2). "Suppose `A = [A₁₁ A₁₂; A₂₁ A₂₂]` is nonsingular and has
lower bandwidth `p` and upper bandwidth `q`. Assume that the diagonal blocks are square. If
`A⁻¹ = X = [X₁₁ X₁₂; X₂₁ X₂₂]` is partitioned conformably, then `rank(X₂₁) ≤ p` (4.3.1) and
`rank(X₁₂) ≤ q` (4.3.2)." The partition is `blockSplit` with a leading block of size `k`. Through
the nullity theorem `rank X₂₁ = rank A₂₁`; no limit argument (P4.3.11) is needed. -/
theorem theorem_4_3_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {p q : ℕ}
    (hp : A.HasLowerBandwidth p) (hq : A.HasUpperBandwidth q) {k : ℕ} (hk : k ≤ n) :
    (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank ≤ p ∧
      (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank ≤ q := by
  have hp' := hasLowerBandwidth_iff_fin.1 hp
  have hq' := hasUpperBandwidth_iff_fin.1 hq
  have hB : IsUnit (A.submatrix (blockSplit hk) (blockSplit hk)) :=
    (isUnit_submatrix_equiv _ _).2 hA
  have hinv : A⁻¹.submatrix (blockSplit hk) (blockSplit hk) =
      (A.submatrix (blockSplit hk) (blockSplit hk))⁻¹ := by
    rw [inv_submatrix_equiv]
  rw [hinv, rank_inv_toBlocks₂₁ hB, rank_inv_toBlocks₁₂ hB]
  refine ⟨rank_le_of_rows_eq_zero _ p fun i hi j => ?_,
    rank_le_of_cols_eq_zero _ q fun j hj i => ?_⟩
  · simp only [toBlocks₂₁, of_apply, submatrix_apply]
    exact hp' _ _ (by simp; omega)
  · simp only [toBlocks₁₂, of_apply, submatrix_apply]
    exact hq' _ _ (by simp; omega)

/-- **§4.3.8**: "It can actually be shown that `rank(A₂₁) = rank(X₂₁)` and
`rank(A₁₂) = rank(X₁₂)`" (Strang and Nguyen), for a nonsingular `A` partitioned as in
`theorem_4_3_3` — the nullity theorem. -/
theorem rank_inv_offDiag_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {k : ℕ}
    (hk : k ≤ n) :
    (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank =
        (A.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₂₁.rank ∧
      (A⁻¹.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank =
        (A.submatrix (blockSplit hk) (blockSplit hk)).toBlocks₁₂.rank := by
  have hB : IsUnit (A.submatrix (blockSplit hk) (blockSplit hk)) :=
    (isUnit_submatrix_equiv _ _).2 hA
  rw [← inv_submatrix_equiv]
  exact ⟨rank_inv_toBlocks₂₁ hB, rank_inv_toBlocks₁₂ hB⟩

end GolubVanLoan.Chapter04
