import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.LU
import NumlibSurface.GolubVanLoan.Chapter02.Section03

/-!
# Golub–Van Loan §4.1: diagonal dominance and symmetry

Surface file for [golub2013matrix] §4.1: LU without pivoting for a column diagonally dominant
matrix (Theorem 4.1.1, with the one-step factorization (4.1.2)), the dominance bound on `‖A⁻¹‖₁`
(Theorem 4.1.2), the `L D Lᵀ` factorization of a symmetric matrix (Theorem 4.1.3) with its
three-step solve, and Algorithm 4.1.1 (LDLT) with its rounding bridge and its exact specification.

## Conventions

Real square matrices `A : Matrix (Fin n) (Fin n) ℝ`, 0-based. Row and column diagonal dominance
(4.1.1) are the backbone's `Matrix.IsDiagDominant`, `Matrix.IsColDiagDominant` (with `‖·‖ = |·|`
over `ℝ`); the margin `δ` of (4.1.3) is a hypothesis. The book's `A = L D Lᵀ` is
`Matrix.IsLDM A L D L`, and "`A(1:k, 1:k)` nonsingular for `k = 1:n−1`" is
`∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)` (the orders `0, …, n − 1`).

Algorithm 4.1.1 follows the algorithm conventions of `NumlibSurface/GolubVanLoan`: every product
and difference passes through the rounding hook `rnd`, and the book's inner products
`A(j, 1:j−1) · v(1:j−1)` and `A(j+1:n, 1:j−1) · v(1:j−1)` are running differences from the entry of
`A` (`runningDiff`), the operation order of the backbone relation `FloatingPoint.RoundsLDL`. The
packed output holds `L` strictly below the diagonal and `D` on it; its unit lower factor is
`1 + F.strictLower` (chapter 3's `packedL F`, written out because chapter 3's surface is not yet
available to this file) and its diagonal factor `Matrix.diagonal F.diag`.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/{DiagDominant,LU}` (Theorems 4.1.1–4.1.3),
`Numlib/FloatingPoint/LU` (`RoundsLDL` and the rigorous (4.1.4)), `Numlib/FloatingPoint/Program`
(the run calculus). The book's two references to an "Algorithm 4.1.2" mean Algorithm 4.1.1. The
book's proof of Theorem 4.1.1 writes a strict inequality in its chain under the weak hypothesis;
the backbone proof is the weak one.
-/

open FloatingPoint Matrix Finset

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.1.1 Diagonal dominance -/

/-- **Theorem 4.1.1.** "If `A` is nonsingular and column diagonally dominant, then it has an LU
factorization and the entries in `L = (ℓ_ij)` satisfy `|ℓ_ij| ≤ 1`." -/
theorem theorem_4_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hdom : A.IsColDiagDominant) : ∃ L U, IsLU A L U ∧ ∀ i j, |L i j| ≤ 1 := by
  simpa only [Real.norm_eq_abs] using exists_isLU_of_isColDiagDominant hA hdom

/-- **(4.1.2)**, the first step of Gaussian elimination in block form: for `α ≠ 0`,
`[α wᵀ; v C] = [1 0; v/α I] [1 0; 0 B] [α wᵀ; 0 I]` with `B = C − (1/α) v wᵀ`, over the
partition `Fin 1 ⊕ Fin n` of the indices of an `(n + 1) × (n + 1)` matrix. -/
theorem equation_4_1_2 {α : ℝ} (hα : α ≠ 0) (w v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) w) (replicateCol (Fin 1) v) C =
      fromBlocks 1 0 (replicateCol (Fin 1) (α⁻¹ • v)) 1 *
        fromBlocks 1 0 0 (C - α⁻¹ • vecMulVec v w) *
        fromBlocks (of fun _ _ => α) (replicateRow (Fin 1) w) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j
    simp [Matrix.mul_apply]
    field_simp
  · ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]

/-- **Theorem 4.1.2.** If `δ = min_j (|a_jj| − ∑_{i ≠ j} |a_ij|) > 0` (4.1.3), then `A` is
nonsingular and `‖A⁻¹‖₁ ≤ 1/δ`. The margin is stated as a lower bound on every column. -/
theorem theorem_4_1_2 {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ j, δ ≤ |A j j| - ∑ i ∈ univ.erase j, |A i j|) :
    IsUnit A ∧ lpOpNorm 1 A⁻¹ ≤ 1 / δ := by
  have hA' : ∀ j, δ ≤ ‖A j j‖ - ∑ i ∈ univ.erase j, ‖A i j‖ := by
    simpa only [Real.norm_eq_abs] using hA
  have hu : IsUnit A := IsStrictColDiagDominant.isUnit fun j => by linarith [hA' j]
  refine ⟨hu, ?_⟩
  rw [GolubVanLoan.Chapter02.equation_2_3_9]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Real.iSup_of_isEmpty]
    positivity
  refine ciSup_le fun j => ?_
  have hx := IsStrictColDiagDominant.mul_sum_norm_le_sum_norm_mulVec (A := A) hA'
    (A⁻¹ *ᵥ Pi.single j 1)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hu), one_mulVec] at hx
  have h1 : ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i| = 1 := by
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp
  have h2 : ∀ i, (A⁻¹ *ᵥ Pi.single j 1) i = A⁻¹ i j := fun i => by
    simp [mulVec, dotProduct, Pi.single_apply]
  simp only [h2, Real.norm_eq_abs] at hx
  rw [h1] at hx
  rw [le_div_iff₀ hδ, mul_comm]
  exact hx

/-! ### §4.1.2 Symmetry and the `L D Lᵀ` factorization -/

/-- **Theorem 4.1.3 (`L D Lᵀ` factorization).** If `A` is symmetric and `A(1:k, 1:k)` is nonsingular
for `k = 1:n−1`, then there exist a unit lower triangular `L` and a diagonal `D` with
`A = L D Lᵀ`, and the factorization is unique. -/
theorem theorem_4_1_3 {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    ∃! LD : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ, IsLDM A LD.1 LD.2 LD.1 := by
  obtain ⟨⟨L, D, M⟩, h, huniq⟩ := existsUnique_isLDM hA
  have hML : M = L := h.eq_of_isSymm hs hA
  subst hML
  refine ⟨(M, D), h, fun LD h' => ?_⟩
  have := huniq (LD.1, LD.2, LD.1) h'
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 this.2.1

/-- **§4.1.2, the three-step solve.** "Once we have the `L D Lᵀ` factorization, then solving
`Ax = b` is a 3-step process: `Lz = b`, `Dy = z`, `Lᵀx = y`. This works because
`Ax = L(D(Lᵀx)) = L(Dy) = Lz = b`." -/
theorem ldlt_solve {A L D : Matrix (Fin n) (Fin n) ℝ} (h : IsLDM A L D L) {b z y x : Fin n → ℝ}
    (hz : L *ᵥ z = b) (hy : D *ᵥ y = z) (hx : Lᵀ *ᵥ x = y) : A *ᵥ x = b := by
  rw [← h.mul_eq, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, hz]

/-! ### Algorithm 4.1.1 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The running difference** `c − ∑_{k ∈ o} a_k b_k` in saxpy order: `t ← fl(t − fl(a_k b_k))`
for `k` along the list `o`, starting from `t = c` (the book's `A(j, j) − A(j, 1:j−1) · v(1:j−1)`
read from the entry of `A`, the order of the backbone relations `FloatingPoint.RoundsLU`,
`RoundsLDL`, `RoundsCholeskyDiv`). -/
def runningDiff {ι : Type} (o : List ι) (a b : ι → ℝ) (c : ℝ) : M ℝ :=
  o.foldlM (fun (t : ℝ) (k : ι) => do let p ← rnd (a k * b k); rnd (t - p)) c

/-- **Algorithm 4.1.1 (LDLT).** "If `A ∈ ℝⁿˣⁿ` is symmetric and has an LU factorization, then this
algorithm computes a unit lower triangular matrix `L` and a diagonal matrix
`D = diag(d₁, …, d_n)` so `A = L D Lᵀ`. The entry `a_ij` is overwritten with `ℓ_ij` if `i > j` and
with `d_i` if `i = j`":
```
for j = 1:n
    for i = 1:j−1
        v(i) = A(j, i) A(i, i)
    end
    A(j, j) = A(j, j) − A(j, 1:j−1) · v(1:j−1)
    A(j+1:n, j) = (A(j+1:n, j) − A(j+1:n, 1:j−1) · v(1:j−1)) / A(j, j)
end
```
The inner products are running differences from the entry of `A` (`runningDiff`), and the column
`A(j+1:n, j)` is computed entry by entry (its entries are independent). -/
noncomputable def algorithm_4_1_1 (A : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) => do
    let v ← ((List.finRange n).filter (· < j)).foldlM (fun (v : Fin n → ℝ) (i : Fin n) => do
      let p ← rnd (A j i * A i i)
      pure (Function.update v i p)) 0
    let d ← runningDiff rnd ((List.finRange n).filter (· < j)) (A j) v (A j j)
    ((List.finRange n).filter (j < ·)).foldlM (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
      let t ← runningDiff rnd ((List.finRange n).filter (· < j)) (B i) v (B i j)
      let l ← rnd (t / d)
      pure (B.updateRow i (Function.update (B i) j l)))
      (A.updateRow j (Function.update (A j) j d))) A

end Programs

/-- `t` is an **admissible running difference** `c − ∑_{k ∈ o} a_k b_k`: there are admissible
roundings `p k` of the products `a_k b_k` such that `t` is an admissible running sum from `c` of
the `−p k` in the order of `o` — the entry relation of the backbone's `RoundsLU`, `RoundsLDL`,
`RoundsCholeskyDiv`. -/
def IsRunningDiff (fp : RoundingModel ℝ) {ι : Type} (o : List ι) (a b : ι → ℝ) (c t : ℝ) : Prop :=
  ∃ p : ι → ℝ, (∀ k ∈ o, fp.Rounds (a k * b k) (p k)) ∧
    RoundsSumFrom fp c (o.map fun k => -p k) t

/-- An admissible running difference only reads the factors `a k`, `b k` for `k` in the list. -/
theorem IsRunningDiff.congr {fp : RoundingModel ℝ} {ι : Type} {o : List ι} {a a' b b' : ι → ℝ}
    {c t : ℝ} (h : IsRunningDiff fp o a b c t) (ha : ∀ k ∈ o, a' k = a k)
    (hb : ∀ k ∈ o, b' k = b k) : IsRunningDiff fp o a' b' c t := by
  obtain ⟨p, hp, hs⟩ := h
  exact ⟨p, fun k hk => by rw [ha k hk, hb k hk]; exact hp k hk, hs⟩

/-- The run set of a running difference over a duplicate-free list is the set of admissible
running differences. -/
theorem mem_run_runningDiff_iff {fp : RoundingModel ℝ} {ι : Type} {o : List ι} (ho : o.Nodup)
    (a b : ι → ℝ) (c t : ℝ) :
    t ∈ (runningDiff fp.round o a b c).run ↔ IsRunningDiff fp o a b c t := by
  classical
  unfold runningDiff IsRunningDiff
  induction o generalizing c with
  | nil =>
    simp only [List.foldlM_nil, SetM.mem_run_pure, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, List.map_nil, true_and, exists_const]
    exact ⟨fun h => by subst h; exact .nil _, fun h => by cases h; rfl⟩
  | cons a₀ o ih =>
    rcases List.nodup_cons.1 ho with ⟨ha, ho'⟩
    simp only [List.foldlM_cons, SetM.mem_run_bind, RoundingModel.mem_run_round, ih ho']
    constructor
    · rintro ⟨c', ⟨p₀, hp₀, hc'⟩, p, hp, hsum⟩
      refine ⟨Function.update p a₀ p₀, fun k hk => ?_, ?_⟩
      · rcases List.mem_cons.1 hk with rfl | hk
        · rwa [Function.update_self]
        · rw [Function.update_of_ne fun e : k = a₀ => ha (e ▸ hk)]
          exact hp k hk
      · rw [List.map_cons, Function.update_self]
        have hmap : (o.map fun k => -Function.update p a₀ p₀ k) = o.map fun k => -p k :=
          List.map_congr_left fun k hk => by
            rw [Function.update_of_ne fun e : k = a₀ => ha (e ▸ hk)]
        rw [hmap]
        exact .cons (by rwa [← sub_eq_add_neg]) hsum
    · rintro ⟨p, hp, (_ | ⟨hc', hsum⟩)⟩
      exact ⟨_, ⟨p a₀, hp a₀ List.mem_cons_self, by rwa [sub_eq_add_neg]⟩, p,
        fun k hk => hp k (List.mem_cons_of_mem _ hk), hsum⟩

/-- **A loop writing one entry of column `j` per row.** Over a duplicate-free list of rows, a loop
whose step `i` replaces the entry `(i, j)` by a result of `h i` applied to the current row `i` has
as results the matrices whose rows off the list are unchanged and whose row `i` on the list is the
initial row with entry `j` replaced by a result of `h i` on the initial row. -/
theorem mem_run_foldlM_updateRow_iff {m k : ℕ} {l : List (Fin m)} (hl : l.Nodup) (j : Fin k)
    (h : Fin m → (Fin k → ℝ) → SetM ℝ) (S S' : Matrix (Fin m) (Fin k) ℝ) :
    S' ∈ (l.foldlM (fun (B : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) => do
        let x ← h i (B i)
        pure (B.updateRow i (Function.update (B i) j x))) S).run ↔
      (∀ i, i ∉ l → S' i = S i) ∧
        ∀ i ∈ l, ∃ x ∈ (h i (S i)).run, S' i = Function.update (S i) j x := by
  have key := SetM.mem_run_foldlM_update_of_nodup
    (fun (i : Fin m) (r : Fin k → ℝ) (_ : Fin m → Fin k → ℝ) =>
      (do let x ← h i r; pure (Function.update r j x) : SetM (Fin k → ℝ))) l hl
    (fun _ _ _ _ _ _ => rfl) S S'
  simp only [bind_assoc, pure_bind, SetM.mem_run_bind, SetM.mem_run_pure] at key
  exact key

/-- The exact running difference is `c − ∑_{k ∈ o} a_k b_k`. -/
theorem runningDiff_id {ι : Type} (o : List ι) (a b : ι → ℝ) (c : ℝ) :
    Id.run (runningDiff (M := Id) pure o a b c) = c - (o.map fun k => a k * b k).sum := by
  unfold runningDiff
  induction o generalizing c with
  | nil => simp
  | cons k o ih =>
    simp only [List.foldlM_cons, pure_bind] at ih ⊢
    rw [ih, List.map_cons, List.sum_cons]
    ring

section Bridge

variable (fp : RoundingModel ℝ)

/-- The indices below `j`, in increasing order. -/
private abbrev lt (j : Fin n) : List (Fin n) := (List.finRange n).filter (· < j)

private theorem mem_lt {j k : Fin n} : k ∈ lt j ↔ k < j := by simp [lt]

private theorem nodup_lt (j : Fin n) : (lt j).Nodup := (List.nodup_finRange n).filter _

/-- Column `j` of the packed state `S` is a finished column of Algorithm 4.1.1: with the rounded
products `v k = fl(ℓ_jk d_k)`, the pivot is the running difference of `a_jj` and the entries below
it are the rounded quotients of the running differences of `a_ij` by the pivot. -/
private def ColDone (A S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : Prop :=
  ∃ v : Fin n → ℝ, (∀ k ∈ lt j, fp.Rounds (S j k * S k k) (v k)) ∧
    IsRunningDiff fp (lt j) (S j) v (A j j) (S j j) ∧
    ∀ i, j < i → ∃ t, IsRunningDiff fp (lt j) (S i) v (A i j) t ∧ fp.Rounds (t / S j j) (S i j)

/-- A finished column stays finished when the state changes only in columns to its right. -/
private theorem ColDone.congr {A S S' : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (h : ColDone fp A S j) (hS : ∀ i k, k ≤ j → S' i k = S i k) : ColDone fp A S' j := by
  obtain ⟨v, hv, hd, hcol⟩ := h
  refine ⟨v, fun k hk => ?_, ?_, fun i hi => ?_⟩
  · have hkj := le_of_lt (mem_lt.1 hk)
    rw [hS j k hkj, hS k k hkj]
    exact hv k hk
  · rw [hS j j le_rfl]
    exact hd.congr (fun k hk => hS j k (le_of_lt (mem_lt.1 hk))) fun _ _ => rfl
  · obtain ⟨t, ht, hl⟩ := hcol i hi
    refine ⟨t, ht.congr (fun k hk => hS i k (le_of_lt (mem_lt.1 hk))) fun _ _ => rfl, ?_⟩
    rw [hS i j le_rfl, hS j j le_rfl]
    exact hl

/-- The loop invariant of Algorithm 4.1.1 after `c` columns: the columns `≥ c` still hold `A`, the
columns `< c` are finished. -/
private def Inv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i k : Fin n, c ≤ k.val → S i k = A i k) ∧ ∀ j : Fin n, j.val < c → ColDone fp A S j

/-- One column step of Algorithm 4.1.1 keeps the invariant. -/
private theorem inv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Inv fp A j S) (S' : Matrix (Fin n) (Fin n) ℝ)
    (hS' : S' ∈ ((do
      let v ← (lt j).foldlM (fun (v : Fin n → ℝ) (i : Fin n) => do
        let p ← fp.round (S j i * S i i)
        pure (Function.update v i p)) 0
      let d ← runningDiff fp.round (lt j) (S j) v (S j j)
      ((List.finRange n).filter (j < ·)).foldlM
        (fun (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
          let t ← runningDiff fp.round (lt j) (B i) v (B i j)
          let l ← fp.round (t / d)
          pure (B.updateRow i (Function.update (B i) j l)))
        (S.updateRow j (Function.update (S j) j d))) : SetM _).run) :
    Inv fp A (j + 1) S' := by
  obtain ⟨hA, hdone⟩ := hS
  simp only [SetM.mem_run_bind] at hS'
  obtain ⟨v, hv, d, hd, hS'⟩ := hS'
  -- the products `v`
  have hv' : ∀ k ∈ lt j, fp.Rounds (S j k * S k k) (v k) := by
    have := (SetM.mem_run_foldlM_update_of_nodup
      (fun (i : Fin n) (_ : ℝ) (_ : Fin n → ℝ) => fp.round (S j i * S i i)) (lt j) (nodup_lt j)
      (fun _ _ _ _ _ _ => rfl) 0 v).1 hv
    exact fun k hk => this.2 k hk
  have hd' : IsRunningDiff fp (lt j) (S j) v (S j j) d :=
    (mem_run_runningDiff_iff (nodup_lt j) _ _ _ _).1 hd
  -- the column loop writes row `i > j` of the matrix once
  set S₁ := S.updateRow j (Function.update (S j) j d) with hS₁
  have hcol := (mem_run_foldlM_updateRow_iff ((List.nodup_finRange n).filter _) j
    (fun i r => do let t ← runningDiff fp.round (lt j) r v (r j); fp.round (t / d)) S₁ S').1
    (by simpa only [bind_assoc] using hS')
  obtain ⟨hout, hin⟩ := hcol
  have hmemgt : ∀ i, i ∈ (List.finRange n).filter (j < ·) ↔ j < i := fun i => by simp
  -- entries outside column `j`, and column `j` above the diagonal, are unchanged
  have hrowj : S' j = Function.update (S j) j d := by
    rw [hout j (by simp), hS₁, updateRow_self]
  have hother : ∀ i k, k ≠ j → S' i k = S i k := by
    intro i k hk
    by_cases hi : j < i
    · obtain ⟨x, -, hr⟩ := hin i ((hmemgt i).2 hi)
      rw [hr, Function.update_of_ne hk, hS₁, updateRow_ne (ne_of_gt hi)]
    · rw [hout i (fun h => hi ((hmemgt i).1 h))]
      by_cases hij : i = j
      · subst hij
        rw [hS₁, updateRow_self, Function.update_of_ne hk]
      · rw [hS₁, updateRow_ne hij]
  refine ⟨fun i k hk => ?_, fun j' hj' => ?_⟩
  · have hkj : k ≠ j := fun h => by rw [h] at hk; simp at hk
    rw [hother i k hkj]
    exact hA i k (by omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | hj'
    · -- an earlier column: unchanged
      refine (hdone j' hj').congr fp fun i k hk => hother i k ?_
      intro h
      rw [h] at hk
      exact absurd (Fin.lt_def.1 (lt_of_le_of_lt hk (Fin.lt_def.2 hj'))) (lt_irrefl _)
    · -- the column just computed
      have hjj : j' = j := Fin.ext hj'
      subst hjj
      have hdiag : S' j' j' = d := by rw [hrowj, Function.update_self]
      have hSjj : S j' j' = A j' j' := hA j' j' le_rfl
      refine ⟨v, fun k hk => ?_, ?_, fun i hi => ?_⟩
      · have hk' := ne_of_lt (mem_lt.1 hk)
        rw [hother j' k hk', hother k k hk']
        exact hv' k hk
      · rw [hdiag, ← hSjj]
        exact hd'.congr (fun k hk => hother j' k (ne_of_lt (mem_lt.1 hk))) fun _ _ => rfl
      · obtain ⟨l, hx, hr⟩ := hin i ((hmemgt i).2 hi)
        simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at hx
        obtain ⟨t, ht, hl⟩ := hx
        have hS₁i : S₁ i = S i := by rw [hS₁, updateRow_ne (ne_of_gt hi)]
        rw [hS₁i] at ht hr
        refine ⟨t, ?_, ?_⟩
        · have ht' := (mem_run_runningDiff_iff (nodup_lt j') _ _ _ _).1 ht
          rw [hA i j' le_rfl] at ht'
          exact ht'.congr (fun k hk => hother i k (ne_of_lt (mem_lt.1 hk))) fun _ _ => rfl
        · rw [hdiag, hr, Function.update_self]
          exact hl

/-- **The rounding bridge of Algorithm 4.1.1**: every run in the relational model is an admissible
`L D Lᵀ` factorization in the operation order of the algorithm, `FloatingPoint.RoundsLDL`, with
`L = 1 + F.strictLower` (chapter 3's `packedL F`) and `D = diag(F)`. No hypothesis on `A`. -/
theorem algorithm_4_1_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_4_1_1 fp.round A).run,
      RoundsLDL fp A (1 + F.strictLower) (diagonal F.diag) := by
  have hfin := SetM.forall_mem_run_foldlM_finRange (Inv fp A)
    ⟨fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    (fun j S hS S' hS' => inv_step fp A j S hS S' hS')
  intro F hF
  obtain ⟨-, hdone⟩ := hfin F hF
  have hL : ∀ i k, k < i → (1 + F.strictLower) i k = F i k := fun i k hki => by
    simp [strictLower, one_apply_ne (ne_of_gt hki), hki]
  choose v hv hd hcol using fun j : Fin n => hdone j j.isLt
  refine ⟨fun i k hik => ?_, fun i => ?_, isDiag_diagonal _, ⟨of fun j k => v j k, ?_, ?_, ?_⟩⟩
  · simp [strictLower, one_apply_ne (ne_of_lt hik), not_lt_of_gt hik]
  · simp [strictLower]
  · intro j k hkj
    rw [hL j k hkj, diagonal_apply_eq, diag_apply]
    exact hv j k (mem_lt.2 hkj)
  · intro j
    obtain ⟨p, hp, hs⟩ := hd j
    refine ⟨lt j, p, nodup_lt j, fun k => mem_lt, fun k hk => ?_, ?_⟩
    · rw [hL j k (mem_lt.1 hk)]
      exact hp k hk
    · rwa [diagonal_apply_eq, diag_apply]
  · intro i j hji
    obtain ⟨t, ⟨p, hp, hs⟩, hl⟩ := hcol j i hji
    refine ⟨lt j, p, t, nodup_lt j, fun k => mem_lt, fun k hk => ?_, hs, ?_⟩
    · rw [hL i k (lt_trans (mem_lt.1 hk) hji)]
      exact hp k hk
    · rw [diagonal_apply_eq, diag_apply, hL i j hji]
      exact hl

end Bridge

/-- The exact semantics of Algorithm 4.1.1 is one of its runs in the exact model. -/
private theorem algorithm_4_1_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_4_1_1 pure A) ∈ (algorithm_4_1_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_4_1_1, runningDiff, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In the exact model, a computed `L D Lᵀ` factorization reproduces `A` on and below the diagonal
wherever the pivot of the column is used as a divisor. -/
private theorem mul_mul_transpose_apply_of_roundsLDL_exact {A L D : Matrix (Fin n) (Fin n) ℝ}
    (h : RoundsLDL (RoundingModel.exact ℝ) A L D) {i k : Fin n} (hki : k ≤ i)
    (hd : k < i → D k k ≠ 0) : (L * D * Lᵀ) i k = A i k := by
  obtain ⟨V, hV, hpiv, hcol⟩ := h.exists_rounds
  have hV' : ∀ j k, k < j → V j k = L j k * D k k := fun j k hkj => hV j k hkj
  rw [mul_mul_transpose_apply_of_isDiag h.lower_apply_eq_zero h.isDiag, min_eq_right hki,
    sum_filter_le_eq_add]
  have hsum : ∀ j, ∀ o : List (Fin n), o.Nodup → (∀ t, t ∈ o ↔ t < k) → ∀ p : Fin n → ℝ,
      (∀ t ∈ o, (RoundingModel.exact ℝ).Rounds (L j t * V k t) (p t)) →
      ∑ t ∈ o.toFinset, p t = ∑ t ∈ univ.filter (· < k), L j t * D t t * L k t := by
    intro j o hnd ho p hp
    have hset : o.toFinset = univ.filter (· < k) := by ext t; simp [ho]
    rw [hset]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htk := (mem_filter.1 ht).2
    rw [hp t ((ho t).2 htk), hV' k t htk]
    ring
  rcases eq_or_lt_of_le hki with rfl | hki'
  · obtain ⟨o, p, hnd, ho, hp, hs⟩ := hpiv k
    rw [(roundsSumFrom_exact_map_neg_iff hnd).1 hs, hsum k o hnd ho p hp, h.lower_diag, mul_one,
      one_mul]
    ring
  · obtain ⟨o, p, t, hnd, ho, hp, hs, hl⟩ := hcol i k hki'
    rw [RoundingModel.exact_rounds_iff] at hl
    rw [hl, (roundsSumFrom_exact_map_neg_iff hnd).1 hs, hsum i o hnd ho p hp, h.lower_diag,
      mul_one, div_mul_cancel₀ _ (hd hki')]
    ring

/-- In the exact model, the pivots of a computed `L D Lᵀ` factorization of a symmetric matrix with
nonsingular leading principal submatrices that serve as divisors are nonzero: by induction, the
leading `(j+1) × (j+1)` block of `L D Lᵀ` is that of `A`, whose determinant is `d₁ ⋯ d_{j+1}`. -/
private theorem roundsLDL_exact_diag_ne_zero {A L D : Matrix (Fin n) (Fin n) ℝ}
    (h : RoundsLDL (RoundingModel.exact ℝ) A L D) (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    ∀ j i : Fin n, j < i → D j j ≠ 0 := by
  have hLu : L.IsUnitLowerTriangular :=
    ⟨fun i k hik => h.lower_apply_eq_zero i k (OrderDual.toDual_lt_toDual.1 hik), h.lower_diag⟩
  have hB : IsLDM (L * D * Lᵀ) L D L := ⟨hLu, h.isDiag, hLu, rfl⟩
  have hsymm : (L * D * Lᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isDiag.isSymm.eq,
      Matrix.mul_assoc]
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro i hji
  have hk : j.val + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hji) i.isLt
  have key : ∀ a b : Fin n, b ≤ a → a.val < j.val + 1 → (L * D * Lᵀ) a b = A a b :=
    fun a b hba ha => mul_mul_transpose_apply_of_roundsLDL_exact h hba fun hba' =>
      ih b (Fin.lt_def.2 (by have := Fin.lt_def.1 hba'; omega)) a hba'
  have hsub : A.strictLeadingPrincipalSubmatrix ⟨j.val + 1, hk⟩ =
      (L * D * Lᵀ).strictLeadingPrincipalSubmatrix ⟨j.val + 1, hk⟩ := by
    ext a b
    have ha : a.1.val < j.val + 1 := Fin.lt_def.1 a.2
    have hb : b.1.val < j.val + 1 := Fin.lt_def.1 b.2
    simp only [strictLeadingPrincipalSubmatrix, toBlock_apply]
    rcases le_total b.1 a.1 with hba | hab
    · exact (key a b hba ha).symm
    · rw [hsymm.apply b.1 a.1, key b a hab hb]
      exact hs.apply b.1 a.1
  have hdet := isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 (hA ⟨j.val + 1, hk⟩))
  rw [hsub, hB.isLU.det_strictLeadingPrincipalSubmatrix, Finset.prod_ne_zero_iff] at hdet
  have hj := hdet j (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩)
  have hDL : (D * Lᵀ) j j = D j j := by
    rw [mul_apply, Finset.sum_eq_single j (fun t _ htj => by rw [h.isDiag htj.symm, zero_mul])
      (by simp), transpose_apply, h.lower_diag, mul_one]
  rwa [hDL] at hj

/-- **Exact correctness of Algorithm 4.1.1**: for a symmetric `A` with `A(1:k, 1:k)` nonsingular for
`k = 1:n−1`, the exact run computes the `L D Lᵀ` factorization of Theorem 4.1.3, with `L` the unit
lower triangle `1 + F.strictLower` of the packed output `F` and `D` its diagonal. Read off the
bridge at the exact model (convention 11), once the pivots used as divisors are known to be
nonzero. -/
theorem algorithm_4_1_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLDM A (1 + (Id.run (algorithm_4_1_1 pure A)).strictLower)
      (diagonal (Id.run (algorithm_4_1_1 pure A)).diag)
      (1 + (Id.run (algorithm_4_1_1 pure A)).strictLower) := by
  have h := algorithm_4_1_1_rounds (RoundingModel.exact ℝ) A _ (algorithm_4_1_1_mem_exact A)
  have hpiv := roundsLDL_exact_diag_ne_zero h hs hA
  have hLu : (1 + (Id.run (algorithm_4_1_1 pure A)).strictLower).IsUnitLowerTriangular :=
    ⟨fun i k hik => h.lower_apply_eq_zero i k (OrderDual.toDual_lt_toDual.1 hik), h.lower_diag⟩
  refine ⟨hLu, h.isDiag, hLu, ?_⟩
  have hsymm : ((1 + (Id.run (algorithm_4_1_1 pure A)).strictLower) *
      diagonal (Id.run (algorithm_4_1_1 pure A)).diag *
      (1 + (Id.run (algorithm_4_1_1 pure A)).strictLower)ᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, h.isDiag.isSymm.eq,
      Matrix.mul_assoc]
  ext i k
  rcases le_total k i with hki | hik
  · exact mul_mul_transpose_apply_of_roundsLDL_exact h hki fun hki' => hpiv k i hki'
  · rw [hsymm.apply k i,
      mul_mul_transpose_apply_of_roundsLDL_exact h hik fun hik' => hpiv i k hik']
    exact (hs.apply k i).symm

end GolubVanLoan.Chapter04
