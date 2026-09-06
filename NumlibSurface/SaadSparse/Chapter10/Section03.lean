import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.LinearSolve.Preconditioner.ILU

/-!
# Saad §10.3: incomplete `LU` factorization preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §10.3: the general static-pattern incomplete factorization `ILU_P` and its existence for
M-matrices (Theorems 10.1 and 10.2), the residual identity (Proposition 10.4), `ILU(0)`, the level
of fill (Definition 10.5) and the modified factorization `MILU` of §10.3.5.

Almost nothing is constructed here. Saad's `ILU_P` is `Matrix.IsILU` of
`Numlib/LinearSolve/Preconditioner/ILU.lean`, stated declaratively — `L` unit lower triangular, `U`
upper triangular, both vanishing on the zero pattern `P`, and `L U` agreeing with `A` off `P` —
rather than as the output of a loop; `isILU_iff` is that reading written out. What the surface adds
is the book's vocabulary: the condition (10.11) on a zero pattern as `IsZeroPattern`, the level of
fill (10.17) and the `ILU(p)` pattern `P_p` as `levelOfFill` and `levelPattern`, and the small
example showing that the `ILU(0)` constraints do not determine the factors.

Saad's `A₁`, "the matrix obtained from the first step of Gaussian elimination", is `Matrix.elimStep`
on the whole index type — the reading under which (10.10) is `equation_10_10` — and the
`(n-1) × (n-1)` matrix he draws from it by deleting the first row and column is
`Matrix.schurComplementSingle`, giving `theorem_10_1_schur`. Theorem 10.1 is stated at an arbitrary
pivot, which is how the book uses it: the elimination is restarted on the trailing block at every
step.

**Proposition 10.3 is the one place where the loops themselves are written down.**  `Matrix.IsILU`
abstracts from the loop order on purpose, and it does not imply the proposition: the constraints do
not determine the factors (`not_unique_isILU0`).  So the two loop orders are transcribed as
`kijSweep` (Algorithm 10.1) and `ikjSweep` (Algorithm 10.3), with `iluRowOp` the body
`ope(row(i), row(k))` that both share, and `proposition_10_3` proves they agree.  Neither sweep
performs Saad's line 1, "for each `(i, j) ∈ P` set `a_ij = 0`": it is common to both algorithms, so
the statement proved is the stronger one, for an arbitrary starting matrix.

Two items of the section get no declaration.

* Theorems 10.6 and 10.7 characterize the fill levels by fill-paths in the adjacency graph. They
  need a symbolic model of Gaussian elimination on a graph that nothing else here would use, and
  Theorem 10.6 is quoted from the literature without proof.
* Algorithms 10.4 and 10.5 are listings. "Algorithm 10.1 does not break down", the first clause of
  Theorem 10.2, is read as the existence of the factors together with the clause `∀ i, U i i ≠ 0` of
  `theorem_10_2`: no pivot vanishes.
-/

open Matrix Stationary
open scoped Matrix

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The zero pattern (10.11), and `ILU_P` -/

/-- **Saad (10.11)**: a *zero pattern* is a set of positions off the diagonal,
`P ⊆ {(i, j) | i ≠ j}`.

Avoiding the diagonal is the only restriction the book places on the entries an incomplete
factorization may discard, and it is exactly what Theorem 10.2 needs: the proof divides by the
pivots, which are therefore never dropped. -/
def IsZeroPattern (P : Set (Fin n × Fin n)) : Prop := ∀ p ∈ P, p.1 ≠ p.2

/-- A zero pattern avoids the diagonal, in the form the existence theorem asks for. -/
theorem IsZeroPattern.diag_notMem {P : Set (Fin n × Fin n)} (hP : IsZeroPattern P) (i : Fin n) :
    (i, i) ∉ P := fun h => hP _ h rfl

/-- The off-diagonal zero pattern `NZ(A)ᶜ` of `A` itself, which is the pattern of `ILU(0)`, is a
zero pattern in the sense of (10.11). -/
theorem isZeroPattern_zeroPattern (A : Matrix (Fin n) (Fin n) ℝ) : IsZeroPattern A.zeroPattern :=
  fun _ hp => hp.2

/-- **Saad's `ILU_P`** (§10.3.1), written out: a pair `L`, `U` is an incomplete `LU` factorization
of `A` for the zero pattern `P` when `L` is unit lower triangular, `U` is upper triangular, both
vanish on `P`, and the product `L U` agrees with `A` off `P`.

Saad defines the factors by Algorithm 10.1 and then proves (Proposition 10.3) that a second loop
order produces the same ones; the declarative form is what all of §10.3–10.5 uses, is satisfied by
either loop order, and does not pretend the factors are unique — they are not, as
`not_unique_isILU0` below records. -/
theorem isILU_iff (P : Set (Fin n × Fin n)) (A L U : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.IsILU P A L U ↔
      ((∀ i, L i i = 1) ∧ ∀ i j, i < j → L i j = 0) ∧ (∀ i j, j < i → U i j = 0) ∧
        (∀ i j, (i, j) ∈ P → L i j = 0 ∧ U i j = 0) ∧
        ∀ i j, (i, j) ∉ P → (L * U) i j = A i j := by
  constructor
  · intro h
    exact ⟨⟨h.l_diag, h.l_eq_zero_of_lt⟩, h.u_eq_zero_of_gt,
      fun i j hij => ⟨h.l_eq_zero_of_mem i j hij, h.u_eq_zero_of_mem i j hij⟩, h.agree⟩
  · rintro ⟨⟨hd, hl⟩, hu, hmem, hag⟩
    exact ⟨⟨hd, hl, hu, fun i j hij => (hmem i j hij).1, fun i j hij => (hmem i j hij).2⟩, hag⟩

/-- **No pivot vanishes**: as soon as the product `L U` of an incomplete factorization is
nonsingular, every diagonal entry of `U` is nonzero.

This is the sense in which the elimination "does not break down": `L` is unit lower triangular, so
`det (L U) = ∏ᵢ uᵢᵢ`, and a vanishing pivot would make the product singular. -/
theorem pivot_ne_zero {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsILU P A L U) (hu : IsUnit (L * U)) (i : Fin n) : U i i ≠ 0 := by
  have hdet : IsUnit (L * U).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L fun i j hij => h.l_eq_zero_of_lt i j hij]
    simp [h.l_diag]
  rw [Matrix.det_mul, hL, one_mul,
    Matrix.det_of_isUpperTriangular fun i j hij => h.u_eq_zero_of_gt i j hij] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet.ne_zero i (Finset.mem_univ i)

/-! ### Theorem 10.1, Ky Fan's theorem -/

/-- **Saad (10.10)**: one step of Gaussian elimination factors `A = L₁ A₁`, with `L₁` the identity
with the scaled pivot column `A_{*,p} / a_{pp}` written into column `p`. -/
theorem equation_10_10 (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n) :
    A = Matrix.elimMul A p * Matrix.elimStep A p := (Matrix.elimMul_mul_elimStep A p).symm

/-- **Saad Theorem 10.1** (Ky Fan): the matrix `A₁` obtained from an M-matrix `A` by one step of
Gaussian elimination is again an M-matrix.

The book states the first step; it is stated here at an arbitrary pivot `p`, which is what the rest
of the section uses, since the elimination is restarted on the trailing block at every step. -/
theorem theorem_10_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (p : Fin n) :
    (Matrix.elimStep A p).IsMMatrix := hA.isMMatrix_elimStep p

/-- **Saad Theorem 10.1, the remark drawn after it**: the smaller matrix obtained from `A₁` by
deleting the pivot row and the pivot column — the `1 × 1`-pivot Schur complement — is an M-matrix
too. This is the form in which the argument is iterated. -/
theorem theorem_10_1_schur {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (p : Fin n) :
    (A.schurComplementSingle p).IsMMatrix := hA.isMMatrix_schurComplementSingle p

/-! ### Theorem 10.2 and Proposition 10.4 -/

/-- **Saad Theorem 10.2**: for an M-matrix `A` and any zero pattern `P` as in (10.11), Algorithm
10.1 does not break down and produces an incomplete factorization `A = L U - R` which is a regular
splitting of `A`.

"Does not break down" is the existence of the factors together with `∀ i, U i i ≠ 0`; the splitting
is `A = M - N` with `M = L U`, and `Stationary.Splitting.IsRegular` is Saad's Definition 4.3, so the
iteration it defines converges (`Matrix.IsILU.complexSpectralRadius_lt_one`). -/
theorem theorem_10_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) {P : Set (Fin n × Fin n)}
    (hP : IsZeroPattern P) :
    ∃ (L U : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit (L * U)),
      Matrix.IsILU P A L U ∧ (∀ i, U i i ≠ 0) ∧ A = L * U - (L * U - A) ∧
        (⟨L * U, hu⟩ : Splitting A).IsRegular := by
  obtain ⟨L, U, hILU, hu, hinv, hres⟩ := hA.exists_isILU P hP.diag_notMem
  exact ⟨L, U, hu, hILU, pivot_ne_zero hILU hu, (sub_sub_cancel _ _).symm,
    hILU.isRegular hu hinv fun i j _ => hres.apply i j⟩

/-- **Saad Proposition 10.4**: an incomplete factorization writes `A = L U - R`, and `-R` is the
matrix of the entries dropped during the elimination — `R` vanishes off the zero pattern. -/
theorem proposition_10_4 {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsILU P A L U) :
    A = L * U - (L * U - A) ∧ ∀ i j, (i, j) ∉ P → (L * U - A) i j = 0 :=
  ⟨(sub_sub_cancel _ _).symm, fun _ _ hij => h.sub_eq_zero_of_notMem hij⟩

/-! ### §10.3.2, `ILU(0)` -/

/-- **Saad Theorem 10.2 for `ILU(0)`** (§10.3.2): taking the zero pattern to be the off-diagonal
zero pattern of `A` itself, an M-matrix has an `ILU(0)` factorization whose factors have the
sparsity of the lower and upper parts of `A`, and the splitting it defines is regular. -/
theorem theorem_10_2_ilu0 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) :
    ∃ (L U : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit (L * U)),
      Matrix.IsILU0 A L U ∧ (∀ i, U i i ≠ 0) ∧ A = L * U - (L * U - A) ∧
        (⟨L * U, hu⟩ : Splitting A).IsRegular :=
  theorem_10_2 hA (isZeroPattern_zeroPattern A)

/-- The matrix of the `ILU(0)` non-uniqueness example, whose second row is zero. -/
def exampleA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 0; 1, 1, 1]

/-- The upper factor of the `ILU(0)` non-uniqueness example. -/
def exampleU : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 0; 0, 0, 1]

/-- The lower factors of the `ILU(0)` non-uniqueness example: the entry `t` in position `(2, 1)` is
multiplied only by the vanishing row `1` of `exampleU`, so no constraint reaches it. -/
def exampleL (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 1, t, 1]

/-- The product of the example factors is the example matrix, for every `t`. -/
theorem exampleL_mul_exampleU (t : ℝ) : exampleL t * exampleU = exampleA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exampleL, exampleU, exampleA, Matrix.mul_apply, Fin.sum_univ_three]

/-- Every member of the family is an `ILU(0)` factorization of `exampleA`. -/
theorem isILU0_example (t : ℝ) : Matrix.IsILU0 exampleA (exampleL t) exampleU := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩, fun i j _ => ?_⟩
  · fin_cases i <;> simp [exampleL]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleL]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleU]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleL, exampleA]
  · fin_cases i <;> fin_cases j <;> simp_all [exampleU, exampleA]
  · rw [exampleL_mul_exampleU]

/-- The family `exampleL` is injective in its parameter. -/
theorem exampleL_injective {s t : ℝ} (h : exampleL s = exampleL t) : s = t := by
  have h21 : exampleL s 2 1 = exampleL t 2 1 := by rw [h]
  simpa [exampleL] using h21

/-- **The `ILU(0)` constraints do not determine the factors** (Saad's remark before Algorithm 10.4):
a matrix can have infinitely many pairs `L`, `U` satisfying them.

`exampleA` has a zero row, so its `ILU(0)` factors satisfy `L U = A` exactly, and the entry of `L`
in position `(2, 1)` is multiplied only by that zero row: it is left free. The standard `ILU(0)` of
Algorithm 10.4 picks one member of the family, which is why the book defines it constructively. -/
theorem not_unique_isILU0 :
    ∃ A L L' U : Matrix (Fin 3) (Fin 3) ℝ,
      Matrix.IsILU0 A L U ∧ Matrix.IsILU0 A L' U ∧ L ≠ L' :=
  ⟨exampleA, exampleL 0, exampleL 1, exampleU, isILU0_example 0, isILU0_example 1,
    fun h => by simpa using exampleL_injective h⟩

/-! ### §10.3.3, Definition 10.5: the level of fill and `ILU(p)` -/

open scoped Classical in
/-- **Saad Definition 10.5**, the initial level of fill: `0` at a nonzero entry and on the diagonal,
`∞` elsewhere. -/
noncomputable def initialLevel (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℕ∞ :=
  if A i j ≠ 0 ∨ i = j then 0 else ⊤

/-- **Saad (10.17)**, the level of fill after `k` elimination steps: eliminating the pivot `k`
updates every level by `lev i j := min (lev i j) (lev i k + lev k j + 1)`.

The book writes the update in place inside Algorithm 10.2; carrying the step index makes it a
function, and `levelOfFill A n` is "the level of fill value after all updates have been performed".
The recurrence has the shape of Floyd–Warshall on the adjacency graph, one pivot per step, and Saad
reads it that way; the identification of the levels with the lengths of fill-paths is his Theorems
10.6 and 10.7, which are not formalized here. -/
noncomputable def levelOfFill (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → Fin n → ℕ∞
  | 0, i, j => initialLevel A i j
  | k + 1, i, j =>
    if h : k < n then
      min (levelOfFill A k i j) (levelOfFill A k i ⟨k, h⟩ + levelOfFill A k ⟨k, h⟩ j + 1)
    else levelOfFill A k i j

@[simp]
theorem levelOfFill_zero (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    levelOfFill A 0 i j = initialLevel A i j := rfl

theorem levelOfFill_succ (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    levelOfFill A (k + 1) i j =
      if h : k < n then
        min (levelOfFill A k i j) (levelOfFill A k i ⟨k, h⟩ + levelOfFill A k ⟨k, h⟩ j + 1)
      else levelOfFill A k i j := rfl

/-- A level of fill is never created: it is positive after `k` steps exactly when it was positive at
the start, because every update adds `1` to a sum of levels. This is the book's remark that an entry
nonzero in `A` keeps level `0` throughout the elimination. -/
theorem zero_lt_levelOfFill_iff (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    0 < levelOfFill A k i j ↔ 0 < initialLevel A i j := by
  induction k with
  | zero => rw [levelOfFill_zero]
  | succ k ih =>
    rw [levelOfFill_succ]
    split_ifs with h
    · exact ⟨fun hlt => ih.1 (lt_min_iff.1 hlt).1,
        fun hlt => lt_min_iff.2 ⟨ih.2 hlt, lt_of_lt_of_le zero_lt_one le_add_self⟩⟩
    · exact ih

/-- **Saad's `P_p`** (§10.3.3, Algorithm 10.5): the zero pattern of `ILU(p)` is the set of positions
whose level of fill, after all the updates (10.17), exceeds `p`. -/
noncomputable def levelPattern (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) : Set (Fin n × Fin n) :=
  {q | (p : ℕ∞) < levelOfFill A n q.1 q.2}

/-- The `ILU(p)` pattern is a zero pattern in the sense of (10.11): a diagonal position has level of
fill `0` and is never in it, so Theorem 10.2 applies to `ILU(p)` for every `p`. -/
theorem isZeroPattern_levelPattern (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    IsZeroPattern (levelPattern A p) := by
  rintro ⟨i, j⟩ hq (rfl : i = j)
  have hpos : 0 < levelOfFill A n i i := lt_of_le_of_lt zero_le hq
  rw [zero_lt_levelOfFill_iff, initialLevel, ite_eq_left (Or.inr rfl)] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **Saad's remark that `p = 0` recovers `ILU(0)`**: the pattern `P₀` is exactly the off-diagonal
zero pattern of `A`, so `levelPattern A 0` is the pattern of `Matrix.IsILU0`. -/
theorem levelPattern_zero (A : Matrix (Fin n) (Fin n) ℝ) : levelPattern A 0 = A.zeroPattern := by
  ext ⟨i, j⟩
  change ((0 : ℕ) : ℕ∞) < levelOfFill A n i j ↔ (i, j) ∈ A.zeroPattern
  rw [Nat.cast_zero, zero_lt_levelOfFill_iff, Matrix.mem_zeroPattern, initialLevel]
  by_cases h : A i j ≠ 0 ∨ i = j
  · rw [ite_eq_left h]
    simp only [lt_self_iff_false, false_iff, not_and, not_not]
    exact fun h1 => h.resolve_left (not_not_intro h1)
  · rw [ite_eq_right h]
    rw [not_or, not_not] at h
    exact iff_of_true (lt_of_lt_of_le zero_lt_one le_top) ⟨h.1, h.2⟩

/-! ### §10.3.5, the modified factorization `MILU` -/

/-- **Saad (10.21)**: the modified factorization is exact on the vector of ones, `A e = L U e`.

The dropped entries of a row are not discarded but subtracted from the diagonal entry of `U` in that
row, which is exactly the constraint `Matrix.IsMILU.mulVec_one`. For a discretized PDE the vector of
ones is a constant function, so `MILU` is exact on constants. -/
theorem milu_mulVec_one {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) : A *ᵥ (1 : Fin n → ℝ) = (L * U) *ᵥ 1 := h.mulVec_one.symm

/-- **Saad's `r_{i,*}^{new} = (r_{i,*} e) e_iᵀ - r_{i,*}`, whose row sum is zero** (Example 10.3):
the residual of a modified factorization has vanishing row sums. -/
theorem milu_residual_mulVec_one {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) : (L * U - A) *ᵥ (1 : Fin n → ℝ) = 0 := h.residual_mulVec_one

/-- **The diagonal compensation of §10.3.5**: the diagonal entry of the residual is minus the sum of
the entries dropped in that row, which is the modification `u_ii := u_ii - (r_{i,*} e)`. -/
theorem milu_residual_diag {P : Set (Fin n × Fin n)} {A L U : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsMILU P A L U) (i : Fin n) :
    (L * U - A) i i = -∑ j ∈ Finset.univ.erase i, (L * U - A) i j := by
  have hrow : ∑ j, (L * U - A) i j = 0 := by
    have := congrFun h.residual_mulVec_one i
    simpa [Matrix.mulVec, dotProduct] using this
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => (L * U - A) i j) (Finset.mem_univ i)
  linarith [hrow, hsplit]

/-! ### §10.3.1: the two loop orders, and Proposition 10.3 -/

section LoopOrder

variable (P : Set (Fin n × Fin n)) [DecidablePred (· ∈ P)]

/-- Saad's `ope(row(i), row(k))`, lines 3–6 of both Algorithm 10.1 and Algorithm 10.3: with `p` the
pivot row `k` and `r` the current row `i`, set `r k := r k / p k` and then, for every `j > k` off
the pattern, `r j := r j - r k * p j`.  Nothing happens at all when `(i, k) ∈ P`. -/
noncomputable def iluRowOp (i k : Fin n) (p r : Fin n → ℝ) : Fin n → ℝ :=
  if (i, k) ∈ P then r
  else fun j =>
    if j = k then r k / p k
    else if k < j ∧ (i, j) ∉ P then r j - r k / p k * p j
    else r j

/-- The `k`-loop of Algorithm 10.3 applied to row `i`: `ope(row(i), row(k))` for
`k = 0, …, m - 1` in this order, each reading row `k` of `ρ`. -/
noncomputable def rowOps (ρ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (a : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => a
  | m + 1 => if h : m < n then
      iluRowOp P i ⟨m, h⟩ (fun j => ρ ⟨m, h⟩ j) (rowOps ρ i a m) else rowOps ρ i a m

/-- **Algorithm 10.3** (the `IKJ` variant), after its outer steps `i = 0, …, I - 1`: at step `i` the
whole of row `i` is produced from the rows `0, …, i - 1`, which are already final and which the
step does not modify. -/
noncomputable def ikjSweep (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | I + 1 => Matrix.of fun i j =>
      if (i : ℕ) = I then rowOps P (ikjSweep A I) i (fun j' => ikjSweep A I i j') I j
      else ikjSweep A I i j

/-- **Algorithm 10.1** (the `KIJ` variant), after its outer steps `k = 0, …, K - 1`: at step `k`
every row `i > k` is updated by `ope(row(i), row(k))`.  The rows are updated independently — each
reads only its own entries and the pivot row `k`, which the step leaves alone — so this is exactly
the `i` loop of the algorithm. -/
noncomputable def kijSweep (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | K + 1 =>
      if h : K < n then Matrix.of fun i j =>
        if K < (i : ℕ) then
          iluRowOp P i ⟨K, h⟩ (fun j' => kijSweep A K ⟨K, h⟩ j') (fun j' => kijSweep A K i j') j
        else kijSweep A K i j
      else kijSweep A K

/-- One step of Algorithm 10.3, entry by entry. -/
theorem ikjSweep_succ_apply (A : Matrix (Fin n) (Fin n) ℝ) (I : ℕ) (i j : Fin n) :
    ikjSweep P A (I + 1) i j
      = if (i : ℕ) = I then rowOps P (ikjSweep P A I) i (fun j' => ikjSweep P A I i j') I j
        else ikjSweep P A I i j := rfl

/-- One step of Algorithm 10.1, entry by entry. -/
theorem kijSweep_succ_apply (A : Matrix (Fin n) (Fin n) ℝ) {K : ℕ} (h : K < n) (i j : Fin n) :
    kijSweep P A (K + 1) i j
      = if K < (i : ℕ) then
          iluRowOp P i ⟨K, h⟩ (fun j' => kijSweep P A K ⟨K, h⟩ j')
            (fun j' => kijSweep P A K i j') j
        else kijSweep P A K i j := by
  rw [kijSweep, dite_eq_left h]
  rfl

variable {P}

/-- The `k`-loop only reads the rows `0, …, m - 1`, so two row families agreeing there give the
same result. -/
theorem rowOps_congr {ρ σ : Matrix (Fin n) (Fin n) ℝ} (i : Fin n) (a : Fin n → ℝ) {m : ℕ}
    (h : ∀ k : Fin n, (k : ℕ) < m → (fun j => ρ k j) = fun j => σ k j) :
    rowOps P ρ i a m = rowOps P σ i a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [rowOps, rowOps, ih fun k hk => h k (by omega)]
      by_cases hm : m < n
      · rw [dite_eq_left hm, dite_eq_left hm, h ⟨m, hm⟩ (by simp)]
      · rw [dite_eq_right hm, dite_eq_right hm]

variable (P)

/-- Rows `I, I + 1, …` are untouched after `I` steps of Algorithm 10.3. -/
theorem ikjSweep_apply_of_le (A : Matrix (Fin n) (Fin n) ℝ) {I : ℕ} {i : Fin n}
    (h : I ≤ (i : ℕ)) (j : Fin n) : ikjSweep P A I i j = A i j := by
  induction I with
  | zero => rfl
  | succ I ih =>
      rw [ikjSweep_succ_apply, ite_eq_right (by omega : ¬(i : ℕ) = I)]
      exact ih (by omega)

/-- Row `i` is final after step `i` of Algorithm 10.3: later steps leave it alone. -/
theorem ikjSweep_apply_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {I : ℕ} {i : Fin n}
    (h : (i : ℕ) < I) : ∀ {J : ℕ}, I ≤ J → ∀ j, ikjSweep P A J i j = ikjSweep P A I i j := by
  intro J
  induction J with
  | zero => exact fun hIJ _ => absurd h (by omega)
  | succ J ih =>
      intro hIJ j
      rcases Nat.eq_or_lt_of_le hIJ with heq | hlt
      · rw [← heq]
      · rw [ikjSweep_succ_apply, ite_eq_right (by omega : ¬(i : ℕ) = J)]
        exact ih (by omega) j

/-- **The rows Algorithm 10.3 produces are the fixed point of the row recurrence**: row `i` of the
output is obtained from row `i` of `A` by `ope(row(i), row(k))` for `k = 0, …, i - 1`, each reading
the *final* row `k`. -/
theorem ikjSweep_row (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (fun j => ikjSweep P A n i j)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (i : ℕ) := by
  have hstep : ∀ j, ikjSweep P A n i j
      = rowOps P (ikjSweep P A (i : ℕ)) i (fun j' => ikjSweep P A (i : ℕ) i j') (i : ℕ) j := by
    intro j
    rw [ikjSweep_apply_of_lt P A (Nat.lt_succ_self _) i.isLt j, ikjSweep_succ_apply,
      ite_eq_left rfl]
  have hstart : (fun j' => ikjSweep P A (i : ℕ) i j') = fun j' => A i j' :=
    funext fun j' => ikjSweep_apply_of_le P A (le_refl _) j'
  have hrows : rowOps P (ikjSweep P A (i : ℕ)) i (fun j' => ikjSweep P A (i : ℕ) i j') (i : ℕ)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (i : ℕ) := by
    rw [hstart]
    exact rowOps_congr i _ fun k hk =>
      funext fun j => (ikjSweep_apply_of_lt P A hk (le_of_lt i.isLt) j).symm
  exact funext fun j => (hstep j).trans (congrFun hrows j)

/-- **The invariant of Algorithm 10.1**: after `K` outer steps, row `i` has received exactly the
operations `ope(row(i), row(k))` for `k < min K i`, each reading the *final* row `k` — because the
pivot row `k` is finished at the moment step `k` uses it and is never touched again. -/
theorem kijSweep_row (A : Matrix (Fin n) (Fin n) ℝ) (K : ℕ) : ∀ i : Fin n,
    (fun j => kijSweep P A K i j)
      = rowOps P (ikjSweep P A n) i (fun j => A i j) (min K (i : ℕ)) := by
  induction K with
  | zero => exact fun i => by rw [Nat.zero_min]; rfl
  | succ K ih =>
      intro i
      by_cases hn : K < n
      · by_cases hKi : K < (i : ℕ)
        · have hpivot : (fun j => kijSweep P A K (⟨K, hn⟩ : Fin n) j)
              = fun j => ikjSweep P A n (⟨K, hn⟩ : Fin n) j := by
            rw [ih ⟨K, hn⟩, ikjSweep_row P A ⟨K, hn⟩]
            simp
          have hrow : (fun j => kijSweep P A K i j)
              = rowOps P (ikjSweep P A n) i (fun j => A i j) K := by
            rw [ih i, min_eq_left (le_of_lt hKi)]
          refine funext fun j => ?_
          rw [kijSweep_succ_apply P A hn, ite_eq_left hKi, hpivot, hrow,
            min_eq_left (by omega : K + 1 ≤ (i : ℕ)), rowOps, dite_eq_left hn]
        · refine funext fun j => ?_
          rw [kijSweep_succ_apply P A hn, ite_eq_right hKi, congrFun (ih i) j,
            min_eq_right (by omega : (i : ℕ) ≤ K), min_eq_right (by omega : (i : ℕ) ≤ K + 1)]
      · have hik : (i : ℕ) ≤ K := by omega
        refine funext fun j => ?_
        rw [kijSweep, dite_eq_right hn, congrFun (ih i) j, min_eq_right hik,
          min_eq_right (by omega : (i : ℕ) ≤ K + 1)]

/-- **Saad, Proposition 10.3**: for a static zero pattern, the `KIJ`-based Algorithm 10.1 and the
`IKJ`-based Algorithm 10.3 produce the same factors.

Saad's own proof rewrites the first two loops of Algorithm 10.1 as a double loop over `k` and `i`
whose body is `ope(row(i), row(k))` and observes that the two loops may be permuted.  What makes
that safe is the invariant `kijSweep_row`: whichever order is used, row `i` ends up carrying
`ope(row(i), row(k))` for `k = 0, …, i - 1` in increasing `k`, each reading the final row `k`.  In
the `KIJ` order that is because step `k` finishes row `k` before it is used and never returns to
it; in the `IKJ` order it is the definition.

The pattern must be *static*, as the book warns: both algorithms here read the same `P` throughout,
and a pattern determined as the elimination proceeds would not have that property. -/
theorem proposition_10_3 (A : Matrix (Fin n) (Fin n) ℝ) :
    kijSweep P A n = ikjSweep P A n := by
  ext i j
  rw [congrFun (kijSweep_row P A n i) j, min_eq_right (le_of_lt i.isLt),
    ← congrFun (ikjSweep_row P A i) j]

end LoopOrder

end SaadSparse.Chapter10
