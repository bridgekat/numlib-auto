import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.Order

/-!
# Triangular systems: forward and backward substitution

Forward and backward substitution as *total functions* on a finite linear order, their correctness
for triangular matrices with a nowhere-zero diagonal, the solve `x = U⁻¹ (L⁻¹ b)` through an LU
factorization, the inverse of a triangular matrix column by column and leading block by leading
block, and the two exact-arithmetic bounds on `|U⁻¹| |U|` of [higham2002accuracy] §8.2 that drive
the componentwise error analysis of substitution ([quarteroni2000numerical] §3.2.2).

## Main definitions

* `Matrix.forwardSubst L b`: forward substitution, [quarteroni2000numerical] (3.22),
  `x i = (b i - ∑_{j < i} l_ij x_j) / l_ii`, by well-founded recursion on the number of indices
  below `i`; `Matrix.backSubst U b`: backward substitution, (3.23), which is forward substitution on
  the dual order (`Matrix.backSubst_eq_forwardSubst_toDual`). Both are total: a zero diagonal entry
  gives junk (`x / 0 = 0`) rather than a hypothesis.
* `Matrix.luSolve L U b = backSubst U (forwardSubst L b)`: the solution of `A x = b` through
  `A = L U` ([quarteroni2000numerical] §3.3.1).

## Main results

* `Matrix.mulVec_forwardSubst`, `Matrix.mulVec_backSubst`: substitution solves a triangular system
  with nowhere-zero diagonal, and `Matrix.forwardSubst_eq_of_mulVec_eq`,
  `Matrix.backSubst_eq_of_mulVec_eq`: it is the only solution.
* `Matrix.isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular` (and the lower version): a
  triangular matrix is nonsingular exactly when its diagonal has no zero, the sentence opening
  [quarteroni2000numerical] §3.2.
* `Matrix.mulVec_luSolve`, `Matrix.mulVec_luSolve_of_mul`, `Matrix.mulVec_luSolve_permMatrix`:
  the LU solve, plain and with a row permutation `P A = L U` (§3.5: solve `L y = P b`, `U x = y`).
* `Matrix.inv_col_eq_backSubst` ((3.26)), `Matrix.inv_toBlock_le_of_isUpperTriangular` ((3.27)),
  `Matrix.inv_apply_of_isUpperTriangular` ((3.28)): the inverse of an upper triangular matrix
  through the systems `U v_i = e_i`, through its leading blocks, and by the entrywise recurrence.
* `Matrix.abs_inv_mul_abs_apply_le_two_pow`, `Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`:
  [higham2002accuracy] Lemma 8.6, `(|U⁻¹| |U|)_{ij} ≤ 2^{j-i}` when `|u_ii| ≥ |u_ij|` for `j > i`,
  and the row sums are at most `2^{n-i+1} - 1`.
* `Matrix.abs_inv_mul_abs_apply_le_of_isDiagDominant`,
  `Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant`: [higham2002accuracy] Lemma 8.8, the
  linear bounds `(|U⁻¹| |U|)_{ij} ≤ j - i + 1` and `‖|U⁻¹| |U|‖_∞ ≤ 2n - 1` for a row diagonally
  dominant upper triangular `U`, the `2n - 1` of [quarteroni2000numerical] §3.1.2.

## Implementation notes

The index type is any `[Fintype n] [LinearOrder n]`, never `Fin N`; "`j < i`" is all substitution
uses, and counts of indices such as `#{k | i ≤ k ∧ k < j}` replace the differences `j - i` of the
book (on `Fin N` they agree, `Matrix.card_filter_le_lt_fin`). Backward substitution is *defined*
as forward substitution on `nᵒᵈ`, so that every fact about it is the dual instance of the forward
one; `Matrix.IsUpperTriangular.isLowerTriangular_orderDual` is the bridge.

The two Higham lemmas are over a linearly ordered field with the entrywise absolute value
`Matrix.abs` of `Numlib/LinearAlgebra/Matrix/Order`, which is where their floating-point consumers
(`Numlib/FloatingPoint/Substitution`) live; row diagonal dominance is spelled out as
`∑_{j ≠ i} |u_ij| ≤ |u_ii|`, since `Matrix.IsDiagDominant` is stated for `RCLike` scalars. Both
proofs normalize `V = D⁻¹ U` implicitly, working with `|(U⁻¹)_{ik}| |u_kk| = |(V⁻¹)_{ik}|`, and
the geometric sums `∑_{k ∈ s} 2^{#{l ∈ s | l < k}} = 2^{#s} - 1` over an arbitrary finset of a
linear order (`Finset.sum_two_pow_card_filter_lt_add_one`) replace the book's
`∑_{k=i+1}^j 2^{k-i-1}`.

## References

* [quarteroni2000numerical] §3.2, §3.3.1, §3.5, §3.6.
* [higham2002accuracy] §8.1–8.2.
-/

open Finset

/-! ### Geometric sums over a finset of a linear order -/

namespace Finset

variable {α : Type*} [LinearOrder α] {R : Type*} [Semiring R]

/-- `∑_{k ∈ s} 2^{#{l ∈ s | l < k}} + 1 = 2^{#s}`: listing `s` in increasing order as `k₀ < k₁ < …`,
the summand at `k_m` is `2^m`. -/
theorem sum_two_pow_card_filter_lt_add_one (s : Finset α) :
    ∑ k ∈ s, (2 : R) ^ #(s.filter (· < k)) + 1 = 2 ^ #s := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h1 : (insert a s).filter (· < a) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h => h.1.resolve_left (fun hx => lt_irrefl a (hx ▸ h.2)),
        fun h => ⟨Or.inr h, ha x h⟩⟩
    have h2 : ∀ k ∈ s, (insert a s).filter (· < k) = s.filter (· < k) := fun k hk => by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h => ⟨h.1.resolve_left (fun hx => absurd (hx ▸ h.2) (not_lt.2 (ha k hk).le)),
        h.2⟩, fun h => ⟨Or.inr h.1, h.2⟩⟩
    rw [sum_insert has, h1, sum_congr rfl fun k hk => by rw [h2 k hk], add_assoc, ih,
      card_insert_of_notMem has, pow_succ, mul_two]

/-- `∑_{k ∈ s} 2^{#{l ∈ s | k < l}} + 1 = 2^{#s}`, the mirror image of
`Finset.sum_two_pow_card_filter_lt_add_one`. -/
theorem sum_two_pow_card_filter_gt_add_one (s : Finset α) :
    ∑ k ∈ s, (2 : R) ^ #(s.filter (k < ·)) + 1 = 2 ^ #s := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h1 : (insert a s).filter (a < ·) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h => h.1.resolve_left (fun hx => lt_irrefl a (hx ▸ h.2)),
        fun h => ⟨Or.inr h, ha x h⟩⟩
    have h2 : ∀ k ∈ s, (insert a s).filter (k < ·) = s.filter (k < ·) := fun k hk => by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h => ⟨h.1.resolve_left (fun hx => absurd (hx ▸ h.2) (not_lt.2 (ha k hk).le)),
        h.2⟩, fun h => ⟨Or.inr h.1, h.2⟩⟩
    rw [sum_insert has, h1, sum_congr rfl fun k hk => by rw [h2 k hk], add_assoc, ih,
      card_insert_of_notMem has, pow_succ, mul_two]

end Finset

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]

/-! ### Interval counts on a finite linear order -/

section Counts

/-- The half-open intervals `(i, j]` and `[i, j)` hold the same number of indices when `i ≤ j`:
both are `[i, j]` with one endpoint removed. -/
theorem card_filter_lt_le_eq_card_filter_le_lt {i j : n} (hij : i ≤ j) :
    #{k | i < k ∧ k ≤ j} = #{k | i ≤ k ∧ k < j} := by
  have h1 : univ.filter (fun k => i ≤ k ∧ k ≤ j) =
      insert i (univ.filter fun k => i < k ∧ k ≤ j) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hik, hkj⟩
      rcases hik.eq_or_lt with rfl | hik
      · exact Or.inl rfl
      · exact Or.inr ⟨hik, hkj⟩
    · rintro (rfl | ⟨hik, hkj⟩)
      · exact ⟨le_rfl, hij⟩
      · exact ⟨hik.le, hkj⟩
  have h2 : univ.filter (fun k => i ≤ k ∧ k ≤ j) =
      insert j (univ.filter fun k => i ≤ k ∧ k < j) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hik, hkj⟩
      rcases hkj.eq_or_lt with rfl | hkj
      · exact Or.inl rfl
      · exact Or.inr ⟨hik, hkj⟩
    · rintro (rfl | ⟨hik, hkj⟩)
      · exact ⟨hij, le_rfl⟩
      · exact ⟨hik, hkj.le⟩
  have := congrArg Finset.card (h1.symm.trans h2)
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp)] at this
  omega

/-- The indices `≥ i` are `i` and the indices `> i`. -/
theorem filter_ge_eq_insert_filter_gt (i : n) :
    univ.filter (i ≤ ·) = insert i (univ.filter (i < ·)) := by
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  exact ⟨fun h => h.eq_or_lt.imp Eq.symm id, fun h => h.elim (fun h => h ▸ le_rfl) le_of_lt⟩

/-- `#{k | i ≤ k} = #{k | i < k} + 1`. -/
theorem card_filter_le_eq_card_filter_lt_add_one (i : n) :
    #{k | i ≤ k} = #{k | i < k} + 1 := by
  rw [filter_ge_eq_insert_filter_gt, card_insert_of_notMem (by simp)]

/-- Splitting a sum over `{r ≥ i}` into the term at `i` and the sum over `{r > i}`, the mirror
image of `Matrix.sum_filter_le_eq_add`. -/
theorem sum_filter_ge_eq_add {M : Type*} [AddCommMonoid M] (f : n → M) (i : n) :
    ∑ r ∈ univ.filter (i ≤ ·), f r = f i + ∑ r ∈ univ.filter (i < ·), f r := by
  rw [filter_ge_eq_insert_filter_gt, Finset.sum_insert (by simp)]

end Counts

variable {K : Type*} [Field K]

/-! ### Nonsingularity of triangular matrices -/

section IsUnit

variable {U L : Matrix n n K}

/-- An upper triangular matrix is nonsingular exactly when its diagonal has no zero entry
([quarteroni2000numerical] §3.2, first sentence): its determinant is the product of the diagonal. -/
theorem isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular (hU : U.IsUpperTriangular) :
    IsUnit U ↔ ∀ i, U i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hU, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

/-- A lower triangular matrix is nonsingular exactly when its diagonal has no zero entry. -/
theorem isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular (hL : L.IsLowerTriangular) :
    IsUnit L ↔ ∀ i, L i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular L hL, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  simp

omit [Fintype n] in
/-- An upper triangular matrix on `n` is a lower triangular matrix on the dual order `nᵒᵈ`. -/
theorem IsUpperTriangular.isLowerTriangular_orderDual (hU : U.IsUpperTriangular) :
    IsLowerTriangular (m := nᵒᵈ) U := fun i j h => hU (i := i) (j := j) h

omit [Fintype n] in
/-- A lower triangular matrix on `n` is an upper triangular matrix on the dual order `nᵒᵈ`. -/
theorem IsLowerTriangular.isUpperTriangular_orderDual (hL : L.IsLowerTriangular) :
    IsUpperTriangular (m := nᵒᵈ) L := fun i j h => hL (i := i) (j := j) h

end IsUnit

/-! ### Forward substitution -/

/-- **Forward substitution**, [quarteroni2000numerical] (3.22): `x i = (b i - ∑_{j < i} l_ij x_j) /
l_ii`, as one total function on a finite linear order, by well-founded recursion on the number of
indices below `i`. A zero diagonal entry gives junk (`x / 0 = 0`) rather than a hypothesis;
`Matrix.mulVec_forwardSubst` says when the result is the solution. -/
noncomputable def forwardSubst (L : Matrix n n K) (b : n → K) : n → K
  | i => (b i - ∑ j ∈ (univ.filter (· < i)).attach, L i j * forwardSubst L b j) / L i i
termination_by i => #{j | j < i}
decreasing_by exact card_filter_lt_lt_of_lt (mem_filter.1 j.2).2

section Forward

variable (L : Matrix n n K) (b : n → K)

/-- The recurrence of forward substitution, [quarteroni2000numerical] (3.22), without the
`attach`. -/
theorem forwardSubst_apply (i : n) :
    forwardSubst L b i = (b i - ∑ j ∈ univ.filter (· < i), L i j * forwardSubst L b j) / L i i := by
  rw [forwardSubst, Finset.sum_attach (univ.filter (· < i)) fun j => L i j * forwardSubst L b j]

variable {L}

/-- A row of `L x` for lower triangular `L` is the sum over the indices `≤ i`, split at `i`. -/
theorem mulVec_apply_of_isLowerTriangular (hL : L.IsLowerTriangular) (x : n → K) (i : n) :
    (L *ᵥ x) i = (∑ j ∈ univ.filter (· < i), L i j * x j) + L i i * x i := by
  rw [mulVec, dotProduct, ← sum_filter_le_eq_add]
  refine (Finset.sum_filter_of_ne fun j _ hj => ?_).symm
  by_contra h
  exact hj (by rw [hL (OrderDual.toDual_lt_toDual.2 (not_le.1 h)), zero_mul])

/-- **Correctness of forward substitution**: for a lower triangular `L` with nowhere-zero diagonal,
`L (forwardSubst L b) = b`. -/
theorem mulVec_forwardSubst (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) :
    L *ᵥ forwardSubst L b = b := by
  ext i
  rw [mulVec_apply_of_isLowerTriangular hL, forwardSubst_apply, mul_div_cancel₀ _ (hd i),
    add_sub_cancel]

/-- The solution of a nonsingular lower triangular system is unique, and it is the one forward
substitution computes. -/
theorem forwardSubst_eq_of_mulVec_eq (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) {x : n → K}
    (hx : L *ᵥ x = b) : forwardSubst L b = x :=
  mulVec_injective_iff_isUnit.2 ((isUnit_iff_forall_diag_ne_zero_of_isLowerTriangular hL).2 hd)
    (by rw [mulVec_forwardSubst b hL hd, hx])

end Forward

/-! ### Backward substitution -/

/-- **Backward substitution**, [quarteroni2000numerical] (3.23): `x i = (b i - ∑_{j > i} u_ij x_j)
/ u_ii`, by well-founded recursion on the number of indices above `i`. It is forward substitution
on the dual order (`Matrix.backSubst_eq_forwardSubst_toDual`). -/
noncomputable def backSubst (U : Matrix n n K) (b : n → K) : n → K
  | i => (b i - ∑ j ∈ (univ.filter (i < ·)).attach, U i j * backSubst U b j) / U i i
termination_by i => #{j | i < j}
decreasing_by exact card_filter_lt_lt_of_lt (n := nᵒᵈ) (mem_filter.1 j.2).2

section Backward

variable (U : Matrix n n K) (b : n → K)

/-- The recurrence of backward substitution, [quarteroni2000numerical] (3.23), without the
`attach`. -/
theorem backSubst_apply (i : n) :
    backSubst U b i = (b i - ∑ j ∈ univ.filter (i < ·), U i j * backSubst U b j) / U i i := by
  rw [backSubst, Finset.sum_attach (univ.filter (i < ·)) fun j => U i j * backSubst U b j]

/-- Backward substitution is forward substitution on the dual order `nᵒᵈ`: the two recurrences
coincide term by term, by strong induction downwards. -/
theorem backSubst_eq_forwardSubst_toDual : backSubst U b = forwardSubst (n := nᵒᵈ) U b := by
  funext i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
  rw [backSubst_apply]
  refine Eq.trans ?_ (forwardSubst_apply (n := nᵒᵈ) U b i).symm
  congr 2
  refine Finset.sum_equiv OrderDual.toDual (fun j => ?_) fun j hj => ?_
  · simp only [mem_filter, mem_univ, true_and]
    exact Iff.rfl
  · rw [ih j (mem_filter.1 hj).2]
    rfl

variable {U}

/-- A row of `U x` for upper triangular `U` is the sum over the indices `≥ i`, split at `i`. -/
theorem mulVec_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (x : n → K) (i : n) :
    (U *ᵥ x) i = U i i * x i + ∑ j ∈ univ.filter (i < ·), U i j * x j := by
  rw [mulVec, dotProduct, ← sum_filter_ge_eq_add (fun j => U i j * x j) i]
  refine (Finset.sum_filter_of_ne fun j _ hj => ?_).symm
  by_contra h
  exact hj (by rw [hU (not_le.1 h), zero_mul])

/-- **Correctness of backward substitution**: for an upper triangular `U` with nowhere-zero
diagonal, `U (backSubst U b) = b`. -/
theorem mulVec_backSubst (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) :
    U *ᵥ backSubst U b = b := by
  ext i
  rw [mulVec_apply_of_isUpperTriangular hU, backSubst_apply, mul_div_cancel₀ _ (hd i),
    sub_add_cancel]

/-- The solution of a nonsingular upper triangular system is unique, and it is the one backward
substitution computes. -/
theorem backSubst_eq_of_mulVec_eq (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {x : n → K}
    (hx : U *ᵥ x = b) : backSubst U b = x :=
  mulVec_injective_iff_isUnit.2 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd)
    (by rw [mulVec_backSubst b hU hd, hx])

end Backward

/-! ### Solving through an LU factorization -/

section LUSolve

variable (L U : Matrix n n K) (b : n → K)

/-- Solving `A x = b` through a factorization `A = L U`: `L y = b` by forward substitution, then
`U x = y` by backward substitution ([quarteroni2000numerical] §3.3.1). -/
noncomputable def luSolve : n → K :=
  backSubst U (forwardSubst L b)

variable {L U}

/-- **The LU solve is correct**: if `A = L U` with nonzero pivots, `A (luSolve L U b) = b`. -/
theorem mulVec_luSolve {A : Matrix n n K} (h : IsLU A L U) (hd : ∀ i, U i i ≠ 0) :
    A *ᵥ luSolve L U b = b := by
  rw [luSolve, ← h.mul_eq, ← mulVec_mulVec, mulVec_backSubst _ h.isUpperTriangular hd,
    mulVec_forwardSubst _ h.isUnitLowerTriangular.isLowerTriangular fun i => by
      rw [h.isUnitLowerTriangular.diag_eq_one]; exact one_ne_zero]

/-- **The LU solve with a row permutation**: if `P A = L U` for a nonsingular `P` and the pivots
are nonzero, then solving `L y = P b`, `U x = y` solves `A x = b`
([quarteroni2000numerical] §3.5). -/
theorem mulVec_luSolve_of_mul {P A : Matrix n n K} (hP : IsUnit P) (h : IsLU (P * A) L U)
    (hd : ∀ i, U i i ≠ 0) : A *ᵥ luSolve L U (P *ᵥ b) = b := by
  have := mulVec_luSolve (P *ᵥ b) h hd
  rw [← mulVec_mulVec] at this
  exact mulVec_injective_iff_isUnit.2 hP this

/-- A permutation matrix is a unit: its determinant is the sign of the permutation. -/
theorem isUnit_permMatrix (σ : Equiv.Perm n) : IsUnit (σ.permMatrix K) := by
  rw [isUnit_iff_isUnit_det, det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The LU solve with partial pivoting**, [quarteroni2000numerical] §3.5: if `P A = L U` for a
permutation matrix `P`, then `x = luSolve L U (P b)` solves `A x = b`. -/
theorem mulVec_luSolve_permMatrix {A : Matrix n n K} {σ : Equiv.Perm n}
    (h : IsLU (σ.permMatrix K * A) L U) (hd : ∀ i, U i i ≠ 0) :
    A *ᵥ luSolve L U (σ.permMatrix K *ᵥ b) = b :=
  mulVec_luSolve_of_mul b (isUnit_permMatrix σ) h hd

end LUSolve

/-! ### The inverse of a triangular matrix -/

section Inverse

variable {U : Matrix n n K}

/-- [quarteroni2000numerical] (3.26): the columns of `U⁻¹` are the backward-substitution
solutions of the systems `U v_i = e_i`. -/
theorem inv_col_eq_backSubst (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (i : n) :
    (fun r => U⁻¹ r i) = backSubst U (Pi.single i 1) := by
  have hUd : IsUnit U.det :=
    (isUnit_iff_isUnit_det U).1 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd)
  refine (backSubst_eq_of_mulVec_eq _ hU hd ?_).symm
  have : (fun r => U⁻¹ r i) = U⁻¹ *ᵥ Pi.single i 1 := (mulVec_single_one _ _).symm
  rw [this, mulVec_mulVec, mul_nonsing_inv U hUd, one_mulVec]

/-- [quarteroni2000numerical] (3.27): the leading block `U⁻¹(≤ k)` of the inverse of an upper
triangular matrix is the inverse of the leading block `U(≤ k)`, so the nonzero part of each column
of `U⁻¹` is found from a leading-block system. Reading `U U⁻¹ = 1` on the block `(≤ k, ≤ k)`, the
cross term vanishes because `U⁻¹` is upper triangular. -/
theorem inv_toBlock_le_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (k : n) : (U.toBlock (· ≤ k) (· ≤ k))⁻¹ = U⁻¹.toBlock (· ≤ k) (· ≤ k) := by
  have hUd : IsUnit U.det :=
    (isUnit_iff_isUnit_det U).1 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd)
  refine inv_eq_right_inv ?_
  have hz : U⁻¹.toBlock (fun i => ¬i ≤ k) (fun i => i ≤ k) = 0 :=
    hU.inv.not_toBlock_eq_zero (b := id) (p := (· ≤ k)) fun _ _ hi hji => hji.trans hi
  have := toBlock_mul_eq_add' (· ≤ k) (· ≤ k) (· ≤ k) U U⁻¹
  rw [mul_nonsing_inv U hUd, toBlock_one_self, hz, Matrix.mul_zero, add_zero] at this
  exact this.symm

/-- The diagonal of the inverse of an upper triangular matrix is the inverse of the diagonal:
`(U⁻¹)_kk = 1 / u_kk`, the first line of [quarteroni2000numerical] (3.28). -/
theorem inv_apply_self_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (k : n) : U⁻¹ k k = (U k k)⁻¹ := by
  have hUd : IsUnit U.det :=
    (isUnit_iff_isUnit_det U).1 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd)
  have h := congrFun (congrFun (mul_nonsing_inv U hUd) k) k
  rw [hU.mul_apply_self hU.inv, one_apply_eq] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Below the diagonal the inverse of an upper triangular matrix vanishes. -/
theorem inv_apply_of_isUpperTriangular_of_lt (hU : U.IsUpperTriangular) {i k : n} (hki : k < i) :
    U⁻¹ i k = 0 :=
  hU.inv hki

/-- The entry `(i, k)` of `U U⁻¹ = 1` above the diagonal, with the vanishing terms removed:
`u_ii (U⁻¹)_ik = -∑_{i < j ≤ k} u_ij (U⁻¹)_jk`. -/
theorem diag_mul_inv_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    {i k : n} (hik : i < k) :
    U i i * U⁻¹ i k = -∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), U i j * U⁻¹ j k := by
  have hUd : IsUnit U.det :=
    (isUnit_iff_isUnit_det U).1 ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hU).2 hd)
  have h := congrFun (congrFun (mul_nonsing_inv U hUd) i) k
  rw [mul_apply, one_apply_ne hik.ne,
    ← Finset.sum_filter_of_ne (p := fun j => i ≤ j ∧ j ≤ k) fun j _ hj => ?_,
    show univ.filter (fun j => i ≤ j ∧ j ≤ k) = insert i (univ.filter fun j => i < j ∧ j ≤ k)
      from ?_, Finset.sum_insert (by simp)] at h
  · exact eq_neg_of_add_eq_zero_left h
  · ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hij, hjk⟩
      rcases hij.eq_or_lt with rfl | hij
      · exact Or.inl rfl
      · exact Or.inr ⟨hij, hjk⟩
    · rintro (rfl | ⟨hij, hjk⟩)
      · exact ⟨le_rfl, hik.le⟩
      · exact ⟨hij.le, hjk⟩
  · by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    rcases hcon with hji | hkj
    · exact hj (by rw [hU hji, zero_mul])
    · exact hj (by rw [hU.inv hkj, mul_zero])

/-- **The inversion recurrence for upper triangular matrices**, [quarteroni2000numerical] (3.28):
above the diagonal, `(U⁻¹)_ik = -u_ii⁻¹ ∑_{i < j ≤ k} u_ij (U⁻¹)_jk`; together with
`Matrix.inv_apply_self_of_isUpperTriangular` (`(U⁻¹)_kk = u_kk⁻¹`) and
`Matrix.inv_apply_of_isUpperTriangular_of_lt` (zero below the diagonal) this computes `U⁻¹` column
by column, each column from the bottom up. -/
theorem inv_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {i k : n}
    (hik : i < k) :
    U⁻¹ i k = -(U i i)⁻¹ * ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), U i j * U⁻¹ j k := by
  rw [neg_mul, ← mul_neg, eq_inv_mul_iff_mul_eq₀ (hd i)]
  exact diag_mul_inv_apply_of_isUpperTriangular hU hd hik

end Inverse

end Matrix

/-! ### The bounds of Higham on `|U⁻¹| |U|` -/

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {U : Matrix n n K}

section Higham

/-- The triangle inequality applied to the inversion recurrence: for `i < k`,
`|u_ii| |(U⁻¹)_ik| ≤ ∑_{i < j ≤ k} |u_ij| |(U⁻¹)_jk|`. -/
theorem abs_diag_mul_abs_inv_apply_le (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {i k : n}
    (hik : i < k) :
    |U i i| * |U⁻¹ i k| ≤ ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), |U i j| * |U⁻¹ j k| := by
  rw [← abs_mul, diag_mul_inv_apply_of_isUpperTriangular hU hd hik, abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _)

/-- The entrywise product `(|U⁻¹| |U|)_ij` vanishes below the diagonal. -/
theorem abs_inv_mul_abs_apply_of_lt (hU : U.IsUpperTriangular) {i j : n} (hji : j < i) :
    (U⁻¹.abs * U.abs) i j = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hki | hik
  · rw [abs_apply, hU.inv hki, abs_zero, zero_mul]
  · rw [abs_apply U, hU (hji.trans_le hik), abs_zero, mul_zero]

/-- On and above the diagonal, `(|U⁻¹| |U|)_ij` is the sum over the indices `i ≤ k ≤ j`. -/
theorem abs_inv_mul_abs_apply_eq_sum (hU : U.IsUpperTriangular) (i j : n) :
    (U⁻¹.abs * U.abs) i j = ∑ k ∈ univ.filter (fun k => i ≤ k ∧ k ≤ j), |U⁻¹ i k| * |U k j| := by
  rw [mul_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hki | hjk
  · exact hk (by rw [abs_apply, hU.inv hki, abs_zero, zero_mul])
  · exact hk (by rw [abs_apply U, hU hjk, abs_zero, mul_zero])

/-- The normalized entry `|(U⁻¹)_kk| |u_kk|` is `1`. -/
theorem abs_inv_apply_self_mul_abs_diag (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (k : n) :
    |U⁻¹ k k| * |U k k| = 1 := by
  rw [inv_apply_self_of_isUpperTriangular hU hd, abs_inv, inv_mul_cancel₀ (abs_ne_zero.2 (hd k))]

/-- The normalized entries `a_ik = |(U⁻¹)_ik| |u_kk|` (the entries of `|V⁻¹|` for `V = D⁻¹ U`)
satisfy `a_ik ≤ ∑_{i < j ≤ k} (|u_ij| / |u_ii|) a_jk` for `i < k`. -/
theorem abs_inv_apply_mul_abs_diag_le_sum (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    {i k : n} (hik : i < k) :
    |U⁻¹ i k| * |U k k| ≤
      ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), |U i j| / |U i i| * (|U⁻¹ j k| * |U k k|) := by
  have hii : 0 < |U i i| := abs_pos.2 (hd i)
  have h := abs_diag_mul_abs_inv_apply_le hU hd hik
  rw [← le_div_iff₀' hii, Finset.sum_div] at h
  refine (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans_eq ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **[higham2002accuracy] Lemma 8.6, the inner bound**: if `|u_ii| ≥ |u_ij|` for `j > i`, then
`|(U⁻¹)_ik| |u_kk| ≤ 2^{#(i, k)}` for `i < k`, where `#(i, k)` counts the indices strictly between
`i` and `k` (the book's `2^{k-i-1}`). By downward induction on `i`: the recurrence bounds `a_ik` by
`1 + ∑_{i < j < k} a_jk ≤ 1 + ∑_{i < j < k} 2^{#(j, k)} = 2^{#(i, k)}`. -/
theorem abs_inv_apply_mul_abs_diag_le_two_pow (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {i k : n} (hik : i < k) :
    |U⁻¹ i k| * |U k k| ≤ 2 ^ #{l | i < l ∧ l < k} := by
  induction i using WellFoundedGT.induction with
  | ind i ih =>
  refine (abs_inv_apply_mul_abs_diag_le_sum hU hd hik).trans ?_
  have hii : 0 < |U i i| := abs_pos.2 (hd i)
  -- each coefficient `|u_ij| / |u_ii|` is at most `1`, and the terms are nonnegative
  have hterm : ∀ j ∈ univ.filter (fun j => i < j ∧ j ≤ k),
      |U i j| / |U i i| * (|U⁻¹ j k| * |U k k|) ≤ |U⁻¹ j k| * |U k k| := fun j hj => by
    have hj' := (mem_filter.1 hj).2
    refine mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    rw [div_le_one hii]
    exact hrow i j hj'.1
  refine (Finset.sum_le_sum hterm).trans ?_
  -- split off the term `j = k`, which is `1`
  have hsplit : univ.filter (fun j => i < j ∧ j ≤ k) =
      insert k (univ.filter fun j => i < j ∧ j < k) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hij, hjk⟩
      rcases hjk.eq_or_lt with rfl | hjk
      · exact Or.inl rfl
      · exact Or.inr ⟨hij, hjk⟩
    · rintro (rfl | ⟨hij, hjk⟩)
      · exact ⟨hik, le_rfl⟩
      · exact ⟨hij, hjk.le⟩
  rw [hsplit, Finset.sum_insert (by simp), abs_inv_apply_self_mul_abs_diag hU hd]
  -- the remaining terms, by the induction hypothesis and the geometric sum
  have hih : ∀ j ∈ univ.filter (fun j => i < j ∧ j < k),
      |U⁻¹ j k| * |U k k| ≤ 2 ^ #((univ.filter fun j => i < j ∧ j < k).filter (j < ·)) :=
    fun j hj => by
      have hj' := (mem_filter.1 hj).2
      refine (ih j hj'.1 hj'.2).trans_eq ?_
      congr 2
      ext l
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => ⟨⟨hj'.1.trans h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have hgeom := Finset.sum_two_pow_card_filter_gt_add_one (R := K)
    (univ.filter fun j => i < j ∧ j < k)
  calc 1 + ∑ j ∈ univ.filter (fun j => i < j ∧ j < k), |U⁻¹ j k| * |U k k|
      ≤ 1 + ∑ j ∈ univ.filter (fun j => i < j ∧ j < k),
          (2 : K) ^ #((univ.filter fun j => i < j ∧ j < k).filter (j < ·)) := by
        gcongr with j hj
        exact hih j hj
    _ = 2 ^ #{l | i < l ∧ l < k} := by rw [add_comm, hgeom]

/-- **[higham2002accuracy] Lemma 8.6**: if `U` is upper triangular with nowhere-zero diagonal and
`|u_ii| ≥ |u_ij|` for all `j > i` (as for the triangular factors of Gaussian elimination with
pivoting, or of a QR factorization with column pivoting), then for `i ≤ j`
`(|U⁻¹| |U|)_ij ≤ 2^{#[i, j)}`, the book's `2^{j-i}`; below the diagonal the entry is `0`
(`Matrix.abs_inv_mul_abs_apply_of_lt`). This is the bound behind the componentwise error estimate
of substitution in [quarteroni2000numerical] §3.2.2. -/
theorem abs_inv_mul_abs_apply_le_two_pow (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {i j : n} (hij : i ≤ j) :
    (U⁻¹.abs * U.abs) i j ≤ 2 ^ #{k | i ≤ k ∧ k < j} := by
  rw [abs_inv_mul_abs_apply_eq_sum hU, ← card_filter_lt_le_eq_card_filter_le_lt hij]
  -- bound `|u_kj|` by `|u_kk|`
  have hterm : ∀ k ∈ univ.filter (fun k => i ≤ k ∧ k ≤ j),
      |U⁻¹ i k| * |U k j| ≤ |U⁻¹ i k| * |U k k| := fun k hk => by
    have hk' := (mem_filter.1 hk).2
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases hk'.2.eq_or_lt with rfl | hkj
    · exact le_rfl
    · exact hrow k j hkj
  refine (Finset.sum_le_sum hterm).trans ?_
  -- split off the term `k = i`, which is `1`
  have hsplit : univ.filter (fun k => i ≤ k ∧ k ≤ j) =
      insert i (univ.filter fun k => i < k ∧ k ≤ j) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨hik, hkj⟩
      rcases hik.eq_or_lt with rfl | hik
      · exact Or.inl rfl
      · exact Or.inr ⟨hik, hkj⟩
    · rintro (rfl | ⟨hik, hkj⟩)
      · exact ⟨le_rfl, hij⟩
      · exact ⟨hik.le, hkj⟩
  rw [hsplit, Finset.sum_insert (by simp), abs_inv_apply_self_mul_abs_diag hU hd]
  have hih : ∀ k ∈ univ.filter (fun k => i < k ∧ k ≤ j),
      |U⁻¹ i k| * |U k k| ≤ 2 ^ #((univ.filter fun k => i < k ∧ k ≤ j).filter (· < k)) :=
    fun k hk => by
      have hk' := (mem_filter.1 hk).2
      refine (abs_inv_apply_mul_abs_diag_le_two_pow hU hd hrow hk'.1).trans_eq ?_
      congr 2
      ext l
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => ⟨⟨h.1, h.2.le.trans hk'.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  have hgeom := Finset.sum_two_pow_card_filter_lt_add_one (R := K)
    (univ.filter fun k => i < k ∧ k ≤ j)
  calc 1 + ∑ k ∈ univ.filter (fun k => i < k ∧ k ≤ j), |U⁻¹ i k| * |U k k|
      ≤ 1 + ∑ k ∈ univ.filter (fun k => i < k ∧ k ≤ j),
          (2 : K) ^ #((univ.filter fun k => i < k ∧ k ≤ j).filter (· < k)) := by
        gcongr with k hk
        exact hih k hk
    _ = 2 ^ #{k | i < k ∧ k ≤ j} := by rw [add_comm, hgeom]

/-- **[higham2002accuracy] Lemma 8.6, the row sums**: under its hypotheses,
`∑_j (|U⁻¹| |U|)_ij ≤ 2^{#{k | i ≤ k}} - 1`, the book's `2^{n-i+1} - 1`, so that
`‖|U⁻¹| |U|‖_∞ ≤ 2^n - 1` (his `cond(U) ≤ 2^n - 1`, and the `2^{n-i+1}` of Theorem 8.7). -/
theorem sum_abs_inv_mul_abs_apply_le_two_pow (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) (i : n) :
    ∑ j, (U⁻¹.abs * U.abs) i j ≤ 2 ^ #{k | i ≤ k} - 1 := by
  rw [← Finset.sum_filter_of_ne (p := (i ≤ ·)) fun j _ hj => ?_]
  · have hgeom := Finset.sum_two_pow_card_filter_lt_add_one (R := K) (univ.filter (i ≤ ·))
    rw [le_sub_iff_add_le, ← hgeom]
    gcongr with j hj
    have hj' := (mem_filter.1 hj).2
    refine (abs_inv_mul_abs_apply_le_two_pow hU hd hrow hj').trans_eq ?_
    congr 2
    ext l
    simp only [mem_filter, mem_univ, true_and]
  · by_contra h
    exact hj (abs_inv_mul_abs_apply_of_lt hU (not_le.1 h))

end Higham

/-! #### Row diagonally dominant triangular matrices -/

section DiagDominant

/-- Row diagonal dominance bounds every off-diagonal entry by the diagonal one. -/
theorem abs_apply_le_abs_diag_of_sum_le (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|)
    {i j : n} (hij : j ≠ i) : |U i j| ≤ |U i i| :=
  (Finset.single_le_sum (f := fun j => |U i j|) (fun _ _ => abs_nonneg _)
    (mem_erase.2 ⟨hij, mem_univ j⟩)).trans (hdom i)

/-- **[higham2002accuracy] Lemma 8.8, the inner bound**: for a row diagonally dominant upper
triangular `U` with nowhere-zero diagonal, the normalized inverse `|(U⁻¹)_ik| |u_kk|` (the entry of
`|V⁻¹|` for `V = D⁻¹ U`) is at most `1`. By downward induction on `i`: `a_ik ≤ ∑_{i < j ≤ k}
(|u_ij| / |u_ii|) a_jk ≤ ∑_{j ≠ i} |u_ij| / |u_ii| ≤ 1`. -/
theorem abs_inv_apply_mul_abs_diag_le_one (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) (i k : n) :
    |U⁻¹ i k| * |U k k| ≤ 1 := by
  rcases lt_trichotomy k i with hki | rfl | hik
  · rw [hU.inv hki, abs_zero, zero_mul]
    exact zero_le_one
  · exact (abs_inv_apply_self_mul_abs_diag hU hd k).le
  induction i using WellFoundedGT.induction with
  | ind i ih =>
  refine (abs_inv_apply_mul_abs_diag_le_sum hU hd hik).trans ?_
  have hii : 0 < |U i i| := abs_pos.2 (hd i)
  calc ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), |U i j| / |U i i| * (|U⁻¹ j k| * |U k k|)
      ≤ ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), |U i j| / |U i i| := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_of_le_one_right (div_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
        have hj' := (mem_filter.1 hj).2
        rcases hj'.2.eq_or_lt with rfl | hjk
        · exact (abs_inv_apply_self_mul_abs_diag hU hd j).le
        · exact ih j hj'.1 hjk
    _ ≤ ∑ j ∈ univ.erase i, |U i j| / |U i i| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_)
          fun _ _ _ => div_nonneg (abs_nonneg _) (abs_nonneg _)
        exact mem_erase.2 ⟨(mem_filter.1 hj).2.1.ne', mem_univ j⟩
    _ ≤ 1 := by
        rw [← Finset.sum_div, div_le_one hii]
        exact hdom i

/-- **[higham2002accuracy] Lemma 8.8, entrywise**: for a row diagonally dominant upper triangular
`U` with nowhere-zero diagonal and `i ≤ j`, `(|U⁻¹| |U|)_ij ≤ #[i, j]`, the number of indices
between `i` and `j` inclusive (the book's `j - i + 1`; Higham states the weaker `i + j - 1`).
Below the diagonal the entry is `0` (`Matrix.abs_inv_mul_abs_apply_of_lt`). This is the bound
behind the "diagonally dominant" clause of [quarteroni2000numerical] §3.2.2. -/
theorem abs_inv_mul_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) {i j : n}
    (hij : i ≤ j) : (U⁻¹.abs * U.abs) i j ≤ #{k | i ≤ k ∧ k ≤ j} := by
  rw [abs_inv_mul_abs_apply_eq_sum hU, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := (mem_filter.1 hk).2
  refine le_trans ?_ (abs_inv_apply_mul_abs_diag_le_one hU hd hdom i k)
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases hk'.2.eq_or_lt with rfl | hkj
  · exact le_rfl
  · exact abs_apply_le_abs_diag_of_sum_le hdom hkj.ne'

/-- The row sums of `|U|` for a row diagonally dominant upper triangular `U`: at most `2 |u_kk|`,
and exactly `|u_kk|` in the last row (which has no entry to the right of the diagonal). -/
theorem sum_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) (k : n) :
    ∑ j, |U k j| ≤ |U k k| * if ∃ j, k < j then 2 else 1 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ k)]
  split_ifs with h
  · linarith [hdom k]
  · push Not at h
    rw [Finset.sum_eq_zero fun j hj => ?_, add_zero, mul_one]
    exact abs_eq_zero.2 (hU (lt_of_le_of_ne (h j) (mem_erase.1 hj).1))

/-- **[higham2002accuracy] Lemma 8.8, the row sums**: for a row diagonally dominant upper
triangular `U` with nowhere-zero diagonal, `∑_j (|U⁻¹| |U|)_ij ≤ 2 #{k | i < k} + 1`, the book's
`2(n - i) + 1`; so `‖|U⁻¹| |U|‖_∞ ≤ 2n - 1`
(`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`), his `cond(U) ≤ 2n - 1`, which is also
the constant of [quarteroni2000numerical] §3.1.2. The proof is his:
`|V⁻¹| |V| e ≤ |V⁻¹| (2, …, 2, 1)ᵀ` with the entries of `|V⁻¹|` at most `1`. -/
theorem sum_abs_inv_mul_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) (i : n) :
    ∑ j, (U⁻¹.abs * U.abs) i j ≤ 2 * #{k | i < k} + 1 := by
  -- the sum as `∑_k |(U⁻¹)_ik| ∑_j |u_kj|`, restricted to `k ≥ i`
  have h1 : ∑ j, (U⁻¹.abs * U.abs) i j =
      ∑ k ∈ univ.filter (i ≤ ·), |U⁻¹ i k| * ∑ j, |U k j| := by
    simp only [mul_apply, abs_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    by_contra h
    exact hk (Finset.sum_eq_zero fun j _ => by rw [hU.inv (not_le.1 h), abs_zero, zero_mul])
  rw [h1]
  -- the termwise bound `|(U⁻¹)_ik| ∑_j |u_kj| ≤ c_k` with `c_k = 2` or `1`
  have h2 : ∀ k ∈ univ.filter (i ≤ ·),
      |U⁻¹ i k| * ∑ j, |U k j| ≤ if ∃ j, k < j then 2 else 1 := fun k _ => by
    calc |U⁻¹ i k| * ∑ j, |U k j|
        ≤ |U⁻¹ i k| * (|U k k| * if ∃ j, k < j then 2 else 1) :=
          mul_le_mul_of_nonneg_left (sum_abs_apply_le_of_isDiagDominant hU hdom k) (abs_nonneg _)
      _ = |U⁻¹ i k| * |U k k| * if ∃ j, k < j then 2 else 1 := by ring
      _ ≤ 1 * if ∃ j, k < j then 2 else 1 :=
          mul_le_mul_of_nonneg_right (abs_inv_apply_mul_abs_diag_le_one hU hd hdom i k)
            (by split_ifs <;> norm_num)
      _ = if ∃ j, k < j then 2 else 1 := one_mul _
  refine (Finset.sum_le_sum h2).trans ?_
  -- `∑_{k ≥ i} c_k = #{k ≥ i} + #{k ≥ i, k not maximal} ≤ 2 #{k > i} + 1`
  have h3 : ∀ k : n, (if ∃ j, k < j then (2 : K) else 1) = 1 + if ∃ j, k < j then 1 else 0 := by
    intro k
    split_ifs <;> norm_num
  simp only [h3, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_boole]
  rw [card_filter_le_eq_card_filter_lt_add_one, Finset.filter_filter]
  have h4 : #(univ.filter fun k => i ≤ k ∧ ∃ j, k < j) ≤ #{k | i < k} := by
    have hM := Finset.exists_max_image univ id (univ_nonempty_iff.2 ⟨i⟩)
    obtain ⟨M, -, hM⟩ := hM
    have hle : ∀ k, k ≤ M := fun k => hM k (mem_univ k)
    calc #(univ.filter fun k => i ≤ k ∧ ∃ j, k < j) ≤ #((univ.filter (i ≤ ·)).erase M) := by
          refine Finset.card_le_card fun k hk => ?_
          simp only [mem_filter, mem_univ, true_and] at hk
          obtain ⟨hik, j, hkj⟩ := hk
          exact mem_erase.2 ⟨fun h => absurd (h ▸ hkj) (not_lt.2 (hle j)), by simpa using hik⟩
      _ = #{k | i < k} := by
          rw [Finset.card_erase_of_mem (by simpa using hle i),
            card_filter_le_eq_card_filter_lt_add_one, Nat.add_sub_cancel]
  have h5 : ((#(univ.filter fun k => i ≤ k ∧ ∃ j, k < j) : ℕ) : K) ≤ #{k | i < k} := by
    exact_mod_cast h4
  push_cast
  linarith

/-- `‖|U⁻¹| |U|‖_∞ ≤ 2n - 1` for a row diagonally dominant upper triangular `U`
([higham2002accuracy] Lemma 8.8): every row sum of `|U⁻¹| |U|` is at most `2 card n - 1`. -/
theorem sum_abs_inv_mul_abs_apply_le_of_isDiagDominant' (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : ∀ i, ∑ j ∈ univ.erase i, |U i j| ≤ |U i i|) (i : n) :
    ∑ j, (U⁻¹.abs * U.abs) i j ≤ 2 * Fintype.card n - 1 := by
  refine (sum_abs_inv_mul_abs_apply_le_of_isDiagDominant hU hd hdom i).trans ?_
  have h : #{k | i < k} + 1 ≤ Fintype.card n := by
    rw [← card_filter_le_eq_card_filter_lt_add_one, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h' : ((#{k | i < k} : ℕ) : K) + 1 ≤ Fintype.card n := by exact_mod_cast h
  linarith

end DiagDominant

end Matrix
