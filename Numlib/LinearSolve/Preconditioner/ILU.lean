import Mathlib.Tactic.FieldSimp
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearSolve.Stationary.RegularSplitting

/-!
# Incomplete `LU` factorizations

An *incomplete* `LU` factorization of a square matrix `A` is a pair `L`, `U` — unit lower
triangular and upper triangular — that both vanish on a prescribed *zero pattern*
`P ⊆ n × n` and whose product agrees with `A` off that pattern. Writing `R = L U - A` for the
residual, `A = L U - R` is a splitting of `A` whose `M` factor is cheap to apply, and `R` is
supported in `P`.

## The declarative definition

`Matrix.IsILU P A L U` states exactly the five constraints above, and not an algorithm.
[Saad][saad2003iterative] §10.3.1 gives several loop orders (`KIJ`, `IKJ`) that compute such
factors, proves that two of them agree, and observes before Algorithm 10.4 that the factors are in
general not unique. Each loop order produces factors satisfying `Matrix.IsILU`, every downstream
statement of §10.3–10.5 uses only these constraints, and no uniqueness is available to be exploited;
so the constraints are the definition here. `Matrix.IsILU0`, taking `P` to be the off-diagonal zero
pattern `Matrix.zeroPattern A` of `A` itself, is the level-zero factorization `ILU(0)`.

`Matrix.IsMILU` is the *modified* variant of §10.3.5: the constraints hold off the diagonal, and
the diagonal is chosen so that the row sums of `L U` and of `A` agree, which is what makes the
preconditioner exact on constant vectors.

## Existence for M-matrices

The theorem of the chapter is that an M-matrix (`Matrix.IsMMatrix`) admits an incomplete
factorization for *every* zero pattern avoiding the diagonal, that no pivot vanishes, and that `A =
L U - R` is then a regular splitting, hence a convergent iteration (`Matrix.IsMMatrix.exists_isILU`
and `Matrix.IsILU.isRegular`). This is due to [Meijerink and van der Vorst][meijerink1977iterative];
the induction rests on Ky Fan's theorem [fan1960note], that one step of Gaussian elimination applied
to an M-matrix produces an M-matrix (`Matrix.IsMMatrix.isMMatrix_schurComplementSingle`), and on the
comparison theorem `Matrix.IsMMatrix.of_entrywiseLE` of `Numlib/LinearAlgebra/Matrix/MMatrix`, which
is what makes the *dropping* step legitimate: discarding a nonpositive off-diagonal entry moves the
matrix up in the entrywise order, and an entrywise-larger matrix with nonpositive off-diagonal
entries is again an M-matrix.

The elimination step is taken in the form `Matrix.elimStep`, which keeps the index type fixed:
it is `G⁻¹ A` for the unipotent `G = Matrix.elimMul A p` carrying the multipliers of column `p`,
so the accumulated `L` factor is a product of such matrices and no reindexing appears. The
`1 × 1`-pivot Schur complement `Matrix.schurComplementSingle` of
`Numlib/LinearAlgebra/Matrix/SchurComplement` is the same step read on the smaller index type, and
Ky Fan's theorem is stated there.

## Threshold factorizations

`Matrix.IsMHat` is the weaker class of matrices for which the ILUT existence theorem of §10.4.1
holds: positive diagonal except possibly in the last row, nonpositive off-diagonal entries, and a
strictly negative sum of the entries to the right of the diagonal in every row but the last. No
nonsingularity and no nonnegative inverse are assumed. `Matrix.IsMHat.ilut_rows` is the resulting
theorem, stated over the abstract row recurrence rather than over an algorithm.
-/

open Finset
open scoped Matrix

namespace Matrix

variable {n α : Type*}

/-! ### The declarative definition -/

section ZeroPattern

variable [Zero α]

/-- **The off-diagonal zero pattern of `A`** (Saad, *Iterative Methods for Sparse Linear Systems*,
§10.3.2): the positions off the diagonal at which `A` vanishes.

Taking it as the zero pattern of an incomplete factorization gives `ILU(0)`, whose factors have
the sparsity of the lower and upper parts of `A`. -/
def zeroPattern (A : Matrix n n α) : Set (n × n) := {p | A p.1 p.2 = 0 ∧ p.1 ≠ p.2}

/-- Membership in the off-diagonal zero pattern, entry by entry. -/
@[simp]
theorem mem_zeroPattern {A : Matrix n n α} {p : n × n} :
    p ∈ A.zeroPattern ↔ A p.1 p.2 = 0 ∧ p.1 ≠ p.2 := Iff.rfl

/-- The off-diagonal zero pattern avoids the diagonal, which is the hypothesis under which the
existence theorem `Matrix.IsMMatrix.exists_isILU` applies. -/
theorem diag_notMem_zeroPattern (A : Matrix n n α) (i : n) : (i, i) ∉ A.zeroPattern :=
  fun h => h.2 rfl

end ZeroPattern

section Defs

variable [Fintype n] [Preorder n] [Semiring α]

/-- The *shape* constraints on a pair of incomplete factors for the zero pattern `P`: `L` is unit
lower triangular, `U` is upper triangular, and both vanish on `P`.

This is the part of `Matrix.IsILU` that does not mention the matrix being factored; it is shared
with the modified factorization `Matrix.IsMILU`. -/
structure IsILUFactors (P : Set (n × n)) (L U : Matrix n n α) : Prop where
  /-- `L` has a unit diagonal. -/
  l_diag : ∀ i, L i i = 1
  /-- `L` is lower triangular. -/
  l_eq_zero_of_lt : ∀ i j, i < j → L i j = 0
  /-- `U` is upper triangular. -/
  u_eq_zero_of_gt : ∀ i j, j < i → U i j = 0
  /-- `L` vanishes on the zero pattern. -/
  l_eq_zero_of_mem : ∀ i j, (i, j) ∈ P → L i j = 0
  /-- `U` vanishes on the zero pattern. -/
  u_eq_zero_of_mem : ∀ i j, (i, j) ∈ P → U i j = 0

/-- **An incomplete `LU` factorization** of `A` for the zero pattern `P` (Saad, *Iterative Methods
for Sparse Linear Systems*, §10.3.2): `L` is unit lower triangular, `U` is upper triangular, both
vanish on `P`, and `L U` agrees with `A` off `P`.

The definition is a constraint rather than an algorithm: every loop order of §10.3.1 produces
factors satisfying it, and the factors it describes are not unique. See the module documentation. -/
structure IsILU (P : Set (n × n)) (A L U : Matrix n n α) : Prop extends IsILUFactors P L U where
  /-- Off the zero pattern, the product of the factors reproduces `A`. -/
  agree : ∀ i j, (i, j) ∉ P → (L * U) i j = A i j

/-- **The modified incomplete `LU` factorization** `MILU` (Saad, *Iterative Methods for Sparse
Linear Systems*, §10.3.5): the shape constraints of `Matrix.IsILU` hold, the product reproduces
`A` off the diagonal and off `P`, and on the diagonal the *row sums* agree,
`(L U) e = A e` for `e` the vector of ones.

The entries that an ordinary incomplete factorization discards are added to the diagonal instead,
so the preconditioner is exact on constant vectors; that is the whole of its justification. -/
structure IsMILU (P : Set (n × n)) (A L U : Matrix n n α) : Prop extends IsILUFactors P L U where
  /-- Off the diagonal and off the zero pattern, the product of the factors reproduces `A`. -/
  agree_of_ne : ∀ i j, i ≠ j → (i, j) ∉ P → (L * U) i j = A i j
  /-- The row sums of `L U` and of `A` agree. -/
  mulVec_one : (L * U) *ᵥ 1 = A *ᵥ 1

/-- **`ILU(0)`** (Saad, *Iterative Methods for Sparse Linear Systems*, §10.3.2, Algorithm 10.4):
the incomplete factorization whose zero pattern is the off-diagonal zero pattern of `A` itself, so
that `L` and `U` have the sparsity of the lower and upper parts of `A` and `L U` matches `A`
wherever `A` is nonzero. -/
abbrev IsILU0 (A L U : Matrix n n α) : Prop := IsILU A.zeroPattern A L U

end Defs

section Residual

variable [Fintype n] [Preorder n] [Ring α] {P : Set (n × n)} {A L U : Matrix n n α}

/-- **Saad's Proposition 10.4** (*Iterative Methods for Sparse Linear Systems*): an incomplete
factorization writes `A = L U - R` with the residual `R = L U - A` supported in the zero
pattern.

This is the form in which `R` enters the regular-splitting statement `Matrix.IsILU.isRegular` and
the error analysis of §10.5. -/
theorem IsILU.sub_eq_zero_of_notMem (h : IsILU P A L U) {i j : n} (hij : (i, j) ∉ P) :
    (L * U - A) i j = 0 := by
  rw [sub_apply, h.agree i j hij, sub_self]

omit [Preorder n] in
/-- **The row-sum identity behind `MILU`** (Saad, *Iterative Methods for Sparse Linear Systems*,
(10.21)): a residual `R = L U - A` has vanishing row sums exactly when the row sums of `L U` and
of `A` agree.

Correcting each diagonal entry of `U` by the row sum of the entries dropped in that row is what
makes the left-hand side hold, and the right-hand side is the defining property
`Matrix.IsMILU.mulVec_one` of the modified factorization. -/
theorem IsILU.dropStrategy_rowSum (A L U : Matrix n n α) :
    (L * U - A) *ᵥ (1 : n → α) = 0 ↔ (L * U) *ᵥ (1 : n → α) = A *ᵥ 1 := by
  rw [sub_mulVec, sub_eq_zero]

/-- The residual of a modified incomplete factorization has vanishing row sums, which is the sense
in which `MILU` is exact on constant vectors. -/
theorem IsMILU.residual_mulVec_one (h : IsMILU P A L U) : (L * U - A) *ᵥ (1 : n → α) = 0 :=
  (IsILU.dropStrategy_rowSum A L U).2 h.mulVec_one

end Residual

/-! ### One step of Gaussian elimination on the smaller index type -/

section SchurSingle

variable [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A sum over the indices other than `p`, read as a sum over the subtype. -/
private theorem sum_subtype_ne (p : n) (f : n → K) :
    ∑ j : {x : n // x ≠ p}, f j.1 = ∑ x ∈ Finset.univ.erase p, f x := by
  have h : ∀ x : n, x ∈ Finset.univ.erase p ↔ x ≠ p := fun x => by simp
  exact (Finset.sum_subtype _ h f).symm

/-- The row of a matrix-vector product, with the pivot term separated off. -/
private theorem sum_ne_eq_mulVec_sub (A : Matrix n n K) (X : n → K) (p t : n) :
    ∑ j : {x : n // x ≠ p}, A t j.1 * X j.1 = (A *ᵥ X) t - A t p * X p := by
  rw [sum_subtype_ne p fun j => A t j * X j, Matrix.mulVec_apply_eq_sum,
    ← Finset.add_sum_erase _ (fun j => A t j * X j) (Finset.mem_univ p)]
  ring

/-- **The defining property of the `1 × 1`-pivot Schur complement.** If `X` is a vector whose
image under `A` vanishes in the pivot row, then the Schur complement applied to the restriction of
`X` reproduces the remaining rows of `A X`.

This is the whole content of one step of Gaussian elimination: `X` is recovered from its
restriction by back-substitution in the pivot row, `A p p X p = -∑_{j ≠ p} A p j X j`. -/
theorem schurComplementSingle_mulVec_of_apply_eq_zero (A : Matrix n n K) {p : n}
    (hpp : A p p ≠ 0) {X : n → K} (hX : (A *ᵥ X) p = 0) (i : {x : n // x ≠ p}) :
    (A.schurComplementSingle p *ᵥ fun t : {x : n // x ≠ p} => X t.1) i = (A *ᵥ X) i.1 := by
  have hp := sum_ne_eq_mulVec_sub A X p p
  rw [hX, zero_sub] at hp
  have hXp : (A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * X j.1 = -X p := by
    rw [hp]; field_simp
  have expand : ∑ j : {x : n // x ≠ p}, A.schurComplementSingle p i j * X j.1
      = (∑ j : {x : n // x ≠ p}, A i.1 j.1 * X j.1)
        - ∑ j : {x : n // x ≠ p}, A i.1 p * (A p p)⁻¹ * (A p j.1 * X j.1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Matrix.schurComplementSingle_apply]; ring
  have pull : ∑ j : {x : n // x ≠ p}, A i.1 p * (A p p)⁻¹ * (A p j.1 * X j.1)
      = A i.1 p * (A p p)⁻¹ * ∑ j : {x : n // x ≠ p}, A p j.1 * X j.1 := by
    rw [Finset.mul_sum]
  have lhs : (A.schurComplementSingle p *ᵥ fun t : {x : n // x ≠ p} => X t.1) i
      = ∑ j : {x : n // x ≠ p}, A.schurComplementSingle p i j * X j.1 :=
    Matrix.mulVec_apply_eq_sum _ _ _
  rw [lhs, expand, pull, mul_assoc, hXp, sum_ne_eq_mulVec_sub A X p i.1]
  ring

/-- The `1 × 1`-pivot Schur complement of a nonsingular matrix with a nonzero pivot is inverted by
the corresponding submatrix of the inverse. -/
theorem schurComplementSingle_mul_submatrix_inv {A : Matrix n n K} {p : n} (hA : IsUnit A)
    (hpp : A p p ≠ 0) :
    A.schurComplementSingle p * A⁻¹.submatrix Subtype.val Subtype.val = 1 := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA
  ext i j
  have hcol : ∀ s : n, (A *ᵥ fun t => A⁻¹ t j.1) s = (1 : Matrix n n K) s j.1 := fun s => by
    rw [Matrix.mulVec_apply_eq_sum, ← Matrix.mul_apply, mul_nonsing_inv A hdet]
  have hzero : (A *ᵥ fun t => A⁻¹ t j.1) p = 0 := by
    rw [hcol p, Matrix.one_apply_ne (Ne.symm j.2)]
  have h := schurComplementSingle_mulVec_of_apply_eq_zero A hpp hzero i
  rw [hcol i.1] at h
  have hone : (1 : Matrix n n K) i.1 j.1
      = (1 : Matrix {x : n // x ≠ p} {x : n // x ≠ p} K) i j := by
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (Subtype.coe_injective.ne hij), Matrix.one_apply_ne hij]
  exact h.trans hone

/-- The `1 × 1`-pivot Schur complement of a nonsingular matrix with a nonzero pivot is
nonsingular. -/
theorem isUnit_schurComplementSingle {A : Matrix n n K} {p : n} (hA : IsUnit A) (hpp : A p p ≠ 0) :
    IsUnit (A.schurComplementSingle p) :=
  have h := schurComplementSingle_mul_submatrix_inv hA hpp
  ⟨⟨_, _, h, _root_.mul_eq_one_comm.1 h⟩, rfl⟩

/-- **The inverse of the `1 × 1`-pivot Schur complement** is the submatrix of `A⁻¹` on the
indices other than the pivot — the `1 × 1`-pivot form of
`Matrix.toBlocks₂₂_inv_eq_inv_schurComplement`. -/
theorem inv_schurComplementSingle {A : Matrix n n K} {p : n} (hA : IsUnit A) (hpp : A p p ≠ 0) :
    (A.schurComplementSingle p)⁻¹ = A⁻¹.submatrix Subtype.val Subtype.val :=
  Matrix.inv_eq_right_inv (schurComplementSingle_mul_submatrix_inv hA hpp)

end SchurSingle

section KyFan

variable [Fintype n] [DecidableEq n]

/-- **Ky Fan's theorem** (Saad, *Iterative Methods for Sparse Linear Systems*, Theorem 10.1): the
matrix obtained from an M-matrix by one step of Gaussian elimination is again an M-matrix.

The three checks are the book's. Off the diagonal, `a_ij - a_ip a_pj / a_pp ≤ a_ij ≤ 0`, because
the subtracted term is a product of two nonpositive entries and a positive pivot. Nonsingularity
and the nonnegativity of the inverse are one identity, `Matrix.inv_schurComplementSingle`: the
inverse of the Schur complement is the submatrix of `A⁻¹` on the indices other than the pivot,
which is the content of Saad's `A_1⁻¹ e_j = A⁻¹ e_j`. -/
theorem IsMMatrix.isMMatrix_schurComplementSingle {A : Matrix n n ℝ} (hA : A.IsMMatrix) (p : n) :
    (A.schurComplementSingle p).IsMMatrix := by
  have hpp : 0 < A p p := hA.diag_pos p
  refine ⟨fun i j hij => ?_, isUnit_schurComplementSingle hA.isUnit hpp.ne', ?_⟩
  · rw [Matrix.schurComplementSingle_apply]
    have h1 : A i.1 j.1 ≤ 0 := hA.offDiag_nonpos _ _ (Subtype.coe_injective.ne hij)
    have h3 : A p j.1 ≤ 0 := hA.offDiag_nonpos _ _ (Ne.symm j.2)
    have h5 : A i.1 p * (A p p)⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hA.offDiag_nonpos _ _ i.2) (inv_pos.2 hpp).le
    nlinarith [h5, h3]
  · rw [inv_schurComplementSingle hA.isUnit hpp.ne']
    exact entrywiseNonneg_iff.2 fun i j => hA.inv_entrywiseNonneg.apply i.1 j.1

end KyFan

/-! ### Threshold factorizations and Saad's `M̂` matrices -/

section MHat

variable [Fintype n] [LinearOrder n]

/-- **Saad's `M̂` matrix** (*Iterative Methods for Sparse Linear Systems*, (10.25)-(10.27)):
the diagonal entries are positive except possibly in the last row, where they need only be
nonnegative; the off-diagonal entries are nonpositive; and in every row but the last the entries
strictly to the right of the diagonal have a strictly negative sum.

This is strictly weaker than `Matrix.IsMMatrix`: neither nonsingularity nor a nonnegative inverse
is required. It is the class for which the threshold factorization `ILUT` of §10.4 is shown not to
break down. "The last row" is the row indexed by the greatest element, `IsMax i`. -/
structure IsMHat (H : Matrix n n ℝ) : Prop where
  /-- The diagonal entries are positive away from the last row. -/
  diag_pos : ∀ i, ¬ IsMax i → 0 < H i i
  /-- The diagonal entry of the last row is nonnegative. -/
  diag_nonneg_of_isMax : ∀ i, IsMax i → 0 ≤ H i i
  /-- The off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → H i j ≤ 0
  /-- In every row but the last, the entries to the right of the diagonal sum to a strictly
  negative number: each such row has a nonzero entry strictly to the right of the diagonal. -/
  sum_gt_neg : ∀ i, ¬ IsMax i → ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j < 0

/-- Every diagonal entry of an `M̂` matrix is nonnegative. -/
theorem IsMHat.diag_nonneg {H : Matrix n n ℝ} (hH : H.IsMHat) (i : n) : 0 ≤ H i i := by
  by_cases hi : IsMax i
  · exact hH.diag_nonneg_of_isMax i hi
  · exact (hH.diag_pos i hi).le

/-- **A diagonally dominant `M̂` matrix** (Saad, *Iterative Methods for Sparse Linear Systems*,
§10.4.1): an `M̂` matrix all of whose row sums are nonnegative. This is the hypothesis of the
`ILUT` existence theorem `Matrix.IsMHat.ilut_rows`. -/
structure IsMHat.IsDiagDominant (H : Matrix n n ℝ) : Prop extends IsMHat H where
  /-- Every row sum is nonnegative. -/
  rowSum_nonneg : ∀ i, 0 ≤ ∑ j, H i j

/-- The sum over the entries strictly to the right of `d` dominates the sum over all entries
other than `d`, when those entries are nonpositive. -/
private theorem sum_erase_le_sum_gt (x : n → ℝ) (d : n) (hoff : ∀ j, j ≠ d → x j ≤ 0) :
    ∑ j ∈ Finset.univ.erase d, x j ≤ ∑ j ∈ Finset.univ.filter (fun j => d < j), x j := by
  have hsub : Finset.univ.filter (fun j => d < j) ⊆ Finset.univ.erase d := fun j hj =>
    Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hj).2.ne', Finset.mem_univ j⟩
  have hsd := Finset.sum_sdiff (f := x) hsub
  have hnp : ∑ j ∈ Finset.univ.erase d \ Finset.univ.filter (fun j => d < j), x j ≤ 0 :=
    Finset.sum_nonpos fun j hj => hoff j (Finset.mem_erase.1 (Finset.mem_sdiff.1 hj).1).1
  linarith

omit [Fintype n] in
/-- A sum of terms that are nonpositive away from `a` is at most the term at `a`. -/
private theorem sum_le_of_mem (x : n → ℝ) (s : Finset n) {a : n} (ha : a ∈ s)
    (hnp : ∀ j ∈ s, j ≠ a → x j ≤ 0) : ∑ j ∈ s, x j ≤ x a := by
  have hsplit := Finset.add_sum_erase s x ha
  have hrest : ∑ j ∈ s.erase a, x j ≤ 0 :=
    Finset.sum_nonpos fun j hj => hnp j (Finset.mem_of_mem_erase hj) (Finset.mem_erase.1 hj).1
  linarith

/-- The diagonal entry is positive as soon as the row sum is nonnegative and the entries to the
right of the diagonal sum to a negative number. -/
private theorem pos_of_sum_nonneg_of_sum_gt_neg (x : n → ℝ) (d : n) (hoff : ∀ j, j ≠ d → x j ≤ 0)
    (hsum : 0 ≤ ∑ j, x j) (hgt : ∑ j ∈ Finset.univ.filter (fun j => d < j), x j < 0) : 0 < x d := by
  have h1 := Finset.add_sum_erase Finset.univ x (Finset.mem_univ d)
  have h2 := sum_erase_le_sum_gt x d hoff
  linarith

/-- **Saad's Theorem 10.8** (*Iterative Methods for Sparse Linear Systems*), the existence result
for the threshold factorization `ILUT`.

The data is the row recurrence (10.23) of §10.4.1 rather than an algorithm: `u k` is the working
copy of row `d` after `k` elimination steps, `w k` is the pivot row used at step `k` — a row of the
`U` factor already computed, with pivot index `p k` strictly to the left of `d` — `l k` is the
multiplier, and `r k` is the part of the row that the drop strategy discards. The hypotheses say
that the pivot rows have the sign pattern and the nonnegative row sums of an `M̂` matrix, that the
multiplier annihilates the pivot entry, that each entry is either kept whole or dropped whole, that
the diagonal entry is never dropped, and — the modification of §10.4.2 — that the entry of largest
modulus to the right of the diagonal is never dropped.

The conclusion is the book's, for every `k`: the row stays nonpositive off its diagonal; its sum
stays nonnegative and never decreases; the entries to the right of the diagonal still sum to a
strictly negative number; and the pivot `u k d` is therefore strictly positive, so the
factorization does not break down.

In the last row, where the hypothesis `¬ IsMax d` fails and (10.27) is vacuous, the first two
clauses alone give `0 ≤ u k d`, which is Saad's `u^n_n ≥ 0`. -/
theorem IsMHat.ilut_rows {H : Matrix n n ℝ} (hH : IsMHat.IsDiagDominant H) {d : n}
    (hd : ¬ IsMax d) (u w : ℕ → n → ℝ) (l : ℕ → ℝ) (r : ℕ → n → ℝ) (p : ℕ → n)
    (hu0 : u 0 = H d) (hrec : ∀ k, u (k + 1) = u k - l k • w k - r k)
    (hw : ∀ k j, j ≠ p k → w k j ≤ 0) (hwsum : ∀ k, 0 ≤ ∑ j, w k j) (hl : ∀ k, l k ≤ 0)
    (hp : ∀ k, p k < d) (hpivot : ∀ k, l k * w k (p k) = u k (p k))
    (hdrop : ∀ k j, r k j = 0 ∨ r k j = u k j - l k * w k j) (hdropDiag : ∀ k, r k d = 0)
    (hkeep : ∀ k, ∃ j₀, d < j₀ ∧ r k j₀ = 0 ∧
      ∀ j, d < j → u k j₀ - l k * w k j₀ ≤ u k j - l k * w k j) (k : ℕ) :
    (∀ j, j ≠ d → u k j ≤ 0) ∧ (0 ≤ ∑ j, u k j ∧ ∑ j, u k j ≤ ∑ j, u (k + 1) j) ∧
      ∑ j ∈ Finset.univ.filter (fun j => d < j), u k j < 0 ∧ 0 < u k d := by
  have step : ∀ k, (∀ j, j ≠ d → u k j ≤ 0) → (0 ≤ ∑ j, u k j) →
      (∑ j ∈ Finset.univ.filter (fun j => d < j), u k j < 0) →
      (∀ j, j ≠ d → u (k + 1) j ≤ 0) ∧ (∑ j, u k j ≤ ∑ j, u (k + 1) j) ∧
        ∑ j ∈ Finset.univ.filter (fun j => d < j), u (k + 1) j < 0 := by
    intro k hoff hsum hgt
    have hu : ∀ j, u (k + 1) j = u k j - l k * w k j - r k j := fun j => by
      rw [hrec k]; simp
    -- the value computed at step `k`, before dropping, is nonpositive off the diagonal
    have hv : ∀ j, j ≠ d → u k j - l k * w k j ≤ 0 := by
      intro j hj
      rcases eq_or_ne j (p k) with rfl | hjp
      · rw [hpivot k, sub_self]
      · have : 0 ≤ l k * w k j := mul_nonneg_of_nonpos_of_nonpos (hl k) (hw k j hjp)
        linarith [hoff j hj]
    have hnext : ∀ j, j ≠ d → u (k + 1) j ≤ 0 := by
      intro j hj
      rcases hdrop k j with h | h
      · rw [hu j, h, sub_zero]; exact hv j hj
      · rw [hu j, h, sub_self]
    have hrnp : ∀ j, r k j ≤ 0 := by
      intro j
      rcases eq_or_ne j d with rfl | hj
      · rw [hdropDiag k]
      · rcases hdrop k j with h | h
        · rw [h]
        · rw [h]; exact hv j hj
    have hsplit : ∑ j, u (k + 1) j = (∑ j, u k j) - l k * ∑ j, w k j - ∑ j, r k j := by
      simp only [hu]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hmono : ∑ j, u k j ≤ ∑ j, u (k + 1) j := by
      have h1 : l k * ∑ j, w k j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hl k) (hwsum k)
      have h2 : ∑ j, r k j ≤ 0 := Finset.sum_nonpos fun j _ => hrnp j
      rw [hsplit]; linarith
    refine ⟨hnext, hmono, ?_⟩
    obtain ⟨j₀, hj₀, hj₀drop, hj₀min⟩ := hkeep k
    have hvsum : ∑ j ∈ Finset.univ.filter (fun j => d < j), (u k j - l k * w k j) < 0 := by
      refine lt_of_le_of_lt (Finset.sum_le_sum fun j hj => ?_) hgt
      have hjd : d < j := (Finset.mem_filter.1 hj).2
      have hjp : j ≠ p k := ne_of_gt ((hp k).trans hjd)
      have : 0 ≤ l k * w k j := mul_nonneg_of_nonpos_of_nonpos (hl k) (hw k j hjp)
      linarith
    have hlt : ∑ j ∈ Finset.univ.filter (fun j => d < j), (u k j - l k * w k j)
        < ∑ _j ∈ Finset.univ.filter (fun j => d < j), (0 : ℝ) := by
      rw [Finset.sum_const_zero]; exact hvsum
    obtain ⟨j₁, hj₁mem, hj₁⟩ := Finset.exists_lt_of_sum_lt hlt
    have hj₀neg : u (k + 1) j₀ < 0 := by
      rw [hu j₀, hj₀drop, sub_zero]
      exact lt_of_le_of_lt (hj₀min j₁ (Finset.mem_filter.1 hj₁mem).2) hj₁
    exact lt_of_le_of_lt (sum_le_of_mem _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₀⟩)
      fun j hj _ => hnext j (Finset.mem_filter.1 hj).2.ne') hj₀neg
  induction k with
  | zero =>
    have hoff : ∀ j, j ≠ d → u 0 j ≤ 0 := fun j hj => by
      rw [hu0]; exact hH.toIsMHat.offDiag_nonpos d j (Ne.symm hj)
    have hsum : 0 ≤ ∑ j, u 0 j := by
      simp only [hu0]; exact hH.rowSum_nonneg d
    have hgt : ∑ j ∈ Finset.univ.filter (fun j => d < j), u 0 j < 0 := by
      simp only [hu0]; exact hH.toIsMHat.sum_gt_neg d hd
    obtain ⟨_, hmono, _⟩ := step 0 hoff hsum hgt
    exact ⟨hoff, ⟨hsum, hmono⟩, hgt, pos_of_sum_nonneg_of_sum_gt_neg _ d hoff hsum hgt⟩
  | succ k ih =>
    obtain ⟨hoff, ⟨hsum, _⟩, hgt, _⟩ := ih
    obtain ⟨hoff', hmono', hgt'⟩ := step k hoff hsum hgt
    have hsum' : 0 ≤ ∑ j, u (k + 1) j := hsum.trans hmono'
    obtain ⟨_, hmono'', _⟩ := step (k + 1) hoff' hsum' hgt'
    exact ⟨hoff', ⟨hsum', hmono''⟩, hgt',
      pos_of_sum_nonneg_of_sum_gt_neg _ d hoff' hsum' hgt'⟩

end MHat

/-! ### One step of Gaussian elimination on the whole index type -/

section ElimStep

variable [Fintype n] [LinearOrder n] [DecidableEq n] {M : Matrix n n ℝ} {p : n}

/-- **The multipliers of one step of Gaussian elimination** at the pivot `p`: the entries
`M i p / M p p` in column `p` and in the rows below `p`, and zero elsewhere. It is nilpotent of
square zero, because its only nonzero column is indexed by `p` and its row `p` vanishes. -/
noncomputable def elimMultipliers (M : Matrix n n ℝ) (p : n) : Matrix n n ℝ :=
  Matrix.of fun i j => if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0

/-- **The unipotent factor** of one step of Gaussian elimination at the pivot `p`. -/
noncomputable def elimMul (M : Matrix n n ℝ) (p : n) : Matrix n n ℝ :=
  1 + elimMultipliers M p

/-- **One step of Gaussian elimination** at the pivot `p`, on the whole index type: the rows
strictly below `p` have `M i p / M p p` times row `p` subtracted from them, and every other row is
left alone. Keeping the index type fixed is what lets the accumulated `L` factor of an incomplete
factorization be a product of `Matrix.elimMul`s, with no reindexing anywhere; the same step read
on the index type without `p` is `Matrix.schurComplementSingle`. -/
noncomputable def elimStep (M : Matrix n n ℝ) (p : n) : Matrix n n ℝ :=
  M - elimMultipliers M p * M

omit [Fintype n] in
/-- Entries of the multiplier matrix: `M i p / M p p` in column `p` below the pivot, zero
elsewhere. -/
@[simp]
theorem elimMultipliers_apply (M : Matrix n n ℝ) (p i j : n) :
    elimMultipliers M p i j = if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := rfl

/-- The multipliers of one row: the product `N M` has the correction of one elimination step as
its entries. -/
theorem elimMultipliers_mul_apply (M : Matrix n n ℝ) (p i j : n) :
    (elimMultipliers M p * M) i j = if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : p < i
  · rw [ite_eq_left hi, Finset.sum_eq_single p (fun c _ hc => by simp [hc]) (by simp)]
    simp [hi]
  · simp [hi]

/-- Entries of the eliminated matrix: the rows below the pivot lose `M i p / M p p` times row
`p`, and every other row is unchanged. -/
theorem elimStep_apply (M : Matrix n n ℝ) (p i j : n) :
    elimStep M p i j = M i j - if p < i then M i p * (M p p)⁻¹ * M p j else 0 := by
  rw [elimStep, Matrix.sub_apply, elimMultipliers_mul_apply]

/-- Above the pivot and in the pivot row itself, one elimination step changes nothing. -/
theorem elimStep_apply_of_not_lt (M : Matrix n n ℝ) {p i : n} (hi : ¬ p < i) (j : n) :
    elimStep M p i j = M i j := by
  rw [elimStep_apply, ite_eq_right hi, sub_zero]

/-- Below the pivot, one elimination step is the usual formula. -/
theorem elimStep_apply_of_lt (M : Matrix n n ℝ) {p i : n} (hi : p < i) (j : n) :
    elimStep M p i j = M i j - M i p * (M p p)⁻¹ * M p j := by
  rw [elimStep_apply, ite_eq_left hi]

/-- One elimination step annihilates the pivot column below the pivot. -/
theorem elimStep_apply_pivot (M : Matrix n n ℝ) {p i : n} (hi : p < i) (hp : M p p ≠ 0) :
    elimStep M p i p = 0 := by
  rw [elimStep_apply_of_lt M hi, mul_assoc, inv_mul_cancel₀ hp, mul_one, sub_self]

/-- One elimination step leaves a column that is already zero in the pivot row alone. -/
theorem elimStep_apply_of_pivot_row_eq_zero (M : Matrix n n ℝ) (p i : n) {j : n}
    (hj : M p j = 0) : elimStep M p i j = M i j := by
  rw [elimStep_apply, hj, mul_zero, ite_self, sub_zero]

/-- The multiplier matrix squares to zero. -/
theorem elimMultipliers_mul_self (M : Matrix n n ℝ) (p : n) :
    elimMultipliers M p * elimMultipliers M p = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_ne c p with rfl | hc
  · simp
  · simp [hc]

/-- The unipotent factor is inverted by `1 - N`. -/
theorem elimMul_mul_one_sub (M : Matrix n n ℝ) (p : n) :
    elimMul M p * (1 - elimMultipliers M p) = 1 := by
  rw [elimMul, add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- `1 - N` inverts the unipotent factor on the left as well. -/
theorem one_sub_mul_elimMul (M : Matrix n n ℝ) (p : n) :
    (1 - elimMultipliers M p) * elimMul M p = 1 := by
  rw [elimMul, Matrix.mul_add, Matrix.mul_one, sub_mul, Matrix.one_mul,
    elimMultipliers_mul_self, sub_zero]
  abel

/-- The unipotent factor of an elimination step is a unit. -/
theorem isUnit_elimMul (M : Matrix n n ℝ) (p : n) : IsUnit (elimMul M p) :=
  ⟨⟨_, _, elimMul_mul_one_sub M p, one_sub_mul_elimMul M p⟩, rfl⟩

/-- The inverse of the unipotent factor is `1 - N`, obtained by negating the multipliers. -/
theorem inv_elimMul (M : Matrix n n ℝ) (p : n) :
    (elimMul M p)⁻¹ = 1 - elimMultipliers M p :=
  Matrix.inv_eq_right_inv (elimMul_mul_one_sub M p)

/-- **The factorization of one elimination step**: `M = G M₁` with `G` the unipotent factor and
`M₁` the eliminated matrix. -/
theorem elimMul_mul_elimStep (M : Matrix n n ℝ) (p : n) : elimMul M p * elimStep M p = M := by
  rw [elimStep, elimMul, Matrix.mul_sub, add_mul, Matrix.one_mul, add_mul, Matrix.one_mul,
    ← Matrix.mul_assoc, elimMultipliers_mul_self, Matrix.zero_mul, add_zero]
  abel

set_option linter.unusedDecidableInType false in
/-- A sum over a linearly ordered index type, split at one point. -/
private theorem sum_split_at (p : n) (f : n → ℝ) :
    ∑ c, f c = f p + (∑ c ∈ Finset.univ.filter (fun c => c < p), f c
      + ∑ c ∈ Finset.univ.filter (fun c => p < c), f c) := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ p)]
  congr 1
  have hu : Finset.univ.erase p
      = Finset.univ.filter (fun c => c < p) ∪ Finset.univ.filter (fun c => p < c) := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
      true_and]
    exact ⟨fun hc => lt_or_gt_of_ne hc, fun hc => hc.elim ne_of_lt ne_of_gt⟩
  rw [hu, Finset.sum_union]
  exact Finset.disjoint_left.2 fun c hc hc' =>
    absurd ((Finset.mem_filter.1 hc).2.trans (Finset.mem_filter.1 hc').2) (lt_irrefl c)

/-- **Ky Fan's theorem on the whole index type** (Saad, *Iterative Methods for Sparse Linear
Systems*, Theorem 10.1): one step of Gaussian elimination applied to an M-matrix produces an
M-matrix.

Off the diagonal the argument is the book's. For the inverse, `M₁ = (1 - N) M` gives
`M₁⁻¹ = M⁻¹ (1 + N)`, which agrees with `M⁻¹` off the pivot column, and in the pivot column is
`(M p p)⁻¹ (δ_{ip} - ∑_{c < p} M⁻¹ i c M c p)`, a nonnegative number because `M⁻¹` is nonnegative
and the off-diagonal entries of `M` are nonpositive. Saad's own argument covers only the first
pivot, where the pivot column of `M₁` is `M p p e_p`; this form of it works at every pivot. -/
theorem IsMMatrix.isMMatrix_elimStep {M : Matrix n n ℝ} (hM : M.IsMMatrix) (p : n) :
    (elimStep M p).IsMMatrix := by
  have hpp : 0 < M p p := hM.diag_pos p
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv M hdet
  have hMinvM : M⁻¹ * M = 1 := nonsing_inv_mul M hdet
  have hE : elimStep M p = (1 - elimMultipliers M p) * M := by
    rw [elimStep, sub_mul, Matrix.one_mul]
  have hfac : elimStep M p * (M⁻¹ * elimMul M p) = 1 := by
    rw [hE, Matrix.mul_assoc, ← Matrix.mul_assoc M M⁻¹ (elimMul M p), hMM, Matrix.one_mul,
      one_sub_mul_elimMul]
  have hunit : IsUnit (elimStep M p) := ⟨⟨_, _, hfac, _root_.mul_eq_one_comm.1 hfac⟩, rfl⟩
  refine ⟨fun i j hij => ?_, hunit, ?_⟩
  · by_cases hi : p < i
    · rw [elimStep_apply_of_lt M hi]
      rcases eq_or_ne j p with rfl | hjp
      · rw [mul_assoc, inv_mul_cancel₀ hpp.ne', mul_one, sub_self]
      · have h1 : M i j ≤ 0 := hM.offDiag_nonpos i j hij
        have h3 : M p j ≤ 0 := hM.offDiag_nonpos p j (Ne.symm hjp)
        have h5 : M i p * (M p p)⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (hM.offDiag_nonpos i p (ne_of_gt hi))
            (inv_pos.2 hpp).le
        nlinarith [h5, h3]
    · rw [elimStep_apply_of_not_lt M hi]
      exact hM.offDiag_nonpos i j hij
  · rw [Matrix.inv_eq_right_inv hfac]
    refine entrywiseNonneg_iff.2 fun i j => ?_
    rw [elimMul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    rcases eq_or_ne j p with rfl | hjp
    · have hNsum : (M⁻¹ * elimMultipliers M j) i j
          = (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j) * (M j j)⁻¹ := by
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [elimMultipliers_apply, and_true]
        split_ifs with h
        · ring
        · rw [mul_zero]
      have hall : M⁻¹ i j * M j j
          + ((∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j)
            + ∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j)
          = (1 : Matrix n n ℝ) i j := by
        rw [← sum_split_at j fun c => M⁻¹ i c * M c j, ← Matrix.mul_apply, hMinvM]
      have hlt : (∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j) ≤ 0 :=
        Finset.sum_nonpos fun c hc =>
          mul_nonpos_of_nonneg_of_nonpos (hM.inv_entrywiseNonneg.apply i c)
            (hM.offDiag_nonpos c j (ne_of_lt (Finset.mem_filter.1 hc).2))
      have hone : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := by
        rcases eq_or_ne i j with rfl | h
        · rw [Matrix.one_apply_eq]; norm_num
        · rw [Matrix.one_apply_ne h]
      have hgoal : M⁻¹ i j
            + (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j) * (M j j)⁻¹
          = ((1 : Matrix n n ℝ) i j
            - ∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j) * (M j j)⁻¹ := by
        have hSgt : (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j)
            = (1 : Matrix n n ℝ) i j - M⁻¹ i j * M j j
              - ∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j := by
          linarith [hall]
        rw [hSgt, sub_mul, sub_mul, mul_assoc, mul_inv_cancel₀ hpp.ne', mul_one]
        ring
      rw [hNsum, hgoal]
      exact mul_nonneg (by linarith) (inv_pos.2 hpp).le
    · have h0 : (M⁻¹ * elimMultipliers M p) i j = 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero fun c _ => by simp [hjp]
      rw [h0, add_zero]
      exact hM.inv_entrywiseNonneg.apply i j

end ElimStep

/-! ### Existence for M-matrices, and the regular splitting -/

section Existence

variable [Fintype n] [LinearOrder n] [DecidableEq n]

open scoped Classical in
/-- The matrix obtained by setting to zero the entries in the zero pattern. -/
private noncomputable def dropPattern (P : Set (n × n)) (M : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if (i, j) ∈ P then 0 else M i j

omit [Fintype n] [LinearOrder n] [DecidableEq n] in
/-- Inside the zero pattern, dropping leaves a zero. -/
private theorem dropPattern_of_mem {P : Set (n × n)} {M : Matrix n n ℝ} {i j : n}
    (h : (i, j) ∈ P) : dropPattern P M i j = 0 := by
  classical
  simp [dropPattern, h]

omit [Fintype n] [LinearOrder n] [DecidableEq n] in
/-- Outside the zero pattern, dropping changes nothing. -/
private theorem dropPattern_of_notMem {P : Set (n × n)} {M : Matrix n n ℝ} {i j : n}
    (h : (i, j) ∉ P) : dropPattern P M i j = M i j := by
  classical
  simp [dropPattern, h]

omit [LinearOrder n] in
/-- A matrix with nonpositive off-diagonal entries is moved up in the entrywise order by
dropping entries off the diagonal, and keeps its nonpositive off-diagonal entries. -/
private theorem isMMatrix_dropPattern {P : Set (n × n)} (hP : ∀ i, (i, i) ∉ P)
    {M : Matrix n n ℝ} (hM : M.IsMMatrix) : (dropPattern P M).IsMMatrix := by
  refine hM.of_entrywiseLE (fun i j => ?_) fun i j hij => ?_
  · rcases Classical.em ((i, j) ∈ P) with h | h
    · rw [dropPattern_of_mem h]
      exact hM.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
    · rw [dropPattern_of_notMem h]
  · rcases Classical.em ((i, j) ∈ P) with h | h
    · rw [dropPattern_of_mem h]
    · rw [dropPattern_of_notMem h]
      exact hM.offDiag_nonpos i j hij

/-- The invariant of the induction that proves Saad's Theorem 10.2: after `k` elimination steps,
`L` is the accumulated unipotent factor, `M` the working matrix, and `L M - A` the residual
accumulated so far. `rank` is the position of an index in the increasing enumeration, so that
"`rank j < k`" is "column `j` has already been eliminated". -/
private structure ILUState (P : Set (n × n)) (A : Matrix n n ℝ) (rank : n → ℕ) (k : ℕ)
    (L M : Matrix n n ℝ) : Prop where
  /-- `L` has a unit diagonal. -/
  l_diag : ∀ i, L i i = 1
  /-- `L` is lower triangular. -/
  l_upper : ∀ i j, i < j → L i j = 0
  /-- `L` differs from the identity only in the columns already eliminated. -/
  l_late : ∀ i j, i ≠ j → k ≤ rank j → L i j = 0
  /-- `L` vanishes on the zero pattern. -/
  l_pattern : ∀ i j, (i, j) ∈ P → L i j = 0
  /-- The inverse of `L` is entrywise nonnegative. -/
  l_inv_nonneg : L⁻¹.EntrywiseNonneg
  /-- `L` is nonsingular. -/
  l_unit : IsUnit L
  /-- The working matrix is still an M-matrix. -/
  m_mmatrix : M.IsMMatrix
  /-- The working matrix vanishes on the zero pattern. -/
  m_pattern : ∀ i j, (i, j) ∈ P → M i j = 0
  /-- The columns already eliminated are upper triangular. -/
  m_lower : ∀ i j, j < i → rank j < k → M i j = 0
  /-- The residual is entrywise nonnegative. -/
  res_nonneg : (L * M - A).EntrywiseNonneg
  /-- The residual is supported in the zero pattern. -/
  res_pattern : ∀ i j, (i, j) ∉ P → (L * M - A) i j = 0

/-- **Meijerink and van der Vorst's theorem** (Saad, *Iterative Methods for Sparse Linear
Systems*, Theorem 10.2): a real M-matrix has an incomplete `LU` factorization for every zero
pattern avoiding the diagonal, no pivot vanishes, and the resulting splitting `A = L U - R` is
regular — the product `L U` is nonsingular with a nonnegative inverse, and the residual is
entrywise nonnegative.

The induction is over the pivots in increasing order. At each step the working matrix is
eliminated below the pivot (`Matrix.elimStep`), which keeps it an M-matrix by Ky Fan's theorem
(`Matrix.IsMMatrix.isMMatrix_elimStep`), and the entries in the zero pattern are then dropped,
which moves it *up* in the entrywise order and so keeps it an M-matrix by the comparison theorem
`Matrix.IsMMatrix.of_entrywiseLE`. The accumulated factor `L` differs from the identity only in
the columns already eliminated, which is what makes the dropped mass pass through it unchanged and
makes the residual a sum of nonnegative matrices.

See `Matrix.IsILU.isRegular` for the reading of the conclusion as a
`Stationary.Splitting.IsRegular`, and hence for the convergence of the iteration it defines. -/
theorem IsMMatrix.exists_isILU {A : Matrix n n ℝ} (hA : A.IsMMatrix) (P : Set (n × n))
    (hP : ∀ i, (i, i) ∉ P) :
    ∃ L U : Matrix n n ℝ, IsILU P A L U ∧ IsUnit (L * U) ∧ ((L * U)⁻¹).EntrywiseNonneg ∧
      (L * U - A).EntrywiseNonneg := by
  classical
  obtain ⟨e⟩ : Nonempty (n ≃o Fin (Fintype.card n)) := ⟨(monoEquivOfFin n rfl).symm⟩
  have hlt : ∀ i j : n, i < j ↔ (e i : ℕ) < (e j : ℕ) := fun i j =>
    Iff.symm (Fin.lt_def.symm.trans e.lt_iff_lt)
  have key : ∀ k : ℕ, ∃ L M : Matrix n n ℝ, ILUState P A (fun j => (e j : ℕ)) k L M := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, dropPattern P A, ?_⟩
      refine ⟨fun i => Matrix.one_apply_eq i, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
        fun i j hij _ => Matrix.one_apply_ne hij,
        fun i j hij => Matrix.one_apply_ne fun hc => hP i (hc ▸ hij), ?_, isUnit_one,
        isMMatrix_dropPattern hP hA, fun i j hij => dropPattern_of_mem hij,
        fun i j _ hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩
      · rw [_root_.inv_one]
        exact entrywiseNonneg_one
      · refine entrywiseNonneg_iff.2 fun i j => ?_
        rw [Matrix.sub_apply, Matrix.one_mul]
        rcases Classical.em ((i, j) ∈ P) with h | h
        · rw [dropPattern_of_mem h, zero_sub, neg_nonneg]
          exact hA.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
        · rw [dropPattern_of_notMem h, sub_self]
      · intro i j h
        rw [Matrix.sub_apply, Matrix.one_mul, dropPattern_of_notMem h, sub_self]
    | succ k ih =>
      obtain ⟨L, M, hst⟩ := ih
      by_cases hk : k < Fintype.card n
      · obtain ⟨p, hp⟩ : ∃ p : n, (e p : ℕ) = k := ⟨e.symm ⟨k, hk⟩, by simp⟩
        have hplt : ∀ j : n, j < p ↔ (e j : ℕ) < k := fun j => by rw [hlt j p, hp]
        have hpgt : ∀ j : n, p < j ↔ k < (e j : ℕ) := fun j => by rw [hlt p j, hp]
        have hpne : ∀ j : n, p < j → (e j : ℕ) ≠ k := fun j hj => ((hpgt j).1 hj).ne'
        have hMpp : 0 < M p p := hst.m_mmatrix.diag_pos p
        -- the eliminated matrix and the dropped one
        have hEM : (elimStep M p).IsMMatrix := hst.m_mmatrix.isMMatrix_elimStep p
        refine ⟨L * elimMul M p, dropPattern P (elimStep M p), ?_⟩
        -- the accumulated factor, entrywise
        have hL' : ∀ i j : n, (L * elimMul M p) i j
            = L i j + if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := by
          intro i j
          have hLN : (L * elimMultipliers M p) i j
              = if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := by
            rw [Matrix.mul_apply]
            rcases eq_or_ne j p with rfl | hjp
            · have hterm : ∀ c : n, elimMultipliers M j c j
                  = if j < c then M c j * (M j j)⁻¹ else 0 := fun c => by simp
              rw [Finset.sum_congr rfl fun c _ => by rw [hterm c],
                Finset.sum_eq_single i (fun c _ hc => ?_) (by simp)]
              · simp only [and_true]
                split_ifs with h
                · rw [hst.l_diag i, one_mul]
                · rw [mul_zero]
              · split_ifs with h
                · rw [hst.l_late i c (Ne.symm hc) (le_of_lt ((hpgt c).1 h)), zero_mul]
                · rw [mul_zero]
            · rw [ite_eq_right fun h => hjp h.2]
              refine Finset.sum_eq_zero fun c _ => ?_
              rw [elimMultipliers_apply, ite_eq_right fun h => hjp h.2, mul_zero]
          rw [elimMul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hLN]
        -- the dropped mass
        obtain ⟨D, hD⟩ : ∃ D : Matrix n n ℝ,
            dropPattern P (elimStep M p) = elimStep M p + D :=
          ⟨dropPattern P (elimStep M p) - elimStep M p, by abel⟩
        have hDapply : ∀ i j : n, D i j = if (i, j) ∈ P then -(elimStep M p i j) else 0 := by
          intro i j
          have hDsub : D i j = dropPattern P (elimStep M p) i j - elimStep M p i j := by
            rw [hD]; simp
          rw [hDsub]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [dropPattern_of_mem h, zero_sub, ite_eq_left h]
          · rw [dropPattern_of_notMem h, sub_self, ite_eq_right h]
        have hDrow : ∀ i j : n, ¬ p < i → D i j = 0 := by
          intro i j hi
          rw [hDapply]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [ite_eq_left h, elimStep_apply_of_not_lt M hi, hst.m_pattern i j h, neg_zero]
          · rw [ite_eq_right h]
        have hDnonneg : ∀ i j : n, 0 ≤ D i j := by
          intro i j
          rw [hDapply]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [ite_eq_left h, neg_nonneg]
            exact hEM.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
          · rw [ite_eq_right h]
        have hDpattern : ∀ i j : n, (i, j) ∉ P → D i j = 0 := fun i j h => by
          rw [hDapply, ite_eq_right h]
        -- the accumulated factor lets the dropped mass through unchanged
        have hLD : (L * elimMul M p) * D = D := by
          ext i j
          rw [Matrix.mul_apply, Finset.sum_eq_single i (fun c _ hc => ?_) (by simp)]
          · have hcond : ¬ (p < i ∧ i = p) := by rintro ⟨h1, rfl⟩; exact absurd h1 (lt_irrefl _)
            rw [hL' i i, ite_eq_right hcond, add_zero, hst.l_diag i, one_mul]
          · by_cases hc' : p < c
            · have hcond : ¬ (p < i ∧ c = p) := fun h => absurd h.2 (ne_of_gt hc')
              rw [hL' i c, hst.l_late i c (Ne.symm hc) (le_of_lt ((hpgt c).1 hc')),
                ite_eq_right hcond, add_zero, zero_mul]
            · rw [hDrow c j hc', mul_zero]
        -- the residual after the step
        have hres : (L * elimMul M p) * dropPattern P (elimStep M p) - A = (L * M - A) + D := by
          rw [hD, Matrix.mul_add, hLD, Matrix.mul_assoc, elimMul_mul_elimStep]
          abel
        refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij hkj => ?_, fun i j hij => ?_, ?_,
          hst.l_unit.mul (isUnit_elimMul M p), isMMatrix_dropPattern hP hEM,
          fun i j hij => dropPattern_of_mem hij, ?_, ?_, ?_⟩
        · have hcond : ¬ (p < i ∧ i = p) := by rintro ⟨h1, rfl⟩; exact absurd h1 (lt_irrefl _)
          rw [hL' i i, ite_eq_right hcond, add_zero, hst.l_diag i]
        · have hcond : ¬ (p < i ∧ j = p) := by
            rintro ⟨h1, rfl⟩; exact absurd (h1.trans hij) (lt_irrefl _)
          rw [hL' i j, hst.l_upper i j hij, ite_eq_right hcond, add_zero]
        · have hcond : ¬ (p < i ∧ j = p) := by
            rintro ⟨-, rfl⟩; omega
          rw [hL' i j, hst.l_late i j hij (by omega), ite_eq_right hcond, add_zero]
        · rcases Classical.em (p < i ∧ j = p) with h | h
          · rw [hL' i j, hst.l_pattern i j hij, ite_eq_left h, zero_add,
              hst.m_pattern i p (by rw [← h.2]; exact hij), zero_mul]
          · rw [hL' i j, hst.l_pattern i j hij, ite_eq_right h, add_zero]
        · rw [Matrix.mul_inv_rev, inv_elimMul]
          refine EntrywiseNonneg.mul (entrywiseNonneg_iff.2 fun i j => ?_) hst.l_inv_nonneg
          rw [Matrix.sub_apply, elimMultipliers_apply]
          rcases Classical.em (p < i ∧ j = p) with h | h
          · rw [ite_eq_left h, h.2, Matrix.one_apply_ne (ne_of_gt h.1), zero_sub, neg_nonneg]
            exact mul_nonpos_of_nonpos_of_nonneg
              (hst.m_mmatrix.offDiag_nonpos i p (ne_of_gt h.1)) (inv_pos.2 hMpp).le
          · rw [ite_eq_right h, sub_zero]
            rcases eq_or_ne i j with rfl | hij
            · rw [Matrix.one_apply_eq]; norm_num
            · rw [Matrix.one_apply_ne hij]
        · intro i j hji hkj
          rcases Classical.em ((i, j) ∈ P) with h | h
          · exact dropPattern_of_mem h
          rw [dropPattern_of_notMem h]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hkj with hlt' | heq
          · have hMpj : M p j = 0 := hst.m_lower p j ((hplt j).2 hlt') hlt'
            rw [elimStep_apply_of_pivot_row_eq_zero M p i hMpj]
            exact hst.m_lower i j hji hlt'
          · have hjp : j = p := e.injective (Fin.ext (by rw [heq, hp]))
            rw [hjp] at hji ⊢
            exact elimStep_apply_pivot M hji hMpp.ne'
        · refine entrywiseNonneg_iff.2 fun i j => ?_
          rw [hres, Matrix.add_apply]
          exact add_nonneg (hst.res_nonneg.apply i j) (hDnonneg i j)
        · intro i j hij
          rw [hres, Matrix.add_apply, hst.res_pattern i j hij, hDpattern i j hij, add_zero]
      · exact ⟨L, M, hst.l_diag, hst.l_upper,
          fun i j hij hkj => hst.l_late i j hij (by omega),
          hst.l_pattern, hst.l_inv_nonneg, hst.l_unit, hst.m_mmatrix, hst.m_pattern,
          fun i j hji hkj => hst.m_lower i j hji (by
            have := (e j).isLt
            omega),
          hst.res_nonneg, hst.res_pattern⟩
  obtain ⟨L, U, hst⟩ := key (Fintype.card n)
  have hupper : ∀ i j : n, j < i → U i j = 0 := fun i j hji =>
    hst.m_lower i j hji (e j).isLt
  have hLU : IsUnit (L * U) := hst.l_unit.mul hst.m_mmatrix.isUnit
  refine ⟨L, U, ⟨⟨hst.l_diag, hst.l_upper, hupper, hst.l_pattern, hst.m_pattern⟩, ?_⟩, hLU, ?_,
    hst.res_nonneg⟩
  · intro i j hij
    have := hst.res_pattern i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at this
    exact this
  · rw [Matrix.mul_inv_rev]
    exact hst.m_mmatrix.inv_entrywiseNonneg.mul hst.l_inv_nonneg

end Existence

section Regular

variable [Fintype n] [LinearOrder n] [DecidableEq n]
variable {P : Set (n × n)} {A L U : Matrix n n ℝ}

/-- **The splitting defined by an incomplete factorization is regular** (Saad, *Iterative Methods
for Sparse Linear Systems*, the sentence drawn after Theorem 10.2): with `M = L U` nonsingular and
entrywise nonnegatively invertible, and the residual nonnegative on the zero pattern, `A = M - N`
is a regular splitting — off the pattern the residual vanishes, by Saad's Proposition 10.4.

Combined with `Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_of_isMMatrix`, this is
the convergence of the `ILU`-preconditioned fixed-point iteration for an M-matrix. -/
theorem IsILU.isRegular (h : IsILU P A L U) (hu : IsUnit (L * U))
    (hinv : ((L * U)⁻¹).EntrywiseNonneg)
    (hres : ∀ i j, (i, j) ∈ P → 0 ≤ (L * U - A) i j) :
    (⟨L * U, hu⟩ : Stationary.Splitting A).IsRegular := by
  refine ⟨?_, entrywiseNonneg_iff.2 fun i j => ?_⟩
  · rwa [show Ring.inverse (L * U) = (L * U)⁻¹ from (nonsing_inv_eq_ringInverse _).symm]
  · by_cases hij : (i, j) ∈ P
    · exact hres i j hij
    · exact (h.sub_eq_zero_of_notMem hij).ge

/-- The `ILU`-preconditioned fixed-point iteration for an M-matrix converges: the spectral radius
of its iteration operator is less than one (Saad, *Iterative Methods for Sparse Linear Systems*,
the corollary drawn from Theorem 10.2). -/
theorem IsILU.complexSpectralRadius_lt_one (hA : A.IsMMatrix) (h : IsILU P A L U)
    (hu : IsUnit (L * U)) (hinv : ((L * U)⁻¹).EntrywiseNonneg)
    (hres : ∀ i j, (i, j) ∈ P → 0 ≤ (L * U - A) i j) :
    (⟨L * U, hu⟩ : Stationary.Splitting A).iterationOperator.complexSpectralRadius < 1 :=
  (h.isRegular hu hinv hres).complexSpectralRadius_lt_one_of_isMMatrix hA

end Regular

end Matrix
