/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Order`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The entrywise order and the entrywise absolute value of matrices

For matrices $A, B$ of the same size over an ordered type, $A \le B$ entrywise means
$a_{ij} \le b_{ij}$ for every entry, and $A$ is nonnegative if $0 \le A$ entrywise; these are the
nonnegative matrices of the theory of regular splittings. The entrywise absolute value $|A|$ is the
matrix of the absolute values $|a_{ij}|$. This file develops the componentwise calculus behind the
convergence theory of regular splittings and behind rounding-error analysis: a product is monotone
in either factor when the other factor is nonnegative ([saad2003iterative], §1.10, Proposition 1.26,
with the companion statements of Proposition 1.24), and nonnegativity is stable under sums,
products, powers and matrix-vector multiplication.

The file also proves the triangle inequality for a product, $|AB| \le |A|\,|B|$, which is the matrix
form of the componentwise bounds of [higham2002accuracy], §3.5. Its consequence for two factors
bounds $|(X + \Delta X)(Y + \Delta Y) - XY|$ for perturbed factors. This is the step by which the
backward errors of the factors of a factorization combine.

## Main definitions

* `Matrix.EntrywiseLE`: $A \le B$ entrywise.
* `Matrix.EntrywiseNonneg`: $A \ge 0$ entrywise.
* `Matrix.abs`: the entrywise absolute value $|A|$.

## Main results

* `Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left`,
  `Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right`: if $A \le B$ entrywise and $C \ge 0$, then
  $CA \le CB$ and $AC \le BC$ ([saad2003iterative], Proposition 1.26).
* `Matrix.EntrywiseNonneg.mul`, `Matrix.EntrywiseNonneg.pow`,
  `Matrix.EntrywiseNonneg.mulVec_nonneg`: products, powers and matrix-vector products of nonnegative
  factors are nonnegative.
* `Matrix.abs_mul_entrywiseLE`, `Matrix.abs_mulVec_le`: $|AB| \le |A|\,|B|$ and $|Ax| \le |A|\,|x|$.
* `Matrix.abs_add_mul_add_sub_mul_entrywiseLE`: the entrywise error bound for a product of perturbed
  factors.

## Notation

* `A ≤ₑ B`: `Matrix.EntrywiseLE A B`, scoped in the namespace `Matrix` beside `*ᵥ`. The entrywise
  absolute value has no notation of its own, because `|·|` is already the lattice absolute value; it
  is written `A.abs`.

## Implementation notes

* The entrywise order is a predicate, not an `LE` instance. Mathlib already orders square matrices
  over an `RCLike` field by the Loewner order, in which $A \le B$ means that $B - A$ is positive
  semidefinite, through instances scoped in `MatrixOrder`. A second `LE` on the same type would make
  every statement about either order ambiguous.
* Vectors are plain `Pi` types, and on them the entrywise order and absolute value are the canonical
  `≤` and `|·|`. So the statements that mix vectors and matrices, such as `Matrix.abs_mulVec_le` and
  `Matrix.EntrywiseNonneg.mulVec_nonneg`, use `≤` and `|·|` on the vector side and `≤ₑ` and
  `Matrix.abs` on the matrix side.
-/

namespace Matrix

variable {l m n ι : Type*} {α : Type*}

/-! ### The entrywise order -/

section LE

variable [LE α]

/-- The **entrywise order** on matrices: $A \le B$ entrywise if $a_{ij} \le b_{ij}$ for every $i$
and $j$.

This is a predicate and not an `LE` instance, because Mathlib's order on square matrices over an
`RCLike` field, scoped in `MatrixOrder`, is the Loewner order ($A \le B$ if and only if $B - A$
is positive semidefinite), and the two orders must not compete for the same notation. -/
def EntrywiseLE (A B : Matrix m n α) : Prop := ∀ i j, A i j ≤ B i j

@[inherit_doc] scoped infix:50 " ≤ₑ " => Matrix.EntrywiseLE

/-- $A \le B$ entrywise if and only if $a_{ij} \le b_{ij}$ for all $i, j$. -/
theorem entrywiseLE_iff {A B : Matrix m n α} : A ≤ₑ B ↔ ∀ i j, A i j ≤ B i j := Iff.rfl

/-- A matrix $A$ is **entrywise nonnegative** if $0 \le A$ entrywise, that is, $a_{ij} \ge 0$ for
all $i, j$. This is the relation written $A \ge 0$ in [saad2003iterative], §1.10. -/
def EntrywiseNonneg [Zero α] (A : Matrix m n α) : Prop := (0 : Matrix m n α) ≤ₑ A

/-- $A$ is entrywise nonnegative if and only if $a_{ij} \ge 0$ for all $i, j$. -/
theorem entrywiseNonneg_iff [Zero α] {A : Matrix m n α} :
    A.EntrywiseNonneg ↔ ∀ i j, 0 ≤ A i j := Iff.rfl

/-- Every entry of an entrywise nonnegative matrix is nonnegative: $a_{ij} \ge 0$. -/
theorem EntrywiseNonneg.apply [Zero α] {A : Matrix m n α} (hA : A.EntrywiseNonneg) (i : m) (j : n) :
    0 ≤ A i j := hA i j

end LE

section Preorder

variable [Preorder α] {A B C : Matrix m n α}

/-- The entrywise order is reflexive: $A \le A$ entrywise. -/
@[refl] theorem EntrywiseLE.refl (A : Matrix m n α) : A ≤ₑ A := fun _ _ => le_rfl

/-- The entrywise order is reflexive, with the matrix implicit. This is the form of
`Matrix.EntrywiseLE.refl` for `exact` and for term-mode arguments, as `le_rfl` is to `le_refl`. -/
theorem EntrywiseLE.rfl : A ≤ₑ A := EntrywiseLE.refl A

/-- The entrywise order is transitive: if $A \le B$ and $B \le C$ entrywise, then $A \le C$
entrywise. -/
@[trans] theorem EntrywiseLE.trans (hAB : A ≤ₑ B) (hBC : B ≤ₑ C) : A ≤ₑ C :=
  fun i j => (hAB i j).trans (hBC i j)

/-- If $A = B$, then $A \le B$ entrywise. -/
theorem EntrywiseLE.of_eq (h : A = B) : A ≤ₑ B := h ▸ EntrywiseLE.rfl

/-- The zero matrix is entrywise nonnegative. -/
theorem entrywiseNonneg_zero [Zero α] : (0 : Matrix m n α).EntrywiseNonneg := EntrywiseLE.rfl

end Preorder

/-- The entrywise order is antisymmetric: if $A \le B$ and $B \le A$ entrywise, then $A = B$. -/
theorem EntrywiseLE.antisymm [PartialOrder α] {A B : Matrix m n α} (hAB : A ≤ₑ B) (hBA : B ≤ₑ A) :
    A = B :=
  Matrix.ext fun i j => le_antisymm (hAB i j) (hBA i j)

/-! ### Sums -/

section AddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable {A B C D : Matrix m n α}

/-- If $A \le B$ and $C \le D$ entrywise, then $A + C \le B + D$ entrywise. -/
theorem EntrywiseLE.add (hAB : A ≤ₑ B) (hCD : C ≤ₑ D) : A + C ≤ₑ B + D :=
  fun i j => add_le_add (hAB i j) (hCD i j)

/-- The sum of two entrywise nonnegative matrices is entrywise nonnegative. -/
theorem EntrywiseNonneg.add (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) :
    (A + B).EntrywiseNonneg :=
  fun i j => add_nonneg (hA.apply i j) (hB.apply i j)

/-- A finite sum of entrywise nonnegative matrices is entrywise nonnegative. For example, the
partial sums of the Neumann series $\sum_k B^k$ of a nonnegative $B$ are nonnegative. -/
theorem EntrywiseNonneg.sum {s : Finset ι} {f : ι → Matrix m n α}
    (hf : ∀ i ∈ s, (f i).EntrywiseNonneg) : (∑ i ∈ s, f i).EntrywiseNonneg := by
  intro i j
  simpa only [Matrix.zero_apply, Matrix.sum_apply] using
    Finset.sum_nonneg fun k hk => (hf k hk).apply i j

end AddCommMonoid

/-- $A \le B$ entrywise if and only if $B - A$ is entrywise nonnegative. -/
theorem entrywiseLE_iff_entrywiseNonneg_sub [AddCommGroup α] [PartialOrder α]
    [IsOrderedAddMonoid α] {A B : Matrix m n α} : A ≤ₑ B ↔ (B - A).EntrywiseNonneg := by
  simp only [entrywiseLE_iff, entrywiseNonneg_iff, Matrix.sub_apply, sub_nonneg]

/-! ### The entrywise absolute value -/

section Abs

variable [Lattice α] [AddGroup α]

/-- The **entrywise absolute value** of a matrix: $|A|$ is the matrix with entries $|a_{ij}|$.

Inside the namespace `Matrix`, the bare name `abs` refers to this function and not to the
lattice absolute value `_root_.abs`. The notation `|·|` is not affected: it still means the
lattice absolute value of a scalar or of a vector. -/
def abs (A : Matrix m n α) : Matrix m n α := A.map (|·|)

/-- The entries of $|A|$ are $|A|_{ij} = |a_{ij}|$. -/
@[simp] theorem abs_apply (A : Matrix m n α) (i : m) (j : n) : A.abs i j = |A i j| := rfl

end Abs

section LatticeOrderedGroup

variable [Lattice α] [AddCommGroup α] [IsOrderedAddMonoid α]

/-- The entrywise absolute value $|A|$ is entrywise nonnegative. -/
theorem entrywiseNonneg_abs (A : Matrix m n α) : A.abs.EntrywiseNonneg :=
  fun i j => abs_nonneg (A i j)

/-- The triangle inequality, entrywise: $|A + B| \le |A| + |B|$ entrywise. -/
theorem abs_add_entrywiseLE (A B : Matrix m n α) : (A + B).abs ≤ₑ A.abs + B.abs :=
  fun i j => by simpa using abs_add_le (A i j) (B i j)

end LatticeOrderedGroup

/-! ### Products -/

section Semiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-- The identity matrix is entrywise nonnegative. -/
theorem entrywiseNonneg_one [DecidableEq n] : (1 : Matrix n n α).EntrywiseNonneg := by
  intro i j
  rw [Matrix.zero_apply, Matrix.one_apply]
  split
  · exact zero_le_one
  · exact le_rfl

/-- Let $C$ be an entrywise nonnegative $m \times l$ matrix and let $A, B$ be $l \times n$ matrices
over an ordered semiring with $A \le B$ entrywise. Then $CA \le CB$ entrywise. This is part of
Proposition 1.26 of [saad2003iterative]. -/
theorem EntrywiseLE.mul_of_entrywiseNonneg_left [Fintype l] {C : Matrix m l α}
    {A B : Matrix l n α} (hC : C.EntrywiseNonneg) (hAB : A ≤ₑ B) : C * A ≤ₑ C * B := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hAB k j) (hC.apply i k)

/-- Let $C$ be an entrywise nonnegative $l \times n$ matrix and let $A, B$ be $m \times l$ matrices
over an ordered semiring with $A \le B$ entrywise. Then $AC \le BC$ entrywise. This is part of
Proposition 1.26 of [saad2003iterative]. -/
theorem EntrywiseLE.mul_of_entrywiseNonneg_right [Fintype l] {C : Matrix l n α}
    {A B : Matrix m l α} (hC : C.EntrywiseNonneg) (hAB : A ≤ₑ B) : A * C ≤ₑ B * C := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hAB i k) (hC.apply k j)

/-- Let $A$ be an $m \times l$ matrix and $B$ an $l \times n$ matrix over an ordered semiring, both
entrywise nonnegative. Then $AB$ is entrywise nonnegative. -/
theorem EntrywiseNonneg.mul [Fintype l] {A : Matrix m l α} {B : Matrix l n α}
    (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) : (A * B).EntrywiseNonneg := by
  intro i j
  simpa only [Matrix.zero_apply, Matrix.mul_apply] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hA.apply i k) (hB.apply k j)

/-- Let $A$ be an entrywise nonnegative square matrix over an ordered semiring. Then $A^k$ is
entrywise nonnegative for every $k \in \mathbb{N}$. -/
theorem EntrywiseNonneg.pow [Fintype n] [DecidableEq n] {A : Matrix n n α}
    (hA : A.EntrywiseNonneg) (k : ℕ) : (A ^ k).EntrywiseNonneg :=
  fun i j => Matrix.pow_apply_nonneg hA.apply k i j

/-- If $c \ge 0$ and $A \le B$ entrywise, then $cA \le cB$ entrywise. -/
theorem EntrywiseLE.smul_of_nonneg {c : α} {A B : Matrix m n α} (hc : 0 ≤ c) (hAB : A ≤ₑ B) :
    c • A ≤ₑ c • B :=
  fun i j => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (hAB i j) hc

/-- Let $A$ be an entrywise nonnegative $m \times n$ matrix over an ordered semiring and let $x$ be
a vector with $x \ge 0$ entrywise. Then $Ax \ge 0$ entrywise. -/
theorem EntrywiseNonneg.mulVec_nonneg [Fintype n] {A : Matrix m n α} {x : n → α}
    (hA : A.EntrywiseNonneg) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := by
  refine Pi.le_def.mpr fun i => ?_
  simpa only [Pi.zero_apply, Matrix.mulVec_apply_eq_sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hA.apply i k) (Pi.le_def.mp hx k)

/-- Let $M, N$ be $m \times n$ matrices over an ordered semiring with $M \le N$ entrywise, and let
$w$ be a vector with $w \ge 0$ entrywise. Then $Mw \le Nw$ entrywise. -/
theorem EntrywiseLE.mulVec_le_of_nonneg [Fintype n] {M N : Matrix m n α} (hMN : M ≤ₑ N)
    {w : n → α} (hw : 0 ≤ w) : M *ᵥ w ≤ N *ᵥ w := by
  refine Pi.le_def.2 fun i => ?_
  simp only [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMN i j) (Pi.le_def.mp hw j)

/-- Let $A$ be an entrywise nonnegative $m \times n$ matrix over an ordered semiring, and let
$x \le y$ be vectors, entrywise. Then $Ax \le Ay$ entrywise. -/
theorem EntrywiseNonneg.mulVec_mono [Fintype n] {A : Matrix m n α} {x y : n → α}
    (hA : A.EntrywiseNonneg) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := by
  refine Pi.le_def.mpr fun i => ?_
  simp only [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (Pi.le_def.mp hxy k) (hA.apply i k)

end Semiring

section StrictSemiring

variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]

/-- Let $P$ be an $m \times n$ matrix over a strictly ordered semiring with $p_{ij} > 0$ for all
$i, j$, and let $w$ be a vector with $w \ge 0$ entrywise and $w \neq 0$. Then $(Pw)_i > 0$ for
every $i$. -/
theorem mulVec_pos_of_forall_pos [Fintype n] {P : Matrix m n α} (hP : ∀ i j, 0 < P i j)
    {w : n → α} (hw : 0 ≤ w) (hwne : w ≠ 0) (i : m) : 0 < (P *ᵥ w) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hwne
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hP i k).le (hw k))
    ⟨j, Finset.mem_univ j, mul_pos (hP i j) ((hw j).lt_of_ne' hj)⟩

end StrictSemiring

/-! ### The absolute value of a product -/

section Ring

variable [Ring α] [LinearOrder α] [IsOrderedRing α]

/-- The entrywise triangle inequality for a matrix product. Let $A$ be an $m \times l$ matrix and
$B$ an $l \times n$ matrix over a linearly ordered ring. Then $$|AB| \le |A|\,|B|$$ entrywise.
This is the matrix form of the componentwise bounds of [higham2002accuracy], §3.5. -/
theorem abs_mul_entrywiseLE [Fintype l] (A : Matrix m l α) (B : Matrix l n α) :
    (A * B).abs ≤ₑ A.abs * B.abs := by
  intro i j
  simp only [Matrix.abs_apply, Matrix.mul_apply]
  calc |∑ k, A i k * B k j|
      ≤ ∑ k, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * |B k j| := by simp [abs_mul]

/-- Let $A$ be an $m \times n$ matrix over a linearly ordered ring and let $x$ be a vector. Then
$|Ax| \le |A|\,|x|$ entrywise. This is the vector form of `Matrix.abs_mul_entrywiseLE`; on the
vector side the order and the absolute value are those of the `Pi` type. -/
theorem abs_mulVec_le [Fintype n] (A : Matrix m n α) (x : n → α) :
    |A *ᵥ x| ≤ A.abs *ᵥ |x| := by
  refine Pi.le_def.mpr fun i => ?_
  simp only [Pi.abs_apply, Matrix.mulVec_apply_eq_sum, Matrix.abs_apply]
  calc |∑ k, A i k * x k|
      ≤ ∑ k, |A i k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * |x k| := by simp [abs_mul]

end Ring

/-! ### Products of perturbed factors -/

section CommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] {p q : Type*} [Fintype p]

/-- **The error of a product of perturbed factors.** Let $X, \Delta X, P$ be $l \times p$ matrices
and $Y, \Delta Y, Q$ be $p \times q$ matrices over a linearly ordered commutative ring, and let
$a, b$ be scalars with $a \ge 0$. If, entrywise, $$|X| \le P, \qquad |\Delta X| \le aP, \qquad
|Y| \le Q, \qquad |\Delta Y| \le bQ,$$ then, entrywise, $$|(X + \Delta X)(Y + \Delta Y) - XY|
\le ((1 + a)(1 + b) - 1)\, PQ.$$

No sign condition on $b$ is needed. The proof uses $(X + \Delta X)(Y + \Delta Y) - XY = X \Delta
Y + \Delta X\, Y + \Delta X\, \Delta Y$. -/
theorem abs_add_mul_add_sub_mul_entrywiseLE {X ΔX P : Matrix l p α} {Y ΔY Q : Matrix p q α}
    {a b : α} (ha : 0 ≤ a) (hX : X.abs ≤ₑ P) (hΔX : ΔX.abs ≤ₑ a • P) (hY : Y.abs ≤ₑ Q)
    (hΔY : ΔY.abs ≤ₑ b • Q) :
    ((X + ΔX) * (Y + ΔY) - X * Y).abs ≤ₑ ((1 + a) * (1 + b) - 1) • (P * Q) := by
  have hP : P.EntrywiseNonneg := fun i j => (abs_nonneg (X i j)).trans (hX i j)
  have haP : (a • P).EntrywiseNonneg := fun i j => (abs_nonneg (ΔX i j)).trans (hΔX i j)
  have h1 : (X * ΔY).abs ≤ₑ b • (P * Q) :=
    (Matrix.abs_mul_entrywiseLE X ΔY).trans <|
      (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right (Matrix.entrywiseNonneg_abs ΔY) hX).trans
        (by rw [← Matrix.mul_smul]; exact Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left hP hΔY)
  have h2 : (ΔX * Y).abs ≤ₑ a • (P * Q) :=
    (Matrix.abs_mul_entrywiseLE ΔX Y).trans <|
      (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right (Matrix.entrywiseNonneg_abs Y) hΔX).trans
        (by
          rw [Matrix.smul_mul]
          exact Matrix.EntrywiseLE.smul_of_nonneg ha
            (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left hP hY))
  have h3 : (ΔX * ΔY).abs ≤ₑ (a * b) • (P * Q) :=
    (Matrix.abs_mul_entrywiseLE ΔX ΔY).trans <|
      (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right (Matrix.entrywiseNonneg_abs ΔY) hΔX).trans <|
        (Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left haP hΔY).trans <|
          Matrix.EntrywiseLE.of_eq (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul])
  have heq : (X + ΔX) * (Y + ΔY) - X * Y = X * ΔY + ΔX * Y + ΔX * ΔY := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  rw [heq]
  intro i j
  have e1 := Matrix.abs_add_entrywiseLE (X * ΔY + ΔX * Y) (ΔX * ΔY) i j
  have e2 := Matrix.abs_add_entrywiseLE (X * ΔY) (ΔX * Y) i j
  have a1 := h1 i j
  have a2 := h2 i j
  have a3 := h3 i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 a1 a2 a3 ⊢
  linarith

end CommRing

end Matrix
