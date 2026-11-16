/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.Order

/-!
# Triangular systems: forward and backward substitution

Let $K$ be a field, and let the indices run over a finite linearly ordered set. Forward substitution
solves a lower triangular system $Lx = b$ by
$$x_i = \frac{b_i - \sum_{j < i} l_{ij} x_j}{l_{ii}},$$
and backward substitution solves an upper triangular system $Ux = b$ by the same recurrence over the
indices $j > i$ ([quarteroni2000numerical], §3.2). This module defines both as total functions and
proves that they give the unique solution when the diagonal has no zero entry. It also solves
$Ax = b$ through an LU factorization $A = LU$ or $PA = LU$ ([quarteroni2000numerical], §3.3.1 and
§3.5), and computes the inverse of an upper triangular matrix column by column, by leading blocks,
and by an entrywise recurrence ([quarteroni2000numerical], §3.2).

Over a linearly ordered field, the module proves the two exact bounds on $|U^{-1}| \, |U|$ of
[higham2002accuracy], §8.2, where $|A|$ is the matrix of the absolute values of the entries. If
$|u_{ii}| \ge |u_{ij}|$ for $j > i$, then $(|U^{-1}| \, |U|)_{ij} \le 2^{j-i}$ (Lemma 8.6). If $U$
is row diagonally dominant, then $(|U^{-1}| \, |U|)_{ij} \le j - i + 1$ (Lemma 8.8). These bounds
drive the componentwise error analysis of substitution ([quarteroni2000numerical], §3.2.2).

## Main definitions

* `Matrix.forwardSubst`: forward substitution, [quarteroni2000numerical] (3.22).
* `Matrix.backSubst`: backward substitution, [quarteroni2000numerical] (3.23), which is forward
  substitution on the reversed order.
* `Matrix.luSolve`: the solution of $Ax = b$ through $A = LU$, by forward and then backward
  substitution.

## Main results

* `Matrix.mulVec_forwardSubst`, `Matrix.mulVec_backSubst`: substitution solves a triangular system
  whose diagonal has no zero entry.
* `Matrix.forwardSubst_eq_of_mulVec_eq`, `Matrix.backSubst_eq_of_mulVec_eq`: this solution is
  unique.
* `Matrix.mulVec_luSolve`, `Matrix.mulVec_luSolve_of_mul`, `Matrix.mulVec_luSolve_permMatrix`: the
  LU solve, without and with a row permutation $PA = LU$, where one solves $Ly = Pb$ and $Ux = y$.
* `Matrix.inv_col_eq_backSubst`: the columns of $U^{-1}$ solve $U v_i = e_i$,
  [quarteroni2000numerical] (3.26).
* `Matrix.inv_toBlock_le_of_isUpperTriangular`: the leading blocks of $U^{-1}$ are the inverses of
  the leading blocks of $U$, [quarteroni2000numerical] (3.27).
* `Matrix.inv_apply_of_isUpperTriangular`: the entrywise recurrence for $U^{-1}$,
  [quarteroni2000numerical] (3.28).
* `Matrix.abs_inv_mul_abs_apply_le_two_pow`, `Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`:
  [higham2002accuracy] Lemma 8.6, $(|U^{-1}| \, |U|)_{ij} \le 2^{j-i}$ when $|u_{ii}| \ge |u_{ij}|$
  for $j > i$, and the row sums are at most $2^{n-i+1} - 1$.
* `Matrix.abs_inv_mul_abs_apply_le_of_isDiagDominant`,
  `Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant`: [higham2002accuracy] Lemma 8.8, the
  linear bounds $(|U^{-1}| \, |U|)_{ij} \le j - i + 1$ and $\| |U^{-1}| \, |U| \|_\infty \le 2n - 1$
  for a row diagonally dominant upper triangular $U$; the constant $2n - 1$ is also the one of
  [quarteroni2000numerical], §3.1.2.

## Implementation notes

* The index type is any `[Fintype n] [LinearOrder n]`, never `Fin N`. Substitution uses only the
  order $j < i$. Counts of indices such as $\#\{k : i \le k < j\}$ replace the differences $j - i$
  of the books; on `Fin N` the two agree, by `Matrix.card_filter_le_lt_fin`.
* Both substitutions are total. A zero diagonal entry gives a value by the convention $t / 0 = 0$,
  not a hypothesis of the definition.
* Backward substitution is defined so that it is forward substitution on the reversed order `nᵒᵈ`,
  and every fact about it is the dual instance of the forward fact. The bridge is
  `Matrix.IsUpperTriangular.isLowerTriangular_orderDual`. This lemma and the criterion
  `Matrix.IsUpperTriangular.isUnit_iff` (a triangular matrix is nonsingular exactly when its
  diagonal has no zero entry, the first sentence of [quarteroni2000numerical], §3.2) are in
  `Numlib.LinearAlgebra.Matrix.Triangular`.
* The two lemmas of Higham are stated over a linearly ordered field with the entrywise absolute
  value `Matrix.abs` of `Numlib.LinearAlgebra.Matrix.Order`, because their floating-point
  applications in `Numlib.FloatingPoint.Substitution` use such fields. Row diagonal dominance there
  is `Matrix.IsAbsDiagDominant` of `Numlib.LinearAlgebra.Matrix.DiagDominant`, that is,
  $\sum_{j \neq i} |u_{ij}| \le |u_{ii}|$ for every $i$. The predicate `Matrix.IsDiagDominant` is
  stated with the norm of `RCLike` scalars instead; over $\mathbb{R}$ the two agree, by
  `Matrix.isDiagDominant_iff_isAbsDiagDominant`.
* Both proofs normalize $V = D^{-1} U$, with $D$ the diagonal of $U$, implicitly: they work with
  $|(U^{-1})_{ik}| \, |u_{kk}| = |(V^{-1})_{ik}|$. The geometric sums $\sum_{k \in s} 2^{\#\{l \in s
  : l < k\}} = 2^{\# s} - 1$ over an arbitrary finite set of a linear order
  (`Finset.sum_two_pow_card_filter_lt_add_one`) replace the sums $\sum_{k=i+1}^{j} 2^{k-i-1}$ of the
  book.
-/

open Finset

/-! ### Geometric sums over a finset of a linear order -/

namespace Finset

variable {α : Type*} [LinearOrder α] {R : Type*} [Semiring R]

/-- Let $s$ be a finite subset of a linear order, and let $R$ be a semiring. Then
$$\sum_{k \in s} 2^{\#\{l \in s : l < k\}} + 1 = 2^{\# s}$$
in $R$. If $s = \{k_0 < k_1 < \dots\}$, the summand at $k_m$ is $2^m$. -/
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

/-- Let $s$ be a finite subset of a linear order, and let $R$ be a semiring. Then
$$\sum_{k \in s} 2^{\#\{l \in s : k < l\}} + 1 = 2^{\# s}$$
in $R$. This is the mirror image of `Finset.sum_two_pow_card_filter_lt_add_one`, and its
instance on the reversed order. -/
theorem sum_two_pow_card_filter_gt_add_one (s : Finset α) :
    ∑ k ∈ s, (2 : R) ^ #(s.filter (k < ·)) + 1 = 2 ^ #s :=
  sum_two_pow_card_filter_lt_add_one (α := αᵒᵈ) s

end Finset

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]

/-! ### Interval counts on a finite linear order -/

section Counts

/-- For indices $i \le j$ of a finite linear order, the half-open intervals $(i, j]$ and $[i, j)$
have the same number of elements: $\#\{k : i < k \le j\} = \#\{k : i \le k < j\}$. Both are
$[i, j]$ with one endpoint removed. -/
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

/-- For an index $i$ of a finite linear order, $\{k : i \le k\} = \{i\} \cup \{k : i < k\}$. -/
theorem filter_ge_eq_insert_filter_gt (i : n) :
    univ.filter (i ≤ ·) = insert i (univ.filter (i < ·)) := by
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  exact ⟨fun h => h.eq_or_lt.imp Eq.symm id, fun h => h.elim (fun h => h ▸ le_rfl) le_of_lt⟩

/-- For an index $i$ of a finite linear order, $\#\{k : i \le k\} = \#\{k : i < k\} + 1$. -/
theorem card_filter_le_eq_card_filter_lt_add_one (i : n) :
    #{k | i ≤ k} = #{k | i < k} + 1 := by
  rw [filter_ge_eq_insert_filter_gt, card_insert_of_notMem (by simp)]

/-- For a function $f$ on a finite linear order with values in an additive commutative monoid, and
an index $i$,
$$\sum_{r \ge i} f(r) = f(i) + \sum_{r > i} f(r).$$
This is the mirror image of `Matrix.sum_filter_le_eq_add`. -/
theorem sum_filter_ge_eq_add {M : Type*} [AddCommMonoid M] (f : n → M) (i : n) :
    ∑ r ∈ univ.filter (i ≤ ·), f r = f i + ∑ r ∈ univ.filter (i < ·), f r := by
  rw [filter_ge_eq_insert_filter_gt, Finset.sum_insert (by simp)]

end Counts

variable {K : Type*} [Field K]

/-! ### Forward substitution -/

/-- **Forward substitution**, [quarteroni2000numerical] (3.22). Let $K$ be a field, let the indices
run over a finite linear order, and let $L \in K^{n \times n}$ and $b \in K^n$. The vector $x$
is defined by
$$x_i = \frac{b_i - \sum_{j < i} l_{ij} x_j}{l_{ii}}.$$

The definition is a total function, by well-founded recursion on the number of indices below
$i$. It uses only the entries $l_{ij}$ with $j \le i$. A zero diagonal entry gives a value by
the convention $t / 0 = 0$, not a hypothesis; `Matrix.mulVec_forwardSubst` says when the result
is the solution of $Lx = b$. -/
noncomputable def forwardSubst (L : Matrix n n K) (b : n → K) : n → K
  | i => (b i - ∑ j ∈ (univ.filter (· < i)).attach, L i j * forwardSubst L b j) / L i i
termination_by i => #{j | j < i}
decreasing_by exact card_filter_lt_lt_of_lt (mem_filter.1 j.2).2

section Forward

variable (L : Matrix n n K) (b : n → K)

/-- The recurrence of forward substitution, [quarteroni2000numerical] (3.22): the vector $x$ of
`Matrix.forwardSubst` satisfies, for every index $i$,
$$x_i = \frac{b_i - \sum_{j < i} l_{ij} x_j}{l_{ii}}.$$
This is the defining equation, with the sum over plain indices instead of the elements of a
subtype. -/
theorem forwardSubst_apply (i : n) :
    forwardSubst L b i = (b i - ∑ j ∈ univ.filter (· < i), L i j * forwardSubst L b j) / L i i := by
  rw [forwardSubst, Finset.sum_attach (univ.filter (· < i)) fun j => L i j * forwardSubst L b j]

variable {L}

/-- Let $L \in K^{n \times n}$ be lower triangular. Then for every vector $x$ and every index $i$,
$$(Lx)_i = \sum_{j < i} l_{ij} x_j + l_{ii} x_i.$$
-/
theorem mulVec_apply_of_isLowerTriangular (hL : L.IsLowerTriangular) (x : n → K) (i : n) :
    (L *ᵥ x) i = (∑ j ∈ univ.filter (· < i), L i j * x j) + L i i * x i := by
  rw [mulVec, dotProduct, ← sum_filter_le_eq_add]
  refine (Finset.sum_filter_of_ne fun j _ hj => ?_).symm
  by_contra h
  exact hj (by rw [hL (OrderDual.toDual_lt_toDual.2 (not_le.1 h)), zero_mul])

/-- **Correctness of forward substitution**. Let $K$ be a field, and let $L \in K^{n \times n}$ be
lower triangular with $l_{ii} \neq 0$ for every $i$. Then for every $b \in K^n$, the vector $x$
of `Matrix.forwardSubst` satisfies $Lx = b$. -/
theorem mulVec_forwardSubst (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) :
    L *ᵥ forwardSubst L b = b := by
  ext i
  rw [mulVec_apply_of_isLowerTriangular hL, forwardSubst_apply, mul_div_cancel₀ _ (hd i),
    add_sub_cancel]

/-- **Uniqueness for forward substitution**. Let $L \in K^{n \times n}$ be lower triangular with
$l_{ii} \neq 0$ for every $i$, and let $Lx = b$. Then $x$ is the vector that forward
substitution computes from $L$ and $b$. -/
theorem forwardSubst_eq_of_mulVec_eq (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) {x : n → K}
    (hx : L *ᵥ x = b) : forwardSubst L b = x :=
  mulVec_injective_iff_isUnit.2 (hL.isUnit_iff.2 hd)
    (by rw [mulVec_forwardSubst b hL hd, hx])

end Forward

/-! ### Backward substitution -/

/-- **Backward substitution**, [quarteroni2000numerical] (3.23). Let $K$ be a field, let the indices
run over a finite linear order, and let $U \in K^{n \times n}$ and $b \in K^n$. The vector $x$
is defined by
$$x_i = \frac{b_i - \sum_{j > i} u_{ij} x_j}{u_{ii}}.$$

The definition is a total function, by well-founded recursion on the number of indices above
$i$. A zero diagonal entry gives a value by the convention $t / 0 = 0$. It is forward
substitution on the reversed order, by `Matrix.backSubst_eq_forwardSubst_toDual`. -/
noncomputable def backSubst (U : Matrix n n K) (b : n → K) : n → K
  | i => (b i - ∑ j ∈ (univ.filter (i < ·)).attach, U i j * backSubst U b j) / U i i
termination_by i => #{j | i < j}
decreasing_by exact card_filter_lt_lt_of_lt (n := nᵒᵈ) (mem_filter.1 j.2).2

section Backward

variable (U : Matrix n n K) (b : n → K)

/-- The recurrence of backward substitution, [quarteroni2000numerical] (3.23): the vector $x$ of
`Matrix.backSubst` satisfies, for every index $i$,
$$x_i = \frac{b_i - \sum_{j > i} u_{ij} x_j}{u_{ii}}.$$
This is the defining equation, with the sum over plain indices instead of the elements of a
subtype. -/
theorem backSubst_apply (i : n) :
    backSubst U b i = (b i - ∑ j ∈ univ.filter (i < ·), U i j * backSubst U b j) / U i i := by
  rw [backSubst, Finset.sum_attach (univ.filter (i < ·)) fun j => U i j * backSubst U b j]

/-- Backward substitution with $U$ and $b$ is forward substitution with the same $U$ and $b$ on the
reversed order `nᵒᵈ`: the two recurrences agree term by term. -/
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

/-- Let $U \in K^{n \times n}$ be upper triangular. Then for every vector $x$ and every index $i$,
$$(Ux)_i = u_{ii} x_i + \sum_{j > i} u_{ij} x_j.$$
-/
theorem mulVec_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (x : n → K) (i : n) :
    (U *ᵥ x) i = U i i * x i + ∑ j ∈ univ.filter (i < ·), U i j * x j := by
  rw [mulVec, dotProduct, ← sum_filter_ge_eq_add (fun j => U i j * x j) i]
  refine (Finset.sum_filter_of_ne fun j _ hj => ?_).symm
  by_contra h
  exact hj (by rw [hU (not_le.1 h), zero_mul])

/-- **Correctness of backward substitution**. Let $K$ be a field, and let $U \in K^{n \times n}$ be
upper triangular with $u_{ii} \neq 0$ for every $i$. Then for every $b \in K^n$, the vector $x$
of `Matrix.backSubst` satisfies $Ux = b$. -/
theorem mulVec_backSubst (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) :
    U *ᵥ backSubst U b = b := by
  ext i
  rw [mulVec_apply_of_isUpperTriangular hU, backSubst_apply, mul_div_cancel₀ _ (hd i),
    sub_add_cancel]

/-- **Uniqueness for backward substitution**. Let $U \in K^{n \times n}$ be upper triangular with
$u_{ii} \neq 0$ for every $i$, and let $Ux = b$. Then $x$ is the vector that backward
substitution computes from $U$ and $b$. -/
theorem backSubst_eq_of_mulVec_eq (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {x : n → K}
    (hx : U *ᵥ x = b) : backSubst U b = x :=
  mulVec_injective_iff_isUnit.2 (hU.isUnit_iff.2 hd)
    (by rw [mulVec_backSubst b hU hd, hx])

end Backward

/-! ### Solving through an LU factorization -/

section LUSolve

variable (L U : Matrix n n K) (b : n → K)

/-- **The LU solve** ([quarteroni2000numerical], §3.3.1). For $L, U \in K^{n \times n}$ and
$b \in K^n$, solve $Ly = b$ by forward substitution and then $Ux = y$ by backward substitution.
The value is $x$. -/
noncomputable def luSolve : n → K :=
  backSubst U (forwardSubst L b)

variable {L U}

/-- **The LU solve is correct**. Let $K$ be a field, and let $A = LU$ be an LU factorization of
$A \in K^{n \times n}$: $L$ is unit lower triangular, $U$ is upper triangular, and $LU = A$. If
$u_{ii} \neq 0$ for every $i$, then for every $b \in K^n$ the vector $x$ of `Matrix.luSolve`
satisfies $Ax = b$.

The LU factorization is `Matrix.IsLU A L U`. -/
theorem mulVec_luSolve {A : Matrix n n K} (h : IsLU A L U) (hd : ∀ i, U i i ≠ 0) :
    A *ᵥ luSolve L U b = b := by
  rw [luSolve, ← h.mul_eq, ← mulVec_mulVec, mulVec_backSubst _ h.isUpperTriangular hd,
    mulVec_forwardSubst _ h.isUnitLowerTriangular.isLowerTriangular fun i => by
      rw [h.isUnitLowerTriangular.diag_eq_one]; exact one_ne_zero]

/-- **The LU solve with a row permutation** ([quarteroni2000numerical], §3.5). Let $K$ be a field,
let $P, A \in K^{n \times n}$ with $P$ nonsingular, and let $PA = LU$ be an LU factorization
with $u_{ii} \neq 0$ for every $i$. Then for every $b \in K^n$, solving $Ly = Pb$ and then
$Ux = y$ gives a vector $x$ with $Ax = b$. -/
theorem mulVec_luSolve_of_mul {P A : Matrix n n K} (hP : IsUnit P) (h : IsLU (P * A) L U)
    (hd : ∀ i, U i i ≠ 0) : A *ᵥ luSolve L U (P *ᵥ b) = b := by
  have := mulVec_luSolve (P *ᵥ b) h hd
  rw [← mulVec_mulVec] at this
  exact mulVec_injective_iff_isUnit.2 hP this

/-- A permutation matrix is nonsingular: its determinant is the sign $\pm 1$ of the permutation. -/
theorem isUnit_permMatrix (σ : Equiv.Perm n) : IsUnit (σ.permMatrix K) := by
  rw [isUnit_iff_isUnit_det, det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The LU solve with partial pivoting** ([quarteroni2000numerical], §3.5). Let $K$ be a field,
let $P$ be the permutation matrix of a permutation $\sigma$, and let $PA = LU$ be an LU
factorization with $u_{ii} \neq 0$ for every $i$. Then for every $b \in K^n$, solving $Ly = Pb$
and then $Ux = y$ gives a vector $x$ with $Ax = b$.

The matrix $P$ is `Equiv.Perm.permMatrix K σ`. -/
theorem mulVec_luSolve_permMatrix {A : Matrix n n K} {σ : Equiv.Perm n}
    (h : IsLU (σ.permMatrix K * A) L U) (hd : ∀ i, U i i ≠ 0) :
    A *ᵥ luSolve L U (σ.permMatrix K *ᵥ b) = b :=
  mulVec_luSolve_of_mul b (isUnit_permMatrix σ) h hd

end LUSolve

/-! ### The inverse of a triangular matrix -/

section Inverse

variable {U : Matrix n n K}

/-- **The columns of the inverse of a triangular matrix**, [quarteroni2000numerical] (3.26). Let
$U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$. Then for every
index $i$, the column $i$ of $U^{-1}$ is the solution $v_i$ of $U v_i = e_i$ that backward
substitution computes. -/
theorem inv_col_eq_backSubst (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (i : n) :
    (fun r => U⁻¹ r i) = backSubst U (Pi.single i 1) := by
  have hUd : IsUnit U.det := hU.isUnit_det_of_diag_ne_zero hd
  refine (backSubst_eq_of_mulVec_eq _ hU hd ?_).symm
  have : (fun r => U⁻¹ r i) = U⁻¹ *ᵥ Pi.single i 1 := (mulVec_single_one _ _).symm
  rw [this, mulVec_mulVec, mul_nonsing_inv U hUd, one_mulVec]

/-- **The leading blocks of the inverse of a triangular matrix**, [quarteroni2000numerical] (3.27).
Let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$, and let $k$
be an index. Write $U_{\le k}$ for the leading block of $U$ with the rows and the columns of
index at most $k$. Then
$$(U_{\le k})^{-1} = (U^{-1})_{\le k}.$$
So the nonzero part of each column of $U^{-1}$ is found from a system with a leading block of
$U$.

The block is `Matrix.toBlock` with the condition $\cdot \le k$ on rows and columns. The proof
reads $U U^{-1} = I$ on the block of indices at most $k$; the other term vanishes because
$U^{-1}$ is upper triangular. -/
theorem inv_toBlock_le_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (k : n) : (U.toBlock (· ≤ k) (· ≤ k))⁻¹ = U⁻¹.toBlock (· ≤ k) (· ≤ k) := by
  have hUd : IsUnit U.det := hU.isUnit_det_of_diag_ne_zero hd
  refine inv_eq_right_inv ?_
  have hz : U⁻¹.toBlock (fun i => ¬i ≤ k) (fun i => i ≤ k) = 0 :=
    hU.inv.not_toBlock_eq_zero (b := id) (p := (· ≤ k)) fun _ _ hi hji => hji.trans hi
  have := toBlock_mul_eq_add' (· ≤ k) (· ≤ k) (· ≤ k) U U⁻¹
  rw [mul_nonsing_inv U hUd, toBlock_one_self, hz, Matrix.mul_zero, add_zero] at this
  exact this.symm

/-- Let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$. Then the
diagonal of $U^{-1}$ is the inverse of the diagonal: $(U^{-1})_{kk} = 1 / u_{kk}$ for every $k$.
This is the first line of [quarteroni2000numerical] (3.28). -/
theorem inv_apply_self_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (k : n) : U⁻¹ k k = (U k k)⁻¹ := by
  have hUd : IsUnit U.det := hU.isUnit_det_of_diag_ne_zero hd
  have h := congrFun (congrFun (mul_nonsing_inv U hUd) k) k
  rw [hU.mul_apply_self hU.inv, one_apply_eq] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Let $U \in K^{n \times n}$ be upper triangular. Then $U^{-1}$ vanishes below the diagonal:
$(U^{-1})_{ik} = 0$ for $k < i$.

No condition on the diagonal is needed, because Mathlib's inverse of a singular matrix is $0$. -/
theorem inv_apply_of_isUpperTriangular_of_lt (hU : U.IsUpperTriangular) {i k : n} (hki : k < i) :
    U⁻¹ i k = 0 :=
  hU.inv hki

/-- Let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$. Then for
indices $i < k$, the entry $(i, k)$ of $U U^{-1} = I$ gives
$$u_{ii} (U^{-1})_{ik} = -\sum_{i < j \le k} u_{ij} (U^{-1})_{jk}.$$
-/
theorem diag_mul_inv_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    {i k : n} (hik : i < k) :
    U i i * U⁻¹ i k = -∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), U i j * U⁻¹ j k := by
  have hUd : IsUnit U.det := hU.isUnit_det_of_diag_ne_zero hd
  have h := congrFun (congrFun (mul_nonsing_inv U hUd) i) k
  rw [Matrix.mul_apply, one_apply_ne hik.ne,
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

/-- **The inversion recurrence for upper triangular matrices**, [quarteroni2000numerical] (3.28).
Let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$. Then for
indices $i < k$,
$$(U^{-1})_{ik} = -\frac{1}{u_{ii}} \sum_{i < j \le k} u_{ij} (U^{-1})_{jk}.$$

Together with `Matrix.inv_apply_self_of_isUpperTriangular` ($(U^{-1})_{kk} = 1 / u_{kk}$) and
`Matrix.inv_apply_of_isUpperTriangular_of_lt` (zero below the diagonal), this computes $U^{-1}$
column by column, and each column from the bottom up. -/
theorem inv_apply_of_isUpperTriangular (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {i k : n}
    (hik : i < k) :
    U⁻¹ i k = -(U i i)⁻¹ * ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), U i j * U⁻¹ j k := by
  rw [neg_mul, ← mul_neg, eq_inv_mul_iff_mul_eq₀ (hd i)]
  exact diag_mul_inv_apply_of_isUpperTriangular hU hd hik

end Inverse

end Matrix

/-! ### The bounds of Higham on $|U^{-1}| \, |U|$ -/

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {U : Matrix n n K}

section Higham

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular with
$u_{ii} \neq 0$ for every $i$. Then for indices $i < k$, the triangle inequality in the
inversion recurrence gives
$$|u_{ii}| \, |(U^{-1})_{ik}| \le \sum_{i < j \le k} |u_{ij}| \, |(U^{-1})_{jk}|.$$
-/
theorem abs_diag_mul_abs_inv_apply_le (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) {i k : n}
    (hik : i < k) :
    |U i i| * |U⁻¹ i k| ≤ ∑ j ∈ univ.filter (fun j => i < j ∧ j ≤ k), |U i j| * |U⁻¹ j k| := by
  rw [← abs_mul, diag_mul_inv_apply_of_isUpperTriangular hU hd hik, abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _)

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular. Then
$(|U^{-1}| \, |U|)_{ij} = 0$ for $j < i$, where $|A|$ is the matrix of the absolute values of
the entries of $A$. -/
theorem abs_inv_mul_abs_apply_of_lt (hU : U.IsUpperTriangular) {i j : n} (hji : j < i) :
    (U⁻¹.abs * U.abs) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hki | hik
  · rw [abs_apply, hU.inv hki, abs_zero, zero_mul]
  · rw [abs_apply U, hU (hji.trans_le hik), abs_zero, mul_zero]

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular. Then
for all indices $i$ and $j$,
$$(|U^{-1}| \, |U|)_{ij} = \sum_{i \le k \le j} |(U^{-1})_{ik}| \, |u_{kj}|.$$
For $j < i$ the sum is empty. -/
theorem abs_inv_mul_abs_apply_eq_sum (hU : U.IsUpperTriangular) (i j : n) :
    (U⁻¹.abs * U.abs) i j = ∑ k ∈ univ.filter (fun k => i ≤ k ∧ k ≤ j), |U⁻¹ i k| * |U k j| := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hki | hjk
  · exact hk (by rw [abs_apply, hU.inv hki, abs_zero, zero_mul])
  · exact hk (by rw [abs_apply U, hU hjk, abs_zero, mul_zero])

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular with
$u_{ii} \neq 0$ for every $i$. Then the normalized diagonal entry satisfies
$|(U^{-1})_{kk}| \, |u_{kk}| = 1$ for every $k$. -/
theorem abs_inv_apply_self_mul_abs_diag (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0) (k : n) :
    |U⁻¹ k k| * |U k k| = 1 := by
  rw [inv_apply_self_of_isUpperTriangular hU hd, abs_inv, inv_mul_cancel₀ (abs_ne_zero.2 (hd k))]

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular with
$u_{ii} \neq 0$ for every $i$. The normalized entries $a_{ik} = |(U^{-1})_{ik}| \, |u_{kk}|$
satisfy, for $i < k$,
$$a_{ik} \le \sum_{i < j \le k} \frac{|u_{ij}|}{|u_{ii}|} \, a_{jk}.$$

The number $a_{ik}$ is the entry $(i, k)$ of $|V^{-1}|$ for $V = D^{-1} U$, where $D$ is the
diagonal of $U$. -/
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

/-- **The inner bound of Lemma 8.6** of [higham2002accuracy]. Let $K$ be a linearly ordered field,
and let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$ and
$|u_{ij}| \le |u_{ii}|$ for all $i < j$. Then for indices $i < k$,
$$|(U^{-1})_{ik}| \, |u_{kk}| \le 2^{\#\{l : i < l < k\}}.$$
The exponent counts the indices strictly between $i$ and $k$; it is the exponent $k - i - 1$ of
the book.

The proof is by downward induction on $i$: the recurrence bounds
$a_{ik} = |(U^{-1})_{ik}| \, |u_{kk}|$ by $1 + \sum_{i < j < k} a_{jk} \le 1 + \sum_{i < j < k}
2^{\#\{l : j < l < k\}} = 2^{\#\{l : i < l < k\}}$. -/
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

/-- **Lemma 8.6** of [higham2002accuracy]. Let $K$ be a linearly ordered field, and let
$U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$ and
$|u_{ij}| \le |u_{ii}|$ for all $i < j$. Then for indices $i \le j$,
$$(|U^{-1}| \, |U|)_{ij} \le 2^{\#\{k : i \le k < j\}}.$$
The exponent is the exponent $j - i$ of the book. Below the diagonal the entry is $0$, by
`Matrix.abs_inv_mul_abs_apply_of_lt`.

The hypothesis holds for the triangular factors of Gaussian elimination with pivoting, and of a
QR factorization with column pivoting. This is the bound behind the componentwise error estimate
of substitution in [quarteroni2000numerical], §3.2.2. -/
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

/-- **The row sums in Lemma 8.6** of [higham2002accuracy]. Let $K$ be a linearly ordered field, and
let $U \in K^{n \times n}$ be upper triangular with $u_{ii} \neq 0$ for every $i$ and
$|u_{ij}| \le |u_{ii}|$ for all $i < j$. Then for every index $i$,
$$\sum_j (|U^{-1}| \, |U|)_{ij} \le 2^{\#\{k : i \le k\}} - 1.$$
In 1-based indices this is the bound $2^{n-i+1} - 1$ of the book. It gives
$\| |U^{-1}| \, |U| \|_\infty \le 2^n - 1$, which is Higham's
$\operatorname{cond}(U) \le 2^n - 1$. The power $2^{n-i+1}$ is also the one in Theorem 8.7 of
[higham2002accuracy]. -/
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

/-! ### Row diagonally dominant triangular matrices -/

section DiagDominant

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be row diagonally dominant:
$\sum_{j \neq i} |u_{ij}| \le |u_{ii}|$ for every $i$. Then every off-diagonal entry satisfies
$|u_{ij}| \le |u_{ii}|$. -/
theorem abs_apply_le_abs_diag_of_sum_le (hdom : U.IsAbsDiagDominant)
    {i j : n} (hij : j ≠ i) : |U i j| ≤ |U i i| :=
  (Finset.single_le_sum (f := fun j => |U i j|) (fun _ _ => abs_nonneg _)
    (mem_erase.2 ⟨hij, mem_univ j⟩)).trans (hdom i)

/-- **The inner bound of Lemma 8.8** of [higham2002accuracy]. Let $K$ be a linearly ordered field,
and let $U \in K^{n \times n}$ be upper triangular and row diagonally dominant, with
$u_{ii} \neq 0$ for every $i$. Then for all indices $i$ and $k$,
$$|(U^{-1})_{ik}| \, |u_{kk}| \le 1.$$

The left side is the entry $(i, k)$ of $|V^{-1}|$ for $V = D^{-1} U$, where $D$ is the diagonal
of $U$. The proof is by downward induction on $i$: $a_{ik} \le \sum_{i < j \le k} (|u_{ij}| /
|u_{ii}|) \, a_{jk} \le \sum_{j \neq i} |u_{ij}| / |u_{ii}| \le 1$.
-/
theorem abs_inv_apply_mul_abs_diag_le_one (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    (hdom : U.IsAbsDiagDominant) (i k : n) :
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

/-- **Lemma 8.8** of [higham2002accuracy], entrywise. Let $K$ be a linearly ordered field, and let
$U \in K^{n \times n}$ be upper triangular and row diagonally dominant, with $u_{ii} \neq 0$ for
every $i$. Then for indices $i \le j$,
$$(|U^{-1}| \, |U|)_{ij} \le \#\{k : i \le k \le j\}.$$
Below the diagonal the entry is $0$, by `Matrix.abs_inv_mul_abs_apply_of_lt`.

The right side is the number of indices from $i$ to $j$ inclusive, that is, $j - i + 1$;
[higham2002accuracy] states the weaker bound $i + j - 1$. This is the bound behind the clause on
diagonally dominant matrices in [quarteroni2000numerical], §3.2.2. -/
theorem abs_inv_mul_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : U.IsAbsDiagDominant) {i j : n}
    (hij : i ≤ j) : (U⁻¹.abs * U.abs) i j ≤ #{k | i ≤ k ∧ k ≤ j} := by
  rw [abs_inv_mul_abs_apply_eq_sum hU, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := (mem_filter.1 hk).2
  refine le_trans ?_ (abs_inv_apply_mul_abs_diag_le_one hU hd hdom i k)
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases hk'.2.eq_or_lt with rfl | hkj
  · exact le_rfl
  · exact abs_apply_le_abs_diag_of_sum_le hdom hkj.ne'

/-- Let $K$ be a linearly ordered field, and let $U \in K^{n \times n}$ be upper triangular and row
diagonally dominant. Then for every row $k$, $\sum_j |u_{kj}| \le 2 |u_{kk}|$, and
$\sum_j |u_{kj}| \le |u_{kk}|$ if no index is greater than $k$ (the last row, which has no entry
to the right of the diagonal). -/
theorem sum_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hdom : U.IsAbsDiagDominant) (k : n) :
    ∑ j, |U k j| ≤ |U k k| * if ∃ j, k < j then 2 else 1 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ k)]
  split_ifs with h
  · linarith [hdom k]
  · push Not at h
    rw [Finset.sum_eq_zero fun j hj => ?_, add_zero, mul_one]
    exact abs_eq_zero.2 (hU (lt_of_le_of_ne (h j) (mem_erase.1 hj).1))

/-- **The row sums in Lemma 8.8** of [higham2002accuracy]. Let $K$ be a linearly ordered field, and
let $U \in K^{n \times n}$ be upper triangular and row diagonally dominant, with $u_{ii} \neq 0$
for every $i$. Then for every index $i$,
$$\sum_j (|U^{-1}| \, |U|)_{ij} \le 2 \, \#\{k : i < k\} + 1.$$
In 1-based indices this is the bound $2(n - i) + 1$ of the book. It gives
$\| |U^{-1}| \, |U| \|_\infty \le 2n - 1$, by
`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`. This is Higham's
$\operatorname{cond}(U) \le 2n - 1$, and the constant of [quarteroni2000numerical], §3.1.2.

The proof is Higham's: $|V^{-1}| \, |V| e \le |V^{-1}| (2, \dots, 2, 1)^T$, and the entries of
$|V^{-1}|$ are at most $1$. -/
theorem sum_abs_inv_mul_abs_apply_le_of_isDiagDominant (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : U.IsAbsDiagDominant) (i : n) :
    ∑ j, (U⁻¹.abs * U.abs) i j ≤ 2 * #{k | i < k} + 1 := by
  -- the sum as `∑_k |(U⁻¹)_ik| ∑_j |u_kj|`, restricted to `k ≥ i`
  have h1 : ∑ j, (U⁻¹.abs * U.abs) i j =
      ∑ k ∈ univ.filter (i ≤ ·), |U⁻¹ i k| * ∑ j, |U k j| := by
    simp only [Matrix.mul_apply, abs_apply, Finset.mul_sum]
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

/-- **The bound $2n - 1$ in Lemma 8.8** of [higham2002accuracy]. Let $K$ be a linearly ordered
field, and let $U \in K^{n \times n}$ be upper triangular and row diagonally dominant, with
$u_{ii} \neq 0$ for every $i$. Then every row sum of $|U^{-1}| \, |U|$ is at most $2n - 1$,
where $n$ is the number of indices, so $\| |U^{-1}| \, |U| \|_\infty \le 2n - 1$. -/
theorem sum_abs_inv_mul_abs_apply_le_of_isDiagDominant' (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : U.IsAbsDiagDominant) (i : n) :
    ∑ j, (U⁻¹.abs * U.abs) i j ≤ 2 * Fintype.card n - 1 := by
  refine (sum_abs_inv_mul_abs_apply_le_of_isDiagDominant hU hd hdom i).trans ?_
  have h : #{k | i < k} + 1 ≤ Fintype.card n := by
    rw [← card_filter_le_eq_card_filter_lt_add_one, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h' : ((#{k | i < k} : ℕ) : K) + 1 ≤ Fintype.card n := by exact_mod_cast h
  linarith

end DiagDominant

end Matrix
