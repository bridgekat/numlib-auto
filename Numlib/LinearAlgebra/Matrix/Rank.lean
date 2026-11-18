/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Rank`, where `Matrix.rank` and its behaviour under
multiplication by an invertible matrix and under reindexing already live.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Data.Matrix.Mul
import Numlib.Data.Subtype
import Numlib.LinearAlgebra.Matrix.BlockDiagonal

/-!
# Rank and nullity of a matrix

Let $A$ be a matrix over a field $K$. The **nullity** of a square matrix $A$ is the dimension of its
null space $\operatorname{Null}(A) = \{x : Ax = 0\}$, which is `LinearMap.ker A.mulVecLin`. This
file proves the rank–nullity relation $\operatorname{rank} A + \dim \operatorname{Null}(A) = n$ for
$A \in K^{n \times n}$, and the invariance of the nullity under the operations that keep the rank:
reindexing and similarity. It also proves the classical characterization of the rank as the largest
order of a nonvanishing minor, which [quarteroni2000numerical] takes as Definition 1.12.

The second half gives tools for rectangular matrices: subadditivity of the rank, the rank
factorization $A = BC$ through $K^r$, a rank bound for a matrix supported on a few rows and columns,
and the ranks of blocks. It ends with the **nullity theorem** of Fiedler and Markham (1986), in the
form of Strang and Nguyen (2004): for an invertible $A$ and index sets $p$, $q$, the blocks
$A^{-1}[p, q]$ and $A[q^c, p^c]$ have null spaces of the same dimension. For a $2 \times 2$ block
matrix this gives $\operatorname{rank} (A^{-1})_{21} = \operatorname{rank} A_{21}$, as in
[golub2013matrix], §4.3.8.

## Main definitions

* `Matrix.kerMulVecLinBlockDiagonal'Equiv`: the null space of a block diagonal matrix is linearly
  equivalent to the product of the null spaces of its blocks.

## Main results

* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity, $\operatorname{rank} A + \dim
  \operatorname{Null}(A) = n$ for $A \in K^{n \times n}$.
* `Matrix.finrank_ker_mulVecLin_reindex`, `Matrix.finrank_ker_mulVecLin_conj`: the nullity does not
  change under reindexing or under similarity $A \mapsto P A P^{-1}$.
* `Matrix.ker_mulVecLin_pow_le_succ`: $\operatorname{Null}(A^k) \subseteq
  \operatorname{Null}(A^{k+1})$.
* `Matrix.finrank_ker_mulVecLin_blockDiagonal'`: the nullity of a block diagonal matrix is the sum
  of the nullities of its blocks.
* `Matrix.rank_eq_sup_card_det_submatrix_ne_zero`: the rank is the largest $k$ such that some
  $k \times k$ submatrix has a nonzero determinant.
* `Matrix.rank_add_le`: $\operatorname{rank}(A + B) \le \operatorname{rank} A + \operatorname{rank}
  B$.
* `Matrix.rank_le_iff_exists_mul`: $\operatorname{rank} A \le r$ if and only if $A = BC$ with
  $B \in K^{m \times r}$ and $C \in K^{r \times n}$.
* `Matrix.rank_le_card_add_card_of_forall_ne_zero`: a matrix whose nonzero entries lie in $s$ rows
  or $t$ columns has rank at most $s + t$.
* `Matrix.finrank_ker_toBlock_inv`, `Matrix.rank_toBlock_inv_add_card`: the nullity theorem, in
  kernel form and in rank form.
* `Matrix.rank_inv_toBlocks₂₁`, `Matrix.rank_inv_toBlocks₁₂`: an off-diagonal block of a nonsingular
  block matrix and the same block of its inverse have the same rank.

## Implementation notes

* Mathlib has `Matrix.rank`, the dimension of the range. It does not have the rank–nullity relation
  for matrices, the invariance of the nullity under reindexing and similarity, or the
  characterization of the rank by minors; this file supplies them.
* Rows and columns are indexed by finite types. An index set is a predicate on the index type, and
  the block $A[p, q]$ is `A.toBlock p q`, indexed by the subtypes of $p$ and $q$. The complement
  $p^c$ is the predicate `fun i => ¬ p i`.
* The nullity theorem uses `Matrix.submatrix_mulVec_eq_comp_mulVec_extend` in
  `Numlib.Data.Matrix.Mul`: a submatrix applied to a vector is the matrix applied to the extension
  of the vector by zero, restricted to the selected rows.
-/

open Module

namespace Matrix

variable {ι : Type*} {m : ι → Type*} {K : Type*} [Field K]

section Square

variable {n n' : Type*} [Fintype n] [Fintype n']

/-- **Rank–nullity for a square matrix.** Let $A \in K^{n \times n}$. Then
$$\operatorname{rank} A + \dim \operatorname{Null}(A) = n.$$
-/
theorem rank_add_finrank_ker_mulVecLin (A : Matrix n n K) :
    A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi]

/-- Let $A \in K^{n \times n}$ and let $\sigma : n \simeq n'$ be a bijection of index types. The
matrix $A$ reindexed by $\sigma$ in its rows and columns has a null space of the same dimension
as $\operatorname{Null}(A)$. -/
theorem finrank_ker_mulVecLin_reindex (σ : n ≃ n') (A : Matrix n n K) :
    finrank K (LinearMap.ker (reindex σ σ A).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (reindex σ σ A)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_reindex] at h₁
  rw [Fintype.card_congr σ] at h₂
  omega

variable [DecidableEq n]

/-- Let $A, P \in K^{n \times n}$ with $P$ invertible. Then $\operatorname{rank}(P A P^{-1}) =
\operatorname{rank} A$. -/
theorem rank_conj {A P : Matrix n n K} (hP : IsUnit P) : (P * A * P⁻¹).rank = A.rank := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det P hd),
    rank_mul_eq_right_of_isUnit_det _ _ hd]

/-- Let $A, P \in K^{n \times n}$ with $P$ invertible. Then $\dim \operatorname{Null}(P A P^{-1}) =
\dim \operatorname{Null}(A)$. -/
theorem finrank_ker_mulVecLin_conj {A P : Matrix n n K} (hP : IsUnit P) :
    finrank K (LinearMap.ker (P * A * P⁻¹).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (P * A * P⁻¹)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_conj hP] at h₁
  omega

/-- Let $A \in K^{n \times n}$ have rank $n$. Then $A$ is invertible.

By rank–nullity the null space of $A$ is zero, so $x \mapsto Ax$ is injective. -/
theorem isUnit_of_rank_eq_card {A : Matrix n n K} (h : A.rank = Fintype.card n) : IsUnit A := by
  have hk := rank_add_finrank_ker_mulVecLin A
  rw [h] at hk
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- Let $A \in K^{n \times n}$ and $k \in \mathbb{N}$. The null spaces of the powers of $A$
increase: $\operatorname{Null}(A^k) \subseteq \operatorname{Null}(A^{k+1})$. -/
theorem ker_mulVecLin_pow_le_succ (A : Matrix n n K) (k : ℕ) :
    LinearMap.ker ((A ^ k).mulVecLin) ≤ LinearMap.ker ((A ^ (k + 1)).mulVecLin) := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  rw [pow_succ', ← mulVec_mulVec, hv, mulVec_zero]

end Square

/-- The rank of a block diagonal matrix is the sum of the ranks of its diagonal blocks. -/
theorem rank_fromBlocks_diagonal {u v w z : Type*}
    [Finite u] [Fintype v] [Finite w] [Fintype z]
    (D : Matrix u v K) (L : Matrix w z K) :
    (fromBlocks D 0 0 L).rank = D.rank + L.rank := by
  let := Fintype.ofFinite u
  let := Fintype.ofFinite w
  let e := LinearEquiv.sumPiEquivProdPi K u w (fun _ => K)
  let f := LinearEquiv.sumPiEquivProdPi K v z (fun _ => K)
  have hMap : e.toLinearMap.comp (fromBlocks D 0 0 L).mulVecLin =
      (D.mulVecLin.prodMap L.mulVecLin).comp f.toLinearMap := by
    ext x : 1
    simp only [LinearMap.comp_apply, mulVecLin_apply, LinearMap.prodMap_apply, fromBlocks_mulVec,
      zero_mulVec, add_zero, zero_add]
    rfl
  have hRange := congrArg LinearMap.range hMap
  rw [LinearMap.range_comp, f.range_comp, LinearMap.range_prodMap] at hRange
  rw [Matrix.rank, ← e.finrank_map_eq, hRange,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, ← Matrix.rank, ← Matrix.rank]

section BlockDiagonal

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)]

/-- Let $M_i \in K^{m_i \times m_i}$ for $i$ in a finite index type. The null space of the block
diagonal matrix $\operatorname{diag}(M_i)_i$ is linearly equivalent to the product
$\prod_i \operatorname{Null}(M_i)$: a vector is in the null space of the block diagonal matrix
exactly when each of its blocks is in the null space of the corresponding $M_i$.

The block diagonal matrix is `Matrix.blockDiagonal' M`, indexed by the sigma type
`(i : ι) × m i`. The equivalence sends a vector $v$ to the family of its blocks $(v_i)_i$. -/
noncomputable def kerMulVecLinBlockDiagonal'Equiv (M : ∀ i, Matrix (m i) (m i) K) :
    LinearMap.ker (blockDiagonal' M).mulVecLin ≃ₗ[K] ∀ i, LinearMap.ker (M i).mulVecLin where
  toFun v i := ⟨fun a => v.1 ⟨i, a⟩, by
    refine LinearMap.mem_ker.2 (funext fun a => ?_)
    have h := congrFun (LinearMap.mem_ker.1 v.2) (⟨i, a⟩ : (i : ι) × m i)
    rwa [mulVecLin_apply, blockDiagonal'_mulVec] at h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun x => (w x.1).1 x.2, by
    refine LinearMap.mem_ker.2 (funext fun x => ?_)
    obtain ⟨i, a⟩ := x
    rw [mulVecLin_apply, blockDiagonal'_mulVec]
    exact congrFun (LinearMap.mem_ker.1 (w i).2) a⟩
  left_inv v := by ext x; obtain ⟨i, a⟩ := x; rfl
  right_inv w := by ext i a; rfl

/-- **The nullity of a block diagonal matrix.** Let $M_i \in K^{m_i \times m_i}$ for $i$ in a finite
index type. Then
$$\dim \operatorname{Null}(\operatorname{diag}(M_i)_i) = \sum_i \dim \operatorname{Null}(M_i).$$

The block diagonal matrix is `Matrix.blockDiagonal' M`. The proof uses
`Matrix.kerMulVecLinBlockDiagonal'Equiv`. -/
theorem finrank_ker_mulVecLin_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) K) :
    finrank K (LinearMap.ker (blockDiagonal' M).mulVecLin)
      = ∑ i, finrank K (LinearMap.ker (M i).mulVecLin) := by
  rw [(kerMulVecLinBlockDiagonal'Equiv M).finrank_eq, Module.finrank_pi_fintype]

end BlockDiagonal

section Minor

variable {m n : Type*} [Fintype n] (A : Matrix m n K)

/-- Let $A \in K^{m \times n}$, and let $r : \{0, \dots, k-1\} \to m$ and
$c : \{0, \dots, k-1\} \to n$ select $k$ rows and $k$ columns. If the minor $\det A[r, c]$ is
nonzero, then $k \le \operatorname{rank} A$.

The $k \times k$ submatrix is invertible, so its rank is $k$, and the rank of a submatrix is at
most the rank of the matrix. The maps $r$ and $c$ need not be injective. -/
theorem card_le_rank_of_det_submatrix_ne_zero {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  have hu : IsUnit (A.submatrix r c) := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have := rank_submatrix_le A r c
  rwa [rank_of_isUnit _ hu, Fintype.card_fin] at this

omit [Fintype n] in
/-- Let $A \in K^{m \times n}$, and let $r$ and $c$ select $k$ rows and $k$ columns. If
$\det A[r, c] \neq 0$, then $r$ is injective, because two equal rows give a zero determinant. -/
theorem injective_of_det_submatrix_ne_zero_left {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective r := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_row_eq hne (funext fun j => by simp [hab]))

omit [Fintype n] in
/-- Let $A \in K^{m \times n}$, and let $r$ and $c$ select $k$ rows and $k$ columns. If
$\det A[r, c] \neq 0$, then $c$ is injective. -/
theorem injective_of_det_submatrix_ne_zero_right {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective c := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_column_eq hne fun i => by simp [hab])

/-- Let $A \in K^{m \times n}$ have rank $k$. Then $A$ has $k$ linearly independent columns: there
is $c : \{0, \dots, k-1\} \to n$ such that the columns $A(:, c(0)), \dots, A(:, c(k-1))$ are
linearly independent. -/
theorem exists_linearIndependent_col {k : ℕ} (h : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (A.col ∘ c) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have htf : t.Finite := (Set.finite_range A.col).subset ht
  have : Fintype t := htf.fintype
  have hcard : Fintype.card t = k := by
    rw [← h, rank_eq_finrank_span_cols, ← hsp, finrank_span_set_eq_card hli, Set.toFinset_card]
  let e : Fin k ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  choose c hc using fun x : t => ht x.2
  refine ⟨c ∘ e, ?_⟩
  have : A.col ∘ (c ∘ e) = ((↑) : t → m → K) ∘ e := funext fun i => hc (e i)
  rw [this]
  exact hli.comp e e.injective

/-- Let $A \in K^{m \times n}$ with $m$ finite, and let $k = \operatorname{rank} A$. Then $A$ has a
$k \times k$ submatrix with nonzero determinant: there are $r : \{0, \dots, k-1\} \to m$ and
$c : \{0, \dots, k-1\} \to n$ with $\det A[r, c] \neq 0$.

The proof chooses $k$ linearly independent columns, and then $k$ linearly independent rows of
the resulting $m \times k$ matrix, which also has rank $k$. A square matrix with linearly
independent rows is invertible. -/
theorem exists_det_submatrix_ne_zero [Finite m] :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  have := Fintype.ofFinite m
  obtain ⟨c, hc⟩ := exists_linearIndependent_col A rfl
  have hB : (A.submatrix id c)ᵀ.rank = A.rank := by
    rw [rank_transpose, rank_eq_finrank_span_cols]
    have : (A.submatrix id c).col = A.col ∘ c := rfl
    rw [this, finrank_span_eq_card hc, Fintype.card_fin]
  obtain ⟨r, hr⟩ := exists_linearIndependent_col _ hB
  refine ⟨r, c, ?_⟩
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← linearIndependent_row_iff_isUnit]
  exact hr

/-- **The rank as the largest nonvanishing minor.** Let $A \in K^{m \times n}$ with $m$ finite. Then
$$\operatorname{rank} A = \sup \{k : \det A[r, c] \neq 0 \text{ for some injective } r : \{0,
  \dots, k-1\} \to m,\ c : \{0, \dots, k-1\} \to n\}.$$
This is Definition 1.12 of [quarteroni2000numerical], stated here as a theorem.

The rows and columns are selected by embeddings `Fin k ↪ m` and `Fin k ↪ n`. The set contains
$0$, because the empty minor is $1$. The rank bounds the set by
`Matrix.card_le_rank_of_det_submatrix_ne_zero`, and the set contains the rank by
`Matrix.exists_det_submatrix_ne_zero`. -/
theorem rank_eq_sup_card_det_submatrix_ne_zero [Finite m] :
    A.rank = sSup {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0} := by
  have hub : ∀ k ∈ {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0},
      k ≤ A.rank := fun k ⟨_, _, h⟩ => card_le_rank_of_det_submatrix_ne_zero A h
  have hmem : A.rank ∈ {k | ∃ (r : Fin k ↪ m) (c : Fin k ↪ n), (A.submatrix r c).det ≠ 0} := by
    obtain ⟨r, c, h⟩ := exists_det_submatrix_ne_zero A
    exact ⟨⟨r, injective_of_det_submatrix_ne_zero_left A h⟩,
      ⟨c, injective_of_det_submatrix_ne_zero_right A h⟩, h⟩
  exact le_antisymm (le_csSup ⟨A.rank, hub⟩ hmem) (csSup_le ⟨_, hmem⟩ hub)

end Minor

/-! ### Subadditivity and rank factorizations -/

section Factorization

variable {m n : Type*} [Fintype n]

/-- **The rank is subadditive.** Let $A, B \in K^{m \times n}$. Then
$$\operatorname{rank}(A + B) \le \operatorname{rank} A + \operatorname{rank} B.$$

The column space of $A + B$ lies in the sum of the column spaces of $A$ and $B$. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, rank, rank, mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **The rank factorization.** Let $A \in K^{m \times n}$ and $r \in \mathbb{N}$. Then
$\operatorname{rank} A \le r$ if and only if $A = BC$ for some $B \in K^{m \times r}$ and
$C \in K^{r \times n}$.

For the forward direction, the coordinates of the columns of $A$ in a basis of the column space,
padded by zeros to length $r$, give $C$. -/
theorem rank_le_iff_exists_mul (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (B : Matrix m (Fin r) K) (C : Matrix (Fin r) n K), A = B * C := by
  classical
  constructor
  · intro h
    set V := LinearMap.range A.mulVecLin
    have hk : finrank K V ≤ r := h
    let e : V ≃ₗ[K] (Fin (finrank K V) → K) := (Module.finBasis K V).equivFun
    let ι : Fin (finrank K V) → Fin r := Fin.castLE hk
    let f : (n → K) →ₗ[K] V := A.mulVecLin.rangeRestrict
    refine ⟨LinearMap.toMatrix' (V.subtype ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.funLeft K K ι),
      LinearMap.toMatrix' (Function.ExtendByZero.linearMap K K ι ∘ₗ e.toLinearMap ∘ₗ f), ?_⟩
    rw [← LinearMap.toMatrix'_comp]
    have hι : LinearMap.funLeft K K ι ∘ₗ Function.ExtendByZero.linearMap K K ι = LinearMap.id := by
      ext x i
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply,
        Function.ExtendByZero.linearMap_apply, LinearMap.id_coe, id_eq]
      exact (Fin.castLE_injective hk).extend_apply _ _ i
    have hcomp : V.subtype ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.funLeft K K ι ∘ₗ
        (Function.ExtendByZero.linearMap K K ι ∘ₗ e.toLinearMap ∘ₗ f) = A.mulVecLin := by
      refine LinearMap.ext fun x => ?_
      have hx := LinearMap.congr_fun hι (e (f x))
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hx
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hx,
        LinearEquiv.symm_apply_apply, Submodule.coe_subtype, f, LinearMap.codRestrict_apply]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hcomp]
    exact (LinearMap.toMatrix'_toLin' A).symm
  · rintro ⟨B, C, rfl⟩
    exact (rank_mul_le_left B C).trans ((rank_le_card_width B).trans_eq (Fintype.card_fin r))

/-- Let $A \in K^{m \times n}$ and $r \in \mathbb{N}$. Then $\operatorname{rank} A \le r$ if and
only if $A = R S^T$ for some $R \in K^{m \times r}$ and $S \in K^{n \times r}$. This is the
generator form of a matrix of displacement rank at most $r$ in [golub2013matrix], (12.1.3). -/
theorem rank_le_iff_exists_mul_transpose (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (R : Matrix m (Fin r) K) (S : Matrix n (Fin r) K), A = R * Sᵀ := by
  rw [rank_le_iff_exists_mul]
  exact ⟨fun ⟨B, C, h⟩ => ⟨B, Cᵀ, by rwa [transpose_transpose]⟩,
    fun ⟨R, S, h⟩ => ⟨R, Sᵀ, h⟩⟩

/-- **A matrix supported on a few rows and columns has small rank.** Let $A \in K^{m \times n}$ with
$m$ finite, let $s$ be a finite set of rows and $t$ a finite set of columns, and suppose that
every nonzero entry $a_{ij}$ has $i \in s$ or $j \in t$. Then
$$\operatorname{rank} A \le |s| + |t|.$$

The proof splits $A$ into its rows in $s$ and the remaining rows, which are supported on the
columns in $t$. The displacement rank bounds (12.1.8)–(12.1.11) of [golub2013matrix] are
instances of this bound. -/
theorem rank_le_card_add_card_of_forall_ne_zero [Finite m] (A : Matrix m n K)
    (s : Finset m) (t : Finset n) (h : ∀ i j, A i j ≠ 0 → i ∈ s ∨ j ∈ t) :
    A.rank ≤ s.card + t.card := by
  classical
  have := Fintype.ofFinite m
  set A₁ : Matrix m n K := Matrix.of fun i j => if i ∈ s then A i j else 0
  set A₂ : Matrix m n K := Matrix.of fun i j => if i ∈ s then 0 else A i j
  have hA : A = A₁ + A₂ := by
    ext i j
    by_cases hi : i ∈ s <;> simp [A₁, A₂, hi]
  have h₁ : A₁.rank ≤ s.card := rank_le_card_of_support_subset A₁ s fun i hi => by
    by_contra his
    have his' : i ∉ s := by simpa using his
    exact hi (funext fun j => by simp [A₁, his'])
  have h₂ : A₂.rank ≤ t.card := by
    rw [← rank_transpose]
    refine rank_le_card_of_support_subset A₂ᵀ t fun j hj => ?_
    by_contra hjt
    refine hj (funext fun i => ?_)
    by_cases his : i ∈ s
    · simp [A₂, his]
    · have : A i j = 0 := by
        by_contra hne
        exact (h i j hne).elim his hjt
      simp [A₂, his, this]
  rw [hA]
  exact (rank_add_le A₁ A₂).trans (add_le_add h₁ h₂)

/-- Let $A \in K^{m \times n}$ with $m$ finite. Then $\operatorname{rank} A = 0$ if and only if
$A = 0$. -/
theorem rank_eq_zero_iff [Finite m] {A : Matrix m n K} : A.rank = 0 ↔ A = 0 := by
  classical
  have := Fintype.ofFinite m
  refine ⟨fun h => ?_, fun h => h ▸ rank_zero⟩
  rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  exact toLin'.injective (h.trans (map_zero toLin').symm)

/-- Let $M \in K^{m \times n}$ and $N \in K^{m \times k}$. If the column space of $N$ lies in the
column space of $M$, then $MX = N$ for some $X \in K^{n \times k}$.

Each column of $N$ is $M$ applied to some vector, and these vectors are the columns of $X$. -/
theorem exists_mul_eq_of_range_mulVecLin_le {k : Type*} [Fintype k] {M : Matrix m n K}
    {N : Matrix m k K} (h : LinearMap.range N.mulVecLin ≤ LinearMap.range M.mulVecLin) :
    ∃ X, M * X = N := by
  classical
  have hc : ∀ j, ∃ x, M *ᵥ x = N *ᵥ Pi.single j 1 := fun j => by
    obtain ⟨x, hx⟩ := h (LinearMap.mem_range_self N.mulVecLin (Pi.single j 1))
    exact ⟨x, hx⟩
  choose x hx using hc
  refine ⟨of fun i j => x j i, ?_⟩
  ext r j
  have := congrFun (hx j) r
  rw [mulVec_single_one, col_apply] at this
  rw [← this]
  rfl

end Factorization

/-! ### Ranks of blocks and of padded matrices -/

section Blocks

variable {m n : Type*}

/-- Let $A \in K^{m \times n}$, and let $p \subseteq p'$ be sets of rows and $q \subseteq q'$ sets
of columns. Then $\operatorname{rank} A[p, q] \le \operatorname{rank} A[p', q']$: shrinking a
block does not increase its rank. -/
theorem rank_toBlock_mono [Fintype n] (A : Matrix m n K) {p p' : m → Prop}
    {q q' : n → Prop} [DecidablePred q] [DecidablePred q'] (hp : ∀ i, p i → p' i)
    (hq : ∀ j, q j → q' j) : (A.toBlock p q).rank ≤ (A.toBlock p' q').rank :=
  rank_submatrix_le (A.toBlock p' q') (Subtype.map id hp) (Subtype.map id hq)

/-- Let $A \in K^{m \times n}$, let $p$ be a set of columns and $q$ a set of rows of $A$. Then
$\operatorname{rank} A^T[p, q] = \operatorname{rank} A[q, p]$. -/
theorem rank_toBlock_transpose [Fintype m] [Fintype n] (A : Matrix m n K) (p : n → Prop)
    (q : m → Prop) [DecidablePred p] [DecidablePred q] :
    (Aᵀ.toBlock p q).rank = (A.toBlock q p).rank :=
  rank_transpose (A.toBlock q p)

/-- **Padding with zero rows does not change the rank.** Let $f : p \to n$ be injective, let
$X \in K^{p \times q}$, and let $I(:, f) \in K^{n \times p}$ be the matrix of the columns
$e_{f(j)}$ of the identity. Then $\operatorname{rank}(I(:, f)\, X) = \operatorname{rank} X$. The
matrix $I(:, f)\, X$ has the rows of $X$ at the positions $f(j)$ and zero rows elsewhere. -/
theorem rank_submatrix_one_mul [Finite n] [DecidableEq n] {p q : Type*} [Fintype p]
    [Fintype q] {f : p → n} (hf : Function.Injective f) (X : Matrix p q K) :
    ((1 : Matrix n n K).submatrix id f * X).rank = X.rank := by
  classical
  have := Fintype.ofFinite n
  refine le_antisymm (rank_mul_le_right _ _) ?_
  have h : ((1 : Matrix n n K).submatrix id f)ᵀ * (1 : Matrix n n K).submatrix id f = 1 := by
    rw [transpose_submatrix, transpose_one, ← submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.one_mul, submatrix_one _ hf]
  calc X.rank = (((1 : Matrix n n K).submatrix id f)ᵀ *
        ((1 : Matrix n n K).submatrix id f * X)).rank := by
        rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    _ ≤ _ := rank_mul_le_right _ _

end Blocks

/-! ### The nullity theorem -/

section Nullity

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A block applied to a vector is the matrix applied to the extension of the vector by zero,
restricted to the rows of the block: $M[p, q]\, x = (M \bar x)|_p$. -/
private theorem toBlock_mulVec (M : Matrix n n K) (p q : n → Prop) [DecidablePred q]
    (x : {j // q j} → K) :
    (M.toBlock p q) *ᵥ x = (M *ᵥ Function.extend Subtype.val x 0) ∘ Subtype.val :=
  submatrix_mulVec_eq_comp_mulVec_extend M Subtype.val Subtype.val_injective x

/-- One direction of the correspondence in the nullity theorem: if $AB = I$ and $B[p, q]\, x = 0$,
then $(B \bar x)|_{p^c}$ is in the null space of $A[q^c, p^c]$, where $\bar x$ is the extension
of $x$ by zero. -/
private theorem mem_ker_toBlock_of_mem_ker_toBlock {A B : Matrix n n K} (hAB : A * B = 1)
    {p q p' q' : n → Prop} [DecidablePred q] [DecidablePred p'] (hp : ∀ i, p' i ↔ ¬ p i)
    (hq : ∀ i, q' i ↔ ¬ q i) {x : {j // q j} → K}
    (hx : (B.toBlock p q) *ᵥ x = 0) :
    (A.toBlock q' p') *ᵥ ((B *ᵥ Function.extend Subtype.val x 0) ∘ Subtype.val) = 0 := by
  have hz : ∀ i, ¬ p' i → (B *ᵥ Function.extend Subtype.val x 0) i = 0 := fun i hi => by
    have := congrFun hx ⟨i, not_not.1 ((not_congr (hp i)).1 hi)⟩
    rwa [toBlock_mulVec] at this
  rw [toBlock_mulVec, Function.extend_val_comp_val hz, mulVec_mulVec, hAB, one_mulVec]
  funext i
  exact Function.extend_val_apply' ((hq i).1 i.2)

/-- **The nullity theorem, kernel form.** Let $A \in K^{n \times n}$ be invertible, and let $p$ and
$q$ be sets of indices. Then
$$\dim \operatorname{Null}(A^{-1}[p, q]) = \dim \operatorname{Null}(A[q^c, p^c]).$$
This is the theorem of Fiedler and Markham (1986) that [golub2013matrix], §12.2, cites.

The linear equivalence between the two null spaces is $x \mapsto (A^{-1} \bar x)|_{p^c}$, with
inverse $y \mapsto (A \bar y)|_q$, where a bar denotes the extension by zero. The complements
are `fun i => ¬ q i` and `fun j => ¬ p j`. -/
theorem finrank_ker_toBlock_inv {A : Matrix n n K} (hA : IsUnit A) (p q : n → Prop)
    [DecidablePred p] [DecidablePred q] :
    finrank K (LinearMap.ker (A⁻¹.toBlock p q).mulVecLin)
      = finrank K (LinearMap.ker (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).mulVecLin) := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := mul_nonsing_inv A hdet
  have h2 : A⁻¹ * A = 1 := nonsing_inv_mul A hdet
  let φ : LinearMap.ker (A⁻¹.toBlock p q).mulVecLin →ₗ[K]
      LinearMap.ker (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).mulVecLin :=
    LinearMap.codRestrict _ (LinearMap.funLeft K K Subtype.val ∘ₗ A⁻¹.mulVecLin ∘ₗ
      Function.ExtendByZero.linearMap K K Subtype.val ∘ₗ Submodule.subtype _) fun x =>
        mem_ker_toBlock_of_mem_ker_toBlock h1 (fun _ => Iff.rfl) (fun _ => Iff.rfl) x.2
  let ψ : LinearMap.ker (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).mulVecLin →ₗ[K]
      LinearMap.ker (A⁻¹.toBlock p q).mulVecLin :=
    LinearMap.codRestrict _ (LinearMap.funLeft K K Subtype.val ∘ₗ A.mulVecLin ∘ₗ
      Function.ExtendByZero.linearMap K K Subtype.val ∘ₗ Submodule.subtype _) fun y =>
        mem_ker_toBlock_of_mem_ker_toBlock h2 (fun _ => not_not.symm) (fun _ => not_not.symm) y.2
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinearMap φ ψ ?_ ?_)
  · ext y : 2
    have hy : (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)) *ᵥ (y : {j // ¬ p j} → K) = 0 := y.2
    have hvan : ∀ i, ¬ q i → (A *ᵥ Function.extend Subtype.val (y : {j // ¬ p j} → K) 0) i = 0 :=
      fun i hi => by
        have := congrFun hy ⟨i, hi⟩
        rwa [toBlock_mulVec] at this
    change (A⁻¹ *ᵥ Function.extend Subtype.val
      ((A *ᵥ Function.extend Subtype.val (y : {j // ¬ p j} → K) 0) ∘ Subtype.val) 0)
        ∘ Subtype.val = (y : {j // ¬ p j} → K)
    rw [Function.extend_val_comp_val hvan, mulVec_mulVec, h2, one_mulVec]
    funext j
    exact Subtype.val_injective.extend_apply _ _ j
  · ext x : 2
    have hx : (A⁻¹.toBlock p q) *ᵥ (x : {j // q j} → K) = 0 := x.2
    have hvan : ∀ i, ¬ ¬ p i →
        (A⁻¹ *ᵥ Function.extend Subtype.val (x : {j // q j} → K) 0) i = 0 := fun i hi => by
      have := congrFun hx ⟨i, not_not.1 hi⟩
      rwa [toBlock_mulVec] at this
    change (A *ᵥ Function.extend Subtype.val
      ((A⁻¹ *ᵥ Function.extend Subtype.val (x : {j // q j} → K) 0) ∘ Subtype.val) 0)
        ∘ Subtype.val = (x : {j // q j} → K)
    rw [Function.extend_val_comp_val hvan, mulVec_mulVec, h1, one_mulVec]
    funext j
    exact Subtype.val_injective.extend_apply _ _ j

/-- **The nullity theorem, rank form** (Fiedler and Markham 1986; Strang and Nguyen 2004). Let
$A \in K^{n \times n}$ be invertible, and let $p$ and $q$ be sets of indices. Then
$$\operatorname{rank} A^{-1}[p, q] + n = \operatorname{rank} A[q^c, p^c] + |p| + |q|.$$

Rank–nullity on the two blocks (`LinearMap.finrank_range_add_finrank_ker`) turns
`Matrix.finrank_ker_toBlock_inv` into this identity. -/
theorem rank_toBlock_inv_add_card {A : Matrix n n K} (hA : IsUnit A) (p q : n → Prop)
    [DecidablePred p] [DecidablePred q] :
    (A⁻¹.toBlock p q).rank + Fintype.card n
      = (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).rank + Fintype.card {i // p i}
        + Fintype.card {j // q j} := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker (A⁻¹.toBlock p q).mulVecLin
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).mulVecLin
  rw [finrank_pi] at h₁ h₂
  have hk := finrank_ker_toBlock_inv hA p q
  have hc : Fintype.card {j // ¬ p j} + Fintype.card {i // p i} = Fintype.card n := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le p)
  rw [rank, rank]
  omega

/-- **The nullity theorem for an off-diagonal block** ([golub2013matrix], §4.3.8; Strang and Nguyen
2004). Let
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}$$
be invertible, with square diagonal blocks $A_{11} \in K^{m \times m}$ and
$A_{22} \in K^{n' \times n'}$. Then the lower-left blocks of $A^{-1}$ and $A$ have the same
rank:
$$\operatorname{rank} (A^{-1})_{21} = \operatorname{rank} A_{21}.$$
The diagonal blocks need not be invertible.

The block $A_{21}$ is `A.toBlocks₂₁`, with rows indexed by $n'$ and columns by $m$. The proof
is the case $p = n'$, $q = m$ of `Matrix.rank_toBlock_inv_add_card`. -/
theorem rank_inv_toBlocks₂₁ {m n' : Type*} [Fintype m] [Fintype n'] [DecidableEq m]
    [DecidableEq n'] {A : Matrix (m ⊕ n') (m ⊕ n') K} (hA : IsUnit A) :
    (A⁻¹).toBlocks₂₁.rank = A.toBlocks₂₁.rank := by
  have h := rank_toBlock_inv_add_card hA (fun i => i.isRight) (fun i => i.isLeft)
  let e₁ : {i : m ⊕ n' // ¬ i.isLeft} ≃ n' :=
    (Equiv.subtypeEquivRight fun i => by simp).trans (Equiv.sumIsRight (α := m) (β := n'))
  let e₂ : {i : m ⊕ n' // ¬ i.isRight} ≃ m :=
    (Equiv.subtypeEquivRight fun i => by simp).trans (Equiv.sumIsLeft (α := m) (β := n'))
  have hB₁ : (A⁻¹.toBlock (fun i => i.isRight) (fun i => i.isLeft)).rank
      = (A⁻¹).toBlocks₂₁.rank := by
    rw [← rank_submatrix (A⁻¹).toBlocks₂₁ (Equiv.sumIsRight (α := m) (β := n'))
      (Equiv.sumIsLeft (α := m) (β := n'))]
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    cases i <;> cases j <;> simp_all [toBlock, toBlocks₂₁]
  have hB₂ : (A.toBlock (fun i => ¬ i.isLeft) (fun j => ¬ j.isRight)).rank
      = A.toBlocks₂₁.rank := by
    rw [← rank_submatrix A.toBlocks₂₁ e₁ e₂]
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    cases i <;> cases j <;> simp_all [e₁, e₂, toBlock, toBlocks₂₁]
  rw [hB₁, hB₂, Fintype.card_sum, Fintype.card_congr (Equiv.sumIsRight (α := m) (β := n')),
    Fintype.card_congr (Equiv.sumIsLeft (α := m) (β := n'))] at h
  omega

/-- **The nullity theorem for the other off-diagonal block.** Let $A$ be an invertible $2 \times 2$
block matrix with square diagonal blocks of orders $m$ and $n'$. Then the upper-right blocks of
$A^{-1}$ and $A$ have the same rank:
$$\operatorname{rank} (A^{-1})_{12} = \operatorname{rank} A_{12}.$$

The block $A_{12}$ is `A.toBlocks₁₂`. The proof applies `Matrix.rank_inv_toBlocks₂₁` to $A^T$:
$(A^{-1})^T = (A^T)^{-1}$, the lower-left block of $A^T$ is the transpose of the upper-right
block of $A$, and transposition keeps the rank. -/
theorem rank_inv_toBlocks₁₂ {m n' : Type*} [Fintype m] [Fintype n'] [DecidableEq m]
    [DecidableEq n'] {A : Matrix (m ⊕ n') (m ⊕ n') K} (hA : IsUnit A) :
    (A⁻¹).toBlocks₁₂.rank = A.toBlocks₁₂.rank := by
  have e : ∀ M : Matrix (m ⊕ n') (m ⊕ n') K, Mᵀ.toBlocks₂₁ = M.toBlocks₁₂ᵀ := fun _ => rfl
  have h := rank_inv_toBlocks₂₁ ((isUnit_transpose A).2 hA)
  rwa [← transpose_nonsing_inv, e, e, rank_transpose, rank_transpose] at h

end Nullity

end Matrix
