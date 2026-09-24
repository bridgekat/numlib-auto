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
import Numlib.LinearAlgebra.Matrix.BlockDiagonal

/-!
# The nullity of a matrix, and the rank as the largest nonvanishing minor

The *nullity* of a square matrix `A` over a field is the dimension of its null space
`LinearMap.ker A.mulVecLin`, the `Null A` of numerical linear algebra. Mathlib has `Matrix.rank`,
the dimension of the range, but not the rank–nullity relation between the two, nor the invariance
of the null space dimension under the operations that leave the rank alone. Nor does it have the
classical characterization of the rank as the largest order of a nonvanishing minor
([quarteroni2000numerical] Definition 1.12), which is the last section.

## Main statements

* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity, `A.rank + nullity A = card`.
* `Matrix.finrank_ker_mulVecLin_reindex` and `Matrix.finrank_ker_mulVecLin_conj`: the nullity is
  unchanged by reindexing and by conjugation with an invertible matrix, both because the rank is.
* `Matrix.ker_mulVecLin_pow_le_succ`: the null spaces of the powers of a square matrix increase.
* `Matrix.finrank_ker_mulVecLin_blockDiagonal'`: the nullity of a block diagonal matrix is the sum
  of the nullities of its blocks, since its null space is the product of theirs
  (`Matrix.kerMulVecLinBlockDiagonal'Equiv`).
* `Matrix.rank_eq_sup_card_det_submatrix_ne_zero`: the rank of a rectangular matrix is the
  largest `k` for which some `k × k` submatrix has nonzero determinant; the two inequalities are
  `Matrix.card_le_rank_of_det_submatrix_ne_zero` and `Matrix.exists_det_submatrix_ne_zero`.
* `Matrix.rank_add_le`, subadditivity, and the rank factorization
  `Matrix.rank_le_iff_exists_mul` (`rank A ≤ r ↔ A = B C` through `K^r`) with its generator form
  `Matrix.rank_le_iff_exists_mul_transpose`; `Matrix.rank_le_card_add_card_of_forall_ne_zero`, the
  rank bound of a matrix supported on a few rows and columns.
* **The nullity theorem** (Fiedler–Markham; Strang–Nguyen): for invertible `A`,
  `Matrix.finrank_ker_toBlock_inv` (the null spaces of `A⁻¹[p, q]` and `A[¬q, ¬p]` have the same
  dimension), its rank form `Matrix.rank_toBlock_inv_add_card`, and the block corollaries
  `Matrix.rank_inv_toBlocks₂₁`, `Matrix.rank_inv_toBlocks₁₂` ([golub2013matrix] §4.3.8). The
  algebra behind it is `Matrix.submatrix_mulVec_eq_comp_mulVec_extend`: a submatrix applied to a
  vector is the matrix applied to its extension by zero.
-/

open Module

namespace Matrix

variable {ι : Type*} {m : ι → Type*} {K : Type*} [Field K]

section Square

variable {n n' : Type*} [Fintype n] [Fintype n']

/-- **Rank–nullity for a square matrix**: the rank of `A` and the dimension of its null space add
up to the number of columns. -/
theorem rank_add_finrank_ker_mulVecLin (A : Matrix n n K) :
    A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi]

/-- Reindexing a square matrix does not change the dimension of its null space. -/
theorem finrank_ker_mulVecLin_reindex (σ : n ≃ n') (A : Matrix n n K) :
    finrank K (LinearMap.ker (reindex σ σ A).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (reindex σ σ A)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_reindex] at h₁
  rw [Fintype.card_congr σ] at h₂
  omega

variable [DecidableEq n]

/-- Conjugating a square matrix by an invertible matrix does not change its rank. -/
theorem rank_conj {A P : Matrix n n K} (hP : IsUnit P) : (P * A * P⁻¹).rank = A.rank := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det P hd),
    rank_mul_eq_right_of_isUnit_det _ _ hd]

/-- Conjugating a square matrix by an invertible matrix does not change the dimension of its null
space. -/
theorem finrank_ker_mulVecLin_conj {A P : Matrix n n K} (hP : IsUnit P) :
    finrank K (LinearMap.ker (P * A * P⁻¹).mulVecLin)
      = finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := rank_add_finrank_ker_mulVecLin (P * A * P⁻¹)
  have h₂ := rank_add_finrank_ker_mulVecLin A
  rw [rank_conj hP] at h₁
  omega

/-- A square matrix over a field of full rank is nonsingular: its kernel has dimension `0` by
rank–nullity, so `x ↦ A x` is injective. -/
theorem isUnit_of_rank_eq_card {A : Matrix n n K} (h : A.rank = Fintype.card n) : IsUnit A := by
  have hk := rank_add_finrank_ker_mulVecLin A
  rw [h] at hk
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- The null spaces of the powers of a square matrix increase with the exponent. -/
theorem ker_mulVecLin_pow_le_succ (A : Matrix n n K) (k : ℕ) :
    LinearMap.ker ((A ^ k).mulVecLin) ≤ LinearMap.ker ((A ^ (k + 1)).mulVecLin) := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  rw [pow_succ', ← mulVec_mulVec, hv, mulVec_zero]

end Square

section BlockDiagonal

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (m i)]

/-- The null space of a block diagonal matrix is the product of the null spaces of its blocks: a
vector is annihilated by `blockDiagonal' M` exactly when each of its blocks is annihilated by the
corresponding `M i`. -/
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

/-- **The nullity of a block diagonal matrix** is the sum of the nullities of its blocks. -/
theorem finrank_ker_mulVecLin_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) K) :
    finrank K (LinearMap.ker (blockDiagonal' M).mulVecLin)
      = ∑ i, finrank K (LinearMap.ker (M i).mulVecLin) := by
  rw [(kerMulVecLinBlockDiagonal'Equiv M).finrank_eq, Module.finrank_pi_fintype]

end BlockDiagonal

section Minor

variable {m n : Type*} [Fintype n] (A : Matrix m n K)

/-- A nonvanishing minor of order `k` forces rank at least `k`: the `k × k` submatrix is a unit,
so its rank is `k`, and the rank of a submatrix is at most the rank. -/
theorem card_le_rank_of_det_submatrix_ne_zero {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  have hu : IsUnit (A.submatrix r c) := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have := rank_submatrix_le A r c
  rwa [rank_of_isUnit _ hu, Fintype.card_fin] at this

omit [Fintype n] in
/-- The row selection of a nonvanishing minor is injective: two equal rows give a zero
determinant. -/
theorem injective_of_det_submatrix_ne_zero_left {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective r := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_row_eq hne (funext fun j => by simp [hab]))

omit [Fintype n] in
/-- The column selection of a nonvanishing minor is injective. -/
theorem injective_of_det_submatrix_ne_zero_right {k : ℕ} {r : Fin k → m} {c : Fin k → n}
    (h : (A.submatrix r c).det ≠ 0) : Function.Injective c := fun a b hab => by
  by_contra hne
  exact h (det_zero_of_column_eq hne fun i => by simp [hab])

/-- A matrix of rank `k` has `k` linearly independent columns. -/
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

/-- A matrix of rank `k` has a nonsingular `k × k` submatrix: choose `k` linearly independent
columns, then `k` linearly independent rows of the resulting `m × k` matrix (which has rank `k`
as well); a square matrix with linearly independent rows is a unit. -/
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
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
  exact hr

/-- [quarteroni2000numerical] Definition 1.12 as a theorem: the rank is the largest order of a
nonvanishing minor. The set of orders is bounded by the rank
(`Matrix.card_le_rank_of_det_submatrix_ne_zero`) and attains it
(`Matrix.exists_det_submatrix_ne_zero`). -/
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

/-- **The rank is subadditive**: `rank (A + B) ≤ rank A + rank B`, the column space of `A + B`
lying in the sum of those of `A` and `B`. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, rank, rank, mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **The rank factorization**: `A` has rank at most `r` exactly when it factors as `A = B C`
through `K^r`, `B : Matrix m (Fin r) K`, `C : Matrix (Fin r) n K`. Coordinates on a basis of the
column space, padded by zeros to length `r`, give the factorization. -/
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
      LinearMap.toMatrix' (Function.ExtendByZero.linearMap K ι ∘ₗ e.toLinearMap ∘ₗ f), ?_⟩
    rw [← LinearMap.toMatrix'_comp]
    have hι : LinearMap.funLeft K K ι ∘ₗ Function.ExtendByZero.linearMap K ι = LinearMap.id := by
      ext x i
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply,
        Function.ExtendByZero.linearMap_apply, LinearMap.id_coe, id_eq]
      exact (Fin.castLE_injective hk).extend_apply _ _ i
    have hcomp : V.subtype ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.funLeft K K ι ∘ₗ
        (Function.ExtendByZero.linearMap K ι ∘ₗ e.toLinearMap ∘ₗ f) = A.mulVecLin := by
      refine LinearMap.ext fun x => ?_
      have hx := LinearMap.congr_fun hι (e (f x))
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hx
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hx,
        LinearEquiv.symm_apply_apply, Submodule.coe_subtype, f, LinearMap.codRestrict_apply]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hcomp]
    exact (LinearMap.toMatrix'_toLin' A).symm
  · rintro ⟨B, C, rfl⟩
    exact (rank_mul_le_left B C).trans ((rank_le_card_width B).trans_eq (Fintype.card_fin r))

/-- The generator form of the rank factorization ([golub2013matrix] (12.1.3), displacement
structure): `rank A ≤ r` exactly when `A = R Sᵀ` with `R : Matrix m (Fin r) K`,
`S : Matrix n (Fin r) K`. -/
theorem rank_le_iff_exists_mul_transpose (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (R : Matrix m (Fin r) K) (S : Matrix n (Fin r) K), A = R * Sᵀ := by
  rw [rank_le_iff_exists_mul]
  exact ⟨fun ⟨B, C, h⟩ => ⟨B, Cᵀ, by rwa [transpose_transpose]⟩,
    fun ⟨R, S, h⟩ => ⟨R, Sᵀ, h⟩⟩

/-- **A matrix supported on `s` rows and `t` columns has rank at most `|s| + |t|`**: if every
nonzero entry lies in a row of `s` or a column of `t`, split `A` into its rows in `s` and the rest,
which is supported on the columns `t`. Every displacement-rank bound of [golub2013matrix]
(12.1.8)–(12.1.11) is an instance. -/
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

end Factorization

/-! ### The nullity theorem -/

/-- A submatrix applied to a vector: `(A.submatrix f g) x` is `A` applied to `x` extended by zero
along an injective `g`, restricted to the rows `f`. -/
theorem submatrix_mulVec_eq_comp_mulVec_extend {R m m' n n' : Type*}
    [NonUnitalNonAssocSemiring R] [Fintype n] [Fintype n'] (B : Matrix m n R) (f : m' → m)
    {g : n' → n} (hg : Function.Injective g) (x : n' → R) :
    B.submatrix f g *ᵥ x = (B *ᵥ Function.extend g x 0) ∘ f := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
  exact Fintype.sum_of_injective g hg _ _ (fun k hk => by
    rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply, mul_zero]) fun j => by
    rw [hg.extend_apply]

section Nullity

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A vector vanishing outside `r` is the extension by zero of its restriction to `r`. -/
private theorem extend_val_comp_val {r : n → Prop} {z : n → K} (hz : ∀ i, ¬ r i → z i = 0) :
    Function.extend (Subtype.val : {i // r i} → n) (z ∘ Subtype.val) 0 = z := by
  funext i
  by_cases hi : r i
  · exact Subtype.val_injective.extend_apply _ _ ⟨i, hi⟩
  · rw [Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hi (ha ▸ a.2)), hz i hi, Pi.zero_apply]

omit [Fintype n] [DecidableEq n] in
/-- An extension by zero vanishes outside the range. -/
private theorem extend_val_apply_of_not {r : n → Prop} (x : {i // r i} → K) {i : n}
    (hi : ¬ r i) : Function.extend (Subtype.val : {i // r i} → n) x 0 i = 0 := by
  rw [Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hi (ha ▸ a.2)), Pi.zero_apply]

omit [DecidableEq n] in
/-- A block applied to a vector is the matrix applied to its extension by zero, restricted. -/
private theorem toBlock_mulVec (M : Matrix n n K) (p q : n → Prop) [DecidablePred q]
    (x : {j // q j} → K) :
    (M.toBlock p q) *ᵥ x = (M *ᵥ Function.extend Subtype.val x 0) ∘ Subtype.val :=
  submatrix_mulVec_eq_comp_mulVec_extend M Subtype.val Subtype.val_injective x

/-- The correspondence of the nullity theorem, one direction: if `A B = 1` and `B[p, q] x = 0`,
then `(B x̄)|_{p'}` is in the null space of `A[q', p']`, where `p'`, `q'` are the complements of
`p`, `q` and `x̄` is the extension of `x` by zero. -/
private theorem mem_ker_toBlock_of_mem_ker_toBlock {A B : Matrix n n K} (hAB : A * B = 1)
    {p q p' q' : n → Prop} [DecidablePred q] [DecidablePred p'] (hp : ∀ i, p' i ↔ ¬ p i)
    (hq : ∀ i, q' i ↔ ¬ q i) {x : {j // q j} → K}
    (hx : (B.toBlock p q) *ᵥ x = 0) :
    (A.toBlock q' p') *ᵥ ((B *ᵥ Function.extend Subtype.val x 0) ∘ Subtype.val) = 0 := by
  have hz : ∀ i, ¬ p' i → (B *ᵥ Function.extend Subtype.val x 0) i = 0 := fun i hi => by
    have := congrFun hx ⟨i, not_not.1 ((not_congr (hp i)).1 hi)⟩
    rwa [toBlock_mulVec] at this
  rw [toBlock_mulVec, extend_val_comp_val hz, mulVec_mulVec, hAB, one_mulVec]
  funext i
  exact extend_val_apply_of_not x ((hq i).1 i.2)

/-- **The nullity theorem, kernel form** (Fiedler–Markham 1986, cited by [golub2013matrix]
§12.2): for an invertible `A` and index predicates `p`, `q`, the null spaces of `A⁻¹[p, q]` and of
`A[¬q, ¬p]` have the same dimension. The correspondence is `x ↦ (A⁻¹ x̄)|_{¬p}`, with inverse
`y ↦ (A ȳ)|_q`, the bars denoting extension by zero. -/
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
      Function.ExtendByZero.linearMap K Subtype.val ∘ₗ Submodule.subtype _) fun x =>
        mem_ker_toBlock_of_mem_ker_toBlock h1 (fun _ => Iff.rfl) (fun _ => Iff.rfl) x.2
  let ψ : LinearMap.ker (A.toBlock (fun i => ¬ q i) (fun j => ¬ p j)).mulVecLin →ₗ[K]
      LinearMap.ker (A⁻¹.toBlock p q).mulVecLin :=
    LinearMap.codRestrict _ (LinearMap.funLeft K K Subtype.val ∘ₗ A.mulVecLin ∘ₗ
      Function.ExtendByZero.linearMap K Subtype.val ∘ₗ Submodule.subtype _) fun y =>
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
    rw [extend_val_comp_val hvan, mulVec_mulVec, h2, one_mulVec]
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
    rw [extend_val_comp_val hvan, mulVec_mulVec, h1, one_mulVec]
    funext j
    exact Subtype.val_injective.extend_apply _ _ j

/-- **The nullity theorem**, rank form (Fiedler–Markham 1986; Strang–Nguyen 2004): for an
invertible `A` and index predicates `p`, `q`,
`rank A⁻¹[p, q] + |n| = rank A[¬q, ¬p] + |p| + |q|`. Rank–nullity on the two blocks
(`LinearMap.finrank_range_add_finrank_ker`) turns `Matrix.finrank_ker_toBlock_inv` into this. -/
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

/-- **The nullity theorem for the off-diagonal blocks** ([golub2013matrix] §4.3.8; Strang–Nguyen
2004): for a nonsingular block matrix, `rank (A⁻¹)₂₁ = rank A₂₁`. The case `p = isRight`,
`q = isLeft` of `Matrix.rank_toBlock_inv_add_card`; no invertibility of the diagonal blocks is
needed. -/
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

/-- **The nullity theorem for the other off-diagonal block**: `rank (A⁻¹)₁₂ = rank A₁₂` for a
nonsingular block matrix, the case `p = isLeft`, `q = isRight` of
`Matrix.rank_toBlock_inv_add_card`. -/
theorem rank_inv_toBlocks₁₂ {m n' : Type*} [Fintype m] [Fintype n'] [DecidableEq m]
    [DecidableEq n'] {A : Matrix (m ⊕ n') (m ⊕ n') K} (hA : IsUnit A) :
    (A⁻¹).toBlocks₁₂.rank = A.toBlocks₁₂.rank := by
  have h := rank_toBlock_inv_add_card hA (fun i => i.isLeft) (fun i => i.isRight)
  let e₁ : {i : m ⊕ n' // ¬ i.isRight} ≃ m :=
    (Equiv.subtypeEquivRight fun i => by simp).trans (Equiv.sumIsLeft (α := m) (β := n'))
  let e₂ : {i : m ⊕ n' // ¬ i.isLeft} ≃ n' :=
    (Equiv.subtypeEquivRight fun i => by simp).trans (Equiv.sumIsRight (α := m) (β := n'))
  have hB₁ : (A⁻¹.toBlock (fun i => i.isLeft) (fun i => i.isRight)).rank
      = (A⁻¹).toBlocks₁₂.rank := by
    rw [← rank_submatrix (A⁻¹).toBlocks₁₂ (Equiv.sumIsLeft (α := m) (β := n'))
      (Equiv.sumIsRight (α := m) (β := n'))]
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    cases i <;> cases j <;> simp_all [toBlock, toBlocks₁₂]
  have hB₂ : (A.toBlock (fun i => ¬ i.isRight) (fun j => ¬ j.isLeft)).rank
      = A.toBlocks₁₂.rank := by
    rw [← rank_submatrix A.toBlocks₁₂ e₁ e₂]
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    cases i <;> cases j <;> simp_all [e₁, e₂, toBlock, toBlocks₁₂]
  rw [hB₁, hB₂, Fintype.card_sum, Fintype.card_congr (Equiv.sumIsLeft (α := m) (β := n')),
    Fintype.card_congr (Equiv.sumIsRight (α := m) (β := n'))] at h
  omega

end Nullity

end Matrix
