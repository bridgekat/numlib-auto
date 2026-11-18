/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.ReducedRowEchelon
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv
import NumlibSurface.BenIsraelGreville.Chapter00.Section03

/-!
# Hermite normal form and rank factorization

Section 0.4 of [benIsrael2003generalized] uses echelon forms to describe elimination
and to construct bases and full-rank factorizations.

## Deviations from the source

* **Equation (71)** (reading). The identity in the leading block requires the
  pivots to be normalized to one. Definition 1 also allows unnormalized pivots.
-/

namespace BenIsraelGreville.Chapter00

open Matrix Module

variable {K m n k : Type*} [Field K]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 0. A matrix in Hermite
normal form is in row-echelon form and all other entries in a pivot column vanish. -/
def IsHermiteNormalForm [LT m] [LT n] (A : Matrix m n K) : Prop :=
  A.IsRowEchelon ∧ ∀ i j c, i ≠ j → A.IsLeadingEntry j c → A i c = 0

/-- Normalizing every pivot of a Hermite normal form to one gives reduced
row-echelon form. -/
theorem IsReducedRowEchelon_iff_isHermiteNormalForm [LinearOrder m] [LT n]
    (A : Matrix m n K) :
    A.IsReducedRowEchelon ↔ IsHermiteNormalForm A ∧
      ∀ i c, A.IsLeadingEntry i c → A i c = 1 := by
  constructor
  · intro h
    exact ⟨⟨h.isRowEchelon, fun _ _ _ hij hp => h.eq_zero_of_ne_of_isLeadingEntry hij hp⟩,
      fun _ _ hp => h.eq_one hp⟩
  · rintro ⟨⟨he, hzero⟩, hone⟩
    refine ⟨he, ?_, ?_⟩
    · intro i c hp
      exact hone i c hp
    · intro i j c hij hp
      exact hzero i j c hij.ne hp

/-- **Equation (71)** of [benIsrael2003generalized], Chapter 0. Reordering the
columns of a normalized Hermite form puts the pivot columns first. In the
resulting block matrix the leading block is the identity and the lower blocks
vanish. -/
theorem exists_permutationMatrix_mul_eq_hermiteBlock [Fintype n] [DecidableEq n]
    {r : ℕ} (A : Matrix (Fin r ⊕ m) n K) (p : Fin r ↪ n)
    (hp : ∀ i j, A (Sum.inl i) (p j) = (1 : Matrix (Fin r) (Fin r) K) i j)
    (hz : ∀ i j, A (Sum.inr i) j = 0) :
    ∃ e : n ≃ Fin r ⊕ {j : n // j ∉ Set.range p},
      ∃ B : Matrix (Fin r) {j : n // j ∉ Set.range p} K,
        A * e.toPEquiv.toMatrix = fromBlocks 1 B 0 0 := by
  classical
  let J := {j : n // j ∉ Set.range p}
  let f : Fin r ⊕ J → n := Sum.elim p Subtype.val
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (p.injective h)
        | inr j => exact (j.2 ⟨i, h⟩).elim
      | inr i =>
        cases b with
        | inl j => exact (i.2 ⟨j, h.symm⟩).elim
        | inr j => exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range p
      · obtain ⟨i, rfl⟩ := hj
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩
  let e := Equiv.ofBijective f hf
  refine ⟨e.symm, fun i j => A (Sum.inl i) j, ?_⟩
  rw [PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
  ext i j
  cases i <;> cases j
  · exact hp _ _
  · rfl
  · exact hz _ _
  · exact hz _ _

/-- **Equation (71)** of [benIsrael2003generalized], Chapter 0. A normalized
Hermite form has a block presentation with its nonzero rows first and their
pivot columns first. -/
theorem exists_reindex_eq_hermiteBlock [LinearOrder m] [LinearOrder n] [WellFoundedLT n]
    (A : Matrix m n K) (hA : A.IsReducedRowEchelon) :
    let I := {i : m // A i ≠ 0}
    let I₀ := {i : m // A i = 0}
    ∃ p : I ↪ n, ∃ e : I ⊕ I₀ ≃ m,
      ∃ f : I ⊕ {j : n // j ∉ Set.range p} ≃ n,
        ∃ B : Matrix I {j : n // j ∉ Set.range p} K,
          A.submatrix e f = fromBlocks 1 B 0 0 := by
  classical
  dsimp only
  let I := {i : m // A i ≠ 0}
  have hLead (i : I) : ∃ j, A.IsLeadingEntry i.val j :=
    row_ne_zero_iff_exists_isLeadingEntry.mp i.property
  let p : I ↪ n := ⟨fun i => (hLead i).choose, by
    intro i j hij
    by_contra! h
    have hi := (hLead i).choose_spec
    have hj := (hLead j).choose_spec
    have hne : i.val ≠ j.val := fun he => h (Subtype.ext he)
    have hz := hA.eq_zero_of_ne_of_isLeadingEntry hne hj
    apply hi.2
    change (hLead i).choose = (hLead j).choose at hij
    rwa [hij]⟩
  let e : I ⊕ {i : m // A i = 0} ≃ m :=
    (Equiv.sumCongr (Equiv.refl I)
      (Equiv.subtypeEquivRight (fun _ => not_not.symm))).trans
      (Equiv.sumCompl fun i => A i ≠ 0)
  let f := (Equiv.sumCongr (Equiv.ofInjective p p.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range p))
  refine ⟨p, e, f, fun i j => A i.val j.val, ?_⟩
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change A i.val (p j) = (1 : Matrix I I K) i j
      by_cases h : i = j
      · subst j
        rw [Matrix.one_apply_eq]
        exact hA.eq_one (hLead i).choose_spec
      · rw [Matrix.one_apply_ne h]
        exact hA.eq_zero_of_ne_of_isLeadingEntry (fun he => h (Subtype.ext he))
          (hLead j).choose_spec
    | inr j => rfl
  | inr i =>
    have hz (j : n) : A i.val j = 0 := congrFun i.property j
    cases j <;> exact hz _

/-- **Section 0.4.2** of [benIsrael2003generalized]. Gaussian elimination
represents the row operations by their elementary matrices in multiplication order. -/
def GaussianElimination [Fintype m] [DecidableEq m] (A B : Matrix m n K) : Prop :=
  ∃ l : List (Matrix m m K), B = l.prod * A ∧
    ∀ E ∈ l, IsScaleOrAddRowMatrix E ∨
      ∃ i j : m, i ≠ j ∧ E = swapRowMatrix i j

/-- **Equation (73)** of [benIsrael2003generalized], Chapter 0. A change by
elementary row operations is exactly left multiplication by an invertible matrix. -/
theorem gaussianElimination_iff_exists_isUnit_mul [Fintype m] [DecidableEq m]
    (A B : Matrix m n K) :
    GaussianElimination A B ↔ ∃ E : Matrix m m K, IsUnit E ∧ B = E * A := by
  constructor
  · rintro ⟨l, hB, hFactors⟩
    refine ⟨l.prod, ?_, hB⟩
    have hUnit (T : Matrix m m K)
        (h : IsScaleOrAddRowMatrix T ∨ ∃ i j : m, i ≠ j ∧ T = swapRowMatrix i j) :
        IsUnit T := by
      rcases h with h | ⟨i, j, _, rfl⟩
      · rcases h with ⟨i, a, ha, rfl⟩ | ⟨i, j, b, hij, rfl⟩
        · exact ⟨Matrix.GeneralLinearGroup.rowScale i (Units.mk0 a ha), rfl⟩
        · exact ⟨Matrix.GeneralLinearGroup.transvection i j hij b, rfl⟩
      · exact ⟨Matrix.GeneralLinearGroup.swap K i j, rfl⟩
    have hProd (l : List (Matrix m m K)) (hl : ∀ T ∈ l, IsUnit T) : IsUnit l.prod := by
      induction l with
      | nil => exact isUnit_one
      | cons T l ih =>
        exact (hl T List.mem_cons_self).mul (ih (fun U hu => hl U (List.mem_cons_of_mem T hu)))
    exact hProd l (fun T hT => hUnit T (hFactors T hT))
  · rintro ⟨E, hE, heq⟩
    obtain ⟨l, rfl, h⟩ := exists_list_scaleOrAdd_of_isUnit E hE
    exact ⟨l, heq, fun T hT => Or.inl (h T hT)⟩

/-- **Section 0.4.2** of [benIsrael2003generalized]. Every finite rectangular
matrix has a normalized Hermite form obtained by an invertible row transformation. -/
theorem exists_isUnit_mul_isReducedRowEchelon {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) K) :
    ∃ E : Matrix (Fin a) (Fin a) K, IsUnit E ∧ (E * A).IsReducedRowEchelon :=
  Matrix.exists_isUnit_mul_isReducedRowEchelon A

/-- **Section 0.4.2** of [benIsrael2003generalized], Equations (72)–(73).
Elementary row operations put every finite rectangular matrix into normalized
Hermite form. -/
theorem exists_gaussianElimination_isReducedRowEchelon {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) K) :
    ∃ B, GaussianElimination A B ∧ B.IsReducedRowEchelon := by
  obtain ⟨E, hE, h⟩ := exists_isUnit_mul_isReducedRowEchelon A
  exact ⟨E * A, (gaussianElimination_iff_exists_isUnit_mul A _).mpr ⟨E, hE, rfl⟩, h⟩

/-- **Equation (74)** of [benIsrael2003generalized], Chapter 0. Invertible
left and right factors can be removed from the transformed matrix. -/
theorem eq_inv_mul_hermiteBlock_mul_inv [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A B : Matrix m n K} {E : Matrix m m K}
    {P : Matrix n n K} (hE : IsUnit E) (hP : IsUnit P) (h : E * A * P = B) :
    A = E⁻¹ * B * P⁻¹ := by
  rw [← h]
  calc
    A = (E⁻¹ * E) * A * (P * P⁻¹) := by
      rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det E).mp hE),
        mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP), Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

section RankFactorization

variable [Fintype m] [Fintype n] [Fintype k]

/-- **Section 0.4.4** of [benIsrael2003generalized]. In a full-rank factorization
of $A$, the two factors have full column and full row rank respectively, and their
common dimension is the rank of $A$. -/
structure IsRankFactorization (A : Matrix m n K) (F : Matrix m k K) (G : Matrix k n K) : Prop where
  eq_mul : A = F * G
  rank_eq : A.rank = Fintype.card k
  rank_left : F.rank = Fintype.card k
  rank_right : G.rank = Fintype.card k

omit [Fintype m] in
/-- **Lemma 1** of [benIsrael2003generalized], Chapter 0. A matrix factors through
a coordinate space of dimension equal to its rank, with both factors of that rank. -/
theorem lemma_1 (A : Matrix m n K) :
    ∃ (F : Matrix m (Fin A.rank) K) (G : Matrix (Fin A.rank) n K), IsRankFactorization A F G := by
  obtain ⟨F, G, h⟩ := (rank_le_iff_exists_mul A A.rank).mp le_rfl
  have hFG : (F * G).rank = Fintype.card (Fin A.rank) := by rw [← h, Fintype.card_fin]
  exact ⟨F, G, h, (Fintype.card_fin _).symm,
    le_antisymm F.rank_le_card_width (hFG.ge.trans (rank_mul_le_left _ _)),
    le_antisymm G.rank_le_card_height (hFG.ge.trans (rank_mul_le_right _ _))⟩

/-- A full-rank factorization transposes by reversing the transposed factors. -/
theorem IsRankFactorization.transpose {A : Matrix m n K} {F : Matrix m k K} {G : Matrix k n K}
    (h : IsRankFactorization A F G) : IsRankFactorization Aᵀ Gᵀ Fᵀ := by
  refine ⟨?_, (rank_transpose A).trans h.rank_eq, (rank_transpose G).trans h.rank_right,
    (rank_transpose F).trans h.rank_left⟩
  rw [h.eq_mul, transpose_mul]

omit [Fintype m] in
/-- Choosing a basis matrix for the range of $A$ determines the right factor
in its full-rank factorization. -/
theorem existsUnique_rankFactorization_right (A : Matrix m n K) (F : Matrix m k K)
    (hF : F.rank = Fintype.card k) (hRange : F.mulVecLin.range = A.mulVecLin.range) :
    ∃! G : Matrix k n K, IsRankFactorization A F G := by
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_mulVecLin_le hRange.ge
  have hRank : A.rank = Fintype.card k :=
    (congrArg (fun L : Submodule K (m → K) => finrank K L) hRange.symm).trans hF
  have hRight : G.rank = Fintype.card k := by
    refine le_antisymm G.rank_le_card_height ?_
    rw [← hRank, ← hG]
    exact rank_mul_le_right _ _
  refine ⟨G, ⟨hG.symm, hRank, hF, hRight⟩, ?_⟩
  intro Y hY
  rw [ext_iff_mulVec]
  intro x
  apply mulVec_injective_iff_rank_eq_card.mpr hF
  rw [mulVec_mulVec, mulVec_mulVec, ← hY.eq_mul, hG]

/-- Choosing a basis matrix for the row space of $A$ determines the left factor
in its full-rank factorization. -/
theorem existsUnique_rankFactorization_left (A : Matrix m n K) (G : Matrix k n K)
    (hG : G.rank = Fintype.card k) (hRange : (Gᵀ).mulVecLin.range = (Aᵀ).mulVecLin.range) :
    ∃! F : Matrix m k K, IsRankFactorization A F G := by
  obtain ⟨F, hF, hUni⟩ := existsUnique_rankFactorization_right Aᵀ Gᵀ
    ((rank_transpose G).trans hG) hRange
  refine ⟨Fᵀ, by simpa only [transpose_transpose] using hF.transpose, ?_⟩
  intro X hX
  simpa only [transpose_transpose] using congrArg Matrix.transpose (hUni Xᵀ hX.transpose)

/-- **Equation (79)** of [benIsrael2003generalized], Chapter 0. If $G$ is the
matrix of independent rows of the Hermite normal form and $P$ selects its
pivot columns, then the corresponding columns $AP$ supply the left factor. -/
theorem hermite_rankFactorization [DecidableEq k] (A : Matrix m n K) (G : Matrix k n K)
    (P : Matrix n k K) (hG : G.rank = Fintype.card k)
    (hRange : (Gᵀ).mulVecLin.range = (Aᵀ).mulVecLin.range) (hP : G * P = 1) :
    IsRankFactorization A (A * P) G := by
  obtain ⟨F, hF, _⟩ := existsUnique_rankFactorization_left A G hG hRange
  have hAP : A * P = F := by rw [hF.eq_mul, Matrix.mul_assoc, hP, Matrix.mul_one]
  rwa [hAP]

end RankFactorization

section HermiteBases

variable [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]

private theorem rank_eq_of_identity_rows {j : Type*} (M : Matrix j k K) (e : k → j)
    (he : M.submatrix e id = 1) : M.rank = Fintype.card k := by
  refine le_antisymm M.rank_le_card_width ?_
  have h := rank_submatrix_le M e (id : k → k)
  rwa [he, rank_one] at h

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The rank of a Hermite block matrix is the size of its leading identity. -/
theorem rank_hermiteBlock (B : Matrix k n K) :
    (fromBlocks (1 : Matrix k k K) B (0 : Matrix m k K) 0).rank = Fintype.card k := by
  let C := fromBlocks (1 : Matrix k k K) B (0 : Matrix m k K) 0
  refine le_antisymm ?_ ?_
  · have hC : C = fromRows (1 : Matrix k k K) (0 : Matrix m k K) * fromCols 1 B := by
      simp [C]
    change C.rank ≤ Fintype.card k
    rw [hC]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  · have h := rank_submatrix_le C (Sum.inl : k → k ⊕ m) (Sum.inl : k → k ⊕ n)
    change (1 : Matrix k k K).rank ≤ C.rank at h
    rwa [rank_one] at h

private theorem rank_eq_of_hermiteBlock {A : Matrix (k ⊕ m) (k ⊕ n) K}
    {E : Matrix (k ⊕ m) (k ⊕ m) K} {P : Matrix (k ⊕ n) (k ⊕ n) K} {B : Matrix k n K}
    (hE : IsUnit E) (hP : IsUnit P) (h : E * A * P = fromBlocks 1 B 0 0) :
    A.rank = Fintype.card k := by
  have hr := congrArg rank h
  rw [rank_mul_eq_left_of_isUnit_det P _ ((isUnit_iff_isUnit_det P).mp hP),
    rank_mul_eq_right_of_isUnit_det E _ ((isUnit_iff_isUnit_det E).mp hE)] at hr
  exact hr.trans (rank_hermiteBlock B)

/-- **Equation (75)** of [benIsrael2003generalized], Chapter 0. The pivot
columns of the original matrix form a basis of its range. Multiplication by
the column injection selects the leading columns of the permuted matrix. -/
theorem pivots_columns_basis_range (A : Matrix (k ⊕ m) (k ⊕ n) K)
    (E : Matrix (k ⊕ m) (k ⊕ m) K) (P : Matrix (k ⊕ n) (k ⊕ n) K)
    (B : Matrix k n K) (hE : IsUnit E) (hP : IsUnit P)
    (h : E * A * P = fromBlocks 1 B 0 0) :
    let P₁ := P * fromRows (1 : Matrix k k K) (0 : Matrix n k K)
    E * (A * P₁) = fromRows 1 0 ∧ (A * P₁).rank = Fintype.card k ∧
      (A * P₁).mulVecLin.range = A.mulVecLin.range := by
  intro P₁
  have he : E * (A * P₁) = fromRows 1 0 := calc
    E * (A * P₁) = (E * A * P) * fromRows (1 : Matrix k k K) (0 : Matrix n k K) := by
      simp only [P₁, Matrix.mul_assoc]
    _ = _ := by rw [h, fromBlocks_mul_fromRows]; simp
  have hRank : (A * P₁).rank = Fintype.card k := by
    have hRows := rank_eq_of_identity_rows (fromRows (1 : Matrix k k K) (0 : Matrix m k K))
      (Sum.inl : k → k ⊕ m) rfl
    rw [← he, rank_mul_eq_right_of_isUnit_det E _ ((isUnit_iff_isUnit_det E).mp hE)] at hRows
    exact hRows
  refine ⟨he, hRank, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · exact hRank.trans (rank_eq_of_hermiteBlock hE hP h).symm

/-- **Equation (76)** of [benIsrael2003generalized], Chapter 0. The columns of
$P[-B; I]$ form a basis of the null space of the original matrix. -/
theorem hermite_nullSpace_basis (A : Matrix (k ⊕ m) (k ⊕ n) K)
    (E : Matrix (k ⊕ m) (k ⊕ m) K) (P : Matrix (k ⊕ n) (k ⊕ n) K)
    (B : Matrix k n K) (hE : IsUnit E) (hP : IsUnit P)
    (h : E * A * P = fromBlocks 1 B 0 0) :
    let N := P * fromRows (-B) 1
    N.rank = Fintype.card n ∧ N.mulVecLin.range = A.mulVecLin.ker := by
  intro N
  have hRank : N.rank = Fintype.card n := by
    change (P * fromRows (-B) 1).rank = Fintype.card n
    rw [rank_mul_eq_right_of_isUnit_det P _ ((isUnit_iff_isUnit_det P).mp hP)]
    exact rank_eq_of_identity_rows (fromRows (-B) 1) (Sum.inr : n → k ⊕ n) rfl
  have hZero : E * (A * N) = 0 := calc
    E * (A * N) = (E * A * P) * fromRows (-B) 1 := by simp only [N, Matrix.mul_assoc]
    _ = 0 := by rw [h, fromBlocks_mul_fromRows]; simp
  have hAN : A * N = 0 := calc
    A * N = E⁻¹ * (E * (A * N)) := by
      rw [← Matrix.mul_assoc E⁻¹ E (A * N), nonsing_inv_mul _ ((isUnit_iff_isUnit_det E).mp hE),
        Matrix.one_mul]
    _ = 0 := by rw [hZero, Matrix.mul_zero]
  refine ⟨hRank, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← mulVecLin_mul, hAN]
    exact map_zero _
  · have hdim := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    change A.rank + finrank K A.mulVecLin.ker = finrank K (k ⊕ n → K) at hdim
    rw [rank_eq_of_hermiteBlock hE hP h, finrank_fintype_fun_eq_card, Fintype.card_sum] at hdim
    change N.rank = finrank K A.mulVecLin.ker
    omega

open scoped ComplexOrder in
/-- **Equation (77)** of [benIsrael2003generalized], Chapter 0. Taking the
adjoint of the independent leading rows gives a basis of the adjoint range. -/
theorem hermite_adjoint_range_basis (A : Matrix (k ⊕ m) (k ⊕ n) ℂ)
    (E : Matrix (k ⊕ m) (k ⊕ m) ℂ) (P : Matrix (k ⊕ n) (k ⊕ n) ℂ)
    (B : Matrix k n ℂ) (hE : IsUnit E) (hP : P ∈ Matrix.unitaryGroup (k ⊕ n) ℂ)
    (h : E * A * P = fromBlocks 1 B 0 0) :
    let G := fromCols (1 : Matrix k k ℂ) (0 : Matrix k m ℂ) * (E * A)
    Gᴴ = P * fromRows 1 Bᴴ ∧ Gᴴ.rank = Fintype.card k ∧
      Gᴴ.mulVecLin.range = Aᴴ.mulVecLin.range := by
  intro G
  let S := fromCols (1 : Matrix k k ℂ) (0 : Matrix k m ℂ)
  have hG : G * P = fromCols 1 B := calc
    G * P = S * (E * A * P) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [h]; simp [S, fromCols_mul_fromBlocks]
  have hAdj : Pᴴ * Gᴴ = fromRows 1 Bᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_one] using congrArg Matrix.conjTranspose hG
  have hAdj' : Gᴴ = P * fromRows 1 Bᴴ := calc
    Gᴴ = (P * Pᴴ) * Gᴴ := by
      rw [Matrix.mul_conjTranspose_self_of_mem_unitaryGroup hP, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, hAdj]
  have hUnitDet := isUnit_det_of_mem_unitaryGroup hP
  have hRank : Gᴴ.rank = Fintype.card k := by
    rw [hAdj', rank_mul_eq_right_of_isUnit_det P _ hUnitDet]
    exact rank_eq_of_identity_rows (fromRows 1 Bᴴ) (Sum.inl : k → k ⊕ n) rfl
  refine ⟨hAdj', hRank, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · have he : Gᴴ = Aᴴ * (Eᴴ * Sᴴ) := by
      change (S * (E * A))ᴴ = _
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [he, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · change Gᴴ.rank = Aᴴ.rank
    rw [hRank, rank_conjTranspose, rank_eq_of_hermiteBlock hE
      ((isUnit_iff_isUnit_det P).mpr hUnitDet) h]

end HermiteBases

/-- **Equation (80)** of [benIsrael2003generalized], Chapter 0. The example matrix
for Gaussian elimination, also used in Chapter 2 for a prescribed inverse. -/
def hermiteExampleMatrix : Matrix (Fin 3) (Fin 6) ℂ :=
  !![0, 2 * Complex.I, Complex.I, 0, 4 + 2 * Complex.I, 1;
    0, 0, 0, -3, -6, -3 - 3 * Complex.I;
    0, 2, 1, 1, 4 - 4 * Complex.I, 1]

end BenIsraelGreville.Chapter00
