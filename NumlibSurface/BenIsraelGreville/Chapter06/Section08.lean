/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GSVD
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Generalized and weighted singular values

Section 6.8 of [benIsrael2003generalized] studies the singular values
of a matrix pair and the singular values for positive definite weights.

## Deviations from the source

* In the proof of **Theorem 21**, the complex determinant factor is
  `(star (det X) * det X)⁻¹`. The ordering is imposed on the coefficients
  of the second matrix.
* In **Remark 1(a)**, the reduction for invertible `B` uses the ordinary
  singular values of `A * B⁻¹`. The paired coefficients in (183) depend
  on the simultaneous decomposition.
* **Definition 8** uses stationarity of the squared quotient so that zero
  singular values are included even when the norm quotient is nonsmooth.
* **Exercise 93** uses the rectangular pseudoinverse of the diagonal
  factor in Equation (201).
-/

namespace BenIsraelGreville.Chapter06

open Matrix
open scoped BigOperators ComplexConjugate

section Pencil

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n] [DecidableEq n]

/-- **Definition 7**, Equation (181) of [benIsrael2003generalized], Chapter 6.
The finite generalized singular values are the nonnegative roots of the Gram pencil. -/
def bSingularValues (A : Matrix a n ℂ) (B : Matrix b n ℂ) : Set ℝ :=
  {μ | 0 ≤ μ ∧ (Aᴴ * A - (μ ^ 2 : ℝ) • (Bᴴ * B)).det = 0}

/-- **Theorem 21**, determinant calculation of [benIsrael2003generalized], Chapter 6.
The determinant of a complex Gram pencil in simultaneous diagonal coordinates. -/
theorem det_gramPencil_of_congruence {A : Matrix a n ℂ} {B : Matrix b n ℂ}
    {X : Matrix n n ℂ} {α β : n → ℝ} (hX : IsUnit X)
    (hA : Xᴴ * (Aᴴ * A) * X = diagonal (fun i => ((α i ^ 2 : ℝ) : ℂ)))
    (hB : Xᴴ * (Bᴴ * B) * X = diagonal (fun i => ((β i ^ 2 : ℝ) : ℂ))) (μ : ℝ) :
    (Aᴴ * A - (μ ^ 2 : ℝ) • (Bᴴ * B)).det =
      (star X.det * X.det)⁻¹ * ∏ i, ((α i ^ 2 - μ ^ 2 * β i ^ 2 : ℝ) : ℂ) := by
  have hd :
      Xᴴ * (Aᴴ * A - (μ ^ 2 : ℝ) • (Bᴴ * B)) * X =
        diagonal (fun i => ((α i ^ 2 - μ ^ 2 * β i ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hA, hB]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have he := congrArg det hd
  rw [det_mul, det_mul, det_conjTranspose, det_diagonal] at he
  have hx : X.det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det X).mp hX)
  apply (eq_inv_mul_iff_mul_eq₀ (mul_ne_zero (star_ne_zero.mpr hx) hx)).2
  rw [← he]
  ring

/-- **Equation (183)** of [benIsrael2003generalized], Chapter 6, without sorting
the diagonal coefficients. A zero pair yields every nonnegative value, and a
nonzero second coefficient yields the ratio of the paired coefficients. -/
theorem mem_bSingularValues_iff_of_congruence {A : Matrix a n ℂ} {B : Matrix b n ℂ}
    {X : Matrix n n ℂ} {α β : n → ℝ} (hX : IsUnit X)
    (hA : Xᴴ * (Aᴴ * A) * X = diagonal (fun i => ((α i ^ 2 : ℝ) : ℂ)))
    (hB : Xᴴ * (Bᴴ * B) * X = diagonal (fun i => ((β i ^ 2 : ℝ) : ℂ)))
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) {μ : ℝ} :
    μ ∈ bSingularValues A B ↔
      0 ≤ μ ∧ ∃ i, (α i = 0 ∧ β i = 0) ∨ (β i ≠ 0 ∧ μ = α i / β i) := by
  classical
  have hx : X.det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det X).mp hX)
  change (0 ≤ μ ∧ _) ↔ _
  rw [det_gramPencil_of_congruence hX hA hB μ,
    mul_eq_zero, or_iff_right (inv_ne_zero (mul_ne_zero (star_ne_zero.mpr hx) hx)),
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Complex.ofReal_eq_zero]
  refine and_congr_right fun hμ => exists_congr fun i => ?_
  have hs : α i ^ 2 - μ ^ 2 * β i ^ 2 = 0 ↔ α i = μ * β i := by
    have hn : 0 ≤ μ * β i := mul_nonneg hμ (hβ i)
    rw [sub_eq_zero, ← mul_pow]
    constructor
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with he | he
      · exact he
      · linarith [hα i]
    · exact fun h => congrArg (· ^ 2) h
  rw [hs]
  by_cases hb : β i = 0
  · simp [hb]
  · simp [hb, eq_div_iff, eq_comm]

end Pencil

section GeneralizedSVD

variable {a b n : ℕ}

/-- **Theorem 21**, Equation (183) of [benIsrael2003generalized], Chapter 6.
The pencil has all nonnegative roots when the stacked matrix has deficient
column rank. At full column rank the roots are the ratios supported on
nonzero `β` in any GSVD. -/
theorem bSingularValues_eq_of_isGSVD
    {A : Matrix (Fin a) (Fin n) ℂ} {B : Matrix (Fin b) (Fin n) ℂ}
    {U : Matrix (Fin a) (Fin a) ℂ} {V : Matrix (Fin b) (Fin b) ℂ}
    {X : Matrix (Fin n) (Fin n) ℂ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U V X α β) (hna : n ≤ a) :
    bSingularValues A B = if (fromRows A B).rank < n then Set.Ici 0
      else {μ | ∃ i : Fin n, β i ≠ 0 ∧ μ = α i / β i} := by
  classical
  ext μ
  rw [mem_bSingularValues_iff_of_congruence h.isUnit
    (h.conjTranspose_mul_gram_mul₁ hna) h.conjTranspose_mul_gram_mul₂
    (fun i => (h.nonneg i).1) (fun i => (h.nonneg i).2)]
  split_ifs with hr
  · have hz := h.eq_zero_and_eq_zero_of_rank_le (fromRows A B).rank le_rfl
    exact ⟨And.left, fun hμ => ⟨hμ, ⟨⟨_, hr⟩, Or.inl hz⟩⟩⟩
  · have hz (i : Fin n) : ¬ (α i = 0 ∧ β i = 0) := by
      rintro ⟨ha, hb⟩
      by_cases hi : (i : ℕ) < (fromRows A B).rank - b
      · have := (h.eq_one_and_eq_zero_of_lt i hi).1
        linarith
      · have hs := h.sq_add_sq i (Nat.le_of_not_gt hi) (i.isLt.trans_le (le_of_not_gt hr))
        simp [ha, hb] at hs
    simp only [hz, false_or, Set.mem_ofPred_eq]
    exact ⟨And.right, fun ⟨i, hi, hμ⟩ =>
      ⟨hμ ▸ div_nonneg (h.nonneg i).1 (h.nonneg i).2, ⟨i, hi, hμ⟩⟩⟩

/-- **Remark 1(d)** of [benIsrael2003generalized], Chapter 6.
The rank test for the pencil is equivalent to a nontrivial common kernel. -/
theorem rank_fromRows_lt_iff_ker_inf_ne_bot
    (A : Matrix (Fin a) (Fin n) ℂ) (B : Matrix (Fin b) (Fin n) ℂ) :
    (fromRows A B).rank < n ↔ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin ≠ ⊥ := by
  have h := LinearMap.finrank_range_add_finrank_ker (fromRows A B).mulVecLin
  rw [← rank, Module.finrank_fin_fun, ← ker_inf_ker_eq_ker_fromRows] at h
  rw [ne_eq, ← Submodule.finrank_eq_zero]
  omega

/-- **Equation (182c)** of [benIsrael2003generalized], Chapter 6.
The decreasing, padded second diagonal has exactly `B.rank` positive entries. -/
theorem secondDiagonal_pos_iff_lt_rank {B : Matrix (Fin b) (Fin n) ℂ}
    {V : Matrix (Fin b) (Fin b) ℂ} {X : Matrix (Fin n) (Fin n) ℂ} {β : ℕ → ℝ}
    (hV : V ∈ unitaryGroup (Fin b) ℂ) (hX : IsUnit X)
    (hnonneg : ∀ i, 0 ≤ β i) (hanti : Antitone β)
    (htail : ∀ i, min b n ≤ i → β i = 0)
    (hD : Vᴴ * B * X = rectDiagonal (fun i => ((β i : ℝ) : ℂ))) (i : ℕ) :
    0 < β i ↔ i < B.rank := by
  have hr : B.rank ≤ min b n :=
    le_min (by simpa using rank_le_card_height B) (by simpa using rank_le_card_width B)
  have hS : IsSVD (B * X) V β 1 := by
    refine ⟨⟨hV, one_mem _, ?_⟩, hanti, hnonneg⟩
    rw [star_eq_conjTranspose, Matrix.mul_one, ← Matrix.mul_assoc]
    exact hD
  by_cases hi : i < min b n
  · rw [hS.singularValues_eq (hi.trans_le (min_le_left _ _)) (hi.trans_le (min_le_right _ _)),
      lt_iff_le_and_ne, and_iff_right ((B * X).sortedSingularValues_nonneg i), ne_comm,
      ne_eq, sortedSingularValues_eq_zero_iff_rank_le,
      rank_mul_eq_left_of_isUnit_det X B ((isUnit_iff_isUnit_det X).mp hX),
      not_le]
  · have hz := htail i (le_of_not_gt hi)
    rw [hz]
    exact iff_of_false (lt_irrefl 0) (not_lt.mpr (hr.trans (le_of_not_gt hi)))

/-- **Theorem 21**, Equation (182) of [benIsrael2003generalized], Chapter 6.
The two matrices have ordinary rectangular diagonals after unitary left
transformations and a common nonsingular right transformation. The second
diagonal is decreasing and padded with zeros. -/
theorem theorem_6_21 (hna : n ≤ a) (A : Matrix (Fin a) (Fin n) ℂ)
    (B : Matrix (Fin b) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin a) (Fin a) ℂ) (V : Matrix (Fin b) (Fin b) ℂ)
      (X : Matrix (Fin n) (Fin n) ℂ) (α β : ℕ → ℝ),
      U ∈ unitaryGroup (Fin a) ℂ ∧ V ∈ unitaryGroup (Fin b) ℂ ∧ IsUnit X ∧
      (∀ i, 0 ≤ α i ∧ 0 ≤ β i) ∧ Antitone β ∧ (∀ i, min b n ≤ i → β i = 0) ∧
      Uᴴ * A * X = rectDiagonal (fun i => ((α i : ℝ) : ℂ)) ∧
      Vᴴ * B * X = rectDiagonal (fun i => ((β i : ℝ) : ℂ)) ∧
      bSingularValues A B = if (fromRows A B).rank < n then Set.Ici 0
        else {μ | ∃ i : Fin n, β i ≠ 0 ∧ μ = α i / β i} := by
  classical
  obtain ⟨U, V, X, α, β, h⟩ := exists_isGSVD hna A B
  let e := Tuple.sortDesc (fun i : Fin n => β i)
  have he : Antitone (fun i : Fin n => β (e i)) :=
    Tuple.antitone_sortDesc (fun i : Fin n => β i)
  let p := (fromRows A B).rank - b
  have hp {j : Fin n} (hj : β (e j) ≠ 0) : p ≤ (e j : ℕ) ∧ (e j : ℕ) < p + b := by
    have hl : p ≤ (e j : ℕ) := by
      by_contra! hlt
      exact hj (h.eq_one_and_eq_zero_of_lt _ hlt).2
    have hr : (e j : ℕ) < (fromRows A B).rank := by
      by_contra! hge
      exact hj (h.eq_zero_and_eq_zero_of_rank_le _ hge).2
    exact ⟨hl, by dsimp [p]; omega⟩
  let J := {j : Fin n // β (e j) ≠ 0}
  let oldRow (j : J) : Fin b := ⟨(e j.1 : ℕ) - p, by
    obtain ⟨_, _⟩ := hp j.2
    omega⟩
  have hOld : Function.Injective oldRow := by
    intro i j hij
    apply Subtype.ext
    apply e.injective
    apply Fin.ext
    have hi := (hp i.2).1
    have hj := (hp j.2).1
    have hval := congrArg Fin.val hij
    change (e i.1 : ℕ) - p = (e j.1 : ℕ) - p at hval
    omega
  have hlt (j : J) : (j.1 : ℕ) < b := by
    let f : Fin ((j.1 : ℕ) + 1) → J := fun i =>
      ⟨⟨i, by have := j.1.isLt; omega⟩, by
        apply ne_of_gt
        have hj : 0 < β (e j.1) := lt_of_le_of_ne (h.nonneg _).2 j.2.symm
        apply hj.trans_le (he ?_)
        change (i : ℕ) ≤ (j.1 : ℕ)
        omega⟩
    have hf : Function.Injective f := fun i k hik =>
      Fin.ext (congrArg (fun t : J => (t.1 : ℕ)) hik)
    have hcard := Fintype.card_le_of_injective (oldRow ∘ f) (hOld.comp hf)
    simpa only [Fintype.card_fin, Nat.succ_le_iff] using hcard
  let newRow (j : J) : Fin b := ⟨j.1, hlt j⟩
  have hNew : Function.Injective newRow := fun i j hij =>
    Subtype.ext (Fin.ext (congrArg (Fin.val : Fin b → ℕ) hij))
  obtain ⟨ev, hev⟩ := Equiv.Perm.exists_extending_pair newRow oldRow hNew hOld
  obtain ⟨eu, heu⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hna)
    (Fin.castLE hna ∘ e) (Fin.castLE_injective hna)
    ((Fin.castLE_injective hna).comp e.injective)
  have heuVal (j : Fin n) : (eu (Fin.castLE hna j) : ℕ) = (e j : ℕ) :=
    congrArg Fin.val (heu j)
  let α' (i : ℕ) := if hi : i < n then α (e ⟨i, hi⟩) else 0
  let β' (i : ℕ) := if hi : i < n then β (e ⟨i, hi⟩) else 0
  have ha' (i : Fin n) : α' i = α (e i) := dite_eq_left i.isLt
  have hb' (i : Fin n) : β' i = β (e i) := dite_eq_left i.isLt
  have hnonneg (i : ℕ) : 0 ≤ α' i ∧ 0 ≤ β' i := by
    by_cases hi : i < n
    · simpa only [α', β', dite_eq_left hi] using h.nonneg (e ⟨i, hi⟩)
    · simp [α', β', hi]
  have hanti : Antitone β' := by
    intro i j hij
    by_cases hj : j < n
    · have hi := lt_of_le_of_lt hij hj
      simpa only [β', dite_eq_left hi, dite_eq_left hj] using
        (he (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij))
    · simpa only [β', dite_eq_right hj] using (hnonneg i).2
  have htail (i : ℕ) (hi : min b n ≤ i) : β' i = 0 := by
    by_cases hin : i < n
    · rw [hb' (⟨i, hin⟩ : Fin n)]
      by_contra hn
      have hib : i < b := hlt ⟨⟨i, hin⟩, hn⟩
      omega
    · exact dite_eq_right hin
  refine ⟨U.submatrix id eu, V.submatrix id ev, X.submatrix id e, α', β',
    submatrix_equiv_mem_unitaryGroup h.mem_unitaryGroup_left₁ (Equiv.refl _) eu,
    submatrix_equiv_mem_unitaryGroup h.mem_unitaryGroup_left₂ (Equiv.refl _) ev,
    (isUnit_submatrix_equiv (Equiv.refl _) e).2 h.isUnit, hnonneg, hanti, htail, ?_, ?_, ?_⟩
  · have hm := submatrix_mul_equiv Uᴴ A eu (Equiv.refl _) id
    have hm' := submatrix_mul_equiv (Uᴴ * A) X eu (Equiv.refl _) e
    simp only [Equiv.coe_refl, submatrix_id_id] at hm hm'
    rw [conjTranspose_submatrix, hm, hm',
      ← star_eq_conjTranspose, h.star_mul_mul₁]
    ext i j
    have hmatch : (eu i : ℕ) = (e j : ℕ) ↔ (i : ℕ) = (j : ℕ) := by
      rw [← heuVal j, Fin.val_inj, eu.injective.eq_iff]
      exact Fin.val_inj.symm
    rw [submatrix_apply, rectDiagonal_apply, rectDiagonal_apply]
    by_cases hij : (i : ℕ) = (j : ℕ)
    · simp only [ite_eq_left (hmatch.mpr hij), ite_eq_left hij]
      exact congrArg (fun k : ℕ => (α k : ℂ)) (hmatch.mpr hij) |>.trans
        (congrArg Complex.ofReal (show α (e j) = α' i.val by rw [hij, ha' j]))
    · simp only [ite_eq_right (hmatch.not.mpr hij), ite_eq_right hij]
  · have hm := submatrix_mul_equiv Vᴴ B ev (Equiv.refl _) id
    have hm' := submatrix_mul_equiv (Vᴴ * B) X ev (Equiv.refl _) e
    simp only [Equiv.coe_refl, submatrix_id_id] at hm hm'
    rw [conjTranspose_submatrix, hm, hm',
      ← star_eq_conjTranspose, h.star_mul_mul₂]
    ext i j
    rw [submatrix_apply, shiftedRectDiagonal_apply, rectDiagonal_apply]
    by_cases hj : β (e j) = 0
    · by_cases hij : (i : ℕ) = (j : ℕ)
      · rw [ite_eq_left hij, hij, hb' j, hj]
        simp
      · simp [hj, hij]
    · let j' : J := ⟨j, hj⟩
      have hrow : (ev (newRow j') : ℕ) = (e j : ℕ) - p :=
        congrArg Fin.val (hev j')
      have hmatch : (e j : ℕ) = (ev i : ℕ) + p ↔ (i : ℕ) = (j : ℕ) := by
        have hpj := (hp hj).1
        have hE : (e j : ℕ) = (ev (newRow j') : ℕ) + p := by omega
        change (e j : ℕ) = (ev i : ℕ) + p ↔ (i : ℕ) = (newRow j' : ℕ)
        rw [hE, Nat.add_right_cancel_iff, Fin.val_inj, ev.injective.eq_iff, eq_comm]
        exact Fin.val_inj.symm
      change (if (e j : ℕ) = (ev i : ℕ) + p then (β (e j) : ℂ) else 0) = _
      by_cases hij : (i : ℕ) = (j : ℕ)
      · simp only [ite_eq_left (hmatch.mpr hij), ite_eq_left hij]
        rw [hij, hb' j]
      · simp only [ite_eq_right (hmatch.not.mpr hij), ite_eq_right hij]
  · rw [bSingularValues_eq_of_isGSVD h hna]
    split_ifs
    · rfl
    · ext μ
      change (∃ i : Fin n, β i ≠ 0 ∧ μ = α i / β i) ↔
        (∃ i : Fin n, β' i ≠ 0 ∧ μ = α' i / β' i)
      simp only [ha', hb']
      exact e.surjective.exists

/-- **Remark 1(b)** of [benIsrael2003generalized], Chapter 6.
The size hypothesis matters for unshifted simultaneous rectangular diagonals.
Both diagonals would send the second coordinate vector to zero in this pair. -/
theorem remark_6_1b :
    ¬ ∃ (U V : Matrix (Fin 1) (Fin 1) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ)
      (α β : ℕ → ℂ),
      U ∈ unitaryGroup (Fin 1) ℂ ∧ V ∈ unitaryGroup (Fin 1) ℂ ∧ IsUnit X ∧
      Uᴴ * (!![1, 0] : Matrix (Fin 1) (Fin 2) ℂ) * X = rectDiagonal α ∧
      Vᴴ * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℂ) * X = rectDiagonal β := by
  rintro ⟨U, V, X, α, β, hu, hv, hx, ha, hb⟩
  let e : Fin 2 → ℂ := Pi.single 1 1
  have he : e ≠ 0 := by
    intro h
    have h1 := congrFun h (1 : Fin 2)
    simp [e] at h1
  have hd (d : ℕ → ℂ) : (rectDiagonal d : Matrix (Fin 1) (Fin 2) ℂ) *ᵥ e = 0 := by
    ext i
    fin_cases i
    simp [mulVec, dotProduct, Fin.sum_univ_two, e, rectDiagonal_apply]
  have hk {R : Matrix (Fin 1) (Fin 2) ℂ} {P : Matrix (Fin 1) (Fin 1) ℂ}
      {d : ℕ → ℂ} (hp : P ∈ unitaryGroup (Fin 1) ℂ) (h : Pᴴ * R * X = rectDiagonal d) :
      R *ᵥ (X *ᵥ e) = 0 := by
    have hR : R * X = P * rectDiagonal d := by
      rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mul_conjTranspose_self_of_mem_unitaryGroup hp, Matrix.one_mul]
    rw [mulVec_mulVec, hR, ← mulVec_mulVec, hd, mulVec_zero]
  have hzero : X *ᵥ e = 0 := by
    have h0 := congrFun (hk hu ha) (0 : Fin 1)
    have h1 := congrFun (hk hv hb) (0 : Fin 1)
    ext j
    fin_cases j
    · simpa [mulVec, dotProduct, Fin.sum_univ_two] using h0
    · simpa [mulVec, dotProduct, Fin.sum_univ_two] using h1
  exact he (mulVec_injective_of_isUnit hx (hzero.trans (mulVec_zero X).symm))

end GeneralizedSVD

section WeightedSVD

open scoped InnerProductSpace ComplexOrder MatrixOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private noncomputable def quadraticForm (P : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℝ :=
  Complex.re ⟪P.toEuclideanLin x, x⟫_ℂ

/-- The squared weighted norm quotient in **Equation (193)** of
[benIsrael2003generalized], Chapter 6. -/
noncomputable def weightedSquaredQuotient (A : Matrix m n ℂ) (W : Matrix m m ℂ)
    (Q : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℝ :=
  quadraticForm (Aᴴ * W * A) x / quadraticForm Q x

/-- **Definition 8**, Equation (193) of [benIsrael2003generalized], Chapter 6.
The nonnegative square roots of stationary values of the squared weighted
norm quotient on the nonzero vectors. The derivative is real. -/
def weightedSingularValues (A : Matrix m n ℂ) (W : Matrix m m ℂ)
    (Q : Matrix n n ℂ) : Set ℝ :=
  {μ | 0 ≤ μ ∧ ∃ x : EuclideanSpace ℂ n, x ≠ 0 ∧
    weightedSquaredQuotient A W Q x = μ ^ 2 ∧
    HasFDerivAt (𝕜 := ℝ) (weightedSquaredQuotient A W Q) 0 x}

/-- **Definition 9** of [benIsrael2003generalized], Chapter 6.
A square matrix is `Q`-orthogonal when its columns have Gram matrix `1`
in the inner product for `Q`. -/
def IsWeightOrthogonal (Q V : Matrix n n ℂ) : Prop :=
  Vᴴ * Q * V = 1

/-- **Definition 9** of [benIsrael2003generalized], Chapter 6.
A square matrix with an identity weighted Gram matrix is invertible. -/
theorem IsWeightOrthogonal.isUnit {Q V : Matrix n n ℂ} (h : IsWeightOrthogonal Q V) :
    IsUnit V :=
  (isUnit_iff_isUnit_det V).mpr (isUnit_det_of_left_inverse (show Vᴴ * Q * V = 1 from h))

private theorem quadraticForm_pos {Q : Matrix n n ℂ}
    (hQ : Q.PosDef) {x : EuclideanSpace ℂ n} (hx : x ≠ 0) : 0 < quadraticForm Q x := by
  have hx' : x.ofLp ≠ 0 := fun h => hx ((WithLp.equiv 2 _).injective h)
  change 0 < RCLike.re ⟪Q.toEuclideanLin x, x⟫_ℂ
  rw [inner_re_symm]
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm (Q *ᵥ x.ofLp)] using hQ.re_dotProduct_pos hx'

private theorem hasFDerivAt_quadraticForm {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (x : EuclideanSpace ℂ n) :
    let : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
    HasFDerivAt (quadraticForm P) (2 • innerSL ℝ (P.toEuclideanLin x)) x := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  let T := P.toEuclideanLin.toContinuousLinearMap.restrictScalars ℝ
  have hs : (T : EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n).IsSymmetric :=
    (isSymmetric_toEuclideanLin_iff.mpr hP).restrictScalars
  exact (hs.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt

omit [DecidableEq m] in
private theorem weighted_stationary_iff {A : Matrix m n ℂ} {W : Matrix m m ℂ}
    {Q : Matrix n n ℂ} (hW : W.IsHermitian) (hQ : Q.PosDef)
    {x : EuclideanSpace ℂ n} (hx : x ≠ 0) {t : ℝ} :
    weightedSquaredQuotient A W Q x = t ∧
      HasFDerivAt (𝕜 := ℝ) (weightedSquaredQuotient A W Q) 0 x ↔
      (Aᴴ * W * A).toEuclideanLin x = t • Q.toEuclideanLin x := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ n) := InnerProductSpace.complexToReal
  let P := Aᴴ * W * A
  have hP : P.IsHermitian := by
    change Pᴴ = P
    simp [P, conjTranspose_mul, hW.eq, Matrix.mul_assoc]
  have hq : quadraticForm Q x ≠ 0 := (quadraticForm_pos hQ hx).ne'
  have hder : HasFDerivAt (𝕜 := ℝ) (weightedSquaredQuotient A W Q)
      ((quadraticForm Q x ^ 2)⁻¹ •
        (quadraticForm Q x • (2 • innerSL ℝ (P.toEuclideanLin x)) -
          quadraticForm P x • (2 • innerSL ℝ (Q.toEuclideanLin x)))) x := by
    have hp' := hasFDerivAt_quadraticForm hP x
    have hq' := hasFDerivAt_quadraticForm hQ.isHermitian x
    convert hp'.mul ((hasFDerivAt_inv hq).comp x hq') using 1
    · ext y
      exact div_eq_mul_inv _ _
    · ext y
      simp only [smul_apply, sub_apply, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, mul_comm, smul_eq_mul,
        innerSL_apply_apply, two_nsmul, Function.comp_apply]
      field_simp
      ring
  have heval : weightedSquaredQuotient A W Q x = t ↔
      quadraticForm P x = t * quadraticForm Q x := div_eq_iff hq
  have hder0 (ht : quadraticForm P x = t * quadraticForm Q x) :
      HasFDerivAt (𝕜 := ℝ) (weightedSquaredQuotient A W Q) 0 x ↔
        P.toEuclideanLin x = t • Q.toEuclideanLin x := by
    have hcalc :
        (quadraticForm Q x • (2 • innerSL ℝ (P.toEuclideanLin x)) -
          quadraticForm P x • (2 • innerSL ℝ (Q.toEuclideanLin x))) =
          (quadraticForm Q x * 2) •
            innerSL ℝ (P.toEuclideanLin x - t • Q.toEuclideanLin x) := by
      rw [ht, map_sub, map_smul, smul_sub]
      simp only [smul_smul, two_nsmul]
      module
    have hz :
        (quadraticForm Q x • (2 • innerSL ℝ (P.toEuclideanLin x)) -
          quadraticForm P x • (2 • innerSL ℝ (Q.toEuclideanLin x))) = 0 ↔
          P.toEuclideanLin x = t • Q.toEuclideanLin x := by
      rw [hcalc, smul_eq_zero, or_iff_right (mul_ne_zero hq two_ne_zero)]
      change InnerProductSpace.toDualMap ℝ _ (P.toEuclideanLin x - t • Q.toEuclideanLin x) = 0 ↔ _
      rw [map_eq_zero_iff _ (InnerProductSpace.toDualMap ℝ _).injective, sub_eq_zero]
    constructor
    · intro hzero
      have hh := hder.unique hzero
      exact hz.mp ((smul_eq_zero.mp hh).resolve_left
        (inv_ne_zero (pow_ne_zero 2 hq)))
    · intro heq
      have hh := hz.mpr heq
      simpa only [hh, smul_zero] using hder
  constructor
  · rintro ⟨ht, hd⟩
    exact (hder0 (heval.mp ht)).mp hd
  · intro heq
    have ht : quadraticForm P x = t * quadraticForm Q x := by
      change ⟪(Aᴴ * W * A).toEuclideanLin x, x⟫_ℝ =
        t * ⟪Q.toEuclideanLin x, x⟫_ℝ
      rw [heq, real_inner_smul_left]
    exact ⟨heval.mpr ht, (hder0 ht).mpr heq⟩

omit [DecidableEq m] in
/-- **Theorem 22**, stationary-point condition in the proof of
[benIsrael2003generalized], Chapter 6. The weighted singular values are the
nonnegative roots of the weighted Gram pencil. -/
theorem mem_weightedSingularValues_iff_det {A : Matrix m n ℂ} {W : Matrix m m ℂ}
    {Q : Matrix n n ℂ} (hW : W.PosDef) (hQ : Q.PosDef) {μ : ℝ} :
    μ ∈ weightedSingularValues A W Q ↔
      0 ≤ μ ∧ (Aᴴ * W * A - (μ ^ 2 : ℝ) • Q).det = 0 := by
  change (0 ≤ μ ∧ _) ↔ _
  rw [← exists_mulVec_eq_zero_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨x, hx, hv, hd⟩
    have he := (weighted_stationary_iff hW.isHermitian hQ hx).mp ⟨hv, hd⟩
    refine ⟨x.ofLp, fun h => hx ((WithLp.equiv 2 _).injective h), ?_⟩
    apply sub_eq_zero.mpr at he
    simpa only [ofLp_toLpLin, Matrix.toLin'_apply, sub_mulVec, smul_mulVec, WithLp.ofLp_sub,
      WithLp.ofLp_smul, WithLp.ofLp_zero] using congrArg WithLp.ofLp he
  · rintro ⟨x, hx, he⟩
    let y : EuclideanSpace ℂ n := WithLp.toLp 2 x
    have hy : y ≠ 0 := fun h => hx (congrArg WithLp.ofLp h)
    refine ⟨y, hy, (weighted_stationary_iff hW.isHermitian hQ hy).mpr ?_⟩
    apply (WithLp.equiv 2 _).injective
    change ((Aᴴ * W * A).toEuclideanLin y).ofLp = ((μ ^ 2 : ℝ) • Q.toEuclideanLin y).ofLp
    exact sub_eq_zero.mp (by simpa only [ofLp_toLpLin, Matrix.toLin'_apply, sub_mulVec,
      smul_mulVec, WithLp.ofLp_smul, WithLp.ofLp_toLp, y] using he)

end WeightedSVD

section WeightedFactorization

open scoped ComplexOrder MatrixOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem sqrt_weight {P : Matrix n n ℂ} (hP : P.PosDef) :
    (CFC.sqrt P)ᴴ * CFC.sqrt P = P ∧ IsUnit (CFC.sqrt P) := by
  have h := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hs : (CFC.sqrt P)ᴴ = CFC.sqrt P := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  exact ⟨by rw [hs, h], isUnit_of_mul_isUnit_left (h.symm ▸ hP.isUnit)⟩

/-- **Equation (196)** of [benIsrael2003generalized], Chapter 6.
An ordinary unitary factor becomes weight-orthogonal after scaling by
the inverse of the positive square root of the weight. -/
theorem isWeightOrthogonal_inv_sqrt_mul {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U ∈ unitaryGroup n ℂ) : IsWeightOrthogonal P ((CFC.sqrt P)⁻¹ * U) := by
  obtain ⟨hG, hu⟩ := sqrt_weight hP
  let S := CFC.sqrt P
  change Sᴴ * S = P at hG
  change (S⁻¹ * U)ᴴ * P * (S⁻¹ * U) = 1
  have hSU : S * (S⁻¹ * U) = U := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv S ((isUnit_iff_isUnit_det S).mp hu), one_mul]
  calc
    _ = (S * (S⁻¹ * U))ᴴ * (S * (S⁻¹ * U)) := by
      rw [← hG]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hSU, conjTranspose_mul_self_of_mem_unitaryGroup hU]

/-- **Theorem 22**, determinant reduction in [benIsrael2003generalized], Chapter 6.
In weight-orthogonal coordinates the weighted pencil determinant is the
Gram pencil determinant times the domain weight determinant. -/
theorem det_weightedPencil_eq {A D : Matrix m n ℂ} {W U : Matrix m m ℂ}
    {Q V : Matrix n n ℂ} (hU : IsWeightOrthogonal W U) (hV : IsWeightOrthogonal Q V)
    (hD : A * V = U * D) (μ : ℝ) :
    (Aᴴ * W * A - (μ ^ 2 : ℝ) • Q).det =
      Q.det * (Dᴴ * D - (μ ^ 2 : ℝ) • (1 : Matrix n n ℂ)).det := by
  have hg : Vᴴ * (Aᴴ * W * A) * V = Dᴴ * D := by
    calc
      _ = (A * V)ᴴ * W * (A * V) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Dᴴ * (Uᴴ * W * U) * D := by rw [hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Dᴴ * D := by rw [show Uᴴ * W * U = 1 from hU, Matrix.mul_one]
  have hq : Vᴴ * Q * V = 1 := hV
  let M := Aᴴ * W * A - (μ ^ 2 : ℝ) • Q
  have he : Vᴴ * M * V = Dᴴ * D - (μ ^ 2 : ℝ) • (1 : Matrix n n ℂ) := by
    dsimp only [M]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hg, hq]
  have hv : Vᴴ.det * Q.det * V.det = 1 := by
    simpa only [det_mul, det_one] using congrArg det hq
  change M.det = _
  calc
    M.det = (Vᴴ.det * Q.det * V.det) * M.det := by rw [hv, one_mul]
    _ = Q.det * (Vᴴ * M * V).det := by rw [det_mul, det_mul]; ring
    _ = _ := by rw [he]

omit [DecidableEq m] in
/-- **Remark 1(a)** of [benIsrael2003generalized], Chapter 6.
For nonsingular `B`, the generalized singular values are the Gram-pencil
roots of `A * B⁻¹` against the identity. -/
theorem bSingularValues_eq_mul_inv {A : Matrix m n ℂ} {B : Matrix n n ℂ} (hB : IsUnit B) :
    bSingularValues A B = bSingularValues (A * B⁻¹) (1 : Matrix n n ℂ) := by
  classical
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv B ((isUnit_iff_isUnit_det B).mp hB)
  have hV : IsWeightOrthogonal (Bᴴ * B) B⁻¹ := by
    change B⁻¹ᴴ * (Bᴴ * B) * B⁻¹ = 1
    calc
      _ = (B * B⁻¹)ᴴ * (B * B⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, conjTranspose_one, Matrix.one_mul]
  have hU : IsWeightOrthogonal (1 : Matrix m m ℂ) 1 := by simp [IsWeightOrthogonal]
  have hD : A * B⁻¹ = (1 : Matrix m m ℂ) * (A * B⁻¹) := (Matrix.one_mul _).symm
  have hC : (Bᴴ * B).det ≠ 0 := by
    rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.mpr ((isUnit_iff_isUnit_det B).mp hB).ne_zero)
      ((isUnit_iff_isUnit_det B).mp hB).ne_zero
  ext μ
  have h := det_weightedPencil_eq hU hV hD μ
  rw [Matrix.mul_one] at h
  simp only [bSingularValues, Set.mem_ofPred_eq, conjTranspose_one, Matrix.one_mul,
    h, mul_eq_zero, or_iff_right hC]

open scoped InnerProductSpace in
private theorem quadraticForm_weighted_gram (M : Matrix m n ℂ) {P : Matrix m m ℂ}
    (hP : P.PosDef) (x : EuclideanSpace ℂ n) :
    quadraticForm (Mᴴ * P * M) x = ‖(CFC.sqrt P).toEuclideanLin (M.toEuclideanLin x)‖ ^ 2 := by
  let N := CFC.sqrt P * M
  have hN : Nᴴ * N = Mᴴ * P * M := by
    calc
      _ = Mᴴ * ((CFC.sqrt P)ᴴ * CFC.sqrt P) * M := by
        simp only [N, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [(sqrt_weight hP).1]
  rw [← hN, quadraticForm, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left,
    inner_self_eq_norm_sq_to_K]
  change RCLike.re ((RCLike.ofReal ‖N.toEuclideanLin x‖ : ℂ) ^ 2) = _
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [show N = CFC.sqrt P * M from rfl, toEuclideanLin_mul_apply]

/-- **Equation (193)** of [benIsrael2003generalized], Chapter 6.
The squared quotient agrees with the quotient of squared Euclidean
norms after applying the positive square roots of the two weights. -/
theorem weightedSquaredQuotient_eq_norm_sq {A : Matrix m n ℂ} {W : Matrix m m ℂ}
    {Q : Matrix n n ℂ} (hW : W.PosDef) (hQ : Q.PosDef) (x : EuclideanSpace ℂ n) :
    weightedSquaredQuotient A W Q x =
      ‖(CFC.sqrt W).toEuclideanLin (A.toEuclideanLin x)‖ ^ 2 /
        ‖(CFC.sqrt Q).toEuclideanLin x‖ ^ 2 := by
  unfold weightedSquaredQuotient
  rw [quadraticForm_weighted_gram A hW x]
  have h := quadraticForm_weighted_gram (1 : Matrix n n ℂ) hQ x
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one, toEuclideanLin_one_apply] at h
  rw [h]

variable {a b : ℕ}

/-- **Theorem 22**, Equations (194)–(196) of [benIsrael2003generalized], Chapter 6.
Positive definite domain and codomain weights admit a weighted SVD.
Its coefficients, padded to the number of columns, are exactly the
stationary weighted singular values. -/
theorem theorem_6_22 (A : Matrix (Fin a) (Fin b) ℂ) {W : Matrix (Fin a) (Fin a) ℂ}
    {Q : Matrix (Fin b) (Fin b) ℂ} (hW : W.PosDef) (hQ : Q.PosDef) :
    ∃ (U : Matrix (Fin a) (Fin a) ℂ) (V : Matrix (Fin b) (Fin b) ℂ) (σ : ℕ → ℝ),
      IsWeightOrthogonal W U ∧ IsWeightOrthogonal Q V ∧
      (∀ i, 0 ≤ σ i) ∧ Antitone σ ∧
      (∀ i, min a b ≤ i → σ i = 0) ∧
      U⁻¹ * A * V = rectDiagonal (fun i => ((σ i : ℝ) : ℂ)) ∧
      weightedSingularValues A W Q = Set.range (fun i : Fin b => σ i) ∧
      ∀ μ : ℝ, (Aᴴ * W * A - (μ ^ 2 : ℝ) • Q).det =
        Q.det * ∏ i : Fin b, ((σ i ^ 2 - μ ^ 2 : ℝ) : ℂ) := by
  classical
  let S := CFC.sqrt W
  let T := CFC.sqrt Q
  let B := S * A * T⁻¹
  obtain ⟨U₀, hU₀, V₀, hV₀, hD⟩ := B.exists_svd
  let U := S⁻¹ * U₀
  let V := T⁻¹ * V₀
  let σ := B.sortedSingularValues
  let D : Matrix (Fin a) (Fin b) ℂ := rectDiagonal (fun i => ((σ i : ℝ) : ℂ))
  change star U₀ * B * V₀ = D at hD
  have hu := isWeightOrthogonal_inv_sqrt_mul hW hU₀
  have hv := isWeightOrthogonal_inv_sqrt_mul hQ hV₀
  have hdS := (isUnit_iff_isUnit_det S).mp (sqrt_weight hW).2
  have hSU : S * U = U₀ := by rw [show U = S⁻¹ * U₀ from rfl, ← Matrix.mul_assoc,
    mul_nonsing_inv S hdS, one_mul]
  have huinv : U⁻¹ = U₀ᴴ * S := by
    apply inv_eq_left_inv
    rw [Matrix.mul_assoc, hSU, conjTranspose_mul_self_of_mem_unitaryGroup hU₀]
  have hDA : U⁻¹ * A * V = D := by
    rw [huinv]
    simpa only [B, V, star_eq_conjTranspose, Matrix.mul_assoc] using hD
  have hAV : A * V = U * D := by
    have hud := (isUnit_iff_isUnit_det U).mp hu.isUnit
    calc
      A * V = U * (U⁻¹ * A * V) := by
        simp only [← Matrix.mul_assoc, mul_nonsing_inv U hud, Matrix.one_mul]
      _ = U * D := by rw [hDA]
  have hrank : B.rank ≤ min a b := by
    exact le_min (by simpa using rank_le_card_height B) (by simpa using rank_le_card_width B)
  have htail (i : ℕ) (hi : min a b ≤ i) : σ i = 0 :=
    (B.sortedSingularValues_eq_zero_iff_rank_le i).mpr (hrank.trans hi)
  have hGram : Dᴴ * D = diagonal (fun i : Fin b => ((σ i ^ 2 : ℝ) : ℂ)) := by
    change (rectDiagonal (fun i => ((σ i : ℝ) : ℂ)) : Matrix (Fin a) (Fin b) ℂ)ᴴ *
      rectDiagonal (fun i => ((σ i : ℝ) : ℂ)) = _
    rw [conjTranspose_rectDiagonal_mul_self]
    congr 1
    funext i
    by_cases hi : (i : ℕ) < a
    · simp [hi, pow_two]
    · simp [hi, htail i (le_trans (min_le_left _ _) (le_of_not_gt hi))]
  have hdet (μ : ℝ) : (Aᴴ * W * A - (μ ^ 2 : ℝ) • Q).det =
      Q.det * ∏ i : Fin b, ((σ i ^ 2 - μ ^ 2 : ℝ) : ℂ) := by
    rw [det_weightedPencil_eq hu hv hAV, hGram]
    congr 1
    rw [← det_diagonal]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  refine ⟨U, V, σ, hu, hv, B.sortedSingularValues_nonneg, B.sortedSingularValues_antitone,
    htail, hDA, ?_, hdet⟩
  ext μ
  rw [mem_weightedSingularValues_iff_det hW hQ, hdet μ, mul_eq_zero,
    or_iff_right (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det Q).mp hQ.isUnit)),
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Complex.ofReal_eq_zero, sub_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨hμ, i, hi⟩
    refine ⟨i, ?_⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with he | he
    · exact he
    · linarith [B.sortedSingularValues_nonneg i]
  · rintro ⟨i, rfl⟩
    exact ⟨B.sortedSingularValues_nonneg i, ⟨i, rfl⟩⟩

private theorem sqrt_mul_mem_unitaryGroup {P U : Matrix n n ℂ}
    (hP : P.PosDef) (hU : IsWeightOrthogonal P U) :
    CFC.sqrt P * U ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_assoc Uᴴ, (sqrt_weight hP).1]
  exact hU

/-- **Exercise 93**, Equation (201) of [benIsrael2003generalized], Chapter 6.
The weighted SVD least-squares operator agrees with the operator obtained
by reducing the weighted problem to Euclidean coordinates. -/
theorem exercise_6_93_operator {A : Matrix (Fin a) (Fin b) ℂ}
    {W U : Matrix (Fin a) (Fin a) ℂ} {Q V : Matrix (Fin b) (Fin b) ℂ}
    {σ : ℕ → ℂ} (hW : W.PosDef) (hQ : Q.PosDef)
    (hU : IsWeightOrthogonal W U) (hV : IsWeightOrthogonal Q V)
    (hD : U⁻¹ * A * V = rectDiagonal σ) :
    V * (rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ).pinv * U⁻¹ =
      (CFC.sqrt Q)⁻¹ * (CFC.sqrt W * A * (CFC.sqrt Q)⁻¹).pinv * CFC.sqrt W := by
  let S := CFC.sqrt W
  let T := CFC.sqrt Q
  let U₀ := S * U
  let V₀ := T * V
  have hU₀ : U₀ ∈ unitaryGroup (Fin a) ℂ := sqrt_mul_mem_unitaryGroup hW hU
  have hV₀ : V₀ ∈ unitaryGroup (Fin b) ℂ := sqrt_mul_mem_unitaryGroup hQ hV
  have ht := (isUnit_iff_isUnit_det T).mp (sqrt_weight hQ).2
  have hr : T⁻¹ * V₀ = V := by
    change T⁻¹ * (T * V) = V
    rw [← Matrix.mul_assoc, nonsing_inv_mul T ht, one_mul]
  have hl : star U₀ * S = U⁻¹ := by
    symm
    apply inv_eq_left_inv
    rw [Matrix.mul_assoc]
    exact mem_unitaryGroup_iff'.mp hU₀
  have hB : star U₀ * (S * A * T⁻¹) * V₀ = rectDiagonal σ := by
    calc
      _ = (star U₀ * S) * A * (T⁻¹ * V₀) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, hr, hD]
  have hp : (rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ).pinv =
      (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin b) (Fin a) ℂ) := by
    have hI : star (1 : Matrix (Fin a) (Fin a) ℂ) *
        (rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ) * (1 : Matrix (Fin b) (Fin b) ℂ) =
        rectDiagonal σ := by simp
    simpa using pinv_eq_of_svd (one_mem (unitaryGroup (Fin a) ℂ))
      (one_mem (unitaryGroup (Fin b) ℂ)) hI
  change _ = T⁻¹ * (S * A * T⁻¹).pinv * S
  rw [pinv_eq_of_svd hU₀ hV₀ hB, hp]
  nth_rw 1 [← hr, ← hl]
  simp only [Matrix.mul_assoc]

open scoped InnerProductSpace in
/-- **Exercise 93** of [benIsrael2003generalized], Chapter 6.
Among the vectors minimizing the residual weighted by `W`, this vector
uniquely minimizes the solution norm weighted by `Q`. -/
theorem exercise_6_93 {A : Matrix (Fin a) (Fin b) ℂ}
    {W U : Matrix (Fin a) (Fin a) ℂ} {Q V : Matrix (Fin b) (Fin b) ℂ}
    {σ : ℕ → ℂ} (hW : W.PosDef) (hQ : Q.PosDef)
    (hU : IsWeightOrthogonal W U) (hV : IsWeightOrthogonal Q V)
    (hD : U⁻¹ * A * V = rectDiagonal σ) (c : EuclideanSpace ℂ (Fin a)) :
    let residual (x : EuclideanSpace ℂ (Fin b)) :=
      ‖(CFC.sqrt W).toEuclideanLin (A.toEuclideanLin x - c)‖
    let solutionNorm (x : EuclideanSpace ℂ (Fin b)) := ‖(CFC.sqrt Q).toEuclideanLin x‖
    ∀ x, ((∀ y, residual x ≤ residual y) ∧
      (∀ y, (∀ z, residual y ≤ residual z) → solutionNorm x ≤ solutionNorm y)) ↔
      x = (V * (rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ).pinv * U⁻¹).toEuclideanLin c := by
  let S := CFC.sqrt W
  let T := CFC.sqrt Q
  let B := S * A * T⁻¹
  let c₀ := S.toEuclideanLin c
  have ht := (sqrt_weight hQ).2
  let f := T.toEuclideanLin
  have hfx (x : EuclideanSpace ℂ (Fin b)) : f x = T.toEuclideanLin x := rfl
  have hSurj : Function.Surjective f :=
    fun y => ⟨T⁻¹.toEuclideanLin y, toEuclideanLin_mul_nonsing_inv_apply ht y⟩
  have hInj : Function.Injective f :=
    (show Function.LeftInverse T⁻¹.toEuclideanLin f from
      toEuclideanLin_nonsing_inv_mul_apply ht).injective
  have hr (x : EuclideanSpace ℂ (Fin b)) :
      B.toEuclideanLin (f x) - c₀ = S.toEuclideanLin (A.toEuclideanLin x - c) := by
    rw [hfx, ← toEuclideanLin_mul_apply]
    have hBT : B * T = S * A := by
      change S * A * T⁻¹ * T = S * A
      exact nonsing_inv_mul_cancel_right T (S * A) ((isUnit_iff_isUnit_det T).mp ht)
    rw [hBT, toEuclideanLin_mul_apply, map_sub]
  have hls (x : EuclideanSpace ℂ (Fin b)) :
      (∀ y, ‖S.toEuclideanLin (A.toEuclideanLin x - c)‖ ≤
        ‖S.toEuclideanLin (A.toEuclideanLin y - c)‖) ↔
        IsLeastSquaresSolution B c₀ (f x) := by
    simp only [← hr, IsLeastSquaresSolution]
    constructor
    · intro h y
      obtain ⟨z, rfl⟩ := hSurj y
      exact h z
    · exact fun h y => h (f y)
  dsimp only
  intro x
  rw [exercise_6_93_operator hW hQ hU hV hD]
  have hsol (x : EuclideanSpace ℂ (Fin b)) : f x = B.pinv.toEuclideanLin c₀ ↔
      x = (T⁻¹ * B.pinv * S).toEuclideanLin c := by
    have hval : f ((T⁻¹ * B.pinv * S).toEuclideanLin c) = B.pinv.toEuclideanLin c₀ := by
      rw [hfx, ← toEuclideanLin_mul_apply]
      have hTB : T * (T⁻¹ * B.pinv * S) = B.pinv * S := by
        simp only [← Matrix.mul_assoc,
          mul_nonsing_inv T ((isUnit_iff_isUnit_det T).mp ht), Matrix.one_mul]
      rw [hTB, toEuclideanLin_mul_apply]
    rw [← hval]
    exact hInj.eq_iff
  rw [← hsol]
  change ((∀ y, ‖S.toEuclideanLin (A.toEuclideanLin x - c)‖ ≤
      ‖S.toEuclideanLin (A.toEuclideanLin y - c)‖) ∧
    (∀ y, (∀ z, ‖S.toEuclideanLin (A.toEuclideanLin y - c)‖ ≤
      ‖S.toEuclideanLin (A.toEuclideanLin z - c)‖) → ‖f x‖ ≤ ‖f y‖)) ↔ _
  simp only [hls]
  constructor
  · rintro ⟨hx, hmin⟩
    apply IsMinNormLeastSquaresSolution.eq_pinv (A := B) (b := c₀)
    refine ⟨hx, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := hSurj y
    exact hmin z hy
  · intro hx
    have hp := isMinNormLeastSquaresSolution_pinv B c₀
    rw [← hx] at hp
    exact ⟨hp.1, fun y hy => hp.2 (f y) hy⟩

end WeightedFactorization

end BenIsraelGreville.Chapter06
