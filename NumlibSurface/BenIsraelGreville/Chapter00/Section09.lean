/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.PerronFrobenius

/-!
# Nonnegative matrices

Section 0.9 of [benIsrael2003generalized] defines block reducibility and states
the Perron–Frobenius theorem for an irreducible nonnegative matrix.

## Deviations from the source

* **Theorem 5(a)** (correction). The positive spectral radius requires at
  least two indices or a nonzero matrix. The zero matrix of size one is
  irreducible under the definition by nonempty blocks.
-/

namespace BenIsraelGreville.Chapter00

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Section 0.9(a)** of [benIsrael2003generalized]. A real matrix is
nonnegative if every entry is nonnegative. -/
abbrev isNonnegative (A : Matrix n n ℝ) : Prop := A.EntrywiseNonneg

/-- **Section 0.9(b)** of [benIsrael2003generalized]. A matrix is reducible
when a nontrivial partition of the indices has a zero lower block. -/
def isReducible (A : Matrix n n ℝ) : Prop :=
  ∃ s : Set n, s.Nonempty ∧ sᶜ.Nonempty ∧ ∀ i ∉ s, ∀ j ∈ s, A i j = 0

omit [Fintype n] [DecidableEq n] in
/-- **Equation (135)** of [benIsrael2003generalized], Chapter 0. A reducible
matrix can be put in block upper triangular form by a single reindexing of its
rows and columns. Both diagonal blocks have positive size. -/
theorem isReducible_iff_blockTriangular [Finite n] (A : Matrix n n ℝ) :
    isReducible A ↔ ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ n)
      (B : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin p) (Fin q) ℝ)
      (D : Matrix (Fin q) (Fin q) ℝ),
      0 < p ∧ 0 < q ∧ A.submatrix e e = fromBlocks B C 0 D := by
  classical
  let := Fintype.ofFinite n
  constructor
  · rintro ⟨s, hs, hs', hz⟩
    have : Nonempty s := hs.to_subtype
    have : Nonempty (sᶜ : Set n) := hs'.to_subtype
    let p := Fintype.card s
    let q := Fintype.card (sᶜ : Set n)
    let e : Fin p ⊕ Fin q ≃ n := ((Fintype.equivFin s).symm.sumCongr
      (Fintype.equivFin (sᶜ : Set n)).symm).trans (Equiv.Set.sumCompl s)
    let N := A.submatrix e e
    have hN : N.toBlocks₂₁ = 0 := by
      ext i j
      exact hz _ ((Fintype.equivFin (sᶜ : Set n)).symm i).2 _ ((Fintype.equivFin s).symm j).2
    refine ⟨p, q, e, N.toBlocks₁₁, N.toBlocks₁₂, N.toBlocks₂₂,
      Fintype.card_pos, Fintype.card_pos, ?_⟩
    exact (fromBlocks_toBlocks N).symm.trans (by rw [hN])
  · rintro ⟨p, q, e, B, C, D, hp, hq, he⟩
    let s : Set n := Set.range (e ∘ Sum.inl)
    have hx (i : Fin q) : e (Sum.inr i) ∉ s := by
      rintro ⟨j, hj⟩
      exact Sum.inl_ne_inr (e.injective hj)
    refine ⟨s, ⟨e (Sum.inl ⟨0, hp⟩), ⟨⟨0, hp⟩, rfl⟩⟩,
      ⟨e (Sum.inr ⟨0, hq⟩), hx ⟨0, hq⟩⟩, ?_⟩
    rintro i hi _ ⟨j, rfl⟩
    obtain ⟨a | b, rfl⟩ := e.surjective i
    · exact (hi ⟨a, rfl⟩).elim
    · exact congrFun (congrFun he (Sum.inr b)) (Sum.inl j)

private theorem pow_apply_eq_zero_of_separating_set (A : Matrix n n ℝ) {s : Set n}
    (hz : ∀ i ∉ s, ∀ j ∈ s, A i j = 0) (k : ℕ) :
    ∀ i ∉ s, ∀ j ∈ s, (A ^ k) i j = 0 := by
  classical
  induction k with
  | zero =>
    intro i hi j hj
    have hne : i ≠ j := fun h => hi (h.symm ▸ hj)
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i hi j hj
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ∈ s
    · rw [hz i hi l hl, zero_mul]
    · rw [ih l hl j hj, mul_zero]

omit [Fintype n] [DecidableEq n] in
/-- On at least two indices, failure of block reducibility for a
nonnegative matrix is equivalent to irreducibility of its positive-entry graph. -/
theorem isIrreducible_iff [Finite n] [Nontrivial n] {A : Matrix n n ℝ} (hA : isNonnegative A) :
    A.IsIrreducible ↔ ¬isReducible A := by
  classical
  let := Fintype.ofFinite n
  rw [Matrix.isIrreducible_iff_exists_pow_pos hA]
  constructor
  · rintro h ⟨s, ⟨j, hj⟩, ⟨i, hi⟩, hz⟩
    obtain ⟨k, _, hk⟩ := h i j
    rw [pow_apply_eq_zero_of_separating_set A hz k i hi j hj] at hk
    exact (lt_irrefl 0) hk
  · intro h
    have hReach (i j : n) : ∃ k : ℕ, 0 < (A ^ k) i j := by
      by_contra! hn
      let s : Set n := {l | ∃ k : ℕ, 0 < (A ^ k) l j}
      have hj : j ∈ s := ⟨0, by simp⟩
      have hi : i ∉ s := fun ⟨k, hk⟩ => (not_lt_of_ge (hn k)) hk
      apply h
      refine ⟨s, ⟨j, hj⟩, ⟨i, hi⟩, ?_⟩
      rintro l hl t ⟨k, hk⟩
      refine le_antisymm (not_lt.mp fun hlt => hl ⟨k + 1, ?_⟩) (hA l t)
      rw [pow_succ', Matrix.mul_apply]
      exact (Finset.sum_pos_iff_of_nonneg fun g _ =>
        mul_nonneg (hA l g) (Matrix.pow_apply_nonneg hA k g j)).mpr
        ⟨t, Finset.mem_univ t, mul_pos hlt hk⟩
    have hDifferent (i j : n) (hij : i ≠ j) : ∃ k > 0, 0 < (A ^ k) i j := by
      obtain ⟨k, hk⟩ := hReach i j
      exact ⟨k, Nat.pos_of_ne_zero (fun h0 => by simp [h0, Matrix.one_apply_ne hij] at hk), hk⟩
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · obtain ⟨t, ht⟩ := exists_ne i
      obtain ⟨k, hk, hkt⟩ := hDifferent i t ht.symm
      obtain ⟨l, _, hlt⟩ := hDifferent t i ht
      refine ⟨k + l, Nat.add_pos_left hk l, ?_⟩
      rw [pow_add, Matrix.mul_apply]
      exact (Finset.sum_pos_iff_of_nonneg fun g _ =>
        mul_nonneg (Matrix.pow_apply_nonneg hA k i g) (Matrix.pow_apply_nonneg hA l g i)).mpr
        ⟨t, Finset.mem_univ t, mul_pos hkt hlt⟩
    · exact hDifferent i j hij

private theorem subsingleton_eq_nonneg_diagonal [Subsingleton n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : isNonnegative A) :
    ∃ d : ℝ, 0 ≤ d ∧ A = diagonal (fun _ => d) ∧ (A.complexSpectralRadius).toReal = d := by
  obtain ⟨i⟩ := ‹Nonempty n›
  let d := A i i
  have hd : 0 ≤ d := hA i i
  have hAd : A = diagonal (fun _ => d) := by
    ext j k
    rw [Subsingleton.elim j i, Subsingleton.elim k i, diagonal_apply_eq]
  refine ⟨d, hd, hAd, ?_⟩
  rw [hAd, Matrix.complexSpectralRadius_diagonal, iSup_const]
  exact abs_of_nonneg hd

/-- **Theorem 5(a)** of [benIsrael2003generalized], Chapter 0. The spectral
radius of a nonnegative irreducible matrix of order at least two is
a positive eigenvalue. -/
theorem theorem_5_a [Nontrivial n] {A : Matrix n n ℝ}
    (hA : isNonnegative A) (hirr : ¬isReducible A) :
    0 < A.complexSpectralRadius.toReal ∧ A.complexSpectralRadius.toReal ∈ spectrum ℝ A := by
  have hi := (isIrreducible_iff hA).mpr hirr
  obtain ⟨x, hpos, hx⟩ := hi.exists_pos_hasEigenvector_complexSpectralRadius
  have hne : x ≠ 0 := by
    intro h
    obtain ⟨i⟩ := (inferInstance : Nonempty n)
    exact (hpos i).ne' (congrFun h i)
  refine ⟨hi.complexSpectralRadius_pos, ?_⟩
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hx, hne⟩

/-- **Theorem 5(a)** of [benIsrael2003generalized], Chapter 0. For positive
size, the spectral radius is a positive eigenvalue whenever the irreducible
nonnegative matrix is nonzero. -/
theorem theorem_5_a_of_ne_zero [Nonempty n] {A : Matrix n n ℝ}
    (hA : isNonnegative A) (hirr : ¬isReducible A) (hne : A ≠ 0) :
    0 < A.complexSpectralRadius.toReal ∧ A.complexSpectralRadius.toReal ∈ spectrum ℝ A := by
  rcases subsingleton_or_nontrivial n with hs | ht
  · obtain ⟨d, hd, hAd, hr⟩ := subsingleton_eq_nonneg_diagonal hA
    have hd0 : d ≠ 0 := fun hz => hne (by simp [hAd, hz])
    rw [hr, hAd, spectrum_diagonal]
    exact ⟨hd.lt_of_ne' hd0, ⟨Classical.arbitrary n, rfl⟩⟩
  · exact theorem_5_a hA hirr

/-- **Theorem 5(b)** of [benIsrael2003generalized], Chapter 0. The spectral
radius of a nonnegative irreducible matrix is an algebraically simple root. -/
theorem theorem_5_b [Nonempty n] {A : Matrix n n ℝ}
    (hA : isNonnegative A) (hirr : ¬isReducible A) :
    A.charpoly.rootMultiplicity A.complexSpectralRadius.toReal = 1 := by
  rcases subsingleton_or_nontrivial n with hs | ht
  · obtain ⟨d, _, hAd, hr⟩ := subsingleton_eq_nonneg_diagonal hA
    have hcard : Fintype.card n = 1 :=
      Fintype.card_eq_one_of_forall_eq (i := Classical.arbitrary n) fun _ => Subsingleton.elim _ _
    rw [hr, hAd, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
      hcard, pow_one]
    exact Polynomial.rootMultiplicity_X_sub_C_self
  · exact ((isIrreducible_iff hA).mpr hirr).rootMultiplicity_charpoly_complexSpectralRadius

omit [DecidableEq n] in
/-- **Theorem 5(c)** of [benIsrael2003generalized], Chapter 0. The spectral
radius of a nonnegative irreducible matrix has a positive eigenvector. -/
theorem theorem_5_c [Nonempty n] {A : Matrix n n ℝ}
    (hA : isNonnegative A) (hirr : ¬isReducible A) :
    ∃ x : n → ℝ, (∀ i, 0 < x i) ∧ A *ᵥ x = A.complexSpectralRadius.toReal • x := by
  classical
  rcases subsingleton_or_nontrivial n with hs | ht
  · obtain ⟨d, _, hAd, hr⟩ := subsingleton_eq_nonneg_diagonal hA
    refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
    funext i
    rw [hr, hAd, Matrix.mulVec_diagonal]
    rfl
  · exact ((isIrreducible_iff hA).mpr hirr).exists_pos_hasEigenvector_complexSpectralRadius

end BenIsraelGreville.Chapter00
