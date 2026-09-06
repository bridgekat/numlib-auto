import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# Saad §12.7.2: Winget regularization of element matrices

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §12.7.2.

The element-by-element preconditioners of the section start from the unassembled form
`A = ∑_e A^[e]` of a finite-element stiffness matrix, scale it by its own diagonal (12.24),
`Ã = D^{-1/2} A D^{-1/2}` with `D = diag(A)`, and then *regularize* each scaled element matrix by
forcing its diagonal to be the identity (12.25),

`Ā^[e] = I + Ã^[e] - diag(Ã^[e])`.

Saad asserts "these matrices are positive definite" and refers the reader to Exercise 8, which
asks *why* they are positive definite "when the matrix `Ã` is obtained from `A` by a diagonal
scaling".  `equation_12_25` is that exercise, under the hypotheses the sentence names: each scaled
element matrix is positive semidefinite (it is a congruence of an element stiffness matrix), the
assembled matrix `Ã = ∑_e Ã^[e]` is positive definite, and the scaling has made its diagonal the
identity — which is `diag_diagonalScaled` below.  None of the finite-element apparatus (the
connectivity matrices `P_e`, the element matrices `A_{K_e}`) is needed: what carries the proof is
that the diagonals of the summands add up to one.

The preconditioners themselves, (12.26)–(12.29), are definitions with no property claimed, and the
rest of §12.7 points back to §10.5 and to Chapter 8.
-/

open Matrix

namespace SaadSparse.Chapter12

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-! ### (12.24): the diagonal scaling -/

/-- **(12.24)**: the diagonal scaling `Ã = D^{-1/2} A D^{-1/2}`, with `D` the diagonal of `A`, has
unit diagonal.  This is the hypothesis under which Saad's Exercise 8 asks for the positive
definiteness of the Winget regularization. -/
theorem diag_diagonalScaled (A : Matrix n n ℝ) (hA : ∀ i, 0 < A i i) (i : n) :
    (diagonal (fun j => (Real.sqrt (A j j))⁻¹) * A * diagonal (fun j => (Real.sqrt (A j j))⁻¹))
      i i = 1 := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, ← mul_assoc,
    mul_comm ((Real.sqrt (A i i))⁻¹) (A i i), mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (hA i).le, mul_inv_cancel₀ (ne_of_gt (hA i))]

/-! ### (12.25): the Winget regularization -/

/-- **(12.25)**: the Winget regularization `Ā^[e] = I + Ã^[e] - diag(Ã^[e])` of a scaled element
matrix, which replaces its diagonal by the identity and leaves everything else alone. -/
def wingetRegularized (M : Matrix n n ℝ) : Matrix n n ℝ := 1 + M - diagonal M.diag

omit [Fintype n] in
/-- The entries of the Winget regularization: the diagonal is `1` and the rest is unchanged. -/
theorem wingetRegularized_apply (M : Matrix n n ℝ) (i j : n) :
    wingetRegularized M i j = if i = j then 1 else M i j := by
  by_cases h : i = j
  · subst h
    simp [wingetRegularized, Matrix.diag]
  · simp [wingetRegularized, h, Matrix.one_apply_ne h]

omit [Fintype n] [DecidableEq n] in
/-- A row of a positive semidefinite matrix through a vanishing diagonal entry is zero: this is the
`2 × 2` Cauchy–Schwarz inequality `|M i j|² ≤ M i i · M j j`, read off the determinant of the
principal submatrix on `{i, j}`. -/
private theorem apply_eq_zero_of_diag_eq_zero {N : Type*} {M : Matrix N N ℝ}
    (hM : M.PosSemidef) {i : N} (hi : M i i = 0) (j : N) : M i j = 0 := by
  have hsub := (hM.submatrix ![i, j]).det_nonneg
  rw [Matrix.det_fin_two] at hsub
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hsub
  have hji : M j i = M i j := by simpa using hM.isHermitian.apply i j
  rw [hi, zero_mul, zero_sub, hji] at hsub
  nlinarith [sq_nonneg (M i j)]

set_option linter.unusedFintypeInType false in
/-- **(12.25) is positive definite** — Saad's Exercise 8 of Chapter 12.  If the scaled element
matrices `Ã^[e]` are positive semidefinite, their sum `Ã` is positive definite, and the diagonal
scaling has made every diagonal entry of `Ã` equal to `1`, then every Winget-regularized element
matrix `Ā^[e] = I + Ã^[e] - diag(Ã^[e])` is positive definite.

The quadratic form is `xᵀ Ā^[e] x = ∑_i (1 - Ã^[e]_ii) x_i² + xᵀ Ã^[e] x`, a sum of two nonnegative
terms, so it vanishes only if both do.  At an index `i` with `x_i ≠ 0` the first forces
`Ã^[e]_ii = 1`, hence `Ã^[f]_ii = 0` for every other element `f`, hence — the summands being
positive semidefinite — the whole `i`-th row of `Ã^[f]` vanishes.  Then `xᵀ Ã^[f] x = 0` for every
`f`, so `xᵀ Ã x = 0`, contradicting the positive definiteness of the assembled matrix. -/
theorem equation_12_25 (Atilde : ι → Matrix n n ℝ) (hpsd : ∀ e, (Atilde e).PosSemidef)
    (hpd : (∑ e, Atilde e).PosDef) (hdiag : ∀ i, (∑ e, Atilde e) i i = 1) (e : ι) :
    (wingetRegularized (Atilde e)).PosDef := by
  classical
  have hdiag' : ∀ i, ∑ f, Atilde f i i = 1 := fun i => by rw [← hdiag i, Matrix.sum_apply]
  have hnonneg : ∀ f i, 0 ≤ Atilde f i i := fun f _ => (hpsd f).diag_nonneg
  have hle : ∀ f i, Atilde f i i ≤ 1 := fun f i => by
    rw [← hdiag' i]
    exact Finset.single_le_sum (f := fun g => Atilde g i i) (fun g _ => hnonneg g i)
      (Finset.mem_univ f)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    ((Matrix.isHermitian_one.add (hpsd e).isHermitian).sub (Matrix.isHermitian_diagonal _))
    fun x hx => ?_
  -- the quadratic form splits as `∑ (1 - Ã^[e]_ii) x_i² + xᵀ Ã^[e] x`
  have hsplit : star x ⬝ᵥ (wingetRegularized (Atilde e) *ᵥ x)
      = (∑ i, (1 - Atilde e i i) * (x i * x i)) + star x ⬝ᵥ (Atilde e *ᵥ x) := by
    have hcombine : ∑ i, (1 - Atilde e i i) * (x i * x i)
        = (∑ i, x i * x i) - ∑ i, x i * (Atilde e i i * x i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [wingetRegularized, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
      Matrix.one_mulVec, hcombine]
    simp only [star_trivial, dotProduct, Matrix.mulVec_diagonal, Matrix.diag]
    ring
  have hterm : ∀ i, 0 ≤ (1 - Atilde e i i) * (x i * x i) := fun i =>
    mul_nonneg (sub_nonneg.2 (hle e i)) (mul_self_nonneg _)
  have hsum_nonneg : (0 : ℝ) ≤ ∑ i, (1 - Atilde e i i) * (x i * x i) :=
    Finset.sum_nonneg fun i _ => hterm i
  have hq_nonneg : (0 : ℝ) ≤ star x ⬝ᵥ (Atilde e *ᵥ x) := (hpsd e).dotProduct_mulVec_nonneg x
  rw [hsplit]
  rcases (add_nonneg hsum_nonneg hq_nonneg).lt_or_eq with hlt | heq
  · exact hlt
  refine absurd ?_ (ne_of_gt (hpd.dotProduct_mulVec_pos hx))
  have hsum_zero : ∑ i, (1 - Atilde e i i) * (x i * x i) = 0 :=
    le_antisymm (by linarith) hsum_nonneg
  have hq_zero : star x ⬝ᵥ (Atilde e *ᵥ x) = 0 := le_antisymm (by linarith) hq_nonneg
  -- at every index where `x` does not vanish, the other elements have a zero diagonal entry there
  have hone : ∀ i, x i ≠ 0 → ∀ f, f ≠ e → Atilde f i i = 0 := by
    intro i hxi f hfe
    have hzero : (1 - Atilde e i i) * (x i * x i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).1 hsum_zero i (Finset.mem_univ i)
    have hei : Atilde e i i = 1 := by
      rcases mul_eq_zero.1 hzero with h | h
      · linarith [sub_eq_zero.1 h]
      · exact absurd (by nlinarith : x i = 0) hxi
    have hsplit' : (∑ g ∈ Finset.univ.erase e, Atilde g i i) + Atilde e i i = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ e)]
      exact hdiag' i
    have hrest : ∑ g ∈ Finset.univ.erase e, Atilde g i i = 0 := by
      rw [hei] at hsplit'; linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hnonneg g i).1 hrest f
      (Finset.mem_erase.2 ⟨hfe, Finset.mem_univ f⟩)
  -- so every summand contributes nothing to the quadratic form at `x`
  have hzero_form : ∀ f, star x ⬝ᵥ (Atilde f *ᵥ x) = 0 := by
    intro f
    by_cases hfe : f = e
    · rw [hfe]; exact hq_zero
    simp only [star_trivial, dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hxi : x i = 0
    · rw [hxi, zero_mul]
    have hrow : ∀ j, Atilde f i j = 0 :=
      apply_eq_zero_of_diag_eq_zero (hpsd f) (hone i hxi f hfe)
    have hmv : (Atilde f *ᵥ x) i = 0 := by simp [Matrix.mulVec, dotProduct, hrow]
    rw [hmv, mul_zero]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_eq_zero fun f _ => hzero_form f

end SaadSparse.Chapter12
