/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Saad, Section 12.7.2: Winget regularization of element matrices

This module formalizes the Winget regularization of Section 12.7.2 of [saad2003iterative] and proves
that it gives positive definite matrices. The element-by-element preconditioners of the section
start from the unassembled form $A = \sum_e A^{[e]}$ of a finite element stiffness matrix. They
scale it by its own diagonal (12.24), $\tilde A = D^{-1/2} A D^{-1/2}$ with
$D = \operatorname{diag}(A)$, and then regularize each scaled element matrix by forcing its diagonal
to be the identity (12.25):
$$\bar A^{[e]} = I + \tilde A^{[e]} - \operatorname{diag}(\tilde A^{[e]}).$$

The book asserts that these matrices are positive definite and refers to Exercise 8 of the chapter,
which asks why they are positive definite when $\tilde A$ is obtained from $A$ by a diagonal
scaling. The theorem `SaadSparse.Chapter12.equation_12_25` answers the exercise under the hypotheses
that the sentence names: each scaled element matrix is positive semidefinite, the assembled matrix
$\tilde A = \sum_e \tilde A^{[e]}$ is positive definite, and the diagonal of $\tilde A$ is the
identity. The last hypothesis is what the scaling (12.24) gives, by
`SaadSparse.Chapter12.diag_diagonalScaled`. The proofs are direct and use only facts about positive
semidefinite matrices from Mathlib.

## Main definitions

* Equation (12.25), `SaadSparse.Chapter12.wingetRegularized`: the Winget regularization
  $I + M - \operatorname{diag}(M)$ of a square matrix $M$.

## Main results

* Equation (12.24), `SaadSparse.Chapter12.diag_diagonalScaled`: if $A$ has a positive diagonal, then
  $D^{-1/2} A D^{-1/2}$ has unit diagonal.
* Equation (12.25), `SaadSparse.Chapter12.equation_12_25`: if the matrices $\tilde A^{[e]}$ are
  positive semidefinite and their sum is positive definite with unit diagonal, then each
  $\bar A^{[e]}$ is positive definite.

## Proof outline

The diagonal entries of the matrices $\tilde A^{[e]}$ are nonnegative and add up to $1$, so
$0 \le \tilde a^{[e]}_{ii} \le 1$. The quadratic form $x^T \bar A^{[e]} x = \sum_i (1 - \tilde
a^{[e]}_{ii}) x_i^2 + x^T \tilde A^{[e]} x$ is therefore a sum of two nonnegative terms. If it
vanishes, then at each index $i$ with $x_i \neq 0$ the first term forces $\tilde a^{[e]}_{ii} = 1$,
hence $\tilde a^{[f]}_{ii} = 0$ for every other element $f$. A positive semidefinite matrix with a
zero diagonal entry has a zero row there, so $x^T \tilde A^{[f]} x = 0$ for every $f$. Then
$x^T \tilde A x = 0$, which contradicts the positive definiteness of $\tilde A$ unless $x = 0$.

## Implementation notes

* Matrices are indexed by a finite type `n`, and the elements by a finite type `ι`. The theorem
  takes the scaled element matrices $\tilde A^{[e]}$ as its data. The connectivity matrices $P_e$
  and the element matrices $A_{K_e}$ of the book do not appear, because the proof does not need
  them.

## Deviations from the source

* **(12.24) and (12.25)** (scope and generalization).
  `SaadSparse.Chapter12.diag_diagonalScaled` uses the positive diagonal of $A$ and proves unit
  diagonal for that choice of $D$. `SaadSparse.Chapter12.equation_12_25` takes already scaled
  positive semidefinite summands and a positive definite unit-diagonal sum, which gives the
  Winget conclusion without finite-element connectivity data.

## Not formalized

* **(12.26)–(12.29)**, the element-by-element preconditioners. They are definitions, and the book
  claims no property of them.
* **Section 12.7.1.** It is a paragraph that points back to Section 10.5.
* **Section 12.7.3**, Algorithm 12.8. It is a block form of the Gauss–Seidel iteration for the
  normal equations, which the material of Chapter 8 covers in general.
-/

open Matrix

namespace SaadSparse.Chapter12

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-! ### Equation (12.24): the diagonal scaling -/

/-- **Equation (12.24)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ have positive
diagonal entries, $a_{ii} > 0$ for all $i$, and let $D = \operatorname{diag}(A)$. Then the
scaled matrix $\tilde A = D^{-1/2} A D^{-1/2}$ has unit diagonal: $\tilde a_{ii} = 1$ for every
$i$.

This is the hypothesis under which Exercise 8 of Chapter 12 asks for the positive definiteness
of the Winget regularization, see `SaadSparse.Chapter12.equation_12_25`. The matrix $D^{-1/2}$
is `diagonal (fun j => (Real.sqrt (A j j))⁻¹)`.

**Reading.** Formalizes unit diagonal consequence of scaling by A's own diagonal, for any positive
diagonal.
-/
theorem diag_diagonalScaled (A : Matrix n n ℝ) (hA : ∀ i, 0 < A i i) (i : n) :
    (diagonal (fun j => (Real.sqrt (A j j))⁻¹) * A * diagonal (fun j => (Real.sqrt (A j j))⁻¹))
      i i = 1 := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, ← mul_assoc,
    mul_comm ((Real.sqrt (A i i))⁻¹) (A i i), mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (hA i).le, mul_inv_cancel₀ (ne_of_gt (hA i))]

/-! ### Equation (12.25): the Winget regularization -/

/-- **Equation (12.25)** of [saad2003iterative]. The **Winget regularization** of a square real
matrix $M$ is
$$\bar M = I + M - \operatorname{diag}(M).$$
It replaces the diagonal of $M$ by the identity and keeps the off-diagonal entries. The book
applies it to each scaled element matrix $\tilde A^{[e]}$ and obtains $\bar A^{[e]}$.

**Reading.** Applies the diagonal replacement formula to any square real matrix.
-/
def wingetRegularized (M : Matrix n n ℝ) : Matrix n n ℝ := 1 + M - diagonal M.diag

omit [Fintype n] in
/-- The entries of the Winget regularization: $\bar M_{ij} = 1$ if $i = j$, and
$\bar M_{ij} = M_{ij}$ if $i \neq j$. -/
theorem wingetRegularized_apply (M : Matrix n n ℝ) (i j : n) :
    wingetRegularized M i j = if i = j then 1 else M i j := by
  by_cases h : i = j
  · subst h
    simp [wingetRegularized, Matrix.diag]
  · simp [wingetRegularized, h, Matrix.one_apply_ne h]

set_option linter.unusedFintypeInType false in
/-- **Equation (12.25)** of [saad2003iterative], positive definiteness (Exercise 8 of Chapter 12).
Let $\tilde A^{[e]} \in \mathbb{R}^{n \times n}$, for $e$ in a finite index set, be symmetric
positive semidefinite matrices. Suppose that their sum $\tilde A = \sum_e \tilde A^{[e]}$ is
positive definite and has unit diagonal, $\tilde a_{ii} = 1$ for all $i$. Then for each $e$ the
Winget-regularized matrix
$$\bar A^{[e]} = I + \tilde A^{[e]} - \operatorname{diag}(\tilde A^{[e]})$$
is positive definite.

The book states only that these matrices are positive definite and leaves the reason to the
exercise. The theorem uses the finite-element setting of the assertion: a scaled element
stiffness matrix is positive semidefinite, and scaling (12.24) by the diagonal of $A$ makes
the diagonal of $\tilde A$ the identity
(`SaadSparse.Chapter12.diag_diagonalScaled`). The proof writes the quadratic form of
$\bar A^{[e]}$ as a sum of two nonnegative terms, and shows that if both vanish at $x$, then
$x^T \tilde A x = 0$.

**Generalization.** The input consists of already scaled positive semidefinite terms whose sum
is positive definite with unit diagonal. The resulting criterion does not depend on the element
connectivity matrices. -/
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
    have hrow : ∀ j, Atilde f i j = 0 := fun j =>
      ((hpsd f).apply_eq_zero_of_diag_eq_zero (hone i hxi f hfe) j).1
    have hmv : (Atilde f *ᵥ x) i = 0 := by simp [Matrix.mulVec, dotProduct, hrow]
    rw [hmv, mul_zero]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_eq_zero fun f _ => hzero_form f

end SaadSparse.Chapter12
