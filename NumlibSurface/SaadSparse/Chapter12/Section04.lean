/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Saad, Section 12.4: Multicolouring and the red–black reduced system

This module formalizes the two pieces of algebra in Section 12.4 of [saad2003iterative]; the rest of
the section describes a greedy colouring algorithm and the parallel sweeps that a colouring makes
possible. In Section 12.4.1, a 2-colouring of the adjacency graph of $A$, in which no two adjacent
nodes have the same colour, makes each submatrix of $A$ on the nodes of one colour diagonal. So
ordering the red unknowns before the black ones puts the system in the form (12.18),
$$\begin{bmatrix} D_1 & F \\ E & D_2 \end{bmatrix} \begin{bmatrix} x_1 \\ x_2 \end{bmatrix} =
  \begin{bmatrix} b_1 \\ b_2 \end{bmatrix},$$
with $D_1$ and $D_2$ diagonal. In Section 12.4.2, eliminating the red unknowns leaves the reduced
system $(D_2 - E D_1^{-1} F) x_2 = b_2 - E D_1^{-1} b_1$ on the black unknowns alone. Its matrix is
the Schur complement of `Numlib.LinearAlgebra.Matrix.SchurComplement`.

The elimination does not use that $D_1$ is diagonal. As the book says, it "is more often employed
when $D_1$ is not diagonal, such as in domain decomposition methods", where it is
`SaadSparse.Chapter14.blockGaussianElimination_eq`.

## Main results

* Section 12.4.1, `SaadSparse.Chapter12.isDiag_submatrix_of_coloring`: the submatrix of $A$ on the
  nodes of one colour is diagonal.
* Equation (12.18), `SaadSparse.Chapter12.equation_12_18`: the red–black system is equivalent to the
  reduced system together with the recovery of the red unknowns.

## Conventions

* The block names of (12.18) put $F$ in the $(1,2)$ corner and $E$ in the $(2,1)$ corner, the
  opposite of the partitioning of Section 14.2. The statements keep the letters of the book.

## Not formalized

* **The colouring itself.** Which nodes receive which colour is a graph problem with no claim
  attached.
* **Algorithm 12.3.** It is a listing.
-/

open Matrix

namespace SaadSparse.Chapter12

/-! ### Section 12.4.1: what a 2-colouring gives -/

/-- **Section 12.4.1** of [saad2003iterative]. Let $A$ be a square matrix indexed by a set $V$ of
nodes, and let $c$ colour each node with one of two colours. Assume that no two distinct nodes
of the same colour are coupled: $a_{ij} = 0$ whenever $i \neq j$ and $c(i) = c(j)$. Then for
each colour $p$, the submatrix of $A$ on the nodes of colour $p$ is diagonal.

Applied to the two colours of a red–black ordering, this says that $D_1$ and $D_2$ in (12.18)
are diagonal. The colours are `Bool`, and the matrix has entries in any type with a zero. -/
theorem isDiag_submatrix_of_coloring {V R : Type*} [Zero R] (A : Matrix V V R)
    (c : V → Bool) (hc : ∀ i j, i ≠ j → c i = c j → A i j = 0) (p : Bool) :
    (A.submatrix (Subtype.val : {i // c i = p} → V) Subtype.val).IsDiag := fun i j hij =>
  hc _ _ (fun h => hij (Subtype.ext h)) (i.2.trans j.2.symm)

/-! ### Section 12.4.2: the reduced system -/

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
variable {D₁ : Matrix m m R} {F : Matrix m n R} {E : Matrix n m R} {D₂ : Matrix n n R}

/-- **Equation (12.18)** of [saad2003iterative] and the reduced system of Section 12.4.2. Let $R$ be
a commutative ring, let $D_1 \in R^{m \times m}$ be nonsingular, and let $F \in R^{m \times n}$,
$E \in R^{n \times m}$ and $D_2 \in R^{n \times n}$. Then $(x_1, x_2)$ solves the red–black
system
$$\begin{bmatrix} D_1 & F \\ E & D_2 \end{bmatrix} \begin{bmatrix} x_1 \\ x_2 \end{bmatrix} =
  \begin{bmatrix} b_1 \\ b_2 \end{bmatrix}$$
if and only if the black unknown $x_2$ solves the reduced system
$$(D_2 - E D_1^{-1} F) x_2 = b_2 - E D_1^{-1} b_1$$
and the red unknown is $x_1 = D_1^{-1} (b_1 - F x_2)$.

The matrix of the reduced system is `Matrix.schurComplement` of the block matrix. The result
does not need $D_1$ or $D_2$ to be diagonal. -/
theorem equation_12_18 (hD₁ : IsUnit D₁) (b₁ : m → R) (b₂ : n → R) (x₁ : m → R) (x₂ : n → R) :
    fromBlocks D₁ F E D₂ *ᵥ Sum.elim x₁ x₂ = Sum.elim b₁ b₂
      ↔ (fromBlocks D₁ F E D₂).schurComplement *ᵥ x₂ = b₂ - E *ᵥ (D₁⁻¹ *ᵥ b₁)
          ∧ x₁ = D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂) := by
  have helim : ∀ (u : m → R) (v : n → R),
      Sum.elim u v = Sum.elim b₁ b₂ ↔ u = b₁ ∧ v = b₂ := by
    refine fun u v => ⟨fun h => ⟨funext fun i => congrFun h (Sum.inl i),
      funext fun i => congrFun h (Sum.inr i)⟩, ?_⟩
    rintro ⟨rfl, rfl⟩
    rfl
  have hred : D₁ *ᵥ x₁ + F *ᵥ x₂ = b₁ ↔ x₁ = D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂) := by
    rw [← eq_sub_iff_add_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h, Matrix.nonsing_inv_mulVec_mulVec hD₁]
    · rw [h, Matrix.mulVec_nonsing_inv_mulVec hD₁]
  have hblack : E *ᵥ (D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂)) + D₂ *ᵥ x₂ = b₂
      ↔ (fromBlocks D₁ F E D₂).schurComplement *ᵥ x₂ = b₂ - E *ᵥ (D₁⁻¹ *ᵥ b₁) := by
    rw [Matrix.schurComplement_fromBlocks]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [← h] <;> abel
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [helim]
  refine ⟨fun h => ⟨?_, hred.1 h.1⟩, fun h => ⟨hred.2 h.2, ?_⟩⟩
  · rw [← hblack, ← hred.1 h.1]
    exact h.2
  · rw [h.2]
    exact hblack.2 h.1

end SaadSparse.Chapter12
