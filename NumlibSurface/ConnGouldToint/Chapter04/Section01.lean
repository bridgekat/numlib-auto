/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Conn, Gould and Toint, Section 4.1: Linear equations in optimization

This module formalizes Section 4.1 of [conn2000trust]. Optimization methods solve linear systems
with the symmetric block matrix
$$K = \begin{bmatrix} H & A^T \\ A & -D \end{bmatrix}$$
of (4.1.1), with $H \in \mathbb{R}^{n \times n}$, $A \in \mathbb{R}^{m \times n}$ and
$D \in \mathbb{R}^{m \times m}$. The system $(H + A^T D A) x = b$ has the Sherman–Morrison–Woodbury
solution (4.1.2), and it is equivalent to an augmented system with the matrix $K$, with $D^{-1}$ in
place of $D$, and the auxiliary variable $y = DAx$ (4.1.3).

The proofs use the backbone modules `Numlib.LinearAlgebra.Matrix.SchurComplement` and
`Numlib.LinearAlgebra.Matrix.NonsingularInverse`.

## Main definitions

* Equation (4.1.1), `ConnGouldToint.Chapter04.optimizationMatrix`: the block matrix $K$.

## Main results

* Equation (4.1.2), `ConnGouldToint.Chapter04.woodbury_solution_4_1_2`: the
  Sherman–Morrison–Woodbury formula solves $(H + A^T D A) x = b$ when $H$, $D$ and
  $D^{-1} + A H^{-1} A^T$ are invertible.
* Equation (4.1.2), `ConnGouldToint.Chapter04.woodbury_middle_inverse_counterexample`: the middle
  matrix $D^{-1} + A H^{-1} A^T$ can be singular when $H$ and $D$ are invertible.
* Equation (4.1.3), `ConnGouldToint.Chapter04.augmented_system_4_1_3`: the augmented system is
  equivalent to $(H + A^T D A) x = b$ together with $y = DAx$.

## Deviations from the source

* **Equations (4.1.1) and (4.1.3)** (generalization). The block constructor and elimination
  identity accept arbitrary square diagonal blocks and rectangular $A$. The source introduces
  symmetric $H$ and $D$ in the optimization setting.
* **Equation (4.1.2)** (correction). The source assumes only that $H$ and $D$ are invertible. The
  formula also needs the invertibility of $D^{-1} + A H^{-1} A^T$. See
  `ConnGouldToint.Chapter04.woodbury_solution_4_1_2` and
  `ConnGouldToint.Chapter04.woodbury_middle_inverse_counterexample`.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter04

variable {m n : ℕ}

/-- **Equation (4.1.1)** of [conn2000trust]. For $H \in \mathbb{R}^{n \times n}$,
$A \in \mathbb{R}^{m \times n}$ and $D \in \mathbb{R}^{m \times m}$, the **optimization matrix**
is the block matrix
$$\begin{bmatrix} H & A^T \\ A & -D \end{bmatrix} \in \mathbb{R}^{(n + m) \times (n + m)}.$$

It is `Matrix.saddleMatrix H Aᵀ (-D)`, indexed by `Fin n ⊕ Fin m`.

**Reading.** Same blocks for arbitrary square H and D.
-/
abbrev optimizationMatrix (H : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.saddleMatrix H Aᵀ (-D)

/-- **Equation (4.1.2)** of [conn2000trust] (Sherman–Morrison–Woodbury formula). Let
$H \in \mathbb{R}^{n \times n}$, $D \in \mathbb{R}^{m \times m}$ and
$A \in \mathbb{R}^{m \times n}$, and suppose that $H$, $D$ and $D^{-1} + A H^{-1} A^T$ are
invertible. Then for every $b \in \mathbb{R}^n$ the vector
$$x = H^{-1} b - H^{-1} A^T (D^{-1} + A H^{-1} A^T)^{-1} A H^{-1} b$$
solves $(H + A^T D A) x = b$.

**Correction.** The source assumes only that $H$ and $D$ are invertible. The middle matrix
$D^{-1} + A H^{-1} A^T$ can then be singular, so its invertibility is an added hypothesis; see
`ConnGouldToint.Chapter04.woodbury_middle_inverse_counterexample`. -/
theorem woodbury_solution_4_1_2 {H : Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin m) (Fin m) ℝ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hH : IsUnit H) (hD : IsUnit D) (hS : IsUnit (D⁻¹ + A * H⁻¹ * Aᵀ))
    (b : Fin n → ℝ) :
    (H + Aᵀ * D * A) *ᵥ
      (H⁻¹ *ᵥ b - (H⁻¹ * Aᵀ * (D⁻¹ + A * H⁻¹ * Aᵀ)⁻¹ * A * H⁻¹) *ᵥ b) = b := by
  have hW := Matrix.add_mul_mul_inv_eq_sub H Aᵀ D A hH hD hS
  have hB : IsUnit (H + Aᵀ * D * A) := by
    obtain ⟨_⟩ := hH.nonempty_invertible
    obtain ⟨_⟩ := hD.nonempty_invertible
    obtain ⟨hSI⟩ := hS.nonempty_invertible
    simp only [← invOf_eq_nonsing_inv] at hSI
    let := Matrix.invertibleAddMulMul H Aᵀ D A
    exact isUnit_of_invertible _
  rw [← sub_mulVec, ← hW]
  exact Matrix.mulVec_nonsing_inv_mulVec hB b

/-- **Equation (4.1.2)** of [conn2000trust], counterexample. There are
$H, D, A \in \mathbb{R}^{1 \times 1}$ with $H$ and $D$ invertible and $D^{-1} + A H^{-1} A^T$
singular.

The witness is $H = -1$ and $D = A = 1$, for which $D^{-1} + A H^{-1} A^T = 0$.

**Reading.** Invertibility of H and D alone leaves the middle matrix singular in a scalar example.
-/
theorem woodbury_middle_inverse_counterexample :
    ∃ H D A : Matrix (Fin 1) (Fin 1) ℝ,
      IsUnit H ∧ IsUnit D ∧ ¬ IsUnit (D⁻¹ + A * H⁻¹ * Aᵀ) := by
  have hInv : (-1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = -1 :=
    Matrix.inv_eq_left_inv (by simp)
  refine ⟨-1, 1, 1, isUnit_one.neg, isUnit_one, ?_⟩
  simp [hInv]

/-- **Equation (4.1.3)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$,
$A \in \mathbb{R}^{m \times n}$, and let $D \in \mathbb{R}^{m \times m}$ be invertible. Then for
$x, b \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$,
$$\begin{bmatrix} H & A^T \\ A & -D^{-1} \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} =
  \begin{bmatrix} b \\ 0 \end{bmatrix} \iff (H + A^T D A) x = b \text{ and } y = DAx.$$

The vector $(x, y)$ is `Sum.elim x y`.

**Reading.** Gives the elimination equivalence without symmetry of H or D.
-/
theorem augmented_system_4_1_3 {H : Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin m) (Fin m) ℝ} (A : Matrix (Fin m) (Fin n) ℝ) (hD : IsUnit D)
    (x b : Fin n → ℝ) (y : Fin m → ℝ) :
    optimizationMatrix H A D⁻¹ *ᵥ Sum.elim x y = Sum.elim b 0 ↔
      (H + Aᵀ * D * A) *ᵥ x = b ∧ y = D *ᵥ (A *ᵥ x) := by
  rw [optimizationMatrix, Matrix.saddleMatrix_mulVec_elim]
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_transpose, neg_mulVec,
    ← sub_eq_add_neg, sub_eq_zero]
  have hy : A *ᵥ x = D⁻¹ *ᵥ y ↔ y = D *ᵥ (A *ᵥ x) := by
    constructor
    · intro h
      rw [h, Matrix.mulVec_nonsing_inv_mulVec hD]
    · intro h
      rw [h, Matrix.nonsing_inv_mulVec_mulVec hD]
  rw [hy]
  constructor <;> rintro ⟨h, hy⟩
  · refine ⟨?_, hy⟩
    simpa [add_mulVec, ← mulVec_mulVec, ← hy] using h
  · refine ⟨?_, hy⟩
    simpa [add_mulVec, ← mulVec_mulVec, ← hy] using h

end ConnGouldToint.Chapter04
