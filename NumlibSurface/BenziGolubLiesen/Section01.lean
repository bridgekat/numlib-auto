/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Real.Basic

/-!
# Benzi, Golub and Liesen, Section 1: Introduction

This module gives the coefficient matrix of the generalized saddle-point system (1.1) of
[benzi2005numerical]. For $A \in \mathbb{R}^{n \times n}$, $B_1, B_2 \in \mathbb{R}^{m \times n}$
and $C \in \mathbb{R}^{m \times m}$ it is the block matrix
$$\mathcal{A} = \begin{bmatrix} A & B_1^T \\ B_2 & -C \end{bmatrix}.$$
The later sections of the library state their results for this matrix and its special cases.

## Main definitions

* Equation (1.1), `BenziGolubLiesen.saddlePointMatrix`: the block matrix $\mathcal{A}$ with blocks
  $A$, $B_1^T$, $B_2$ and $-C$.

## Implementation notes

* The matrix is indexed by `n ⊕ m`: the first $n$ coordinates belong to the block $A$, the last $m$
  coordinates to the block $C$.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*}

/-- **Equation (1.1)** of [benzi2005numerical]. For $A \in \mathbb{R}^{n \times n}$,
$B_1, B_2 \in \mathbb{R}^{m \times n}$ and $C \in \mathbb{R}^{m \times m}$, the **saddle-point
matrix** is
$$\mathcal{A} = \begin{bmatrix} A & B_1^T \\ B_2 & -C \end{bmatrix} \in \mathbb{R}^{(n + m)
  \times (n + m)}.$$

The matrix is `Matrix.fromBlocks A B₁ᵀ B₂ (-C)`, indexed by `n ⊕ m`. The index types need not be
finite. -/
abbrev saddlePointMatrix (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ) (C : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks A B₁ᵀ B₂ (-C)

end BenziGolubLiesen
