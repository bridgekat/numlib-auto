/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.HermitianPart

/-!
# Solvability of saddle-point block matrices

This file studies the real saddle-point matrix
$$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & -C \end{bmatrix}$$
with $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. Let $H = (A + A^T)/2$ be the symmetric part of $A$. When $H$ and
$C$ are positive semidefinite, a vector $(x, y)$ is in the null space of $\mathcal{A}$ exactly when
$Ax + B^T y = 0$, $Hx = 0$, $Bx = 0$ and $Cy = 0$. For symmetric positive semidefinite $A$ this
gives a complete criterion: $\mathcal{A}$ is nonsingular if and only if $\ker A \cap \ker B = \{0\}$
and $\ker C \cap \ker B^T = \{0\}$. These results give Theorems 3.1–3.4 of [benzi2005numerical].

## Main results

* `Matrix.mulVec_injective_iff_rank_eq_card`: a matrix over a field is injective on column vectors
  if and only if its rank equals its number of columns.
* `Matrix.fromBlocks_transpose_neg_mulVec_eq_zero_iff`: if $H$ and $C$ are positive semidefinite,
  then $\mathcal{A}(x, y) = 0$ if and only if $Ax + B^T y = 0$, $Hx = 0$, $Bx = 0$ and $Cy = 0$.
* `Matrix.isUnit_fromBlocks_transpose_neg_iff`: if $A$ and $C$ are positive semidefinite, then
  $\mathcal{A}$ is nonsingular if and only if $\ker A \cap \ker B = \{0\}$ and
  $\ker C \cap \ker B^T = \{0\}$.
* `Matrix.isUnit_fromBlocks_transpose_neg_of_hermitianPart`: if $H$ and $C$ are positive
  semidefinite, $B$ has full row rank and $\ker H \cap \ker B = \{0\}$, then $\mathcal{A}$ is
  nonsingular.
* `Matrix.ker_inter_eq_bot_of_isUnit_fromBlocks`: if a block matrix
  $\begin{bmatrix} A & D \\ B & C \end{bmatrix}$ is nonsingular, then $\ker A \cap \ker B = \{0\}$.
* `Matrix.ranks_of_isUnit_fromBlocks_transpose_zero`: if $\begin{bmatrix} A & B_1^T \\ B_2 & 0
  \end{bmatrix}$ is nonsingular, then $B_1$ has rank $m$ and
  $\begin{bmatrix} A \\ B_2 \end{bmatrix}$ has rank $n$.

## Implementation notes

* Block matrices are `Matrix.fromBlocks`, indexed by `n ⊕ m`, and the vector $(x, y)$ is
  `Sum.elim x y`. The symmetric part $H$ is `Matrix.hermitianPart A`.
* Kernels are kernels of `Matrix.mulVecLin`, and a trivial intersection is written `⊓ … = ⊥`.
-/

namespace Matrix

variable {n m K : Type*}

/-- Let $M \in K^{m \times n}$ be a matrix over a field $K$. The map $x \mapsto Mx$ is injective if
and only if $\operatorname{rank} M = n$. -/
theorem mulVec_injective_iff_rank_eq_card [Fintype n] [Field K] {M : Matrix m n K} :
    Function.Injective M.mulVec ↔ M.rank = Fintype.card n := by
  rw [mulVec_injective_iff, M.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

private theorem sumElim_zero [Zero K] :
    Sum.elim (0 : n → K) (0 : m → K) = (0 : n ⊕ m → K) := by
  funext i
  cases i <;> rfl

variable [Fintype n] [Fintype m]

/-- Let $B \in \mathbb{R}^{m \times n}$ have rank $m$. Then the conjugate transpose
$B^H \in \mathbb{C}^{n \times m}$ of $B$, viewed as a complex matrix, is injective: $B^H y = 0$
implies $y = 0$ for $y \in \mathbb{C}^m$.

The complex matrix is `B.map Complex.ofReal`. -/
theorem mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank {B : Matrix m n ℝ}
    (hB : B.rank = Fintype.card m) : Function.Injective (B.map Complex.ofReal)ᴴ.mulVec := by
  have hBr : Function.Injective Bᵀ.mulVec :=
    Matrix.mulVec_injective_iff_rank_eq_card.mpr (by rwa [rank_transpose])
  rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot, ker_mulVecLin_eq_bot_iff]
  intro v hv
  have hre : Bᵀ *ᵥ (fun j ↦ (v j).re) = Bᵀ *ᵥ 0 := by
    funext i
    have hi := congrArg Complex.re (congrFun hv i)
    simpa [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] using hi
  have him : Bᵀ *ᵥ (fun j ↦ (v j).im) = Bᵀ *ᵥ 0 := by
    funext i
    have hi := congrArg Complex.im (congrFun hv i)
    simpa [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im] using hi
  funext i
  apply Complex.ext
  · exact congrFun (hBr hre) i
  · exact congrFun (hBr him) i

/-- Let $A \in K^{n \times n}$, $D \in K^{n \times m}$, $B \in K^{m \times n}$ and
$C \in K^{m \times m}$ over a semiring $K$. Then
$$\begin{bmatrix} A & D \\ B & C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} = 0
  \iff Ax + Dy = 0 \text{ and } Bx + Cy = 0.$$
-/
theorem fromBlocks_mulVec_sumElim_eq_zero_iff [Semiring K]
    (A : Matrix n n K) (D : Matrix n m K) (B : Matrix m n K) (C : Matrix m m K)
    (x : n → K) (y : m → K) :
    fromBlocks A D B C *ᵥ Sum.elim x y = 0 ↔
      A *ᵥ x + D *ᵥ y = 0 ∧ B *ᵥ x + C *ᵥ y = 0 := by
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, ← sumElim_zero, Sum.elim_eq_iff]

/-- Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. Suppose that the symmetric part $H = (A + A^T)/2$ of $A$ and
the matrix $C$ are positive semidefinite. Then for $x \in \mathbb{R}^n$ and
$y \in \mathbb{R}^m$,
$$\begin{bmatrix} A & B^T \\ B & -C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} = 0
  \iff Ax + B^T y = 0,\ Hx = 0,\ Bx = 0 \text{ and } Cy = 0.$$

The symmetric part is `Matrix.hermitianPart A`. The proof combines the two block equations into
$x^T H x + y^T C y = 0$, where both terms are nonnegative. -/
theorem fromBlocks_transpose_neg_mulVec_eq_zero_iff
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (x : n → ℝ) (y : m → ℝ) :
    fromBlocks A Bᵀ B (-C) *ᵥ Sum.elim x y = 0 ↔
      A *ᵥ x + Bᵀ *ᵥ y = 0 ∧ hermitianPart A *ᵥ x = 0 ∧
        B *ᵥ x = 0 ∧ C *ᵥ y = 0 := by
  rw [fromBlocks_mulVec_sumElim_eq_zero_iff, neg_mulVec, ← sub_eq_add_neg, sub_eq_zero]
  constructor
  · rintro ⟨htop, hbottom⟩
    have hsum : x ⬝ᵥ (hermitianPart A *ᵥ x) + y ⬝ᵥ (C *ᵥ y) = 0 := by
      rw [dotProduct_mulVec_hermitianPart, ← hbottom, ← dotProduct_transpose_mulVec B x y,
        ← dotProduct_add, htop, dotProduct_zero]
    have hx : 0 ≤ x ⬝ᵥ (hermitianPart A *ᵥ x) := by
      simpa using hA.dotProduct_mulVec_nonneg x
    have hy : 0 ≤ y ⬝ᵥ (C *ᵥ y) := by simpa using hC.dotProduct_mulVec_nonneg y
    have hx0 : x ⬝ᵥ (hermitianPart A *ᵥ x) = 0 := by linarith
    have hy0 : y ⬝ᵥ (C *ᵥ y) = 0 := by linarith
    have hCy : C *ᵥ y = 0 := hC.dotProduct_mulVec_zero_iff.mp (by simpa using hy0)
    exact ⟨htop, hA.dotProduct_mulVec_zero_iff.mp (by simpa using hx0), hbottom.trans hCy, hCy⟩
  · rintro ⟨htop, _, hBx, hCy⟩
    exact ⟨htop, hBx.trans hCy.symm⟩

/-- Let $M$ be a square matrix over a field, indexed by $n \sqcup m$. Then $M$ is nonsingular if and
only if, for all $x \in K^n$ and $y \in K^m$, $M (x, y) = 0$ implies $x = 0$ and $y = 0$. -/
theorem isUnit_iff_mulVec_sumElim [Field K] [DecidableEq n] [DecidableEq m]
    {M : Matrix (n ⊕ m) (n ⊕ m) K} :
    IsUnit M ↔ ∀ (x : n → K) (y : m → K), M *ᵥ Sum.elim x y = 0 → x = 0 ∧ y = 0 := by
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot,
    ker_mulVecLin_eq_bot_iff]
  constructor
  · intro h x y hxy
    have hz := h _ hxy
    rwa [← sumElim_zero, Sum.elim_eq_iff] at hz
  · intro h z hz
    rw [← Sum.elim_comp_inl_inr z] at hz ⊢
    obtain ⟨hx, hy⟩ := h _ _ hz
    rw [hx, hy, sumElim_zero]

variable [DecidableEq n] [DecidableEq m]

/-- Let $A \in \mathbb{R}^{n \times n}$ and $C \in \mathbb{R}^{m \times m}$ be symmetric positive
semidefinite, and let $B \in \mathbb{R}^{m \times n}$. Then the saddle-point matrix is
nonsingular if and only if both kernel intersections are trivial:
$$\begin{bmatrix} A & B^T \\ B & -C \end{bmatrix} \text{ is nonsingular} \iff
  \ker A \cap \ker B = \{0\} \text{ and } \ker C \cap \ker B^T = \{0\}.$$

This gives Theorems 3.1 and 3.2 of [benzi2005numerical]. Positive semidefinite is
`Matrix.PosSemidef`, which includes symmetry. -/
theorem isUnit_fromBlocks_transpose_neg_iff
    {A : Matrix n n ℝ} (B : Matrix m n ℝ) {C : Matrix m m ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    IsUnit (fromBlocks A Bᵀ B (-C)) ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
      LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥ := by
  rw [isUnit_iff_mulVec_sumElim]
  simp only [fromBlocks_transpose_neg_mulVec_eq_zero_iff B
    (hA.isHermitian.hermitianPart_eq ▸ hA) hC, hA.isHermitian.hermitianPart_eq,
    Submodule.eq_bot_iff, Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h
    refine ⟨fun x ⟨hxA, hxB⟩ ↦ ?_, fun y ⟨hyC, hyB⟩ ↦ ?_⟩
    · exact (h x 0 (by simp [hxA, hxB])).1
    · exact (h 0 y (by simp [hyC, hyB])).2
  · rintro ⟨hx, hy⟩ x y ⟨htop, hxA, hxB, hyC⟩
    exact ⟨hx x ⟨hxA, hxB⟩, hy y ⟨hyC, by simpa [hxA] using htop⟩⟩

/-- Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. Suppose that the symmetric part $H = (A + A^T)/2$ of $A$ and
the matrix $C$ are positive semidefinite, that $B^T$ is injective (that is, $B$ has full row
rank), and that $\ker H \cap \ker B = \{0\}$. Then
$$\begin{bmatrix} A & B^T \\ B & -C \end{bmatrix}$$
is nonsingular.

This is the sufficient condition of Theorem 3.4 of [benzi2005numerical]. The symmetric part is
`Matrix.hermitianPart A`. -/
theorem isUnit_fromBlocks_transpose_neg_of_hermitianPart
    {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}
    (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    IsUnit (fromBlocks A Bᵀ B (-C)) := by
  rw [isUnit_iff_mulVec_sumElim]
  intro x y hxy
  obtain ⟨htop, hHx, hBx, _⟩ := (fromBlocks_transpose_neg_mulVec_eq_zero_iff B hA hC x y).1 hxy
  have hx : x = 0 := (Submodule.eq_bot_iff _).mp hker x ⟨hHx, hBx⟩
  refine ⟨hx, hB ?_⟩
  simpa [hx] using htop

/-- Let $A \in K^{n \times n}$, $D \in K^{n \times m}$, $B \in K^{m \times n}$ and
$C \in K^{m \times m}$ over a field $K$. If the block matrix
$$\begin{bmatrix} A & D \\ B & C \end{bmatrix}$$
is nonsingular, then $\ker A \cap \ker B = \{0\}$.

The reason is that a common null vector $x$ of $A$ and $B$ gives the null vector $(x, 0)$ of the
block matrix. -/
theorem ker_inter_eq_bot_of_isUnit_fromBlocks
    [Field K] {A : Matrix n n K} {B : Matrix m n K} {D : Matrix n m K}
    {C : Matrix m m K} (h : IsUnit (fromBlocks A D B C)) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hxA, hxB⟩ ↦ ?_
  change A *ᵥ x = 0 at hxA
  change B *ᵥ x = 0 at hxB
  exact ((isUnit_iff_mulVec_sumElim.mp h) x 0
    ((fromBlocks_mulVec_sumElim_eq_zero_iff A D B C x 0).2
      (by simpa using And.intro hxA hxB))).1

/-- Let $A \in K^{n \times n}$ and $B_1, B_2 \in K^{m \times n}$ over a field $K$. If
$$\begin{bmatrix} A & B_1^T \\ B_2 & 0 \end{bmatrix}$$
is nonsingular, then $\operatorname{rank} B_1 = m$ and
$$\operatorname{rank} \begin{bmatrix} A \\ B_2 \end{bmatrix} = n.$$

This gives Theorem 3.3 of [benzi2005numerical]. The stacked matrix is `Matrix.fromRows A B₂`. -/
theorem ranks_of_isUnit_fromBlocks_transpose_zero
    [Field K] {A : Matrix n n K} {B₁ B₂ : Matrix m n K}
    (h : IsUnit (fromBlocks A B₁ᵀ B₂ (0 : Matrix m m K))) :
    B₁.rank = Fintype.card m ∧ (fromRows A B₂).rank = Fintype.card n := by
  have hnull := isUnit_iff_mulVec_sumElim.mp h
  constructor
  · rw [← rank_transpose, ← mulVec_injective_iff_rank_eq_card, ← coe_mulVecLin,
      ← LinearMap.ker_eq_bot, ker_mulVecLin_eq_bot_iff]
    intro y hy
    exact (hnull 0 y ((fromBlocks_mulVec_sumElim_eq_zero_iff A B₁ᵀ B₂ 0 0 y).2
      (by simp [hy]))).2
  · rw [← mulVec_injective_iff_rank_eq_card, ← coe_mulVecLin, ← LinearMap.ker_eq_bot,
      ker_mulVecLin_eq_bot_iff]
    intro x hx
    rw [fromRows_mulVec, ← sumElim_zero, Sum.elim_eq_iff] at hx
    exact (Submodule.eq_bot_iff _).mp (ker_inter_eq_bot_of_isUnit_fromBlocks h) x hx

end Matrix
