/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 3.2: Solvability conditions

This module formalizes the nonsingularity criteria for saddle-point matrices in Section 3.2 of
[benzi2005numerical]. For $A \in \mathbb{R}^{n \times n}$, $B, B_1, B_2 \in \mathbb{R}^{m \times n}$
and $C \in \mathbb{R}^{m \times m}$, the matrices are
$$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & -C \end{bmatrix} \quad \text{and} \quad
  \begin{bmatrix} A & B_1^T \\ B_2 & 0 \end{bmatrix},$$
as in (1.1). The criteria are stated in terms of the kernels of the blocks, the rank of $B$, and the
symmetric part $H = \frac{1}{2}(A + A^T)$ of $A$. Theorems 3.1 and 3.2 treat symmetric $A$, Theorem
3.3 gives necessary conditions for a zero block $C$, and Theorem 3.4 treats nonsymmetric $A$. The
proofs specialize results in `Numlib.LinearAlgebra.Matrix.SaddlePoint`.

## Main results

* Theorem 3.1, `BenziGolubLiesen.theorem_3_1`: if $A$ is symmetric positive definite and $C$ is
  symmetric positive semidefinite, then $\ker C \cap \ker B^T = \{0\}$ implies that $\mathcal{A}$ is
  nonsingular, and so does $\operatorname{rank} B = m$.
* Theorem 3.2, `BenziGolubLiesen.theorem_3_2`: if $A$ is symmetric positive semidefinite, $B$ has
  rank $m$ and $C = 0$, then $\mathcal{A}$ is nonsingular if and only if
  $\ker A \cap \ker B = \{0\}$.
* Theorem 3.3, `BenziGolubLiesen.theorem_3_3`: if the matrix with blocks $A$, $B_1^T$, $B_2$ and $0$
  is nonsingular, then $B_1$ has rank $m$ and the stacked matrix
  $\begin{bmatrix} A \\ B_2 \end{bmatrix}$ has rank $n$.
* Theorem 3.4, `BenziGolubLiesen.theorem_3_4`: if $H$ and $C$ are positive semidefinite and $B$ has
  rank $m$, then $\ker H \cap \ker B = \{0\}$ implies that $\mathcal{A}$ is nonsingular, and
  nonsingularity implies $\ker A \cap \ker B = \{0\}$.
* Examples after Theorem 3.4, `BenziGolubLiesen.theorem_3_4_converses`: neither implication of
  Theorem 3.4 has a true converse, even for $C = 0$.

## Implementation notes

* A kernel is the kernel of `Matrix.mulVecLin`, and the condition that two kernels intersect
  trivially is `LinearMap.ker _ ⊓ LinearMap.ker _ = ⊥`.
* Nonsingularity of a square matrix is `IsUnit`.
* The symmetric part $H$ is `Matrix.hermitianPart A`. For a real matrix, `Matrix.PosDef` and
  `Matrix.PosSemidef` include symmetry.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {A : Matrix n n ℝ} {B B₁ B₂ : Matrix m n ℝ} {C : Matrix m m ℝ}

omit [DecidableEq n] [DecidableEq m] in
private theorem fullRowRank_injective (hB : B.rank = Fintype.card m) :
    Function.Injective Bᵀ.mulVec :=
  Matrix.mulVec_injective_iff_rank_eq_card.mpr (by rwa [Matrix.rank_transpose])

/-- **Theorem 3.1** of [benzi2005numerical]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $B \in \mathbb{R}^{m \times n}$, and let $C \in \mathbb{R}^{m \times m}$
be symmetric positive semidefinite. Then:

* if $\ker C \cap \ker B^T = \{0\}$, the matrix $\mathcal{A} = \begin{bmatrix} A & B^T \\ B & -C
  \end{bmatrix}$ is nonsingular;
* in particular, if $B$ has full rank, $\operatorname{rank} B = m$, then $\mathcal{A}$ is
  nonsingular.

The matrix $\mathcal{A}$ is `BenziGolubLiesen.saddlePointMatrix A B B C`. -/
theorem theorem_3_1 (hA : A.PosDef) (hC : C.PosSemidef) :
    (LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥ →
      IsUnit (saddlePointMatrix A B B C)) ∧
    (B.rank = Fintype.card m → IsUnit (saddlePointMatrix A B B C)) := by
  have hkerA : LinearMap.ker A.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hA.mulVec_injective
  have h (hker : LinearMap.ker C.mulVecLin ⊓ LinearMap.ker Bᵀ.mulVecLin = ⊥) :
      IsUnit (saddlePointMatrix A B B C) :=
    (isUnit_fromBlocks_transpose_neg_iff B hA.posSemidef hC).mpr ⟨by simp [hkerA], hker⟩
  refine ⟨h, fun hB ↦ h ?_⟩
  have hkerB : LinearMap.ker Bᵀ.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fullRowRank_injective hB)
  simp only [hkerB, inf_bot_eq]

/-- **Theorem 3.2** of [benzi2005numerical]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive semidefinite, and let $B \in \mathbb{R}^{m \times n}$ have rank $m$. Then the matrix
$$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$$
is nonsingular if and only if $\ker A \cap \ker B = \{0\}$.

The matrix $\mathcal{A}$ is `BenziGolubLiesen.saddlePointMatrix A B B 0`. -/
theorem theorem_3_2 (hA : A.PosSemidef) (hB : B.rank = Fintype.card m) :
    IsUnit (saddlePointMatrix A B B 0) ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ := by
  have hkerB : LinearMap.ker Bᵀ.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fullRowRank_injective hB)
  simpa only [hkerB, inf_bot_eq, and_true] using
    isUnit_fromBlocks_transpose_neg_iff B hA (PosSemidef.zero (n := m))

/-- **Theorem 3.3** of [benzi2005numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$B_1, B_2 \in \mathbb{R}^{m \times n}$. If the matrix
$$\begin{bmatrix} A & B_1^T \\ B_2 & 0 \end{bmatrix}$$
is nonsingular, then $\operatorname{rank} B_1 = m$ and the stacked matrix $\begin{bmatrix} A \\
B_2 \end{bmatrix} \in \mathbb{R}^{(n + m) \times n}$ has rank $n$.

The block matrix is `BenziGolubLiesen.saddlePointMatrix A B₁ B₂ 0`, and the stacked matrix is
`Matrix.fromRows A B₂`. No further hypotheses on the blocks are needed. -/
theorem theorem_3_3 (h : IsUnit (saddlePointMatrix A B₁ B₂ 0)) :
    B₁.rank = Fintype.card m ∧ (fromRows A B₂).rank = Fintype.card n :=
  ranks_of_isUnit_fromBlocks_transpose_zero (by simpa [saddlePointMatrix] using h)

/-- **Theorem 3.4** of [benzi2005numerical]. Let $A \in \mathbb{R}^{n \times n}$ have positive
semidefinite symmetric part $H = \frac{1}{2}(A + A^T)$, let $B \in \mathbb{R}^{m \times n}$ have
rank $m$, and let $C \in \mathbb{R}^{m \times m}$ be symmetric positive semidefinite. Let
$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & -C \end{bmatrix}$. Then:

* if $\ker H \cap \ker B = \{0\}$, then $\mathcal{A}$ is nonsingular;
* if $\mathcal{A}$ is nonsingular, then $\ker A \cap \ker B = \{0\}$.

The symmetric part $H$ is `Matrix.hermitianPart A`, and $\mathcal{A}$ is
`BenziGolubLiesen.saddlePointMatrix A B B C`. `BenziGolubLiesen.theorem_3_4_converses` shows
that neither implication can be reversed. -/
theorem theorem_3_4 (hA : (hermitianPart A).PosSemidef) (hC : C.PosSemidef)
    (hB : B.rank = Fintype.card m) :
    ((LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) →
      IsUnit (saddlePointMatrix A B B C)) ∧
    (IsUnit (saddlePointMatrix A B B C) →
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :=
  ⟨isUnit_fromBlocks_transpose_neg_of_hermitianPart hA hC (fullRowRank_injective hB),
    ker_inter_eq_bot_of_isUnit_fromBlocks⟩

private theorem singleRow_fullRank {k : ℕ} (j : Fin k) :
    (Matrix.single (0 : Fin 1) j (1 : ℝ)).rank = 1 := by
  suffices (Matrix.single (0 : Fin 1) j (1 : ℝ)).rank = Fintype.card (Fin 1) by
    simpa only [Fintype.card_fin] using this
  rw [← rank_transpose, ← mulVec_injective_iff_rank_eq_card, transpose_single]
  intro x y h
  have h0 := congrFun h j
  simp only [single_mulVec, Function.update_self, one_mul] at h0
  funext i
  fin_cases i
  exact h0

private theorem converse_i_counterexample :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 1) (Fin 3) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧ IsUnit (saddlePointMatrix A B B 0) ∧
        LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin ≠ ⊥ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, 0; 1, 0, 0; 0, 0, 0]
  let B : Matrix (Fin 1) (Fin 3) ℝ := Matrix.single 0 2 1
  have hH : hermitianPart A = Matrix.diagonal ![1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, hermitianPart_eq_smul_add_transpose, Matrix.diagonal_apply]
  refine ⟨A, B, ?_, singleRow_fullRank 2, ?_, ?_⟩
  · rw [hH, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · rw [isUnit_iff_mulVec_sumElim]
    intro x y h
    change fromBlocks A Bᵀ B (-(0 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ Sum.elim x y = 0 at h
    rw [fromBlocks_mulVec_sumElim_eq_zero_iff] at h
    have hx0 : x 0 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ] using
        congrFun h.1 1
    have hy0 : y 0 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ] using
        congrFun h.1 2
    have hx1 : x 1 = 0 := by
      simpa [A, B, transpose_single, single_mulVec, dotProduct, Fin.sum_univ_succ, hx0] using
        congrFun h.1 0
    have hx2 : x 2 = 0 := by
      simpa [B, single_mulVec] using congrFun h.2 0
    constructor
    · funext i
      fin_cases i
      · exact hx0
      · exact hx1
      · exact hx2
    · funext i
      fin_cases i
      exact hy0
  · intro h
    let x : Fin 3 → ℝ := ![0, 1, 0]
    have hx : x ∈ LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
      rw [hH]
      simp only [Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply]
      constructor <;> ext i <;> fin_cases i <;>
        norm_num [B, x, mulVec, dotProduct, Fin.sum_univ_succ, Matrix.single, diagonal_apply]
    have hzero := (Submodule.eq_bot_iff _).mp h x hx
    have h1 := congrFun hzero 1
    norm_num [x] at h1

private theorem converse_ii_counterexample :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
        ¬IsUnit (saddlePointMatrix A B B 0) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1]
  let B : Matrix (Fin 1) (Fin 2) ℝ := Matrix.single 0 1 1
  have hH : hermitianPart A = Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, hermitianPart_eq_smul_add_transpose, Matrix.diagonal_apply]
  refine ⟨A, B, ?_, singleRow_fullRank 1, ?_, ?_⟩
  · rw [hH, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  · have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (by
      norm_num [A, Matrix.det_fin_two])
    simp [(LinearMap.ker_eq_bot.mpr (mulVec_injective_iff_isUnit.mpr hA) :
      LinearMap.ker A.mulVecLin = ⊥)]
  · intro h
    let x : Fin 2 → ℝ := ![1, 0]
    let y : Fin 1 → ℝ := ![-1]
    have hxy : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = 0 := by
      change fromBlocks A Bᵀ B (-(0 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ Sum.elim x y = 0
      rw [fromBlocks_mulVec_sumElim_eq_zero_iff]
      constructor
      · ext i
        fin_cases i <;>
          norm_num [A, B, x, y, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.single]
      · simp [B, x, single_mulVec]
    have h0 := congrFun ((isUnit_iff_mulVec_sumElim.mp h) x y hxy).1 0
    norm_num [x] at h0

/-- **Examples after Theorem 3.4** of [benzi2005numerical]. The two implications of Theorem 3.4 do
not have true converses, even when $C = 0$:

* there are $A \in \mathbb{R}^{3 \times 3}$ and $B \in \mathbb{R}^{1 \times 3}$ such that
  $H = \frac{1}{2}(A + A^T)$ is positive semidefinite, $\operatorname{rank} B = 1$ and
  $\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$ is nonsingular, but
  $\ker H \cap \ker B \neq \{0\}$;
* there are $A \in \mathbb{R}^{2 \times 2}$ and $B \in \mathbb{R}^{1 \times 2}$ such that $H$ is
  positive semidefinite, $\operatorname{rank} B = 1$ and $\ker A \cap \ker B = \{0\}$, but
  $\begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}$ is singular.

The proof uses the witnesses $A = \begin{bmatrix} 1 & -1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 0
\end{bmatrix}$, $B = \begin{bmatrix} 0 & 0 & 1 \end{bmatrix}$, with
$H = \operatorname{diag}(1, 0, 0)$, and $A = \begin{bmatrix} 0 & -1 \\ 1 & 1 \end{bmatrix}$,
$B = \begin{bmatrix} 0 & 1 \end{bmatrix}$, with $H = \operatorname{diag}(0, 1)$. -/
theorem theorem_3_4_converses :
    (∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 1) (Fin 3) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧ IsUnit (saddlePointMatrix A B B 0) ∧
        LinearMap.ker (hermitianPart A).mulVecLin ⊓ LinearMap.ker B.mulVecLin ≠ ⊥) ∧
    (∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      (hermitianPart A).PosSemidef ∧ B.rank = 1 ∧
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ ∧
        ¬IsUnit (saddlePointMatrix A B B 0)) :=
  ⟨converse_i_counterexample, converse_ii_counterexample⟩

end BenziGolubLiesen
