/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Numlib.Analysis.Convex.Saddle.Minimax
import Numlib.Optimization.AffineQuadraticKKT

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
* `BenziGolubLiesen.IsGeneralizedSaddlePoint`: the classification by conditions C1–C5.
* `BenziGolubLiesen.quadraticObjective` and `BenziGolubLiesen.quadraticLagrangian`: the objective
  and Lagrangian for the quadratic problem (1.4)–(1.5).

## Main results

* `BenziGolubLiesen.isSaddlePoint_quadraticLagrangian_iff`: the block system (1.3) is equivalent
  to the Lagrangian saddle inequalities.
* `BenziGolubLiesen.quadraticLagrangian_minimax`: the two iterated extrema are equal at a solution.

## Implementation notes

* The matrix is indexed by `n ⊕ m`: the first $n$ coordinates belong to the block $A$, the last $m$
  coordinates to the block $C$.

## Deviations from the source

* **Section 1.1, quadratic Lagrangian saddle** (generalization). The source identifies
  block-system solutions as saddle points. The equivalence also gives the reverse implication.
  See `BenziGolubLiesen.isSaddlePoint_quadraticLagrangian_iff`.
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

variable [Fintype n] [Fintype m]

/-- **Section 1.1** of [benzi2005numerical]. A generalized saddle-point system has $m \le n$,
nonzero leading and coupling blocks, and satisfies at least one of C1–C5: symmetry of $A$,
positive semidefiniteness of its symmetric part, equality of the coupling blocks, positive
semidefiniteness of $C$, or $C = 0$, respectively. -/
def IsGeneralizedSaddlePoint (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ) (C : Matrix m m ℝ) : Prop :=
  Fintype.card m ≤ Fintype.card n ∧ A ≠ 0 ∧ B₁ ≠ 0 ∧ B₂ ≠ 0 ∧
    (Aᵀ = A ∨ ((1 / 2 : ℝ) • (A + Aᵀ)).PosSemidef ∨ B₁ = B₂ ∨ C.PosSemidef ∨ C = 0)

omit [Fintype m] in
/-- **Section 1.1** of [benzi2005numerical]. Condition C5 implies C4. -/
theorem conditionC4_of_C5 {C : Matrix m m ℝ} (hC : C = 0) : C.PosSemidef :=
  hC.symm ▸ PosSemidef.zero

/-- **Equations (1.1), (1.3) and (1.6)** of [benzi2005numerical], in block component form. -/
theorem saddlePointMatrix_mulVec_iff (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (C : Matrix m m ℝ) (x f : n → ℝ) (y g : m → ℝ) :
    saddlePointMatrix A B₁ B₂ C *ᵥ Sum.elim x y = Sum.elim f g ↔
      A *ᵥ x + B₁ᵀ *ᵥ y = f ∧ B₂ *ᵥ x - C *ᵥ y = g := by
  simp only [saddlePointMatrix, fromBlocks_mulVec, neg_mulVec, sub_eq_add_neg]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (.inl i), funext fun i => congrFun h (.inr i)⟩
  · rintro ⟨h₁, h₂⟩
    change Sum.elim (A *ᵥ x + B₁ᵀ *ᵥ y) (B₂ *ᵥ x + -(C *ᵥ y)) = Sum.elim f g
    rw [h₁, h₂]

/-- **Equation (1.4)** of [benzi2005numerical]. The quadratic objective is
$J(x)=\tfrac12 x^T A x - f^T x$. -/
noncomputable def quadraticObjective (A : Matrix n n ℝ) (f x : n → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / 2 - f ⬝ᵥ x

/-- **Section 1.1** of [benzi2005numerical]. The Lagrangian for (1.4)–(1.5) is
$\mathcal L(x,y)=J(x)+(Bx-g)^Ty$. -/
noncomputable def quadraticLagrangian (A : Matrix n n ℝ) (B : Matrix m n ℝ) (f : n → ℝ)
    (g : m → ℝ) (x : n → ℝ) (y : m → ℝ) : ℝ :=
  quadraticObjective A f x + (B *ᵥ x - g) ⬝ᵥ y

private theorem lagrangian_add {A : Matrix n n ℝ} (hA : Aᵀ = A) (B : Matrix m n ℝ)
    (f x d : n → ℝ) (g y : m → ℝ) :
    quadraticLagrangian A B f g (x + d) y = quadraticLagrangian A B f g x y +
      d ⬝ᵥ (A *ᵥ x + Bᵀ *ᵥ y - f) + (d ⬝ᵥ (A *ᵥ d)) / 2 := by
  have hcross : x ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ x) := by
    rw [← hA, dotProduct_transpose_mulVec, hA]
  simp only [quadraticLagrangian, quadraticObjective, mulVec_add, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, dotProduct_transpose_mulVec, hcross,
    dotProduct_comm y (B *ᵥ d), dotProduct_comm d f]
  ring

/-- **Section 1.1** of [benzi2005numerical]. With $A$ symmetric positive semidefinite, the
solutions of (1.3) are exactly the saddle points of the quadratic Lagrangian.

**Generalization.** The source states that each solution is a saddle point. The reverse
direction follows from the saddle inequalities by varying the multiplier to obtain
feasibility and varying the primal point to obtain stationarity.

The multiplier
is the first argument of `ConvexAnalysis.IsSaddlePoint`, which maximizes in that argument. -/
theorem isSaddlePoint_quadraticLagrangian_iff {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (B : Matrix m n ℝ) (f x : n → ℝ) (g y : m → ℝ) :
    ConvexAnalysis.IsSaddlePoint
      (fun q : (m → ℝ) × (n → ℝ) => (quadraticLagrangian A B f g q.2 q.1 : EReal)) (y, x) ↔
      saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g := by
  have hsym : Aᵀ = A := by simpa using hA.isHermitian.eq
  rw [saddlePointMatrix_mulVec_iff, zero_mulVec, sub_zero]
  constructor
  · rintro ⟨hmax, hmin⟩
    have hm : ∀ z, quadraticLagrangian A B f g x z ≤ quadraticLagrangian A B f g x y :=
      fun z => EReal.coe_le_coe_iff.mp (hmax z)
    let w := B *ᵥ x - g
    have hw := hm (y + w)
    simp only [quadraticLagrangian, dotProduct_add, ← show w = B *ᵥ x - g from rfl] at hw
    have hnonneg : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    have hzero : w = 0 := dotProduct_self_eq_zero.mp (le_antisymm (by linarith) hnonneg)
    refine ⟨sub_eq_zero.mp ?_, sub_eq_zero.mp hzero⟩
    let v := A *ᵥ x + Bᵀ *ᵥ y - f
    have hline (t : ℝ) : quadraticLagrangian A B f g (x + t • v) y =
        quadraticLagrangian A B f g x y + t * (v ⬝ᵥ v) + t ^ 2 * ((v ⬝ᵥ (A *ᵥ v)) / 2) := by
      rw [lagrangian_add hsym]
      change _ + (t • v) ⬝ᵥ v + ((t • v) ⬝ᵥ (A *ᵥ (t • v))) / 2 = _
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    apply dotProduct_self_eq_zero.mp
    apply LinearMap.linearCoeff_eq_zero_of_quadratic_nonneg (a := (v ⬝ᵥ (A *ᵥ v)) / 2)
    intro t
    have ht := EReal.coe_le_coe_iff.mp (hmin (x + t • v))
    change quadraticLagrangian A B f g x y ≤ quadraticLagrangian A B f g (x + t • v) y at ht
    rw [hline] at ht
    linarith only [ht]
  · rintro ⟨hf, hg⟩
    constructor
    · intro z
      simp [quadraticLagrangian, hg]
    · intro z
      have hdiff : x + (z - x) = z := by abel
      have h := lagrangian_add hsym B f x (z - x) g y
      rw [hdiff, hf, sub_self, dotProduct_zero, add_zero] at h
      have hq : 0 ≤ (z - x) ⬝ᵥ (A *ᵥ (z - x)) := by
        simpa using hA.dotProduct_mulVec_nonneg (z - x)
      exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **Equations (1.3)–(1.5)** of [benzi2005numerical]. The primal component of a solution of
the first-order system minimizes the quadratic objective on the affine constraint set. -/
theorem quadraticObjective_isMinOn_of_saddlePointSystem {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {B : Matrix m n ℝ} {f x : n → ℝ} {g y : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g) :
    x ∈ {z | B *ᵥ z = g} ∧ IsMinOn (quadraticObjective A f) {z | B *ᵥ z = g} x := by
  have hx : B *ᵥ x = g := by simpa using ((saddlePointMatrix_mulVec_iff A B B 0 x f y g).mp h).2
  refine ⟨hx, ?_⟩
  intro z hz
  change B *ᵥ z = g at hz
  have hmin := ((isSaddlePoint_quadraticLagrangian_iff hA B f x g y).mpr h).2 z
  simpa [quadraticLagrangian, hx, hz] using hmin

/-- **Section 1.1** of [benzi2005numerical]. The minimax and maximin values of the quadratic
Lagrangian coincide at every solution of (1.3). The iterated extrema are taken in `EReal` to
allow unbounded slices of the Lagrangian away from the solution. Equality of values alone does
not identify a saddle pair; see `ConvexAnalysis.isSaddlePoint_iff_attained` for the attainment
conditions in the converse. -/
theorem quadraticLagrangian_minimax {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {B : Matrix m n ℝ} {f x : n → ℝ} {g y : m → ℝ}
    (h : saddlePointMatrix A B B 0 *ᵥ Sum.elim x y = Sum.elim f g) :
    (⨅ z, ⨆ w, (quadraticLagrangian A B f g z w : EReal)) = quadraticLagrangian A B f g x y ∧
    (⨆ w, ⨅ z, (quadraticLagrangian A B f g z w : EReal)) = quadraticLagrangian A B f g x y := by
  have hs := (isSaddlePoint_quadraticLagrangian_iff hA B f x g y).mpr h
  exact ⟨hs.minimax_eq, hs.maximin_eq⟩

end BenziGolubLiesen
