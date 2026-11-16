/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Conn, Gould and Toint, Section 2.3: Vector and matrix norms

This module formalizes Section 2.3 of [conn2000trust]. The dual norm of a linear functional
$\varphi$ on a real normed space is $\|\varphi\|_D = \sup_{\|x\| \le 1} |\varphi(x)|$, and a
symmetric positive-definite matrix $H$ defines the energy norm $\|x\|_H = \sqrt{x^T H x}$. For a
matrix $A \in \mathbb{R}^{m \times n}$, the section compares the norms $\|A\|_p$ induced by the
vector $p$-norms for $p = 1, 2, \infty$ and the Frobenius norm $\|A\|_F$, and shows that these
matrix norms are consistent, that is, $\|AB\| \le \|A\| \|B\|$.

The proofs specialize the backbone modules `Numlib.Analysis.Matrix.OperatorNorm` and
`Numlib.Analysis.InnerProductSpace.Energy`.

## Main definitions

* Equation (2.3.1), `ConnGouldToint.Chapter02.dualNorm`: the dual norm of a real continuous linear
  functional.
* Equation (2.3.2), `ConnGouldToint.Chapter02.hNorm`: the energy norm $\|x\|_H$.
* Equation (2.3.5), `ConnGouldToint.Chapter02.IsConsistentMatrixNorm`: a family of matrix norms with
  $\|AB\| \le \|A\| \|B\|$.

## Main results

* Equation (2.3.1), `ConnGouldToint.Chapter02.dualNorm_eq_iSup`: the dual norm is the supremum of
  $|\varphi(x)|$ over the unit ball and the supremum of $|\varphi(x)| / \|x\|$ over $x \neq 0$.
* Equation (2.3.2), `ConnGouldToint.Chapter02.hNorm_eq_sqrt`: $\|x\|_H = \sqrt{x^T H x}$.
* Equation (2.3.3), `ConnGouldToint.Chapter02.matrix_norms_2_3_3`: the chain of comparisons between
  $\|A\|_\infty$, $\|A\|_2$ and $\|A\|_1$.
* Equation (2.3.4), `ConnGouldToint.Chapter02.frobenius_bounds_2_3_4`:
  $\|A\|_2 \le \|A\|_F \le \sqrt{n} \|A\|_2$.
* Equation (2.3.5), `ConnGouldToint.Chapter02.isConsistentMatrixNorm_lp`: the induced $p$-norms are
  consistent.
* Equation (2.3.5), `ConnGouldToint.Chapter02.isConsistentMatrixNorm_frobenius`: the Frobenius norm
  is consistent.
* Equation (2.3.6), `ConnGouldToint.Chapter02.symmetric_norms_2_3_6`: for symmetric $H$,
  $\|H\|_2 \le \|H\|_1 = \|H\|_\infty$.

## Conventions

* The induced norm $\|A\|_p$ is `Matrix.lpOpNorm p A`, with `p : ℝ≥0∞`. Thus $\|A\|_1$ is the
  largest column sum $\max_j \sum_i |a_{ij}|$, and $\|A\|_\infty$ is `Matrix.lpOpNorm ⊤ A`, the
  largest row sum $\max_i \sum_j |a_{ij}|$.
* The Frobenius norm $\|A\|_F$ is the norm `‖A‖` of the scoped instance `Matrix.Norms.Frobenius`.
-/

open scoped ENNReal Matrix.Norms.Frobenius
open Matrix

namespace ConnGouldToint.Chapter02

section Dual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Equation (2.3.1)** of [conn2000trust]. Let $E$ be a real normed space. The **dual norm** of a
continuous linear functional $\varphi : E \to \mathbb{R}$ is its operator norm
$$\|\varphi\|_D = \sup_{\|x\| \le 1} |\varphi(x)|.$$

In coordinates, the functional associated with a vector $x$ sends $y$ to $x^T y$. The definition
is the norm `‖φ‖` of `E →L[ℝ] ℝ`. -/
noncomputable abbrev dualNorm (φ : E →L[ℝ] ℝ) : ℝ := ‖φ‖

/-- **Equation (2.3.1)** of [conn2000trust]. Let $E$ be a real normed space, and let
$\varphi : E \to \mathbb{R}$ be a continuous linear functional. Then
$$\|\varphi\|_D = \sup_{\|x\| \le 1} |\varphi(x)| \quad \text{and} \quad \|\varphi\|_D = \sup_{x
  \neq 0} \frac{|\varphi(x)|}{\|x\|}.$$

The suprema are `iSup` over the subtypes $\{x : \|x\| \le 1\}$ and $\{x : x \neq 0\}$. When
$E = 0$ the second subtype is empty; its supremum is then $0$, by the Lean convention
$\sup \emptyset = 0$ for real numbers, and $\|\varphi\|_D = 0$ as well. -/
theorem dualNorm_eq_iSup (φ : E →L[ℝ] ℝ) :
    dualNorm φ = (⨆ x : {x : E // ‖x‖ ≤ 1}, |φ x|) ∧
      dualNorm φ = ⨆ x : {x : E // x ≠ 0}, |φ x| / ‖(x : E)‖ := by
  constructor
  · let a (x : {x : E // ‖x‖ ≤ 1}) := |φ x|
    have ha : ∀ x, a x ≤ ‖φ‖ := fun x => by
      change |φ x| ≤ ‖φ‖
      rw [← Real.norm_eq_abs]
      exact (φ.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg φ) x.property)
    refine le_antisymm (ContinuousLinearMap.opNorm_le_of_unit_norm
      (Real.iSup_nonneg fun x => abs_nonneg (φ x)) fun x hx => ?_) (Real.iSup_le ha (norm_nonneg _))
    rw [Real.norm_eq_abs]
    exact le_ciSup ⟨‖φ‖, Set.forall_mem_range.2 ha⟩ ⟨x, hx.le⟩
  · let a (x : {x : E // x ≠ 0}) := |φ x| / ‖(x : E)‖
    have ha : ∀ x, a x ≤ ‖φ‖ := fun x =>
      (div_le_iff₀ (norm_pos_iff.2 x.property)).2 (by
        simpa [Real.norm_eq_abs] using φ.le_opNorm x)
    refine le_antisymm (φ.opNorm_le_bound' (Real.iSup_nonneg fun x =>
      div_nonneg (abs_nonneg _) (norm_nonneg _)) fun x hx => ?_)
      (Real.iSup_le ha (norm_nonneg _))
    rw [Real.norm_eq_abs]
    have hx' := norm_ne_zero_iff.1 hx
    exact (div_le_iff₀ (norm_pos_iff.2 hx')).1
      (le_ciSup ⟨‖φ‖, Set.forall_mem_range.2 ha⟩ ⟨x, hx'⟩)

end Dual

variable {m n k : ℕ}

/-- **Equation (2.3.2)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. The **$H$-norm** of $x \in \mathbb{R}^n$ is the energy norm
$\|x\|_H = \sqrt{\langle Hx, x \rangle}$.

The definition is `energyNorm` of `Matrix.toEuclideanLin H`. The positive definiteness is an
argument that the formula does not use. -/
noncomputable abbrev hNorm (H : Matrix (Fin n) (Fin n) ℝ) (_ : H.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm H.toEuclideanLin x

/-- **Equation (2.3.2)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, and let $x \in \mathbb{R}^n$. Then $\|x\|_H = \sqrt{x^T H x}$. -/
theorem hNorm_eq_sqrt (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    hNorm H hH x = √(WithLp.ofLp x ⬝ᵥ (H *ᵥ WithLp.ofLp x)) := by
  simp [hNorm, energyNorm, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin_apply]

/-- **Equation (2.3.3)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$. Then the induced
norms satisfy the chain
$$\|A\|_\infty \le \sqrt{n} \|A\|_2 \le n \|A\|_1 \le n \sqrt{m} \|A\|_2 \le n m \|A\|_\infty.$$

Each step is a comparison of two of the norms: $\|A\|_\infty \le \sqrt{n} \|A\|_2$,
$\|A\|_2 \le \sqrt{n} \|A\|_1$, $\|A\|_1 \le \sqrt{m} \|A\|_2$ and
$\|A\|_2 \le \sqrt{m} \|A\|_\infty$. -/
theorem matrix_norms_2_3_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm ⊤ A ≤ √(n : ℝ) * lpOpNorm 2 A ∧
    √(n : ℝ) * lpOpNorm 2 A ≤ n * lpOpNorm 1 A ∧
    (n : ℝ) * lpOpNorm 1 A ≤ n * √(m : ℝ) * lpOpNorm 2 A ∧
    (n : ℝ) * √(m : ℝ) * lpOpNorm 2 A ≤ n * m * lpOpNorm ⊤ A := by
  obtain ⟨hi₂, h₂i⟩ := A.l2_opNorm_le_sqrt_card_mul_linfty_opNorm
  obtain ⟨h₁₂, h₂₁⟩ := A.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one
  simp only [Fintype.card_fin] at hi₂ h₂i h₁₂ h₂₁
  refine ⟨h₂i, ?_, ?_, ?_⟩
  · simpa only [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)] using
      mul_le_mul_of_nonneg_left h₂₁ (Real.sqrt_nonneg n)
  · simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left h₁₂ (Nat.cast_nonneg n)
  · simpa only [← mul_assoc, mul_assoc (n : ℝ) (√(m : ℝ)) (√(m : ℝ)),
      Real.mul_self_sqrt (Nat.cast_nonneg m)] using
      mul_le_mul_of_nonneg_left hi₂ (by positivity : 0 ≤ (n : ℝ) * √(m : ℝ))

/-- **Equation (2.3.4)** of [conn2000trust]. Let $A \in \mathbb{R}^{m \times n}$. Then
$$\|A\|_2 \le \|A\|_F \le \sqrt{n} \|A\|_2.$$
-/
theorem frobenius_bounds_2_3_4 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ ‖A‖ ∧ ‖A‖ ≤ √(n : ℝ) * lpOpNorm 2 A :=
  ⟨A.l2_opNorm_le_frobenius_norm,
    A.frobenius_norm_le_sqrt_rank_mul_l2_opNorm.trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast A.rank_le_width))
        (lpOpNorm_nonneg _ _))⟩

/-- **Equation (2.3.5)** of [conn2000trust]. A family $N$ of functions on real matrices of all
shapes is a **consistent matrix norm** if
$$N(AB) \le N(A) N(B)$$
for all $A \in \mathbb{R}^{m \times n}$ and $B \in \mathbb{R}^{n \times k}$, for all $m$, $n$
and $k$.

The predicate asks only for the submultiplicative inequality. It does not ask that each $N$ be a
norm. -/
def IsConsistentMatrixNorm (N : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  ∀ {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ),
    N (A * B) ≤ N A * N B

/-- **Equation (2.3.5)** of [conn2000trust], induced norms. For every $p \in [1, \infty]$, the
induced matrix norms $\|\cdot\|_p$ form a consistent matrix norm:
$\|AB\|_p \le \|A\|_p \|B\|_p$. -/
theorem isConsistentMatrixNorm_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsConsistentMatrixNorm (fun A => lpOpNorm p A) :=
  fun A B => lpOpNorm_mul_le p A B

/-- **Equation (2.3.5)** of [conn2000trust], Frobenius norm. The Frobenius norm is a consistent
matrix norm: $\|AB\|_F \le \|A\|_F \|B\|_F$. -/
theorem isConsistentMatrixNorm_frobenius :
    IsConsistentMatrixNorm (fun A => ‖A‖) := by
  intro m n k A B
  exact (frobenius_norm_mul_le_lpOpNorm_two_mul A B).trans
    (mul_le_mul_of_nonneg_right A.l2_opNorm_le_frobenius_norm (norm_nonneg B))

/-- **Equation (2.3.6)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric. Then
$$\|H\|_2 \le \|H\|_1 = \|H\|_\infty.$$
-/
theorem symmetric_norms_2_3_6 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    lpOpNorm 2 H ≤ lpOpNorm 1 H ∧ lpOpNorm 1 H = lpOpNorm ⊤ H := by
  have h : H.IsHermitian := by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hH
  have he : lpOpNorm 1 H = lpOpNorm ⊤ H :=
    h.lpOpNorm_one_eq_linfty_opNorm.trans (lpOpNorm_top H).symm
  exact ⟨h.l2_opNorm_le_linfty_opNorm.trans_eq he.symm, he⟩

end ConnGouldToint.Chapter02
