/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Block
import Numlib.Stationary.Splitting
import Numlib.Stationary.Sweep
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 4.1: Jacobi, Gauss–Seidel and SOR

This module formalizes §4.1 of [saad2003iterative], the basic relaxation methods for a linear system
$Ax = b$ with $A \in \mathbb{R}^{n \times n}$. The matrix is split as $A = D - E - F$ (4.2), where
$D$ is the diagonal of $A$, $-E$ its strict lower triangular part and $-F$ its strict upper
triangular part. The module defines the Jacobi step (4.3)–(4.5), the forward, backward and symmetric
Gauss–Seidel steps (4.6)–(4.9), and the SOR and SSOR steps (4.11)–(4.14). It shows that each of them
is the step $x \mapsto x + M^{-1}(b - Ax)$ of a splitting $A = M - N$ (4.18)–(4.23), and it
identifies the preconditioners $M_{JA}$, $M_{GS}$, $M_{SOR}$ and $M_{SSOR}$ of (4.24)–(4.27).

The last part treats block relaxation (§4.1.1, (4.15)–(4.17), Algorithms 4.1–4.2) for
non-overlapping blocks. The blocks are the fibres of a labelling
$\pi : \{1, \dots, n\} \to \{1, \dots, p\}$, and $D$, $E$, $F$ have block analogues. One block
Jacobi sweep is one step of the additive projection process over the blocks, and one block
Gauss–Seidel sweep is one sweep of the multiplicative projection process, as in §5.4. The proofs
specialize `Numlib.Stationary.Splitting`, `Numlib.Stationary.Sweep` and `Numlib.Stationary.Block`.

## Main definitions

* Equation (4.2), `SaadSparse.Chapter04.D`, `SaadSparse.Chapter04.E`, `SaadSparse.Chapter04.F`: the
  diagonal part and the negated strict lower and strict upper parts of $A$.
* Equation (4.4), `SaadSparse.Chapter04.jacobiStep`: the Jacobi step $x'_i = (b_i - \sum_{j \neq i}
  a_{ij} x_j)/a_{ii}$.
* Equation (4.8), `SaadSparse.Chapter04.gsStep`: the Gauss–Seidel step $x' = (D - E)^{-1}(Fx + b)$.
* Equation (4.9), `SaadSparse.Chapter04.backwardGsStep`: the backward Gauss–Seidel step
  $x' = (D - F)^{-1}(Ex + b)$.
* §4.1, `SaadSparse.Chapter04.symmetricGsStep`: a forward Gauss–Seidel step followed by a backward
  one.
* Equation (4.12), `SaadSparse.Chapter04.sorStep`: the SOR step with relaxation parameter $\omega$.
* §4.1, `SaadSparse.Chapter04.backwardSORStep` and `SaadSparse.Chapter04.ssorStep`: the backward SOR
  step, and a forward SOR step followed by a backward one.
* Equations (4.13)–(4.14), `SaadSparse.Chapter04.G_ssor` and `SaadSparse.Chapter04.f_ssor`: the SSOR
  iteration matrix $G_\omega$ and right-hand side $f_\omega$.
* Equations (4.15)–(4.16), `SaadSparse.Chapter04.blockD`, `SaadSparse.Chapter04.blockE`,
  `SaadSparse.Chapter04.blockF`: the block diagonal part and the negated strict block lower and
  upper parts of $A$.
* Equations (4.18) and (4.22), `SaadSparse.Chapter04.affineStep` and
  `SaadSparse.Chapter04.Splitting.step`: the affine step $x \mapsto Gx + f$, and the step
  $x \mapsto Gx + M^{-1} b$ of a splitting.
* Equation (4.26), `SaadSparse.Chapter04.M_sor`: the SOR preconditioner
  $M_{SOR} = \omega^{-1}(D - \omega E)$.
* Equation (4.27), `SaadSparse.Chapter04.M_ssor`: the SSOR preconditioner $M_{SSOR} = (\omega(2 -
  \omega))^{-1}(D - \omega E) D^{-1} (D - \omega F)$.
* Algorithms 4.1 and 4.2, `SaadSparse.Chapter04.blockJacobiStep` and
  `SaadSparse.Chapter04.blockGaussSeidelStep`: one block Jacobi sweep and one block Gauss–Seidel
  sweep, for non-overlapping blocks.

## Main results

* Equation (4.5), `SaadSparse.Chapter04.jacobiStep_eq`: the Jacobi step is the step of the splitting
  with $M = D$.
* Equations (4.8)–(4.9), `SaadSparse.Chapter04.gsStep_eq` and
  `SaadSparse.Chapter04.backwardGsStep_eq`: Gauss–Seidel is the splitting with $M = D - E$, backward
  Gauss–Seidel the splitting with $M = D - F$.
* Equation (4.12), `SaadSparse.Chapter04.sorStep_eq`: SOR is the splitting with
  $M = \omega^{-1}(D - \omega E)$.
* Equations (4.13)–(4.14), `SaadSparse.Chapter04.ssorStep_eq_affine`: the SSOR step is
  $x \mapsto G_\omega x + f_\omega$.
* Equation (4.17), `SaadSparse.Chapter04.equation_4_17`: the block Jacobi sweep is
  $x' = x + D^{-1}(b - Ax)$ with $D$ the block diagonal.
* Equations (4.24)–(4.27), `SaadSparse.Chapter04.M_JA_eq`, `SaadSparse.Chapter04.M_GS_eq`,
  `SaadSparse.Chapter04.M_sor_eq`, `SaadSparse.Chapter04.M_ssor_eq`,
  `SaadSparse.Chapter04.ssorStep_eq`: the preconditioners of the Jacobi, Gauss–Seidel, SOR and SSOR
  splittings.
* Algorithms 4.1 and 4.2, `SaadSparse.Chapter04.blockJacobiStep_eq` and
  `SaadSparse.Chapter04.blockGaussSeidelStep_eq`: the block sweeps are the steps of the splittings
  with $M = D$ and $M = D - E$ for the block parts.
* §5.4, `SaadSparse.Chapter04.blockJacobiStep_eq_additiveStep` and
  `SaadSparse.Chapter04.blockGaussSeidelStep_eq_multiplicativeStep`: the block sweeps are the
  additive and the multiplicative projection processes over the blocks.

## Implementation notes

* A splitting is `Stationary.Splitting A`, a nonsingular matrix $M$; the complementary part is
  $N = M - A$. The theorems that identify a step with a splitting need $D$ nonsingular, which is
  `IsUnit (diagPart A)`.
* The steps are defined by explicit formulas with the matrix inverse of Mathlib, which is $0$ at a
  singular matrix. The defining equations of the steps (for example
  `SaadSparse.Chapter04.gsStep_spec`) need the nonsingularity of the matrix that is inverted.
* The steps act on plain vectors `Fin n → ℝ` with `Matrix.mulVec`. The block results of §5.4 pass to
  `EuclideanSpace ℝ (Fin n)` through `WithLp.toLp 2`.

## Not formalized

* **Algorithm 4.1 with overlapping blocks.** The book proves no theorem about the overlapping case.
-/

open Matrix Finset Stationary

namespace SaadSparse.Chapter04

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ} {ω : ℝ}

/-! ### The splitting $A = D - E - F$ (4.2) -/

/-- **Equation (4.2)** of [saad2003iterative]. The **diagonal part** $D$ of
$A \in \mathbb{R}^{n \times n}$ is the diagonal matrix with the diagonal entries $a_{ii}$ of
$A$. -/
def D (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := diagPart A

/-- **Equation (4.2)** of [saad2003iterative]. The matrix $E$ is the negative of the **strict lower
triangular part** of $A \in \mathbb{R}^{n \times n}$: $e_{ij} = -a_{ij}$ for $i > j$, and
$e_{ij} = 0$ otherwise. -/
def E (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictLower A

/-- **Equation (4.2)** of [saad2003iterative]. The matrix $F$ is the negative of the **strict upper
triangular part** of $A \in \mathbb{R}^{n \times n}$: $f_{ij} = -a_{ij}$ for $i < j$, and
$f_{ij} = 0$ otherwise. -/
def F (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictUpper A

/-- Equation (4.2) of [saad2003iterative]: every $A \in \mathbb{R}^{n \times n}$ satisfies
$A = D - E - F$. -/
theorem decomp (A : Matrix (Fin n) (Fin n) ℝ) : A = D A - E A - F A :=
  (diagPart_sub_neg_strictLower_sub_neg_strictUpper A).symm

/-- The matrix $D - E$ is the lower triangular part of $A$, including the diagonal. -/
theorem D_sub_E (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = diagPart A + strictLower A := by
  rw [D, E, sub_neg_eq_add]

/-- The matrix $D - F$ is the upper triangular part of $A$, including the diagonal. -/
theorem D_sub_F (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = diagPart A + strictUpper A := by
  rw [D, F, sub_neg_eq_add]

/-- If the diagonal $D$ of $A$ is nonsingular, then the lower triangular matrix $D - E$ is
nonsingular. -/
theorem isUnit_D_sub_E (h : IsUnit (diagPart A)) : IsUnit (D A - E A) := by
  rw [D_sub_E]; exact isUnit_diagPart_add_strictLower h

/-- If the diagonal $D$ of $A$ is nonsingular, then the upper triangular matrix $D - F$ is
nonsingular. -/
theorem isUnit_D_sub_F (h : IsUnit (diagPart A)) : IsUnit (D A - F A) := by
  rw [D_sub_F]; exact isUnit_diagPart_add_strictUpper h

/-- For every $A$, $E + F = D - A$. -/
theorem E_add_F (A : Matrix (Fin n) (Fin n) ℝ) : E A + F A = D A - A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-- For every $A$, $D - E = A + F$. -/
theorem D_sub_E_eq (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = A + F A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-- For every $A$, $D - F = A + E$. -/
theorem D_sub_F_eq (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = A + E A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-! ### Componentwise formulas for the matrix–vector products -/

/-- For every vector $y$, $(Dy)_i = a_{ii} y_i$. -/
@[simp]
theorem D_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (D A *ᵥ y) i = A i i * y i := by
  simp [D, mulVec, dotProduct, ite_mul]

/-- For every vector $y$, $(Ey)_i = -\sum_{j < i} a_{ij} y_j$. -/
theorem E_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (E A *ᵥ y) i = -∑ j ∈ univ.filter (· < i), A i j * y j := by
  simp [E, mulVec, dotProduct, ite_mul, Finset.sum_filter]

/-- For every vector $y$, $(Fy)_i = -\sum_{j > i} a_{ij} y_j$. -/
theorem F_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (F A *ᵥ y) i = -∑ j ∈ univ.filter (i < ·), A i j * y j := by
  simp [F, mulVec, dotProduct, ite_mul, Finset.sum_filter]

/-- For every vector $y$, $(Ay)_i = a_{ii} y_i + \sum_{j \neq i} a_{ij} y_j$. -/
theorem mulVec_eq_sum_erase (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ y) i = A i i * y i + ∑ j ∈ univ.erase i, A i j * y j := by
  rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (mem_univ i)]

/-!
### Elementary facts about matrix inverses

The cancellations $M^{-1}(Mu) = u$ and $M(M^{-1}u) = u$, and the fact that $Mv = u$ gives
$v = M^{-1}u$, are `Matrix.nonsing_inv_mulVec_mulVec`, `Matrix.mulVec_nonsing_inv_mulVec` and
`Matrix.nonsing_inv_mulVec_eq`.
-/

private theorem isUnit_smul_of_isUnit {c : ℝ} (hc : c ≠ 0) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUnit M) : IsUnit (c • M) := by
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp hM))

/-! ### General splittings and the affine iteration (4.10)–(4.11), (4.18)–(4.23) -/

/-- **Section 4.2** of [saad2003iterative], splittings. A **splitting** $A = M - N$ of
$A \in \mathbb{R}^{n \times n}$ is given by a nonsingular matrix $M$; the complementary part is
$N = M - A$.

This is `Stationary.Splitting A`, with $M$ the field `Stationary.Splitting.m` and $N$ the
definition `Stationary.Splitting.n`. -/
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Stationary.Splitting A

/-- **Equations (4.18) and (4.28)** of [saad2003iterative]. For $G \in \mathbb{R}^{n \times n}$ and
$f \in \mathbb{R}^n$, the **affine step** is the map $x \mapsto Gx + f$. -/
def affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) : Fin n → ℝ := G *ᵥ x + f

/-- **Equation (4.22)** of [saad2003iterative]. The **step** of a splitting $A = M - N$ with
right-hand side $b$ is the affine map
$$x \mapsto Gx + M^{-1}b, \qquad G = I - M^{-1}A = M^{-1}N.$$

The matrix $G$ is `Stationary.Splitting.iterationOperator`. -/
noncomputable def Splitting.step (s : Splitting A) (b : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  affineStep s.iterationOperator (s.m⁻¹ *ᵥ b)

/-- §4.2 of [saad2003iterative]: one step of a splitting is $x \mapsto x + M^{-1}r$, where
$r = b - Ax$ is the residual. -/
theorem Splitting.step_eq (s : Splitting A) (b x : Fin n → ℝ) :
    Splitting.step s b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) := by
  have hG : s.iterationOperator = 1 - s.m⁻¹ * A := by
    rw [Stationary.Splitting.iterationOperator, nonsing_inv_eq_ringInverse]
  rw [Splitting.step, affineStep, hG, sub_mulVec, one_mulVec, mulVec_sub, ← mulVec_mulVec]
  abel

/-- The step of a splitting is characterized by $M(x' - x) = b - Ax$: if $y$ satisfies
$M(y - x) = b - Ax$, then $y$ is the step from $x$. -/
theorem Splitting.step_eq_of_mulVec (s : Splitting A) (b x y : Fin n → ℝ)
    (h : s.m *ᵥ (y - x) = b - A *ᵥ x) : Splitting.step s b x = y := by
  rw [Splitting.step_eq, nonsing_inv_mulVec_eq s.isUnit h]
  abel

/-- Equation (4.20) of [saad2003iterative]: the iteration operator of a splitting is
$G = I - M^{-1}A$. -/
theorem iterationOperator_eq_one_sub (s : Splitting A) :
    s.iterationOperator = 1 - s.m⁻¹ * A := by
  rw [Stationary.Splitting.iterationOperator, nonsing_inv_eq_ringInverse]

/-- Equation (4.29) of [saad2003iterative], §4.2.1: a vector $x$ is a fixed point of the step of a
splitting if and only if $Ax = b$. -/
theorem step_fixed_iff (s : Splitting A) (b x : Fin n → ℝ) :
    Splitting.step s b x = x ↔ A *ᵥ x = b := by
  rw [Splitting.step_eq]
  constructor
  · intro h
    have h0 : s.m⁻¹ *ᵥ (b - A *ᵥ x) = 0 := by
      have := congrArg (fun z => z - x) h
      simpa using this
    have := congrArg (fun z => s.m *ᵥ z) h0
    simp only [mulVec_nonsing_inv_mulVec s.isUnit, mulVec_zero] at this
    have hx := sub_eq_zero.mp this
    exact hx.symm
  · intro h
    rw [h, sub_self, mulVec_zero, add_zero]

/-- §4.1.2 of [saad2003iterative]: for a nonsingular $M$, the preconditioned system
$M^{-1}Ax = M^{-1}b$ has the same solutions as $Ax = b$. -/
theorem preconditioned_iff {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M)
    (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M⁻¹ *ᵥ (A *ᵥ x) = M⁻¹ *ᵥ b ↔ A *ᵥ x = b := by
  constructor
  · intro h
    have := congrArg (fun z => M *ᵥ z) h
    simpa only [mulVec_nonsing_inv_mulVec hM] using this
  · intro h; rw [h]

/-! ### Jacobi (4.3)–(4.5) -/

/-- **Equation (4.4)** of [saad2003iterative]. The **Jacobi step** from $x$ is the vector $x'$ with
$$x'_i = \frac{1}{a_{ii}} \Big( b_i - \sum_{j \neq i} a_{ij} x_j \Big), \qquad i = 1, \dots,
  n.$$
It annihilates the $i$-th component of the residual while all other components of $x$ keep their
previous values.

If $a_{ii} = 0$, the component $x'_i$ is $0$, because division by zero is zero in Lean. -/
noncomputable def jacobiStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i

/-- Equation (4.3) of [saad2003iterative]: if every $a_{ii} \neq 0$, the Jacobi step satisfies
$a_{ii} x'_i + \sum_{j \neq i} a_{ij} x_j = b_i$ for every $i$. -/
theorem jacobiStep_spec (hd : ∀ i, A i i ≠ 0) (b x : Fin n → ℝ) (i : Fin n) :
    A i i * jacobiStep A b x i + ∑ j ∈ univ.erase i, A i j * x j = b i := by
  rw [jacobiStep, mul_div_cancel₀ _ (hd i)]
  abel

/-- §4.1 of [saad2003iterative]: if every $a_{ii} \neq 0$, the Jacobi step in residual form is
$x'_i = x_i + (b - Ax)_i / a_{ii}$, that is $x' = x + D^{-1}(b - Ax)$. -/
theorem jacobiStep_apply (hd : ∀ i, A i i ≠ 0) (b x : Fin n → ℝ) (i : Fin n) :
    jacobiStep A b x i = x i + (b i - (A *ᵥ x) i) / A i i := by
  have hi : A i i ≠ 0 := hd i
  have key : b i - (A i i * x i + ∑ j ∈ univ.erase i, A i j * x j)
      = (b i - ∑ j ∈ univ.erase i, A i j * x j) - A i i * x i := by ring
  rw [jacobiStep, mulVec_eq_sum_erase, eq_comm, key, sub_div, mul_div_cancel_left₀ _ hi]
  ring

/-- Equation (4.5) of [saad2003iterative]: if $D$ is nonsingular, the Jacobi step is the step of the
splitting with $M = D$, `Matrix.jacobiSplitting`. -/
theorem jacobiStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    jacobiStep A b = Splitting.step (jacobiSplitting A h) b := by
  have hd := (isUnit_diagPart_iff A).mp h
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (jacobiSplitting A h).m = D A := rfl
  funext i
  have hspec := jacobiStep_spec hd b x i
  have hA := mulVec_eq_sum_erase A x i
  rw [hm]
  simp only [Pi.sub_apply, D_mulVec]
  rw [hA, mul_sub]
  linarith

/-- Equation (4.5) of [saad2003iterative]: if $D$ is nonsingular, the Jacobi step in matrix form is
$x' = D^{-1}(E + F)x + D^{-1}b$. -/
theorem jacobiStep_eq_vec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    jacobiStep A b x = (D A)⁻¹ *ᵥ ((E A + F A) *ᵥ x) + (D A)⁻¹ *ᵥ b := by
  have hD : IsUnit (D A) := h
  rw [jacobiStep_eq h, Splitting.step_eq]
  have hm : (jacobiSplitting A h).m = D A := rfl
  rw [hm, E_add_F, sub_mulVec, mulVec_sub, mulVec_sub, nonsing_inv_mulVec_mulVec hD]
  abel

/-! ### Gauss–Seidel (4.6)–(4.9) -/

/-- **Equation (4.8)** of [saad2003iterative]. The **Gauss–Seidel step** from $x$ is
$$x' = (D - E)^{-1}(Fx + b).$$
-/
noncomputable def gsStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - E A)⁻¹ *ᵥ (F A *ᵥ x + b)

/-- **Equation (4.9)** of [saad2003iterative]. The **backward Gauss–Seidel step** from $x$ is
$$x' = (D - F)^{-1}(Ex + b).$$
-/
noncomputable def backwardGsStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - F A)⁻¹ *ᵥ (E A *ᵥ x + b)

/-- **Section 4.1** of [saad2003iterative], symmetric Gauss–Seidel. The **symmetric Gauss–Seidel
step** is a forward Gauss–Seidel step followed by a backward Gauss–Seidel step. -/
noncomputable def symmetricGsStep (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := backwardGsStep A b ∘ gsStep A b

/-- Equation (4.6) of [saad2003iterative]: if $D$ is nonsingular, the Gauss–Seidel step solves
$(D - E)x' = Fx + b$. -/
theorem gsStep_spec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (D A - E A) *ᵥ gsStep A b x = F A *ᵥ x + b :=
  mulVec_nonsing_inv_mulVec (isUnit_D_sub_E h) _

/-- Equation (4.9) of [saad2003iterative]: if $D$ is nonsingular, the backward Gauss–Seidel step
solves $(D - F)x' = Ex + b$. -/
theorem backwardGsStep_spec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (D A - F A) *ᵥ backwardGsStep A b x = E A *ᵥ x + b :=
  mulVec_nonsing_inv_mulVec (isUnit_D_sub_F h) _

/-- Equation (4.7) of [saad2003iterative]: if $D$ is nonsingular, the Gauss–Seidel step satisfies
the componentwise recursion
$$x'_i = \frac{1}{a_{ii}} \Big( -\sum_{j < i} a_{ij} x'_j - \sum_{j > i} a_{ij} x_j + b_i
  \Big),$$
which uses the components $x'_j$, $j < i$, that are already updated. -/
theorem gsStep_apply (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) (i : Fin n) :
    gsStep A b x i =
      (-(∑ j ∈ univ.filter (· < i), A i j * gsStep A b x j)
        - ∑ j ∈ univ.filter (i < ·), A i j * x j + b i) / A i i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hspec := congrFun (gsStep_spec h b x) i
  rw [sub_mulVec, Pi.sub_apply, D_mulVec, E_mulVec, Pi.add_apply, F_mulVec] at hspec
  rw [eq_div_iff hi]
  linarith

/-- §4.1 of [saad2003iterative]: if $D$ is nonsingular, the backward Gauss–Seidel step satisfies
$x'_i = \big( -\sum_{j > i} a_{ij} x'_j - \sum_{j < i} a_{ij} x_j + b_i \big) / a_{ii}$. -/
theorem backwardGsStep_apply (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) (i : Fin n) :
    backwardGsStep A b x i =
      (-(∑ j ∈ univ.filter (i < ·), A i j * backwardGsStep A b x j)
        - ∑ j ∈ univ.filter (· < i), A i j * x j + b i) / A i i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hspec := congrFun (backwardGsStep_spec h b x) i
  rw [sub_mulVec, Pi.sub_apply, D_mulVec, F_mulVec, Pi.add_apply, E_mulVec] at hspec
  rw [eq_div_iff hi]
  linarith

/-- Equation (4.8) of [saad2003iterative]: if $D$ is nonsingular, the Gauss–Seidel step is the step
of the splitting with $M = D - E$, `Matrix.gaussSeidelSplitting`. -/
theorem gsStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    gsStep A b = Splitting.step (gaussSeidelSplitting A h) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (gaussSeidelSplitting A h).m = D A - E A := (D_sub_E A).symm
  rw [hm, mulVec_sub, gsStep_spec h b x, D_sub_E_eq, add_mulVec]
  abel

/-- Equation (4.9) of [saad2003iterative]: if $D$ is nonsingular, the backward Gauss–Seidel step is
the step of the splitting with $M = D - F$, `Matrix.backwardGaussSeidelSplitting`. -/
theorem backwardGsStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    backwardGsStep A b = Splitting.step (backwardGaussSeidelSplitting A h) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (backwardGaussSeidelSplitting A h).m = D A - F A := (D_sub_F A).symm
  rw [hm, mulVec_sub, backwardGsStep_spec h b x, D_sub_F_eq, add_mulVec]
  abel

/-! ### SOR and SSOR (4.11)–(4.14) -/

/-- **Equation (4.12)** of [saad2003iterative]. The **SOR step** with relaxation parameter
$\omega \in \mathbb{R}$ from $x$ is
$$x' = (D - \omega E)^{-1} \big( (\omega F + (1 - \omega) D) x + \omega b \big).$$
-/
noncomputable def sorStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - ω • E A)⁻¹ *ᵥ ((ω • F A + (1 - ω) • D A) *ᵥ x + ω • b)

/-- **Section 4.1** of [saad2003iterative], backward SOR. The **backward SOR step** with parameter
$\omega$ from $x$ is
$$x' = (D - \omega F)^{-1} \big( (\omega E + (1 - \omega) D) x + \omega b \big).$$
-/
noncomputable def backwardSORStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Fin n → ℝ :=
  (D A - ω • F A)⁻¹ *ᵥ ((ω • E A + (1 - ω) • D A) *ᵥ x + ω • b)

/-- **Section 4.1** of [saad2003iterative], SSOR. The **SSOR step** with parameter $\omega$ is a
forward SOR step followed by a backward SOR step. -/
noncomputable def ssorStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := backwardSORStep A ω b ∘ sorStep A ω b

/-- Equation (4.11) of [saad2003iterative]: $\omega A = (D - \omega E) - (\omega F + (1 - \omega)
D)$ for every $\omega$. -/
theorem omega_smul_decomp (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    ω • A = (D A - ω • E A) - (ω • F A + (1 - ω) • D A) := by
  conv_lhs => rw [decomp A]
  module

/-- The backward form of equation (4.11) of [saad2003iterative]: $\omega A = (D - \omega F) -
(\omega E + (1 - \omega) D)$ for every $\omega$. -/
theorem omega_smul_decomp' (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    ω • A = (D A - ω • F A) - (ω • E A + (1 - ω) • D A) := by
  conv_lhs => rw [decomp A]
  module

/-- If $D$ is nonsingular and $\omega \neq 0$, then $D - \omega E$ is nonsingular. -/
theorem isUnit_D_sub_smul_E (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    IsUnit (D A - ω • E A) := by
  have hm : D A - ω • E A = ω • (ω⁻¹ • diagPart A + strictLower A) := by
    rw [D, E, smul_neg, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  rw [hm]
  exact isUnit_smul_of_isUnit hω (sorSplitting A h hω).isUnit

/-- If $D$ is nonsingular and $\omega \neq 0$, then $D - \omega F$ is nonsingular. -/
theorem isUnit_D_sub_smul_F (h : IsUnit (diagPart A)) (_hω : ω ≠ 0) :
    IsUnit (D A - ω • F A) := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hm : D A - ω • F A = diagPart A + ω • strictUpper A := by
    rw [D, F, smul_neg, sub_neg_eq_add]
  have hut : (diagPart A + ω • strictUpper A).IsUpperTriangular := by
    intro i j hij
    have hji : j < i := hij
    simp [hji.ne', asymm hji]
  rw [hm, isUnit_iff_isUnit_det, det_of_isUpperTriangular hut, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa using hd i

/-- Equation (4.12) of [saad2003iterative]: if $D$ is nonsingular and $\omega \neq 0$, the SOR step
solves $(D - \omega E)x' = (\omega F + (1 - \omega) D)x + \omega b$. -/
theorem sorStep_spec (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • E A) *ᵥ sorStep A ω b x = (ω • F A + (1 - ω) • D A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_D_sub_smul_E h hω) _

/-- §4.1 of [saad2003iterative]: if $D$ is nonsingular and $\omega \neq 0$, the backward SOR step
solves $(D - \omega F)x' = (\omega E + (1 - \omega) D)x + \omega b$. -/
theorem backwardSORStep_spec (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • F A) *ᵥ backwardSORStep A ω b x = (ω • E A + (1 - ω) • D A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_D_sub_smul_F h hω) _

/-- §4.1 of [saad2003iterative]: SOR with $\omega = 1$ is Gauss–Seidel. -/
theorem sorStep_one (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    sorStep A 1 b = gsStep A b := by
  funext x
  simp [sorStep, gsStep]

/-- The SOR step is the SOR sweep `Matrix.sorSweep` of the backbone, which is written with $L = -E$
and $U = -F$: $D - \omega E = D + \omega L$ and $\omega F + (1 - \omega) D = (1 - \omega) D -
\omega U$. -/
theorem sorStep_eq_sorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ) :
    sorStep A ω b = sorSweep A ω b := by
  funext x
  simp only [sorStep, sorSweep, D, E, F, smul_neg, sub_neg_eq_add, neg_add_eq_sub]

/-- The backward SOR step is the backward SOR sweep `Matrix.backwardSorSweep` of the backbone. -/
theorem backwardSORStep_eq_backwardSorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ)
    (b : Fin n → ℝ) : backwardSORStep A ω b = backwardSorSweep A ω b := by
  funext x
  simp only [backwardSORStep, backwardSorSweep, D, E, F, smul_neg, sub_neg_eq_add,
    neg_add_eq_sub]

/-- The step of a splitting is `Stationary.Splitting.mulVecStep`, the map
$x \mapsto M^{-1}(Nx + b)$. -/
theorem Splitting.step_eq_mulVecStep (s : Splitting A) (b : Fin n → ℝ) :
    Splitting.step s b = Stationary.Splitting.mulVecStep s b := by
  funext x
  rw [Splitting.step_eq, Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]

/-- Equation (4.12) of [saad2003iterative]: if $D$ is nonsingular and $\omega \neq 0$, the SOR step
is the step of the splitting with $M = \omega^{-1}(D - \omega E)$, `Matrix.sorSplitting`. The
proof specializes `Matrix.sorSweep_eq_mulVecStep`. -/
theorem sorStep_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b : Fin n → ℝ) :
    sorStep A ω b = Splitting.step (sorSplitting A h hω) b := by
  rw [sorStep_eq_sorSweep, sorSweep_eq_mulVecStep A h hω, Splitting.step_eq_mulVecStep]

/-! ### Preconditioners (4.24)–(4.27) -/

/-- Equation (4.24) of [saad2003iterative]: the Jacobi preconditioner is $M_{JA} = D$. -/
theorem M_JA_eq (h : IsUnit (diagPart A)) : (jacobiSplitting A h).m = D A := rfl

/-- Equation (4.25) of [saad2003iterative]: the Gauss–Seidel preconditioner is $M_{GS} = D - E$. -/
theorem M_GS_eq (h : IsUnit (diagPart A)) : (gaussSeidelSplitting A h).m = D A - E A :=
  (D_sub_E A).symm

/-- **Equation (4.26)** of [saad2003iterative]. The **SOR preconditioner** with parameter $\omega$
is
$$M_{SOR} = \frac{1}{\omega} (D - \omega E).$$

Theorem 4.16 of the book uses the name $M_{SOR}$ for the SOR iteration matrix instead. Here the
name is used only for the preconditioner. -/
noncomputable def M_sor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ω⁻¹ • (D A - ω • E A)

/-- If $D$ is nonsingular and $\omega \neq 0$, the SOR preconditioner $M_{SOR}$ is the matrix $M$ of
the SOR splitting `Matrix.sorSplitting`. -/
theorem M_sor_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    M_sor A ω = (sorSplitting A h hω).m := by
  have hm : (sorSplitting A h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  rw [hm, M_sor, D, E, smul_neg, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω,
    one_smul]

/-- **Equation (4.27)** of [saad2003iterative]. The **SSOR preconditioner** with parameter $\omega$
is
$$M_{SSOR} = \frac{1}{\omega (2 - \omega)} (D - \omega E) D^{-1} (D - \omega F).$$
-/
noncomputable def M_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (ω * (2 - ω))⁻¹ • ((D A - ω • E A) * (D A)⁻¹ * (D A - ω • F A))

/-- If $D$ is nonsingular, $\omega \neq 0$ and $\omega \neq 2$, the SSOR preconditioner $M_{SSOR}$
is the matrix $M$ of the SSOR splitting `Matrix.ssorSplitting`. -/
theorem M_ssor_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    M_ssor A ω = (ssorSplitting A h hω hω2).m := by
  have hm : (ssorSplitting A h hω hω2).m =
      (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
        (diagPart A + ω • strictUpper A)) := rfl
  rw [hm, M_ssor, D, E, F, smul_neg, smul_neg, sub_neg_eq_add, sub_neg_eq_add]

/-- Equations (4.13)–(4.14) and (4.27) of [saad2003iterative]: if $D$ is nonsingular,
$\omega \neq 0$ and $\omega \neq 2$, the SSOR step is the step of the splitting with
$M = M_{SSOR}$, `Matrix.ssorSplitting`. The proof specializes `Matrix.ssorSweep_eq_mulVecStep`,
and `SaadSparse.Chapter04.M_ssor_eq` identifies the matrix $M$. -/
theorem ssorStep_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (hω2 : ω ≠ 2) (b : Fin n → ℝ) :
    ssorStep A ω b = Splitting.step (ssorSplitting A h hω hω2) b := by
  funext x
  rw [ssorStep, Function.comp_apply, sorStep_eq_sorSweep, backwardSORStep_eq_backwardSorSweep,
    ssorSweep_eq_mulVecStep A h hω hω2, Splitting.step_eq_mulVecStep]

/-! ### The closed form (4.13)–(4.14) of the SSOR iteration -/

/-- **Equation (4.13)** of [saad2003iterative]. The **SSOR iteration matrix** with parameter
$\omega$ is
$$G_\omega = (D - \omega F)^{-1} (\omega E + (1 - \omega) D) (D - \omega E)^{-1} (\omega F +
  (1 - \omega) D).$$
-/
noncomputable def G_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
    (ω • F A + (1 - ω) • D A)

/-- **Equation (4.14)** of [saad2003iterative]. The **SSOR right-hand side** with parameter $\omega$
is
$$f_\omega = \omega (D - \omega F)^{-1} \big( I + (\omega E + (1 - \omega) D)(D - \omega E)^{-1}
  \big) b.$$
-/
noncomputable def f_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  ω • ((D A - ω • F A)⁻¹ *ᵥ
    ((1 + (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹) *ᵥ b))

/-- Equations (4.13)–(4.14) of [saad2003iterative]: for every $A$ and $\omega$, the SSOR step is the
affine map $x \mapsto G_\omega x + f_\omega$. -/
theorem ssorStep_eq_affine (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b := by
  simp only [ssorStep, Function.comp_apply, backwardSORStep, sorStep, G_ssor, f_ssor,
    ← mulVec_mulVec, mulVec_add, add_mulVec, one_mulVec, mulVec_smul, smul_add]
  abel

/-! ### Block relaxation (§4.1.1, (4.15)–(4.17), Algorithms 4.1–4.2) -/

section Block

variable {p : ℕ} {π : Fin n → Fin p}

/-- **Equations (4.15)–(4.16)** of [saad2003iterative]. Let
$\pi : \{1, \dots, n\} \to \{1, \dots, p\}$ label the indices, so that the blocks are the sets
$\pi^{-1}(k)$. The **block diagonal part** $D$ of $A$ keeps the entries $a_{ij}$ with
$\pi(i) = \pi(j)$ and sets the other entries to $0$. -/
def blockD (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  blockDiagPart π A

/-- **Equation (4.16)** of [saad2003iterative]. For the labelling $\pi$, the matrix $E$ is the
negative of the **strict block lower part** of $A$: $e_{ij} = -a_{ij}$ if $\pi(j) < \pi(i)$, and
$e_{ij} = 0$ otherwise. -/
def blockE (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -blockStrictLower π A

/-- **Equation (4.16)** of [saad2003iterative]. For the labelling $\pi$, the matrix $F$ is the
negative of the **strict block upper part** of $A$: $f_{ij} = -a_{ij}$ if $\pi(i) < \pi(j)$, and
$f_{ij} = 0$ otherwise. -/
def blockF (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -blockStrictUpper π A

/-- §4.1.1 of [saad2003iterative]: for the block parts, $A = D - E - F$. -/
theorem blockDecomp (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) :
    A = blockD π A - blockE π A - blockF π A := by
  rw [blockD, blockE, blockF, sub_neg_eq_add, sub_neg_eq_add]
  exact (blockDiagPart_add_blockStrictLower_add_blockStrictUpper π A).symm

/-- §4.1.1 of [saad2003iterative]: for the block parts, $E + F = D - A$. -/
theorem blockE_add_blockF (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) :
    blockE π A + blockF π A = blockD π A - A := by
  ext i j
  rcases lt_trichotomy (π i) (π j) with hlt | heq | hlt
  · simp [blockD, blockE, blockF, hlt, hlt.ne, asymm hlt]
  · simp [blockD, blockE, blockF, heq]
  · simp [blockD, blockE, blockF, hlt, hlt.ne', asymm hlt]

/-- §4.1.1 of [saad2003iterative]: for the block parts, $D - E = A + F$. -/
theorem blockD_sub_blockE_eq (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ) :
    blockD π A - blockE π A = A + blockF π A := by
  ext i j
  rcases lt_trichotomy (π i) (π j) with hlt | heq | hlt
  · simp [blockD, blockE, blockF, hlt, hlt.ne, asymm hlt]
  · simp [blockD, blockE, blockF, heq]
  · simp [blockD, blockE, blockF, hlt, hlt.ne', asymm hlt]

/-- §4.1.1 of [saad2003iterative]: if the block diagonal $D$ is nonsingular, then the block lower
part $D - E$ is nonsingular. -/
theorem isUnit_blockD_sub_blockE (h : IsUnit (blockD π A)) : IsUnit (blockD π A - blockE π A) := by
  rw [blockD, blockE, sub_neg_eq_add]
  exact isUnit_blockDiagPart_add_blockStrictLower h

/-- **Algorithm 4.1** of [saad2003iterative], for non-overlapping blocks. One **block Jacobi sweep**
from $x$ is
$$x' = D^{-1} \big( (E + F) x + b \big),$$
with $D$, $E$, $F$ the block parts for the labelling $\pi$. Every block is updated from the same
previous iterate. -/
noncomputable def blockJacobiStep (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) : Fin n → ℝ :=
  (blockD π A)⁻¹ *ᵥ ((blockE π A + blockF π A) *ᵥ x + b)

/-- **Algorithm 4.2** of [saad2003iterative], for non-overlapping blocks. One **block Gauss–Seidel
sweep** from $x$ is
$$x' = (D - E)^{-1} (Fx + b),$$
with $D$, $E$, $F$ the block parts for the labelling $\pi$. Each block uses the blocks that are
updated before it. -/
noncomputable def blockGaussSeidelStep (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) : Fin n → ℝ :=
  (blockD π A - blockE π A)⁻¹ *ᵥ (blockF π A *ᵥ x + b)

/-- **Equation (4.17)** of [saad2003iterative]. If the block diagonal $D$ is nonsingular, the block
Jacobi sweep satisfies
$$x' = x + D^{-1}(b - Ax).$$
On block $i$ this is the update $\xi_i \leftarrow \xi_i + A_{ii}^{-1}(b - Ax)_i$ of the book. -/
theorem equation_4_17 (h : IsUnit (blockD π A)) (b x : Fin n → ℝ) :
    blockJacobiStep π A b x = x + (blockD π A)⁻¹ *ᵥ (b - A *ᵥ x) := by
  rw [blockJacobiStep, blockE_add_blockF, sub_mulVec, mulVec_add, mulVec_sub, mulVec_sub,
    nonsing_inv_mulVec_mulVec h]
  abel

/-- **Equations (4.16)–(4.17)** of [saad2003iterative]. If the block diagonal $D$ is nonsingular,
the block Jacobi sweep is the step of the splitting with $M = D$.

The splitting is `Matrix.blockJacobiSplitting`. -/
theorem blockJacobiStep_eq (h : IsUnit (blockD π A)) (b : Fin n → ℝ) :
    blockJacobiStep π A b = Splitting.step (blockJacobiSplitting π A h) b := by
  funext x
  rw [Splitting.step_eq, equation_4_17 h]
  rfl

/-- **Algorithm 4.2** of [saad2003iterative]. If the block diagonal $D$ is nonsingular, the block
Gauss–Seidel sweep is the step of the splitting with $M = D - E$, the block lower part of $A$.

The splitting is `Matrix.blockGaussSeidelSplitting`. -/
theorem blockGaussSeidelStep_eq (h : IsUnit (blockD π A)) (b : Fin n → ℝ) :
    blockGaussSeidelStep π A b = Splitting.step (blockGaussSeidelSplitting π A h) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (blockGaussSeidelSplitting π A h).m = blockD π A - blockE π A := by
    rw [blockD, blockE, sub_neg_eq_add]; rfl
  rw [hm, mulVec_sub, blockGaussSeidelStep,
    mulVec_nonsing_inv_mulVec (isUnit_blockD_sub_blockE h), blockD_sub_blockE_eq, add_mulVec]
  abel

/-- **Section 5.4** of [saad2003iterative], block Jacobi as an additive process. If the block
diagonal $D$ is nonsingular, one block Jacobi sweep is one step of the additive projection
process over the blocks, with $K_k = L_k$ the coordinate subspace of the block $\pi^{-1}(k)$ and
all weights equal to $1$. This is the reading of (4.17) as (5.7) that §5.4 gives.

The process is `Projection.additiveStep` for `Matrix.toEuclideanLin A`, and the subspaces are
`EuclideanSpace.blockSubspace ℝ π`. The vectors pass to `EuclideanSpace ℝ (Fin n)` through
`WithLp.toLp 2`. -/
theorem blockJacobiStep_eq_additiveStep (h : IsUnit (blockD π A)) (b x : Fin n → ℝ) :
    WithLp.toLp 2 (blockJacobiStep π A b x) =
      Projection.additiveStep (toEuclideanLin A) (WithLp.toLp 2 b)
        (EuclideanSpace.blockSubspace ℝ π) (EuclideanSpace.blockSubspace ℝ π)
        (isNondegeneratePair_blockSubspace h) 1 (WithLp.toLp 2 x) := by
  rw [blockJacobiSplitting_step_eq_additiveStep h (WithLp.toLp 2 b) (WithLp.toLp 2 x),
    equation_4_17 h]
  rfl

/-- **Section 5.4** of [saad2003iterative], Algorithm 5.6, block Gauss–Seidel as a multiplicative
process. If the block diagonal $D$ is nonsingular, one block Gauss–Seidel sweep is one sweep of
the multiplicative projection process over the blocks, with $K_k = L_k$ the coordinate subspace
of the block $\pi^{-1}(k)$, taken in increasing order of the label $k$.

The process is `Projection.multiplicativeStep` for `Matrix.toEuclideanLin A`, over the sorted
list of the labels. -/
theorem blockGaussSeidelStep_eq_multiplicativeStep (h : IsUnit (blockD π A)) (b x : Fin n → ℝ) :
    WithLp.toLp 2 (blockGaussSeidelStep π A b x) =
      Projection.multiplicativeStep (toEuclideanLin A) (WithLp.toLp 2 b)
        (EuclideanSpace.blockSubspace ℝ π) (EuclideanSpace.blockSubspace ℝ π)
        (isNondegeneratePair_blockSubspace h) (Finset.sort (Finset.univ : Finset (Fin p)))
        (WithLp.toLp 2 x) := by
  rw [blockGaussSeidelSplitting_step_eq_multiplicativeStep h (WithLp.toLp 2 b) (WithLp.toLp 2 x),
    blockGaussSeidelStep_eq h, Splitting.step_eq]
  rfl

end Block


end SaadSparse.Chapter04
