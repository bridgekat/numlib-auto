/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section07

/-!
# Saad, Section 6.8: The conjugate residual method

This module formalizes Section 6.8 of [saad2003iterative]. The conjugate residual algorithm
(Algorithm 6.20) solves $Ax = b$ for a Hermitian matrix $A$. It starts from $r_0 = b - A x_0$ and
$p_0 = r_0$, and computes
$$\alpha_j = \frac{(r_j, A r_j)}{(A p_j, A p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  r_{j+1} = r_j - \alpha_j A p_j, \quad \beta_j = \frac{(r_{j+1}, A r_{j+1})}{(r_j, A r_j)}, \quad
  p_{j+1} = r_{j+1} + \beta_j p_j,$$
and it updates $A p_{j+1} = A r_{j+1} + \beta_j A p_j$ without a further matrix-vector product.
Section 6.8 derives the algorithm from GMRES for the particular case where $A$ is Hermitian. For a
symmetric positive definite $A$ the residuals are $A$-orthogonal, the vectors $A p_i$ are
orthogonal, and $x_j$ minimizes $\|b - Ax\|_2$ over $x_0 + \mathcal{K}_j(A, r_0)$. So the algorithm
computes the same approximation as GMRES (Algorithm 6.9). For a symmetric, possibly indefinite $A$
the minimal-residual property holds as long as the algorithm does not divide by zero.

The proofs specialize the backbone module `Numlib.Krylov.CR`: Algorithm 6.20 is the backbone
recurrence `CR.iterate` (`SaadSparse.Chapter06.cr_eq_CR`). The GMRES approximation is that of
`NumlibSurface.SaadSparse.Chapter06.Section05`.

## Main definitions

* Algorithm 6.20, `SaadSparse.Chapter06.cr`: the quadruple $(x_j, r_j, p_j, A p_j)$ after $j$ steps
  of the conjugate residual algorithm, with one step `SaadSparse.Chapter06.crStep`.

## Main results

* Algorithm 6.20, `SaadSparse.Chapter06.cr_eq_CR`: for a Hermitian $A$, Algorithm 6.20 is the
  backbone conjugate residual recurrence.
* Section 6.8, `SaadSparse.Chapter06.algorithm_6_20_orthogonality`: $(r_i, A r_j) = 0$ and
  $(A p_i, A p_j) = 0$ for $i \ne j$.
* Section 6.8, `SaadSparse.Chapter06.algorithm_6_20_isMinResidualIterate`: $x_j$ minimizes the
  residual norm over $x_0 + \mathcal{K}_j(A, r_0)$.
* Section 6.8, `SaadSparse.Chapter06.algorithm_6_20_isMinResidualIterate_of_no_breakdown`: the same
  for a symmetric, possibly indefinite $A$, as long as the algorithm does not divide by zero.
* Section 6.8, `SaadSparse.Chapter06.algorithm_6_20_eq_alg_6_9`: the conjugate residual algorithm
  and GMRES compute the same approximations.

## Implementation notes

* Indices start at $0$, as in the book. A quotient with denominator $0$ is $0$ in Lean, which
  reproduces the breakdown behaviour of the book.
* The step length uses the inner product $(x, y) = \sum_i x_i \bar y_i$ of the book, so its
  numerator $(r_j, A r_j)$ is Mathlib's `inner 𝕜 (op A r_j) r_j`. The backbone `CR.iterate` writes
  the numerator as $\langle r_j, A r_j \rangle$. The two agree because $A$ is Hermitian, the
  standing hypothesis of the section.
* The definitions are polymorphic in the scalar field $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The
  numbered results are stated over $\mathbb{R}$, with $A$ symmetric positive definite or symmetric,
  the generality of the source.
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.20 -/

/-- The step length $\alpha_j = (r_j, A r_j)/(A p_j, A p_j)$ of line 3 of Algorithm 6.20, computed
from a quadruple $(x_j, r_j, p_j, A p_j)$. -/
noncomputable def crStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A s.2.1) s.2.1 / inner 𝕜 s.2.2.2 s.2.2.2

/-- The next residual $r_{j+1} = r_j - \alpha_j A p_j$ of line 5 of Algorithm 6.20, computed from a
quadruple $(x_j, r_j, p_j, A p_j)$. -/
noncomputable def crStepR (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - crStepAlpha A s • s.2.2.2

/-- The coefficient $\beta_j = (r_{j+1}, A r_{j+1})/(r_j, A r_j)$ of line 6 of Algorithm 6.20,
computed from a quadruple $(x_j, r_j, p_j, A p_j)$. -/
noncomputable def crStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A (crStepR A s)) (crStepR A s) / inner 𝕜 (op A s.2.1) s.2.1

/-- **Algorithm 6.20** of [saad2003iterative], one step. The map that sends a quadruple
$(x_j, r_j, p_j, q_j)$, where $q_j$ stands for $A p_j$, to
$(x_{j+1}, r_{j+1}, p_{j+1}, q_{j+1})$ by lines 3–8 of the algorithm:
$$\alpha_j = \frac{(r_j, A r_j)}{(q_j, q_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  r_{j+1} = r_j - \alpha_j q_j,$$
$$\beta_j = \frac{(r_{j+1}, A r_{j+1})}{(r_j, A r_j)}, \quad p_{j+1} = r_{j+1} + \beta_j p_j,
  \quad q_{j+1} = A r_{j+1} + \beta_j q_j.$$

Line 8 updates $A p_{j+1}$ without a further matrix-vector product. A quotient with denominator
$0$ is $0$. -/
noncomputable def crStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + crStepAlpha A s • s.2.2.1, crStepR A s,
    crStepR A s + crStepBeta A s • s.2.2.1,
    op A (crStepR A s) + crStepBeta A s • s.2.2.2)

/-- **Algorithm 6.20** of [saad2003iterative] (conjugate residual). For
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the quadruple
$(x_j, r_j, p_j, A p_j)$ after $j$ steps of the algorithm, started from $r_0 = b - A x_0$,
$p_0 = r_0$ and $A p_0$. -/
noncomputable def cr (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (crStep A)^[j] (x₀, b - op A x₀, b - op A x₀, op A (b - op A x₀))

/-- The step length `SaadSparse.Chapter06.crStepAlpha` is $(r_j, A r_j)/(A p_j, A p_j)$. -/
theorem crStepAlpha_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepAlpha A s = inner 𝕜 (op A s.2.1) s.2.1 / inner 𝕜 s.2.2.2 s.2.2.2 := rfl

/-- The residual `SaadSparse.Chapter06.crStepR` is $r_j - \alpha_j A p_j$. -/
theorem crStepR_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepR A s = s.2.1 - crStepAlpha A s • s.2.2.2 := rfl

/-- The coefficient `SaadSparse.Chapter06.crStepBeta` is $(r_{j+1}, A r_{j+1})/(r_j, A r_j)$. -/
theorem crStepBeta_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepBeta A s = inner 𝕜 (op A (crStepR A s)) (crStepR A s) / inner 𝕜 (op A s.2.1) s.2.1 :=
  rfl

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The iterate $x_j$ of Algorithm 6.20 after $j$ steps. -/
noncomputable def crX (j : ℕ) : 𝔼 := (cr A b x₀ j).1

/-- The residual $r_j$ of Algorithm 6.20 after $j$ steps. -/
noncomputable def crR (j : ℕ) : 𝔼 := (cr A b x₀ j).2.1

/-- The search direction $p_j$ of Algorithm 6.20 after $j$ steps. -/
noncomputable def crP (j : ℕ) : 𝔼 := (cr A b x₀ j).2.2.1

/-- The vector $A p_j$ carried by line 8 of Algorithm 6.20 after $j$ steps. -/
noncomputable def crAp (j : ℕ) : 𝔼 := (cr A b x₀ j).2.2.2

/-- The step length $\alpha_j$ of Algorithm 6.20 at step $j$. -/
noncomputable def crAlpha (j : ℕ) : 𝕜 := crStepAlpha A (cr A b x₀ j)

/-- The coefficient $\beta_j$ of Algorithm 6.20 at step $j$. -/
noncomputable def crBeta (j : ℕ) : 𝕜 := crStepBeta A (cr A b x₀ j)

/-- The quadruple after $j + 1$ steps of Algorithm 6.20 is one step applied to the quadruple after
$j$ steps. -/
theorem cr_succ (j : ℕ) : cr A b x₀ (j + 1) = crStep A (cr A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate $x_0$ of Algorithm 6.20 is the initial guess. -/
@[simp] theorem crX_zero : crX A b x₀ 0 = x₀ := rfl

/-- The residual $r_0$ of Algorithm 6.20 is $b - A x_0$. -/
@[simp] theorem crR_zero : crR A b x₀ 0 = b - op A x₀ := rfl

/-- Algorithm 6.20, line 1: $p_0 = r_0$. -/
@[simp] theorem crP_zero : crP A b x₀ 0 = crR A b x₀ 0 := rfl

/-- The fourth component of the quadruple starts as $A p_0$. -/
@[simp] theorem crAp_zero : crAp A b x₀ 0 = op A (crP A b x₀ 0) := rfl

/-- Algorithm 6.20, line 3: $\alpha_j = (r_j, A r_j)/(A p_j, A p_j)$. -/
theorem crAlpha_eq (j : ℕ) : crAlpha A b x₀ j =
    inner 𝕜 (op A (crR A b x₀ j)) (crR A b x₀ j) /
      inner 𝕜 (crAp A b x₀ j) (crAp A b x₀ j) := rfl

/-- Algorithm 6.20, line 4: $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem crX_succ (j : ℕ) :
    crX A b x₀ (j + 1) = crX A b x₀ j + crAlpha A b x₀ j • crP A b x₀ j := by
  rw [crX, cr_succ]
  rfl

/-- Algorithm 6.20, line 5: $r_{j+1} = r_j - \alpha_j A p_j$. -/
theorem crR_succ (j : ℕ) :
    crR A b x₀ (j + 1) = crR A b x₀ j - crAlpha A b x₀ j • crAp A b x₀ j := by
  rw [crR, cr_succ]
  rfl

/-- The residual $r_{j+1}$ is the residual computed by `SaadSparse.Chapter06.crStepR` from the
quadruple at step $j$. -/
theorem crR_succ_eq_crStepR (j : ℕ) : crR A b x₀ (j + 1) = crStepR A (cr A b x₀ j) := by
  rw [crR, cr_succ]
  rfl

/-- Algorithm 6.20, line 6: $\beta_j = (r_{j+1}, A r_{j+1})/(r_j, A r_j)$. -/
theorem crBeta_eq (j : ℕ) : crBeta A b x₀ j =
    inner 𝕜 (op A (crR A b x₀ (j + 1))) (crR A b x₀ (j + 1)) /
      inner 𝕜 (op A (crR A b x₀ j)) (crR A b x₀ j) := by
  rw [crBeta, crStepBeta_def, crR_succ_eq_crStepR]
  rfl

/-- Algorithm 6.20, line 7: $p_{j+1} = r_{j+1} + \beta_j p_j$. -/
theorem crP_succ (j : ℕ) :
    crP A b x₀ (j + 1) = crR A b x₀ (j + 1) + crBeta A b x₀ j • crP A b x₀ j := by
  rw [crP, cr_succ, crR_succ_eq_crStepR]
  rfl

/-- Algorithm 6.20, line 8: $A p_{j+1} = A r_{j+1} + \beta_j A p_j$. -/
theorem crAp_succ (j : ℕ) :
    crAp A b x₀ (j + 1) = op A (crR A b x₀ (j + 1)) + crBeta A b x₀ j • crAp A b x₀ j := by
  rw [crAp, cr_succ, crR_succ_eq_crStepR]
  rfl

/-! ### Identification with the backbone conjugate residual recurrence -/

private theorem crStepAlpha_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepAlpha A (s.x, s.r, s.p, s.q) = CR.alpha (op A) s := by
  rw [crStepAlpha_def, CR.alpha, hA s.r s.r]

private theorem crStepR_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepR A (s.x, s.r, s.p, s.q) = (CR.step (op A) s).r := by
  rw [crStepR_def, crStepAlpha_eq_CR A hA s, CR.step]

private theorem crStepBeta_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepBeta A (s.x, s.r, s.p, s.q) =
      inner 𝕜 (CR.step (op A) s).r (op A (CR.step (op A) s).r) / inner 𝕜 s.r (op A s.r) := by
  rw [crStepBeta_def, crStepR_eq_CR A hA s, hA s.r s.r, hA (CR.step (op A) s).r]

private theorem crStep_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStep A (s.x, s.r, s.p, s.q) = ((CR.step (op A) s).x, (CR.step (op A) s).r,
      (CR.step (op A) s).p, (CR.step (op A) s).q) := by
  rw [crStep, crStepAlpha_eq_CR A hA s, crStepR_eq_CR A hA s, crStepBeta_eq_CR A hA s, CR.step]

/-- Algorithm 6.20 is the backbone conjugate residual recurrence. Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian. Then for every $j \ge 0$ the quadruple
$(x_j, r_j, p_j, A p_j)$ of Algorithm 6.20 is the quadruple of iterate, residual, direction and
image of the direction of `CR.iterate (op A) b x₀ j`.

The symmetry of $A$ is needed only to move $A$ across the inner products in $\alpha_j$ and
$\beta_j$. -/
theorem cr_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    cr A b x₀ j = ((CR.iterate (op A) b x₀ j).x, (CR.iterate (op A) b x₀ j).r,
      (CR.iterate (op A) b x₀ j).p, (CR.iterate (op A) b x₀ j).q) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cr_succ, ih, CR.iterate_succ, crStep_eq_CR A hA]

/-- For a Hermitian $A$, the iterate $x_j$ of Algorithm 6.20 is that of `CR.iterate`. -/
theorem crX_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crX A b x₀ j = (CR.iterate (op A) b x₀ j).x := by rw [crX, cr_eq_CR A b x₀ hA]

/-- For a Hermitian $A$, the residual $r_j$ of Algorithm 6.20 is that of `CR.iterate`. -/
theorem crR_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crR A b x₀ j = (CR.iterate (op A) b x₀ j).r := by rw [crR, cr_eq_CR A b x₀ hA]

/-- For a Hermitian $A$, the direction $p_j$ of Algorithm 6.20 is that of `CR.iterate`. -/
theorem crP_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crP A b x₀ j = (CR.iterate (op A) b x₀ j).p := by rw [crP, cr_eq_CR A b x₀ hA]

/-- For a Hermitian $A$, the vector carried by line 8 of Algorithm 6.20 is the field `q` of
`CR.iterate`. -/
theorem crAp_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crAp A b x₀ j = (CR.iterate (op A) b x₀ j).q := by rw [crAp, cr_eq_CR A b x₀ hA]

/-- For a Hermitian $A$, the vector carried by line 8 of Algorithm 6.20 is $A p_j$. -/
theorem crAp_eq_apply_crP (hA : (op A).IsSymmetric) (j : ℕ) :
    crAp A b x₀ j = op A (crP A b x₀ j) := by
  rw [crAp_eq_CR A b x₀ hA, crP_eq_CR A b x₀ hA, CR.q_eq]

/-- For a Hermitian $A$, the residual carried by Algorithm 6.20 is the true residual:
$r_j = b - A x_j$. -/
theorem crR_eq_residual (hA : (op A).IsSymmetric) (j : ℕ) :
    crR A b x₀ j = b - op A (crX A b x₀ j) := by
  rw [crR_eq_CR A b x₀ hA, crX_eq_CR A b x₀ hA, CR.residual_eq]

/-! ### The invariants of Section 6.8 -/

variable {A b x₀}

/-- Section 6.8: for a Hermitian positive definite $A$, the vectors $A p_i$ of Algorithm 6.20 are
orthogonal, $(A p_i, A p_j) = 0$ for $i \ne j$. -/
theorem inner_crAp_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (crAp A b x₀ i) (crAp A b x₀ j) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crAp_eq_apply_crP A b x₀ hs, crAp_eq_apply_crP A b x₀ hs, crP_eq_CR A b x₀ hs,
    crP_eq_CR A b x₀ hs]
  exact CR.inner_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- Section 6.8: for a Hermitian positive definite $A$, the residuals of Algorithm 6.20 are
$A$-orthogonal (conjugate), $(r_i, A r_j) = 0$ for $i \ne j$. -/
theorem inner_apply_crR_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (crR A b x₀ i) (op A (crR A b x₀ j)) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crR_eq_CR A b x₀ hs, crR_eq_CR A b x₀ hs]
  exact CR.inner_residual_apply_residual_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$: $(r_i, A p_j) = 0$ for $j < i$. So the residual is
orthogonal to the earlier vectors $A p_j$, which is the Petrov–Galerkin condition behind the
minimization. -/
theorem inner_crR_crAp_eq_zero (hA : A.PosDef) {i j : ℕ} (h : j < i) :
    inner 𝕜 (crR A b x₀ i) (crAp A b x₀ j) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crAp_eq_apply_crP A b x₀ hs, crR_eq_CR A b x₀ hs, crP_eq_CR A b x₀ hs]
  exact CR.inner_residual_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$ and every $m$, the directions $p_0, \dots, p_{m-1}$ of
Algorithm 6.20 span $\mathcal{K}_m(A, r_0)$. -/
theorem span_crP_eq (hA : A.PosDef) (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => crP A b x₀ (i : ℕ)) =
      krylov A (r₀ A b x₀) m := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [krylov_eq]
  simp only [crP_eq_CR A b x₀ hs]
  exact CR.span_direction_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) m

/-- Algorithm 6.20 realizes the minimal-residual specification: for a Hermitian positive definite
$A$ and every $j$, the iterate $x_j$ minimizes $\|b - A x\|$ over $x_0 + \mathcal{K}_j(A, r_0)$.
This is the sense in which Section 6.8 obtains the conjugate residual algorithm from GMRES for a
Hermitian $A$. -/
theorem crX_isMinResidualIterate (hA : A.PosDef) (j : ℕ) :
    Krylov.IsMinResidualIterate (op A) b x₀ j (crX A b x₀ j) := by
  rw [crX_eq_CR A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CR.isMinResidualIterate b x₀ (isSymmetricCoercive_op_of_posDef hA) j

/-- The minimal-residual property for a Hermitian, possibly indefinite $A$: if $(r_i, A r_i) \ne 0$
and $A p_i \ne 0$ for every $i < j$, so that Algorithm 6.20 does not divide by zero in its first
$j$ steps, then $x_j$ minimizes $\|b - A x\|$ over $x_0 + \mathcal{K}_j(A, r_0)$. -/
theorem crX_isMinResidualIterate_of_no_breakdown (hA : (op A).IsSymmetric) {j : ℕ}
    (h1 : ∀ i < j, inner 𝕜 (op A (crR A b x₀ i)) (crR A b x₀ i) ≠ 0)
    (h2 : ∀ i < j, crAp A b x₀ i ≠ 0) :
    Krylov.IsMinResidualIterate (op A) b x₀ j (crX A b x₀ j) := by
  rw [crX_eq_CR A b x₀ hA]
  refine CR.isMinResidualIterate_of_no_breakdown b x₀ hA j (fun i hi => ?_) fun i hi => ?_
  · rw [← crR_eq_CR A b x₀ hA, ← hA (crR A b x₀ i) (crR A b x₀ i)]
    exact h1 i hi
  · rw [← crAp_eq_CR A b x₀ hA]
    exact h2 i hi

/-- The conjugate residual algorithm coincides with GMRES: for a Hermitian positive definite $A$ and
$j \le \mu$, the grade of $v_1 = r_0/\|r_0\|_2$, the iterate $x_j$ of Algorithm 6.20 is the
approximation after $j$ steps of GMRES (Algorithm 6.9), since both are the minimal-residual
iterate. -/
theorem crX_eq_gmresFixed (hA : A.PosDef) {j : ℕ} (hj : j ≤ grade A (v₁ A b x₀)) :
    crX A b x₀ j = gmresFixed A b x₀ j := by
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA.isUnit) b x₀ j
  rw [hz _ (crX_isMinResidualIterate hA j),
    hz _ (gmresFixed_isMinResidualIterate A b x₀ hj (isUnit_R_of_isUnit A b x₀ hA.isUnit hj))]

end General

/-! ### The results of Section 6.8, over the real numbers -/

section BookResults

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **Section 6.8** of [saad2003iterative], the orthogonality relations of Algorithm 6.20. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$,
and let $i \ne j$. Then the residuals of Algorithm 6.20 are $A$-orthogonal and the vectors
$A p_i$ are orthogonal:
$$(r_i, A r_j) = 0, \qquad (A p_i, A p_j) = 0.$$
-/
theorem algorithm_6_20_orthogonality (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner ℝ (crR A b x₀ i) (op A (crR A b x₀ j)) = 0 ∧
      inner ℝ (op A (crP A b x₀ i)) (op A (crP A b x₀ j)) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  refine ⟨inner_apply_crR_eq_zero hA h, ?_⟩
  rw [← crAp_eq_apply_crP A b x₀ hs, ← crAp_eq_apply_crP A b x₀ hs]
  exact inner_crAp_eq_zero hA h

/-- **Section 6.8** of [saad2003iterative], Algorithm 6.20 as the Hermitian case of GMRES. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and $b, x_0 \in \mathbb{R}^n$.
Then for every $j \ge 0$ the iterate $x_j$ of Algorithm 6.20 satisfies
$x_j \in x_0 + \mathcal{K}_j(A, r_0)$ and
$$\|b - A x_j\|_2 \le \|b - A x\|_2 \quad \text{for every } x \in x_0 + \mathcal{K}_j(A, r_0).$$

The property is `Krylov.IsMinResidualIterate`. -/
theorem algorithm_6_20_isMinResidualIterate (hA : A.PosDef) (j : ℕ) :
    Krylov.IsMinResidualIterate (op A) b x₀ j (crX A b x₀ j) :=
  crX_isMinResidualIterate hA j

/-- **Section 6.8** of [saad2003iterative], the indefinite case. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, possibly indefinite, let $b, x_0 \in \mathbb{R}^n$, and let $j \ge 0$. Assume that
$(r_i, A r_i) \ne 0$ and $A p_i \ne 0$ for every $i < j$, so that the algorithm does not divide
by zero in its first $j$ steps. Then the iterate $x_j$ of Algorithm 6.20 minimizes
$\|b - A x\|_2$ over $x_0 + \mathcal{K}_j(A, r_0)$.

The vector $A p_i$ of the hypothesis is the vector `SaadSparse.Chapter06.crAp` carried by
line 8. The property is `Krylov.IsMinResidualIterate`. -/
theorem algorithm_6_20_isMinResidualIterate_of_no_breakdown (hA : A.IsSymm) {j : ℕ}
    (h1 : ∀ i < j, inner ℝ (op A (crR A b x₀ i)) (crR A b x₀ i) ≠ 0)
    (h2 : ∀ i < j, crAp A b x₀ i ≠ 0) :
    Krylov.IsMinResidualIterate (op A) b x₀ j (crX A b x₀ j) :=
  crX_isMinResidualIterate_of_no_breakdown (isSymmetric_op_of_isSymm hA) h1 h2

/-- **Section 6.8** of [saad2003iterative], the conjugate residual algorithm and full GMRES. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$,
and let $j \le \mu$, the grade of $v_1 = r_0/\|r_0\|_2$. Then the iterate $x_j$ of Algorithm
6.20 is the approximation after $j$ steps of GMRES (Algorithm 6.9).

The GMRES approximation is `SaadSparse.Chapter06.gmresFixed`, GMRES run for exactly $j$ Arnoldi
steps. Both iterates are the unique minimal-residual iterate on $x_0 + \mathcal{K}_j(A, r_0)$. -/
theorem algorithm_6_20_eq_alg_6_9 (hA : A.PosDef) {j : ℕ} (hj : j ≤ grade A (v₁ A b x₀)) :
    crX A b x₀ j = gmresFixed A b x₀ j :=
  crX_eq_gmresFixed hA hj

end BookResults

end SaadSparse.Chapter06
