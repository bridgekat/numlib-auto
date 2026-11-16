/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.CG
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Section04
import NumlibSurface.SaadSparse.Chapter06.Section06

/-!
# Saad, Section 6.7: The conjugate gradient method

This module formalizes Section 6.7 of [saad2003iterative] for a linear system $Ax = b$ with initial
guess $x_0$, initial residual $r_0 = b - Ax_0$, $\beta = \|r_0\|_2$ and $v_1 = r_0 / \beta$. The
Lanczos method for linear systems (Algorithm 6.16) takes $x_m = x_0 + V_m y_m$ with
$y_m = T_m^{-1}(\beta e_1)$ (6.86), where $V_m$ and $T_m$ come from the Lanczos algorithm of Section
6.6, and its residual is $b - Ax_m = -\beta_{m+1} (e_m^T y_m) v_{m+1}$ (6.87). The direct version
D-Lanczos (Algorithm 6.17) computes the same iterates by the factorization $T_m = L_m U_m$,
(6.88)–(6.89). Proposition 6.20 states that the residuals are multiples of the Lanczos vectors and
that the auxiliary vectors $p_i$ of D-Lanczos are $A$-conjugate. The conjugate gradient algorithm
(Algorithm 6.18) starts from $p_0 = r_0$ and computes
$$\alpha_j = \frac{(r_j, r_j)}{(A p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad r_{j+1} =
  r_j - \alpha_j A p_j, \quad \beta_j = \frac{(r_{j+1}, r_{j+1})}{(r_j, r_j)}, \quad p_{j+1} =
  r_{j+1} + \beta_j p_j,$$
and Algorithm 6.19 is its three-term form (6.96)–(6.98). Section 6.7.3 expresses the entries of
$T_m$ by the coefficients of the conjugate gradient algorithm, (6.99)–(6.103).

For a symmetric positive definite $A$ the four algorithms compute the same iterate, the Galerkin
iterate: $x_m - x_0 \in \mathcal{K}_m(A, r_0)$ and $b - Ax_m \perp \mathcal{K}_m(A, r_0)$. Algorithm
6.16 is FOM for a symmetric matrix, and D-Lanczos is DIOM(2). The proofs specialize the backbone
modules `Numlib.Krylov.CG`, `Numlib.Krylov.Lanczos` and `Numlib.Krylov.Iterate`: Algorithm 6.18 is
the backbone recurrence `CG.iterate` (`SaadSparse.Chapter06.cg_eq_CG`), so the orthogonality of the
residuals, the $A$-conjugacy of the directions, the Galerkin property and the three-term form come
from `Numlib.Krylov.CG`. The modules `NumlibSurface.SaadSparse.Chapter06.Section04` and
`NumlibSurface.SaadSparse.Chapter06.Section06` supply FOM, DIOM and the Lanczos algorithm.

## Main definitions

* Algorithm 6.16, `SaadSparse.Chapter06.lanczosMethod`: the Lanczos method for linear systems,
  $x_m = x_0 + V_m T_m^{-1}(\beta e_1)$, stopped at the grade of $r_0$.
* Equations (6.88)–(6.89), `SaadSparse.Chapter06.dlLambda` and `SaadSparse.Chapter06.dlEta`: the
  entries $\lambda_m$ and $\eta_m$ of the factors of $T_m = L_m U_m$.
* Algorithm 6.17, `SaadSparse.Chapter06.dLanczosX`, with `SaadSparse.Chapter06.dlZeta` and
  `SaadSparse.Chapter06.dlP`: the iterates of D-Lanczos, $x_m = x_{m-1} + \zeta_m p_m$.
* Algorithm 6.18, `SaadSparse.Chapter06.cg`: the conjugate gradient algorithm, with one step
  `SaadSparse.Chapter06.cgStep` and the step length `SaadSparse.Chapter06.cgAlpha`.
* Algorithm 6.19, `SaadSparse.Chapter06.cg3`: the three-term recurrence variant, with the scalars
  `SaadSparse.Chapter06.cgGamma` and `SaadSparse.Chapter06.cgRho` of (6.97).

## Main results

* Equation (6.86), `SaadSparse.Chapter06.lanczosMethodAt_isGalerkinIterate`: the iterate of
  Algorithm 6.16 is the Galerkin iterate on $\mathcal{K}_m(A, r_0)$.
* Equation (6.87), `SaadSparse.Chapter06.equation_6_87`:
  $b - Ax_m = -\beta_{m+1} (e_m^T y_m) v_{m+1}$.
* Proposition 6.20(1), `SaadSparse.Chapter06.proposition_6_20_1`: the residual of Algorithm 6.16 is
  a multiple of $v_{m+1}$.
* Proposition 6.20(2), `SaadSparse.Chapter06.proposition_6_20_2`: the auxiliary vectors of Algorithm
  6.17 are $A$-conjugate.
* Section 6.7, `SaadSparse.Chapter06.lanczosMethod_eq_fom`: Algorithm 6.16 is FOM for a symmetric
  matrix.
* Section 6.7.1, `SaadSparse.Chapter06.dLanczos_eq_diom2`: Algorithm 6.17 is DIOM(2).
* Section 6.7.1, `SaadSparse.Chapter06.cg_eq_CG`: Algorithm 6.18 is the backbone conjugate gradient
  recurrence.
* Section 6.7.1, `SaadSparse.Chapter06.cgX_eq_dLanczosX`: the conjugate gradient algorithm and
  D-Lanczos compute the same iterates.
* Equation (6.96), `SaadSparse.Chapter06.equation_6_96`: $r_{m+1} = \rho_m (r_m - \gamma_m A r_m) +
  (1 - \rho_m) r_{m-1}$.
* Equation (6.98), `SaadSparse.Chapter06.equation_6_98`: $x_{m+1} = \rho_m (x_m + \gamma_m r_m) +
  (1 - \rho_m) x_{m-1}$.
* Equation (6.99), `SaadSparse.Chapter06.equation_6_99`: the residual $r_j$ is a nonzero multiple of
  the Lanczos vector $v_{j+1}$.
* Equation (6.100), `SaadSparse.Chapter06.equation_6_100`: $r_j = p_j - \beta_{j-1} p_{j-1}$.
* Equation (6.101), `SaadSparse.Chapter06.equation_6_101`: $\delta_{j+1} = 1/\alpha_j +
  \beta_{j-1}/\alpha_{j-1}$.
* Equation (6.102), `SaadSparse.Chapter06.equation_6_102`: $\delta_1 = 1/\alpha_0$.
* Equation (6.103), `SaadSparse.Chapter06.equation_6_103`:
  $\eta_{j+1} = \sqrt{\beta_{j-1}}/\alpha_{j-1}$.
* Exercise P-6.17, `SaadSparse.Chapter06.equation_6_97_of_eq_6_96`: the coefficient (6.97) is forced
  by (6.96).

## Conventions

* The conjugate gradient iterates are numbered from $0$ in the book, and the Lean indices agree:
  `cgX A b x₀ j` is $x_j$ and `cgAlpha A b x₀ j` is $\alpha_j$.
* The Lanczos data are shifted by one, as in `NumlibSurface.SaadSparse.Chapter06.Section06`:
  `lanczosV A v₁ j` is $v_{j+1}$.
* The D-Lanczos data `dlEta`, `dlLambda`, `dlZeta` and `dlP` are shifted by one, so that
  `dlEta A v₁ m` is $\eta_{m+1}$.
* The D-Lanczos iterate `dLanczosX A b x₀ m` is $x_m$.
* In Section 6.7.3 the book writes the diagonal and off-diagonal entries of $T_m$ as $\delta_j$ and
  $\eta_j$. These are the coefficients $\alpha_j$ and $\beta_j$ of Algorithm 6.15, `lanczosAlpha`
  and `lanczosBeta`.

## Implementation notes

* The definitions are polymorphic in the scalar field $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The
  results on Algorithms 6.18 and 6.19 alone, including (6.96), (6.98) and Exercise P-6.17, are
  stated for a Hermitian positive definite $A$ over $\mathbb{K}$, which includes the real symmetric
  positive definite case of the book. The results on Algorithms 6.16 and 6.17, and the results
  (6.99)–(6.103) that relate Algorithm 6.18 to the Lanczos data, are stated over $\mathbb{R}$, with
  $A$ symmetric or symmetric positive definite.
* A division by $0$ gives $0$ in Lean, and the inverse of a singular matrix is $0$. This reproduces
  the breakdown behaviour of the book. The results take the nonsingularity of $T_m$
  (`IsUnit (T A (v₁ A b x₀) m).det`) and the nonvanishing of the pivots $\eta_i$ as hypotheses where
  the proofs need them.
* Algorithms 6.16 and 6.17 start from the unit vector $v_1 = r_0/\|r_0\|_2$ of
  `NumlibSurface.SaadSparse.Chapter06.Common`. The lemmas `SaadSparse.Chapter06.lanczosV_v₁`,
  `SaadSparse.Chapter06.T_v₁` and `SaadSparse.Chapter06.lanczosBeta_succ_v₁` translate the Lanczos
  data of $v_1$ to the backbone data indexed by $r_0$.
* The statement that D-Lanczos is DIOM(2) rests on the fact that for a symmetric matrix the
  incomplete orthogonalization of Algorithm 6.6 with $k = 2$ computes the same vectors and
  coefficients as Algorithm 6.1 (`SaadSparse.Chapter06.iop_two_eq_arnoldiCGS`).
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.18: the conjugate gradient method -/

/-- The step length $\alpha_j = (r_j, r_j)/(A p_j, p_j)$ of line 3 of Algorithm 6.18, computed from
a triple $(x_j, r_j, p_j)$. -/
noncomputable def cgStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- The next residual $r_{j+1} = r_j - \alpha_j A p_j$ of line 5 of Algorithm 6.18, computed from a
triple $(x_j, r_j, p_j)$. -/
noncomputable def cgStepR (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - cgStepAlpha A s • op A s.2.2

/-- The coefficient $\beta_j = (r_{j+1}, r_{j+1})/(r_j, r_j)$ of line 6 of Algorithm 6.18, computed
from a triple $(x_j, r_j, p_j)$. -/
noncomputable def cgStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (cgStepR A s) (cgStepR A s) / inner 𝕜 s.2.1 s.2.1

/-- **Algorithm 6.18** of [saad2003iterative], one step. The map that sends a triple
$(x_j, r_j, p_j)$ to $(x_{j+1}, r_{j+1}, p_{j+1})$ by lines 3–7 of the algorithm:
$$\alpha_j = \frac{(r_j, r_j)}{(A p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  r_{j+1} = r_j - \alpha_j A p_j, \quad \beta_j = \frac{(r_{j+1}, r_{j+1})}{(r_j, r_j)}, \quad
  p_{j+1} = r_{j+1} + \beta_j p_j.$$

The scalars are `SaadSparse.Chapter06.cgStepAlpha` and `SaadSparse.Chapter06.cgStepBeta`. A
quotient with denominator $0$ is $0$. -/
noncomputable def cgStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + cgStepAlpha A s • s.2.2, cgStepR A s, cgStepR A s + cgStepBeta A s • s.2.2)

/-- **Algorithm 6.18** of [saad2003iterative] (conjugate gradient). For
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the triple
$(x_j, r_j, p_j)$ after $j$ steps of the algorithm, started from $r_0 = b - A x_0$ and
$p_0 = r_0$.

The iteration has no stopping test. A quotient with denominator $0$ is $0$, so for a positive
definite $A$ the iterate stays fixed once a residual vanishes
(`SaadSparse.Chapter06.cgP_eq_zero_of_cgR_eq_zero`). -/
noncomputable def cg (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (cgStep A)^[j] (x₀, b - op A x₀, b - op A x₀)

/-- The step length `SaadSparse.Chapter06.cgStepAlpha` is $(r_j, r_j)/(A p_j, p_j)$. -/
theorem cgStepAlpha_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepAlpha A s = inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2) := rfl

/-- The residual `SaadSparse.Chapter06.cgStepR` is $r_j - \alpha_j A p_j$. -/
theorem cgStepR_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepR A s = s.2.1 - cgStepAlpha A s • op A s.2.2 := rfl

/-- The coefficient `SaadSparse.Chapter06.cgStepBeta` is $(r_{j+1}, r_{j+1})/(r_j, r_j)$. -/
theorem cgStepBeta_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepBeta A s = inner 𝕜 (cgStepR A s) (cgStepR A s) / inner 𝕜 s.2.1 s.2.1 := rfl

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The iterate $x_j$ of Algorithm 6.18 after $j$ steps. -/
noncomputable def cgX (j : ℕ) : 𝔼 := (cg A b x₀ j).1

/-- The residual $r_j$ of Algorithm 6.18 after $j$ steps. -/
noncomputable def cgR (j : ℕ) : 𝔼 := (cg A b x₀ j).2.1

/-- The search direction $p_j$ of Algorithm 6.18 after $j$ steps. -/
noncomputable def cgP (j : ℕ) : 𝔼 := (cg A b x₀ j).2.2

/-- **Algorithm 6.18** of [saad2003iterative], the step length. For $j \ge 0$, the scalar
$$\alpha_j = \frac{(r_j, r_j)}{(A p_j, p_j)}$$
computed on line 3 of Algorithm 6.18 at step $j$.

It is $0$ when $(A p_j, p_j) = 0$. -/
noncomputable def cgAlpha (j : ℕ) : 𝕜 := cgStepAlpha A (cg A b x₀ j)

/-- The coefficient $\beta_j = (r_{j+1}, r_{j+1})/(r_j, r_j)$ computed on line 6 of Algorithm 6.18
at step $j$. -/
noncomputable def cgBeta (j : ℕ) : 𝕜 := cgStepBeta A (cg A b x₀ j)

/-- The triple after $j + 1$ steps of Algorithm 6.18 is one step applied to the triple after $j$
steps. -/
theorem cg_succ (j : ℕ) : cg A b x₀ (j + 1) = cgStep A (cg A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate $x_0$ of Algorithm 6.18 is the initial guess. -/
@[simp] theorem cgX_zero : cgX A b x₀ 0 = x₀ := rfl

/-- The residual $r_0$ of Algorithm 6.18 is $b - A x_0$. -/
@[simp] theorem cgR_zero : cgR A b x₀ 0 = b - op A x₀ := rfl

/-- Algorithm 6.18, line 1: $p_0 = r_0$. -/
@[simp] theorem cgP_zero : cgP A b x₀ 0 = cgR A b x₀ 0 := rfl

/-- Equation (6.92): $\alpha_j = (r_j, r_j)/(A p_j, p_j)$. -/
theorem cgAlpha_eq (j : ℕ) : cgAlpha A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j)) := rfl

/-- Equation (6.90): $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem cgX_succ (j : ℕ) :
    cgX A b x₀ (j + 1) = cgX A b x₀ j + cgAlpha A b x₀ j • cgP A b x₀ j := by
  rw [cgX, cg_succ]
  rfl

/-- Equation (6.91): $r_{j+1} = r_j - \alpha_j A p_j$. -/
theorem cgR_succ (j : ℕ) :
    cgR A b x₀ (j + 1) = cgR A b x₀ j - cgAlpha A b x₀ j • op A (cgP A b x₀ j) := by
  rw [cgR, cg_succ]
  rfl

/-- The residual $r_{j+1}$ is the residual computed by `SaadSparse.Chapter06.cgStepR` from the
triple at step $j$. -/
theorem cgR_succ_eq_cgStepR (j : ℕ) : cgR A b x₀ (j + 1) = cgStepR A (cg A b x₀ j) := by
  rw [cgR, cg_succ]
  rfl

/-- Algorithm 6.18, line 6: $\beta_j = (r_{j+1}, r_{j+1})/(r_j, r_j)$. -/
theorem cgBeta_eq (j : ℕ) : cgBeta A b x₀ j =
    inner 𝕜 (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) /
      inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) := by
  rw [cgBeta, cgStepBeta_def, cgR_succ_eq_cgStepR]
  rfl

/-- Equation (6.93): $p_{j+1} = r_{j+1} + \beta_j p_j$. -/
theorem cgP_succ (j : ℕ) :
    cgP A b x₀ (j + 1) = cgR A b x₀ (j + 1) + cgBeta A b x₀ j • cgP A b x₀ j := by
  rw [cgP, cg_succ, cgR_succ_eq_cgStepR]
  rfl

/-- Equation (6.94) without division: $\alpha_j A p_j = r_j - r_{j+1}$. -/
theorem cgAlpha_smul_apply_cgP (j : ℕ) :
    cgAlpha A b x₀ j • op A (cgP A b x₀ j) = cgR A b x₀ j - cgR A b x₀ (j + 1) := by
  rw [cgR_succ]
  abel

/-! ### Identification with the backbone conjugate gradient recurrence -/

private theorem cgStepAlpha_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepAlpha A (s.x, s.r, s.p) = CG.alpha (op A) s := by
  change (inner 𝕜 s.r s.r / inner 𝕜 s.p (op A s.p) : 𝕜)
    = inner 𝕜 s.r s.r / inner 𝕜 (op A s.p) s.p
  rw [hA s.p s.p]

private theorem cgStepR_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepR A (s.x, s.r, s.p) = (CG.step (op A) s).r := by
  rw [cgStepR_def, cgStepAlpha_eq_CG A hA s, CG.step_r]

private theorem cgStepBeta_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepBeta A (s.x, s.r, s.p) = CG.beta (op A) s := by
  rw [cgStepBeta_def, cgStepR_eq_CG A hA s]
  rfl

private theorem cgStep_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStep A (s.x, s.r, s.p) =
      ((CG.step (op A) s).x, (CG.step (op A) s).r, (CG.step (op A) s).p) := by
  rw [cgStep, cgStepAlpha_eq_CG A hA s, cgStepR_eq_CG A hA s, cgStepBeta_eq_CG A hA s,
    CG.step_x, CG.step_p]

/-- Algorithm 6.18 is the backbone conjugate gradient recurrence. Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian. Then for every $j \ge 0$ the triple
$(x_j, r_j, p_j)$ of Algorithm 6.18 is the triple of iterate, residual and direction of
`CG.iterate (op A) b x₀ j`.

The symmetry of $A$ is needed only to move $A$ across the inner product in $\alpha_j$. -/
theorem cg_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cg A b x₀ j = ((CG.iterate (op A) b x₀ j).x, (CG.iterate (op A) b x₀ j).r,
      (CG.iterate (op A) b x₀ j).p) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cg_succ, ih, CG.iterate_succ, cgStep_eq_CG A hA]

/-- For a Hermitian $A$, the iterate $x_j$ of Algorithm 6.18 is that of `CG.iterate`. -/
theorem cgX_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgX A b x₀ j = (CG.iterate (op A) b x₀ j).x := by rw [cgX, cg_eq_CG A b x₀ hA]

/-- For a Hermitian $A$, the residual $r_j$ of Algorithm 6.18 is that of `CG.iterate`. -/
theorem cgR_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgR A b x₀ j = (CG.iterate (op A) b x₀ j).r := by rw [cgR, cg_eq_CG A b x₀ hA]

/-- For a Hermitian $A$, the direction $p_j$ of Algorithm 6.18 is that of `CG.iterate`. -/
theorem cgP_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgP A b x₀ j = (CG.iterate (op A) b x₀ j).p := by rw [cgP, cg_eq_CG A b x₀ hA]

/-- For a Hermitian $A$, the step length $\alpha_j$ of Algorithm 6.18 is `CG.alpha` at the state of
`CG.iterate`. -/
theorem cgAlpha_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgAlpha A b x₀ j = CG.alpha (op A) (CG.iterate (op A) b x₀ j) := by
  rw [cgAlpha, cg_eq_CG A b x₀ hA, cgStepAlpha_eq_CG A hA]

/-- For a Hermitian $A$, the coefficient $\beta_j$ of Algorithm 6.18 is `CG.beta` at the state of
`CG.iterate`. -/
theorem cgBeta_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgBeta A b x₀ j = CG.beta (op A) (CG.iterate (op A) b x₀ j) := by
  rw [cgBeta, cg_eq_CG A b x₀ hA, cgStepBeta_eq_CG A hA]

/-- For a Hermitian $A$, the residual carried by Algorithm 6.18 is the true residual:
$r_j = b - A x_j$. -/
theorem cgR_eq_residual (hA : (op A).IsSymmetric) (j : ℕ) :
    cgR A b x₀ j = b - op A (cgX A b x₀ j) := by
  rw [cgR_eq_CG A b x₀ hA, cgX_eq_CG A b x₀ hA, CG.residual_eq]

/-! ### The orthogonality relations of Section 6.7.1 for Algorithm 6.18 -/

/-- A Hermitian positive definite matrix $A$ defines a symmetric coercive operator $x \mapsto Ax$ on
$\mathbb{K}^n$. -/
theorem isSymmetricCoercive_op_of_posDef {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) :
    (op A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

variable {A b x₀}

/-- For a Hermitian positive definite $A$, the residuals of Algorithm 6.18 are mutually orthogonal:
$(r_i, r_j) = 0$ for $i \ne j$. -/
theorem inner_cgR_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (cgR A b x₀ i) (cgR A b x₀ j) = 0 := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$, the search directions of Algorithm 6.18 are
$A$-conjugate: $(A p_i, p_j) = 0$ for $i \ne j$. -/
theorem inner_apply_cgP_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (op A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  rw [cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$: $(r_i, p_j) = 0$ for $j < i$. This is the Galerkin
condition in the form used in Section 6.7.1. -/
theorem inner_cgR_cgP_eq_zero (hA : A.PosDef) {i j : ℕ} (h : j < i) :
    inner 𝕜 (cgR A b x₀ i) (cgP A b x₀ j) = 0 := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$: $(r_i, p_j) = \|r_j\|_2^2$ for $i \le j$. -/
theorem inner_cgR_cgP (hA : A.PosDef) {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (cgR A b x₀ i) (cgP A b x₀ j) = ((‖cgR A b x₀ j‖ ^ 2 : ℝ) : 𝕜) := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_direction_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- For a Hermitian positive definite $A$: if $r_j = 0$, then $p_j = 0$. So Algorithm 6.18 is
stationary after a breakdown. -/
theorem cgP_eq_zero_of_cgR_eq_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j = 0) :
    cgP A b x₀ j = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgP_eq_CG A b x₀ hs]
  exact CG.direction_eq_zero_of_residual_eq_zero (op A) b x₀ (by rwa [cgR_eq_CG A b x₀ hs] at hr)

/-- For a Hermitian positive definite $A$: if $r_j \ne 0$, then $(A p_j, p_j) \ne 0$. So Algorithm
6.18 is well defined until the residual vanishes. -/
theorem inner_cgP_apply_cgP_ne_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j)) ≠ 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  have hp := CG.re_inner_apply_direction_pos b x₀ (isSymmetricCoercive_op_of_posDef hA)
    (k := j) (by rwa [cgR_eq_CG A b x₀ hs] at hr)
  rw [← cgP_eq_CG A b x₀ hs, hs (cgP A b x₀ j) (cgP A b x₀ j)] at hp
  intro h
  rw [h] at hp
  simp at hp

/-- For a Hermitian positive definite $A$: if $r_j \ne 0$, then $\alpha_j \ne 0$. -/
theorem cgAlpha_ne_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    cgAlpha A b x₀ j ≠ 0 := by
  rw [cgAlpha_eq]
  exact div_ne_zero (fun h => hr (inner_self_eq_zero.1 h)) (inner_cgP_apply_cgP_ne_zero hA hr)

/-- Equation (6.92), second form: for a Hermitian positive definite $A$,
$(A p_j, p_j) = (A p_j, r_j)$, because $p_j - r_j$ is a multiple of $p_{j-1}$ and the directions
are $A$-conjugate. -/
theorem inner_cgP_apply_cgP_eq (hA : A.PosDef) (j : ℕ) :
    inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j))
      = inner 𝕜 (cgR A b x₀ j) (op A (cgP A b x₀ j)) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  cases j with
  | zero => rw [cgP_zero]
  | succ j =>
    have hconj : inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ (j + 1))) = 0 := by
      rw [← hs (cgP A b x₀ j) (cgP A b x₀ (j + 1))]
      exact inner_apply_cgP_eq_zero hA (by omega)
    nth_rewrite 1 [cgP_succ]
    rw [inner_add_left, inner_smul_left, hconj, mul_zero, add_zero]

/-- Equation (6.92): for a Hermitian positive definite $A$, $\alpha_j = (r_j, r_j)/(A p_j, r_j)$,
the form that the derivation in the book produces. -/
theorem cgAlpha_eq' (hA : A.PosDef) (j : ℕ) : cgAlpha A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgP A b x₀ j)) := by
  rw [cgAlpha_eq, inner_cgP_apply_cgP_eq hA]

/-- Equation (6.94): for a Hermitian positive definite $A$, if $r_j \ne 0$, then
$A p_j = -\alpha_j^{-1} (r_{j+1} - r_j)$. -/
theorem apply_cgP_eq (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    op A (cgP A b x₀ j) =
      -((cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ (j + 1) - cgR A b x₀ j)) := by
  have h2 : -((cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ (j + 1) - cgR A b x₀ j))
      = (cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ j - cgR A b x₀ (j + 1)) := by
    rw [← smul_neg, neg_sub]
  rw [h2, ← cgAlpha_smul_apply_cgP, smul_smul, inv_mul_cancel₀ (cgAlpha_ne_zero hA hr), one_smul]

variable (A b x₀)

/-! ### Algorithm 6.19: the three-term recurrence variant -/

private theorem inner_self_div (x y : 𝔼) :
    inner 𝕜 x x / inner 𝕜 y y = ((‖x‖ ^ 2 / ‖y‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- **Algorithm 6.19** of [saad2003iterative], line 3. For the residuals $r_j$ of Algorithm 6.18,
the scalar
$$\gamma_j = \frac{(r_j, r_j)}{(A r_j, r_j)}.$$

The definition uses the residuals of Algorithm 6.18, not those of the three-term recurrence.
`SaadSparse.Chapter06.cg3_eq` shows that the two agree. The scalar is $0$ when
$(A r_j, r_j) = 0$. -/
noncomputable def cgGamma (j : ℕ) : 𝕜 :=
  inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgR A b x₀ j))

/-- The scalar `SaadSparse.Chapter06.cgGamma` is $(r_j, r_j)/(A r_j, r_j)$. -/
theorem cgGamma_def (j : ℕ) : cgGamma A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgR A b x₀ j)) := rfl

/-- The scalars $\rho_j$ of line 4 of Algorithm 6.19, computed from the residuals of Algorithm 6.18:
$\rho_0 = 1$ and, for $j \ge 1$, (6.97)
$$\rho_j = \left(1 - \frac{\gamma_j}{\gamma_{j-1}} \cdot \frac{(r_j, r_j)}{(r_{j-1}, r_{j-1})}
  \cdot \frac{1}{\rho_{j-1}}\right)^{-1}.$$
-/
noncomputable def cgRho (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝕜
  | 0 => 1
  | j + 1 => (1 - cgGamma A b x₀ (j + 1) / cgGamma A b x₀ j *
      (inner 𝕜 (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) /
        inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j)) / cgRho A b x₀ j)⁻¹

/-- $\rho_0 = 1$. -/
@[simp] theorem cgRho_zero : cgRho A b x₀ 0 = 1 := rfl

/-- Equation (6.97) with norms: $\rho_{j+1} = \left(1 - \frac{\gamma_{j+1}}{\gamma_j} \cdot
\frac{\|r_{j+1}\|^2}{\|r_j\|^2} \cdot \frac{1}{\rho_j}\right)^{-1}$. -/
theorem cgRho_succ (j : ℕ) : cgRho A b x₀ (j + 1) =
    (1 - cgGamma A b x₀ (j + 1) / cgGamma A b x₀ j *
      ((‖cgR A b x₀ (j + 1)‖ ^ 2 / ‖cgR A b x₀ j‖ ^ 2 : ℝ) : 𝕜) / cgRho A b x₀ j)⁻¹ := by
  rw [cgRho, inner_self_div]

/-- For a Hermitian $A$, the scalar $\gamma_j$ is the backbone `CG.gamma (op A) b x₀ j`. -/
theorem cgGamma_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgGamma A b x₀ j = CG.gamma (op A) b x₀ j := by
  have h : CG.gamma (op A) b x₀ j =
      inner 𝕜 (CG.iterate (op A) b x₀ j).r (CG.iterate (op A) b x₀ j).r /
        inner 𝕜 (CG.iterate (op A) b x₀ j).r (op A (CG.iterate (op A) b x₀ j).r) := by
    change inner 𝕜 _ _ / inner 𝕜 (op A _) _ = _
    rw [hA _ _]
  rw [h, cgGamma_def, cgR_eq_CG A b x₀ hA]

/-- For a Hermitian $A$, the scalar $\rho_j$ is the backbone `CG.rho (op A) b x₀ j`. -/
theorem cgRho_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgRho A b x₀ j = CG.rho (op A) b x₀ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hCG : CG.rho (op A) b x₀ (j + 1) =
        (1 - CG.gamma (op A) b x₀ (j + 1) / CG.gamma (op A) b x₀ j *
          ((‖(CG.iterate (op A) b x₀ (j + 1)).r‖ ^ 2 /
            ‖(CG.iterate (op A) b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) / CG.rho (op A) b x₀ j)⁻¹ := rfl
    rw [cgRho_succ, hCG, ih, cgGamma_eq_CG A b x₀ hA, cgGamma_eq_CG A b x₀ hA,
      cgR_eq_CG A b x₀ hA, cgR_eq_CG A b x₀ hA]

variable {A b x₀}

/-- **Equation (6.98)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
positive definite, and let the residuals $r_0, \dots, r_m$ of Algorithm 6.18 be nonzero. Then
the iterates of Algorithm 6.18 satisfy
$$x_{m+1} = \rho_m (x_m + \gamma_m r_m) + (1 - \rho_m) x_{m-1}.$$

For $m = 0$ the term $x_{m-1}$ is $x_0$, because the natural number $0 - 1$ is $0$ in Lean. This
does no harm, because $\rho_0 = 1$. The scalars $\rho_m$ and $\gamma_m$ are
`SaadSparse.Chapter06.cgRho` and `SaadSparse.Chapter06.cgGamma`. -/
theorem equation_6_98 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m, cgR A b x₀ j ≠ 0) :
    cgX A b x₀ (m + 1) = cgRho A b x₀ m • (cgX A b x₀ m + cgGamma A b x₀ m • cgR A b x₀ m) +
      (1 - cgRho A b x₀ m) • cgX A b x₀ (m - 1) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgX_eq_CG A b x₀ hs, cgX_eq_CG A b x₀ hs, cgX_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs,
    cgRho_eq_CG A b x₀ hs, cgGamma_eq_CG A b x₀ hs]
  exact CG.iterate_succ_eq_three_term b x₀ (isSymmetricCoercive_op_of_posDef hA) m
    fun j hj => by rw [← cgR_eq_CG A b x₀ hs]; exact hr j hj

/-- **Equation (6.96)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
positive definite, and let the residuals $r_0, \dots, r_m$ of Algorithm 6.18 be nonzero. Then
$$r_{m+1} = \rho_m (r_m - \gamma_m A r_m) + (1 - \rho_m) r_{m-1}.$$

For $m = 0$ the term $r_{m-1}$ is $r_0$, because the natural number $0 - 1$ is $0$ in Lean. This
does no harm, because $\rho_0 = 1$. -/
theorem equation_6_96 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m, cgR A b x₀ j ≠ 0) :
    cgR A b x₀ (m + 1) =
      cgRho A b x₀ m • (cgR A b x₀ m - cgGamma A b x₀ m • op A (cgR A b x₀ m)) +
        (1 - cgRho A b x₀ m) • cgR A b x₀ (m - 1) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgR_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs,
    cgRho_eq_CG A b x₀ hs, cgGamma_eq_CG A b x₀ hs]
  exact CG.residual_succ_eq_three_term b x₀ (isSymmetricCoercive_op_of_posDef hA) m
    fun j hj => by rw [← cgR_eq_CG A b x₀ hs]; exact hr j hj

variable (A b x₀)

/-- The state of Algorithm 6.19 after $j$ steps: $(x_j, x_{j-1}, r_j, r_{j-1}, \rho_{j-1},
\gamma_{j-1})$.

The initial state has $x_{-1} = 0$, as in the book, and $r_{-1} = 0$. With $r_{-1} = 0$ the
quotient $(r_0, r_0)/(r_{-1}, r_{-1})$ is $0$ in Lean, so the formula of line 4 gives
$\rho_0 = 1$, as line 1 of the book requires. -/
structure CG3State (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] where
  /-- The current iterate $x_j$. -/
  x : EuclideanSpace 𝕜 (Fin n)
  /-- The previous iterate $x_{j-1}$. -/
  xPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The current residual $r_j$. -/
  r : EuclideanSpace 𝕜 (Fin n)
  /-- The previous residual $r_{j-1}$. -/
  rPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The previous coefficient $\rho_{j-1}$. -/
  rho : 𝕜
  /-- The previous coefficient $\gamma_{j-1}$. -/
  gamma : 𝕜

/-- The scalar $\gamma_j = (r_j, r_j)/(A r_j, r_j)$ of line 3 of Algorithm 6.19, computed from the
state. -/
noncomputable def cg3StepGamma (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : 𝕜 :=
  inner 𝕜 s.r s.r / inner 𝕜 s.r (op A s.r)

/-- The scalar $\rho_j$ of (6.97), line 4 of Algorithm 6.19, computed from the state: $\rho_j =
\left(1 - \frac{\gamma_j}{\gamma_{j-1}} \cdot \frac{(r_j, r_j)}{(r_{j-1}, r_{j-1})} \cdot
\frac{1}{\rho_{j-1}}\right)^{-1}$. -/
noncomputable def cg3StepRho (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : 𝕜 :=
  (1 - cg3StepGamma A s / s.gamma * (inner 𝕜 s.r s.r / inner 𝕜 s.rPrev s.rPrev) / s.rho)⁻¹

/-- One pass through lines 3–6 of Algorithm 6.19: with $\gamma_j$ and $\rho_j$ computed from the
state, $x_{j+1} = \rho_j (x_j + \gamma_j r_j) + (1 - \rho_j) x_{j-1}$ and $r_{j+1} = \rho_j
(r_j - \gamma_j A r_j) + (1 - \rho_j) r_{j-1}$. -/
noncomputable def cg3Step (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : CG3State n 𝕜 :=
  { x := cg3StepRho A s • (s.x + cg3StepGamma A s • s.r) + (1 - cg3StepRho A s) • s.xPrev,
    xPrev := s.x,
    r := cg3StepRho A s • (s.r - cg3StepGamma A s • op A s.r) + (1 - cg3StepRho A s) • s.rPrev,
    rPrev := s.r,
    rho := cg3StepRho A s,
    gamma := cg3StepGamma A s }

/-- The initial state of Algorithm 6.19, line 1: $x_0$, $x_{-1} = 0$, $r_0 = b - A x_0$ and
$r_{-1} = 0$. The stored previous coefficients are both $1$; the value $\rho_0 = 1$ follows from
$r_{-1} = 0$. -/
noncomputable def cg3Init (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : CG3State n 𝕜 :=
  { x := x₀, xPrev := 0, r := b - op A x₀, rPrev := 0, rho := 1, gamma := 1 }

/-- **Algorithm 6.19** of [saad2003iterative] (conjugate gradient, three-term recurrence variant).
For $A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $j \ge 0$, this is the state
of the algorithm after $j$ steps from the initial state of line 1.

The initial state is `SaadSparse.Chapter06.cg3Init`, and one step is
`SaadSparse.Chapter06.cg3Step`. A quotient with denominator $0$ is $0$. -/
noncomputable def cg3 (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : CG3State n 𝕜 :=
  (cg3Step A)^[j] (cg3Init A b x₀)

/-- The scalar `SaadSparse.Chapter06.cg3StepGamma` is $(r_j, r_j)/(A r_j, r_j)$. -/
theorem cg3StepGamma_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3StepGamma A s = inner 𝕜 s.r s.r / inner 𝕜 s.r (op A s.r) := rfl

/-- The scalar `SaadSparse.Chapter06.cg3StepRho` is given by the formula (6.97). -/
theorem cg3StepRho_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3StepRho A s =
      (1 - cg3StepGamma A s / s.gamma * (inner 𝕜 s.r s.r / inner 𝕜 s.rPrev s.rPrev) / s.rho)⁻¹ :=
  rfl

/-- One pass of Algorithm 6.19 gives the state $(x_{j+1}, x_j, r_{j+1}, r_j, \rho_j, \gamma_j)$ with
the updates of lines 5 and 6. -/
theorem cg3Step_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3Step A s =
      { x := cg3StepRho A s • (s.x + cg3StepGamma A s • s.r) + (1 - cg3StepRho A s) • s.xPrev,
        xPrev := s.x,
        r := cg3StepRho A s • (s.r - cg3StepGamma A s • op A s.r) +
          (1 - cg3StepRho A s) • s.rPrev,
        rPrev := s.r, rho := cg3StepRho A s, gamma := cg3StepGamma A s } := rfl

/-- The state after $j + 1$ steps of Algorithm 6.19 is one step applied to the state after $j$
steps. -/
theorem cg3_succ (j : ℕ) : cg3 A b x₀ (j + 1) = cg3Step A (cg3 A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

private theorem cg3Step_state (j : ℕ) :
    cg3Step A
      { x := cgX A b x₀ (j + 1), xPrev := cgX A b x₀ j, r := cgR A b x₀ (j + 1),
        rPrev := cgR A b x₀ j, rho := cgRho A b x₀ j, gamma := cgGamma A b x₀ j } =
      { x := cgRho A b x₀ (j + 1) •
            (cgX A b x₀ (j + 1) + cgGamma A b x₀ (j + 1) • cgR A b x₀ (j + 1)) +
          (1 - cgRho A b x₀ (j + 1)) • cgX A b x₀ j,
        xPrev := cgX A b x₀ (j + 1),
        r := cgRho A b x₀ (j + 1) •
            (cgR A b x₀ (j + 1) - cgGamma A b x₀ (j + 1) • op A (cgR A b x₀ (j + 1))) +
          (1 - cgRho A b x₀ (j + 1)) • cgR A b x₀ j,
        rPrev := cgR A b x₀ (j + 1),
        rho := cgRho A b x₀ (j + 1),
        gamma := cgGamma A b x₀ (j + 1) } := rfl

private theorem cg3_zero : cg3 A b x₀ 0 = cg3Init A b x₀ := rfl

private theorem cg3StepGamma_init :
    cg3StepGamma A (cg3Init A b x₀) = cgGamma A b x₀ 0 := rfl

private theorem cg3StepRho_init : cg3StepRho A (cg3Init A b x₀) = 1 := by
  rw [cg3StepRho_def]
  simp [cg3Init]

variable {A b x₀}

/-- Algorithm 6.19 computes the conjugate gradient iterates. Let $A \in \mathbb{K}^{n \times n}$ be
Hermitian positive definite, and let the residuals $r_0, \dots, r_j$ of Algorithm 6.18 be
nonzero. Then the state of Algorithm 6.19 after $j + 1$ steps is
$(x_{j+1}, x_j, r_{j+1}, r_j, \rho_j, \gamma_j)$, with the iterates and residuals of Algorithm
6.18. -/
theorem cg3_eq (hA : A.PosDef) {j : ℕ} (hr : ∀ i ≤ j, cgR A b x₀ i ≠ 0) :
    cg3 A b x₀ (j + 1) =
      { x := cgX A b x₀ (j + 1), xPrev := cgX A b x₀ j, r := cgR A b x₀ (j + 1),
        rPrev := cgR A b x₀ j, rho := cgRho A b x₀ j, gamma := cgGamma A b x₀ j } := by
  induction j with
  | zero =>
    rw [cg3_succ, cg3_zero, cg3Step_def, cg3StepRho_init, cg3StepGamma_init,
      equation_6_98 hA (m := 0) hr, equation_6_96 hA (m := 0) hr]
    simp [cg3Init]
  | succ j ih =>
    rw [cg3_succ, ih (fun i hi => hr i (by omega)), cg3Step_state,
      equation_6_98 hA (m := j + 1) hr, equation_6_96 hA (m := j + 1) hr]
    simp

/-- **Exercise P-6.17** of [saad2003iterative]: the coefficient (6.97) is forced by the recurrence
(6.96) and the orthogonality of the residuals. Let $A \in \mathbb{K}^{n \times n}$ be Hermitian
positive definite, and let the residuals $r_0, \dots, r_{m+1}$ of Algorithm 6.18 be nonzero. If
a scalar $\rho$ satisfies
$$r_{m+2} = \rho (r_{m+1} - \gamma_{m+1} A r_{m+1}) + (1 - \rho) r_m,$$
then $\rho = \rho_{m+1}$, the scalar of (6.97). -/
theorem equation_6_97_of_eq_6_96 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m + 1, cgR A b x₀ j ≠ 0)
    {ρ : 𝕜}
    (h96 : cgR A b x₀ (m + 2) =
      ρ • (cgR A b x₀ (m + 1) - cgGamma A b x₀ (m + 1) • op A (cgR A b x₀ (m + 1))) +
        (1 - ρ) • cgR A b x₀ m) :
    ρ = cgRho A b x₀ (m + 1) := by
  set c := cgRho A b x₀ (m + 1) with hc
  set X := cgGamma A b x₀ (m + 1) *
    inner 𝕜 (cgR A b x₀ m) (op A (cgR A b x₀ (m + 1))) + inner 𝕜 (cgR A b x₀ m) (cgR A b x₀ m)
    with hX
  have key : ∀ σ : 𝕜, cgR A b x₀ (m + 2) =
      σ • (cgR A b x₀ (m + 1) - cgGamma A b x₀ (m + 1) • op A (cgR A b x₀ (m + 1))) +
        (1 - σ) • cgR A b x₀ m → σ * X = inner 𝕜 (cgR A b x₀ m) (cgR A b x₀ m) := by
    intro σ hσ
    have h := congrArg (fun z => (inner 𝕜 (cgR A b x₀ m) z : 𝕜)) hσ
    simp only [inner_add_right, inner_smul_right, inner_sub_right] at h
    rw [inner_cgR_eq_zero hA (show m ≠ m + 2 by omega),
      inner_cgR_eq_zero hA (show m ≠ m + 1 by omega)] at h
    rw [hX]
    linear_combination h
  have hcX := key c (equation_6_96 hA (m := m + 1) hr)
  have hρX := key ρ h96
  have hXne : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcX
    exact hr m (by omega) (inner_self_eq_zero.1 hcX.symm)
  exact mul_right_cancel₀ hXne (hρX.trans hcX.symm)

end General

section Real

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### Algorithm 6.16: the Lanczos method for linear systems -/

/-- The vector $y_m = T_m^{-1}(\beta e_1) \in \mathbb{R}^m$ of (6.86), where $\beta = \|r_0\|_2$ and
$T_m$ is computed from $v_1 = r_0/\beta$; if $T_m$ is singular, the Lean inverse is $0$ and
$y_m = 0$. -/
noncomputable def lanczosMethodY (m : ℕ) : Fin m → ℝ :=
  (T A (v₁ A b x₀) m)⁻¹ *ᵥ Krylov.firstVec ‖b - op A x₀‖ m

/-- The vector `SaadSparse.Chapter06.lanczosMethodY` is $T_m^{-1}(\beta e_1)$. -/
theorem lanczosMethodY_def (m : ℕ) : lanczosMethodY A b x₀ m =
    (T A (v₁ A b x₀) m)⁻¹ *ᵥ Krylov.firstVec ‖b - op A x₀‖ m := rfl

/-- Equation (6.86): $x_m = x_0 + V_m y_m = x_0 + \sum_{j=1}^{m} (y_m)_j v_j$, the result of $m$
steps of Algorithm 6.16 without the stopping test. -/
noncomputable def lanczosMethodAt (m : ℕ) : 𝔼 :=
  x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • lanczosV A (v₁ A b x₀) (j : ℕ)

/-- **Algorithm 6.16** of [saad2003iterative] (the Lanczos method for linear systems). For
$A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$ and $m \ge 0$, this is the
approximation
$$x_m = x_0 + V_m T_m^{-1}(\beta e_1)$$
computed by the algorithm from $v_1 = r_0/\beta$ and $\beta = \|r_0\|_2$, with the book's "if
$\beta_{j+1} = 0$ then set $m := j$ and Stop".

The stopping rule replaces $m$ by $\min(m, \mu)$, where $\mu$ is the grade of $r_0$. The iterate
for a fixed number of steps is `SaadSparse.Chapter06.lanczosMethodAt`. If $T_m$ is singular, the
Lean inverse is $0$. -/
noncomputable def lanczosMethod (m : ℕ) : 𝔼 :=
  lanczosMethodAt A b x₀ (min m (grade A (b - op A x₀)))

/-- The iterate `SaadSparse.Chapter06.lanczosMethodAt` is $x_0 + \sum_{j=1}^{m} (y_m)_j v_j$. -/
theorem lanczosMethodAt_def (m : ℕ) : lanczosMethodAt A b x₀ m =
    x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • lanczosV A (v₁ A b x₀) (j : ℕ) :=
  rfl

/-- If $m \le \mu$, the grade of $r_0$, the stopping rule of Algorithm 6.16 does not act, and the
algorithm gives the iterate for exactly $m$ steps. -/
theorem lanczosMethod_eq_lanczosMethodAt {m : ℕ} (hm : m ≤ grade A (b - op A x₀)) :
    lanczosMethod A b x₀ m = lanczosMethodAt A b x₀ m := by
  rw [lanczosMethod, min_eq_left hm]

variable {A b x₀}

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. The Lanczos vectors computed
from $v_1 = r_0/\|r_0\|_2$ are the backbone Arnoldi vectors `Arnoldi.vec (op A) r₀` of $r_0$
itself, the indexing that the backbone Krylov results use. -/
theorem lanczosV_v₁ (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (j : ℕ) :
    lanczosV A (v₁ A b x₀) j = Arnoldi.vec (op A) (b - op A x₀) j := by
  rw [lanczosV_eq A _ (isSymmetric_op_of_isSymm hA) (norm_v₁ A b x₀ hb), v₁_def]
  exact arnoldiCGS_normalize A hb j

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. The matrix $T_m$ computed from
$v_1 = r_0/\|r_0\|_2$ is the backbone Arnoldi matrix $H_m$ of $r_0$,
`Arnoldi.hessenbergSq (op A) r₀ m`. -/
theorem T_v₁ (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    T A (v₁ A b x₀) m = Arnoldi.hessenbergSq (op A) (b - op A x₀) m := by
  rw [T_eq_H A _ hA (norm_v₁ A b x₀ hb), v₁_def]
  exact H_normalize A hb m

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. For $j \ge 1$, the coefficient
$\beta_{j+1}$ computed from $v_1 = r_0/\|r_0\|_2$ is the backbone subdiagonal Arnoldi
coefficient $h_{j+1,j}$ of $r_0$. -/
theorem lanczosBeta_succ_v₁ (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (j : ℕ) :
    lanczosBeta A (v₁ A b x₀) (j + 1)
      = Arnoldi.coeff (op A) (b - op A x₀) (j + 1) j := by
  have h := lanczosBeta_succ_eq_arnoldiCoeff A (v₁ A b x₀)
    (isSymmetric_op_of_isSymm hA) (norm_v₁ A b x₀ hb) j
  have h2 : arnoldiCoeff A (v₁ A b x₀) (j + 1) j
      = Arnoldi.coeff (op A) (b - op A x₀) (j + 1) j := by
    rw [v₁_def]
    exact arnoldiCoeff_normalize A hb (j + 1) j
  rw [h2] at h
  simpa using h

/-- If $T_m$ is nonsingular, then $T_m y_m = \beta e_1$. -/
theorem mulVec_lanczosMethodY {m : ℕ} (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    T A (v₁ A b x₀) m *ᵥ lanczosMethodY A b x₀ m
      = Krylov.firstVec ‖b - op A x₀‖ m := by
  rw [lanczosMethodY_def, Matrix.mulVec_nonsing_inv_mulVec ((Matrix.isUnit_iff_isUnit_det _).2 hT)]

private theorem lanczosMethodAt_eq_sum (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    lanczosMethodAt A b x₀ m =
      x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • Arnoldi.vec (op A) (b - op A x₀) (j : ℕ) := by
  rw [lanczosMethodAt_def]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [lanczosV_v₁ hA hb])

private theorem mulVec_hessenbergSq (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ lanczosMethodY A b x₀ m
      = Krylov.firstVec ‖b - op A x₀‖ m := by
  rw [← T_v₁ hA hb]
  exact mulVec_lanczosMethodY hT

/-- Equation (6.86): let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $r_0 \ne 0$, let
$m \le \mu$, the grade of $r_0$, and let $T_m$ be nonsingular. Then the iterate
$x_m = x_0 + V_m T_m^{-1}(\beta e_1)$ is the Galerkin iterate on $\mathcal{K}_m(A, r_0)$:
$x_m - x_0 \in \mathcal{K}_m(A, r_0)$ and $b - A x_m \perp \mathcal{K}_m(A, r_0)$. -/
theorem lanczosMethodAt_isGalerkinIterate (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (lanczosMethodAt A b x₀ m) := by
  rw [lanczosMethodAt_eq_sum hA hb]
  exact (Krylov.isGalerkinIterate_iff_mulVec_eq (by rwa [← grade_eq]) _).2
    (mulVec_hessenbergSq hA hb hT)

/-- **Equation (6.87)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric,
let $r_0 = b - A x_0 \ne 0$, let $m \ge 1$, and let $T_m$ be nonsingular. Then the iterate
$x_m = x_0 + V_m y_m$ with $y_m = T_m^{-1}(\beta e_1)$ has the residual
$$b - A x_m = -\beta_{m+1} (e_m^T y_m) \, v_{m+1}.$$

The quantities $e_m^T y_m$, $\beta_{m+1}$ and $v_{m+1}$ are the last entry of
`lanczosMethodY A b x₀ m`, `lanczosBeta A (v₁ A b x₀) m` and `lanczosV A (v₁ A b x₀) m`. The
statement does not assume $m \le \mu$. -/
theorem equation_6_87 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ} (hm : 0 < m)
    (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    b - op A (lanczosMethodAt A b x₀ m) =
      -(lanczosBeta A (v₁ A b x₀) m * lanczosMethodY A b x₀ m ⟨m - 1, by omega⟩) •
        lanczosV A (v₁ A b x₀) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [lanczosMethodAt_eq_sum hA hb, lanczosV_v₁ hA hb, lanczosBeta_succ_v₁ hA hb]
  exact Krylov.residual_galerkin_eq hm (lanczosMethodY A b x₀ (k + 1))
    (mulVec_hessenbergSq hA hb hT)

/-- **Proposition 6.20(1)** of [saad2003iterative], for Algorithm 6.16. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $r_0 \ne 0$, let $m \ge 1$, and let $T_m$ be
nonsingular. Then the residual of the iterate $x_m$ of Algorithm 6.16 is a multiple of the
Lanczos vector $v_{m+1}$: there is $\sigma_m \in \mathbb{R}$ with
$$b - A x_m = \sigma_m v_{m+1}.$$

The case $m = 0$, where $r_0 = \beta v_1$, is not part of the statement. The iterate is
`SaadSparse.Chapter06.lanczosMethodAt`, without the stopping test. The form for Algorithm 6.17
is `SaadSparse.Chapter06.residual_dLanczosX`. The orthogonality of the residuals, which the book
derives from part 1, is `SaadSparse.Chapter06.inner_residual_lanczosMethodAt_eq_zero`. -/
theorem proposition_6_20_1 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ} (hm : 0 < m)
    (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    ∃ σ : ℝ, b - op A (lanczosMethodAt A b x₀ m) = σ • lanczosV A (v₁ A b x₀) m :=
  ⟨_, equation_6_87 hA hb hm hT⟩

/-- Proposition 6.20(1), second half: let $A \in \mathbb{R}^{n \times n}$ be symmetric and
$r_0 \ne 0$. If $i, j \ge 1$, $i \ne j$, and $T_i$ and $T_j$ are nonsingular, then the residuals
of the iterates $x_i$ and $x_j$ of Algorithm 6.16 are orthogonal, because each is a multiple of
a Lanczos vector. -/
theorem inner_residual_lanczosMethodAt_eq_zero (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hij : i ≠ j)
    (hTi : IsUnit (T A (v₁ A b x₀) i).det)
    (hTj : IsUnit (T A (v₁ A b x₀) j).det) :
    inner ℝ (b - op A (lanczosMethodAt A b x₀ i)) (b - op A (lanczosMethodAt A b x₀ j)) = 0 := by
  rw [equation_6_87 hA hb hi hTi, equation_6_87 hA hb hj hTj, inner_smul_left, inner_smul_right,
    lanczosV_v₁ hA hb, lanczosV_v₁ hA hb,
    Arnoldi.inner_vec_eq_zero (op A) (b - op A x₀) hij]
  simp

/-! ### Algorithm 6.17: the direct version of the Lanczos method (D-Lanczos) -/

variable (A b x₀)

/-- Equation (6.89): the diagonal entries of $U_m$ in the factorization $T_m = L_m U_m$ of (6.84),
$\eta_1 = \alpha_1$ and $\eta_{m+1} = \alpha_{m+1} - \lambda_{m+1} \beta_{m+1}$ for $m \ge 1$.
The value `dlEta A v₁ m` is $\eta_{m+1}$. -/
noncomputable def dlEta (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → ℝ
  | 0 => lanczosAlpha A v₁ 0
  | m + 1 => lanczosAlpha A v₁ (m + 1) -
      lanczosBeta A v₁ (m + 1) / dlEta A v₁ m * lanczosBeta A v₁ (m + 1)

/-- Equation (6.88): the subdiagonal entries of $L_m$, $\lambda_1 = 0$ and
$\lambda_{m+1} = \beta_{m+1}/\eta_m$ for $m \ge 1$. The value `dlLambda A v₁ m` is
$\lambda_{m+1}$. -/
noncomputable def dlLambda (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → ℝ
  | 0 => 0
  | m + 1 => lanczosBeta A v₁ (m + 1) / dlEta A v₁ m

/-- The entries of $z_m = L_m^{-1}(\beta e_1)$: $\zeta_1 = \beta$ and
$\zeta_{m+1} = -\lambda_{m+1} \zeta_m$ for $m \ge 1$. The value `dlZeta A v₁ β m` is
$\zeta_{m+1}$. -/
noncomputable def dlZeta (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) (β : ℝ) : ℕ → ℝ
  | 0 => β
  | m + 1 => -dlLambda A v₁ (m + 1) * dlZeta A v₁ β m

/-- The columns of $P_m = V_m U_m^{-1}$: $p_1 = \eta_1^{-1} v_1$ and $p_{m+1} =
\eta_{m+1}^{-1}(v_{m+1} - \beta_{m+1} p_m)$ for $m \ge 1$. The vector `dlP A v₁ m` is $p_{m+1}$. -/
noncomputable def dlP (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => (dlEta A v₁ 0)⁻¹ • lanczosV A v₁ 0
  | m + 1 => (dlEta A v₁ (m + 1))⁻¹ •
      (lanczosV A v₁ (m + 1) - lanczosBeta A v₁ (m + 1) • dlP A v₁ m)

/-- **Algorithm 6.17** of [saad2003iterative] (D-Lanczos). The iterates $x_0$ and
$x_m = x_{m-1} + \zeta_m p_m$ for $m \ge 1$, where $\zeta_m$ and $p_m$ are computed from
$v_1 = r_0/\beta$ and $\beta = \|r_0\|_2$. -/
noncomputable def dLanczosX (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => dLanczosX A b x₀ m +
      dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ m • dlP A (v₁ A b x₀) m

variable {A b x₀}

/-- $\eta_1 = \alpha_1$. -/
theorem dlEta_zero (v₁ : 𝔼) : dlEta A v₁ 0 = lanczosAlpha A v₁ 0 := rfl

/-- $\lambda_1 = 0$. -/
theorem dlLambda_zero (v₁ : 𝔼) : dlLambda A v₁ 0 = 0 := rfl

/-- Equation (6.88): $\lambda_{m+1} = \beta_{m+1}/\eta_m$ for $m \ge 1$. -/
theorem dlLambda_succ (v₁ : 𝔼) (m : ℕ) :
    dlLambda A v₁ (m + 1) = lanczosBeta A v₁ (m + 1) / dlEta A v₁ m := rfl

/-- Equation (6.89): $\eta_{m+1} = \alpha_{m+1} - \lambda_{m+1} \beta_{m+1}$ for $m \ge 1$. -/
theorem dlEta_succ (v₁ : 𝔼) (m : ℕ) : dlEta A v₁ (m + 1) =
    lanczosAlpha A v₁ (m + 1) - dlLambda A v₁ (m + 1) * lanczosBeta A v₁ (m + 1) := rfl

/-- $\zeta_1 = \beta$. -/
theorem dlZeta_zero (v₁ : 𝔼) (β : ℝ) : dlZeta A v₁ β 0 = β := rfl

/-- $\zeta_{m+1} = -\lambda_{m+1} \zeta_m$ for $m \ge 1$. -/
theorem dlZeta_succ (v₁ : 𝔼) (β : ℝ) (m : ℕ) :
    dlZeta A v₁ β (m + 1) = -dlLambda A v₁ (m + 1) * dlZeta A v₁ β m := rfl

/-- $p_1 = \eta_1^{-1} v_1$. -/
theorem dlP_zero (v₁ : 𝔼) : dlP A v₁ 0 = (dlEta A v₁ 0)⁻¹ • lanczosV A v₁ 0 := rfl

/-- $p_{m+1} = \eta_{m+1}^{-1}(v_{m+1} - \beta_{m+1} p_m)$ for $m \ge 1$. -/
theorem dlP_succ (v₁ : 𝔼) (m : ℕ) : dlP A v₁ (m + 1) = (dlEta A v₁ (m + 1))⁻¹ •
    (lanczosV A v₁ (m + 1) - lanczosBeta A v₁ (m + 1) • dlP A v₁ m) := rfl

/-- The iterate $x_0$ of Algorithm 6.17 is the initial guess. -/
@[simp] theorem dLanczosX_zero : dLanczosX A b x₀ 0 = x₀ := rfl

/-- Algorithm 6.17: $x_m = x_{m-1} + \zeta_m p_m$ for $m \ge 1$. -/
theorem dLanczosX_succ (m : ℕ) : dLanczosX A b x₀ (m + 1) = dLanczosX A b x₀ m +
    dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ m • dlP A (v₁ A b x₀) m := rfl

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $\|v_1\|_2 = 1$. For $m \ge 1$, if
$\eta_1, \dots, \eta_m$ are nonzero, then
$$A p_m = v_m + \lambda_{m+1} v_{m+1}.$$
So $A$ maps the auxiliary vectors of Algorithm 6.17 into the span of two consecutive Lanczos
vectors; this is the content of the factorization $T_m = L_m U_m$ in the form that the induction
needs. -/
theorem apply_dlP (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) :
    ∀ m : ℕ, (∀ i ≤ m, dlEta A v₁ i ≠ 0) →
      op A (dlP A v₁ m) = lanczosV A v₁ m + dlLambda A v₁ (m + 1) • lanczosV A v₁ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro hη
    have h0 : lanczosAlpha A v₁ 0 ≠ 0 := hη 0 le_rfl
    rw [dlP_zero, map_smul, apply_lanczosV_zero_real A v₁ hA hv, dlLambda_succ, dlEta_zero]
    match_scalars
    · field_simp
    · field_simp
  | succ m ih =>
    intro hη
    have hlam : dlLambda A v₁ (m + 2) = lanczosBeta A v₁ (m + 2) / dlEta A v₁ (m + 1) :=
      dlLambda_succ v₁ (m + 1)
    have hne : dlEta A v₁ (m + 1) ≠ 0 := hη (m + 1) le_rfl
    have heta := dlEta_succ (A := A) v₁ m
    rw [dlP_succ, map_smul, map_sub, map_smul, apply_lanczosV_real A v₁ hA hv,
      ih fun i hi => hη i (by omega), hlam]
    match_scalars
    · field_simp
      ring
    · field_simp
      linear_combination -heta
    · field_simp

/-- **Proposition 6.20(1)** of [saad2003iterative], for Algorithm 6.17. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. For $m \ge 0$, if
$\eta_1, \dots, \eta_m$ are nonzero, then the residual of the D-Lanczos iterate is
$b - A x_m = \zeta_{m+1} v_{m+1}$. This is the reason why the algorithm computes the Galerkin
iterate. -/
theorem residual_dLanczosX (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) :
    ∀ m : ℕ, (∀ i < m, dlEta A (v₁ A b x₀) i ≠ 0) →
      b - op A (dLanczosX A b x₀ m) =
        dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ m • lanczosV A (v₁ A b x₀) m := by
  have hv := norm_v₁ A b x₀ hb
  have hn : ‖b - op A x₀‖ ≠ 0 := norm_ne_zero_iff.2 hb
  intro m
  induction m with
  | zero =>
    intro _
    have hone : (‖b - op A x₀‖ : ℝ) • v₁ A b x₀ = b - op A x₀ := by
      rw [v₁_def, smul_smul]
      simp [mul_inv_cancel₀ hn]
    rw [dLanczosX_zero, dlZeta_zero, lanczosV_zero]
    exact hone.symm
  | succ m ih =>
    intro hη
    have h := ih fun i hi => hη i (by omega)
    have hp := apply_dlP hA hv m fun i hi => hη i (by omega)
    have hstep : b - op A (dLanczosX A b x₀ (m + 1)) = (b - op A (dLanczosX A b x₀ m)) -
        dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ m •
          op A (dlP A (v₁ A b x₀) m) := by
      rw [dLanczosX_succ, map_add, map_smul]
      abel
    rw [hstep, h, hp, dlZeta_succ]
    module

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $\|v_1\|_2 = 1$. For $m \ge 1$, the
auxiliary vector $p_m$ of Algorithm 6.17 lies in $\mathcal{K}_m(A, v_1)$. -/
theorem dlP_mem_krylov (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) (m : ℕ) :
    dlP A v₁ m ∈ krylov A v₁ (m + 1) := by
  have hA' := isSymmetric_op_of_isSymm hA
  induction m with
  | zero =>
    rw [dlP_zero]
    exact Submodule.smul_mem _ _ (lanczosV_mem_krylov A v₁ hA' hv 0)
  | succ m ih =>
    have hmono : krylov A v₁ (m + 1) ≤ krylov A v₁ (m + 2) := krylov_mono A v₁ (by omega)
    rw [dlP_succ]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (lanczosV_mem_krylov A v₁ hA' hv (m + 1)) (Submodule.smul_mem _ _ (hmono ih)))

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. For every $m$, the D-Lanczos
iterate satisfies $x_m - x_0 \in \mathcal{K}_m(A, r_0)$. -/
theorem dLanczosX_sub_mem (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    dLanczosX A b x₀ m - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) m := by
  have hv := norm_v₁ A b x₀ hb
  induction m with
  | zero => simp
  | succ m ih =>
    have hmem : dlP A (v₁ A b x₀) m ∈ Krylov.subspace (op A) (b - op A x₀) (m + 1) := by
      rw [← krylov_v₁ A b x₀]
      exact dlP_mem_krylov hA hv m
    have hmono := Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m)
    rw [dLanczosX_succ, show dLanczosX A b x₀ m + _ - x₀ = (dLanczosX A b x₀ m - x₀) +
      dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ m • dlP A (v₁ A b x₀) m from by abel]
    exact Submodule.add_mem _ (hmono ih) (Submodule.smul_mem _ _ hmem)

/-- Equations (6.86)–(6.89): let $A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \ne 0$. If
$\eta_1, \dots, \eta_m$ are nonzero, then the iterate $x_m$ of Algorithm 6.17 is the Galerkin
iterate on $\mathcal{K}_m(A, r_0)$.

For a symmetric positive definite $A$ the Galerkin iterate is unique, so $x_m$ is then the
iterate of Algorithm 6.16 (`SaadSparse.Chapter06.dLanczosX_eq_lanczosMethodAt`). -/
theorem dLanczosX_isGalerkinIterate (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ)
    (hη : ∀ i < m, dlEta A (v₁ A b x₀) i ≠ 0) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (dLanczosX A b x₀ m) := by
  have hv := norm_v₁ A b x₀ hb
  refine ⟨dLanczosX_sub_mem hA hb m, ?_⟩
  rw [residual_dLanczosX hA hb m hη]
  refine Submodule.smul_mem _ _ ?_
  rw [← krylov_v₁ A b x₀]
  exact lanczosV_mem_orthogonal A _ (isSymmetric_op_of_isSymm hA) hv m

/-! ### Section 6.7.1: the three algorithms compute the same iterates -/

/-- For a symmetric positive definite $A \in \mathbb{R}^{n \times n}$ there is at most one Galerkin
iterate on $\mathcal{K}_m(A, r_0)$. -/
theorem galerkin_unique (hA : A.PosDef) {m : ℕ} {x y : 𝔼}
    (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x)
    (hy : Krylov.IsGalerkinIterate (op A) b x₀ m y) : x = y := by
  obtain ⟨z, _, hz⟩ := Krylov.existsUnique_isGalerkinIterate_of_isCoercive
    (isSymmetricCoercive_op_of_posDef hA).isCoercive b x₀ m
  rw [hz x hx, hz y hy]

/-- For a symmetric positive definite $A \in \mathbb{R}^{n \times n}$ and every $m$, the iterate
$x_m$ of Algorithm 6.18 is the Galerkin iterate on $\mathcal{K}_m(A, r_0)$. -/
theorem cgX_isGalerkinIterate (hA : A.PosDef) (m : ℕ) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (cgX A b x₀ m) := by
  rw [cgX_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.isGalerkinIterate b x₀ (isSymmetricCoercive_op_of_posDef hA) m

/-- Section 6.7.1: the conjugate gradient algorithm is mathematically equivalent to D-Lanczos. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and $r_0 \ne 0$. If
$\eta_1, \dots, \eta_m$ are nonzero, then the iterates $x_m$ of Algorithms 6.18 and 6.17 are
equal. -/
theorem cgX_eq_dLanczosX (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) (m : ℕ)
    (hη : ∀ i < m, dlEta A (v₁ A b x₀) i ≠ 0) :
    cgX A b x₀ m = dLanczosX A b x₀ m :=
  galerkin_unique hA (cgX_isGalerkinIterate hA m)
    (dLanczosX_isGalerkinIterate hA.isSymm hb m hη)

/-- Section 6.7.1: let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and
$r_0 \ne 0$. If $\eta_1, \dots, \eta_m$ are nonzero, $m \le \mu$, the grade of $r_0$, and $T_m$
is nonsingular, then the iterate of Algorithm 6.17 is the iterate of Algorithm 6.16. -/
theorem dLanczosX_eq_lanczosMethodAt (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hη : ∀ i < m, dlEta A (v₁ A b x₀) i ≠ 0)
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    dLanczosX A b x₀ m = lanczosMethodAt A b x₀ m :=
  galerkin_unique hA (dLanczosX_isGalerkinIterate hA.isSymm hb m hη)
    (lanczosMethodAt_isGalerkinIterate hA.isSymm hb hm hT)

/-- **Section 6.7** of [saad2003iterative], Algorithm 6.16 is the full orthogonalization method for
a symmetric matrix. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $m \ge 0$, and let
$m' = \min(m, \mu)$, where $\mu$ is the grade of $v_1 = r_0/\|r_0\|_2$. If the Arnoldi matrix
$H_{m'}$ is nonsingular, then Algorithm 6.16 and FOM (Algorithm 6.4), both run with $m$ steps,
give the same approximation.

Both are the Galerkin iterate on $\mathcal{K}_{m'}(A, r_0)$. The stopping rule "if
$\beta_{j+1} = 0$ set $m := j$" of Algorithm 6.16 and the stopping rule of FOM,
`SaadSparse.Chapter06.mEff`, stop at the same step, because $v_1$ and $r_0$ have the same grade.
The hypothesis is `SaadSparse.Chapter06.FOMDefined A b x₀ (mEff A b x₀ m)`. -/
theorem lanczosMethod_eq_fom (hA : A.IsSymm) {m : ℕ}
    (hH : FOMDefined A b x₀ (mEff A b x₀ m)) :
    lanczosMethod A b x₀ m = fom A b x₀ m := by
  have hmE : mEff A b x₀ m = min m (grade A (b - op A x₀)) := by
    rw [mEff, grade_v₁, grade_eq]
  rcases eq_or_ne (b - op A x₀) 0 with hb | hb
  · have h0 : grade A (b - op A x₀) = 0 := by rw [hb, grade_eq, Krylov.grade_zero]
    rw [lanczosMethod, h0, min_zero, fom, hmE, h0, min_zero, fomFixed_zero, lanczosMethodAt_def]
    simp
  · have hT : IsUnit (T A (v₁ A b x₀) (mEff A b x₀ m)).det := by
      rw [T_v₁ hA hb, ← H_v₁ A b x₀]
      exact (Matrix.isUnit_iff_isUnit_det _).1 hH
    rw [lanczosMethod, ← hmE, fom]
    exact eq_fomFixed_of_isGalerkinIterate A b x₀ hH (mEff_le A b x₀ m)
      (lanczosMethodAt_isGalerkinIterate hA hb (hmE ▸ min_le_right m _) hT)

/-- Section 6.7.1: let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and
$r_0 \ne 0$. If $m \le \mu$, the grade of $r_0$, and $T_m$ is nonsingular, then the iterate of
Algorithm 6.18 is the iterate of Algorithm 6.16. -/
theorem cgX_eq_lanczosMethodAt (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (v₁ A b x₀) m).det) :
    cgX A b x₀ m = lanczosMethodAt A b x₀ m :=
  galerkin_unique hA (cgX_isGalerkinIterate hA m)
    (lanczosMethodAt_isGalerkinIterate hA.isSymm hb hm hT)

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric and $\|v_1\|_2 = 1$. Then $(v_k, p_j) = 0$ for
$k > j \ge 1$, because the auxiliary vector $p_j$ of Algorithm 6.17 lies in $\mathcal{K}_j$. -/
theorem inner_lanczosV_dlP_eq_zero (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) :
    ∀ (j : ℕ) {k : ℕ}, j < k → inner ℝ (lanczosV A v₁ k) (dlP A v₁ j) = 0 := by
  have hA' := isSymmetric_op_of_isSymm hA
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [dlP_zero, real_inner_smul_right, inner_lanczosV_eq_zero A v₁ hA' hv (by omega), mul_zero]
  | succ j ih =>
    intro k hk
    rw [dlP_succ, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      inner_lanczosV_eq_zero A v₁ hA' hv (show k ≠ j + 1 by omega), ih (by omega), mul_zero,
      sub_zero, mul_zero]

/-- **Proposition 6.20(2)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, let $\|v_1\|_2 = 1$, and let $p_1, p_2, \dots$ be the auxiliary vectors of Algorithm
6.17 computed from $v_1$. If $i \ne j$ and $\eta_1, \dots, \eta_{\max(i, j)}$ are nonzero, then
$$(A p_i, p_j) = 0.$$
So the vectors $p_i$ form an $A$-conjugate set.

The vectors are `SaadSparse.Chapter06.dlP`, indexed from $0$: `dlP A v₁ i` is $p_{i+1}$. The
statement holds for every unit starting vector $v_1$, not only for $r_0/\|r_0\|_2$. -/
theorem proposition_6_20_2 (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) {i j : ℕ} (hij : i ≠ j)
    (hη : ∀ k ≤ max i j, dlEta A v₁ k ≠ 0) :
    inner ℝ (op A (dlP A v₁ i)) (dlP A v₁ j) = 0 := by
  have key : ∀ a c : ℕ, c < a → (∀ k ≤ a, dlEta A v₁ k ≠ 0) →
      inner ℝ (op A (dlP A v₁ a)) (dlP A v₁ c) = 0 := by
    intro a c hca hη'
    rw [apply_dlP hA hv a hη', inner_add_left, real_inner_smul_left,
      inner_lanczosV_dlP_eq_zero hA hv c (by omega),
      inner_lanczosV_dlP_eq_zero hA hv c (by omega), mul_zero, add_zero]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [isSymmetric_op_of_isSymm hA (dlP A v₁ i) (dlP A v₁ j), real_inner_comm]
    exact key j i h fun k hk => hη k (hk.trans (le_max_right i j))
  · exact key i j h fun k hk => hη k (hk.trans (le_max_left i j))

/-! ### Section 6.7.3: eigenvalue estimates, (6.99)–(6.103) -/

/-- For a symmetric positive definite $A \in \mathbb{R}^{n \times n}$: if the residual $r_k$ of
Algorithm 6.18 is nonzero, then $r_j \ne 0$ for every $j \le k$. -/
theorem cgR_ne_zero_of_le (hA : A.PosDef) {k j : ℕ} (hr : cgR A b x₀ k ≠ 0) (hj : j ≤ k) :
    cgR A b x₀ j ≠ 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  intro h0
  refine hr ?_
  rw [cgR_eq_CG A b x₀ hs] at h0 ⊢
  rw [CG.iterate_eq_of_residual_eq_zero' (op A) b x₀ h0 k hj]
  exact h0

/-- The sign $(-1)^k$ of (6.99) squares to $1$. -/
private theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

/-- Equation (6.99): let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let
$r_k \ne 0$. Then the Lanczos vector computed from $v_1 = r_0/\|r_0\|_2$ is
$v_{k+1} = (-1)^k r_k / \|r_k\|_2$. -/
theorem lanczosV_eq_smul_cgR (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    lanczosV A (v₁ A b x₀) k =
      ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹) • cgR A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := by simpa using cgR_ne_zero_of_le hA hr (Nat.zero_le k)
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  have h := CG.arnoldi_vec_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) k
    (by rwa [cgR_eq_CG A b x₀ hs] at hr)
  rw [lanczosV_v₁ hA.isSymm hb, cgR_eq_CG A b x₀ hs]
  simpa using h

/-- **Equation (6.99)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and let the residual $r_k$ of Algorithm 6.18 be nonzero. Then $r_k$ is a
nonzero multiple of the Lanczos vector $v_{k+1}$ computed from $v_1 = r_0/\|r_0\|_2$: there is
$\sigma \ne 0$ with
$$r_k = \sigma v_{k+1}.$$

The explicit form $v_{k+1} = (-1)^k r_k / \|r_k\|_2$ is
`SaadSparse.Chapter06.lanczosV_eq_smul_cgR`. -/
theorem equation_6_99 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ cgR A b x₀ k = σ • lanczosV A (v₁ A b x₀) k := by
  have hn : ‖cgR A b x₀ k‖ ≠ 0 := norm_ne_zero_iff.2 hr
  refine ⟨(-1 : ℝ) ^ k * ‖cgR A b x₀ k‖,
    mul_ne_zero (pow_ne_zero k (by norm_num)) hn, ?_⟩
  have hone : ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖) * ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹) = 1 :=
    calc ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖) * ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹)
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (‖cgR A b x₀ k‖ * ‖cgR A b x₀ k‖⁻¹) := by ring
      _ = 1 := by rw [neg_one_pow_mul_self, mul_inv_cancel₀ hn, mul_one]
  rw [lanczosV_eq_smul_cgR hA hr, smul_smul, hone, one_smul]

/-- **Equation (6.100)** of [saad2003iterative]. For every $A \in \mathbb{R}^{n \times n}$,
$b, x_0 \in \mathbb{R}^n$ and $j \ge 1$, the residuals and the directions of Algorithm 6.18
satisfy
$$r_j = p_j - \beta_{j-1} p_{j-1}.$$

This is line 7 of the algorithm solved for $r_j$, so it needs no hypothesis on $A$. In Lean the
index is $j + 1$ with $j \ge 0$. -/
theorem equation_6_100 (j : ℕ) :
    cgR A b x₀ (j + 1) = cgP A b x₀ (j + 1) - cgBeta A b x₀ j • cgP A b x₀ j := by
  rw [cgP_succ]
  abel

/-- Section 6.7.1: for a symmetric positive definite $A \in \mathbb{R}^{n \times n}$,
$\beta_j = -(r_{j+1}, A p_j)/(p_j, A p_j)$, the form that the derivation in the book produces. -/
theorem cgBeta_eq' (hA : A.PosDef) (j : ℕ) : cgBeta A b x₀ j =
    -(inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1)) /
      inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j)) := by
  by_cases hr : cgR A b x₀ j = 0
  · rw [cgBeta_eq, hr, cgP_eq_zero_of_cgR_eq_zero hA hr]
    simp
  · have hX : inner ℝ (cgP A b x₀ j) (op A (cgP A b x₀ j)) ≠ 0 :=
      inner_cgP_apply_cgP_ne_zero hA hr
    have hX' : inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j) ≠ 0 := by
      rw [real_inner_comm]
      exact hX
    have hR : (inner ℝ (cgR A b x₀ j) (cgR A b x₀ j) : ℝ) ≠ 0 := fun h =>
      hr (inner_self_eq_zero.1 h)
    have h1 : cgAlpha A b x₀ j * inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j)
        = inner ℝ (cgR A b x₀ j) (cgR A b x₀ j) := by
      rw [cgAlpha_eq, real_inner_comm (op A (cgP A b x₀ j)), div_mul_cancel₀ _ hX']
    have h2 : cgAlpha A b x₀ j * inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1))
        = -inner ℝ (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) := by
      rw [← real_inner_smul_left, cgAlpha_smul_apply_cgP, inner_sub_left,
        inner_cgR_eq_zero hA (show j ≠ j + 1 by omega), zero_sub]
    rw [cgBeta_eq]
    field_simp
    linear_combination inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j) * h2 -
      inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1)) * h1

/-- For a real symmetric $A$ and $r_0 \ne 0$, the coefficient $\alpha_{j+1}$ computed from
$v_1 = r_0/\|r_0\|_2$ is the backbone Lanczos coefficient of $r_0$. -/
private theorem lanczosAlpha_v₁ (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (j : ℕ) :
    lanczosAlpha A (v₁ A b x₀) j = Lanczos.alpha (op A) (b - op A x₀) j := by
  have h := lanczosAlpha_eq_arnoldiCoeff A (v₁ A b x₀)
    (isSymmetric_op_of_isSymm hA) (norm_v₁ A b x₀ hb) j
  have h2 : arnoldiCoeff A (v₁ A b x₀) j j = Arnoldi.coeff (op A) (b - op A x₀) j j := by
    rw [v₁_def]
    exact arnoldiCoeff_normalize A hb j j
  have h3 := Lanczos.coe_alpha (b - op A x₀) (isSymmetric_op_of_isSymm hA) j
  rw [h2, ← h3] at h
  simpa using h

/-- **Equation (6.102)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and $r_0 \ne 0$. Then the first diagonal entry of $T_m$, computed from
$v_1 = r_0/\|r_0\|_2$, is
$$\delta_1 = \frac{1}{\alpha_0},$$
where $\alpha_0$ is the first step length of Algorithm 6.18.

The proof specializes `CG.lanczos_alpha_zero_eq`, and the entry is
`lanczosAlpha A (v₁ A b x₀) 0`, the coefficient $\alpha_1$ of Algorithm 6.15. -/
theorem equation_6_102 (hA : A.PosDef) (hr : cgR A b x₀ 0 ≠ 0) :
    lanczosAlpha A (v₁ A b x₀) 0 = 1 / cgAlpha A b x₀ 0 := by
  have hs := isSymmetricCoercive_op_of_posDef hA
  have hr' : (CG.iterate (op A) b x₀ 0).r ≠ 0 := by rwa [cgR_eq_CG A b x₀ hs.isSymmetric] at hr
  rw [lanczosAlpha_v₁ hA.isSymm hr, cgAlpha_eq_CG A b x₀ hs.isSymmetric, one_div]
  simpa using CG.lanczos_alpha_zero_eq b x₀ hs hr'

/-- **Equation (6.101)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $j \ge 1$, and let the residual $r_j$ of Algorithm 6.18 be nonzero. Then
the diagonal entry $\delta_{j+1}$ of $T_m$, computed from $v_1 = r_0/\|r_0\|_2$, is
$$\delta_{j+1} = \frac{1}{\alpha_j} + \frac{\beta_{j-1}}{\alpha_{j-1}},$$
where $\alpha_j$ and $\beta_j$ are the coefficients of Algorithm 6.18.

In Lean $j = k + 1$ with $k \ge 0$. The proof specializes `CG.lanczos_alpha_succ_eq`, and the
entry is `lanczosAlpha A (v₁ A b x₀) (k + 1)`. -/
theorem equation_6_101 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    lanczosAlpha A (v₁ A b x₀) (k + 1) =
      1 / cgAlpha A b x₀ (k + 1) + cgBeta A b x₀ k / cgAlpha A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := cgR_ne_zero_of_le hA hr (Nat.zero_le _)
  have hs := isSymmetricCoercive_op_of_posDef hA
  have hr' : (CG.iterate (op A) b x₀ (k + 1)).r ≠ 0 := by
    rwa [cgR_eq_CG A b x₀ hs.isSymmetric] at hr
  rw [lanczosAlpha_v₁ hA.isSymm hb, cgAlpha_eq_CG A b x₀ hs.isSymmetric,
    cgAlpha_eq_CG A b x₀ hs.isSymmetric, cgBeta_eq_CG A b x₀ hs.isSymmetric, one_div]
  simpa using CG.lanczos_alpha_succ_eq b x₀ hs hr'

/-- **Equation (6.103)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $j \ge 1$, and let the residual $r_j$ of Algorithm 6.18 be nonzero. Then
the off-diagonal entry $\eta_{j+1}$ of $T_m$, computed from $v_1 = r_0/\|r_0\|_2$, is
$$\eta_{j+1} = \frac{\sqrt{\beta_{j-1}}}{\alpha_{j-1}},$$
where $\alpha_j$ and $\beta_j$ are the coefficients of Algorithm 6.18.

In Lean $j = k + 1$ with $k \ge 0$. The proof specializes `CG.lanczos_beta_eq`, and the entry is
`lanczosBeta A (v₁ A b x₀) (k + 1)`, the coefficient $\beta_{j+1}$ of Algorithm 6.15. The proof
uses $\sqrt{\beta_k} = \|r_{k+1}\| / \|r_k\|$. -/
theorem equation_6_103 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    lanczosBeta A (v₁ A b x₀) (k + 1) =
      Real.sqrt (cgBeta A b x₀ k) / cgAlpha A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := cgR_ne_zero_of_le hA hr (Nat.zero_le _)
  have hs := isSymmetricCoercive_op_of_posDef hA
  have hr' : (CG.iterate (op A) b x₀ (k + 1)).r ≠ 0 := by
    rwa [cgR_eq_CG A b x₀ hs.isSymmetric] at hr
  have hbeta : cgBeta A b x₀ k = ‖cgR A b x₀ (k + 1)‖ ^ 2 / ‖cgR A b x₀ k‖ ^ 2 := by
    rw [cgBeta_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hsqrt : Real.sqrt (cgBeta A b x₀ k) = ‖cgR A b x₀ (k + 1)‖ / ‖cgR A b x₀ k‖ := by
    rw [hbeta, ← div_pow, Real.sqrt_sq (by positivity)]
  have hL : lanczosBeta A (v₁ A b x₀) (k + 1) = Lanczos.beta (op A) (b - op A x₀) k := by
    rw [lanczosBeta_succ_v₁ hA.isSymm hb, ← Lanczos.coe_beta]
    rfl
  rw [hL, CG.lanczos_beta_eq b x₀ hs hr', hsqrt, cgR_eq_CG A b x₀ hs.isSymmetric,
    cgR_eq_CG A b x₀ hs.isSymmetric, cgAlpha_eq_CG A b x₀ hs.isSymmetric, RCLike.re_to_real,
    div_div]

/-- Section 6.7.1, last sentence: let $A \in \mathbb{R}^{n \times n}$ be symmetric positive
definite, $r_0 \ne 0$ and $r_j \ne 0$. If $\eta_1, \dots, \eta_{j+1}$ are nonzero, then the
search direction $p_j$ of Algorithm 6.18 is a nonzero multiple of the auxiliary vector $p_{j+1}$
of Algorithm 6.17. -/
theorem cgP_smul_dlP (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {j : ℕ} (hr : cgR A b x₀ j ≠ 0)
    (hη : ∀ i < j + 1, dlEta A (v₁ A b x₀) i ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ cgP A b x₀ j = c • dlP A (v₁ A b x₀) j := by
  have hα := cgAlpha_ne_zero hA hr
  have hxj := cgX_eq_dLanczosX hA hb j fun i hi => hη i (by omega)
  have hxj1 := cgX_eq_dLanczosX hA hb (j + 1) hη
  have hres := residual_dLanczosX hA.isSymm hb j fun i hi => hη i (by omega)
  have hζ : dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ j ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hres
    exact hr (by rw [cgR_eq_residual A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
      hxj, hres])
  have hstep : cgAlpha A b x₀ j • cgP A b x₀ j =
      dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ j • dlP A (v₁ A b x₀) j := by
    have h1 : cgX A b x₀ (j + 1) = cgX A b x₀ j + cgAlpha A b x₀ j • cgP A b x₀ j
        := cgX_succ A b x₀ j
    have h2 := dLanczosX_succ (A := A) (b := b) (x₀ := x₀) j
    rw [hxj1, hxj] at h1
    rw [h2] at h1
    exact (add_right_injective (dLanczosX A b x₀ j) h1.symm)
  refine ⟨dlZeta A (v₁ A b x₀) ‖b - op A x₀‖ j / cgAlpha A b x₀ j,
    div_ne_zero hζ hα, ?_⟩
  rw [div_eq_inv_mul, ← smul_smul, ← hstep, smul_smul, inv_mul_cancel₀ hα, one_smul]

end Real

/-!
### Section 6.7.1: D-Lanczos is DIOM(2)

The book's remark that Algorithm 6.17 "is DIOM(2)", and hence that the conjugate gradient algorithm
is a variation of DIOM(2), rests on a fact about a symmetric matrix: the incomplete
orthogonalization of Algorithm 6.6 with $k = 2$ computes the same vectors as Algorithm 6.1. The only
coefficients that it drops are the $h_{ij}$ with $i + 1 < j$, and those vanish by symmetry.
-/

section IncompleteTwo

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-- Before the band starts, the truncated inner loop of Algorithm 6.6 does not change the vector. -/
private theorem iopW_of_le (u : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) :
    ∀ {N : ℕ}, N ≤ lo → iopW u lo w₀ N = w₀ := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    rw [iopW_succ, ih (by omega), iopCoeffOf]
    split_ifs with h1
    · omega
    · rw [zero_smul, sub_zero]

variable (M : Matrix (Fin n) (Fin n) 𝕜) (w₁ : EuclideanSpace 𝕜 (Fin n))

/-- Let $M \in \mathbb{K}^{n \times n}$ be Hermitian and $\|w_1\| = 1$. Then the Arnoldi
coefficients of $M$ and $w_1$ are tridiagonal: $h_{ij} = 0$ for $i + 1 < j$. -/
theorem arnoldiCoeff_eq_zero_of_isSymmetric (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1)
    {i j : ℕ} (h : i + 1 < j) : arnoldiCoeff M w₁ i j = 0 := by
  rw [arnoldiCoeff_eq M w₁ hw]
  exact Arnoldi.coeff_eq_zero_of_isSymmetric hM w₁ h

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the inner loop of Algorithm 6.6 with $k = 2$, run on the
Arnoldi vectors, gives the Arnoldi coefficients. -/
private theorem iopCoeffOf_two (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) {i : ℕ}
    (hi : i < j + 1) :
    iopCoeffOf (arnoldiCGS M w₁) (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) i
      = arnoldiCoeff M w₁ i j := by
  match j with
  | 0 =>
    obtain rfl : i = 0 := by omega
    rw [iopCoeffOf]
    split_ifs with h1
    · rw [iopW_of_le _ _ _ (Nat.zero_le _)]
      rfl
    · omega
  | (k + 1) =>
    have hlo : k + 1 + 1 - 2 = k := by omega
    rw [hlo, iopCoeffOf]
    split_ifs with h1
    · rcases eq_or_lt_of_le h1 with h2 | h2
      · obtain rfl : i = k := h2.symm
        rw [iopW_of_le _ _ _ le_rfl]
        rfl
      · obtain rfl : i = k + 1 := by omega
        rw [iopW_succ, iopCoeffOf]
        split_ifs with h3
        · rw [iopW_of_le _ _ _ le_rfl, inner_sub_right, inner_smul_right,
            inner_arnoldiCGS_eq_zero M w₁ hw (by omega : k + 1 ≠ k), mul_zero, sub_zero]
          rfl
        · omega
    · exact (arnoldiCoeff_eq_zero_of_isSymmetric M w₁ hM hw (by omega)).symm

/-- Algorithm 6.6 with $k = 2$ is Algorithm 6.1 for a Hermitian matrix: for a Hermitian $M$ and
$\|w_1\| = 1$, the two algorithms compute the same vectors. -/
theorem iop_two_eq_arnoldiCGS (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) :
    iop M w₁ 2 j = arnoldiCGS M w₁ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => rw [iop_zero, arnoldiCGS_zero]
    | (j + 1) =>
      have hfam : ∀ i < j + 1, iop M w₁ 2 i = arnoldiCGS M w₁ i := fun i hi => ih i (by omega)
      have hsum : ∑ i ∈ Finset.range (j + 1),
          iopCoeffOf (arnoldiCGS M w₁) (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) i •
            arnoldiCGS M w₁ i
          = ∑ i ∈ Finset.range (j + 1), arnoldiCoeff M w₁ i j • arnoldiCGS M w₁ i :=
        Finset.sum_congr rfl fun i hi => by
          rw [iopCoeffOf_two M w₁ hM hw j (Finset.mem_range.1 hi)]
      have hW : iopVecW M w₁ 2 j = arnoldiW M w₁ j := by
        rw [iopVecW, hfam j (by omega),
          iopW_congr (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) hfam, iopW_eq_sub_sum, arnoldiW,
          hsum]
      rw [iop_succ, hW, arnoldiCGS_succ]

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the sequence of vectors of Algorithm 6.6 with $k = 2$ is
the sequence of Algorithm 6.1. -/
theorem iop_two_eq (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) :
    iop M w₁ 2 = arnoldiCGS M w₁ :=
  funext (iop_two_eq_arnoldiCGS M w₁ hM hw)

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the vectors $w_j$ of Algorithm 6.6 with $k = 2$ are those
of Algorithm 6.1. -/
theorem iopVecW_two_eq_arnoldiW (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) :
    iopVecW M w₁ 2 j = arnoldiW M w₁ j := by
  rw [iopVecW, iop_two_eq M w₁ hM hw, iopW_eq_sub_sum, arnoldiW]
  exact congrArg _ (Finset.sum_congr rfl fun i hi => by
    rw [iopCoeffOf_two M w₁ hM hw j (Finset.mem_range.1 hi)])

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the coefficients $h_{ij}$ of Algorithm 6.6 with $k = 2$
are the Arnoldi coefficients, for all $i$ and $j$. -/
theorem iopCoeff_two_eq_arnoldiCoeff (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (i j : ℕ) :
    iopCoeff M w₁ 2 i j = arnoldiCoeff M w₁ i j := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · rw [iop_two_eq M w₁ hM hw]
    exact iopCoeffOf_two M w₁ hM hw j (by omega)
  · rw [h2, iopVecW_two_eq_arnoldiW M w₁ hM hw, arnoldiCoeff_succ_self M w₁ hw]
  · exact (arnoldiCoeff_eq_zero_of_lt M w₁ hw (by omega)).symm

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the matrix $V_m$ of Algorithm 6.6 with $k = 2$ is the
Arnoldi matrix $V_m$. -/
theorem VI_two_eq_V (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (m : ℕ) :
    VI M w₁ 2 m = V M w₁ m := by
  rw [VI, V, iop_two_eq M w₁ hM hw]

/-- For a Hermitian $M$ and $\|w_1\| = 1$, the matrix $H_m$ of Algorithm 6.6 with $k = 2$ is the
Arnoldi matrix $H_m$. -/
theorem HI_two_eq_H (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (m : ℕ) :
    HI M w₁ 2 m = H M w₁ m := by
  ext i j
  rw [HI_apply, H_apply, iopCoeff_two_eq_arnoldiCoeff M w₁ hM hw]

variable (c x₀ : EuclideanSpace 𝕜 (Fin n))

/-- IOM(2) is FOM for a Hermitian matrix: if $M$ is Hermitian and $r_0 = c - M x_0 \ne 0$, then for
every $m$ the iterate of IOM(2) (Algorithm 6.7 with $k = 2$) after $m$ steps is the iterate of
FOM after $m$ steps. -/
theorem iomFixed_two_eq_fomFixed (hM : (op M).IsSymmetric) (hr : r₀ M c x₀ ≠ 0) (m : ℕ) :
    iomFixed M c x₀ 2 m = fomFixed M c x₀ m := by
  have hw : ‖v₁ M c x₀‖ = 1 := norm_v₁ M c x₀ hr
  rw [iomFixed, fomFixed, VI_two_eq_V M _ hM hw, iomY, fomY, HI_two_eq_H M _ hM hw]

/-- DIOM(2) is FOM for a Hermitian matrix wherever Algorithm 6.8 does not divide by $0$: if $M$ is
Hermitian, $r_0 = c - M x_0 \ne 0$, and the pivots $u_{ll}$, $l < m$, of the factorization in
Algorithm 6.8 with $k = 2$ are nonzero, then the iterate of DIOM(2) after $m$ steps is the
iterate of FOM after $m$ steps. -/
theorem diom_two_eq_fomFixed (hM : (op M).IsSymmetric) (hr : r₀ M c x₀ ≠ 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff M (v₁ M c x₀) 2) l l ≠ 0) :
    diom M c x₀ 2 m = fomFixed M c x₀ m :=
  (diom_eq_iomFixed M c x₀ 2 hpiv).trans (iomFixed_two_eq_fomFixed M c x₀ hM hr m)

end IncompleteTwo

section RealTwo

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **Section 6.7.1** of [saad2003iterative], D-Lanczos is DIOM(2). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $r_0 \ne 0$, and let $m \le \mu$, the grade of
$r_0$. Assume that $\eta_1, \dots, \eta_m$ are nonzero, and that the pivots $u_{ll}$, $l < m$,
of the factorization in Algorithm 6.8 with $k = 2$ are nonzero. Then the iterate $x_m$ of
Algorithm 6.17 is the iterate of DIOM(2), Algorithm 6.8 with $k = 2$. This is the remark of the
book that the conjugate gradient algorithm is a variation of DIOM(2).

Both iterates are the Galerkin iterate on $\mathcal{K}_m(A, r_0)$. For D-Lanczos this is
`SaadSparse.Chapter06.dLanczosX_isGalerkinIterate`. For DIOM(2) it holds because for a symmetric
$A$ the truncated orthogonalization of Algorithm 6.6 with $k = 2$ is the Arnoldi process, so
DIOM(2) is FOM. The pivots are `dioU (iopCoeff A (v₁ A b x₀) 2) l l`. -/
theorem dLanczos_eq_diom2 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀))
    (hη : ∀ i < m, dlEta A (v₁ A b x₀) i ≠ 0)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) 2) l l ≠ 0) :
    dLanczosX A b x₀ m = diom A b x₀ 2 m := by
  have hsym := isSymmetric_op_of_isSymm hA
  have hw : ‖v₁ A b x₀‖ = 1 := norm_v₁ A b x₀ hb
  have hH : FOMDefined A b x₀ m := by
    rw [FOMDefined, ← HI_two_eq_H A (v₁ A b x₀) hsym hw]
    exact isUnit_HI_of_pivots A (v₁ A b x₀) 2 hpiv
  rw [diom_two_eq_fomFixed A b x₀ hsym hb hpiv]
  exact eq_fomFixed_of_isGalerkinIterate A b x₀ hH (by rwa [grade_v₁, ← grade_eq])
    (dLanczosX_isGalerkinIterate hA hb m hη)

end RealTwo

end SaadSparse.Chapter06
