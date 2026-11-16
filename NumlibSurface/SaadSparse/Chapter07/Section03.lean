/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter07.Section02

/-!
# Saad, Section 7.3: BCG and QMR

This module formalizes Section 7.3 of [saad2003iterative], which derives two solvers for a
nonsymmetric system $Ax = b$ from the Lanczos biorthogonalization of Section 7.1. Write
$r_0 = b - Ax_0$, $\beta = \|r_0\|_2$ and $v_1 = r_0/\beta$. The biconjugate gradient method (BCG,
Algorithm 7.3) runs the recurrence on $(x_j, r_j, r^*_j, p_j, p^*_j)$ with
$\alpha_j = (r_j, r^*_j)/(Ap_j, p^*_j)$ and $\beta_j = (r_{j+1}, r^*_{j+1})/(r_j, r^*_j)$. Its
residuals are biorthogonal and its directions are $A$-biconjugate (Proposition 7.2), its iterate is
the Petrov–Galerkin approximation onto $\mathcal{K}_m(A, r_0)$ orthogonally to
$\mathcal{K}_m(A^H, r^*_0)$, and it computes the iterate $x_m = x_0 + V_m T_m^{-1}(\beta e_1)$ of
Algorithm 7.2, equations (7.10)–(7.12). The proofs specialize the backbone BCG of
`Numlib.Krylov.BiLanczos`.

The quasi-minimal residual method (QMR, Algorithm 7.4) chooses $x^Q_m = x_0 + V_m y$ so that $y$
minimizes the quasi-residual norm $\|\beta e_1 - \bar T_m y\|_2$ of (7.17). Its quasi-residual norm
is $\rho^Q_m = |\gamma_{m+1}| = |s_1 \cdots s_m| \, \|r_0\|_2$, where $c_i$ and $s_i$ are the Givens
rotations that reduce $\bar T_m$ to triangular form. With $\rho_m$ the residual norm of the
Algorithm 7.2 iterate $x_m$, the module proves $\rho^Q_m = |c_m| \rho_m$, the bound of Proposition
7.3, the comparison with GMRES of Theorem 7.4, the harmonic relations (7.23)–(7.24), Proposition
7.5, and the smoothing relations (7.26)–(7.30). The last of these says that QMR is the quasi-minimal
residual smoothing (Algorithm 7.5) of the Algorithm 7.2 iterates. These proofs specialize
`Numlib.Krylov.QuasiMinRes`.

## Main definitions

* Algorithm 7.3, `SaadSparse.Chapter07.bcg`: the biconjugate gradient method (BCG), with the
  coefficients `SaadSparse.Chapter07.bcgAlpha` and `SaadSparse.Chapter07.bcgBeta`.
* `SaadSparse.Chapter07.BCGNoBreakdown`: neither denominator of Algorithm 7.3 vanishes before step
  $m$.
* Algorithm 7.4, `SaadSparse.Chapter07.qmr`: the quasi-minimal residual method (QMR), which is
  Algorithm 6.12 (QGMRES) on the two-sided Lanczos basis.
* Algorithm 7.5, `SaadSparse.Chapter07.qmrSmoothing`: the quasi-minimal residual smoothing of an
  arbitrary sequence of iterates.

## Main results

* `SaadSparse.Chapter07.bcg_eq`: Algorithm 7.3 is the backbone BCG iteration for $A$ and $A^H$.
* Proposition 7.2, `SaadSparse.Chapter07.proposition_7_2`: $(r_i, r^*_j) = 0$ and
  $(Ap_i, p^*_j) = 0$ for $i \neq j$.
* Section 7.3.1, `SaadSparse.Chapter07.bcg_isPetrovGalerkin`: the BCG iterate is a Petrov–Galerkin
  approximation onto $\mathcal{K}_m(A, r_0)$ orthogonally to $\mathcal{K}_m(A^H, r^*_0)$.
* Equations (7.10)–(7.12), `SaadSparse.Chapter07.bcg_eq_lanczosSolve`: BCG computes the iterate of
  Algorithm 7.2.
* Section 7.3.2, `SaadSparse.Chapter07.qmr_isQuasiMinResidualIterate`: the QMR iterate minimizes the
  quasi-residual norm.
* Equation (7.16), `SaadSparse.Chapter07.equation_7_16`: $b - A(x_0 + V_m y) = V_{m+1}(\beta e_1 -
  \bar T_m y)$.
* Equation (7.18), `SaadSparse.Chapter07.equation_7_18`: $\rho^Q_m = |s_1 \cdots s_m| \, \|r_0\|_2$.
* Equation (7.19), `SaadSparse.Chapter07.equation_7_19`: $\gamma_{m+1} v_{m+1} = c_m r_m$.
* Equation (7.20), `SaadSparse.Chapter07.equation_7_20`: $\rho^Q_m = |c_m| \rho_m$ for unit Lanczos
  vectors.
* Proposition 7.3, `SaadSparse.Chapter07.proposition_7_3` and
  `SaadSparse.Chapter07.proposition_7_3_sqrt`: $\|b - Ax^Q_m\|_2 \le \|V_{m+1}\|_2 \, |s_1 \cdots
  s_m| \, \|r_0\|_2$, and $\|V_{m+1}\|_2 \le \sqrt{m+1}$ for unit Lanczos vectors.
* Theorem 7.4, `SaadSparse.Chapter07.theorem_7_4`: $\|r^Q_m\|_2 \le \kappa_2(V_{m+1}) \|r^G_m\|_2$.
* Equation (7.23), `SaadSparse.Chapter07.equation_7_23`: $1/(\rho^Q_{m+1})^2 = 1/(\rho^Q_m)^2 +
  1/\rho_{m+1}^2$.
* Equation (7.24), `SaadSparse.Chapter07.equation_7_24`:
  $1/(\rho^Q_m)^2 = \sum_{i=0}^{m} 1/\rho_i^2$.
* Proposition 7.5, `SaadSparse.Chapter07.proposition_7_5`: $\rho^Q_m \le \min_{i \le m} \rho_i \le
  \sqrt{m+1} \, \rho^Q_m$.
* Equations (7.26)–(7.27), `SaadSparse.Chapter07.equation_7_26`: $b - Ax^Q_m = \gamma_{m+1} z_{m+1}$
  and the recurrence for $z_{m+1}$.
* Equation (7.28), `SaadSparse.Chapter07.equation_7_28`: $r^Q_{m+1} = |s_{m+1}|^2 r^Q_m + \bar
  c_{m+1} \gamma_{m+2} v_{m+2}$.
* Equation (7.29), `SaadSparse.Chapter07.equation_7_29`: $r^Q_{m+1} = |s_{m+1}|^2 r^Q_m +
  |c_{m+1}|^2 r_{m+1}$.
* Equation (7.30), `SaadSparse.Chapter07.equation_7_30`: $x^Q_{m+1} = |s_{m+1}|^2 x^Q_m +
  |c_{m+1}|^2 x_{m+1}$.
* Algorithm 7.5, `SaadSparse.Chapter07.qmrSmoothing_eq_qmr`: Algorithm 7.5 applied to the Algorithm
  7.2 iterates reproduces QMR.
* Exercise P-7.7, `SaadSparse.Chapter07.problem_7_7`, `SaadSparse.Chapter07.problem_7_7_direction`
  and `SaadSparse.Chapter07.problem_7_7_start`: the three-term recurrences of the BCG residuals and
  of the BCG directions, and their first terms.

## Proof outline

The book derives (7.10)–(7.12) from the factorization $T_m = L_m U_m$ and the direction matrices
$P_m = V_m U_m^{-1}$ and $P^*_m = W_m L_m^{-H}$. Here both the BCG iterate and the Algorithm 7.2
iterate are Petrov–Galerkin approximations onto $\mathcal{K}_m(A, r_0)$ orthogonally to
$\mathcal{K}_m(A^H, r^*_0)$, and a nonsingular $T_m$ makes such an approximation unique. For QMR,
`SaadSparse.Chapter07.qmr_isQuasiMinResidualIterate` identifies the iterate with the backbone
quasi-minimal residual specification, and the results from (7.16) on are theorems of
`Numlib.Krylov.QuasiMinRes` read through it. Proposition 7.3 is
`Krylov.IsQuasiMinResidualIterate.norm_residual_le`, Theorem 7.4 is
`Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul`, and (7.23), (7.24) and Proposition 7.5 are
`Krylov.inv_sq_norm_gamma`, `Krylov.inv_sq_norm_gamma_eq_sum` and
`Krylov.exists_norm_gamma_div_givensC_le`.

## Conventions

* The scalar field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`𝕜` with `[RCLike 𝕜]`). Algorithm
  7.5 and its relation to QMR are stated over $\mathbb{R}$.
* Indices are $0$-based as in `SaadSparse.Chapter07.bilanczosV`. The BCG iterates are $0$-based
  in the book already. The other quantities correspond as follows.
  * The book's $v_{j+1}$ is `qmrV A b x₀ w₁ j`.
  * The book's $\gamma_{m+1}$ is `SaadSparse.Chapter06.γ h β m`.
  * The book's $c_{m+1}$ is `SaadSparse.Chapter06.c h m`.
  * The book's $s_{m+1}$ is `SaadSparse.Chapter06.s h m`.
  * The quasi-residual norm $\rho^Q_m = |\gamma_{m+1}|$ is
    `SaadSparse.Chapter06.quasiResidualNorm h β m`.
* "Algorithm 7.1 has no serious breakdown" is `SaadSparse.Chapter07.NoSeriousBreakdown`: whenever
  $(\hat v_{j+1}, \hat w_{j+1}) = 0$, also $\hat v_{j+1} = 0$.
* From (7.18) on, the book normalizes the Lanczos vectors to $\|v_j\|_2 = 1$. This is a different
  scaling from Algorithm 7.1, admissible by (7.1). It is the hypothesis $\|v_j\|_2 = 1$ for all $j$
  of `SaadSparse.Chapter07.equation_7_20` and the results after it. By
  `SaadSparse.Chapter07.equation_7_1_norm`, the choice $\delta_{j+1} = \|\hat v_{j+1}\|_2$ satisfies
  the constraint (7.1) and gives a unit primal vector without changing $(v_j, w_j) = 1$, so the
  hypothesis is a scaling of Algorithm 7.1 and not a new assumption.

## Implementation notes

* QMR is Algorithm 6.12 run on the two-sided Lanczos basis: `SaadSparse.Chapter07.qmr` is
  `SaadSparse.Chapter06.qgmres` at the basis `SaadSparse.Chapter07.qmrV` and the coefficients
  `SaadSparse.Chapter07.qmrCoeff`. The quantities $c_i$, $s_i$, $\gamma_i$, $z_i$ and $\rho^Q_m$ are
  those of `NumlibSurface.SaadSparse.Chapter06.Section05`.
* The condition number $\kappa_2(V_{m+1})$ of Theorem 7.4 enters as the ratio $C/c$ of a two-sided
  bound $c\|y\|_2 \le \|V_{m+1}y\|_2 \le C\|y\|_2$. Such a $c > 0$ exists because $V_{m+1}$ has full
  rank (`SaadSparse.Chapter07.problem_7_2`). For this reason the full-rank hypothesis that the book
  assumes in Theorem 6.11 is not needed here.
* Only the residual recurrence of exercise P-7.7 divides by $\alpha_j$, so only it needs a
  no-breakdown hypothesis.
* The coefficients `SaadSparse.Chapter07.bcgAlpha` and `SaadSparse.Chapter07.bcgBeta` are used again
  by the transpose-free variants of Section 7.4.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### §7.3.1: Algorithm 7.3, the biconjugate gradient algorithm -/

section BCG

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- One pass through lines 4–10 of Algorithm 7.3 (BCG). From the state
$(x_j, r_j, r^*_j, p_j, p^*_j)$ it computes $\alpha_j = (r_j, r^*_j)/(Ap_j, p^*_j)$,
$x_{j+1} = x_j + \alpha_j p_j$, $r_{j+1} = r_j - \alpha_j Ap_j$,
$r^*_{j+1} = r^*_j - \bar\alpha_j A^H p^*_j$, $\beta_j = (r_{j+1}, r^*_{j+1})/(r_j, r^*_j)$,
$p_{j+1} = r_{j+1} + \beta_j p_j$ and $p^*_{j+1} = r^*_{j+1} + \bar\beta_j p^*_j$. A division by
zero gives $0$. The state is the backbone record `BCG.State`. -/
noncomputable def bcgStep (s : BCG.State (EuclideanSpace 𝕜 (Fin n))) :
    BCG.State (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 s.rs s.r / inner 𝕜 s.ps (op A s.p)
  let r : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A s.p
  let rs : EuclideanSpace 𝕜 (Fin n) := s.rs - starRingEnd 𝕜 α • op Aᴴ s.ps
  let β : 𝕜 := inner 𝕜 rs r / inner 𝕜 s.rs s.r
  { x := s.x + α • s.p
    r := r
    rs := rs
    p := r + β • s.p
    ps := rs + starRingEnd 𝕜 β • s.ps }

/-- **Algorithm 7.3** of [saad2003iterative] (BCG). Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. The state of BCG after $k$ steps is the result of $k$
applications of `SaadSparse.Chapter07.bcgStep` to the initial state
$(x_0, r_0, r^*_0, p_0, p^*_0)$ with $r_0 = p_0 = b - Ax_0$ and $p^*_0 = r^*_0$.

The book requires $(r_0, r^*_0) \neq 0$. The definition accepts any $r^*_0$, and the condition
is part of the hypothesis `SaadSparse.Chapter07.BCGNoBreakdown` of the theorems below. -/
noncomputable def bcg (k : ℕ) : BCG.State (EuclideanSpace 𝕜 (Fin n)) :=
  (bcgStep A)^[k] { x := x₀, r := b - op A x₀, rs := rs₀, p := b - op A x₀, ps := rs₀ }

private theorem bcgStep_eq (s : BCG.State (EuclideanSpace 𝕜 (Fin n))) :
    bcgStep A s = BCG.step (op A) (op Aᴴ) s := rfl

/-- Algorithm 7.3 is the backbone BCG iteration: for every $k$, the state
`SaadSparse.Chapter07.bcg A b x₀ rs₀ k` equals `BCG.iterate (op A) (op Aᴴ) b x₀ rs₀ k`, the
backbone BCG iteration for the operator $x \mapsto Ax$ and its adjoint $x \mapsto A^H x$. -/
theorem bcg_eq (k : ℕ) : bcg A b x₀ rs₀ k = BCG.iterate (op A) (op Aᴴ) b x₀ rs₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bcg, Function.iterate_succ_apply', ← bcg, ih, bcgStep_eq, ← BCG.iterate_succ]

/-- Lines 1 and 2 of Algorithm 7.3: the initial state of BCG is $(x_0, r_0, r^*_0, r_0, r^*_0)$ with
$r_0 = b - Ax_0$. -/
@[simp] theorem bcg_zero :
    bcg A b x₀ rs₀ 0
      = { x := x₀, r := b - op A x₀, rs := rs₀, p := b - op A x₀, ps := rs₀ } := rfl

/-- Line 4 of Algorithm 7.3: the backbone step length `BCG.alpha` at step $k$ is
$\alpha_k = (r_k, r^*_k)/(Ap_k, p^*_k)$, computed from the state of BCG after $k$ steps. -/
theorem bcg_alpha_eq (k : ℕ) : BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ k =
    inner 𝕜 (bcg A b x₀ rs₀ k).rs (bcg A b x₀ rs₀ k).r /
      inner 𝕜 (bcg A b x₀ rs₀ k).ps (op A (bcg A b x₀ rs₀ k).p) := by
  rw [bcg_eq]; rfl

/-- Line 8 of Algorithm 7.3: the backbone coefficient `BCG.beta` at step $k$ is
$\beta_k = (r_{k+1}, r^*_{k+1})/(r_k, r^*_k)$, computed from the states of BCG after $k$ and
$k + 1$ steps. -/
theorem bcg_beta_eq (k : ℕ) : BCG.beta (op A) (op Aᴴ) b x₀ rs₀ k =
    inner 𝕜 (bcg A b x₀ rs₀ (k + 1)).rs (bcg A b x₀ rs₀ (k + 1)).r /
      inner 𝕜 (bcg A b x₀ rs₀ k).rs (bcg A b x₀ rs₀ k).r := by
  rw [bcg_eq, bcg_eq]; rfl

/-- The step length $\alpha_j$ of Algorithm 7.3: the backbone `BCG.alpha` for the operators $A$ and
$A^H$. -/
noncomputable abbrev bcgAlpha (j : ℕ) : 𝕜 := BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ j

/-- The direction coefficient $\beta_j$ of Algorithm 7.3: the backbone `BCG.beta` for the operators
$A$ and $A^H$. -/
noncomputable abbrev bcgBeta (j : ℕ) : 𝕜 := BCG.beta (op A) (op Aᴴ) b x₀ rs₀ j

/-- Line 4 of Algorithm 7.3: $\alpha_j = (r_j, r^*_j)/(Ap_j, p^*_j)$. -/
theorem bcgAlpha_eq (j : ℕ) : bcgAlpha A b x₀ rs₀ j =
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r /
      inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ j).p) :=
  bcg_alpha_eq A b x₀ rs₀ j

/-- Line 8 of Algorithm 7.3: $\beta_j = (r_{j+1}, r^*_{j+1})/(r_j, r^*_j)$. -/
theorem bcgBeta_eq (j : ℕ) : bcgBeta A b x₀ rs₀ j =
    inner 𝕜 (bcg A b x₀ rs₀ (j + 1)).rs (bcg A b x₀ rs₀ (j + 1)).r /
      inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r :=
  bcg_beta_eq A b x₀ rs₀ j

end BCG

section BCGBreakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- Algorithm 7.3 of [saad2003iterative] does not break down before step $m$: for every $k < m$,
$$(r_k, r^*_k) \neq 0 \quad\text{and}\quad (Ap_k, p^*_k) \neq 0.$$ These are the denominators of
$\beta_k$ (line 8) and of $\alpha_k$ (line 4).

The backbone hypothesis `BCG.NoBreakdown` also contains the adjoint relation
$(Ax, y) = (x, A^H y)$. This relation holds for every matrix, so this structure is the whole of
the book's hypothesis, and `SaadSparse.Chapter07.BCGNoBreakdown.toBCG` gives the backbone
hypothesis. -/
structure BCGNoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Prop where
  /-- For every $k < m$, $(r_k, r^*_k) \neq 0$: the numerator of $\alpha_k$ and the denominator of
  $\beta_k$ do not vanish. -/
  inner_residual_ne_zero : ∀ k < m, inner 𝕜 (bcg A b x₀ rs₀ k).rs (bcg A b x₀ rs₀ k).r ≠ 0
  /-- For every $k < m$, $(Ap_k, p^*_k) \neq 0$: the denominator of $\alpha_k$ does not vanish. -/
  inner_apply_direction_ne_zero : ∀ k < m,
    inner 𝕜 (bcg A b x₀ rs₀ k).ps (op A (bcg A b x₀ rs₀ k).p) ≠ 0

/-- If Algorithm 7.3 does not break down before step $m$, then it does not break down before step
$k$ for every $k \le m$. -/
theorem BCGNoBreakdown.mono {k : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) (hk : k ≤ m) :
    BCGNoBreakdown A b x₀ rs₀ k :=
  ⟨fun j hj => h.inner_residual_ne_zero j (hj.trans_le hk),
    fun j hj => h.inner_apply_direction_ne_zero j (hj.trans_le hk)⟩

/-- If Algorithm 7.3 does not break down before step $m$, then the backbone hypothesis
`BCG.NoBreakdown` holds for the operators $A$ and $A^H$ and the same $m$. -/
theorem BCGNoBreakdown.toBCG (h : BCGNoBreakdown A b x₀ rs₀ m) :
    BCG.NoBreakdown (op A) (op Aᴴ) b x₀ rs₀ m where
  adjoint := LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A)
  inner_residual_ne_zero k hk := by
    have := h.inner_residual_ne_zero k hk
    rwa [bcg_eq] at this
  inner_apply_direction_ne_zero k hk := by
    have := h.inner_apply_direction_ne_zero k hk
    rwa [bcg_eq] at this

/-- **Proposition 7.2** of [saad2003iterative], equations (7.13)–(7.14). Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm
7.3 does not break down before step $m$. Then for all $i, j \le m$ with $i \neq j$, $$(r_i,
r^*_j) = 0 \quad\text{and}\quad (Ap_i, p^*_j) = 0.$$ That is, the BCG residuals are biorthogonal
and the BCG directions are $A$-biconjugate.

The book asks for the same result in exercise P-7.10. -/
theorem proposition_7_2 (h : BCGNoBreakdown A b x₀ rs₀ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m)
    (hij : i ≠ j) :
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ i).r = 0 ∧
      inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ i).p) = 0 := by
  simp only [bcg_eq]
  exact ⟨BCG.inner_residual_dualResidual_eq_zero h.toBCG hi hj hij,
    BCG.inner_dualDirection_apply_direction_eq_zero h.toBCG hi hj hij⟩

/-- **Section 7.3.1** of [saad2003iterative], BCG as a projection process. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm
7.3 does not break down before step $m$. Then the BCG iterate $x_m$ is the Petrov–Galerkin
approximation onto $\mathcal{K}_m(A, r_0)$ orthogonally to $\mathcal{K}_m(A^H, r^*_0)$: $$x_m
\in x_0 + \mathcal{K}_m(A, r_0) \quad\text{and}\quad b - Ax_m \perp \mathcal{K}_m(A^H, r^*_0).$$
This is the projection process with which the section opens.

The Krylov subspaces are `SaadSparse.Chapter06.krylov`, and the conclusion is `IsPetrovGalerkin`
for the operator `op A`. -/
theorem bcg_isPetrovGalerkin (h : BCGNoBreakdown A b x₀ rs₀ m) :
    IsPetrovGalerkin (op A) b x₀ (Chapter06.krylov A (Chapter06.r₀ A b x₀) m)
      (Chapter06.krylov Aᴴ rs₀ m) (bcg A b x₀ rs₀ m).x := by
  simp only [Chapter06.krylov_eq, bcg_eq]
  exact BCG.isPetrovGalerkin h.toBCG

/-- **Exercise P-7.7** of [saad2003iterative], the residual recurrence. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, assume that Algorithm 7.3
does not break down before step $m$, and let $k < m$. Then the BCG residuals satisfy $$r_{k+2} =
\Bigl(1 + \frac{\alpha_{k+1} \beta_k}{\alpha_k}\Bigr) r_{k+1} - \alpha_{k+1} A r_{k+1} -
\frac{\alpha_{k+1} \beta_k}{\alpha_k} r_k.$$ The recurrence comes from the elimination of the
direction vectors between lines 5, 6 and 9 of Algorithm 7.3.

The hypothesis is needed because of the division by $\alpha_k$.
`BCG.alpha_smul_residual_add_two` is the same identity multiplied by $\alpha_k$, and it holds at
every step. The coefficients are the backbone `BCG.alpha` and `BCG.beta`;
`SaadSparse.Chapter07.bcg_alpha_eq` and `SaadSparse.Chapter07.bcg_beta_eq` give their formulas
from lines 4 and 8. `SaadSparse.Chapter07.problem_7_7_start` gives the first two residuals. -/
theorem problem_7_7 (h : BCGNoBreakdown A b x₀ rs₀ m) {k : ℕ} (hk : k < m) :
    (bcg A b x₀ rs₀ (k + 2)).r
      = (1 + BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ (k + 1) * BCG.beta (op A) (op Aᴴ) b x₀ rs₀ k /
            BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ k) • (bcg A b x₀ rs₀ (k + 1)).r
        - BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ (k + 1) • op A (bcg A b x₀ rs₀ (k + 1)).r
        - (BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ (k + 1) * BCG.beta (op A) (op Aᴴ) b x₀ rs₀ k /
            BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ k) • (bcg A b x₀ rs₀ k).r := by
  simp only [bcg_eq]
  exact BCG.residual_add_two (op A) (op Aᴴ) b x₀ rs₀ (h.toBCG.alpha_ne_zero hk)

/-- **Exercise P-7.7** of [saad2003iterative], the direction recurrence. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$. For every $k \ge 0$, the
BCG directions satisfy $$p_{k+2} = (1 + \beta_{k+1}) p_{k+1} - \alpha_{k+1} A p_{k+1} - \beta_k
p_k.$$

The recurrence comes from the elimination of the residuals. It needs no hypothesis, also at a
breakdown, where Lean's division by zero gives $\alpha_k = 0$ or $\beta_k = 0$. -/
theorem problem_7_7_direction (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    (bcg A b x₀ rs₀ (k + 2)).p
      = (1 + BCG.beta (op A) (op Aᴴ) b x₀ rs₀ (k + 1)) • (bcg A b x₀ rs₀ (k + 1)).p
        - BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ (k + 1) • op A (bcg A b x₀ rs₀ (k + 1)).p
        - BCG.beta (op A) (op Aᴴ) b x₀ rs₀ k • (bcg A b x₀ rs₀ k).p := by
  simp only [bcg_eq]
  exact BCG.direction_add_two (op A) (op Aᴴ) b x₀ rs₀ k

/-- **Exercise P-7.7** of [saad2003iterative], the first terms of the two recurrences. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$. The first step of BCG
gives $$r_1 = r_0 - \alpha_0 A r_0 \quad\text{and}\quad p_1 = (1 + \beta_0) p_0 - \alpha_0 A
p_0.$$ Together with $r_0 = p_0 = b - Ax_0$ (`SaadSparse.Chapter07.bcg_zero`), these start the
recurrences of `SaadSparse.Chapter07.problem_7_7` and
`SaadSparse.Chapter07.problem_7_7_direction`. -/
theorem problem_7_7_start (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    (bcg A b x₀ rs₀ 1).r
        = (bcg A b x₀ rs₀ 0).r
          - BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ 0 • op A (bcg A b x₀ rs₀ 0).r ∧
      (bcg A b x₀ rs₀ 1).p
        = (1 + BCG.beta (op A) (op Aᴴ) b x₀ rs₀ 0) • (bcg A b x₀ rs₀ 0).p
          - BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ 0 • op A (bcg A b x₀ rs₀ 0).p := by
  simp only [bcg_eq]
  exact ⟨BCG.residual_one (op A) (op Aᴴ) b x₀ rs₀, BCG.direction_one (op A) (op Aᴴ) b x₀ rs₀⟩

/-- Equation (7.5) entry by entry: while Algorithm 7.1 does not break down, $(Av_j, w_i)$ is the
entry $(i, j)$ of the tridiagonal coefficient array, in $0$-based indices. -/
private theorem inner_bilanczosW_apply_bilanczosV {v w : EuclideanSpace 𝕜 (Fin n)} {k : ℕ}
    (hnb : NoBreakdown A v w k) {i j : ℕ} (hi : i ≤ k) (hj : j + 1 ≤ k) :
    inner 𝕜 (bilanczosW A v w i) (op A (bilanczosV A v w j)) = bilanczosCoeff A v w i j := by
  obtain ⟨M, rfl⟩ : ∃ M, k = M + 1 := ⟨k - 1, by omega⟩
  rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
  exact BiLanczos.inner_dualVec_apply_vec hnb.toBiLanczos hi (by omega)

/-- If Algorithm 7.1 does not break down before step $m$ and $T_m$ is nonsingular, then every
$z \in \mathcal{K}_m(A, v_1)$ with $Az \perp \mathcal{K}_m(A^H, w_1)$ is zero, so the
Petrov–Galerkin approximation of Algorithm 7.2 is unique. -/
private theorem eq_zero_of_apply_mem_orthogonal {v w : EuclideanSpace 𝕜 (Fin n)}
    (hnb : NoBreakdown A v w m) (hT : IsUnit (T A v w m)) {z : EuclideanSpace 𝕜 (Fin n)}
    (hz : z ∈ Chapter06.krylov A v m) (hAz : op A z ∈ (Chapter06.krylov Aᴴ w m)ᗮ) : z = 0 := by
  rw [← (proposition_7_1_span hnb).1] at hz
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hz
  have hTy : T A v w m *ᵥ y = 0 := by
    funext i
    have hmem : bilanczosW A v w (i : ℕ) ∈ Chapter06.krylov Aᴴ w m := by
      rw [← (proposition_7_1_span hnb).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h0 : inner 𝕜 (bilanczosW A v w (i : ℕ)) (op A z) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hAz _ hmem
    have hentry : ∀ j : Fin m,
        inner 𝕜 (bilanczosW A v w (i : ℕ)) (op A (bilanczosV A v w (j : ℕ)))
          = T A v w m i j := fun j =>
      inner_bilanczosW_apply_bilanczosV hnb (le_of_lt i.2) j.2
    rw [← hy, map_sum, inner_sum] at h0
    simp only [map_smul, inner_smul_right, hentry] at h0
    rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, ← h0]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hy0 : y = 0 := by
    have h1 : (T A v w m)⁻¹ *ᵥ (T A v w m *ᵥ y) = 0 := by rw [hTy, Matrix.mulVec_zero]
    rwa [Matrix.nonsing_inv_mulVec_mulVec hT] at h1
  rw [← hy, hy0]
  simp

/-- **Equations (7.10)–(7.12)** of [saad2003iterative]: BCG computes the iterate of Algorithm 7.2.
Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, let
$r_0 = b - Ax_0 \neq 0$ and $v_1 = r_0/\beta$, and assume $(r^*_0, v_1) \neq 0$. Let $w_1$ be
$r^*_0$ scaled so that $(v_1, w_1) = 1$. Assume that Algorithm 7.3 does not break down before
step $m$, that Algorithm 7.1 started from $(v_1, w_1)$ does not break down before step $m$, and
that $T_m$ is nonsingular. Then the BCG iterate after $m$ steps is $$x_m = x_0 + V_m T_m^{-1}
(\beta e_1),$$ the iterate of Algorithm 7.2.

The book derives this from the factorization $T_m = L_m U_m$ and the direction matrices
$P_m = V_m U_m^{-1}$ and $P^*_m = W_m L_m^{-H}$. The proof here uses that both iterates are
Petrov–Galerkin approximations onto $\mathcal{K}_m(A, r_0)$ orthogonally to
$\mathcal{K}_m(A^H, r^*_0)$, and that a nonsingular $T_m$ makes such an approximation unique.
The vector $w_1$ is `SaadSparse.Chapter07.w₁ A b x₀ rs₀`, and the iterate of Algorithm 7.2 is
`SaadSparse.Chapter07.lanczosSolve`. -/
theorem bcg_eq_lanczosSolve (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hnb : NoBreakdown A (Chapter06.v₁ A b x₀) (w₁ A b x₀ rs₀) m)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) (w₁ A b x₀ rs₀) m))
    (hr : Chapter06.r₀ A b x₀ ≠ 0) (hw : inner 𝕜 (Chapter06.v₁ A b x₀) rs₀ ≠ 0) :
    (bcg A b x₀ rs₀ m).x = lanczosSolve A b x₀ (w₁ A b x₀ rs₀) m := by
  have hK : Chapter06.krylov A (Chapter06.v₁ A b x₀) m
      = Chapter06.krylov A (Chapter06.r₀ A b x₀) m := by
    rw [Chapter06.v₁_def,
      Chapter06.krylov_smul A _ (inv_ne_zero (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hr)))]
  have hL : Chapter06.krylov Aᴴ (w₁ A b x₀ rs₀) m = Chapter06.krylov Aᴴ rs₀ m := by
    rw [show w₁ A b x₀ rs₀ = (inner 𝕜 (Chapter06.v₁ A b x₀) rs₀)⁻¹ • rs₀ from rfl,
      Chapter06.krylov_smul Aᴴ _ (inv_ne_zero hw)]
  have hlan := lanczosSolve_isPetrovGalerkin hnb hT
  rw [hK, hL] at hlan
  refine (bcg_isPetrovGalerkin h).eq_of_forall hlan fun z hz hAz => ?_
  exact eq_zero_of_apply_mem_orthogonal hnb hT (by rw [hK]; exact hz) (by rw [hL]; exact hAz)

end BCGBreakdown

/-! ### §7.3.2: Algorithm 7.4, the quasi-minimal residual method -/

section QMR

/-- The basis in which QMR expands its iterate: the primal vectors of Algorithm 7.1 started from
$v_1 = r_0/\beta$ and a dual vector $w_1$. `qmrV A b x₀ w₁ j` is the book's $v_{j+1}$. -/
noncomputable abbrev qmrV (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n) :=
  bilanczosV A (Chapter06.v₁ A b x₀) w₁

/-- The tridiagonal coefficient array of (7.2) and (7.15), whose leading $(m + 1) \times m$ block is
$\bar T_m$, for Algorithm 7.1 started from $(v_1, w_1) = (r_0/\beta, w_1)$. QMR applies its
Givens rotations to this array. -/
noncomputable abbrev qmrCoeff (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → ℕ → 𝕜 :=
  bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 7.4** of [saad2003iterative] (QMR). Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. The QMR iterate after $m$ steps is $$x^Q_m = x_0 + V_m y_m,
\qquad y_m = R_m^{-1} g_m,$$ where $V_m = [v_1, \dots, v_m]$ is the primal basis of Algorithm
7.1 started from $v_1 = r_0/\beta$ and $w_1$, and $R_m$ and $g_m$ come from the Givens rotations
that reduce $\bar T_m$ to triangular form. This is Algorithm 6.12 (QGMRES) applied to the
two-sided Lanczos basis and coefficients. When $R_m$ is nonsingular, $y_m$ minimizes the
quasi-residual norm $\|\beta e_1 - \bar T_m y\|_2$ of (7.17)
(`SaadSparse.Chapter07.qmr_isQuasiMinResidualIterate`).

The definition is `SaadSparse.Chapter06.qgmres` at the basis `SaadSparse.Chapter07.qmrV` and the
coefficients `SaadSparse.Chapter07.qmrCoeff`. When $R_m$ is singular, Lean's matrix inverse is
$0$, so $y_m = 0$. -/
noncomputable def qmr (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  Chapter06.qgmres x₀ (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m

/-- The starting relation $r_0 = \beta v_1$. -/
private theorem smul_qmrV_zero :
    b - op A x₀ = (Chapter06.β A b x₀ : 𝕜) • qmrV A b x₀ w₁ 0 := (smul_v₁_eq_r₀ A b x₀).symm

/-- The quasi-residual norm $\rho^Q_m$ is the norm of the backbone scalar `Krylov.gamma h β m`. -/
private theorem quasiResidualNorm_eq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) :
    Chapter06.quasiResidualNorm h β m = ‖Krylov.gamma h β m‖ := rfl

private theorem gamma_eq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) :
    Chapter06.γ h β m = Krylov.gamma h β m := rfl

private theorem givensC_eq (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Chapter06.c h m = Krylov.givensC h m := rfl

private theorem givensS_eq (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Chapter06.s h m = Krylov.givensS h m := rfl

/-- $|\beta| = \|r_0\|_2$, where $\beta$ is the real number $\|r_0\|_2$ seen as a scalar. -/
private theorem norm_beta : ‖(Chapter06.β A b x₀ : 𝕜)‖ = ‖Chapter06.r₀ A b x₀‖ := by
  rw [Chapter06.β_eq_norm_r₀, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-- Equation (7.19) at the level of the rotations: if the square Hessenberg system
$H_{m+1} y = \beta e_1$ has a solution $y$, then $\gamma_{m+2} = -c_{m+1} h_{m+2,m+1} \eta$ with
$\eta$ the last component of $y$, also at a degenerate rotation, where both sides vanish. -/
private theorem gamma_succ_eq_givensC_mul {h : ℕ → ℕ → 𝕜}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (β : 𝕜) {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (Krylov.hessenbergSqOf h (m + 1)).mulVec y = Krylov.firstVec β (m + 1)) :
    Krylov.gamma h β (m + 1)
      = Krylov.givensC h m * -(h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩) := by
  rw [Krylov.gamma_succ,
    ← Krylov.rotated_self_mul_eq_gamma h (Matrix.isUpperHessenberg_iff_nat.2 hh) β hy,
    Krylov.givensS, Krylov.givensC, Krylov.rotated_eq_of_le h m (m + 1) m le_rfl]
  ring

/-- If the rotated diagonal entry in position $m$ is nonzero, then the denominator of rotation $m$
is nonzero. -/
private theorem givensRho_ne_zero_of_rotated_self (h : ℕ → ℕ → 𝕜) {m : ℕ}
    (hd : Krylov.rotated h m m m ≠ 0) : Krylov.givensRho h m ≠ 0 := by
  intro h0
  have hsq := Krylov.givensRho_sq h m
  rw [h0] at hsq
  have h1 : ‖Krylov.rotated h m m m‖ ^ 2 = 0 := by
    nlinarith [norm_nonneg (Krylov.rotated h m (m + 1) m), sq_nonneg (0 : ℝ)]
  exact hd (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

/-- If $\gamma_{m+1} \neq 0$ and the system $H_{m+1} y = \beta e_1$ has a solution, then
$c_{m+1} \neq 0$, so the Galerkin iterate exists. -/
private theorem givensC_ne_zero {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (β : 𝕜)
    {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (Krylov.hessenbergSqOf h (m + 1)).mulVec y = Krylov.firstVec β (m + 1))
    (h0 : Krylov.gamma h β m ≠ 0) : Krylov.givensC h m ≠ 0 := by
  have hd : Krylov.rotated h m m m ≠ 0 := fun hc =>
    h0 (by
      rw [← Krylov.rotated_self_mul_eq_gamma h (Matrix.isUpperHessenberg_iff_nat.2 hh) β hy,
        hc, zero_mul])
  exact div_ne_zero hd (RCLike.ofReal_ne_zero.2 (givensRho_ne_zero_of_rotated_self h hd))

/-- If one quasi-residual scalar $\gamma_k$ vanishes, then all later ones vanish. -/
private theorem gamma_eq_zero_of_le (h : ℕ → ℕ → 𝕜) (β : 𝕜) {k m : ℕ} (hk : k ≤ m)
    (hc : Krylov.gamma h β k = 0) : Krylov.gamma h β m = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    rw [← Nat.add_assoc, Krylov.gamma_succ, ih (Nat.le_add_right k d), mul_zero]

/-- The Galerkin residual norms in the form that the harmonic identities of
`Numlib.Krylov.QuasiMinRes` use: $\rho^F_0 = |\beta|$ and
$\rho^F_{k+1} = |\gamma_{k+2}|/|c_{k+1}|$ in the book's indices. -/
private noncomputable def rhoF (h : ℕ → ℕ → 𝕜) (β : 𝕜) : ℕ → ℝ
  | 0 => ‖β‖
  | k + 1 => ‖Krylov.gamma h β (k + 1)‖ / ‖Krylov.givensC h k‖

private theorem rhoF_zero (h : ℕ → ℕ → 𝕜) (β : 𝕜) : rhoF h β 0 = ‖β‖ := rfl

private theorem rhoF_succ (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    rhoF h β (k + 1) = ‖Krylov.gamma h β (k + 1)‖ / ‖Krylov.givensC h k‖ := rfl

/-- QMR after $0$ steps returns $x^Q_0 = x_0$. -/
@[simp] theorem qmr_zero : qmr A b x₀ w₁ 0 = x₀ := by
  rw [qmr, Chapter06.qgmres, Chapter06.toEuclideanLin_colMatrix_apply]
  simp

variable {A b x₀ w₁}

/-- **Section 7.3.2** of [saad2003iterative], the quasi-minimal residual property of QMR. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, w_1 \in \mathbb{K}^n$, and assume that the
triangular matrix $R_m$ obtained from $\bar T_m$ by the Givens rotations is nonsingular. Then
the QMR iterate is $x^Q_m = x_0 + V_m y$ for a vector $y \in \mathbb{K}^m$ that minimizes the
quasi-residual norm $\|\beta e_1 - \bar T_m y\|_2$ over all of $\mathbb{K}^m$.

The conclusion is the backbone specification `Krylov.IsQuasiMinResidualIterate` for the basis
`SaadSparse.Chapter07.qmrV` and the coefficients `SaadSparse.Chapter07.qmrCoeff`. The results
from (7.16) on follow from this identification and theorems of `Numlib.Krylov.QuasiMinRes`. -/
theorem qmr_isQuasiMinResidualIterate {m : ℕ} (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) :
    Krylov.IsQuasiMinResidualIterate (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜)
      x₀ m (qmr A b x₀ w₁ m) :=
  Chapter06.qgmres_isQuasiMinResidualIterate x₀ _ _ _
    (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) hR

/-- **Equation (7.16)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$, and assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown. Then for every $m$ and every $y \in \mathbb{K}^m$, $$b - A(x_0 + V_m y) =
V_{m+1}(\beta e_1 - \bar T_m y).$$ Taking norms gives (7.17). If the $v_i$ were orthonormal, the
right-hand side would have the norm $\|\beta e_1 - \bar T_m y\|_2$, as in GMRES, and the
quasi-residual norm would be the residual norm.

The products $V_m y$ and $V_{m+1} u$ are written as the sums $\sum_j y_j v_j$ and
$\sum_i u_i v_i$. -/
theorem equation_7_16 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) (m : ℕ) (y : Fin m → 𝕜) :
    b - op A (x₀ + ∑ j, y j • qmrV A b x₀ w₁ (j : ℕ))
      = ∑ i, (Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1)
          - (Tbar A (Chapter06.v₁ A b x₀) w₁ m).mulVec y) i • qmrV A b x₀ w₁ (i : ℕ) := by
  rw [Tbar_eq_hessenbergOf]
  exact (bilanczos_hessenbergRelation h).residual_eq (smul_qmrV_zero A b x₀ w₁) m y

/-- **Equation (7.18)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. For every $m$, the quasi-residual norm
$\rho^Q_m = |\gamma_{m+1}|$ of QMR is the product of the sines of the Givens rotations,
$$\rho^Q_m = |s_1 s_2 \cdots s_m| \, \|r_0\|_2, \qquad\text{hence}\qquad \rho^Q_{m+1} =
|s_{m+1}| \, \rho^Q_m.$$

The norm $\rho^Q_m$ is `SaadSparse.Chapter06.quasiResidualNorm` for
`SaadSparse.Chapter07.qmrCoeff`, and $s_{k+1}$ is
`SaadSparse.Chapter06.s (qmrCoeff A b x₀ w₁) k`. -/
theorem equation_7_18 (m : ℕ) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
        = (∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖) * ‖Chapter06.r₀ A b x₀‖ ∧
      Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)
        = ‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖
          * Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m := by
  refine ⟨?_, ?_⟩
  · rw [quasiResidualNorm_eq, Krylov.norm_gamma_eq_prod, norm_beta]
  · rw [quasiResidualNorm_eq, quasiResidualNorm_eq, Krylov.gamma_succ, norm_mul, norm_neg]

/-- **Equation (7.19)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$, and assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown. Let $m \ge 1$ and assume that $T_m$ is nonsingular. Then $$\gamma_{m+1}
v_{m+1} = c_m r_m,$$ where $r_m = b - Ax_m$ is the residual of the iterate $x_m$ of Algorithm
7.2 (the BCG iterate). This is the two-sided form of (6.56).

Both sides are multiples of $v_{m+1}$, by (7.9). The Lean statement is written for $m + 1$ with
$m \ge 0$. -/
theorem equation_7_19 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) • qmrV A b x₀ w₁ (m + 1)
      = Chapter06.c (qmrCoeff A b x₀ w₁) m • (b - op A (lanczosSolve A b x₀ w₁ (m + 1))) := by
  have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (m + 1)).mulVec
      (lanczosSolveY A b x₀ w₁ (m + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1) := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hres : b - op A (lanczosSolve A b x₀ w₁ (m + 1))
      = -(qmrCoeff A b x₀ w₁ (m + 1) m
          * lanczosSolveY A b x₀ w₁ (m + 1) ⟨m, Nat.lt_succ_self m⟩)
        • qmrV A b x₀ w₁ (m + 1) := by
    rw [show qmrCoeff A b x₀ w₁ (m + 1) m = bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ (m + 1) from
      bilanczosCoeff_succ_self A _ _ m]
    exact residual_lanczosSolve h hT (Nat.succ_pos m)
  rw [hres, smul_smul, gamma_eq, givensC_eq,
    gamma_succ_eq_givensC_mul (h := qmrCoeff A b x₀ w₁)
      (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy]

/-- **Equation (7.20)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown and that its primal vectors have unit norm, $\|v_j\|_2 = 1$ for all $j$. Let
$m \ge 1$ and assume that $T_m$ is nonsingular. Then $$\rho^Q_m = |c_m| \, \rho_m,$$ where
$\rho_m = \|b - Ax_m\|_2$ is the residual norm of the iterate $x_m$ of Algorithm 7.2.

The Lean statement is written for $m + 1$ with $m \ge 0$. -/
theorem equation_7_20 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)
      = ‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ * ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ := by
  have hnorm := congrArg norm (equation_7_19 h hT)
  rw [norm_smul, norm_smul, hv (m + 1), mul_one] at hnorm
  rw [quasiResidualNorm_eq]
  exact hnorm

/-- The norms $\rho^F_i$ of the harmonic identities, for the two-sided Lanczos data, are the
residual norms $\rho_i = \|b - Ax_i\|_2$ of Algorithm 7.2. -/
private theorem rhoF_eq_norm_residual (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0) {i : ℕ} (hi : i ≤ m) :
    rhoF (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) i
      = ‖b - op A (lanczosSolve A b x₀ w₁ i)‖ := by
  cases i with
  | zero => rw [rhoF_zero, lanczosSolve_zero, norm_beta]
  | succ k =>
    have hk : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) k ≠ 0 := fun hcc =>
      h0 (gamma_eq_zero_of_le _ _ (by omega) hcc)
    have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (k + 1)).mulVec
        (lanczosSolveY A b x₀ w₁ (k + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (k + 1) := by
      rw [← T_eq_hessenbergSqOf]
      exact T_mulVec_lanczosSolveY A b x₀ w₁ (hT (k + 1))
    have hcne : ‖Krylov.givensC (qmrCoeff A b x₀ w₁) k‖ ≠ 0 := norm_ne_zero_iff.2
      (givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy hk)
    have h20 := equation_7_20 hs hv (hT (k + 1))
    rw [quasiResidualNorm_eq, givensC_eq] at h20
    rw [rhoF_succ, h20, mul_comm, mul_div_assoc, div_self hcne, mul_one]

/-- If no residual of Algorithm 7.2 vanishes, then no quasi-residual scalar $\gamma_m$ vanishes, by
(7.20) and an induction that gives $c_m \neq 0$ from $\gamma_m \neq 0$. -/
private theorem gamma_ne_zero (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0 := by
  induction m with
  | zero =>
    intro hcc
    have hb : (Chapter06.β A b x₀ : 𝕜) = 0 := hcc
    have hnb : ‖Chapter06.r₀ A b x₀‖ = 0 := by
      rw [← norm_beta (A := A) (b := b) (x₀ := x₀), hb, norm_zero]
    exact hne 0 (by rw [lanczosSolve_zero]; exact norm_eq_zero.1 hnb)
  | succ k ih =>
    have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (k + 1)).mulVec
        (lanczosSolveY A b x₀ w₁ (k + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (k + 1) := by
      rw [← T_eq_hessenbergSqOf]
      exact T_mulVec_lanczosSolveY A b x₀ w₁ (hT (k + 1))
    have hc := givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy ih
    have h20 := equation_7_20 hs hv (hT (k + 1))
    rw [quasiResidualNorm_eq, givensC_eq] at h20
    intro hcc
    rw [hcc, norm_zero] at h20
    exact mul_ne_zero (norm_ne_zero_iff.2 hc) (norm_ne_zero_iff.2 (hne (k + 1))) h20.symm

/-- **Proposition 7.3** of [saad2003iterative], equation (7.21). Let $A \in \mathbb{K}^{n \times n}$
and $b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown and that $R_m$ is nonsingular. Let $C$ be a bound for $V_{m+1}$, that is,
$\|V_{m+1} u\|_2 \le C \|u\|_2$ for all $u \in \mathbb{K}^{m+1}$. Then the QMR iterate satisfies
$$\|b - Ax^Q_m\|_2 \le C \, |s_1 \cdots s_m| \, \|r_0\|_2.$$ With $C = \|V_{m+1}\|_2$ this is
the printed bound.

The product $V_{m+1} u$ is the sum $\sum_i u_i v_i$. The proof specializes
`Krylov.IsQuasiMinResidualIterate.norm_residual_le`. -/
theorem proposition_7_3 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) {C : ℝ}
    (hC : ∀ w : Fin (m + 1) → 𝕜, ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖
      ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qmr A b x₀ w₁ m)‖
      ≤ C * ((∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖)
        * ‖Chapter06.r₀ A b x₀‖) := by
  have hprod := (equation_7_18 (A := A) (b := b) (x₀ := x₀) (w₁ := w₁) m).1
  rw [quasiResidualNorm_eq] at hprod
  rw [← hprod]
  exact Krylov.IsQuasiMinResidualIterate.norm_residual_le (bilanczos_hessenbergRelation h)
    (smul_qmrV_zero A b x₀ w₁)
    ((Chapter06.isUnit_R_iff _ (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij)).1 hR) hC
    (qmr_isQuasiMinResidualIterate hR)

/-- **Proposition 7.3** of [saad2003iterative], the bound for normalized vectors. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1
started from $(v_1, w_1)$ has no serious breakdown, that $R_m$ is nonsingular, and that
$\|v_j\|_2 \le 1$ for all $j$. Then $\|V_{m+1}\|_2 \le \sqrt{m+1}$ by the Cauchy–Schwarz
inequality, and therefore $$\|b - Ax^Q_m\|_2 \le \sqrt{m+1} \, |s_1 \cdots s_m| \, \|r_0\|_2.$$

The bound on $\|V_{m+1}\|_2$ is `Krylov.norm_sum_smul_le_sqrt_mul`. -/
theorem proposition_7_3_sqrt (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ ≤ 1) :
    ‖b - op A (qmr A b x₀ w₁ m)‖
      ≤ Real.sqrt (m + 1)
        * ((∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖)
          * ‖Chapter06.r₀ A b x₀‖) := by
  refine proposition_7_3 h hR fun w => ?_
  have := Krylov.norm_sum_smul_le_sqrt_mul (v := qmrV A b x₀ w₁) hv w
  rwa [Nat.cast_add, Nat.cast_one] at this

/-- **Theorem 7.4** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$ with $r_0 \neq 0$, and let $m \le \operatorname{grade}(v_1)$.
Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no serious breakdown and does not break
down before step $m$, that the matrix $R_m$ of QMR is nonsingular, and that the matrix $R_m$ of
GMRES, formed from the Arnoldi coefficients, is nonsingular. Let $c > 0$ and $C$ be such that
$$c \|u\|_2 \le \|V_{m+1} u\|_2 \le C \|u\|_2 \qquad (u \in \mathbb{K}^{m+1}).$$ Then
$$\|r^Q_m\|_2 \le \frac{C}{c} \, \|r^G_m\|_2,$$ where $r^Q_m = b - Ax^Q_m$ is the residual of
QMR and $r^G_m$ is the residual of GMRES after $m$ steps. The best constants give
$C/c = \kappa_2(V_{m+1})$, the condition number of the Lanczos basis.

This is the same theorem as Theorem 6.11 (`SaadSparse.Chapter06.theorem_6_11`). The full-rank
hypothesis that the book assumes there is contained in $c > 0$, and such a $c$ exists because
$V_{m+1}$ has full rank (`SaadSparse.Chapter07.problem_7_2`). GMRES is
`SaadSparse.Chapter06.gmresFixed`. The proof specializes
`Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul`. -/
theorem theorem_7_4 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hnb : NoBreakdown A (Chapter06.v₁ A b x₀) w₁ m) (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hm : m ≤ Chapter06.grade A (Chapter06.v₁ A b x₀))
    (hRA : IsUnit (Chapter06.R (Chapter06.arnoldiCoeff A (Chapter06.v₁ A b x₀)) m))
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜, c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖
      ≤ ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜, ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖
      ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qmr A b x₀ w₁ m)‖ ≤ C / c * ‖b - op A (Chapter06.gmresFixed A b x₀ m)‖ := by
  have hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => qmrV A b x₀ w₁ (i : ℕ))
      = Chapter06.krylov A (Chapter06.r₀ A b x₀) m := by
    rw [(proposition_7_1_span hnb).1, Chapter06.v₁_def,
      Chapter06.krylov_smul A _ (inv_ne_zero (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hr)))]
  exact Chapter06.theorem_6_11 b x₀ (bilanczos_hessenbergRelation h) (smul_qmrV_zero A b x₀ w₁) hR
    hm hRA hspan hc0 hc hC

/-- **Equation (7.23)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown and that its primal vectors have unit norm. Let $m \ge 0$, and assume that
$T_{m+1}$ is nonsingular and that $\gamma_{m+2} \neq 0$, that is, $\rho^Q_{m+1} \neq 0$. Then
$$\frac{1}{(\rho^Q_{m+1})^2} = \frac{1}{(\rho^Q_m)^2} + \frac{1}{\rho_{m+1}^2},$$ where
$\rho_{m+1}$ is the residual norm of the iterate $x_{m+1}$ of Algorithm 7.2. This is the
two-sided analogue of (6.65).

The proof specializes `Krylov.inv_sq_norm_gamma`. -/
theorem equation_7_23 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1)))
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) ≠ 0) :
    1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) ^ 2
      = 1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ^ 2
        + 1 / ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ ^ 2 := by
  have hk : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0 := fun hcc =>
    h0 (gamma_eq_zero_of_le _ _ (Nat.le_succ m) hcc)
  have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (m + 1)).mulVec
      (lanczosSolveY A b x₀ w₁ (m + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1) := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hcne : ‖Krylov.givensC (qmrCoeff A b x₀ w₁) m‖ ≠ 0 := norm_ne_zero_iff.2
    (givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy hk)
  have h20 := equation_7_20 h hv hT
  rw [quasiResidualNorm_eq, givensC_eq] at h20
  have hkey : ‖Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)‖
      / ‖Krylov.givensC (qmrCoeff A b x₀ w₁) m‖
      = ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ := by
    rw [h20, mul_comm, mul_div_assoc, div_self hcne, mul_one]
  rw [quasiResidualNorm_eq, quasiResidualNorm_eq, Krylov.inv_sq_norm_gamma _ _ h0, hkey]

/-- **Equation (7.24)** of [saad2003iterative], the smoothing property of QMR. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1
started from $(v_1, w_1)$ has no serious breakdown, that its primal vectors have unit norm, that
$T_k$ is nonsingular for every $k$, and that $\rho^Q_m \neq 0$. Then the quasi-residual norm is
the harmonic combination $$\frac{1}{(\rho^Q_m)^2} = \sum_{i=0}^{m} \frac{1}{\rho_i^2}$$ of the
residual norms $\rho_i = \|b - Ax_i\|_2$ of Algorithm 7.2.

The proof specializes `Krylov.inv_sq_norm_gamma_eq_sum`. -/
theorem equation_7_24 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0) :
    1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ^ 2
      = ∑ i ∈ Finset.range (m + 1), 1 / ‖b - op A (lanczosSolve A b x₀ w₁ i)‖ ^ 2 := by
  rw [quasiResidualNorm_eq,
    Krylov.inv_sq_norm_gamma_eq_sum _ _ (rhoF_zero _ _) (rhoF_succ _ _) h0]
  exact Finset.sum_congr rfl fun i hi => by
    rw [rhoF_eq_norm_residual h hv hT h0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/-- **Proposition 7.5** of [saad2003iterative], equation (7.25). Let $A \in \mathbb{K}^{n \times n}$
and $b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown, that its primal vectors have unit norm, that $T_k$ is nonsingular for every
$k$, that $\rho^Q_m \neq 0$, and that the residual $b - Ax_i$ of Algorithm 7.2 is nonzero for
every $i \le m$. Let $\rho_{m*} = \min_{0 \le i \le m} \rho_i$ be the smallest residual norm of
Algorithm 7.2 among $x_0, \dots, x_m$. Then $$\rho^Q_m \le \rho_{m*} \le \sqrt{m+1} \,
\rho^Q_m.$$

The minimum is `Finset.inf'` over $\{0, \dots, m\}$. The proof specializes
`Krylov.exists_norm_gamma_div_givensC_le`. -/
theorem proposition_7_5 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0)
    (hne : ∀ i ≤ m, b - op A (lanczosSolve A b x₀ w₁ i) ≠ 0) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
        ≤ (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩
            (fun i => ‖b - op A (lanczosSolve A b x₀ w₁ i)‖) ∧
      (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩
          (fun i => ‖b - op A (lanczosSolve A b x₀ w₁ i)‖)
        ≤ Real.sqrt (m + 1)
          * Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m := by
  rw [quasiResidualNorm_eq]
  refine ⟨Finset.le_inf' _ _ fun i hi => ?_, ?_⟩
  · have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [← rhoF_eq_norm_residual h hv hT h0 hi']
    refine Krylov.norm_gamma_le _ _ (rhoF_zero _ _) (rhoF_succ _ _) hi' h0 ?_
    rw [rhoF_eq_norm_residual h hv hT h0 hi']
    exact norm_ne_zero_iff.2 (hne i hi')
  · obtain ⟨i, hi, hle⟩ := Krylov.exists_norm_gamma_div_givensC_le (qmrCoeff A b x₀ w₁)
      (Chapter06.β A b x₀ : 𝕜) (rhoF_zero _ _) (rhoF_succ _ _) m
    refine le_trans (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ?_
    rw [← rhoF_eq_norm_residual h hv hT h0 hi]
    exact hle

/-- **Equations (7.26)–(7.27)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown and that $R_m$ is nonsingular. Then the QMR residual is $$b - Ax^Q_m =
\gamma_{m+1} z_{m+1},$$ and the auxiliary vectors satisfy $$z_{m+2} = -\bar s_{m+1} z_{m+1} +
\bar c_{m+1} v_{m+2}.$$

The vector $z_{m+1}$ is the last column of $Z_{m+1} = V_{m+1} Q_m^H$ of (6.52),
`SaadSparse.Chapter06.z`. -/
theorem equation_7_26 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) :
    b - op A (qmr A b x₀ w₁ m)
        = Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
          • Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) m ∧
      Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (m + 1)
        = starRingEnd 𝕜 (-Chapter06.s (qmrCoeff A b x₀ w₁) m)
            • Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) m
          + starRingEnd 𝕜 (Chapter06.c (qmrCoeff A b x₀ w₁) m) • qmrV A b x₀ w₁ (m + 1) := by
  exact ⟨Chapter06.equation_6_50 (bilanczos_hessenbergRelation h) (smul_qmrV_zero A b x₀ w₁) hR,
    Chapter06.equation_6_53 _ _ m⟩

/-- **Equation (7.28)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that Algorithm 7.1 started from $(v_1, w_1)$ has no
serious breakdown and that $R_m$ and $R_{m+1}$ are nonsingular. Then the QMR residuals
$r^Q_m = b - Ax^Q_m$ satisfy $$r^Q_{m+1} = |s_{m+1}|^2 \, r^Q_m + \bar c_{m+1} \gamma_{m+2} \,
v_{m+2}.$$ Over $\mathbb{R}$, and with the index shifted by one, this is the printed $r^Q_m =
s_m^2 r^Q_{m-1} + c_m \gamma_{m+1} v_{m+1}$.

The identity comes from (7.27) inserted into (7.26), with the recurrence
$\gamma_{m+2} = -s_{m+1} \gamma_{m+1}$. Nothing in it is special to the two-sided Lanczos basis,
and the proof specializes `SaadSparse.Chapter06.equation_6_55`. -/
theorem equation_7_28 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hR' : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) (m + 1))) :
    b - op A (qmr A b x₀ w₁ (m + 1))
      = ((‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜) • (b - op A (qmr A b x₀ w₁ m))
        + (starRingEnd 𝕜 (Chapter06.c (qmrCoeff A b x₀ w₁) m)
            * Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1))
          • qmrV A b x₀ w₁ (m + 1) := by
  rw [show ((‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜)
      = (‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ : 𝕜) ^ 2 by push_cast; ring]
  exact Chapter06.equation_6_55 (bilanczos_hessenbergRelation h) (smul_qmrV_zero A b x₀ w₁) hR hR'

/-- **Equation (7.29)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that the first $m + 1$ Givens rotations for the
coefficients of Algorithm 7.1 are nondegenerate, that $R_m$ and $R_{m+1}$ are nonsingular, and
that $T_{m+1}$ is nonsingular. Then $$r^Q_{m+1} = |s_{m+1}|^2 \, r^Q_m + |c_{m+1}|^2 \,
r_{m+1},$$ where $r^Q_m = b - Ax^Q_m$ and $r_{m+1}$ is the residual of the iterate $x_{m+1}$ of
Algorithm 7.2 (the BCG iterate). This is the residual form of the smoothing relation, and it
comes from (7.28) and (7.19). It explains why peaks of the BCG residual norms correspond to
plateaus of the QMR quasi-residual norms: when $|s_{m+1}|$ is near $1$, which means slow
progress of BCG, $r^Q$ is almost unchanged.

A rotation is nondegenerate when its denominator `Krylov.givensRho` is nonzero. -/
theorem equation_7_29 {m : ℕ}
    (hρ : ∀ k < m + 1, Krylov.givensRho (qmrCoeff A b x₀ w₁) k ≠ 0)
    (hRm : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) (m + 1)))
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    b - op A (qmr A b x₀ w₁ (m + 1))
      = ((‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜) • (b - op A (qmr A b x₀ w₁ m))
        + ((‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜)
          • (b - op A (lanczosSolve A b x₀ w₁ (m + 1))) := by
  refine Krylov.IsQuasiMinResidualIterate.residual_eq_combination
    (Matrix.isUpperHessenberg_iff_nat.2 fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) hρ
    (w := lanczosSolveY A b x₀ w₁ (m + 1)) (qmr_isQuasiMinResidualIterate hR)
    (qmr_isQuasiMinResidualIterate hRm) ?_ (lanczosSolve_eq_add_sum A b x₀ w₁ (m + 1))
  rw [← T_eq_hessenbergSqOf]
  exact T_mulVec_lanczosSolveY A b x₀ w₁ hT

/-- **Equation (7.30)** of [saad2003iterative]: QMR is a residual smoothing of Algorithm 7.2 with
the parameter $|c_{m+1}|^2$. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, w_1 \in \mathbb{K}^n$. Assume that the first $m + 1$ Givens rotations for the
coefficients of Algorithm 7.1 are nondegenerate, that $R_m$ and $R_{m+1}$ are nonsingular, and
that $T_{m+1}$ is nonsingular. Then $$x^Q_{m+1} = |s_{m+1}|^2 \, x^Q_m + |c_{m+1}|^2 \,
x_{m+1},$$ where $x_{m+1}$ is the iterate of Algorithm 7.2. This is the iterate form of (7.29),
from which the book derives it. Equation (7.31) writes it as $x^Q_{m+1} = x^Q_m + |c_{m+1}|^2
(x_{m+1} - x^Q_m)$.

No hypothesis on serious breakdown is needed: the identity concerns the rotations and the two
coordinate systems, not the basis. -/
theorem equation_7_30 {m : ℕ}
    (hρ : ∀ k < m + 1, Krylov.givensRho (qmrCoeff A b x₀ w₁) k ≠ 0)
    (hRm : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) (m + 1)))
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    qmr A b x₀ w₁ (m + 1)
      = ((‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜) • qmr A b x₀ w₁ m
        + ((‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜)
          • lanczosSolve A b x₀ w₁ (m + 1) := by
  refine Krylov.IsQuasiMinResidualIterate.eq_combination
    (Matrix.isUpperHessenberg_iff_nat.2 fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) hρ
    (w := lanczosSolveY A b x₀ w₁ (m + 1)) (qmr_isQuasiMinResidualIterate hR)
    (qmr_isQuasiMinResidualIterate hRm) ?_ (lanczosSolve_eq_add_sum A b x₀ w₁ (m + 1))
  rw [← T_eq_hessenbergSqOf]
  exact T_mulVec_lanczosSolveY A b x₀ w₁ hT

end QMR

/-! ### Algorithm 7.5: quasi-minimal residual smoothing -/

section Smoothing

/-- **Algorithm 7.5** of [saad2003iterative] (the quasi-minimal residual smoothing of Zhou and
Walker). Let $x_0, x_1, \dots \in \mathbb{R}^n$ be any sequence, with given residual vectors
$r_0, r_1, \dots$. Set $\tau_0 = \|r_0\|_2$, $x^Q_0 = x_0$ and $r^Q_0 = r_0$, and for $j \ge 1$
$$\frac{1}{\tau_j^2} = \frac{1}{\tau_{j-1}^2} + \frac{1}{\|r_j\|_2^2}, \qquad \eta_j =
  \frac{\tau_{j-1}^2}{\tau_{j-1}^2 + \|r_j\|_2^2},$$
$$x^Q_j = x^Q_{j-1} + \eta_j (x_j - x^Q_{j-1}), \qquad r^Q_j = r^Q_{j-1} + \eta_j (r_j -
  r^Q_{j-1}).$$
The value at $j$ is the pair $(x^Q_j, r^Q_j)$.

When $\tau_{j-1} \neq 0$ and $r_j \neq 0$, $\eta_j = (\tau_j/\|r_j\|_2)^2$, which is the form of
the book. The definition is `SaadSparse.Chapter06.qmrs`, the smoothing of Section 6.5.8, applied
to an arbitrary sequence. Lean's division by zero gives $1/0 = 0$ in the recurrence for
$\tau_j$; thus if $\tau_{j-1} = 0$ and $r_j \neq 0$, then $\eta_j = 0$ but $\tau_j = \|r_j\|_2$. -/
noncomputable abbrev qmrSmoothing (xO rO : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := Chapter06.qmrs xO rO

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ w₁ : EuclideanSpace ℝ (Fin n)}

private theorem qmrsTau_zero (rO : ℕ → EuclideanSpace ℝ (Fin n)) :
    Chapter06.qmrsTau rO 0 = ‖rO 0‖ := rfl

private theorem qmrsTau_succ (rO : ℕ → EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Chapter06.qmrsTau rO (m + 1)
      = Real.sqrt (1 / (1 / Chapter06.qmrsTau rO m ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2)) := rfl

private theorem qmrsEta_def (rO : ℕ → EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Chapter06.qmrsEta rO m
      = Chapter06.qmrsTau rO m ^ 2 / (Chapter06.qmrsTau rO m ^ 2 + ‖rO (m + 1)‖ ^ 2) := rfl

/-- If $P, R > 0$ and $1/(cR)^2 = 1/P^2 + 1/R^2$, then $P^2/(P^2 + R^2) = c^2$: with $P = \rho^Q_m$,
$R = \rho_{m+1}$ and (7.23), the smoothing parameter of Algorithm 6.14 is $|c_{m+1}|^2$. -/
private theorem eta_eq_sq (P R c : ℝ) (hP : 0 < P) (hR : 0 < R)
    (h23 : 1 / (c * R) ^ 2 = 1 / P ^ 2 + 1 / R ^ 2) :
    P ^ 2 / (P ^ 2 + R ^ 2) = c ^ 2 := by
  have hP2 : (0 : ℝ) < P ^ 2 := by positivity
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at h23
    have : (0 : ℝ) < 1 / P ^ 2 + 1 / R ^ 2 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at h23
    linarith
  have hfin : P ^ 2 = (P ^ 2 + R ^ 2) * c ^ 2 := by
    field_simp at h23
    linear_combination h23
  rw [div_eq_iff (by positivity)]
  linear_combination hfin

/-- Applied to the iterates of Algorithm 7.2, the scale factors of Algorithm 7.5 are the
quasi-residual norms of QMR, $\tau_m = \rho^Q_m$, by (7.23). -/
private theorem qmrsTau_eq (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Chapter06.qmrsTau (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m
      = Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : ℝ) m := by
  induction m with
  | zero =>
    have habs : ‖(Chapter06.β A b x₀ : ℝ)‖ = ‖Chapter06.r₀ A b x₀‖ :=
      (Real.norm_eq_abs (Chapter06.β A b x₀)).trans
        (abs_of_nonneg (norm_nonneg (Chapter06.r₀ A b x₀)))
    rw [qmrsTau_zero, quasiResidualNorm_eq, lanczosSolve_zero]
    exact habs.symm
  | succ k ih =>
    have h23 := equation_7_23 hs hv (hT (k + 1)) (gamma_ne_zero hs hv hT hne (k + 1))
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h23
    rw [qmrsTau_succ, ih, ← h23, one_div_one_div, quasiResidualNorm_eq,
      Real.sqrt_sq (norm_nonneg _)]

/-- Applied to the iterates of Algorithm 7.2, the smoothing parameter of step $m + 1$ of Algorithm
7.5 is $|c_{m+1}|^2$, which makes the algorithm reproduce QMR. -/
private theorem qmrsEta_eq (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Chapter06.qmrsEta (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m
      = ‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ ^ 2 := by
  have h20 := equation_7_20 hs hv (hT (m + 1))
  have h23 := equation_7_23 hs hv (hT (m + 1)) (gamma_ne_zero hs hv hT hne (m + 1))
  have hpos := gamma_ne_zero hs hv hT hne m
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h20 h23 hpos
  rw [qmrsEta_def, qmrsTau_eq hs hv hT hne m, quasiResidualNorm_eq]
  refine eta_eq_sq _ _ _ (norm_pos_iff.2 hpos) (norm_pos_iff.2 (hne (m + 1))) ?_
  rw [← h20, h23, quasiResidualNorm_eq]

/-- **Algorithm 7.5** of [saad2003iterative], applied to the iterates of Algorithm 7.2. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0, w_1 \in \mathbb{R}^n$. Assume that Algorithm 7.1
started from $(v_1, w_1)$ has no serious breakdown, that its primal vectors have unit norm, that
$T_k$ and the QMR matrix $R_k$ are nonsingular for every $k$, and that no residual
$r_j = b - Ax_j$ of Algorithm 7.2 vanishes. Then Algorithm 7.5 applied to the iterates $x_j$ of
Algorithm 7.2 (the BCG iterates) and their residuals $r_j$ reproduces the QMR iterates: for
every $m$, its iterate $x^Q_m$ is the iterate of Algorithm 7.4.

This is the remark of the book that closes Section 7.3. The reason is that (7.29) is the
smoothing recurrence with $\eta_m = |c_m|^2 = (\rho^Q_m/\rho_m)^2$. -/
theorem qmrSmoothing_eq_qmr {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ w₁ : EuclideanSpace ℝ (Fin n)} (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hR : ∀ k, IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    (qmrSmoothing (fun j => lanczosSolve A b x₀ w₁ j)
        (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m).1 = qmr A b x₀ w₁ m := by
  simp only [qmrSmoothing]
  induction m with
  | zero => simp [Chapter06.qmrs_zero]
  | succ k ih =>
    have hρ := (Chapter06.isUnit_R_iff (qmrCoeff A b x₀ w₁)
      (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij)).1 (hR (k + 1))
    have hcs := Krylov.norm_givensC_sq_add_norm_givensS_sq (qmrCoeff A b x₀ w₁) k
      (hρ k (Nat.lt_succ_self k))
    rw [Chapter06.qmrs_succ, ih, qmrsEta_eq h hv hT hne k,
      equation_7_30 hρ (hR k) (hR (k + 1)) (hT (k + 1))]
    simp only [RCLike.ofReal_real_eq_id, id_eq, givensC_eq, givensS_eq] at hcs ⊢
    rw [show ‖Krylov.givensS (qmrCoeff A b x₀ w₁) k‖ ^ 2
        = 1 - ‖Krylov.givensC (qmrCoeff A b x₀ w₁) k‖ ^ 2 from by linarith]
    module

end Smoothing

end SaadSparse.Chapter07
