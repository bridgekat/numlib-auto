/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Chebyshev
import Numlib.Analysis.InnerProductSpace.Orthonormal
import Numlib.Krylov.Hessenberg

/-!
# Quasi-minimal residual methods

This module studies what a Krylov method can still prove when the basis in which it expands the
residual is not orthonormal. Throughout, an iterate basis $z_0, z_1, \dots$ and a residual basis
$v_0, v_1, \dots$ are tied by the two-family Hessenberg relation
$A z_j = \sum_{i \le j+1} h_{ij} v_i$ (`Krylov.HessenbergRelation₂`). If $b - A x_0 = \beta v_0$,
the residual of $x_0 + \sum_{j<m} y_j z_j$ has the coordinates $\beta e_1 - \bar H_m y$ in the
residual basis. The **quasi-residual** is the Euclidean norm $\|\beta e_1 - \bar H_m y\|_2$ of these
coordinates, and a **quasi-minimal-residual iterate** is $x_0 + \sum_j y_j z_j$ with $y$ a minimizer
of the quasi-residual. QMR ([freund1991qmr]; Algorithm 7.4 of [saad2003iterative]), TFQMR (Algorithm
7.8), QGMRES and DQGMRES (Algorithms 6.12–6.13) and FGMRES (Algorithm 9.6) all produce such
iterates, each for its own $z$, $v$ and $h$.

For the Arnoldi basis the quasi-minimal-residual iterate is the minimal-residual iterate. In general
it minimizes something else, and the module bounds the difference: the true residual is at most
$C |\gamma_m|$ when $\|\sum_i w_i v_i\| \le C \|w\|_2$, and at most $C/c$ times the residual of any
other point of the same affine space when also $c \|w\|_2 \le \|\sum_i w_i v_i\|$. The module also
proves the harmonic relations between the quasi-residual norms and the Galerkin norms, stated
through the Givens rotations alone, and the smoothing identity
$x^Q_{m+1} = |s_m|^2 x^Q_m + |c_m|^2 x^F_{m+1}$ ([saad2003iterative], (7.29)–(7.30) and (6.58);
[zhou1994residual]).

## Main definitions

* `Krylov.quasiResidual`: the quasi-residual $\|\beta e_1 - \bar H_m y\|_2$.
* `Krylov.IsQuasiMinResidualIterate`: $x = x_0 + \sum_{j<m} y_j z_j$ with $y$ a minimizer of the
  quasi-residual.

## Main results

* `Krylov.quasiResidual_isMinOn_iff`: $y$ minimizes the quasi-residual if and only if
  $R_m y = (g_0, \dots, g_{m-1})$.
* `Krylov.quasiResidual_eq_norm_gamma`: the minimum of the quasi-residual is $|\gamma_m|$.
* `Krylov.IsQuasiMinResidualIterate.norm_residual_le`: if $\|\sum_i w_i v_i\| \le C \|w\|_2$, then
  $\|b - A x\| \le C |\gamma_m|$ ([saad2003iterative], Proposition 7.3).
* `Krylov.norm_sum_smul_le_sqrt_mul`: for vectors of norm at most $1$, the constant $C = \sqrt{m+1}$
  works.
* `Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul`: if
  $c \|w\|_2 \le \|\sum_i w_i v_i\| \le C \|w\|_2$ with $c > 0$, the residual of $x$ is at most
  $C/c$ times the residual of every point of the same affine space ([saad2003iterative], Theorems
  6.11 and 7.4).
* `Krylov.IsQuasiMinResidualIterate.isMinOn_norm_residual`: with an orthonormal residual basis, $x$
  minimizes $\|b - A x\|$ over $x_0 + \operatorname{span}\{z_0, \dots, z_{m-1}\}$
  ([saad2003iterative], Proposition 9.2).
* `Krylov.isQuasiMinResidualIterate_iff_isMinResidualIterate`: for the Arnoldi basis, the
  quasi-minimal-residual iterates are the minimal-residual iterates.
* `Krylov.inv_sq_norm_gamma` and `Krylov.inv_sq_norm_gamma_eq_sum`: $1/(\rho^Q_{m+1})^2 =
  1/(\rho^Q_m)^2 + 1/(\rho^F_{m+1})^2$ and $1/(\rho^Q_m)^2 = \sum_{i \le m} 1/(\rho^F_i)^2$
  ([saad2003iterative], (7.23) and (7.24)).
* `Krylov.exists_norm_gamma_div_givensC_le`: $\min_{i \le m} \rho^F_i \le \sqrt{m+1} \, \rho^Q_m$
  ([saad2003iterative], Proposition 7.5).
* `Krylov.IsQuasiMinResidualIterate.eq_combination` and
  `Krylov.IsQuasiMinResidualIterate.residual_eq_combination`:
  $x^Q_{m+1} = |s_m|^2 x^Q_m + |c_m|^2 x^F_{m+1}$, and the same combination for the residuals.

## Notation

* $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and $(h_{ij})_{i, j \ge 0}$ are scalars in
  $\mathbb{K}$.
* $\bar H_m = (h_{ij})_{i \le m, j < m}$ is the $(m+1) \times m$ Hessenberg matrix, and
  $H_m = (h_{ij})_{i, j < m}$ is the square Hessenberg matrix. In Lean they are
  `Krylov.hessenbergOf h m` and `Krylov.hessenbergSqOf h m`.
* $\beta e_1 \in \mathbb{K}^{m+1}$ is the vector `Krylov.firstVec β (m + 1)`.
* $c_k$, $s_k$ and $\rho_k$ are the parameters of the $k$-th Givens rotation of $\bar H_m$
  (`Krylov.givensC`, `Krylov.givensS`, `Krylov.givensRho`), $R_m$ is the upper triangular matrix
  after the first $m$ rotations, and $g_k = \bar c_k \gamma_k$ (`Krylov.gvec`) with
  $\gamma_0 = \beta$ and $\gamma_{k+1} = -s_k \gamma_k$ (`Krylov.gamma`).
* $\rho^Q_k = |\gamma_k|$ is the quasi-residual norm after $k$ steps, and
  $\rho^F_k = \rho^Q_k / |c_{k-1}|$ for $k \ge 1$, with $\rho^F_0 = |\beta|$, is the Galerkin norm.
  Where $c_{k-1} = 0$, the division gives $\rho^F_k = 0$, and the term $1/(\rho^F_k)^2$ is $0$.
* $x^Q_m$ is the quasi-minimal-residual iterate and $x^F_m$ the Galerkin iterate after $m$ steps.
  Indices start at $0$, as in the rest of the Krylov library.

## Implementation notes

* The residual formulas `Krylov.HessenbergRelation₂.residual_eq` and
  `Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq` of `Numlib.Krylov.Hessenberg` hold for two
  families $z$, $v$. All results of this module use them at this generality.
* The harmonic relations are stated for $\gamma_k$ and $c_k$ alone, with no basis. They are the
  Givens forms of `Krylov.inv_sq_norm_residual_minRes` and
  `Krylov.exists_norm_residual_galerkin_le`, which are (6.65) and Proposition 6.15 of
  [saad2003iterative] for true residuals.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-! ### The quasi-residual -/

/-- Let $(h_{ij})_{i, j \ge 0}$ be scalars, $\beta \in \mathbb{K}$ and $m \in \mathbb{N}$. The
**quasi-residual** of $y \in \mathbb{K}^m$ is the Euclidean norm
$$\|\beta e_1 - \bar H_m y\|_2$$
in $\mathbb{K}^{m+1}$ ([saad2003iterative], §7.3.2).

Under a two-family Hessenberg relation with $b - A x_0 = \beta v_0$, the vector
$\beta e_1 - \bar H_m y$ holds the coordinates, in the residual basis $v_0, \dots, v_m$, of the
residual of $x_0 + \sum_{j<m} y_j z_j$. The quasi-residual is the true residual norm when this
basis is orthonormal. -/
noncomputable def quasiResidual (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

/-- The quasi-residual of $y$ is the Euclidean norm of
$\beta e_1 - \bar H_m y \in \mathbb{K}^{m+1}$. -/
theorem quasiResidual_def (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    quasiResidual h β m y =
      ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ := rfl

/-- The quasi-residual is nonnegative. -/
theorem quasiResidual_nonneg (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    0 ≤ quasiResidual h β m y := norm_nonneg _

namespace HessenbergRelation₂

/-- Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K}$, and let sequences
$z$, $v$ in $E$ and scalars $h_{ij}$ satisfy the two-family Hessenberg relation
$A z_j = \sum_{i \le j+1} h_{ij} v_i$. Let $b, x_0 \in E$ and $\beta \in \mathbb{K}$ with
$b - A x_0 = \beta v_0$, and let $C \in \mathbb{R}$ with
$\|\sum_{i=0}^{m} w_i v_i\| \le C \|w\|_2$ for all $w \in \mathbb{K}^{m+1}$. Then for every
$y \in \mathbb{K}^m$
$$\Big\| b - A \Big( x_0 + \sum_{j<m} y_j z_j \Big) \Big\| \le C \, \|\beta e_1 - \bar H_m
  y\|_2.$$
This is Proposition 7.3 and (6.51) of [saad2003iterative].

The bound holds for every $y$ and needs no hypothesis on the Givens rotations. At a minimizer of
the quasi-residual it gives `Krylov.IsQuasiMinResidualIterate.norm_residual_le`. -/
theorem norm_residual_le {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜}
    (hv : HessenbergRelation₂ A z v h) {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    {C : ℝ} (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • z j)‖ ≤ C * quasiResidual h β m y := by
  rw [hv.residual_eq hr m y, quasiResidual_def]
  exact hC _

end HessenbergRelation₂

section QuasiResidual

variable (h : ℕ → ℕ → 𝕜)

/-- Let $(h_{ij})$ be upper Hessenberg, let $m \in \mathbb{N}$ with $\rho_k \neq 0$ for all $k < m$,
and let $\beta \in \mathbb{K}$. Then $y \in \mathbb{K}^m$ minimizes the quasi-residual
$\|\beta e_1 - \bar H_m y\|_2$ over $\mathbb{K}^m$ if and only if
$$R_m y = (g_0, \dots, g_{m-1}),$$
where $R_m$ is the upper triangular $m \times m$ matrix after the first $m$ Givens rotations and
$g_k = \bar c_k \gamma_k$ ([saad2003iterative], (6.41)–(6.43)).

Here $R_m$ is `Krylov.hessenbergSqOf (Krylov.rotated h m) m` and $g_k$ is `Krylov.gvec h β k`. -/
theorem quasiResidual_isMinOn_iff (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (β : 𝕜) (y : Fin m → 𝕜) :
    IsMinOn (quasiResidual h β m) Set.univ y ↔
      (hessenbergSqOf (rotated h m) m).mulVec y = fun i : Fin m => gvec h β (i : ℕ) := by
  have hsplit : ∀ w : Fin m → 𝕜, quasiResidual h β m w ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h m) m).mulVec w) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 +
        ‖gamma h β m‖ ^ 2 := fun w => norm_sq_firstVec_sub_mulVec_eq h hh hρ β w
  constructor
  · intro hmin
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      (isUnit_hessenbergSqOf_rotated_self h hh hρ) (fun i : Fin m => gvec h β (i : ℕ))
    have hw2 : quasiResidual h β m w ^ 2 = ‖gamma h β m‖ ^ 2 := by
      rw [hsplit w, hw, sub_self]
      simp
    have hle : quasiResidual h β m y ≤ quasiResidual h β m w :=
      isMinOn_iff.mp hmin w (Set.mem_univ w)
    have hD : ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
        (hessenbergSqOf (rotated h m) m).mulVec y) : EuclideanSpace 𝕜 (Fin m))‖ = 0 := by
      have h1 := hsplit y
      have h2 := quasiResidual_nonneg h β m y
      have h4 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h m) m).mulVec y) : EuclideanSpace 𝕜 (Fin m))‖ := norm_nonneg _
      nlinarith
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at hD
    exact (sub_eq_zero.mp hD).symm
  · intro hy
    have hy2 : quasiResidual h β m y ^ 2 = ‖gamma h β m‖ ^ 2 := by
      rw [hsplit y, hy, sub_self]
      simp
    refine isMinOn_iff.mpr fun w _ => ?_
    have h1 := hsplit w
    have h3 := quasiResidual_nonneg h β m w
    nlinarith

/-- Let $(h_{ij})$ be upper Hessenberg, let $m \in \mathbb{N}$ with $\rho_k \neq 0$ for all $k < m$,
and let $\beta \in \mathbb{K}$. If $y \in \mathbb{K}^m$ minimizes the quasi-residual, then
$$\|\beta e_1 - \bar H_m y\|_2 = |\gamma_m|.$$
By `Krylov.norm_gamma_eq_prod`, this value is $|s_0 \cdots s_{m-1}| \, |\beta|$
([saad2003iterative], (7.18) and (6.42)).

No basis enters the statement. -/
theorem quasiResidual_eq_norm_gamma (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (β : 𝕜) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    quasiResidual h β m y = ‖gamma h β m‖ := by
  have hsol := (quasiResidual_isMinOn_iff h hh hρ β y).mp hy
  have h1 : quasiResidual h β m y ^ 2 = ‖gamma h β m‖ ^ 2 := by
    rw [quasiResidual_def, norm_sq_firstVec_sub_mulVec_eq h hh hρ β y, hsol, sub_self]
    simp
  have h2 := quasiResidual_nonneg h β m y
  have h3 := norm_nonneg (gamma h β m)
  nlinarith

end QuasiResidual

/-! ### The quasi-minimal-residual specification -/

/-- Let $z$ be a sequence in $E$, let $(h_{ij})$ be scalars, and let $\beta \in \mathbb{K}$,
$x_0 \in E$ and $m \in \mathbb{N}$. A point $x \in E$ is a **quasi-minimal-residual iterate** at
step $m$ if
$$x = x_0 + \sum_{j<m} y_j z_j$$
for some $y \in \mathbb{K}^m$ that minimizes the quasi-residual $\|\beta e_1 - \bar H_m y\|_2$
over $\mathbb{K}^m$.

QMR (Algorithm 7.4 of [saad2003iterative]), TFQMR (Algorithm 7.8), QGMRES and DQGMRES
(Algorithms 6.12–6.13) and FGMRES (Algorithm 9.6) all produce such iterates, each for its own
$z$, $v$ and $h$. The residual basis $v$ does not enter the definition. It enters the theorems
through the hypothesis `Krylov.HessenbergRelation₂ A z v h`. -/
def IsQuasiMinResidualIterate (z : ℕ → E) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (x₀ : E) (m : ℕ) (x : E) : Prop :=
  ∃ y : Fin m → 𝕜, IsMinOn (quasiResidual h β m) Set.univ y ∧ x = x₀ + ∑ j, y j • z j

/-- Let $v_0, v_1, \dots$ be vectors with $\|v_i\| \le 1$ for all $i$. Then for every
$n \in \mathbb{N}$ and $w \in \mathbb{K}^n$
$$\Big\| \sum_{i<n} w_i v_i \Big\| \le \sqrt{n} \, \|w\|_2.$$
For unit basis vectors this is the bound $\|V_{m+1}\|_2 \le \sqrt{m+1}$ of (6.51) and (7.83) in
[saad2003iterative].

The proof is the Cauchy–Schwarz inequality. The bound gives the constant $C$ of
`Krylov.IsQuasiMinResidualIterate.norm_residual_le` in the normalization of the source. -/
theorem norm_sum_smul_le_sqrt_mul {n : ℕ} {v : ℕ → E} (hv : ∀ i, ‖v i‖ ≤ 1) (w : Fin n → 𝕜) :
    ‖∑ i, w i • v i‖ ≤ Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ := by
  have h1 : ‖∑ i, w i • v i‖ ≤ ∑ i, ‖w i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv _)
  have h2 : (∑ i, ‖w i‖) ^ 2 ≤ (n : ℝ) * ∑ i, ‖w i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ‖w i‖)
  have h3 : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have h4 : (0 : ℝ) ≤ ∑ i, ‖w i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h5 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have h6 : (0 : ℝ) ≤ Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ := by
    positivity
  have h8 : (∑ i, ‖w i‖) ^ 2 ≤
      (Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖) ^ 2 := by
    rw [mul_pow, h5, h3]
    exact h2
  refine h1.trans ?_
  have h9 := Real.sqrt_le_sqrt h8
  rwa [Real.sqrt_sq h4, Real.sqrt_sq h6] at h9

namespace IsQuasiMinResidualIterate

variable {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ x : E} {β : 𝕜} {m : ℕ}

/-- Let $A$, $z$, $v$ and $h$ satisfy the two-family Hessenberg relation
$A z_j = \sum_{i \le j+1} h_{ij} v_i$, let $b - A x_0 = \beta v_0$, and let $\rho_k \neq 0$ for
all $k < m$. Let $C \in \mathbb{R}$ with $\|\sum_{i=0}^{m} w_i v_i\| \le C \|w\|_2$ for all
$w \in \mathbb{K}^{m+1}$. If $x$ is a quasi-minimal-residual iterate at step $m$, then
$$\|b - A x\| \le C \, |\gamma_m|.$$
This is Proposition 7.3 of [saad2003iterative], with (6.51) and (7.83).

The constant $C$ measures how far the residual basis is from an orthonormal one. For vectors of
norm at most $1$, `Krylov.norm_sum_smul_le_sqrt_mul` gives $C = \sqrt{m+1}$. -/
theorem norm_residual_le (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    (hρ : ∀ k < m, givensRho h k ≠ 0) {C : ℝ}
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (hx : IsQuasiMinResidualIterate z h β x₀ m x) : ‖b - A x‖ ≤ C * ‖gamma h β m‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine (hv.norm_residual_le hr hC y).trans_eq ?_
  rw [quasiResidual_eq_norm_gamma h hv.isUpperHessenberg hρ β hy]

/-- Let $A$, $z$, $v$ and $h$ satisfy the two-family Hessenberg relation
$A z_j = \sum_{i \le j+1} h_{ij} v_i$, and let $b - A x_0 = \beta v_0$. Let $0 < c$ and $C$ be
real numbers with
$$c \|w\|_2 \le \Big\| \sum_{i=0}^{m} w_i v_i \Big\| \le C \|w\|_2 \qquad (w \in
  \mathbb{K}^{m+1}).$$
If $x$ is a quasi-minimal-residual iterate at step $m$, then for every $w \in \mathbb{K}^m$
$$\|b - A x\| \le \frac{C}{c} \, \Big\| b - A \Big( x_0 + \sum_{j<m} w_j z_j \Big) \Big\|.$$
This is Theorem 7.4 of [saad2003iterative] and Theorem 6.11. When the other point is the
minimal-residual iterate, it gives $\|r^Q_m\| \le \kappa_2(V_{m+1}) \|r^G_m\|$.

The ratio $C/c$ plays the part of the condition number of the residual basis. The proof needs
neither a factorization of the residual basis nor its full rank, and it makes no assumption on
the Givens rotations. -/
theorem norm_residual_le_mul (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜,
      c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤ ‖∑ i, w i • v i‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (hx : IsQuasiMinResidualIterate z h β x₀ m x) (w : Fin m → 𝕜) :
    ‖b - A x‖ ≤ C / c * ‖b - A (x₀ + ∑ j, w j • z j)‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hone : ‖(WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
      EuclideanSpace 𝕜 (Fin (m + 1)))‖ = 1 := by
    have hsq : ‖(WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Pi.single_apply]
      rw [Finset.sum_eq_single (0 : Fin (m + 1))]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    nlinarith [norm_nonneg (WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
      EuclideanSpace 𝕜 (Fin (m + 1)))]
  have hcC : c ≤ C := by
    have h1 := hc (Pi.single (0 : Fin (m + 1)) (1 : 𝕜))
    have h2 := hC (Pi.single (0 : Fin (m + 1)) (1 : 𝕜))
    rw [hone, mul_one] at h1 h2
    linarith
  have hC0 : 0 ≤ C := hc0.le.trans hcC
  rw [hv.residual_eq hr m y, hv.residual_eq hr m w]
  have hmin := isMinOn_iff.mp hy w (Set.mem_univ w)
  rw [quasiResidual_def, quasiResidual_def] at hmin
  refine ((hC _).trans (mul_le_mul_of_nonneg_left hmin hC0)).trans ?_
  have h9 : C * ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec w) :
      EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      C / c * (c * ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec w) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖) := by
    field_simp
  rw [h9]
  exact mul_le_mul_of_nonneg_left (hc _) (div_nonneg hC0 hc0.le)

/-- Let $A$, $z$, $v$ and $h$ satisfy the two-family Hessenberg relation
$A z_j = \sum_{i \le j+1} h_{ij} v_i$, let $b - A x_0 = \beta v_0$, and let $v_0, \dots, v_m$ be
orthonormal; the iterate basis $z$ is arbitrary. If $x$ is a quasi-minimal-residual iterate at
step $m$, then $x$ is a minimal-residual point of $x_0 + \operatorname{span}\{z_0, \dots,
z_{m-1}\}$: $x - x_0$ lies in this span, and $\|b - A x\| \le \|b - A x'\|$ for every $x'$ of
$x_0 + \operatorname{span}\{z_0, \dots, z_{m-1}\}$. This is Proposition 9.2 of
[saad2003iterative], the optimality of FGMRES.

With an orthonormal residual basis the quasi-residual is the residual norm. The conclusion is
`IsMinResidual` for the span. -/
theorem isMinOn_norm_residual (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    (hon : Orthonormal 𝕜 fun i : Fin (m + 1) => v (i : ℕ))
    (hx : IsQuasiMinResidualIterate z h β x₀ m x) :
    IsMinResidual A b x₀ (Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ))) x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hnorm : ∀ u : Fin m → 𝕜,
      ‖b - A (x₀ + ∑ j, u j • z j)‖ = quasiResidual h β m u := fun u => by
    rw [hv.residual_eq hr m u, hon.norm_sum_smul_eq_norm_toLp, quasiResidual_def]
  refine ⟨?_, fun w hw => ?_⟩
  · have hmem : ∑ j, y j • z (j : ℕ) ∈
        Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ)) :=
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    simpa using hmem
  · obtain ⟨c, hcw⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hw
    have hwe : w = x₀ + ∑ j, c j • z j := by
      rw [hcw]
      abel
    rw [hwe, hnorm, hnorm]
    exact isMinOn_iff.mp hy c (Set.mem_univ c)

end IsQuasiMinResidualIterate

/-- Let $A$ be a linear operator on $E$, let $b, x_0 \in E$, and let $r_0 = b - A x_0$ have a
finite-dimensional Krylov space $\mathcal{K}(A, r_0)$. Let $m \le \operatorname{grade}(A, r_0)$.
Take the Arnoldi vectors of $A$ and $r_0$ as the iterate basis, the Arnoldi coefficients as $h$,
and $\beta = \|r_0\|$. Then $x$ is a quasi-minimal-residual iterate at step $m$ if and only if
$x$ is a minimal-residual iterate at step $m$, that is, $x$ minimizes $\|b - A x\|$ over
$x_0 + \mathcal{K}_m(A, r_0)$.

This is the statement of [saad2003iterative], §6.5.6, that QGMRES coincides with GMRES when the
orthogonalization is complete. It shows that `Krylov.IsQuasiMinResidualIterate` generalizes
`Krylov.IsMinResidualIterate`.

The Arnoldi vectors are `Arnoldi.vec A (b - A x₀)`, the coefficients are
`Arnoldi.coeff A (b - A x₀)`, and the Krylov space is `Krylov.fullSubspace A (b - A x₀)`. -/
theorem isQuasiMinResidualIterate_iff_isMinResidualIterate {A : E →ₗ[𝕜] E} {b x₀ : E}
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (x : E) :
    IsQuasiMinResidualIterate (Arnoldi.vec A (b - A x₀)) (Arnoldi.coeff A (b - A x₀))
        (‖b - A x₀‖ : 𝕜) x₀ m x ↔ IsMinResidualIterate A b x₀ m x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (isMinResidualIterate_iff_isMinOn hm y).mpr hy
  · intro hx
    have hmem : x - x₀ ∈ Submodule.span 𝕜 (Set.range fun j : Fin m =>
        Arnoldi.vec A (b - A x₀) (j : ℕ)) := by
      rw [span_range_vec]
      exact hx.mem
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hmem
    have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ) := by
      rw [hy]
      abel
    rw [hxe] at hx
    exact ⟨y, (isMinResidualIterate_iff_isMinOn hm y).mp hx, hxe⟩

/-! ### The harmonic relations between quasi-residual norms -/

section Harmonic

variable (h : ℕ → ℕ → 𝕜)

/-- Let $(h_{ij})$ be scalars and $k \in \mathbb{N}$. If the subdiagonal entry $h_{k+1,k}$ is
nonzero, then the $k$-th Givens rotation is nondegenerate: $\rho_k \neq 0$.

This is how the hypothesis $\rho_k \neq 0$ for all $k < m$ of
`Krylov.quasiResidual_eq_norm_gamma` and of the residual bounds is met in practice. For the
Arnoldi coefficients it is `Krylov.givensRho_arnoldi_ne_zero`. The result is the companion of
`Krylov.givensRho_ne_zero_of_rotated_ne_zero` in `Numlib.Krylov.Hessenberg`. -/
theorem givensRho_ne_zero_of_subdiag_ne_zero {k : ℕ} (hk : h (k + 1) k ≠ 0) :
    givensRho h k ≠ 0 := by
  intro h0
  have hd := (rotated_eq_zero_of_givensRho_eq_zero h h0).2
  rw [rotated_eq_of_le h k (k + 1) k le_rfl] at hd
  exact hk hd

/-- For real $S, G \neq 0$ and $C$ with $C^2 + S^2 = 1$, $1/(SG)^2 = 1/G^2 + C^2/(SG)^2$. -/
private theorem inv_sq_harmonic {S G C : ℝ} (hS : S ≠ 0) (hG : G ≠ 0)
    (hCS : C ^ 2 + S ^ 2 = 1) : 1 / (S * G) ^ 2 = 1 / G ^ 2 + C ^ 2 / (S * G) ^ 2 := by
  have h1 : S ^ 2 / (S * G) ^ 2 = 1 / G ^ 2 := by
    rw [mul_pow]
    field_simp
  rw [← h1, ← add_div, show S ^ 2 + C ^ 2 = 1 by linarith]

/-- Let $(h_{ij})$ be scalars, $\beta \in \mathbb{K}$ and $m \in \mathbb{N}$, with
$\gamma_{m+1} \neq 0$. Then
$$\frac{1}{|\gamma_{m+1}|^2} = \frac{1}{|\gamma_m|^2} + \frac{1}{(|\gamma_{m+1}| / |c_m|)^2},$$
that is, $1/(\rho^Q_{m+1})^2 = 1/(\rho^Q_m)^2 + 1/(\rho^F_{m+1})^2$. This is (7.23) of
[saad2003iterative], and the Givens form of (6.65).

If $c_m = 0$, the last term is $0$ by the convention $t / 0 = 0$. The proof is
$|c_m|^2 + |s_m|^2 = 1$ together with $\gamma_{m+1} = -s_m \gamma_m$ (`Krylov.gamma_succ`). -/
theorem inv_sq_norm_gamma (β : 𝕜) {m : ℕ} (h0 : gamma h β (m + 1) ≠ 0) :
    1 / ‖gamma h β (m + 1)‖ ^ 2 =
      1 / ‖gamma h β m‖ ^ 2 + 1 / (‖gamma h β (m + 1)‖ / ‖givensC h m‖) ^ 2 := by
  have hsucc := gamma_succ h β m
  have hs : givensS h m ≠ 0 := fun hc => by rw [hsucc, hc] at h0; simp at h0
  have hγ : gamma h β m ≠ 0 := fun hc => by rw [hsucc, hc] at h0; simp at h0
  have hρ : givensRho h m ≠ 0 := fun hc => hs (by rw [givensS, hc]; simp)
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m hρ
  have hs0 : ‖givensS h m‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hγ0 : ‖gamma h β m‖ ≠ 0 := norm_ne_zero_iff.mpr hγ
  have hns : ‖gamma h β (m + 1)‖ = ‖givensS h m‖ * ‖gamma h β m‖ := by
    rw [hsucc, norm_mul, norm_neg]
  have hkey : 1 / ((‖givensS h m‖ * ‖gamma h β m‖) / ‖givensC h m‖) ^ 2 =
      ‖givensC h m‖ ^ 2 / (‖givensS h m‖ * ‖gamma h β m‖) ^ 2 := by
    rw [div_pow, one_div_div]
  rw [hns, hkey]
  exact inv_sq_harmonic hs0 hγ0 hcs

/-- Let $(h_{ij})$ be scalars and $\beta \in \mathbb{K}$, and let $\rho^F_0, \rho^F_1, \dots$ be the
real numbers with $\rho^F_0 = |\beta|$ and $\rho^F_{k+1} = |\gamma_{k+1}| / |c_k|$. If
$\gamma_m \neq 0$, then
$$\frac{1}{|\gamma_m|^2} = \sum_{i=0}^{m} \frac{1}{(\rho^F_i)^2}.$$
So the quasi-residual norm is a harmonic average of the Galerkin norms. This is (7.24) of
[saad2003iterative], and the Givens form of Corollary 6.14.

A term with $c_{i-1} = 0$ is $0$, by the convention $t / 0 = 0$. -/
theorem inv_sq_norm_gamma_eq_sum (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) {m : ℕ}
    (h0 : gamma h β m ≠ 0) :
    1 / ‖gamma h β m‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), 1 / ρF i ^ 2 := by
  induction m with
  | zero => simp [hρF0, gamma]
  | succ n ih =>
      have hn : gamma h β n ≠ 0 := fun hc => by rw [gamma_succ h β n, hc] at h0; simp at h0
      rw [Finset.sum_range_succ, ← ih hn, hρF n, inv_sq_norm_gamma h β h0]

/-- The numbers $\rho^F_i$ of `Krylov.inv_sq_norm_gamma_eq_sum` are nonnegative. -/
private theorem rhoF_nonneg (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) (i : ℕ) : 0 ≤ ρF i := by
  cases i with
  | zero => rw [hρF0]; exact norm_nonneg _
  | succ n => rw [hρF n]; positivity

/-- Let $(h_{ij})$ be scalars and $\beta \in \mathbb{K}$, and let $\rho^F_0 = |\beta|$ and
$\rho^F_{k+1} = |\gamma_{k+1}| / |c_k|$. Let $i \le m$, with $\gamma_m \neq 0$ and
$\rho^F_i \neq 0$. Then
$$|\gamma_m| \le \rho^F_i.$$
This is the first half of Proposition 7.5 of [saad2003iterative]: the quasi-residual norm is at
most the Galerkin norm at every step $i \le m$ where the Galerkin iterate exists.

For $i \ge 1$ and $\gamma_m \neq 0$, the hypothesis $\rho^F_i \neq 0$ says that
$c_{i-1} \neq 0$. -/
theorem norm_gamma_le (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) {m i : ℕ} (hi : i ≤ m)
    (h0 : gamma h β m ≠ 0) (hρi : ρF i ≠ 0) : ‖gamma h β m‖ ≤ ρF i := by
  have hsum := inv_sq_norm_gamma_eq_sum h β hρF0 hρF h0
  have hpos : 0 < ‖gamma h β m‖ := norm_pos_iff.mpr h0
  have hipos : 0 < ρF i := lt_of_le_of_ne (rhoF_nonneg h β hρF0 hρF i) (Ne.symm hρi)
  have hle : 1 / ρF i ^ 2 ≤ ∑ j ∈ Finset.range (m + 1), 1 / ρF j ^ 2 :=
    Finset.single_le_sum (f := fun j => 1 / ρF j ^ 2) (fun j _ => by positivity)
      (Finset.mem_range.mpr (by omega))
  rw [← hsum] at hle
  have h1 : ‖gamma h β m‖ ^ 2 ≤ ρF i ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ρF i ^ 2)
      (by positivity : (0 : ℝ) < ‖gamma h β m‖ ^ 2)] at hle
    linarith
  nlinarith

/-- Let $(h_{ij})$ be scalars and $\beta \in \mathbb{K}$, and let $\rho^F_0 = |\beta|$ and
$\rho^F_{k+1} = |\gamma_{k+1}| / |c_k|$, with $t / 0 = 0$. Then for every $m \in \mathbb{N}$
there is an $i \le m$ with
$$\rho^F_i \le \sqrt{m+1} \, |\gamma_m|,$$
that is, $\min_{i \le m} \rho^F_i \le \sqrt{m+1} \, \rho^Q_m$. This is Proposition 7.5 of
[saad2003iterative], the analogue of Proposition 6.15.

The statement has no hypothesis: if $\gamma_m = 0$, then $i = m$ works. Otherwise the result
follows from `Krylov.inv_sq_norm_gamma_eq_sum`, because a sum of $m + 1$ terms is at most
$m + 1$ times its largest term. -/
theorem exists_norm_gamma_div_givensC_le (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) (m : ℕ) :
    ∃ i ≤ m, ρF i ≤ Real.sqrt (m + 1) * ‖gamma h β m‖ := by
  rcases eq_or_ne (gamma h β m) 0 with h0 | h0
  · refine ⟨m, le_rfl, ?_⟩
    have hρm : ρF m = 0 := by
      cases m with
      | zero => rw [hρF0, show β = 0 from h0, norm_zero]
      | succ n => rw [hρF n, h0, norm_zero, zero_div]
    rw [hρm, h0, norm_zero, mul_zero]
  exact Real.exists_le_sqrt_mul_of_one_div_sq_eq_sum (norm_pos_iff.mpr h0)
    (inv_sq_norm_gamma_eq_sum h β hρF0 hρF h0)

end Harmonic

/-! ### Quasi-minimal residual smoothing -/

section Smoothing

variable (h : ℕ → ℕ → 𝕜)

/-- If $H_{m+1} w = \beta e_1$, then the rotated matrix $\tilde R_{m+1}$ maps $w$ to the truncated
rotated right-hand side $(g_0, \dots, g_{m-1}, \gamma_m)$. -/
private theorem rotated_mulVec_of_mulVec_eq
    (hh : Matrix.IsUpperHessenberg (n := ℕ) h) (β : 𝕜) {m : ℕ}
    {w : Fin (m + 1) → 𝕜} (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (i : Fin (m + 1)) :
    (hessenbergSqOf (rotated h m) (m + 1)).mulVec w i = gvecTrunc h β m (i : ℕ) := by
  have hd' : ∀ l : Fin (m + 2), (l : ℕ) ≠ m + 1 →
      (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec w) l = 0 := fun l hl => by
    rw [firstVec_sub_mulVec_apply_of_mulVec_eq h hh β hw, ite_eq_right hl]
  have hsub : (hessenbergOf h (m + 1)).mulVec w =
      firstVec β (m + 2) - (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec w) :=
    (sub_sub_cancel _ _).symm
  rw [hessenbergSqOf_rotated_mulVec h w i, hsub, Matrix.mulVec_sub, Pi.sub_apply,
    givensQAux_mulVec_firstVec h β (m + 1) m (by omega), givensQAux_mulVec_of_last h _ hd' i,
    sub_zero]
  rfl

/-- The coordinate form of (7.29) of [saad2003iterative]: the quasi-minimal-residual coordinates at
step $m + 1$ are $|s_m|^2$ times the coordinates at step $m$, padded with a zero, plus $|c_m|^2$
times the Galerkin coordinates. -/
private theorem coeff_eq_combination (hh : Matrix.IsUpperHessenberg (n := ℕ) h) {m : ℕ}
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) (β : 𝕜) {y u w : Fin (m + 1) → 𝕜} {y' : Fin m → 𝕜}
    (hy : (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y =
      fun i : Fin (m + 1) => gvec h β (i : ℕ))
    (hy' : (hessenbergSqOf (rotated h m) m).mulVec y' = fun i : Fin m => gvec h β (i : ℕ))
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (huc : ∀ j : Fin m, u j.castSucc = y' j) (hul : u (Fin.last m) = 0) :
    y = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • u + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • w := by
  have hρm : givensRho h m ≠ 0 := hρ m (by omega)
  have hρm' : ((givensRho h m : ℝ) : 𝕜) ≠ 0 := by
    simpa using hρm
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m hρm
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  -- the padded step-`m` coordinates
  have hRu : ∀ i : Fin (m + 1), (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec u i =
      if (i : ℕ) < m then gvec h β (i : ℕ) else 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc, hul, mul_zero, add_zero]
    by_cases hi : (i : ℕ) < m
    · rw [ite_eq_left hi, ← congrFun hy' ⟨(i : ℕ), hi⟩]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Fin.val_castSucc, huc j, rotated_succ_eq_of_lt h hh m (j : ℕ) j.isLt (i : ℕ)]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have him : (i : ℕ) = m := by omega
      rw [Fin.val_castSucc, him,
        rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
  -- the Galerkin coordinates
  have hRw : ∀ i : Fin (m + 1), (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec w i =
      if (i : ℕ) < m then gvec h β (i : ℕ)
      else ((givensRho h m : ℝ) : 𝕜) * w (Fin.last m) := by
    intro i
    by_cases hi : (i : ℕ) < m
    · rw [ite_eq_left hi, ← gvecTrunc_of_lt h β hi, ← rotated_mulVec_of_mulVec_eq h hh β hw i]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
    · have him : (i : ℕ) = m := by omega
      rw [ite_eq_right hi]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      rw [Fin.sum_univ_castSucc]
      have hzero : ∀ j : Fin m, rotated h (m + 1) (i : ℕ) (j.castSucc : ℕ) * w j.castSucc = 0 :=
        fun j => by
          rw [Fin.val_castSucc, him,
            rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
      rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, zero_add, him,
        Fin.val_last, rotated_succ_self]
  -- the last rotated equation
  have hlast : ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) * (((givensRho h m : ℝ) : 𝕜) * w (Fin.last m)) =
      gvec h β m := by
    have hgam : rotated h m m m * w (Fin.last m) = gamma h β m :=
      rotated_self_mul_eq_gamma h hh β hw
    have hc : givensC h m * ((givensRho h m : ℝ) : 𝕜) = rotated h m m m := by
      rw [givensC, div_mul_cancel₀ _ hρm']
    have hconj : ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) =
        starRingEnd 𝕜 (givensC h m) * givensC h m := by
      rw [RCLike.conj_mul]
      push_cast
      ring
    rw [gvec, ← hgam, ← hc, hconj]
    ring
  refine Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_hessenbergSqOf_rotated_self h hh hρ) ?_
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hy]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hRu i, hRw i]
  by_cases hi : (i : ℕ) < m
  · rw [ite_eq_left hi, ite_eq_left hi, ← add_mul, had, one_mul]
  · have him : (i : ℕ) = m := by omega
    rw [ite_eq_right hi, ite_eq_right hi, mul_zero, zero_add, hlast, him]

variable {h}

namespace IsQuasiMinResidualIterate

variable {A : E →ₗ[𝕜] E} {z v : ℕ → E} {b x₀ x x' xF : E} {β : 𝕜} {m : ℕ}

/-- Let $(h_{ij})$ be upper Hessenberg with $\rho_k \neq 0$ for all $k \le m$, let $z$ be a sequence
in $E$, and let $\beta \in \mathbb{K}$ and $x_0 \in E$. Let $x$ and $x'$ be
quasi-minimal-residual iterates at the steps $m + 1$ and $m$. Let $w \in \mathbb{K}^{m+1}$ solve
the Galerkin system $H_{m+1} w = \beta e_1$, and let $x^F = x_0 + \sum_{j \le m} w_j z_j$. Then
$$x = |s_m|^2 \, x' + |c_m|^2 \, x^F.$$
This is (7.29) of [saad2003iterative] and (6.58): the quasi-minimal-residual iterate at step
$m + 1$ is a combination of the one at step $m$ and the Galerkin iterate at step $m + 1$. This
identity lets QMR be implemented as quasi-minimal residual smoothing of BCG.

The statement uses neither the operator nor a residual basis. Here $H_{m+1}$ is
`Krylov.hessenbergSqOf h (m + 1)`. -/
theorem eq_combination (hh : Matrix.IsUpperHessenberg (n := ℕ) h)
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) {w : Fin (m + 1) → 𝕜}
    (hx : IsQuasiMinResidualIterate z h β x₀ (m + 1) x)
    (hx' : IsQuasiMinResidualIterate z h β x₀ m x')
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (hxF : xF = x₀ + ∑ j, w j • z j) :
    x = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • x' + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • xF := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hx'
  have hρ' : ∀ k < m, givensRho h k ≠ 0 := fun k hk => hρ k (by omega)
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m (hρ m (by omega))
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  obtain ⟨u, huc, hul⟩ : ∃ u : Fin (m + 1) → 𝕜,
      (∀ j : Fin m, u j.castSucc = y' j) ∧ u (Fin.last m) = 0 :=
    ⟨Fin.snoc y' 0, fun j => by simp, by simp⟩
  have hcomb := coeff_eq_combination h hh hρ β
    ((quasiResidual_isMinOn_iff h hh hρ β y).mp hy)
    ((quasiResidual_isMinOn_iff h hh hρ' β y').mp hy') hw huc hul
  have hsum : ∑ j, u j • z (j : ℕ) = ∑ j, y' j • z (j : ℕ) := by
    rw [Fin.sum_univ_castSucc, hul, zero_smul, add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [huc j, Fin.val_castSucc]
  have hx0 : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • x₀ + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • x₀ = x₀ := by
    rw [← add_smul, had, one_smul]
  rw [hxF, hcomb]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, hsum, smul_add]
  conv_lhs => rw [← hx0]
  module

/-- Under the hypotheses of `Krylov.IsQuasiMinResidualIterate.eq_combination`, for every linear
operator $A$ and every $b \in E$,
$$b - A x = |s_m|^2 \, (b - A x') + |c_m|^2 \, (b - A x^F),$$
that is, $r^Q_{m+1} = |s_m|^2 r^Q_m + |c_m|^2 r^F_{m+1}$. This is (7.30) of [saad2003iterative]
and (6.58). -/
theorem residual_eq_combination (hh : Matrix.IsUpperHessenberg (n := ℕ) h)
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) {w : Fin (m + 1) → 𝕜}
    (hx : IsQuasiMinResidualIterate z h β x₀ (m + 1) x)
    (hx' : IsQuasiMinResidualIterate z h β x₀ m x')
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (hxF : xF = x₀ + ∑ j, w j • z j) :
    b - A x = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • (b - A x') +
      ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • (b - A xF) := by
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m (hρ m (by omega))
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  have hb : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • b + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • b = b := by
    rw [← add_smul, had, one_smul]
  rw [eq_combination hh hρ hx hx' hw hxF, map_add, map_smul, map_smul, smul_sub, smul_sub]
  conv_lhs => rw [← hb]
  module

end IsQuasiMinResidualIterate

end Smoothing

end Krylov
