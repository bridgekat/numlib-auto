/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Numlib.Analysis.PDE.Heat.SineSeries
import Numlib.FiniteDifference.Derivative
import Numlib.FiniteDifference.TwoLevel
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.AtkinsonHan.Chapter06.Section02

/-!
# Atkinson and Han, Section 6.3: Two-level difference schemes

This module formalizes Section 6.3 of [han2009theoretical]. The section studies the two-level
recursion (6.3.4)–(6.3.5),
$$v^{m+1} = Q v^m + h_t g^m, \qquad v^0 = u^0,$$
whose exact values $u^m$ satisfy the same recursion with an extra local truncation error
$h_t \tau^m$ (6.3.6). Definition 6.3.1 defines consistency, order, stability and convergence of a
family of such schemes as the mesh parameters $h_x$ and $h_t$ tend to $0$. Theorem 6.3.2 says that a
consistent and stable family converges, and that a stable family of order $(p_1, p_2)$ has error
$O(h_x^{p_1} + h_t^{p_2})$. The general results specialize `FiniteDifference.norm_sub_le_of_stable`
of `Numlib.FiniteDifference.TwoLevel`.

Examples 6.3.3 and 6.3.4 apply the theorem to the forward and the backward scheme for the heat
equation $u_t = \nu u_{xx} + f$ on $(0, \pi) \times (0, T)$ with homogeneous Dirichlet boundary
values. For an exact solution with $u_{tt}$ and $u_{xxxx}$ continuous on $[0, \pi] \times [0, T]$,
both schemes have error at most $c (h_x^2 + h_t)$ in the maximum norm and in the weighted discrete
norm $\|v\|_{2, h_x} = \sqrt{h_x} \|v\|_2$: the forward scheme for $r = \nu h_t / h_x^2 \le 1/2$,
the backward scheme for every $r$. The stability bounds use the eigenvalues of tridiagonal Toeplitz
matrices (Exercise 6.3.1) from `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, and the truncation
errors use Taylor bounds.

## Main definitions

* Definition 6.3.1, `AtkinsonHan.Chapter06.IsConsistentScheme`: the largest truncation error
  $\sup_{m h_t \le T} \|\tau^m\|$ tends to $0$ as the mesh is refined.
* Definition 6.3.1 and (6.3.7), `AtkinsonHan.Chapter06.IsSchemeOfOrder`:
  $\|\tau^m\| \le c (h_x^{p_1} + h_t^{p_2})$ for every mesh.
* Definition 6.3.1, `AtkinsonHan.Chapter06.IsStableScheme`: $\|Q^m\| \le M_0$ for $m h_t \le T$,
  with $M_0$ independent of the mesh.
* Definition 6.3.1, `AtkinsonHan.Chapter06.IsConvergentScheme`: the largest error
  $\sup_{m h_t \le T} \|u^m - v^m\|$ tends to $0$ as the mesh is refined.
* Examples 6.3.3 and 6.3.4, `AtkinsonHan.Chapter06.IsRegularHeatSolution`: a solution of the heat
  equation with bounded $u_{tt}$ and $u_{xxxx}$ on the closed rectangle, with its derivatives.
* Examples 6.3.3 and 6.3.4, `AtkinsonHan.Chapter06.gridValues`: the values $u^m_j = u(x_j, t_m)$ of
  a function on the interior grid points.

## Main results

* Theorem 6.3.2, `AtkinsonHan.Chapter06.theorem_6_3_2`: a consistent and stable family of two-level
  schemes is convergent.
* Theorem 6.3.2, `AtkinsonHan.Chapter06.theorem_6_3_2'`: a stable family of order $(p_1, p_2)$ has
  error at most $M_0 T c (h_x^{p_1} + h_t^{p_2})$.
* Example 6.3.3, `AtkinsonHan.Chapter06.example_6_3_3`: for $r \le 1/2$ the forward scheme has
  maximum-norm error at most $(M_{tt}/2 + \nu M_{xxxx}/12) T (h_x^2 + h_t)$.
* Example 6.3.3, `AtkinsonHan.Chapter06.example_6_3_3_l2`: the same bound, times $\sqrt{\pi}$, in
  the weighted discrete $2$-norm.
* Example 6.3.4, `AtkinsonHan.Chapter06.example_6_3_4`: for every $r$ the backward scheme has
  maximum-norm error at most $(M_{tt}/2 + \nu M_{xxxx}/12) T (h_x^2 + h_t)$.
* Example 6.3.4, `AtkinsonHan.Chapter06.example_6_3_4_l2`: the same bound, times $\sqrt{\pi}$, in
  the weighted discrete $2$-norm.
* Examples 6.3.3 and 6.3.4, `AtkinsonHan.Chapter06.sineSeries_isRegularHeatSolution`: the
  sine-series solutions (6.2.7) of Example 6.2.4 have the assumed regularity.
* Examples 6.3.3 and 6.3.4, `AtkinsonHan.Chapter06.example_6_3_3_sineSeries` and
  `AtkinsonHan.Chapter06.example_6_3_4_sineSeries`: the two error bounds for the sine-series
  solutions.
* Exercise 6.3.1, `AtkinsonHan.Chapter06.exercise_6_3_1`: the $N \times N$ tridiagonal Toeplitz
  matrix with diagonal $a$, subdiagonal $b$ and superdiagonal $c$, $bc \ge 0$, has the eigenvalues
  $a + 2\sqrt{bc} \cos(j\pi/(N + 1))$, $1 \le j \le N$.

## Conventions

* A family of schemes is indexed by a type `ι`, and "as $h_x, h_t \to 0$" is a limit along a filter
  `l` on `ι`.
* The book's $N_x - 1$ interior grid points $x_1, \dots, x_{N_x - 1}$ are indexed by `Fin (N + 1)`
  from $0$, so $N_x = N + 2$, $h_x = \pi / (N + 2)$ and $x_j = (j + 1) h_x$. The time step is
  $h_t = T / N_t$ and $t_m = m h_t$.
* The scheme matrices are `Matrix.symmTridiagonalToeplitz (N + 1) a b`, the matrix
  $\operatorname{tridiag}(a, b, a)$ with $b$ on the diagonal. The maximum norm is the norm of
  `Fin (N + 1) → ℝ`.

## Implementation notes

* The truncation error $\tau^m$ is data of the statements, defined by the relation (6.3.6) that the
  exact values satisfy.
* The regularity of the exact solution that Examples 6.3.3 and 6.3.4 assume is the structure
  `AtkinsonHan.Chapter06.IsRegularHeatSolution`. It carries the derivatives of $u$ in $x$ up to
  order four and in $t$ up to order two, one-sided at the edges, with the bounds $M_{tt}$ and
  $M_{xxxx}$. The error bounds hold at the time levels $m \le N_t$, because the solution is assumed
  regular only on $[0, T]$.
* The backward scheme $Q_1 v^{m+1} = v^m + h_t f^{m+1}$ is the two-level scheme with $Q = Q_1^{-1}$
  and $g^m = Q f^{m+1}$.

## Deviations from the source

* **Definition 6.3.1 and Theorem 6.3.2** (generalization). The source works in
  $\mathbb{R}^{N_x - 1}$ with a norm chosen per example. The library states them for an arbitrary
  real normed space. See `AtkinsonHan.Chapter06.theorem_6_3_2`.
* **Definition 6.3.1** (reading). The limit "as $h_x, h_t \to 0$" is a limit along a filter on the
  index set of the family. See `AtkinsonHan.Chapter06.IsConsistentScheme`.

## Not formalized

* **Exercise 6.3.2** (the Crank–Nicolson scheme).
* **Exercise 6.3.3** (the generalized midpoint scheme).
-/

open Filter Set
open scoped Real

namespace AtkinsonHan.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- **Definition 6.3.1** of [han2009theoretical], consistency. Let $E$ be a real normed space and
let a family of two-level schemes be indexed by $i \in \iota$, with time steps $h_t(i)$ and
truncation errors $\tau_i^m \in E$, refined along a filter $l$ on $\iota$. The family is
**consistent** on $[0, T]$ if for every $\varepsilon > 0$, eventually along $l$,
$\|\tau_i^m\| \le \varepsilon$ for all $m \in \mathbb{N}$ with $m h_t(i) \le T$. That is,
$\sup_{m h_t \le T} \|\tau^m\| \to 0$ as the mesh is refined. -/
def IsConsistentScheme (l : Filter ι) (ht : ι → ℝ) (τ : ι → ℕ → E) (T : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ ε

/-- **Definition 6.3.1** of [han2009theoretical], order, with (6.3.7). A family of two-level schemes
with mesh parameters $h_x(i)$, $h_t(i)$ and truncation errors $\tau_i^m$ is **of order**
$(p_1, p_2)$ with constant $c$ on $[0, T]$ if
$$\|\tau_i^m\| \le c \bigl(h_x(i)^{p_1} + h_t(i)^{p_2}\bigr)$$
for every $i$ and every $m \in \mathbb{N}$ with $m h_t(i) \le T$.

A family of some order is consistent as soon as $h_x^{p_1} + h_t^{p_2} \to 0$ along the
refinement. -/
def IsSchemeOfOrder (hx ht : ι → ℝ) (τ : ι → ℕ → E) (T c : ℝ) (p₁ p₂ : ℕ) : Prop :=
  ∀ (i : ι) (m : ℕ), (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ c * (hx i ^ p₁ + ht i ^ p₂)

/-- **Definition 6.3.1** of [han2009theoretical], stability. A family of two-level schemes with
iteration operators $Q_i \in \mathcal{L}(E)$ is **stable** on $[0, T]$ with constant $M_0$ if
$\|Q_i^m\| \le M_0$ for every $i$ and every $m \in \mathbb{N}$ with $m h_t(i) \le T$. The single
constant $M_0$ for all indices expresses that the bound does not depend on the mesh. -/
def IsStableScheme (ht : ι → ℝ) (Q : ι → E →L[ℝ] E) (T M₀ : ℝ) : Prop :=
  ∀ (i : ι) (m : ℕ), (m : ℝ) * ht i ≤ T → ‖Q i ^ m‖ ≤ M₀

/-- **Definition 6.3.1** of [han2009theoretical], convergence. A family with exact values $u_i^m$
and computed values $v_i^m$ is **convergent** on $[0, T]$ along the filter $l$ if for every
$\varepsilon > 0$, eventually along $l$, $\|u_i^m - v_i^m\| \le \varepsilon$ for all
$m \in \mathbb{N}$ with $m h_t(i) \le T$. That is, $\sup_{m h_t \le T} \|u^m - v^m\| \to 0$ as
the mesh is refined. -/
def IsConvergentScheme (l : Filter ι) (ht : ι → ℝ) (u v : ι → ℕ → E) (T : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖u i m - v i m‖ ≤ ε

section Theorem632

variable {ht hx : ι → ℝ} {Q : ι → E →L[ℝ] E} {u v g τ : ι → ℕ → E} {T M₀ : ℝ}

/-- At one mesh $i$ of a stable family, if $\|\tau_i^m\| \le \delta$ whenever $m h_t(i) \le T$, then
$\|u_i^m - v_i^m\| \le M_0 T \delta$ for every $m$ with $m h_t(i) \le T$. -/
private theorem error_le (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀) (i : ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (hτ : ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ δ) {m : ℕ} (hm : (m : ℝ) * ht i ≤ T) :
    ‖u i m - v i m‖ ≤ M₀ * T * δ := by
  have hle : ∀ k : ℕ, k ≤ m → (k : ℝ) * ht i ≤ T := fun k hk =>
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hht i)) hm
  exact FiniteDifference.norm_sub_le_of_stable (hht i) hδ hm (fun k _ => hv i k)
    (fun k _ => hu i k) (h0 i) (fun k hk => hstab i k (hle k hk))
    (fun k hk => hτ k (hle k hk.le)) le_rfl

/-- **Theorem 6.3.2** of [han2009theoretical], convergence. Let $E$ be a real normed space,
$T \ge 0$, and let a family of two-level schemes have time steps $h_t(i) \ge 0$, iteration
operators $Q_i$, data $g_i^m$ and truncation errors $\tau_i^m$. Let the computed values satisfy
$v_i^{m+1} = Q_i v_i^m + h_t(i) g_i^m$, let the exact values satisfy $u_i^{m+1} = Q_i u_i^m +
h_t(i) g_i^m + h_t(i) \tau_i^m$, and let $u_i^0 = v_i^0$. If the family is stable with constant
$M_0$ and consistent along a filter $l$, then it is convergent along $l$.

The proof bounds the error at each mesh by $\sup_{m h_t \le T} \|u^m - v^m\| \le M_0 T \sup_{m
h_t \le T} \|\tau^m\|$, by `FiniteDifference.norm_sub_le_of_stable`. -/
theorem theorem_6_3_2 {l : Filter ι} (hT : 0 ≤ T) (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀)
    (hcons : IsConsistentScheme l ht τ T) :
    IsConvergentScheme l ht u v T := by
  intro ε hε
  have hM : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hMT : (0 : ℝ) ≤ max M₀ 0 * T := mul_nonneg hM hT
  have hden : (0 : ℝ) < max M₀ 0 * T + 1 := by linarith
  have hδpos : (0 : ℝ) < ε / (max M₀ 0 * T + 1) := div_pos hε hden
  filter_upwards [hcons _ hδpos] with i hi
  intro m hm
  calc ‖u i m - v i m‖ ≤ M₀ * T * (ε / (max M₀ 0 * T + 1)) :=
        error_le hht hv hu h0 hstab i hδpos.le hi hm
    _ ≤ max M₀ 0 * T * (ε / (max M₀ 0 * T + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hT) hδpos.le
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hden]
        nlinarith [hε.le]

/-- **Theorem 6.3.2** of [han2009theoretical], the error estimate. Under the recursions of
`AtkinsonHan.Chapter06.theorem_6_3_2`, with $T \ge 0$ and $h_t(i) \ge 0$, let the family be
stable with constant $M_0$ and of order $(p_1, p_2)$ with constant $c$. Then for every mesh $i$
and every $m$ with $m h_t(i) \le T$,
$$\|u_i^m - v_i^m\| \le M_0 T c \bigl(h_x(i)^{p_1} + h_t(i)^{p_2}\bigr).$$

Consistency is not a separate hypothesis: the order condition (6.3.7) implies it once the mesh
is refined. -/
theorem theorem_6_3_2' (hT : 0 ≤ T) (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀) {c : ℝ} {p₁ p₂ : ℕ}
    (hord : IsSchemeOfOrder hx ht τ T c p₁ p₂) (i : ι) {m : ℕ} (hm : (m : ℝ) * ht i ≤ T) :
    ‖u i m - v i m‖ ≤ M₀ * T * (c * (hx i ^ p₁ + ht i ^ p₂)) := by
  have hδ0 : 0 ≤ c * (hx i ^ p₁ + ht i ^ p₂) :=
    le_trans (norm_nonneg _) (hord i 0 (by simpa using hT))
  exact error_le hht hv hu h0 hstab i hδ0 (fun k hk => hord i k hk) hm

end Theorem632

section Toeplitz

/-- **Exercise 6.3.1** of [han2009theoretical]. Let $N \in \mathbb{N}$ and $a, b, c \in \mathbb{R}$
with $bc \ge 0$. Let $Q$ be the $N \times N$ tridiagonal Toeplitz matrix with $a$ on the
diagonal, $b$ on the subdiagonal and $c$ on the superdiagonal. Then $\mu \in \mathbb{R}$ is an
eigenvalue of $Q$ if and only if
$$\mu = a + 2\sqrt{bc} \cos\frac{j\pi}{N + 1} \qquad \text{for some } 1 \le j \le N.$$

The index $j$ is `j : Fin N`, so the $j$ of the source is `j + 1`. The matrix is
`Matrix.tridiagonalToeplitz N b a c`, whose arguments are in the order (subdiagonal, diagonal,
superdiagonal), while the source lists them as (diagonal, subdiagonal, superdiagonal). The proof
is `Matrix.tridiagonalToeplitz_hasEigenvalue_iff`. Examples 6.3.3 and 6.3.4 use the symmetric
case $b = c$ to read the stability of the heat equation schemes off the eigenvalues. -/
theorem exercise_6_3_1 (N : ℕ) (a b c : ℝ) (hbc : 0 ≤ b * c) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (Matrix.tridiagonalToeplitz N b a c)) μ ↔
      ∃ j : Fin N, μ = a + 2 * Real.sqrt (b * c)
        * Real.cos ((((j : ℕ) : ℝ) + 1) * π / ((N : ℝ) + 1)) :=
  Matrix.tridiagonalToeplitz_hasEigenvalue_iff N b a c hbc μ

end Toeplitz

/-! ### Examples 6.3.3 and 6.3.4: the forward and backward schemes for the heat equation -/

section HeatSchemes

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The regularity assumed in Examples 6.3.3 and 6.3.4 of [han2009theoretical]. Let
$\nu, T, M_{tt}, M_{xxxx} \in \mathbb{R}$ and $f, u : \mathbb{R}^2 \to \mathbb{R}$. The function
$u$ is a **regular solution** of the heat equation $u_t = \nu u_{xx} + f$ on
$[0, \pi] \times [0, T]$, with spatial derivatives $u_x^{(m)}$ for $m \le 4$ and time
derivatives $u_t^{(m)}$ for $m \le 2$, if the following hold.

1. $u_x^{(0)} = u_t^{(0)} = u$.
2. On the closed rectangle, $u_x^{(m+1)}$ is the derivative in $x$ of $u_x^{(m)}$ within
   $[0, \pi]$ for $m < 4$, and $u_t^{(m+1)}$ is the derivative in $t$ of $u_t^{(m)}$ within
   $[0, T]$ for $m < 2$.
3. $|u_t^{(2)}| \le M_{tt}$ and $|u_x^{(4)}| \le M_{xxxx}$ on the closed rectangle.
4. $u_t^{(1)} = \nu u_x^{(2)} + f$ on the closed rectangle.
5. $u(0, t) = u(\pi, t) = 0$ for $t \in [0, T]$.

The source assumes $u_{tt}$ and $u_{xxxx}$ continuous on the closed rectangle. The derivatives
within the closed intervals are one-sided at the edges, and the two bounds are the constants
that the error bounds depend on. The equation is asked for on the closed rectangle, which
continuity of the derivatives gives from the open one. -/
structure IsRegularHeatSolution (ν T : ℝ) (f u : ℝ × ℝ → ℝ) (ux ut : ℕ → ℝ × ℝ → ℝ)
    (Mtt Mxxxx : ℝ) : Prop where
  /-- The derivative of order $0$ in $x$ is $u$. -/
  ux_zero : ux 0 = u
  /-- The derivative of order $0$ in $t$ is $u$. -/
  ut_zero : ut 0 = u
  /-- For $m < 4$, $u_x^{(m+1)}(x, t)$ is the derivative of $y \mapsto u_x^{(m)}(y, t)$ at $x$
  within $[0, \pi]$, for all $(x, t) \in [0, \pi] \times [0, T]$. -/
  hasDerivWithinAt_ux : ∀ m < 4, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) π,
    HasDerivWithinAt (fun y => ux m (y, t)) (ux (m + 1) (x, t)) (Icc 0 π) x
  /-- For $m < 2$, $u_t^{(m+1)}(x, t)$ is the derivative of $s \mapsto u_t^{(m)}(x, s)$ at $t$
  within $[0, T]$, for all $(x, t) \in [0, \pi] \times [0, T]$. -/
  hasDerivWithinAt_ut : ∀ m < 2, ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt (fun s => ut m (x, s)) (ut (m + 1) (x, t)) (Icc 0 T) t
  /-- The bound $|u_{tt}| \le M_{tt}$ on $[0, \pi] \times [0, T]$. -/
  abs_ut_two_le : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, |ut 2 (x, t)| ≤ Mtt
  /-- The bound $|u_{xxxx}| \le M_{xxxx}$ on $[0, \pi] \times [0, T]$. -/
  abs_ux_four_le : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, |ux 4 (x, t)| ≤ Mxxxx
  /-- The heat equation $u_t = \nu u_{xx} + f$ on $[0, \pi] \times [0, T]$. -/
  equation : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, ut 1 (x, t) = ν * ux 2 (x, t) + f (x, t)
  /-- The boundary value $u(0, t) = 0$ for $t \in [0, T]$. -/
  left : ∀ t ∈ Icc (0 : ℝ) T, u (0, t) = 0
  /-- The boundary value $u(\pi, t) = 0$ for $t \in [0, T]$. -/
  right : ∀ t ∈ Icc (0 : ℝ) T, u (π, t) = 0

variable {ν T : ℝ} {f u : ℝ × ℝ → ℝ} {ux ut : ℕ → ℝ × ℝ → ℝ} {Mtt Mxxxx : ℝ}

namespace IsRegularHeatSolution

variable (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
include hu

/-- The forward Taylor bound in time for a regular solution of the heat equation. For
$x \in [0, \pi]$, $t \in [0, T]$, $k \ge 0$ and $t + k \le T$,
$$|u(x, t + k) - u(x, t) - k \, u_t(x, t)| \le M_{tt} k^2 / 2.$$
-/
theorem abs_sub_forward_time_le {x t k : ℝ} (hx : x ∈ Icc (0 : ℝ) π) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : 0 ≤ k) (htk : t + k ≤ T) :
    |u (x, t + k) - u (x, t) - k * ut 1 (x, t)| ≤ Mtt * k ^ 2 / 2 := by
  have hsub : Icc t (t + k) ⊆ Icc 0 T := Icc_subset_Icc ht.1 htk
  have h := norm_sub_sub_smul_le_mul_sq_div_two (y := fun s => u (x, s))
    (y' := fun s => ut 1 (x, s)) (y'' := fun s => ut 2 (x, s)) (M := Mtt) (by linarith)
    (fun s hs => by
      have := hu.hasDerivWithinAt_ut 0 (by norm_num) x hx s (hsub hs)
      rw [hu.ut_zero] at this
      exact this.mono hsub)
    (fun s hs => (hu.hasDerivWithinAt_ut 1 (by norm_num) x hx s (hsub hs)).mono hsub)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hu.abs_ut_two_le x hx s (hsub hs))
  simpa [smul_eq_mul, Real.norm_eq_abs] using h

/-- The backward Taylor bound in time for a regular solution of the heat equation. For
$x \in [0, \pi]$, $t \in [0, T]$, $k \ge 0$ and $t + k \le T$,
$$|u(x, t + k) - u(x, t) - k \, u_t(x, t + k)| \le M_{tt} k^2 / 2.$$
-/
theorem abs_sub_backward_time_le {x t k : ℝ} (hx : x ∈ Icc (0 : ℝ) π) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : 0 ≤ k) (htk : t + k ≤ T) :
    |u (x, t + k) - u (x, t) - k * ut 1 (x, t + k)| ≤ Mtt * k ^ 2 / 2 := by
  have hsub : Icc t (t + k) ⊆ Icc 0 T := Icc_subset_Icc ht.1 htk
  have h := norm_sub_sub_smul_le_mul_sq_div_two' (y := fun s => u (x, s))
    (y' := fun s => ut 1 (x, s)) (y'' := fun s => ut 2 (x, s)) (M := Mtt) (by linarith)
    (fun s hs => by
      have := hu.hasDerivWithinAt_ut 0 (by norm_num) x hx s (hsub hs)
      rw [hu.ut_zero] at this
      exact this.mono hsub)
    (fun s hs => (hu.hasDerivWithinAt_ut 1 (by norm_num) x hx s (hsub hs)).mono hsub)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hu.abs_ut_two_le x hx s (hsub hs))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  have e : u (x, t + k) - u (x, t) - k * ut 1 (x, t + k)
      = -(u (x, t) - u (x, t + k) - (t - (t + k)) * ut 1 (x, t + k)) := by ring
  rw [e, abs_neg]
  exact h

/-- The Taylor bound for the centred second difference in space, for a regular solution of the heat
equation. For $h \ge 0$, $x - h, x + h \in [0, \pi]$ and $t \in [0, T]$,
$$|u(x + h, t) - 2u(x, t) + u(x - h, t) - h^2 u_{xx}(x, t)| \le M_{xxxx} h^4 / 12.$$
-/
theorem abs_centred_sub_le {x t h : ℝ} (hxl : x - h ∈ Icc (0 : ℝ) π) (hxr : x + h ∈ Icc (0 : ℝ) π)
    (hh : 0 ≤ h) (ht : t ∈ Icc (0 : ℝ) T) :
    |u (x + h, t) - 2 * u (x, t) + u (x - h, t) - h ^ 2 * ux 2 (x, t)| ≤ Mxxxx * h ^ 4 / 12 := by
  simpa only [hu.ux_zero] using
    FiniteDifference.abs_secondDiff_sub_le (y := fun m y => ux m (y, t))
    (fun m hm s hs => hu.hasDerivWithinAt_ux m hm t ht s hs)
    (fun s hs => hu.abs_ux_four_le s hs t ht) hxl hxr hh

end IsRegularHeatSolution

/-! ### The grid and the two matrices -/

/-- The values of a function $u$ of $(x, t)$ on the interior grid at time level $m$: the vector
$u^m \in \mathbb{R}^{N+1}$ with $u^m_j = u(x_j, t_m)$, $x_j = (j + 1) h_x$ and $t_m = m h_t$,
used in Examples 6.3.3 and 6.3.4.

The index is `j : Fin (N + 1)`, from $0$. So the interior points $x_1, \dots, x_{N_x - 1}$ of
the source are indexed from $0$, and $N_x = N + 2$. -/
def gridValues (N : ℕ) (u : ℝ × ℝ → ℝ) (hx ht : ℝ) (m : ℕ) : Fin (N + 1) → ℝ :=
  fun j => u (((j : ℕ) + 1) * hx, m * ht)

/-- The entry $j$ of the grid vector $u^m$ is $u((j + 1) h_x, m h_t)$. -/
theorem gridValues_apply (N : ℕ) (u : ℝ × ℝ → ℝ) (hx ht : ℝ) (m : ℕ) (j : Fin (N + 1)) :
    gridValues N u hx ht m j = u (((j : ℕ) + 1) * hx, m * ht) := rfl

/-- If $h_x = \pi / (N + 2)$ and $u$ vanishes at $x = 0$ and $x = \pi$ at time $t_m$, then row $i$
of $\operatorname{tridiag}(a, b, a) \, u^m$ is $a u(x_i - h_x, t_m) + b u(x_i, t_m) + a u(x_i +
h_x, t_m)$. -/
private theorem symmTridiagonalToeplitz_mulVec_gridValues {N : ℕ} {u : ℝ × ℝ → ℝ} {hx ht : ℝ}
    (hhx : hx = π / (N + 2)) (a b : ℝ) (m : ℕ) (h0 : u (0, m * ht) = 0) (hπ : u (π, m * ht) = 0)
    (i : Fin (N + 1)) :
    (symmTridiagonalToeplitz (N + 1) a b *ᵥ gridValues N u hx ht m) i
      = a * u ((i : ℕ) * hx, m * ht) + b * u (((i : ℕ) + 1) * hx, m * ht)
        + a * u (((i : ℕ) + 2) * hx, m * ht) := by
  have hN2 : ((N : ℝ) + 2) ≠ 0 := by positivity
  rw [symmTridiagonalToeplitz_mulVec_apply']
  congr 1
  · congr 1
    split_ifs with hi
    · rw [gridValues_apply]
      congr 3
      push_cast [Nat.cast_sub hi]
      ring
    · have : (i : ℕ) = 0 := by omega
      rw [this, Nat.cast_zero, zero_mul, h0, mul_zero]
  · split_ifs with hi
    · rw [gridValues_apply]
      push_cast
      ring_nf
    · have : (i : ℕ) = N := by omega
      rw [this, show ((N : ℝ) + 2) * hx = π by rw [hhx]; field_simp, hπ, mul_zero]

/-- A matrix as a bounded operator on $\mathbb{R}^{N+1}$ with the maximum norm. -/
private noncomputable def toLinfty {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

private theorem toLinfty_apply {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) : toLinfty A v = A *ᵥ v := by
  rw [toLinfty, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]

/-- The Euclidean norm of $v \in \mathbb{R}^{N+1}$ with $|v_j| \le \delta$ for all $j$ is at most
$\sqrt{N + 1} \, \delta$. -/
private theorem norm_toLp_le {N : ℕ} (v : Fin (N + 1) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ j, |v j| ≤ δ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (N + 1)))‖ ≤ Real.sqrt ((N : ℝ) + 1) * δ := by
  refine (PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top v).trans ?_
  rw [PiLp.norm_toLp, Fintype.card_fin, Nat.cast_add_one]
  exact mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hδ).2 fun j =>
    (Real.norm_eq_abs _).trans_le (hv j)) (Real.sqrt_nonneg _)

/-! ### The forward scheme, Example 6.3.3 -/

section Forward

variable {N Nt : ℕ} {hx ht r : ℝ} (hν : 0 < ν) (hT : 0 < T) (hNt : 0 < Nt)
  (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)

/-- The local truncation error $\tau^m$ of the forward scheme, defined by (6.3.6) as
$(u^{m+1} - Q u^m - h_t f^m) / h_t$. -/
private noncomputable def forwardTrunc (N : ℕ) (u f : ℝ × ℝ → ℝ) (hx ht r : ℝ) (m : ℕ) :
    Fin (N + 1) → ℝ :=
  ht⁻¹ • (gridValues N u hx ht (m + 1) - symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ
    gridValues N u hx ht m - ht • gridValues N f hx ht m)

include hT hNt hht in
private theorem gridValues_succ_forward (u f : ℝ × ℝ → ℝ) (m : ℕ) :
    gridValues N u hx ht (m + 1)
      = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ gridValues N u hx ht m
        + ht • gridValues N f hx ht m + ht • forwardTrunc N u f hx ht r m := by
  have hht0 : ht ≠ 0 := by rw [hht]; positivity
  rw [forwardTrunc, smul_smul, mul_inv_cancel₀ hht0, one_smul]
  abel

include hν hT hNt hhx hht hr in
/-- The truncation error of the forward scheme in Example 6.3.3 satisfies $|\tau^m_j| \le
(M_{tt}/2 + \nu M_{xxxx}/12)(h_x^2 + h_t)$ for every time level $m < N_t$. -/
private theorem abs_forwardTrunc_le (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
    {m : ℕ} (hm : m < Nt) (j : Fin (N + 1)) :
    |forwardTrunc N u f hx ht r m j| ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  -- the grid point and the two time levels
  set x : ℝ := ((j : ℕ) + 1) * hx with hxdef
  set t : ℝ := m * ht with htdef
  have hxmem : x ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have hxl : x - hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by rw [hxdef]; nlinarith, by linarith [hxmem.2]⟩
  have hxr : x + hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by linarith [hxmem.1], ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 2 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 2 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) + π / (N + 2) = ((j : ℕ) + 2) * (π / (N + 2)) := by ring
      _ ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have htmem : t ∈ Icc (0 : ℝ) T := by
    refine ⟨by positivity, ?_⟩
    rw [htdef, hht]
    have : (m : ℝ) ≤ Nt := by exact_mod_cast hm.le
    calc (m : ℝ) * (T / Nt) ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have htk : t + ht ≤ T := by
    rw [htdef, hht]
    have : (m : ℝ) + 1 ≤ Nt := by exact_mod_cast hm
    calc (m : ℝ) * (T / Nt) + T / Nt = ((m : ℝ) + 1) * (T / Nt) := by ring
      _ ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  -- the boundary values at the two levels
  have hb0 : u (0, m * ht) = 0 := hu.left _ htmem
  have hbπ : u (π, m * ht) = 0 := hu.right _ htmem
  -- the identity `h_t τ = A - r B`
  have hrow := symmTridiagonalToeplitz_mulVec_gridValues (u := u) (ht := ht) hhx r (1 - 2 * r) m
    hb0 hbπ j
  have hτ : ht * forwardTrunc N u f hx ht r m j
      = (u (x, t + ht) - u (x, t) - ht * ut 1 (x, t))
        - r * (u (x + hx, t) - 2 * u (x, t) + u (x - hx, t) - hx ^ 2 * ux 2 (x, t)) := by
    have heq := hu.equation x hxmem t htmem
    have hrhx : r * hx ^ 2 = ν * ht := by
      rw [hr, div_mul_cancel₀ _ (pow_ne_zero 2 hhx0.ne')]
    simp only [forwardTrunc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hrow, gridValues_apply]
    rw [mul_inv_cancel_left₀ hht0.ne', heq]
    have e1 : (((j : ℕ) : ℝ) + 1) * hx = x := rfl
    have e2 : (((m + 1 : ℕ) : ℝ)) * ht = t + ht := by push_cast; ring
    have e3 : ((j : ℕ) : ℝ) * hx = x - hx := by rw [hxdef]; ring
    have e4 : (((j : ℕ) : ℝ) + 2) * hx = x + hx := by rw [hxdef]; ring
    rw [e1, e2, e3, e4]
    linear_combination (-(ux 2 (x, t))) * hrhx
  have hA := hu.abs_sub_forward_time_le hxmem htmem hht0.le htk
  have hB := hu.abs_centred_sub_le hxl hxr hhx0.le htmem
  have hbound : |ht * forwardTrunc N u f hx ht r m j|
      ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
    rw [hτ]
    have hrhx4 : r * hx ^ 4 = ν * ht * hx ^ 2 := by
      rw [hr]; field_simp
    calc |u (x, t + ht) - u (x, t) - ht * ut 1 (x, t)
          - r * (u (x + hx, t) - 2 * u (x, t) + u (x - hx, t) - hx ^ 2 * ux 2 (x, t))|
        ≤ Mtt * ht ^ 2 / 2 + r * (Mxxxx * hx ^ 4 / 12) := by
          refine (abs_sub _ _).trans (add_le_add hA ?_)
          rw [abs_mul, abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_left hB hr0
      _ = ht * (Mtt / 2 * ht + ν * Mxxxx / 12 * hx ^ 2) := by
          rw [show r * (Mxxxx * hx ^ 4 / 12) = (r * hx ^ 4) * Mxxxx / 12 by ring, hrhx4]; ring
      _ ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
          refine mul_le_mul_of_nonneg_left ?_ hht0.le
          nlinarith [mul_nonneg hMtt (sq_nonneg hx), mul_nonneg (mul_nonneg hν.le hMx) hht0.le]
  rw [abs_mul, abs_of_pos hht0] at hbound
  exact le_of_mul_le_mul_left hbound hht0

/-- **Example 6.3.3** of [han2009theoretical], the maximum norm. Let $\nu > 0$, $T > 0$,
$N, N_t \in \mathbb{N}$ with $N_t > 0$, $h_x = \pi / (N + 2)$, $h_t = T / N_t$ and
$r = \nu h_t / h_x^2 \le 1/2$. Let $u$ be a regular solution of $u_t = \nu u_{xx} + f$
(`AtkinsonHan.Chapter06.IsRegularHeatSolution`) with bounds $M_{tt}$ and $M_{xxxx}$. Let
$v^0 = u^0$ and let $v$ follow the forward scheme (6.1.8)–(6.1.10),
$$v^{m+1} = Q v^m + h_t f^m, \qquad Q = \operatorname{tridiag}(r, 1 - 2r, r).$$
Then for every time level $m \le N_t$,
$$\max_j |u(x_j, t_m) - v^m_j| \le \Bigl(\frac{M_{tt}}{2} + \frac{\nu M_{xxxx}}{12}\Bigr) T
  (h_x^2 + h_t).$$

This is the order-$(2, 1)$ estimate of Theorem 6.3.2. For $r \le 1/2$, $\|Q\|_\infty \le 1$, so
the scheme is stable with $M_0 = 1$, and Taylor expansion bounds the truncation error. The proof
applies `FiniteDifference.norm_sub_le_of_stable` with the horizon cut at $N_t$, because $u$ is
assumed regular only on $[0, T]$. -/
theorem example_6_3_3 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2) (hr2 : r ≤ 1 / 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N f hx ht m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N u hx ht m - v m‖ ≤ (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q := toLinfty (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r)) with hQ
  -- stability: `‖Q‖_∞ ≤ 1`
  have hQ1 : ‖Q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hQ, toLinfty_apply]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine (abs_symmTridiagonalToeplitz_mulVec_apply_le _ _ _ _).trans ?_
    rw [abs_of_nonneg hr0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * r),
      show 2 * r + (1 - 2 * r) = 1 by ring, one_mul]
  have hδ : 0 ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q) (u := gridValues N u hx ht) (v := v)
    (g := gridValues N f hx ht) (τ := forwardTrunc N u f hx ht r) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by rw [hv k, hQ, toLinfty_apply])
    (fun k _ => by rw [gridValues_succ_forward hT hNt hht u f k, hQ, toLinfty_apply])
    hv0.symm (fun k _ => ContinuousLinearMap.norm_pow_le_one hQ1 k)
    (fun k hk => (pi_norm_le_iff_of_nonneg hδ).2 fun j => by
      rw [Real.norm_eq_abs]
      exact abs_forwardTrunc_le hν hT hNt hhx hht hr hu hk j) hm
  calc ‖gridValues N u hx ht m - v m‖ ≤ 1 * T * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := h
    _ = (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by ring

/-- For $0 \le r \le 1/2$, the eigenvalues $1 - 2r + 2r \cos\theta_k$ of
$\operatorname{tridiag}(r, 1 - 2r, r)$ lie in $[-1, 1]$, which gives $\|Q\|_2 \le 1$ in Example
6.3.3. -/
private theorem isSymmetricBoundedBy_forward {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 1 / 2) :
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r))).IsSymmetricBoundedBy
      (-1) 1 := by
  refine isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc r (1 - 2 * r) fun k => ?_
  have h1 := Real.neg_one_le_cos ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  have h2 := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  constructor <;> nlinarith

/-- If $h_x = \pi / (N + 2)$ and $\|w\|_2 \le \sqrt{N + 1} \, C$ for $w \in \mathbb{R}^{N+1}$ and
$C \ge 0$, then $\sqrt{h_x \sum_j w_j^2} \le \sqrt{\pi} \, C$, because $h_x (N + 1) \le \pi$. -/
private theorem sqrt_mul_sum_sq_le {N : ℕ} {hx : ℝ} (hhx : hx = π / (N + 2)) (w : Fin (N + 1) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (N + 1)))‖ ≤ Real.sqrt ((N : ℝ) + 1) * C) :
    Real.sqrt (hx * ∑ j, w j ^ 2) ≤ Real.sqrt π * C := by
  have hhx0 : 0 ≤ hx := by rw [hhx]; positivity
  have hN : hx * ((N : ℝ) + 1) ≤ π := by
    rw [hhx, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [EuclideanSpace.norm_eq] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  calc Real.sqrt (hx * ∑ j, w j ^ 2) = Real.sqrt hx * Real.sqrt (∑ j, w j ^ 2) :=
        Real.sqrt_mul hhx0 _
    _ ≤ Real.sqrt hx * (Real.sqrt ((N : ℝ) + 1) * C) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = Real.sqrt (hx * ((N : ℝ) + 1)) * C := by rw [Real.sqrt_mul hhx0]; ring
    _ ≤ Real.sqrt π * C := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN) hC

/-- **Example 6.3.3** of [han2009theoretical], the weighted discrete $2$-norm. Under the hypotheses
of `AtkinsonHan.Chapter06.example_6_3_3`, for every time level $m \le N_t$,
$$\|u^m - v^m\|_{2, h_x} = \sqrt{h_x} \, \|u^m - v^m\|_2 \le \sqrt{\pi} \Bigl(\frac{M_{tt}}{2} +
  \frac{\nu M_{xxxx}}{12}\Bigr) T (h_x^2 + h_t).$$

In $\|\cdot\|_{2, h_x}$ the induced matrix norm is the spectral norm. The eigenvalues
$1 - 4r \sin^2(j\pi / (2 N_x))$ of $Q$ (Exercise 6.3.1) lie in $[-1, 1]$ for $r \le 1/2$, so
$\|Q\|_2 \le 1$ and the scheme is stable with $M_0 = 1$. The factor $\sqrt{\pi}$ bounds
$\sqrt{h_x (N_x - 1)}$, which converts the maximum-norm bound on $\tau^m$ into a bound in the
weighted $2$-norm. -/
theorem example_6_3_3_l2 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2) (hr2 : r ≤ 1 / 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N f hx ht m)
    {m : ℕ} (hm : m ≤ Nt) :
    Real.sqrt (hx * ∑ j, (gridValues N u hx ht m j - v m j) ^ 2)
      ≤ Real.sqrt π * ((Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht)) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) :=
    toEuclideanCLM (𝕜 := ℝ) (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r)) with hQ
  have hQ1 : ‖Q‖ ≤ 1 :=
    norm_toEuclideanCLM_le_of_isSymmetricBoundedBy zero_le_one
      (isSymmetricBoundedBy_forward hr0 hr2)
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have hδ : 0 ≤ Real.sqrt ((N : ℝ) + 1) * c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q)
    (u := fun k => WithLp.toLp 2 (gridValues N u hx ht k))
    (v := fun k => WithLp.toLp 2 (v k)) (g := fun k => WithLp.toLp 2 (gridValues N f hx ht k))
    (τ := fun k => WithLp.toLp 2 (forwardTrunc N u f hx ht r k)) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by rw [hv k, WithLp.toLp_add, WithLp.toLp_smul, hQ, toEuclideanCLM_toLp])
    (fun k _ => by
      rw [gridValues_succ_forward hT hNt hht u f k, WithLp.toLp_add, WithLp.toLp_add,
        WithLp.toLp_smul, WithLp.toLp_smul, hQ, toEuclideanCLM_toLp])
    (by rw [hv0]) (fun k _ => ContinuousLinearMap.norm_pow_le_one hQ1 k)
    (fun k hk => norm_toLp_le _ hc0 fun j => abs_forwardTrunc_le hν hT hNt hhx hht hr hu hk j) hm
  rw [← WithLp.toLp_sub, one_mul, ← mul_assoc] at h
  have key := sqrt_mul_sum_sq_le hhx (gridValues N u hx ht m - v m) (C := T * c) (by positivity)
    (h.trans (le_of_eq (by ring)))
  simp only [Pi.sub_apply] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]; ring

end Forward

/-! ### The backward scheme, Example 6.3.4 -/

section Backward

variable {N Nt : ℕ} {hx ht r : ℝ} (hν : 0 < ν) (hT : 0 < T) (hNt : 0 < Nt)
  (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)

/-- For $r \ge 0$, the matrix $Q_1 = \operatorname{tridiag}(-r, 1 + 2r, -r)$ of the backward scheme
is invertible. -/
private theorem isUnit_backward {r : ℝ} (hr0 : 0 ≤ r) :
    IsUnit (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r)) :=
  (posDef_symmTridiagonalToeplitz (N + 1) (by rw [abs_neg, abs_of_nonneg hr0]; linarith)).isUnit

/-- For $r \ge 0$, the eigenvalues $1 + 2r - 2r \cos\theta_k$ of $Q_1$ lie in $[1, 1 + 4r]$. -/
private theorem isSymmetricBoundedBy_backward {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) :
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))).IsSymmetricBoundedBy
      1 (1 + 4 * r) := by
  refine isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc (-r) (1 + 2 * r) fun k => ?_
  have h1 := Real.neg_one_le_cos ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  have h2 := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  constructor <;> nlinarith

/-- For $r \ge 0$, $\|Q_1^{-1} x\|_\infty \le \|x\|_\infty$ by diagonal dominance: if $Q_1 y = x$,
then $(1 + 2r) |y_i| \le |x_i| + 2r \|y\|_\infty$ at every index. -/
private theorem norm_mulVec_inv_backward_le {r : ℝ} (hr0 : 0 ≤ r) (x : Fin (N + 1) → ℝ) :
    ‖(symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ *ᵥ x‖ ≤ ‖x‖ := by
  set y := (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ *ᵥ x with hy
  have hQy : symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_backward hr0)), Matrix.one_mulVec]
  have hyi : ∀ j, |y j| ≤ ‖y‖ := fun j => (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm y j)
  have hxi : ∀ j, |x j| ≤ ‖x‖ := fun j => (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm x j)
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have key : ‖y‖ ≤ (‖x‖ + 2 * r * ‖y‖) / (1 + 2 * r) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs, le_div_iff₀ h12]
    have hrow := congrFun hQy i
    rw [symmTridiagonalToeplitz_mulVec_apply'] at hrow
    have h1 : |if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0| ≤ r * ‖y‖ := by
      split_ifs
      · rw [abs_mul, abs_neg, abs_of_nonneg hr0]
        exact mul_le_mul_of_nonneg_left (hyi _) hr0
      · rw [abs_zero]; positivity
    have h2 : |if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0| ≤ r * ‖y‖ := by
      split_ifs
      · rw [abs_mul, abs_neg, abs_of_nonneg hr0]
        exact mul_le_mul_of_nonneg_left (hyi _) hr0
      · rw [abs_zero]; positivity
    have h3 : (1 + 2 * r) * y i = x i - (if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0)
        - (if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0) := by
      linarith
    calc |y i| * (1 + 2 * r) = |(1 + 2 * r) * y i| := by
          rw [abs_mul, abs_of_pos h12, mul_comm]
      _ ≤ |x i| + |if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0|
          + |if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0| := by
          rw [h3]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ‖x‖ + r * ‖y‖ + r * ‖y‖ := add_le_add (add_le_add (hxi i) h1) h2
      _ = ‖x‖ + 2 * r * ‖y‖ := by ring
  rw [le_div_iff₀ h12] at key
  linarith

/-- For $r \ge 0$, $\|Q_1^{-1}\|_2 \le 1$, because the eigenvalues of $Q_1$ are at least $1$. -/
private theorem norm_toEuclideanCLM_inv_backward_le {r : ℝ} (hr0 : 0 ≤ r) :
    ‖toEuclideanCLM (𝕜 := ℝ) (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have hb := (isSymmetricBoundedBy_backward (N := N) hr0).isCoerciveWith.norm_le_norm_apply
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ z)
  rw [one_mul, toEuclideanLin_mul_nonsing_inv_apply (isUnit_backward hr0)] at hb
  exact hb

/-- The local truncation error $\bar\tau^m$ of the backward scheme, defined by the implicit relation
$Q_1 u^{m+1} = u^m + h_t f^{m+1} + h_t \bar\tau^m$. -/
private noncomputable def backwardTrunc (N : ℕ) (u f : ℝ × ℝ → ℝ) (hx ht r : ℝ) (m : ℕ) :
    Fin (N + 1) → ℝ :=
  ht⁻¹ • (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ gridValues N u hx ht (m + 1)
    - gridValues N u hx ht m - ht • gridValues N f hx ht (m + 1))

include hT hNt hht in
private theorem mulVec_gridValues_succ_backward (u f : ℝ × ℝ → ℝ) (m : ℕ) :
    symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ gridValues N u hx ht (m + 1)
      = gridValues N u hx ht m + ht • gridValues N f hx ht (m + 1)
        + ht • backwardTrunc N u f hx ht r m := by
  have hht0 : ht ≠ 0 := by rw [hht]; positivity
  rw [backwardTrunc, smul_smul, mul_inv_cancel₀ hht0, one_smul]
  abel

include hν hT hNt hhx hht hr in
/-- The truncation error of the backward scheme in Example 6.3.4 satisfies $|\bar\tau^m_j| \le
(M_{tt}/2 + \nu M_{xxxx}/12)(h_x^2 + h_t)$ for every time level $m < N_t$. -/
private theorem abs_backwardTrunc_le (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
    {m : ℕ} (hm : m < Nt) (j : Fin (N + 1)) :
    |backwardTrunc N u f hx ht r m j| ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set x : ℝ := ((j : ℕ) + 1) * hx with hxdef
  set t : ℝ := m * ht with htdef
  have hxmem : x ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have hxl : x - hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by rw [hxdef]; nlinarith, by linarith [hxmem.2]⟩
  have hxr : x + hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by linarith [hxmem.1], ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 2 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 2 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) + π / (N + 2) = ((j : ℕ) + 2) * (π / (N + 2)) := by ring
      _ ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have htmem : t ∈ Icc (0 : ℝ) T := by
    refine ⟨by positivity, ?_⟩
    rw [htdef, hht]
    have : (m : ℝ) ≤ Nt := by exact_mod_cast hm.le
    calc (m : ℝ) * (T / Nt) ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have htk : t + ht ≤ T := by
    rw [htdef, hht]
    have : (m : ℝ) + 1 ≤ Nt := by exact_mod_cast hm
    calc (m : ℝ) * (T / Nt) + T / Nt = ((m : ℝ) + 1) * (T / Nt) := by ring
      _ ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have ht'mem : t + ht ∈ Icc (0 : ℝ) T := ⟨by positivity, htk⟩
  have e2 : (((m + 1 : ℕ) : ℝ)) * ht = t + ht := by push_cast; ring
  -- the boundary values at the level `m + 1`
  have hb0 : u (0, ((m + 1 : ℕ) : ℝ) * ht) = 0 := by rw [e2]; exact hu.left _ ht'mem
  have hbπ : u (π, ((m + 1 : ℕ) : ℝ) * ht) = 0 := by rw [e2]; exact hu.right _ ht'mem
  have hrow := symmTridiagonalToeplitz_mulVec_gridValues (u := u) (ht := ht) hhx (-r) (1 + 2 * r)
    (m + 1) hb0 hbπ j
  -- the identity `h_t τ̄ = A - r B`, at the level `m + 1`
  have hτ : ht * backwardTrunc N u f hx ht r m j
      = (u (x, t + ht) - u (x, t) - ht * ut 1 (x, t + ht))
        - r * (u (x + hx, t + ht) - 2 * u (x, t + ht) + u (x - hx, t + ht)
          - hx ^ 2 * ux 2 (x, t + ht)) := by
    have heq := hu.equation x hxmem (t + ht) ht'mem
    have hrhx : r * hx ^ 2 = ν * ht := by
      rw [hr, div_mul_cancel₀ _ (pow_ne_zero 2 hhx0.ne')]
    simp only [backwardTrunc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hrow, gridValues_apply]
    rw [mul_inv_cancel_left₀ hht0.ne', heq]
    have e1 : (((j : ℕ) : ℝ) + 1) * hx = x := rfl
    have e3 : ((j : ℕ) : ℝ) * hx = x - hx := by rw [hxdef]; ring
    have e4 : (((j : ℕ) : ℝ) + 2) * hx = x + hx := by rw [hxdef]; ring
    rw [e1, e2, e3, e4]
    linear_combination (-(ux 2 (x, t + ht))) * hrhx
  have hA := hu.abs_sub_backward_time_le hxmem htmem hht0.le htk
  have hB := hu.abs_centred_sub_le hxl hxr hhx0.le ht'mem
  have hbound : |ht * backwardTrunc N u f hx ht r m j|
      ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
    rw [hτ]
    have hrhx4 : r * hx ^ 4 = ν * ht * hx ^ 2 := by
      rw [hr]; field_simp
    calc |u (x, t + ht) - u (x, t) - ht * ut 1 (x, t + ht)
          - r * (u (x + hx, t + ht) - 2 * u (x, t + ht) + u (x - hx, t + ht)
            - hx ^ 2 * ux 2 (x, t + ht))|
        ≤ Mtt * ht ^ 2 / 2 + r * (Mxxxx * hx ^ 4 / 12) := by
          refine (abs_sub _ _).trans (add_le_add hA ?_)
          rw [abs_mul, abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_left hB hr0
      _ = ht * (Mtt / 2 * ht + ν * Mxxxx / 12 * hx ^ 2) := by
          rw [show r * (Mxxxx * hx ^ 4 / 12) = (r * hx ^ 4) * Mxxxx / 12 by ring, hrhx4]; ring
      _ ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
          refine mul_le_mul_of_nonneg_left ?_ hht0.le
          nlinarith [mul_nonneg hMtt (sq_nonneg hx), mul_nonneg (mul_nonneg hν.le hMx) hht0.le]
  rw [abs_mul, abs_of_pos hht0] at hbound
  exact le_of_mul_le_mul_left hbound hht0

/-- **Example 6.3.4** of [han2009theoretical], the maximum norm. Let $\nu > 0$, $T > 0$,
$N, N_t \in \mathbb{N}$ with $N_t > 0$, $h_x = \pi / (N + 2)$, $h_t = T / N_t$ and
$r = \nu h_t / h_x^2$, with no condition on $r$. Let $u$ be a regular solution of
$u_t = \nu u_{xx} + f$ (`AtkinsonHan.Chapter06.IsRegularHeatSolution`) with bounds $M_{tt}$ and
$M_{xxxx}$. Let $v^0 = u^0$ and let $v$ follow the backward scheme (6.1.12)–(6.1.14),
$$Q_1 v^{m+1} = v^m + h_t f^{m+1}, \qquad Q_1 = \operatorname{tridiag}(-r, 1 + 2r, -r).$$
Then for every time level $m \le N_t$,
$$\max_j |u(x_j, t_m) - v^m_j| \le \Bigl(\frac{M_{tt}}{2} + \frac{\nu M_{xxxx}}{12}\Bigr) T
  (h_x^2 + h_t).$$

The scheme is the two-level scheme with $Q = Q_1^{-1}$ and $g^m = Q f^{m+1}$. Diagonal dominance
gives $\|Q\|_\infty \le 1$, so the scheme is unconditionally stable with $M_0 = 1$. Its
truncation error $\tau^m = Q \bar\tau^m$ satisfies
$\|\tau^m\|_\infty \le \|\bar\tau^m\|_\infty$, and Taylor expansion at $(x_j, t_{m+1})$ bounds
$\bar\tau^m$. As in `AtkinsonHan.Chapter06.example_6_3_3`, the horizon is cut at $N_t$. -/
theorem example_6_3_4 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N f hx ht (m + 1))
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N u hx ht m - v m‖ ≤ (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q₁ := symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) with hQ₁
  have hunit := isUnit_backward (N := N) hr0
  have hdet : IsUnit Q₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hinv : ∀ w : Fin (N + 1) → ℝ, Q₁⁻¹ *ᵥ (Q₁ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  set Q := toLinfty Q₁⁻¹ with hQ
  have hQ1 : ‖Q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hQ, toLinfty_apply]
    exact norm_mulVec_inv_backward_le hr0 w
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q) (u := gridValues N u hx ht) (v := v)
    (g := fun k => Q₁⁻¹ *ᵥ gridValues N f hx ht (k + 1))
    (τ := fun k => Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hc0 (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by
      rw [hQ, toLinfty_apply, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← hv k, hinv])
    (fun k _ => by
      rw [hQ, toLinfty_apply, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
        ← Matrix.mulVec_add, ← mulVec_gridValues_succ_backward hT hNt hht u f k, hinv])
    hv0.symm (fun k _ => ContinuousLinearMap.norm_pow_le_one hQ1 k)
    (fun k hk => (norm_mulVec_inv_backward_le hr0 _).trans
      ((pi_norm_le_iff_of_nonneg hc0).2 fun j => by
        rw [Real.norm_eq_abs]
        exact abs_backwardTrunc_le hν hT hNt hhx hht hr hu hk j)) hm
  calc ‖gridValues N u hx ht m - v m‖ ≤ 1 * T * c := h
    _ = (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by rw [hc]; ring

/-- **Example 6.3.4** of [han2009theoretical], the weighted discrete $2$-norm. Under the hypotheses
of `AtkinsonHan.Chapter06.example_6_3_4`, for every time level $m \le N_t$,
$$\sqrt{h_x} \, \|u^m - v^m\|_2 \le \sqrt{\pi} \Bigl(\frac{M_{tt}}{2} + \frac{\nu
  M_{xxxx}}{12}\Bigr) T (h_x^2 + h_t).$$

The eigenvalues $1 + 4r \cos^2(j\pi / (2 N_x))$ of $Q_1$ (Exercise 6.3.1) are at least $1$. So
the eigenvalues of $Q = Q_1^{-1}$ lie in $(0, 1]$, $\|Q\|_2 \le 1$, the scheme is
unconditionally stable in $\|\cdot\|_{2, h_x}$, and $\|\tau^m\|_2 \le \|\bar\tau^m\|_2$. -/
theorem example_6_3_4_l2 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N f hx ht (m + 1))
    {m : ℕ} (hm : m ≤ Nt) :
    Real.sqrt (hx * ∑ j, (gridValues N u hx ht m j - v m j) ^ 2)
      ≤ Real.sqrt π * ((Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht)) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q₁ := symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) with hQ₁
  have hunit := isUnit_backward (N := N) hr0
  have hdet : IsUnit Q₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hinv : ∀ w : Fin (N + 1) → ℝ, Q₁⁻¹ *ᵥ (Q₁ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  set Q : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) :=
    toEuclideanCLM (𝕜 := ℝ) Q₁⁻¹ with hQ
  have hQ1 : ‖Q‖ ≤ 1 := norm_toEuclideanCLM_inv_backward_le hr0
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have hδ : 0 ≤ Real.sqrt ((N : ℝ) + 1) * c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q)
    (u := fun k => WithLp.toLp 2 (gridValues N u hx ht k))
    (v := fun k => WithLp.toLp 2 (v k))
    (g := fun k => WithLp.toLp 2 (Q₁⁻¹ *ᵥ gridValues N f hx ht (k + 1)))
    (τ := fun k => WithLp.toLp 2 (Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k)) (h := ht) (T := T)
    (M₀ := 1) (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by
      rw [hQ, toEuclideanCLM_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_add, ← Matrix.mulVec_smul,
        ← Matrix.mulVec_add, ← hv k, hinv])
    (fun k _ => by
      rw [hQ, toEuclideanCLM_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add,
        ← WithLp.toLp_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
        ← Matrix.mulVec_add, ← mulVec_gridValues_succ_backward hT hNt hht u f k, hinv])
    (by rw [hv0]) (fun k _ => ContinuousLinearMap.norm_pow_le_one hQ1 k)
    (fun k hk => by
      have h1 : ‖(WithLp.toLp 2 (Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k) :
          EuclideanSpace ℝ (Fin (N + 1)))‖
          ≤ ‖(WithLp.toLp 2 (backwardTrunc N u f hx ht r k) : EuclideanSpace ℝ (Fin (N + 1)))‖ := by
        have := Q.le_opNorm (WithLp.toLp 2 (backwardTrunc N u f hx ht r k))
        rw [hQ, toEuclideanCLM_toLp] at this
        exact this.trans (by nlinarith [norm_nonneg (WithLp.toLp 2 (backwardTrunc N u f hx ht r k) :
          EuclideanSpace ℝ (Fin (N + 1)))])
      exact h1.trans (norm_toLp_le _ hc0 fun j =>
        abs_backwardTrunc_le hν hT hNt hhx hht hr hu hk j)) hm
  rw [← WithLp.toLp_sub, one_mul, ← mul_assoc] at h
  have key := sqrt_mul_sum_sq_le hhx (gridValues N u hx ht m - v m) (C := T * c) (by positivity)
    (h.trans (le_of_eq (by ring)))
  simp only [Pi.sub_apply] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]; ring

end Backward

/-! ### The sine-series solutions of Example 6.2.4 satisfy the hypotheses -/

section SineSeries

/-- The sine-series solutions have the regularity of Examples 6.3.3 and 6.3.4 of
[han2009theoretical]. Let $\nu > 0$, $T \in \mathbb{R}$, and let
$$u(x, t) = \sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t} \sin((j + 1) x)$$
be the solution (6.2.7) of Example 6.2.4. Then $u$ is a regular solution of $u_t = \nu u_{xx}$
(with $f = 0$) on $[0, \pi] \times [0, T]$, with $M_{tt} = \sum_{j < n} |b_j| (\nu (j + 1)^2)^2$
and $M_{xxxx} = \sum_{j < n} |b_j| (j + 1)^4$.

The derivatives are `Heat.sineSeriesDerivX` and `Heat.sineSeriesDerivT`. -/
theorem sineSeries_isRegularHeatSolution (hν : 0 < ν) (T : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    IsRegularHeatSolution ν T 0 (Heat.sineSeries ν n b) (Heat.sineSeriesDerivX ν n b)
      (Heat.sineSeriesDerivT ν n b) (∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2)
      (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) where
  ux_zero := Heat.sineSeriesDerivX_zero
  ut_zero := Heat.sineSeriesDerivT_zero
  hasDerivWithinAt_ux m _ t _ x _ := (Heat.hasDerivAt_sineSeriesDerivX m x t).hasDerivWithinAt
  hasDerivWithinAt_ut m _ x _ t _ := (Heat.hasDerivAt_sineSeriesDerivT m x t).hasDerivWithinAt
  abs_ut_two_le x _ t ht := Heat.abs_sineSeriesDerivT_le hν.le 2 (p := (x, t)) ht.1
  abs_ux_four_le x _ t ht := Heat.abs_sineSeriesDerivX_le hν.le 4 (p := (x, t)) ht.1
  equation x _ t _ := by rw [Heat.sineSeriesDerivT_one, Pi.zero_apply, add_zero]
  left t _ := Heat.sineSeries_zero_left t
  right t _ := Heat.sineSeries_pi_left t

/-- **Example 6.3.3** of [han2009theoretical], for the sine-series solutions of Example 6.2.4. Under
the mesh hypotheses of `AtkinsonHan.Chapter06.example_6_3_3`, with $r \le 1/2$, let $u$ be the
sine series (6.2.7) and let $v^0 = u^0$ and $v^{m+1} = \operatorname{tridiag}(r, 1 - 2r, r) \,
v^m$. Then for every $m \le N_t$, with $M_{tt} = \sum_{j < n} |b_j| (\nu (j + 1)^2)^2$ and
$M_{xxxx} = \sum_{j < n} |b_j| (j + 1)^4$,
$$\max_j |u^m_j - v^m_j| \le \Bigl(\frac{M_{tt}}{2} + \frac{\nu M_{xxxx}}{12}\Bigr) T (h_x^2 +
  h_t),$$
and the same bound times $\sqrt{\pi}$ holds for $\sqrt{h_x} \, \|u^m - v^m\|_2$.

The regularity hypotheses are discharged by
`AtkinsonHan.Chapter06.sineSeries_isRegularHeatSolution`. -/
theorem example_6_3_3_sineSeries (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt)
    {hx ht r : ℝ} (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hr2 : r ≤ 1 / 2) (n : ℕ) (b : ℕ → ℝ) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N (Heat.sineSeries ν n b) hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N (Heat.sineSeries ν n b) hx ht m - v m‖
        ≤ ((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht) ∧
      Real.sqrt (hx * ∑ j, (gridValues N (Heat.sineSeries ν n b) hx ht m j - v m j) ^ 2)
        ≤ Real.sqrt π * (((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht)) := by
  have hv' : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N (0 : ℝ × ℝ → ℝ) hx ht m := fun m => by
    have : gridValues N (0 : ℝ × ℝ → ℝ) hx ht m = 0 := by funext j; rfl
    rw [hv m, this, smul_zero, add_zero]
  exact ⟨example_6_3_3 hν hT hNt hhx hht hr hr2 (sineSeries_isRegularHeatSolution hν T n b) hv0 hv'
    hm, example_6_3_3_l2 hν hT hNt hhx hht hr hr2 (sineSeries_isRegularHeatSolution hν T n b) hv0
    hv' hm⟩

/-- **Example 6.3.4** of [han2009theoretical], for the sine-series solutions of Example 6.2.4. Under
the mesh hypotheses of `AtkinsonHan.Chapter06.example_6_3_4`, with no condition on $r$, let $u$
be the sine series (6.2.7) and let $v^0 = u^0$ and $\operatorname{tridiag}(-r, 1 + 2r, -r) \,
v^{m+1} = v^m$. Then for every $m \le N_t$, with $M_{tt} = \sum_{j < n} |b_j| (\nu (j + 1)^2)^2$
and $M_{xxxx} = \sum_{j < n} |b_j| (j + 1)^4$,
$$\max_j |u^m_j - v^m_j| \le \Bigl(\frac{M_{tt}}{2} + \frac{\nu M_{xxxx}}{12}\Bigr) T (h_x^2 +
  h_t),$$
and the same bound times $\sqrt{\pi}$ holds for $\sqrt{h_x} \, \|u^m - v^m\|_2$.

The regularity hypotheses are discharged by
`AtkinsonHan.Chapter06.sineSeries_isRegularHeatSolution`. -/
theorem example_6_3_4_sineSeries (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt)
    {hx ht r : ℝ} (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (n : ℕ) (b : ℕ → ℝ) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N (Heat.sineSeries ν n b) hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1) = v m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N (Heat.sineSeries ν n b) hx ht m - v m‖
        ≤ ((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht) ∧
      Real.sqrt (hx * ∑ j, (gridValues N (Heat.sineSeries ν n b) hx ht m j - v m j) ^ 2)
        ≤ Real.sqrt π * (((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht)) := by
  have hv' : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N (0 : ℝ × ℝ → ℝ) hx ht (m + 1) := fun m => by
    have : gridValues N (0 : ℝ × ℝ → ℝ) hx ht (m + 1) = 0 := by funext j; rfl
    rw [hv m, this, smul_zero, add_zero]
  exact ⟨example_6_3_4 hν hT hNt hhx hht hr (sineSeries_isRegularHeatSolution hν T n b) hv0 hv' hm,
    example_6_3_4_l2 hν hT hNt hhx hht hr (sineSeries_isRegularHeatSolution hν T n b) hv0 hv' hm⟩

end SineSeries

end HeatSchemes

end AtkinsonHan.Chapter06
