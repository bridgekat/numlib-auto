/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.ODE.PicardLindelof
import Numlib.IntegralEquations.Basic
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Stationary.Basic
import Numlib.Stationary.Splitting
import NumlibSurface.AtkinsonHan.Chapter05.Section01

/-!
# Atkinson and Han, Section 5.2: Applications of the fixed-point theorem to iterative methods

This module formalizes Section 5.2 of [han2009theoretical], four applications of the Banach
fixed-point theorem (Theorem 5.1.3). The first is the iteration $x_{n+1} = T(x_n)$ for a contractive
map $T$ of an interval $[a, b]$ into itself (Theorem 5.2.1). The second is the stationary iterative
methods for a linear system $Ax = b$: for a splitting $A = N - M$ with $N$ nonsingular, the
iteration $N x_n = M x_{n-1} + b$ converges from every starting point if and only if the spectral
radius of $N^{-1} M$ is less than $1$. The section also relates the spectral radius $r_\sigma(A)$ to
matrix norms: $r_\sigma(A) \le \|A\|$, $r_\sigma(A)$ is the infimum of the operator norms of $A$,
and $\|A^k\|^{1/k} \to r_\sigma(A)$. The third is the integral equations of the second kind: the
linear Fredholm equation, the nonlinear Urysohn equation (Theorem 5.2.2) and the Volterra equation
(Theorem 5.2.3). The fourth is the Picard iteration for the initial value problem $u' = f(t, u)$,
$u(t_0) = z$ (Theorem 5.2.4).

The proofs specialize the backbone modules `Numlib.Stationary.Basic`, `Numlib.Stationary.Splitting`,
`Numlib.LinearAlgebra.Matrix.Complexify`, `Numlib.LinearAlgebra.Matrix.Hessenberg`,
`Numlib.Nonlinear.FixedPoint`, `Numlib.IntegralEquations.Basic` and
`Numlib.Analysis.ODE.PicardLindelof`.

## Main definitions

* Section 5.2.2, `AtkinsonHan.Chapter05.BookSplitting`: a splitting $A = N - M$ of a square matrix
  with $N$ nonsingular, with its iteration matrix $N^{-1} M$
  (`AtkinsonHan.Chapter05.BookSplitting.iterMatrix`) and its step
  $x_n = N^{-1} M x_{n-1} + N^{-1} b$ (`AtkinsonHan.Chapter05.BookSplitting.iterStep`).
* Section 5.2.2, `AtkinsonHan.Chapter05.jacobi`, `AtkinsonHan.Chapter05.gaussSeidel` and
  `AtkinsonHan.Chapter05.sor`: the Jacobi, Gauss–Seidel and SOR splittings.
* `AtkinsonHan.Chapter05.mulVecCLM`: a square matrix as a continuous linear map of $\mathbb{R}^d$
  with the maximum norm.

## Main results

* Theorem 5.2.1, `AtkinsonHan.Chapter05.theorem_5_2_1` and
  `AtkinsonHan.Chapter05.theorem_5_2_1_deriv`: the Banach fixed-point theorem on $[a, b]$, and the
  criterion $|T'| \le \alpha < 1$ for contractivity.
* Equation (5.2.5), `AtkinsonHan.Chapter05.BookSplitting.equation_5_2_5`: the error equation
  $x - x_n = (N^{-1} M)^n (x - x_0)$.
* Section 5.2.2(b), `AtkinsonHan.Chapter05.BookSplitting.tendsto_of_opNorm_lt_one`: the iteration
  converges if $\|N^{-1} M\| < 1$.
* Section 5.2.2, relation 1, `AtkinsonHan.Chapter05.complexSpectralRadius_le_opNorm`:
  $r_\sigma(A) \le \|A\|$ for the maximum-norm operator norm.
* Section 5.2.2, relation 2, `AtkinsonHan.Chapter05.exists_opNorm_le_complexSpectralRadius_add`: for
  every $\varepsilon > 0$ there is a vector norm whose operator norm of $A$ lies in
  $[r_\sigma(A), r_\sigma(A) + \varepsilon]$.
* Section 5.2.2, relation 3, `AtkinsonHan.Chapter05.tendsto_pow_rpow_complexSpectralRadius`:
  Gelfand's formula $\|A^k\|^{1/k} \to r_\sigma(A)$.
* Section 5.2.2(c), `AtkinsonHan.Chapter05.tendsto_pow_iff_complexSpectralRadius_lt_one`:
  $G^k \to 0$ if and only if $r_\sigma(G) < 1$.
* Section 5.2.2(d), `AtkinsonHan.Chapter05.BookSplitting.forall_tendsto_iff` and
  `AtkinsonHan.Chapter05.BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one`: the
  iteration converges from every $x_0$ if and only if $(N^{-1} M)^k \to 0$, if and only if
  $r_\sigma(N^{-1} M) < 1$.
* Equation (5.2.7), `AtkinsonHan.Chapter05.equation_5_2_7`: the linear Fredholm equation of the
  second kind under the condition (5.2.8).
* Theorem 5.2.2, `AtkinsonHan.Chapter05.theorem_5_2_2`: the Urysohn equation (5.2.10) with a small
  Lipschitz constant.
* Theorem 5.2.3, `AtkinsonHan.Chapter05.theorem_5_2_3`: the Volterra equation (5.2.15), with no
  smallness condition.
* Theorem 5.2.4 (Picard–Lindelöf), `AtkinsonHan.Chapter05.theorem_5_2_4` and
  `AtkinsonHan.Chapter05.theorem_5_2_4_ode`: the Picard iteration is a contraction in a weighted
  norm, and the initial value problem has a unique continuously differentiable solution on
  $[t_0 - a_0, t_0 + a_0]$ with $a_0 = \min(a, b/M)$.

## Conventions

* The book writes a splitting as $A = N - M$ with $N$ nonsingular. The backbone
  `Stationary.Splitting` writes $a = m - n$ with $m$ invertible. So $m = N$ and $n = M$; the lemmas
  `AtkinsonHan.Chapter05.BookSplitting.toSplitting_m` and
  `AtkinsonHan.Chapter05.BookSplitting.toSplitting_n` record this.
* Vectors are elements of `ι → ℝ` with the maximum norm, and the norm of a matrix $G$ is the
  operator norm of `AtkinsonHan.Chapter05.mulVecCLM G`, the maximum absolute row sum. The spectral
  radius $r_\sigma(G)$ is computed over $\mathbb{C}$: it is `Matrix.complexSpectralRadius G`, with
  values in $[0, \infty]$, and finite.
* A function in $C[a, b]$ is integrated over $[a, b]$ through its extension to $\mathbb{R}$ by
  `Set.projIcc`.

## Implementation notes

* `AtkinsonHan.Chapter05.theorem_5_2_4_ode` is the book's Theorem 5.2.4 in the book's generality:
  values in a Banach space, a two-sided interval around $t_0$, and a right-hand side that is defined
  and Lipschitz only on the box $\{(t, u) : |t - t_0| \le a, \|u - z\| \le b\}$.
  `AtkinsonHan.Chapter05.theorem_5_2_4` is the convergence of Picard's iteration, the part whose
  proof is Bielecki's contraction argument. It is stated for a scalar equation whose right-hand side
  is Lipschitz in $u$ on all of $\mathbb{R}$, on an interval $[t_0, t_1]$ to the right of $t_0$.
* Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` does not say that the
  solution stays in the ball $\|u - z\| \le b$, which the uniqueness theorem
  `ODE_solution_unique_of_mem_Icc` needs. The backbone module `Numlib.Analysis.ODE.PicardLindelof`
  proves this containment.

## Not formalized

* The remark after Theorem 5.2.3: under its hypotheses on $[a, \infty)$, the Volterra equation has a
  unique solution in $C[a, \infty)$, whose restrictions are the solutions on each $[a, b]$. The
  backbone Volterra operator `IntegralOperator.volterra` is defined only on a compact interval, so
  the remark needs a second kernel type on $[a, \infty)$. The fact that the solution on $[a, b']$
  restricts to the solution on $[a, b]$ follows from the uniqueness part of
  `AtkinsonHan.Chapter05.theorem_5_2_3` on $[a, b]$.
-/

open Filter Set Topology
open scoped Matrix

namespace AtkinsonHan.Chapter05

section Scalar

variable {a b α : ℝ} {T : ℝ → ℝ}

/-- On $\mathbb{R}$, $T$ is contractive on $K$ with constant $\alpha$ (Definition 5.1.2) if and only
if $0 \le \alpha < 1$ and $|T(u) - T(v)| \le \alpha |u - v|$ for all $u, v \in K$. This is the
form in which the book writes Theorem 5.2.1. -/
theorem contractiveOn_real_iff {K : Set ℝ} :
    ContractiveOn T K α ↔ 0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, |T u - T v| ≤ α * |u - v| := by
  simp only [ContractiveOn, Real.norm_eq_abs]

/-- **Theorem 5.2.1** of [han2009theoretical], the Banach fixed-point theorem on an interval. Let
$a \le b$, and let $T : \mathbb{R} \to \mathbb{R}$ map $[a, b]$ into $[a, b]$ and be contractive
on $[a, b]$ with constant $\alpha$. Then:

1. $T$ has a unique fixed point $u \in [a, b]$;
2. for every $u_0 \in [a, b]$, the iterates $u_n = T^n(u_0)$ converge to this fixed point $u$,
   and for every $n \ge 0$,
$$|u_n - u| \le \frac{\alpha^n}{1 - \alpha} |u_0 - u_1|, \qquad |u_{n+1} - u| \le
  \frac{\alpha}{1 - \alpha} |u_n - u_{n+1}|, \qquad |u_{n+1} - u| \le \alpha |u_n - u|.$$
-/
theorem theorem_5_2_1 (hab : a ≤ b) (hT : MapsTo T (Icc a b) (Icc a b))
    (hα : ContractiveOn T (Icc a b) α) :
    (∃! u, u ∈ Icc a b ∧ T u = u) ∧
      ∀ u₀ ∈ Icc a b, ∃ u ∈ Icc a b, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) :=
  theorem_5_1_3 isClosed_Icc (nonempty_Icc.2 hab) hT hα

/-- **Theorem 5.2.1** of [han2009theoretical], the derivative criterion. Let $0 \le \alpha < 1$, and
let $T : \mathbb{R} \to \mathbb{R}$ have the derivative $T'(x)$ within $[a, b]$ at every
$x \in [a, b]$, with $|T'(x)| \le \alpha$ there. Then $T$ is contractive on $[a, b]$ with
constant $\alpha$.

This is the scalar case of the backbone theorem `lipschitzOnWith_of_hasFDerivWithinAt`, that is,
of Mathlib's `Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`. -/
theorem theorem_5_2_1_deriv {T' : ℝ → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (T' x) (Icc a b) x)
    (hbound : ∀ x ∈ Icc a b, |T' x| ≤ α) : ContractiveOn T (Icc a b) α :=
  (contractiveOn_iff hα0).2
    ⟨hα1, (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hT hbound⟩

end Scalar

section Splittings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A square matrix $G$ as a continuous linear map $x \mapsto Gx$ of `ι → ℝ` to itself. The space
`ι → ℝ` has the maximum norm, and the backbone iteration `Stationary.step` acts in this normed
space. -/
noncomputable def mulVecCLM (G : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin G)

omit [DecidableEq ι] in
/-- The map `AtkinsonHan.Chapter05.mulVecCLM G` sends $x$ to $Gx$. -/
@[simp]
theorem mulVecCLM_apply (G : Matrix ι ι ℝ) (x : ι → ℝ) : mulVecCLM G x = G *ᵥ x := rfl

/-- The $k$-th power of `AtkinsonHan.Chapter05.mulVecCLM G` sends $x$ to $G^k x$. -/
theorem mulVecCLM_pow (G : Matrix ι ι ℝ) (k : ℕ) :
    ∀ x : ι → ℝ, (mulVecCLM G ^ k) x = G ^ k *ᵥ x := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ]
    change (mulVecCLM G ^ k) (mulVecCLM G x) = (G ^ k * G) *ᵥ x
    rw [mulVecCLM_apply, ih, Matrix.mulVec_mulVec]

omit [DecidableEq ι] in
/-- The operator norm satisfies $\|G^k\| \le \|G\|^k$. -/
private theorem norm_mulVecCLM_pow_le (G : Matrix ι ι ℝ) (k : ℕ) :
    ‖mulVecCLM G ^ k‖ ≤ ‖mulVecCLM G‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- $G^k \to 0$ if and only if $G^k v \to 0$ for every vector $v$. -/
private theorem tendsto_pow_zero_iff_mulVec (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔
      ∀ v : ι → ℝ, Tendsto (fun k => G ^ k *ᵥ v) atTop (𝓝 0) := by
  constructor
  · intro h v
    have hc : Continuous fun M : Matrix ι ι ℝ => M *ᵥ v :=
      continuous_id.matrix_mulVec continuous_const
    have hcomp := (hc.tendsto 0).comp h
    simpa [Function.comp_def] using hcomp
  · intro h
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hj := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
    simpa using hj

/-- **Section 5.2.2** of [han2009theoretical], splittings. A **splitting** of a square matrix $A$
consists of square matrices $N$ and $M$ with $A = N - M$ and $N$ nonsingular. -/
structure BookSplitting (A : Matrix ι ι ℝ) where
  /-- The nonsingular part $N$ of the splitting. -/
  N : Matrix ι ι ℝ
  /-- The second part $M$ of the splitting. -/
  M : Matrix ι ι ℝ
  /-- The splitting identity $A = N - M$. -/
  eq : A = N - M
  /-- The matrix $N$ is nonsingular. -/
  isUnit : IsUnit N

namespace BookSplitting

variable {A : Matrix ι ι ℝ} (s : BookSplitting A)

/-- The **iteration matrix** $N^{-1} M$ of the splitting $A = N - M$. -/
noncomputable def iterMatrix : Matrix ι ι ℝ := s.N⁻¹ * s.M

/-- One step of the iteration $N x_n = M x_{n-1} + b$ of the splitting, that is,
$x_n = N^{-1} M x_{n-1} + N^{-1} b$. -/
noncomputable def iterStep (b x : ι → ℝ) : ι → ℝ := s.iterMatrix *ᵥ x + s.N⁻¹ *ᵥ b

/-- The backbone splitting `Stationary.Splitting` that corresponds to the splitting $A = N - M$. The
backbone writes $a = m - n$ with $m$ invertible, so $m = N$ and $n = M$. -/
def toSplitting : Stationary.Splitting A := ⟨s.N, s.isUnit⟩

/-- The invertible part $m$ of the backbone splitting is the book's $N$. -/
@[simp]
theorem toSplitting_m : s.toSplitting.m = s.N := rfl

/-- The second part $n$ of the backbone splitting is the book's $M$. -/
theorem toSplitting_n : s.toSplitting.n = s.M := by
  have h : s.toSplitting.n = s.N - A := rfl
  have h2 : s.N - A = s.N - (s.N - s.M) := by rw [← s.eq]
  rw [h, h2, sub_sub_cancel]

/-- The iteration operator of the backbone splitting is the book's iteration matrix $N^{-1} M$. -/
theorem toSplitting_iterationOperator : s.toSplitting.iterationOperator = s.iterMatrix := by
  rw [Stationary.Splitting.iterationOperator_eq, toSplitting_n, toSplitting_m, iterMatrix,
    Matrix.nonsing_inv_eq_ringInverse]

/-- The book's iteration step $x \mapsto N^{-1} M x + N^{-1} b$ is the backbone's affine step
`Stationary.step` with the linear part $N^{-1} M$ and the constant part $N^{-1} b$. -/
theorem iterStep_eq_stationary_step (b : ι → ℝ) :
    s.iterStep b = Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) := rfl

/-- If $Ax = b$, then $x$ is a fixed point of the iteration: $N^{-1} M x + N^{-1} b = x$. -/
theorem step_fixed {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    mulVecCLM s.iterMatrix x + s.N⁻¹ *ᵥ b = x := by
  have hdet : IsUnit s.N.det := (Matrix.isUnit_iff_isUnit_det _).mp s.isUnit
  have hkey : s.N⁻¹ * (s.N - s.M) = 1 - s.iterMatrix := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hdet, iterMatrix]
  have hb : s.N⁻¹ *ᵥ b = x - s.iterMatrix *ᵥ x := by
    have h1 : s.N⁻¹ *ᵥ b = s.N⁻¹ *ᵥ ((s.N - s.M) *ᵥ x) := by rw [← hx, ← s.eq]
    rw [h1, Matrix.mulVec_mulVec, hkey, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [hb]

/-- **Equation (5.2.5)** of [han2009theoretical], the error equation. Let $A = N - M$ be a
splitting, let $Ax = b$, let $x_0$ be a vector, and let $x_n$ be the iterates of
$N x_n = M x_{n-1} + b$ from $x_0$. Then for every $n \ge 0$,
$$x - x_n = (N^{-1} M)^n (x - x_0).$$
-/
theorem equation_5_2_5 {x b : ι → ℝ} (hx : A *ᵥ x = b) (x₀ : ι → ℝ) (k : ℕ) :
    x - (s.iterStep b)^[k] x₀ = s.iterMatrix ^ k *ᵥ (x - x₀) := by
  have h := Stationary.step_iterate_sub (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) (s.step_fixed hx)
    x₀ k
  rw [mulVecCLM_pow] at h
  rw [← neg_sub ((s.iterStep b)^[k] x₀) x, iterStep_eq_stationary_step, h, Matrix.mulVec_sub,
    Matrix.mulVec_sub]
  abel

/-- **Section 5.2.2(b)** of [han2009theoretical]. Let $A = N - M$ be a splitting, and let the
iteration matrix satisfy $\|N^{-1} M\| < 1$ in the operator norm of the maximum norm. Let
$Ax = b$. Then for every $x_0$ the iterates of $N x_n = M x_{n-1} + b$ converge to $x$.

The proof specializes the backbone theorem `Stationary.norm_iterate_sub_le`. -/
theorem tendsto_of_opNorm_lt_one (hG : ‖mulVecCLM s.iterMatrix‖ < 1) {x b : ι → ℝ}
    (hx : A *ᵥ x = b) (x₀ : ι → ℝ) :
    Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => Stationary.norm_iterate_sub_le _ _ hG (s.step_fixed hx) x₀ k) ?_)
  have h1 : Tendsto (fun k : ℕ => ‖mulVecCLM s.iterMatrix‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG
  simpa using (h1.div_const (1 - ‖mulVecCLM s.iterMatrix‖)).mul_const
    ‖Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) x₀ - x₀‖

/-- **Section 5.2.2(d)** of [han2009theoretical]. Let $A = N - M$ be a splitting, and let $Ax = b$.
Then the iterates of $N x_n = M x_{n-1} + b$ converge to $x$ from every starting point $x_0$ if
and only if $(N^{-1} M)^k \to 0$ as $k \to \infty$. -/
theorem forall_tendsto_iff {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Tendsto (fun k => s.iterMatrix ^ k) atTop (𝓝 0) := by
  rw [tendsto_pow_zero_iff_mulVec]
  constructor
  · intro h v
    have hv := (h (x - v)).const_sub x
    rw [sub_self] at hv
    have heq : (fun k => x - (s.iterStep b)^[k] (x - v)) = fun k => s.iterMatrix ^ k *ᵥ v := by
      funext k
      simpa using s.equation_5_2_5 hx (x - v) k
    rwa [heq] at hv
  · intro h x₀
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have heq : (fun k => ‖(s.iterStep b)^[k] x₀ - x‖)
        = fun k => ‖s.iterMatrix ^ k *ᵥ (x - x₀)‖ := by
      funext k
      rw [← norm_neg, neg_sub, s.equation_5_2_5 hx x₀]
    rw [heq]
    simpa using (h (x - x₀)).norm

end BookSplitting

/-- **Section 5.2.2(c)** of [han2009theoretical]. For a real square matrix $G$, $G^k \to 0$ as
$k \to \infty$ if and only if $r_\sigma(G) < 1$, where $r_\sigma(G)$ is the spectral radius
computed over $\mathbb{C}$.

This is the backbone theorem `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔ Matrix.complexSpectralRadius G < 1 :=
  Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one G

/-- **Section 5.2.2(c) and (d)** of [han2009theoretical], the classical criterion. Let $A = N - M$
be a splitting, and let $Ax = b$. Then the iterates of $N x_n = M x_{n-1} + b$ converge to $x$
from every starting point $x_0$ if and only if $r_\sigma(N^{-1} M) < 1$. -/
theorem BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one {A : Matrix ι ι ℝ}
    (s : BookSplitting A) {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Matrix.complexSpectralRadius s.iterMatrix < 1 :=
  (s.forall_tendsto_iff hx).trans
    (Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one s.iterMatrix)

omit [DecidableEq ι] in
/-- **Section 5.2.2** of [han2009theoretical], relation 1, in the form in which the book uses it. If
a real square matrix $G$ satisfies $\|G\| < 1$ in the operator norm of the maximum norm, then
$r_\sigma(G) < 1$.

The inequality $r_\sigma(G) \le \|G\|$ itself is
`AtkinsonHan.Chapter05.complexSpectralRadius_le_opNorm`. This proof uses
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` instead, which needs no matrix norm. -/
theorem complexSpectralRadius_lt_one_of_opNorm_lt_one {G : Matrix ι ι ℝ}
    (hG : ‖mulVecCLM G‖ < 1) : Matrix.complexSpectralRadius G < 1 := by
  classical
  rw [← Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one, tendsto_pow_zero_iff_mulVec]
  intro v
  have hb : ∀ k : ℕ, ‖G ^ k *ᵥ v‖ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ := fun k =>
    calc ‖G ^ k *ᵥ v‖ = ‖(mulVecCLM G ^ k) v‖ := by rw [mulVecCLM_pow]
      _ ≤ ‖mulVecCLM G ^ k‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_mulVecCLM_pow_le G k) (norm_nonneg _)
  have hlim : Tendsto (fun k : ℕ => ‖mulVecCLM G‖ ^ k * ‖v‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG).mul_const ‖v‖
  exact squeeze_zero_norm hb hlim

open scoped Matrix.Norms.Operator in
omit [DecidableEq ι] in
/-- **Section 5.2.2** of [han2009theoretical], relation 1. For every real square matrix $G$,
$$r_\sigma(G) \le \|G\|,$$
where $\|G\|$ is the operator norm induced by the maximum norm on $\mathbb{R}^d$, that is, the
maximum absolute row sum.

The operator norm is `‖AtkinsonHan.Chapter05.mulVecCLM G‖`, which equals Mathlib's $\ell^\infty$
operator norm of the matrix by `Matrix.linfty_opNorm_eq_opNorm`. The backbone proves the
inequality for every submultiplicative, absolutely homogeneous, positive definite matrix norm
(`Matrix.complexSpectralRadius_le_of_norm`); the case used here is
`Matrix.complexSpectralRadius_le_linfty_opNNNorm`. The spectral radius has values in
$[0, \infty]$ and is finite for a matrix over a finite index type
(`Matrix.complexSpectralRadius_ne_top`), so its conversion to a real number loses nothing. -/
theorem complexSpectralRadius_le_opNorm (G : Matrix ι ι ℝ) :
    (Matrix.complexSpectralRadius G).toReal ≤ ‖mulVecCLM G‖ := by
  classical
  exact
    calc (Matrix.complexSpectralRadius G).toReal
        ≤ ((‖G‖₊ : ENNReal)).toReal :=
          ENNReal.toReal_mono ENNReal.coe_ne_top (Matrix.complexSpectralRadius_le_linfty_opNNNorm G)
      _ = ‖G‖ := by simp
      _ = ‖mulVecCLM G‖ := Matrix.linfty_opNorm_eq_opNorm G

omit [DecidableEq ι] in
/-- **Section 5.2.2** of [han2009theoretical], relation 2 (the $\varepsilon$-norm theorem). Let $A$
be a real square matrix and $\varepsilon > 0$. Then there is a seminorm $p$ on $\mathbb{R}^d$
such that

1. $\|x\|_\infty \le p(x)$ for all $x$;
2. $p(x) \le C \|x\|_\infty$ for all $x$, for some constant $C$;
3. $p(Ax) \le (r_\sigma(A) + \varepsilon) \, p(x)$ for all $x$;
4. if $c \ge 0$ and $p(Ax) \le c \, p(x)$ for all $x$, then $r_\sigma(A) \le c$.

Parts 1 and 2 say that $p$ is a norm equivalent to the maximum norm. The operator norm $\|A\|_p$
of $A$ induced by $p$ is the least $c \ge 0$ with $p(Ax) \le c \, p(x)$ for all $x$, so parts 3
and 4 say that $r_\sigma(A) \le \|A\|_p \le r_\sigma(A) + \varepsilon$. With relation 1 for
every operator norm, it follows that $r_\sigma(A)$ is the infimum of the operator norms of $A$.

The book quotes this result from Ortega and Rheinboldt, whose proof makes $A$ triangular and
scales the off-diagonal entries by $\operatorname{diag}(\delta, \delta^2, \dots)$. The backbone
theorem `Matrix.exists_seminorm_forall_mulVec_le` uses Gelfand's formula instead:
$p(x) = \sum_{j<k} c^{-j} \|A^j x\|$ for $c = r_\sigma(A) + \varepsilon$ and a $k$ with
$\|A^k\| \le c^k$. Part 4 is `Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le`. -/
theorem exists_opNorm_le_complexSpectralRadius_add (A : Matrix ι ι ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℝ (ι → ℝ), (∀ x, ‖x‖ ≤ p x) ∧ (∃ C, ∀ x, p x ≤ C * ‖x‖) ∧
      (∀ x, p (A *ᵥ x) ≤ ((Matrix.complexSpectralRadius A).toReal + ε) * p x) ∧
      ∀ c : ℝ, 0 ≤ c → (∀ x, p (A *ᵥ x) ≤ c * p x) →
        (Matrix.complexSpectralRadius A).toReal ≤ c := by
  classical
  obtain ⟨p, hlow, ⟨C, hup⟩, hA⟩ := Matrix.exists_seminorm_forall_mulVec_le A hε
  exact ⟨p, hlow, ⟨C, hup⟩, hA, fun c hc hcA =>
    Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le A p one_pos
      (by simpa using hlow) hup hc hcA⟩

open scoped Matrix.Norms.Operator in
/-- **Section 5.2.2** of [han2009theoretical], relation 3 (Gelfand's formula). For every real square
matrix $G$,
$$\lim_{k \to \infty} \|G^k\|^{1/k} = r_\sigma(G),$$
where $\|\cdot\|$ is the operator norm of the maximum norm. So the spectral radius is the
asymptotic rate of convergence of the iteration.

The backbone theorem `Matrix.tendsto_pow_rpow_linfty_opNorm` is the same limit for the norm on
`Matrix ι ι ℝ`. The book states the formula for any matrix norm, not necessarily induced by a
vector norm. This is the same limit, because two norms on a finite-dimensional space differ at
most by a factor $C$, and $C^{1/k} \to 1$. -/
theorem tendsto_pow_rpow_complexSpectralRadius (G : Matrix ι ι ℝ) :
    Tendsto (fun k : ℕ => ‖mulVecCLM (G ^ k)‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (Matrix.complexSpectralRadius G).toReal) := by
  refine (Matrix.tendsto_pow_rpow_linfty_opNorm G).congr fun k => ?_
  congr 1
  exact Matrix.linfty_opNorm_eq_opNorm (G ^ k)

section Classical

variable [LinearOrder ι]

/-- **Section 5.2.2** of [han2009theoretical], the **Jacobi splitting**. Write $A = D + L + U$ with
$D$ the diagonal, $L$ the strictly lower triangular and $U$ the strictly upper triangular part
of $A$, and let $D$ be nonsingular. The Jacobi splitting is $N = D$, $M = -(L + U)$. -/
noncomputable def jacobi (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart, -(A.strictLower + A.strictUpper), by
    rw [sub_neg_eq_add, ← add_assoc, Matrix.diagPart_add_strictLower_add_strictUpper], h⟩

/-- **Section 5.2.2** of [han2009theoretical], the **Gauss–Seidel splitting**. With $A = D + L + U$
as for the Jacobi splitting and $D$ nonsingular, the Gauss–Seidel splitting is $N = D + L$,
$M = -U$. -/
noncomputable def gaussSeidel (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart + A.strictLower, -A.strictUpper, by
    rw [sub_neg_eq_add, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.gaussSeidelSplitting A h).isUnit⟩

/-- **Section 5.2.2** of [han2009theoretical], the **SOR splitting**. With $A = D + L + U$ as for
the Jacobi splitting, $D$ nonsingular, and a relaxation parameter $\omega \ne 0$, the SOR
splitting is
$$N = \tfrac{1}{\omega} D + L, \qquad M = N - A = \bigl(\tfrac{1}{\omega} - 1\bigr) D - U.$$
-/
noncomputable def sor (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    BookSplitting A :=
  ⟨ω⁻¹ • A.diagPart + A.strictLower, (ω⁻¹ - 1) • A.diagPart - A.strictUpper, by
    have hsub : ω⁻¹ • A.diagPart + A.strictLower - ((ω⁻¹ - 1) • A.diagPart - A.strictUpper)
        = A.diagPart + A.strictLower + A.strictUpper := by
      rw [sub_smul, one_smul]
      abel
    rw [hsub, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.sorSplitting A h hω).isUnit⟩

/-- The book's Jacobi splitting corresponds to the backbone's Jacobi splitting
`Matrix.jacobiSplitting`. -/
@[simp]
theorem jacobi_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (jacobi A h).toSplitting = Matrix.jacobiSplitting A h := rfl

/-- The book's Gauss–Seidel splitting corresponds to the backbone's Gauss–Seidel splitting
`Matrix.gaussSeidelSplitting`. -/
@[simp]
theorem gaussSeidel_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (gaussSeidel A h).toSplitting = Matrix.gaussSeidelSplitting A h := rfl

/-- The book's SOR splitting corresponds to the backbone's SOR splitting `Matrix.sorSplitting`. -/
@[simp]
theorem sor_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    (sor A h hω).toSplitting = Matrix.sorSplitting A h hω := rfl

/-- The Gauss–Seidel splitting is the SOR splitting with $\omega = 1$: the two have the same matrix
$N = D + L$, and therefore the same $M = N - A$. -/
theorem sor_one (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (sor A h one_ne_zero).N = (gaussSeidel A h).N := by
  change (1 : ℝ)⁻¹ • A.diagPart + A.strictLower = A.diagPart + A.strictLower
  rw [inv_one, one_smul]

end Classical

end Splittings

/-!
### Integral equations of the second kind and the Picard iteration

This part covers Sections 5.2.3 and 5.2.4 of [han2009theoretical].
-/

section IntegralEquations

open IntegralOperator

open scoped NNReal Nat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Theorem 5.1.3 on a whole Banach space: a contractive map $T$ of $V$ has a unique fixed point,
the iteration converges to it from every starting point, and the bounds (5.1.4)–(5.1.6) hold. -/
private theorem theorem_5_1_3_univ {T : V → V} {α : ℝ} (hα : ContractiveOn T univ α) :
    (∃! u, T u = u) ∧
      ∀ u₀ : V, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) := by
  obtain ⟨huniq, hconv⟩ :=
    theorem_5_1_3 isClosed_univ ⟨(0 : V), mem_univ 0⟩ (mapsTo_univ T univ) hα
  refine ⟨by simpa using huniq, fun u₀ => ?_⟩
  obtain ⟨u, -, hfix, hlim, h1, h2, h3⟩ := hconv u₀ (mem_univ u₀)
  exact ⟨u, hfix, hlim, h1, h2, h3⟩

/-- Exercise 5.1.2 on a whole Banach space: if $T$ is continuous and some iterate $T^m$ with
$m \ge 1$ is contractive, then $T$ has a unique fixed point and the iteration converges to it
from every starting point. -/
private theorem exercise_5_1_2_univ {T : V → V} {α : ℝ} (hc : Continuous T) {m : ℕ} (hm : 0 < m)
    (hα : ContractiveOn T^[m] univ α) :
    (∃! u, T u = u) ∧ ∀ u₀ : V, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  obtain ⟨huniq, hconv⟩ := exercise_5_1_2 isClosed_univ ⟨(0 : V), mem_univ 0⟩ (mapsTo_univ T univ)
    hc.continuousOn hm hα
  refine ⟨by simpa using huniq, fun u₀ => ?_⟩
  obtain ⟨u, -, hfix, hlim⟩ := hconv u₀ (mem_univ u₀)
  exact ⟨u, hfix, hlim⟩

variable {a b : ℝ}

/-- The kernel $(t, s, z) \mapsto k(t, s, z + f(s))$, which turns the Volterra equation
$u = \mathcal{V}u + f$ into $v = \mathcal{V}' v$ by the substitution $v = u - f$. -/
private def shiftKernel (k : C(Icc a b × Icc a b × ℝ, ℝ)) (f : C(Icc a b, ℝ)) :
    C(Icc a b × Icc a b × ℝ, ℝ) :=
  ⟨fun p => k (p.1, p.2.1, p.2.2 + f p.2.1), by fun_prop⟩

/-- If $z \mapsto k(t, s, z)$ is Lipschitz with constant $M$ for all $t, s$, then so is
$z \mapsto k(t, s, z + f(s))$. -/
private theorem lipschitzWith_shiftKernel {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (f : C(Icc a b, ℝ))
    (t s : Icc a b) : LipschitzWith M fun z => shiftKernel k f (t, s, z) :=
  LipschitzWith.of_dist_le_mul fun z w => by
    have h : dist (k (t, s, z + f s)) (k (t, s, w + f s)) ≤ M * dist (z + f s) (w + f s) :=
      (hk t s).dist_le_mul _ _
    rwa [dist_add_right] at h

/-- The Volterra operator of the shifted kernel at $u$ is the Volterra operator of $k$ at $u + f$.
-/
private theorem volterra_shiftKernel (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ))
    (f u : C(Icc a b, ℝ)) : volterra hab (shiftKernel k f) u = volterra hab k (u + f) :=
  rfl

/-- The iterates of $u \mapsto \mathcal{V}u + f$ are the iterates of the Volterra operator of the
shifted kernel, conjugated by the translation $u \mapsto u + f$. -/
private theorem iterate_volterra_add (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ))
    (f : C(Icc a b, ℝ)) (n : ℕ) (v : C(Icc a b, ℝ)) :
    (fun u => volterra hab k u + f)^[n] v
      = (volterra hab (shiftKernel k f))^[n] (v - f) + f := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    rw [volterra_shiftKernel]

/-- **Equation (5.2.7)** of [han2009theoretical], the linear Fredholm integral equation of the
second kind. Let $a \le b$, let $k$ be a continuous function on $[a, b] \times [a, b]$, let
$f \in C[a, b]$, and let $\lambda \in \mathbb{R}$ satisfy the condition (5.2.8),
$$\alpha = \frac{1}{|\lambda|} \max_{a \le x \le b} \int_a^b |k(x, y)| \, dy < 1.$$
Let $T : C[a, b] \to C[a, b]$ be the map
$$(Tu)(x) = \frac{1}{\lambda} \Bigl( \int_a^b k(x, y) \, u(y) \, dy + f(x) \Bigr),$$
whose fixed points are the solutions of $\lambda u(x) - \int_a^b k(x, y) u(y) \, dy = f(x)$.
Then $T$ has a unique fixed point $u$, and for every $u_0 \in C[a, b]$ the iterates $T^n u_0$
converge to $u$ in the maximum norm, with
$$\|T^n u_0 - u\|_\infty \le \frac{\alpha^n}{1 - \alpha} \|u_0 - T u_0\|_\infty \qquad \text{for
  all } n \ge 0.$$

The number $\alpha$ is the contractivity constant of $T$, by the norm formula (2.2.8) for the
integral operator. The maximum is the supremum `⨆ x`. In Lean $1/0 = 0$, so for $\lambda = 0$
the map $T$ is $0$ and the statement is trivial. -/
theorem equation_5_2_7 (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) (f : C(Icc a b, ℝ))
    {lam : ℝ} (hlam : |lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) < 1)
    (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (x : Icc a b),
      T u x = lam⁻¹ * ((∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y)) + f x)) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        ∀ n, ‖T^[n] u₀ - u‖
          ≤ (|lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) ^ n
              / (1 - |lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) * ‖u₀ - T u₀‖ := by
  have hTeq : T = fun u => lam⁻¹ • (fredholm hab k u + f) := by
    funext u; ext x; rw [hT u x]; simp [mul_add]
  subst hTeq
  have hnorm : ‖fredholm hab k‖ = ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)| :=
    norm_fredholm hab k
  have hα : ContractiveOn (fun u => lam⁻¹ • (fredholm hab k u + f)) univ
      (|lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) := by
    refine ⟨by rw [← hnorm]; positivity, hlam, fun u _ v _ => ?_⟩
    have hsub : lam⁻¹ • (fredholm hab k u + f) - lam⁻¹ • (fredholm hab k v + f)
        = lam⁻¹ • fredholm hab k (u - v) := by
      rw [map_sub, ← smul_sub]; congr 1; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_inv, ← hnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((fredholm hab k).le_opNorm _) (by positivity)
  obtain ⟨huniq, hconv⟩ := theorem_5_1_3_univ hα
  refine ⟨huniq, fun u₀ => ?_⟩
  obtain ⟨u, hfix, hlim, h1, -, -⟩ := hconv u₀
  exact ⟨u, hfix, hlim, h1⟩

/-- **Theorem 5.2.2** of [han2009theoretical], the Urysohn integral equation of the second kind
(5.2.10). Let $a \le b$, let $k$ be a continuous function on
$[a, b] \times [a, b] \times \mathbb{R}$, and let $z \mapsto k(x, y, z)$ be Lipschitz with
constant $M$ for all $x, y \in [a, b]$ (5.2.11)–(5.2.12). Let $f \in C[a, b]$, and let
$\mu \in \mathbb{R}$ satisfy $\alpha = |\mu| M (b - a) < 1$. Let $T : C[a, b] \to C[a, b]$ be
the map
$$(Tu)(x) = \mu \int_a^b k(x, y, u(y)) \, dy + f(x).$$
Then:

1. the equation $u = Tu$ has a unique solution $u \in C[a, b]$;
2. for every $u_0 \in C[a, b]$ the iteration (5.2.13) $u_n = T u_{n-1}$ converges to $u$ in the
   maximum norm, and for every $n \ge 0$,
$$\|u_n - u\|_\infty \le \frac{\alpha^n}{1 - \alpha} \|u_0 - u_1\|_\infty, \qquad \|u_{n+1} -
  u\|_\infty \le \frac{\alpha}{1 - \alpha} \|u_n - u_{n+1}\|_\infty, \qquad \|u_{n+1} -
  u\|_\infty \le \alpha \|u_n - u\|_\infty.$$
-/
theorem theorem_5_2_2 (hab : a ≤ b) {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ x y : Icc a b, LipschitzWith M fun z => k (x, y, z)) (f : C(Icc a b, ℝ)) {mu : ℝ}
    (hmu : |mu| * ((M : ℝ) * (b - a)) < 1) (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (x : Icc a b),
      T u x = mu * (∫ y in a..b, k (x, projIcc a b hab y, u (projIcc a b hab y))) + f x) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖
          ≤ (|mu| * ((M : ℝ) * (b - a))) ^ n / (1 - |mu| * ((M : ℝ) * (b - a)))
              * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖
          ≤ |mu| * ((M : ℝ) * (b - a)) / (1 - |mu| * ((M : ℝ) * (b - a)))
              * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ |mu| * ((M : ℝ) * (b - a)) * ‖T^[n] u₀ - u‖) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have hTeq : T = fun u => mu • urysohn hab k u + f := by
    funext u; ext x; rw [hT u x]; simp
  subst hTeq
  refine theorem_5_1_3_univ ⟨by positivity, hmu, fun u _ v _ => ?_⟩
  have hlip := (lipschitzWith_urysohn hab hk).dist_le_mul u v
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hba] at hlip
  have hsub : mu • urysohn hab k u + f - (mu • urysohn hab k v + f)
      = mu • (urysohn hab k u - urysohn hab k v) := by rw [smul_sub]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left hlip (abs_nonneg _)

/-- **Theorem 5.2.3** of [han2009theoretical], the Volterra integral equation of the second kind
(5.2.15). Let $a \le b$, let $k$ be a continuous function on
$[a, b] \times [a, b] \times \mathbb{R}$, and let $z \mapsto k(t, s, z)$ be Lipschitz with some
constant $M$ for all $t, s \in [a, b]$. Let $f \in C[a, b]$, and let $T : C[a, b] \to C[a, b]$
be the map
$$(Tu)(t) = \int_a^t k(t, s, u(s)) \, ds + f(t).$$
Then the equation $u = Tu$ has a unique solution $u \in C[a, b]$, and for every
$u_0 \in C[a, b]$ the iteration (5.2.16) $u_n = T u_{n-1}$ converges to $u$ in the maximum norm.

No smallness condition on $M$ is needed. The factorial estimate
`IntegralOperator.norm_iterate_volterra_sub_le` on the iterated kernels makes some power of $T$
a contraction, and Exercise 5.1.2 applies. -/
theorem theorem_5_2_3 (hab : a ≤ b) {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (f : C(Icc a b, ℝ))
    (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (t : Icc a b),
      T u t = (∫ s in a..(t : ℝ), k (t, projIcc a b hab s, u (projIcc a b hab s))) + f t) :
    (∃! u, T u = u) ∧ ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  have hTeq : T = fun u => volterra hab k u + f := by
    funext u; ext t; rw [hT u t]; simp
  subst hTeq
  obtain ⟨m, hm, hcw⟩ :=
    exists_contractingWith_iterate_volterra hab (lipschitzWith_shiftKernel hk f)
  refine exercise_5_1_2_univ
    ((lipschitzWith_volterra hab hk).continuous.add continuous_const) hm
    ⟨NNReal.coe_nonneg _, by exact_mod_cast hcw.1, fun u _ v _ => ?_⟩
  rw [iterate_volterra_add hab k f m u, iterate_volterra_add hab k f m v,
    add_sub_add_right_eq_sub]
  have h := hcw.2.dist_le_mul (u - f) (v - f)
  rw [dist_eq_norm, dist_eq_norm] at h
  have huv : u - f - (v - f) = u - v := by abel
  rwa [huv] at h

/-- **Theorem 5.2.4** of [han2009theoretical] (Picard–Lindelöf), the convergence of Picard's
iteration. Let $t_0 \le t_1$, let $g$ be a continuous function on
$[t_0, t_1] \times \mathbb{R}$, let $w \mapsto g(s, w)$ be Lipschitz with constant $L$ for every
$s \in [t_0, t_1]$, let $z \in \mathbb{R}$, and let $\beta > L$. Give $C[t_0, t_1]$ the weighted
(Bielecki) norm
$$\|v\|_\beta = \max_{t_0 \le t \le t_1} e^{-\beta (t - t_0)} |v(t)|,$$
and let $T$ be the map of the integral equation (5.2.19),
$$(Tu)(t) = z + \int_{t_0}^t g(s, u(s)) \, ds.$$
Then, with $\alpha = L / \beta$:

1. $T$ has a unique fixed point $u$;
2. for every $u_0$ the Picard iteration (5.2.20) $u_n = T^n u_0$ converges to $u$ in the norm
   $\|\cdot\|_\beta$, and for every $n \ge 0$,
$$\|u_n - u\|_\beta \le \frac{\alpha^n}{1 - \alpha} \|u_0 - u_1\|_\beta, \qquad \|u_{n+1} -
  u\|_\beta \le \frac{\alpha}{1 - \alpha} \|u_n - u_{n+1}\|_\beta, \qquad \|u_{n+1} - u\|_\beta
  \le \alpha \|u_n - u\|_\beta.$$

The fixed points of $T$ are the solutions of the initial value problem $u' = g(t, u)$,
$u(t_0) = z$ on $[t_0, t_1]$. In the norm $\|\cdot\|_\beta$ the map $T$ is a contraction with
constant $L/\beta$. This norm is equivalent to the maximum norm
(`IntegralOperator.Bielecki.exp_mul_norm_equiv_le_norm`), so the convergence is uniform
convergence on $[t_0, t_1]$. The space with the norm $\|\cdot\|_\beta$ is
`IntegralOperator.Bielecki t₀ t₁ β`. The book states the theorem in a Banach space, on an
interval on both sides of $t_0$, and for a right-hand side that is Lipschitz only on a box; that
form is `AtkinsonHan.Chapter05.theorem_5_2_4_ode`. -/
theorem theorem_5_2_4 {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {g : C(Icc t₀ t₁ × ℝ, ℝ)} {L : ℝ≥0}
    (hg : ∀ s : Icc t₀ t₁, LipschitzWith L fun w => g (s, w)) (z : ℝ) {β : ℝ} (hβ : (L : ℝ) < β)
    (T : Bielecki t₀ t₁ β → Bielecki t₀ t₁ β)
    (hT : ∀ (u : Bielecki t₀ t₁ β) (t : Icc t₀ t₁),
      Bielecki.equiv (T u) t
        = z + ∫ s in t₀..(t : ℝ), g (projIcc t₀ t₁ ht s, Bielecki.equiv u (projIcc t₀ t₁ ht s))) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ ((L : ℝ) / β) ^ n / (1 - (L : ℝ) / β) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖
          ≤ (L : ℝ) / β / (1 - (L : ℝ) / β) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ (L : ℝ) / β * ‖T^[n] u₀ - u‖) := by
  have hβ0 : (0 : ℝ) < β := lt_of_le_of_lt L.coe_nonneg hβ
  have hdiv : (0 : ℝ) ≤ (L : ℝ) / β := by positivity
  -- the Picard operator is the Volterra operator of the kernel `(t, s, w) ↦ g (s, w)`, shifted by
  -- the constant function `z`
  set k : C(Icc t₀ t₁ × Icc t₀ t₁ × ℝ, ℝ) := ⟨fun p => g (p.2.1, p.2.2), by fun_prop⟩ with hk
  set f : C(Icc t₀ t₁, ℝ) := .const _ z with hf
  have hklip : ∀ t s : Icc t₀ t₁, LipschitzWith L fun w => k (t, s, w) := fun _ s => hg s
  have hTeq : T = fun u => Bielecki.equiv.symm (volterra ht k (Bielecki.equiv u) + f) := by
    funext u
    refine Bielecki.equiv.injective (ContinuousMap.ext fun t => ?_)
    rw [hT u t]
    simp [hk, hf, add_comm]
  subst hTeq
  have hstep : ∀ w : Bielecki t₀ t₁ β,
      volterraBielecki ht (shiftKernel k f) β (w - Bielecki.equiv.symm f)
        = Bielecki.equiv.symm (volterra ht k (Bielecki.equiv w)) := by
    intro w
    refine Bielecki.equiv.injective ?_
    rw [equiv_volterraBielecki, LinearEquiv.apply_symm_apply, volterra_shiftKernel]
    congr 1
    rw [map_sub, LinearEquiv.apply_symm_apply]
    abel
  obtain ⟨-, hlip⟩ := contractingWith_volterra_bielecki ht (lipschitzWith_shiftKernel hklip f) hβ
  refine theorem_5_1_3_univ ⟨hdiv, by rwa [div_lt_one hβ0], fun u _ v _ => ?_⟩
  dsimp only
  have h := hlip.dist_le_mul (u - Bielecki.equiv.symm f) (v - Bielecki.equiv.symm f)
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hdiv, hstep u, hstep v] at h
  have huv : u - Bielecki.equiv.symm f - (v - Bielecki.equiv.symm f) = u - v := by abel
  rw [huv, ← map_sub] at h
  have hcancel : volterra ht k (Bielecki.equiv u) + f - (volterra ht k (Bielecki.equiv v) + f)
      = volterra ht k (Bielecki.equiv u) - volterra ht k (Bielecki.equiv v) := by abel
  rw [← map_sub, hcancel]
  exact h

/-- **Theorem 5.2.4** of [han2009theoretical] (Picard–Lindelöf), the differential form. Let $E$ be a
real Banach space, $t_0 \in \mathbb{R}$, $z \in E$ and $a, b, M > 0$. Let
$f : \mathbb{R} \times E \to E$ be continuous on the box
$$Q_b = \{(t, u) : |t - t_0| \le a, \ \|u - z\| \le b\},$$
let $u \mapsto f(t, u)$ be Lipschitz on $\|u - z\| \le b$ with constant $L$ for every $t$ with
$|t - t_0| \le a$, let $\|f(t, u)\| \le M$ on $Q_b$, and let $a_0 = \min(a, b/M)$. Write
$I = [t_0 - a_0, t_0 + a_0]$. Then there is a function $u : \mathbb{R} \to E$ such that

1. $u(t_0) = z$;
2. $\|u(t) - z\| \le b$ for all $t \in I$;
3. $u'(t) = f(t, u(t))$ for all $t \in I$, with the derivative taken within $I$;
4. $t \mapsto f(t, u(t))$ is continuous on $I$, so $u$ is continuously differentiable on $I$;
5. every $v : \mathbb{R} \to E$ with $v(t_0) = z$, $\|v(t) - z\| \le b$ on $I$ and
   $v'(t) = f(t, v(t))$ on $I$ agrees with $u$ on $I$.

The condition $\|u(t) - z\| \le b$ is part of the book's statement, not an extra demand: $f$ is
given only on $Q_b$, so a solution of the book's problem stays in $Q_b$. It is also what makes
the uniqueness meaningful, since off the box the differential equation says nothing.

The four constants of the book are the four constants of Mathlib's `IsPicardLindelof`: $b$ is
its ball radius, $M$ its bound on the field, $L$ its Lipschitz constant, and $a_0$ the largest
half-length that its condition `mul_max_le` permits. The proof is
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt`. The convergence of Picard's
iteration is `AtkinsonHan.Chapter05.theorem_5_2_4`. -/
theorem theorem_5_2_4_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {t₀ a b M a₀ : ℝ} {L : ℝ≥0} {z : E} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2)
      (Icc (t₀ - a) (t₀ + a) ×ˢ Metric.closedBall z b))
    (hlip : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith L (f t) (Metric.closedBall z b))
    (hbdd : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ u ∈ Metric.closedBall z b, ‖f t u‖ ≤ M)
    (ha₀ : a₀ = min a (b / M)) :
    ∃ u : ℝ → E, u t₀ = z ∧
      (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀), u t ∈ Metric.closedBall z b) ∧
      (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀),
        HasDerivWithinAt u (f t (u t)) (Icc (t₀ - a₀) (t₀ + a₀)) t) ∧
      ContinuousOn (fun t => f t (u t)) (Icc (t₀ - a₀) (t₀ + a₀)) ∧
      ∀ v : ℝ → E, v t₀ = z → (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀), v t ∈ Metric.closedBall z b) →
        (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀),
          HasDerivWithinAt v (f t (v t)) (Icc (t₀ - a₀) (t₀ + a₀)) t) →
        EqOn u v (Icc (t₀ - a₀) (t₀ + a₀)) := by
  obtain ⟨bn, rfl⟩ : ∃ bn : ℝ≥0, (bn : ℝ) = b := ⟨b.toNNReal, Real.coe_toNNReal b hb.le⟩
  obtain ⟨Mn, rfl⟩ : ∃ Mn : ℝ≥0, (Mn : ℝ) = M := ⟨M.toNNReal, Real.coe_toNNReal M hM.le⟩
  have ha₀pos : 0 < a₀ := ha₀ ▸ lt_min ha (by positivity)
  have hmem₀ : t₀ ∈ Icc (t₀ - a₀) (t₀ + a₀) := ⟨by linarith, by linarith⟩
  have hsub : Icc (t₀ - a₀) (t₀ + a₀) ⊆ Icc (t₀ - a) (t₀ + a) := by
    have h : a₀ ≤ a := ha₀ ▸ min_le_left _ _
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hmulmax : (Mn : ℝ) * max (t₀ + a₀ - t₀) (t₀ - (t₀ - a₀)) ≤ (bn : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    have h1 : a₀ ≤ (bn : ℝ) / Mn := ha₀ ▸ min_le_right _ _
    have h2 : (Mn : ℝ) * a₀ ≤ bn := by
      have h := mul_le_mul_of_nonneg_left h1 hM.le
      rwa [mul_div_cancel₀ _ hM.ne'] at h
    simpa using h2
  have hpl : IsPicardLindelof f (⟨t₀, hmem₀⟩ : Icc (t₀ - a₀) (t₀ + a₀)) z bn 0 Mn L := by
    refine ⟨fun t ht => hlip t (hsub ht), fun u hu => ?_,
      fun t ht u hu => hbdd t (hsub ht) u hu, hmulmax⟩
    exact hcont.comp (f := fun t : ℝ => (t, u)) (by fun_prop) fun t ht => ⟨hsub ht, hu⟩
  obtain ⟨u, hu₀, humem, hu, huniq⟩ :=
    hpl.exists_unique_mem_closedBall_hasDerivWithinAt (Metric.mem_closedBall_self le_rfl)
      ⟨by linarith, by linarith⟩
  refine ⟨u, hu₀, humem, hu, ?_, huniq⟩
  exact hcont.comp (f := fun t : ℝ => (t, u t))
    (continuousOn_id.prodMk fun t ht => (hu t ht).continuousWithinAt)
    fun t ht => ⟨hsub ht, humem t ht⟩

end IntegralEquations

end AtkinsonHan.Chapter05
