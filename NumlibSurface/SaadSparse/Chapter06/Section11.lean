/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Iterate
import Numlib.Krylov.Subspace
import Numlib.Projection.Basic
import Numlib.Projection.Optimality
import Numlib.RingTheory.Polynomial.ChebyshevEllipse
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section07

/-!
# Saad, Section 6.11: Convergence analysis

This module formalizes Section 6.11 of [saad2003iterative], which bounds the error of the conjugate
gradient method and the residual of GMRES by min–max problems over polynomials, and solves these
problems with Chebyshev polynomials. Sections 6.11.1–6.11.2 treat the real Chebyshev polynomials
$C_k$ of (6.109)–(6.112), the shifted and normalized polynomial $\hat C_k$ of (6.113) on an interval
$[\alpha, \beta]$ and its min–max property (Theorem 6.25), and the complex Chebyshev polynomials on
an ellipse $E(c, d, a)$ (Lemma 6.26, Theorem 6.27, (6.118)–(6.120)). Section 6.11.3 proves that the
conjugate gradient iterates satisfy
$$\|x_* - x_m\|_A \le \frac{\|x_* - x_0\|_A}{C_m(1 + 2\eta)} \quad\text{and}\quad \|x_* - x_m\|_A
  \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^m \|x_* - x_0\|_A$$
for a symmetric positive definite $A$, with $\eta = \lambda_{\min} / (\lambda_{\max} -
\lambda_{\min})$ and $\kappa = \lambda_{\max} / \lambda_{\min}$ (Theorem 6.29 and (6.128)). Section
6.11.4 proves that restarted GMRES converges for a positive definite $A$ (Theorem 6.30) and bounds
the GMRES residual for a diagonalizable $A$ (Proposition 6.32 and Corollary 6.33).

Every result specializes the backbone. The Chebyshev results come from
`Numlib.RingTheory.Polynomial.ChebyshevMinimax` and `Numlib.RingTheory.Polynomial.ChebyshevEllipse`.
The conjugate gradient bounds come from `Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`
and `Krylov.IsGalerkinIterate.energyNorm_error_le` of `Numlib.Krylov.Convergence.CG`, applied to
`SaadSparse.Chapter06.cgX_isGalerkinIterate`. Theorem 6.30 is `Krylov.restarted_minRes_tendsto`, and
Lemma 6.31 is `Krylov.IsMinResidualIterate.norm_residual_le_norm_aeval` applied to
`SaadSparse.Chapter06.gmresFixed_isMinResidualIterate`.

## Main definitions

* Equation (6.109), `SaadSparse.Chapter06.C`: the Chebyshev polynomial $C_k$ of the first kind of
  degree $k$.
* Equation (6.113), `SaadSparse.Chapter06.Chat`: the Chebyshev polynomial $\hat C_k$ of
  $[\alpha, \beta]$, normalized to $1$ at $\gamma$.
* Equation (6.114), `SaadSparse.Chapter06.Ccomplex`: the Chebyshev polynomials of the first kind
  over $\mathbb{C}$.
* Equation (6.118), `SaadSparse.Chapter06.ellipse`: the ellipse $E(c, d, a)$, parameterized by the
  Joukowski radius $\rho$.
* Section 6.11.2, `SaadSparse.Chapter06.filledEllipse`: the closed region that the ellipse
  $E(c, d, a)$ encloses.
* Equation (6.119), `SaadSparse.Chapter06.ChatComplex`: the Chebyshev polynomial $\hat C_k$ of the
  ellipse $E(c, d, a)$, normalized to $1$ at $\gamma$.
* Equation (6.122), `SaadSparse.Chapter06.η`: $\eta = \lambda_{\min} / (\lambda_{\max} -
  \lambda_{\min})$.
* Section 6.11.3, `SaadSparse.Chapter06.κ`, `SaadSparse.Chapter06.anorm`: the condition number
  $\kappa = \lambda_{\max} / \lambda_{\min}$ and the $A$-norm $\|x\|_A$.
* Theorem 6.30, `SaadSparse.Chapter06.symmPart`: the symmetric part $(A + A^T)/2$.
* Proposition 6.32, `SaadSparse.Chapter06.epsMin`: $\varepsilon^{(m)} = \min_{p \in \mathbb{P}_m,\,
  p(0) = 1} \max_i |p(\lambda_i)|$.

## Main results

* Equation (6.109), `SaadSparse.Chapter06.equation_6_109`: $C_k(t) = \cos(k \cos^{-1} t)$ for
  $t \in [-1, 1]$.
* Section 6.11.1, `SaadSparse.Chapter06.C_rec`: the three-term recurrence
  $C_{k+2} = 2t C_{k+1} - C_k$.
* Equations (6.110)–(6.112), `SaadSparse.Chapter06.equation_6_110`,
  `SaadSparse.Chapter06.equation_6_111`, `SaadSparse.Chapter06.equation_6_112`: the closed forms of
  $C_k(t)$ for $t \ge 1$, and the lower bound $\frac12 (t + \sqrt{t^2 - 1})^k \le C_k(t)$.
* Theorem 6.25, `SaadSparse.Chapter06.theorem_6_25`, `SaadSparse.Chapter06.theorem_6_25_value`,
  `SaadSparse.Chapter06.theorem_6_25_value_mid`: among the polynomials $p$ of degree at most $k$
  with $p(\gamma) = 1$, $\hat C_k$ minimizes $\max_{t \in [\alpha, \beta]} |p(t)|$, and the minimum
  is $1 / |C_k(1 + 2(\gamma - \beta)/(\beta - \alpha))|$.
* Lemma 6.26, `SaadSparse.Chapter06.lemma_6_26` (Zarantonello): on the circle of radius $\rho$ about
  $0$, the min–max value for $p(\gamma) = 1$ is $(\rho / |\gamma|)^k$.
* Theorem 6.27, `SaadSparse.Chapter06.theorem_6_27`: the two-sided bound (6.117) on the min–max
  value on the ellipse $E_\rho$.
* Equations (6.119)–(6.120), `SaadSparse.Chapter06.ellipse_max_Chat`: the maximum of $|\hat C_k|$ on
  $E(c, d, a)$ is $C_k(a/d) / |C_k((c - \gamma)/d)|$.
* Lemma 6.28, `SaadSparse.Chapter06.lemma_6_28`: the CG iterate is $x_m = x_0 + q_m(A) r_0$, and
  $q_m$ minimizes $\|(I - A q(A)) d_0\|_A$ over the polynomials of degree less than $m$.
* Theorem 6.29, `SaadSparse.Chapter06.theorem_6_29`: the CG error bound (6.123), $\|x_* - x_m\|_A
  \le \|x_* - x_0\|_A / C_m(1 + 2\eta)$.
* Equations (6.124)–(6.127), `SaadSparse.Chapter06.equation_6_124`,
  `SaadSparse.Chapter06.equation_6_125`, `SaadSparse.Chapter06.equation_6_126`,
  `SaadSparse.Chapter06.equation_6_127`: the chain of real identities and estimates for the
  Chebyshev argument $1 + 2\eta$.
* Equation (6.128), `SaadSparse.Chapter06.equation_6_128`: $\|x_* - x_m\|_A \le 2 ((\sqrt\kappa -
  1)/(\sqrt\kappa + 1))^m \|x_* - x_0\|_A$.
* Theorem 6.30, `SaadSparse.Chapter06.theorem_6_30`, `SaadSparse.Chapter06.theorem_6_30_rate`: for a
  positive definite $A$, each cycle of GMRES(m) reduces the residual by the factor
  $\sqrt{1 - \mu^2/\sigma^2}$, and GMRES(m) converges for every $m \ge 1$.
* Lemma 6.31, `SaadSparse.Chapter06.lemma_6_31`: the GMRES iterate is $x_m = x_0 + q_m(A) r_0$, and
  $q_m$ minimizes $\|(I - A q(A)) r_0\|_2$ over the polynomials of degree less than $m$.
* Proposition 6.32, `SaadSparse.Chapter06.proposition_6_32`: for $A = X \Lambda X^{-1}$, the GMRES
  residual satisfies $\|r_m\|_2 \le \kappa_2(X) \varepsilon^{(m)} \|r_0\|_2$.
* Corollary 6.33, `SaadSparse.Chapter06.corollary_6_33`: if moreover the eigenvalues lie in an
  ellipse $E(c, d, a)$ that excludes the origin, then $\|r_m\|_2 \le \kappa_2(X) (C_m(a/d) /
  |C_m(c/d)|) \|r_0\|_2$.

## Conventions

* $C_k$ is Mathlib's `Polynomial.Chebyshev.T ℝ k`, and its complex counterpart is
  `Polynomial.Chebyshev.T ℂ k`.
* The extreme eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$ of a symmetric matrix are the
  infimum and the supremum of `Matrix.IsHermitian.eigenvalues`.
* The $A$-norm is the backbone's `energyNorm` (`SaadSparse.Chapter06.anorm_eq`), and $\|A\|_2$ is
  the operator norm of `Matrix.Norms.L2Operator`.
* The GMRES iterate with exactly $m$ Arnoldi steps is `SaadSparse.Chapter06.gmresFixed`, and the
  iterate of GMRES(m) after $k$ cycles is `SaadSparse.Chapter06.gmresRestarted`.

## Implementation notes

* The backbone's normalized polynomial `Polynomial.Chebyshev.shifted` uses the affine map $t \mapsto
  (\beta + \alpha - 2t)/(\beta - \alpha)$, where the book uses
  $t \mapsto 1 + 2(t - \beta)/(\beta - \alpha)$. The two maps differ by a sign, which cancels in the
  quotient (`SaadSparse.Chapter06.Chat_eq_shifted`). The results on the interval follow from the
  backbone through this identity: (6.109)–(6.112) from the closed forms, and Theorem 6.25 from
  `Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval` and
  `Polynomial.Chebyshev.sSup_abs_eval_shifted`.
* Mathlib's `Polynomial.Chebyshev.T` is written in full in this module, because the tridiagonal
  Lanczos matrix $T_m$ of Section 6.6 is `SaadSparse.Chapter06.T`, and inside the namespace that
  name takes precedence.
* The results on the ellipse specialize `Numlib.RingTheory.Polynomial.ChebyshevEllipse`: Lemma 6.26
  is `Polynomial.zarantonello`, Theorem 6.27 is `Polynomial.Chebyshev.ellipse_minimax_bounds`, and
  (6.119)–(6.120) is `Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse`.
* The ellipse is parameterized by the Joukowski radius $\rho$, not by the semi-major axis $a$. The
  two are related by $a = d(\rho + \rho^{-1})/2$, but solving for $\rho$ needs
  $\operatorname{arcosh}$, and every estimate of Section 6.11.2 is a function of $\rho$. The
  argument $a/d$ of $C_k$ in the book stays as it is, because $a/d = (\rho + \rho^{-1})/2$.
* Corollary 6.33 needs one step that the book leaves implicit: its hypothesis places the spectrum
  inside the ellipse, while (6.119)–(6.120) bounds $|\hat C_m|$ on the ellipse. The step is the
  maximum modulus principle on the filled ellipse, `Polynomial.norm_eval_le_of_forall_mem_ellipse`.
  Its proof uses an annulus, not a disc: the Joukowski map identifies $w$ with $w^{-1}$, so the
  filled ellipse is the image of a closed annulus, and the symmetry
  $\hat C_m(J(w)) = \hat C_m(J(w^{-1}))$ folds the inner boundary circle onto the outer one.
* The conjugate gradient bounds take the spectral hypothesis in the form of quadratic-form bounds,
  `LinearMap.IsSymmetricBoundedBy`, which `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`
  derives from the extreme eigenvalues. The backbone proof uses a compression of $A$ to the Krylov
  subspace, so no diagonalization of $A$ is needed.
* For Theorem 6.30, the work here is to show that a cycle of GMRES(m) is a minimal-residual iterate
  (`SaadSparse.Chapter06.gmres_isMinResidualIterate`), and to identify the constants
  $\mu = \lambda_{\min}((A + A^T)/2)$ and $\sigma = \|A\|_2$ of the book with the coercivity
  constant and the operator norm of the backbone.
* Proposition 6.32 adds the bound `SaadSparse.Chapter06.norm_aeval_diagonal_mulVec_le` for a
  diagonalizable complex matrix, since the backbone's `norm_aeval_apply_le_of_conj` covers only a
  symmetric diagonal factor.

## Deviations from the source

* **Equation (6.112)** (reading). The book writes the growth estimate as an approximation
  $C_k(t) \gtrsim \frac12 (t + \sqrt{t^2 - 1})^k$. It is stated as the inequality
  $\frac12 (t + \sqrt{t^2 - 1})^k \le C_k(t)$ for $t \ge 1$. See
  `SaadSparse.Chapter06.equation_6_112`.
* **Theorem 6.25** (reading). The book says "non-empty interval $[\alpha, \beta]$". This is read as
  nondegenerate, $\alpha < \beta$, since (6.113) divides by $\beta - \alpha$. See
  `SaadSparse.Chapter06.theorem_6_25`.
* **Theorem 6.29** (reading). The book's $\eta$ is infinite when $\lambda_{\min} = \lambda_{\max}$,
  so the bound (6.123) tacitly assumes $\lambda_{\min} < \lambda_{\max}$. This hypothesis is
  explicit. See `SaadSparse.Chapter06.theorem_6_29`.
-/

open scoped Polynomial

namespace SaadSparse.Chapter06

/-! ### Sections 6.11.1–6.11.2: Chebyshev polynomials and the min–max property -/

section ChebyshevMinimax

open Polynomial.Chebyshev (shifted T_add_two T_eval_neg T_real_cos T_real_cosh
  eval_T_eq_half_add_pow half_pow_le_eval_T shifted_degree_le shifted_eval_self
  sSup_abs_eval_shifted one_div_eval_T_le_sSup_abs_eval)

variable {t α β γ : ℝ}

/-! ### (6.109)–(6.112): the real Chebyshev polynomials -/

/-- **Equation (6.109)** of [saad2003iterative]. The **Chebyshev polynomial of the first kind**
$C_k$ of degree $k$, a real polynomial.

This is Mathlib's `Polynomial.Chebyshev.T ℝ k`. -/
noncomputable abbrev C (k : ℕ) : ℝ[X] := Polynomial.Chebyshev.T ℝ (k : ℤ)

/-- **Equation (6.114)** of [saad2003iterative]. The Chebyshev polynomial of the first kind $C_k$ of
degree $k$, as a complex polynomial.

This is Mathlib's `Polynomial.Chebyshev.T ℂ k`. It is used only by the results on the ellipse in
Section 6.11.2 (Lemma 6.26, Theorem 6.27 with (6.117), and (6.119)–(6.120)) and by Corollary
6.33, which evaluates $C_m$ at $c/d$. -/
noncomputable abbrev Ccomplex (k : ℕ) : ℂ[X] := Polynomial.Chebyshev.T ℂ (k : ℤ)

/-- **Equation (6.109)** of [saad2003iterative]. For every $k \in \mathbb{N}$ and $t \in [-1, 1]$,
$$C_k(t) = \cos(k \cos^{-1} t).$$
-/
theorem equation_6_109 (k : ℕ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (C k).eval t = Real.cos (k * Real.arccos t) := by
  have h : Real.cos (Real.arccos t) = t := Real.cos_arccos ht.1 ht.2
  have hT := T_real_cos (Real.arccos t) (k : ℤ)
  rw [h] at hT
  exact hT.trans (by norm_cast)

/-- **Section 6.11.1** of [saad2003iterative], the three-term recurrence. For every
$k \in \mathbb{N}$,
$$C_{k+2}(t) = 2t\, C_{k+1}(t) - C_k(t).$$
-/
theorem C_rec (k : ℕ) : C (k + 2) = 2 * Polynomial.X * C (k + 1) - C k := by
  have h := T_add_two (R := ℝ) (n := (k : ℤ))
  have h1 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
  have h2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [show C (k + 2) = Polynomial.Chebyshev.T ℝ (((k + 2 : ℕ) : ℤ)) from rfl, h1, h,
    show C (k + 1) = Polynomial.Chebyshev.T ℝ (((k + 1 : ℕ) : ℤ)) from rfl, h2]

/-- $C_0 = 1$. -/
theorem C_zero : C 0 = 1 := Polynomial.Chebyshev.T_zero ℝ

/-- $C_1(t) = t$. -/
theorem C_one : C 1 = Polynomial.X := Polynomial.Chebyshev.T_one ℝ

/-- **Equation (6.110)** of [saad2003iterative]. For every $k \in \mathbb{N}$ and $t \ge 1$,
$$C_k(t) = \cosh(k \cosh^{-1} t).$$
-/
theorem equation_6_110 (k : ℕ) (ht : 1 ≤ t) : (C k).eval t = Real.cosh (k * Real.arcosh t) := by
  have h : Real.cosh (Real.arcosh t) = t := Real.cosh_arcosh ht
  have hT := T_real_cosh (Real.arcosh t) (k : ℤ)
  rw [h] at hT
  exact hT.trans (by norm_cast)

/-- **Equation (6.111)** of [saad2003iterative]. For every $k \in \mathbb{N}$ and $t \ge 1$,
$$C_k(t) = \frac12 \left[ \left(t + \sqrt{t^2 - 1}\right)^k + \left(t + \sqrt{t^2 -
  1}\right)^{-k} \right].$$
-/
theorem equation_6_111 (k : ℕ) (ht : 1 ≤ t) :
    (C k).eval t =
      ((t + Real.sqrt (t ^ 2 - 1)) ^ k + ((t + Real.sqrt (t ^ 2 - 1))⁻¹) ^ k) / 2 := by
  rw [Real.add_sqrt_self_sq_sub_one_inv ht]
  exact eval_T_eq_half_add_pow ht k

/-- **Equation (6.112)** of [saad2003iterative]. For every $k \in \mathbb{N}$ and $t \ge 1$,
$$\frac12 \left(t + \sqrt{t^2 - 1}\right)^k \le C_k(t).$$

**Reading.** The book writes this growth estimate as the approximation
$C_k(t) \gtrsim \frac12 (t + \sqrt{t^2 - 1})^k$. It is stated here as an inequality, which
follows from (6.111). -/
theorem equation_6_112 (k : ℕ) (ht : 1 ≤ t) :
    (t + Real.sqrt (t ^ 2 - 1)) ^ k / 2 ≤ (C k).eval t :=
  half_pow_le_eval_T ht k

/-! ### (6.113): the shifted and normalized Chebyshev polynomial -/

/-- **Equation (6.113)** of [saad2003iterative]. For reals $\alpha$, $\beta$, $\gamma$ and
$k \in \mathbb{N}$, the **shifted and normalized Chebyshev polynomial** of $[\alpha, \beta]$ is
$$\hat C_k(t) = \frac{C_k\left(1 + 2 \frac{t - \beta}{\beta - \alpha}\right)}{C_k\left(1 + 2
  \frac{\gamma - \beta}{\beta - \alpha}\right)},$$
which takes the value $1$ at $\gamma$.

The definition is meant for $\alpha < \beta$ and $\gamma \notin [\alpha, \beta]$, where the
denominator is nonzero. Otherwise the divisions by zero give $0$ in Lean. -/
noncomputable def Chat (k : ℕ) (α β γ : ℝ) : ℝ[X] :=
  Polynomial.C (1 / (C k).eval (1 + 2 * (γ - β) / (β - α))) *
    (C k).comp (Polynomial.C (1 - 2 * β / (β - α)) + Polynomial.C (2 / (β - α)) * Polynomial.X)

/-- For $\alpha < \beta$, the affine map of the book is the negative of that of the backbone: $1 +
2(x - \beta)/(\beta - \alpha) = -(\beta + \alpha - 2x)/(\beta - \alpha)$. -/
private theorem shift_neg (hαβ : α < β) (x : ℝ) :
    1 + 2 * (x - β) / (β - α) = -((β + α - 2 * x) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  field_simp
  ring

private theorem eval_Chat (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (Chat k α β γ).eval t =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (1 + 2 * (t - β) / (β - α)) /
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (1 + 2 * (γ - β) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [Chat, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show 1 - 2 * β / (β - α) + 2 / (β - α) * t = 1 + 2 * (t - β) / (β - α) by
    field_simp; ring]
  ring

private theorem eval_shifted (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (shifted k α β γ).eval t =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval ((β + α - 2 * t) / (β - α)) /
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval ((β + α - 2 * γ) / (β - α)) := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [shifted, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show (β + α) / (β - α) - 2 / (β - α) * t = (β + α - 2 * t) / (β - α) by field_simp]
  ring

private theorem cast_negOnePow_ne_zero (m : ℤ) : ((m.negOnePow : ℤ) : ℝ) ≠ 0 := by
  rcases Int.isUnit_iff.1 (Units.isUnit m.negOnePow) with h | h <;> rw [h] <;> norm_num

/-- For $\alpha < \beta$ and every $\gamma$, the polynomial $\hat C_k$ of (6.113) equals the
backbone's `Polynomial.Chebyshev.shifted k α β γ`. The two affine maps differ by a sign and
$C_k(-x) = (-1)^k C_k(x)$, so the sign cancels in the quotient. -/
theorem Chat_eq_shifted (k : ℕ) (hαβ : α < β) (γ : ℝ) : Chat k α β γ = shifted k α β γ := by
  refine Polynomial.funext fun t => ?_
  rw [eval_Chat k hαβ γ t, eval_shifted k hαβ γ t, shift_neg hαβ t, shift_neg hαβ γ,
    T_eval_neg, T_eval_neg]
  exact mul_div_mul_left _ _ (cast_negOnePow_ne_zero _)

/-- **Equation (6.113)** of [saad2003iterative], evaluated. For $\alpha < \beta$ and all reals
$\gamma$, $t$,
$$\hat C_k(t) = \frac{C_k(1 + 2(t - \beta)/(\beta - \alpha))}{C_k(1 + 2(\gamma - \beta)/(\beta -
  \alpha))}.$$
-/
theorem Chat_eval (k : ℕ) (hαβ : α < β) (γ t : ℝ) :
    (Chat k α β γ).eval t =
      (C k).eval (1 + 2 * (t - β) / (β - α)) / (C k).eval (1 + 2 * (γ - β) / (β - α)) :=
  eval_Chat k hαβ γ t

/-- For $\alpha < \beta$, the polynomial $\hat C_k$ has degree at most $k$, so it is a competitor in
the min–max problem of Theorem 6.25. -/
theorem Chat_degree_le (k : ℕ) (hαβ : α < β) (γ : ℝ) : (Chat k α β γ).degree ≤ k := by
  rw [Chat_eq_shifted k hαβ γ]
  exact shifted_degree_le k α β γ

/-- For $\alpha < \beta$ and $\gamma \notin [\alpha, \beta]$, $\hat C_k(\gamma) = 1$: the
normalization of (6.113). -/
theorem Chat_eval_gamma (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    (Chat k α β γ).eval γ = 1 := by
  rw [Chat_eq_shifted k hαβ γ]
  exact shifted_eval_self k hαβ hγ

/-! ### Theorem 6.25: the Chebyshev min–max property -/

/-- **Theorem 6.25** of [saad2003iterative]. Let $[\alpha, \beta]$ be a nondegenerate real interval,
$\alpha < \beta$, let $\gamma \notin [\alpha, \beta]$, and let $k \in \mathbb{N}$. Then the
minimum
$$\min_{p \in \mathbb{P}_k,\ p(\gamma) = 1} \ \max_{t \in [\alpha, \beta]} |p(t)|$$
over the real polynomials $p$ of degree at most $k$ with $p(\gamma) = 1$ is attained by the
polynomial $\hat C_k$ of (6.113).

**Reading.** The book says "non-empty interval $[\alpha, \beta]$". This is read as
nondegenerate, $\alpha < \beta$, since (6.113) divides by $\beta - \alpha$.

The statement is that $\max_{t \in [\alpha, \beta]} |\hat C_k(t)|$ is the least element of the
set of values $\max_{t \in [\alpha, \beta]} |p(t)|$, written with `IsLeast` and `sSup`. -/
theorem theorem_6_25 (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧
        M = sSup ((fun t => |p.eval t|) '' Set.Icc α β)}
      (sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β)) := by
  refine ⟨⟨Chat k α β γ, Chat_degree_le k hαβ γ, Chat_eval_gamma k hαβ hγ, rfl⟩, ?_⟩
  rintro M ⟨p, hp, hpγ, rfl⟩
  rw [Chat_eq_shifted k hαβ γ, sSup_abs_eval_shifted k hαβ hγ]
  exact one_div_eval_T_le_sSup_abs_eval k hαβ hγ p hp hpγ

/-- **Theorem 6.25** of [saad2003iterative], the value of the minimum. For $\alpha < \beta$ and
$\gamma \notin [\alpha, \beta]$,
$$\max_{t \in [\alpha, \beta]} |\hat C_k(t)| = \frac{1}{\left|C_k\left(1 + 2 \frac{\gamma -
  \beta}{\beta - \alpha}\right)\right|}.$$
-/
theorem theorem_6_25_value (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β) =
      1 / |(C k).eval (1 + 2 * (γ - β) / (β - α))| := by
  rw [Chat_eq_shifted k hαβ γ, sSup_abs_eval_shifted k hαβ hγ,
    show (1 : ℝ) + 2 * (γ - β) / (β - α) = -((β + α - 2 * γ) / (β - α)) from shift_neg hαβ γ,
    Polynomial.Chebyshev.abs_eval_T_neg]

/-- **Theorem 6.25** of [saad2003iterative], the value of the minimum in terms of the midpoint
$\mu = (\alpha + \beta)/2$. For $\alpha < \beta$ and $\gamma \notin [\alpha, \beta]$,
$$\max_{t \in [\alpha, \beta]} |\hat C_k(t)| = \frac{1}{\left|C_k\left(2 \frac{\gamma -
  \mu}{\beta - \alpha}\right)\right|}.$$
-/
theorem theorem_6_25_value_mid (k : ℕ) (hαβ : α < β) (hγ : γ ∉ Set.Icc α β) :
    sSup ((fun t => |(Chat k α β γ).eval t|) '' Set.Icc α β) =
      1 / |(C k).eval (2 * (γ - (α + β) / 2) / (β - α))| := by
  have h : β - α ≠ 0 := sub_ne_zero.mpr hαβ.ne'
  rw [theorem_6_25_value k hαβ hγ,
    show (1 : ℝ) + 2 * (γ - β) / (β - α) = 2 * (γ - (α + β) / 2) / (β - α) by field_simp; ring]

end ChebyshevMinimax

/-! ### Section 6.11.2: the complex ellipse $E(c, d, a)$ and the min–max estimates on it -/

section ComplexEllipse

/-- **Equation (6.118)** of [saad2003iterative]. For $c, d \in \mathbb{C}$ and
$\rho \in \mathbb{R}$, the **ellipse** $E(c, d, a)$ is the image
$$\{c + d\, J(w) : |w| = \rho\}$$
of the circle $C(0, \rho)$ under $w \mapsto c + d\, J(w)$, where $J(w) = (w + w^{-1})/2$ is the
Joukowski map of (6.115)–(6.116). For $d \neq 0$ and $\rho \ge 1$ it has centre $c$, foci
$c \pm d$, and semi-major axis $a = d(\rho + \rho^{-1})/2$. The ellipse $E_\rho$ of Section
6.11.2 is `SaadSparse.Chapter06.ellipse 0 1 ρ`.

This is the backbone's `Set.ellipse`. The parameter is the Joukowski radius $\rho$, not the
semi-major axis $a$. The two determine each other through $a = d(\rho + \rho^{-1})/2$ and
$b = d(\rho - \rho^{-1})/2$, but solving for $\rho$ needs $\operatorname{arcosh}$, and every
estimate of Section 6.11.2 is a function of $\rho$. The argument $a/d$ of $C_k$ in the book
stays as it is, because $a/d = (\rho + \rho^{-1})/2$. -/
noncomputable abbrev ellipse (c d : ℂ) (ρ : ℝ) : Set ℂ := Set.ellipse c d ρ

/-- **Section 6.11.2** of [saad2003iterative], the region enclosed by the ellipse. For
$c, d \in \mathbb{C}$ and $\rho \in \mathbb{R}$, this is the image of the closed annulus
$\rho^{-1} \le |w| \le \rho$ under $w \mapsto c + d\, J(w)$. For $\rho \ge 1$ it is the union of
the confocal ellipses `SaadSparse.Chapter06.ellipse c d s` with $1 \le s \le \rho$, that is, the
ellipse $E(c, d, a)$ together with its interior.

This is the backbone's `Set.filledEllipse`; the description as a union is
`Set.filledEllipse_eq_biUnion`. It gives meaning to "the spectrum is enclosed in the ellipse" in
Corollary 6.33. -/
noncomputable abbrev filledEllipse (c d : ℂ) (ρ : ℝ) : Set ℂ := Set.filledEllipse c d ρ

/-- **Equation (6.119)** of [saad2003iterative]. For $k \in \mathbb{N}$ and
$c, d, \gamma \in \mathbb{C}$, the Chebyshev polynomial of the ellipse $E(c, d, a)$, normalized
to $1$ at $\gamma$:
$$\hat C_k(z) = \frac{C_k((c - z)/d)}{C_k((c - \gamma)/d)}.$$
It is the complex counterpart of (6.113).

This is the backbone's `Polynomial.Chebyshev.shiftedComplex`. If the denominator is $0$, the
polynomial is $0$, by division by zero in Lean. -/
noncomputable abbrev ChatComplex (k : ℕ) (c d gam : ℂ) : ℂ[X] :=
  Polynomial.Chebyshev.shiftedComplex k c d gam

/-- **Lemma 6.26** of [saad2003iterative] (Zarantonello). Let $C(0, \rho)$ be the circle with centre
the origin and radius $\rho > 0$, let $\gamma \in \mathbb{C}$ with $|\gamma| > \rho$, and let
$k \in \mathbb{N}$. Then
$$\min_{p \in \mathbb{P}_k,\ p(\gamma) = 1} \ \max_{z \in C(0, \rho)} |p(z)| =
  \left(\frac{\rho}{|\gamma|}\right)^k,$$
where $p$ ranges over the complex polynomials of degree at most $k$, and the minimum is
attained.

The statement is that $(\rho/|\gamma|)^k$ is the least element of the set of values, written
with `IsLeast` and `sSup`. It does not name the minimizer, which in the book is $(z/\gamma)^k$.
This is the backbone's `Polynomial.zarantonello`. -/
theorem lemma_6_26 (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {gam : ℂ} (hgam : ρ < ‖gam‖) :
    IsLeast {M : ℝ | ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval gam = 1 ∧
        M = sSup ((fun z => ‖p.eval z‖) '' Metric.sphere 0 ρ)} ((ρ / ‖gam‖) ^ k) :=
  Polynomial.zarantonello k hρ hgam

/-- **Theorem 6.27** of [saad2003iterative], with **equation (6.117)**. Let $\rho \ge 1$, and let
$E_\rho$ be the ellipse with centre the origin, foci $\pm 1$ and semi-major axis
$(\rho + \rho^{-1})/2$. Let $w_\gamma \in \mathbb{C}$ with $|w_\gamma| > \rho$, so that
$\gamma = J(w_\gamma)$ is a point that $E_\rho$ does not enclose, and let $k \in \mathbb{N}$.
Then
$$\frac{\rho^k}{|w_\gamma|^k}
  \le \inf_{p \in \mathbb{P}_k,\ p(\gamma) = 1} \ \max_{z \in E_\rho} |p(z)|
  \le \frac{\rho^k + \rho^{-k}}{|w_\gamma^k + w_\gamma^{-k}|},$$
where $p$ ranges over the complex polynomials of degree at most $k$.

The point $\gamma$ is given by its preimage $w_\gamma$ under the Joukowski map
`Complex.joukowski`. The ellipse `SaadSparse.Chapter06.ellipse 0 1 ρ` is $E_\rho$. The lower
bound is Lemma 6.26 applied to the polynomial $w \mapsto w^k p(J(w))$ of degree $2k$. The upper
bound is the value of the normalized Chebyshev polynomial $C_k(z)/C_k(\gamma)$. This is the
backbone's `Polynomial.Chebyshev.ellipse_minimax_bounds`. -/
theorem theorem_6_27 (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) {wgam : ℂ} (hw : ρ < ‖wgam‖) :
    (ρ / ‖wgam‖) ^ k ≤
        sInf {M : ℝ | ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval (Complex.joukowski wgam) = 1 ∧
          M = sSup ((fun z => ‖p.eval z‖) '' ellipse 0 1 ρ)} ∧
      sInf {M : ℝ | ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval (Complex.joukowski wgam) = 1 ∧
          M = sSup ((fun z => ‖p.eval z‖) '' ellipse 0 1 ρ)} ≤
        (ρ ^ k + (ρ ^ k)⁻¹) / ‖wgam ^ k + (wgam ^ k)⁻¹‖ := by
  obtain ⟨hlow, hmem⟩ := Polynomial.Chebyshev.ellipse_minimax_bounds k hρ hw
  exact ⟨le_csInf ⟨_, hmem⟩ hlow, csInf_le ⟨_, hlow⟩ hmem⟩

/-- **Equations (6.119)–(6.120)** of [saad2003iterative]. Let $k \in \mathbb{N}$, $\rho \ge 1$, and
$c, d, \gamma \in \mathbb{C}$ with $d \neq 0$ and $C_k((c - \gamma)/d) \neq 0$. Then the maximum
of the normalized Chebyshev polynomial $\hat C_k$ of (6.119) on the ellipse $E(c, d, a)$ is
$$\max_{z \in E(c, d, a)} |\hat C_k(z)| = \frac{C_k(a/d)}{|C_k((c - \gamma)/d)|}, \qquad
  \frac{a}{d} = \frac{\rho + \rho^{-1}}{2}.$$

This is the backbone's `Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse`. -/
theorem ellipse_max_Chat (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) {c d gam : ℂ} (hd : d ≠ 0)
    (hgam : (Ccomplex k).eval ((c - gam) / d) ≠ 0) :
    sSup ((fun z => ‖(ChatComplex k c d gam).eval z‖) '' ellipse c d ρ) =
      (C k).eval ((ρ + ρ⁻¹) / 2) / ‖(Ccomplex k).eval ((c - gam) / d)‖ :=
  Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse k hρ hd hgam

end ComplexEllipse

/-! ### Sections 6.11.3–6.11.4: convergence of the conjugate gradient method and of GMRES -/

/-! ### The quantities of §6.11.3 -/

section Quantities

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-- **Equation (6.122)** of [saad2003iterative]. For reals $\lambda_{\min}$ and $\lambda_{\max}$,
$$\eta = \frac{\lambda_{\min}}{\lambda_{\max} - \lambda_{\min}}.$$

If $\lambda_{\max} = \lambda_{\min}$, the value is $0$, by division by zero in Lean, while the
book's $\eta$ is then infinite. -/
noncomputable def η (lmin lmax : ℝ) : ℝ := lmin / (lmax - lmin)

/-- **Section 6.11.3** of [saad2003iterative], the spectral condition number
$\kappa = \lambda_{\max} / \lambda_{\min}$. It is $0$ if $\lambda_{\min} = 0$. -/
noncomputable def κ (lmin lmax : ℝ) : ℝ := lmax / lmin

/-- **Section 6.11.3** of [saad2003iterative], the **$A$-norm** $\|x\|_A = \sqrt{(Ax, x)}$, for an
$n \times n$ matrix $A$ and $x \in \mathbb{K}^n$.

The value is $\sqrt{\operatorname{Re}(Ax, x)}$, which is $0$ when
$\operatorname{Re}(Ax, x) < 0$. For a positive definite $A$ it is the usual $A$-norm. -/
noncomputable def anorm (A : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : ℝ :=
  Real.sqrt (RCLike.re (inner 𝕜 (op A x) x))

/-- The $A$-norm of the book is the backbone's energy norm: $\|x\|_A$ =
`energyNorm (SaadSparse.Chapter06.op A) x`. -/
theorem anorm_eq (A : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : anorm A x = energyNorm (op A) x := rfl

/-- If $\lambda_{\min} \neq \lambda_{\max}$, the Chebyshev argument of (6.123) is
$$1 + 2\eta = \frac{\lambda_{\max} + \lambda_{\min}}{\lambda_{\max} - \lambda_{\min}}.$$
-/
theorem one_add_two_mul_η {lmin lmax : ℝ} (h : lmin ≠ lmax) :
    1 + 2 * η lmin lmax = (lmax + lmin) / (lmax - lmin) := by
  have hd : lmax - lmin ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [η]
  field_simp
  ring

/-- Polynomials in $A$ commute with $A$. -/
private theorem aeval_apply_comm (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝕜[X]) (u : 𝔼) :
    Polynomial.aeval (op A) p (op A u) = op A (Polynomial.aeval (op A) p u) := by
  have h1 : Polynomial.aeval (op A) p (op A u) = (Polynomial.aeval (op A) p * op A) u := rfl
  have h2 : op A (Polynomial.aeval (op A) p u) = (op A * Polynomial.aeval (op A) p) u := rfl
  rw [h1, h2,
    show Polynomial.aeval (op A) p * op A = Polynomial.aeval (op A) (p * Polynomial.X) by
      rw [map_mul, Polynomial.aeval_X],
    show op A * Polynomial.aeval (op A) p = Polynomial.aeval (op A) (Polynomial.X * p) by
      rw [map_mul, Polynomial.aeval_X],
    mul_comm]

end Quantities

/-!
### Extreme values of a finite family of reals

The book's $\lambda_{\min}$ and $\lambda_{\max}$ are the infimum and the supremum of the family of
eigenvalues. These are the facts about them that the specializations need.
-/

section Extremes

variable {ι : Type*} [Finite ι] {f : ι → ℝ}

private theorem ciInf_le' (i : ι) : ⨅ j, f j ≤ f i := ciInf_le (Finite.bddBelow_range f) i

private theorem le_ciSup' (i : ι) : f i ≤ ⨆ j, f j := le_ciSup (Finite.bddAbove_range f) i

private theorem lt_ciInf_of_forall [Nonempty ι] {a : ℝ} (h : ∀ i, a < f i) : a < ⨅ i, f i := by
  obtain ⟨i, hi⟩ := Finite.exists_min f
  exact lt_of_lt_of_le (h i) (le_ciInf hi)

end Extremes

section Infimum

variable {ι : Type*} [Nonempty ι] {f : ι → ℝ}

/-- If $c \ge 0$ and $L \le c f(i)$ for every $i$, then $L \le c \inf_i f(i)$. -/
private theorem le_mul_ciInf {L c : ℝ} (hc : 0 ≤ c) (h : ∀ i, L ≤ c * f i) :
    L ≤ c * ⨅ i, f i := by
  rcases hc.eq_or_lt with h0 | h0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := h i
    rw [← h0, zero_mul] at hi ⊢
    exact hi
  · have h1 : ∀ i, L / c ≤ f i := fun i => (div_le_iff₀ h0).2 ((h i).trans_eq (mul_comm _ _))
    exact ((div_le_iff₀ h0).1 (le_ciInf h1)).trans_eq (mul_comm _ _)

end Infimum

/-! ### §6.11.3: convergence of the conjugate gradient method -/

section ConjugateGradient

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ xstar : EuclideanSpace ℝ (Fin n)}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The two ways of writing the error of a Krylov iterate agree: if $Ax_* = b$, then
$(I - A q(A)) d_0 = x_* - (x_0 + q(A) r_0)$ with $d_0 = x_* - x_0$, because $r_0 = A d_0$. -/
private theorem error_eq (hstar : op A xstar = b) (q : ℝ[X]) :
    ((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (xstar - x₀) =
      xstar - (x₀ + Polynomial.aeval (op A) q (r₀ A b x₀)) := by
  have hr : op A (xstar - x₀) = r₀ A b x₀ := by rw [map_sub, hstar]
  rw [← hr, aeval_apply_comm]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply]
  abel

/-- **Lemma 6.28** of [saad2003iterative]. Let $A$ be a real symmetric positive definite
$n \times n$ matrix, let $b, x_0, x_* \in \mathbb{R}^n$ with $Ax_* = b$, let $d_0 = x_* - x_0$
and $r_0 = b - Ax_0$, and let $m \in \mathbb{N}$. Then there is a polynomial $q_m$ of degree
less than $m$ such that the $m$-th conjugate gradient iterate is
$$x_m = x_0 + q_m(A) r_0,$$
and $q_m$ minimizes $\|(I - A q(A)) d_0\|_A$ over all polynomials $q$ of degree less than $m$.

The iterate $x_m$ is `SaadSparse.Chapter06.cgX`, from Algorithm 6.18. -/
theorem lemma_6_28 (hA : A.PosDef) (hstar : op A xstar = b) (m : ℕ) :
    ∃ q : ℝ[X], q.degree < m ∧ cgX A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) ∧
      ∀ q' : ℝ[X], q'.degree < m →
        anorm A (((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (xstar - x₀)) ≤
          anorm A (((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q') (xstar - x₀)) := by
  have hAc : (op A).IsSymmetricCoercive := isSymmetricCoercive_op_of_posDef hA
  have hgal := cgX_isGalerkinIterate (b := b) (x₀ := x₀) hA m
  obtain ⟨q, hq, hqe⟩ :=
    (Krylov.mem_subspace_iff_exists_aeval (op A) (b - op A x₀)).1 hgal.mem
  have hxeq : cgX A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) :=
    sub_eq_iff_eq_add'.1 hqe.symm
  refine ⟨q, hq, hxeq, fun q' hq' => ?_⟩
  have hy : x₀ + Polynomial.aeval (op A) q' (r₀ A b x₀) - x₀ ∈
      Krylov.subspace (op A) (b - op A x₀) m := by
    rw [add_sub_cancel_left]
    exact Krylov.aeval_apply_mem_subspace (op A) _ hq'
  rw [anorm_eq, anorm_eq, error_eq hstar q, error_eq hstar q', ← hxeq]
  exact IsGalerkin.energyNorm_le hAc hgal hstar hy

/-- The eigenvalues of a real positive definite matrix are positive. -/
private theorem eigenvalues_pos_of_posDef (hA : A.PosDef) (hH : A.IsHermitian) (i : Fin n) :
    0 < hH.eigenvalues i := by
  have hAc : (op A).IsSymmetricCoercive := isSymmetricCoercive_op_of_posDef hA
  have hev : Module.End.HasEigenvalue (op A) ((hH.eigenvalues i : ℝ)) :=
    (Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff hH _).2 ⟨i, by simp⟩
  simpa using hAc.re_pos_of_hasEigenvalue hev

variable (A)

/-- Let $A$ be a real positive definite $n \times n$ matrix with $n \ge 1$. Then $x \mapsto Ax$ is
symmetric and
$$\lambda_{\min} \|x\|^2 \le (Ax, x) \le \lambda_{\max} \|x\|^2$$
for every $x$, where $\lambda_{\min}$ and $\lambda_{\max}$ are the smallest and the largest
eigenvalue of $A$. This is the form in which the backbone's Chebyshev bounds take the spectral
hypothesis of the book. -/
theorem isSymmetricBoundedBy_op [NeZero n] (hA : A.PosDef) :
    (op A).IsSymmetricBoundedBy (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i) :=
  Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hA.1
    fun i => ⟨ciInf_le' i, le_ciSup' i⟩

/-- The smallest eigenvalue $\lambda_{\min}$ of a real positive definite $n \times n$ matrix with
$n \ge 1$ is positive. -/
theorem iInf_eigenvalues_pos [NeZero n] (hA : A.PosDef) : 0 < ⨅ i, hA.1.eigenvalues i := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact lt_ciInf_of_forall fun i => eigenvalues_pos_of_posDef hA hA.1 i

/-- For a real positive definite $n \times n$ matrix with $n \ge 1$,
$\lambda_{\min} \le \lambda_{\max}$. -/
theorem iInf_eigenvalues_le_iSup [NeZero n] (hA : A.PosDef) :
    ⨅ i, hA.1.eigenvalues i ≤ ⨆ i, hA.1.eigenvalues i := by
  obtain ⟨i⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (ciInf_le' i).trans (le_ciSup' i)

variable {A}

/-- **Theorem 6.29** of [saad2003iterative], with **equation (6.123)**. Let $A$ be a real symmetric
positive definite $n \times n$ matrix with $n \ge 1$, whose extreme eigenvalues satisfy
$\lambda_{\min} < \lambda_{\max}$, and let $\eta = \lambda_{\min}/(\lambda_{\max} -
\lambda_{\min})$. Let $b, x_0, x_* \in \mathbb{R}^n$ with $Ax_* = b$. Then for every
$m \in \mathbb{N}$ the $m$-th conjugate gradient iterate $x_m$ satisfies
$$\|x_* - x_m\|_A \le \frac{\|x_* - x_0\|_A}{C_m(1 + 2\eta)}.$$

**Reading.** The book's $\eta$ is infinite when $\lambda_{\min} = \lambda_{\max}$, so the
hypothesis $\lambda_{\min} < \lambda_{\max}$ is a tacit assumption of the book. Without it,
(6.128) holds; see `SaadSparse.Chapter06.equation_6_128`.

The iterate $x_m$ is `SaadSparse.Chapter06.cgX`. The proof specializes
`Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`. -/
theorem theorem_6_29 [NeZero n] (hA : A.PosDef) (hstar : op A xstar = b)
    (hl : ⨅ i, hA.1.eigenvalues i < ⨆ i, hA.1.eigenvalues i) (m : ℕ) :
    anorm A (xstar - cgX A b x₀ m) ≤
      anorm A (xstar - x₀) /
        (C m).eval (1 + 2 * η (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) := by
  rw [anorm_eq, anorm_eq, one_add_two_mul_η hl.ne]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T (iInf_eigenvalues_pos A hA) hl
    (isSymmetricBoundedBy_op A hA) (cgX_isGalerkinIterate hA m) hstar

/-- **Equation (6.124)** of [saad2003iterative]. Let $0 < \lambda_{\min} < \lambda_{\max}$ and
$\eta = \lambda_{\min}/(\lambda_{\max} - \lambda_{\min})$. Then for every $m \in \mathbb{N}$,
$$\frac12 \left(1 + 2\eta + \sqrt{(1 + 2\eta)^2 - 1}\right)^m \le C_m(1 + 2\eta).$$
-/
theorem equation_6_124 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (m : ℕ) :
    (1 + 2 * η lmin lmax + Real.sqrt ((1 + 2 * η lmin lmax) ^ 2 - 1)) ^ m / 2 ≤
      (C m).eval (1 + 2 * η lmin lmax) := by
  refine equation_6_112 m ?_
  rw [one_add_two_mul_η hll.ne, le_div_iff₀ (by linarith)]
  linarith

/-- **Equation (6.125)** of [saad2003iterative]. Let $0 < \lambda_{\min} < \lambda_{\max}$ and
$\eta = \lambda_{\min}/(\lambda_{\max} - \lambda_{\min})$. Then
$$\sqrt{(1 + 2\eta)^2 - 1} = 2 \sqrt{\eta(\eta + 1)}.$$
-/
theorem equation_6_125 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    Real.sqrt ((1 + 2 * η lmin lmax) ^ 2 - 1) =
      2 * Real.sqrt (η lmin lmax * (η lmin lmax + 1)) := by
  have hη : 0 ≤ η lmin lmax := div_nonneg hl.le (by linarith)
  rw [show (1 + 2 * η lmin lmax) ^ 2 - 1 = 2 ^ 2 * (η lmin lmax * (η lmin lmax + 1)) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- **Equation (6.126)** of [saad2003iterative]. Let $0 < \lambda_{\min} < \lambda_{\max}$ and
$\eta = \lambda_{\min}/(\lambda_{\max} - \lambda_{\min})$. Then
$$1 + 2\eta + 2\sqrt{\eta(\eta + 1)} = \left(\sqrt{\eta} + \sqrt{\eta + 1}\right)^2.$$
-/
theorem equation_6_126 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    1 + 2 * η lmin lmax + 2 * Real.sqrt (η lmin lmax * (η lmin lmax + 1)) =
      (Real.sqrt (η lmin lmax) + Real.sqrt (η lmin lmax + 1)) ^ 2 := by
  have hη : 0 ≤ η lmin lmax := div_nonneg hl.le (by linarith)
  have hs : Real.sqrt (η lmin lmax * (η lmin lmax + 1)) =
      Real.sqrt (η lmin lmax) * Real.sqrt (η lmin lmax + 1) := Real.sqrt_mul hη _
  rw [add_sq, Real.sq_sqrt hη, Real.sq_sqrt (by linarith), hs]
  ring

/-- **Equation (6.127)** of [saad2003iterative]. Let $0 < \lambda_{\min} < \lambda_{\max}$, $\eta =
\lambda_{\min}/(\lambda_{\max} - \lambda_{\min})$ and $\kappa = \lambda_{\max}/\lambda_{\min}$.
Then
$$\left(\sqrt{\eta} + \sqrt{\eta + 1}\right)^2 = \frac{\sqrt{\kappa} + 1}{\sqrt{\kappa} - 1}.$$
-/
theorem equation_6_127 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    (Real.sqrt (η lmin lmax) + Real.sqrt (η lmin lmax + 1)) ^ 2 =
      (Real.sqrt (κ lmin lmax) + 1) / (Real.sqrt (κ lmin lmax) - 1) := by
  have hd : (0 : ℝ) < lmax - lmin := by linarith
  have hmax : (0 : ℝ) < lmax := by linarith
  have key : ∀ s S D : ℝ, 0 < s → 0 < D → s < S → D ^ 2 = S ^ 2 - s ^ 2 →
      (s / D + S / D) ^ 2 = (S / s + 1) / (S / s - 1) := by
    intro s S D hs hD hsS hD2
    have hSs : S - s ≠ 0 := sub_ne_zero.mpr hsS.ne'
    have hSs' : S + s ≠ 0 := ne_of_gt (by linarith)
    have hq : S / s - 1 ≠ 0 := (sub_pos.2 ((one_lt_div hs).2 hsS)).ne'
    have e2 : (S / s + 1) / (S / s - 1) = (S + s) / (S - s) := by field_simp
    rw [← add_div, div_pow, hD2, e2, show S ^ 2 - s ^ 2 = (S - s) * (S + s) by ring,
      div_eq_div_iff (mul_ne_zero hSs hSs') hSs]
    ring
  have h1 : Real.sqrt (η lmin lmax) = Real.sqrt lmin / Real.sqrt (lmax - lmin) := by
    rw [η, Real.sqrt_div hl.le]
  have h2 : Real.sqrt (η lmin lmax + 1) = Real.sqrt lmax / Real.sqrt (lmax - lmin) := by
    rw [show η lmin lmax + 1 = lmax / (lmax - lmin) by rw [η]; field_simp; ring,
      Real.sqrt_div hmax.le]
  have h3 : Real.sqrt (κ lmin lmax) = Real.sqrt lmax / Real.sqrt lmin := by
    rw [κ, Real.sqrt_div hmax.le]
  rw [h1, h2, h3]
  exact key _ _ _ (Real.sqrt_pos.2 hl) (Real.sqrt_pos.2 hd) (Real.sqrt_lt_sqrt hl.le hll)
    (by rw [Real.sq_sqrt hd.le, Real.sq_sqrt hmax.le, Real.sq_sqrt hl.le])

/-- **Equation (6.128)** of [saad2003iterative]. Let $A$ be a real symmetric positive definite
$n \times n$ matrix with $n \ge 1$, let $\kappa = \lambda_{\max}/\lambda_{\min}$, and let
$b, x_0, x_* \in \mathbb{R}^n$ with $Ax_* = b$. Then for every $m \in \mathbb{N}$ the $m$-th
conjugate gradient iterate $x_m$ satisfies
$$\|x_* - x_m\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^m \|x_* -
  x_0\|_A.$$

Unlike (6.123), this bound does not need $\lambda_{\min} < \lambda_{\max}$. The proof
specializes `Krylov.IsGalerkinIterate.energyNorm_error_le`. -/
theorem equation_6_128 [NeZero n] (hA : A.PosDef) (hstar : op A xstar = b) (m : ℕ) :
    anorm A (xstar - cgX A b x₀ m) ≤
      2 * ((Real.sqrt (κ (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) - 1) /
        (Real.sqrt (κ (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) + 1)) ^ m *
        anorm A (xstar - x₀) := by
  rw [anorm_eq, anorm_eq, κ]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le (iInf_eigenvalues_pos A hA)
    (iInf_eigenvalues_le_iSup A hA) (isSymmetricBoundedBy_op A hA)
    (cgX_isGalerkinIterate hA m) hstar

end ConjugateGradient

/-! ### §6.11.4: convergence of GMRES -/

section GMRESConvergence

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

open scoped Matrix Matrix.Norms.L2Operator

/-- **Theorem 6.30** of [saad2003iterative], the symmetric part $(A + A^T)/2$ of a real square
matrix $A$. -/
noncomputable def symmPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2⁻¹ : ℝ) • (A + Aᵀ)

/-- The symmetric part $(A + A^T)/2$ of a real square matrix is symmetric. -/
theorem symmPart_isHermitian (A : Matrix (Fin n) (Fin n) ℝ) : (symmPart A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm, symmPart]
  simp [Matrix.transpose_add, add_comm]

private theorem op_symmPart (A : Matrix (Fin n) (Fin n) ℝ) :
    op (symmPart A) = (2⁻¹ : ℝ) • (op A + LinearMap.adjoint (op A)) := by
  have h : Matrix.toEuclideanLin ((2⁻¹ : ℝ) • (A + Aᴴ)) =
      (2⁻¹ : ℝ) • (Matrix.toEuclideanLin A + LinearMap.adjoint (Matrix.toEuclideanLin A)) := by
    rw [map_smul, map_add, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [symmPart, show (Aᵀ : Matrix (Fin n) (Fin n) ℝ) = Aᴴ from
    (Matrix.conjTranspose_eq_transpose_of_trivial A).symm]
  exact h

/-- The quadratic form of $A$ equals that of its symmetric part: $((A + A^T)/2\, x, x) = (Ax, x)$.
-/
private theorem inner_op_symmPart (A : Matrix (Fin n) (Fin n) ℝ) (x : 𝔼) :
    inner ℝ (op (symmPart A) x) x = inner ℝ (op A x) x := by
  rw [op_symmPart, LinearMap.smul_apply, LinearMap.add_apply, real_inner_smul_left,
    inner_add_left, LinearMap.adjoint_inner_left, real_inner_comm x (op A x)]
  ring

/-- If $(Ax, x) > 0$ for every nonzero real vector $x$, which is the hypothesis "$A$ is positive
definite" of Theorem 6.30 in the sense of the book, then $(A + A^T)/2$ is a positive definite
matrix. -/
theorem symmPart_posDef (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) :
    (symmPart A).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.2 (symmPart_isHermitian A), ?_⟩
  rw [LinearMap.isCoercive_iff_forall_pos]
  intro x hx
  simpa [inner_op_symmPart] using hA x hx

variable (A)

/-- For a real $n \times n$ matrix $A$ with $n \ge 1$, let $\mu = \lambda_{\min}((A + A^T)/2)$. Then
$(Ax, x) \ge \mu \|x\|^2$ for every $x$. So $\mu$ is a coercivity constant of $A$, the constant
of Theorem 6.30. -/
theorem isCoerciveWith_op [NeZero n] :
    (op A).IsCoerciveWith (⨅ i, (symmPart_isHermitian A).eigenvalues i) := by
  have hbdd := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin (symmPart_isHermitian A)
    (lmin := ⨅ i, (symmPart_isHermitian A).eigenvalues i)
    (lmax := ⨆ i, (symmPart_isHermitian A).eigenvalues i) fun i => ⟨ciInf_le' i, le_ciSup' i⟩
  intro x
  simpa [inner_op_symmPart] using hbdd.le_re_inner x

/-- If $n \ge 1$ and $(Ax, x) > 0$ for every nonzero real vector $x$, then the coercivity constant
$\mu = \lambda_{\min}((A + A^T)/2)$ of Theorem 6.30 is positive. -/
theorem iInf_eigenvalues_symmPart_pos [NeZero n]
    (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) :
    0 < ⨅ i, (symmPart_isHermitian A).eigenvalues i := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact lt_ciInf_of_forall fun i =>
    eigenvalues_pos_of_posDef (symmPart_posDef hA) (symmPart_isHermitian A) i

/-- A real square matrix $A$ with $(Ax, x) > 0$ for every nonzero $x$ is nonsingular. -/
theorem isUnit_of_forall_inner_pos (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) : IsUnit A := by
  have hco : (op A).IsCoercive := by
    rw [LinearMap.isCoercive_iff_forall_pos]
    intro x hx
    simpa using hA x hx
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have h : op A (WithLp.toLp 2 u) = op A (WithLp.toLp 2 v) := by
    simp only [Matrix.toLpLin_apply]
    rw [huv]
  simpa using congrArg WithLp.ofLp (hco.injective h)

variable {A}

/-- Let $A$ be a nonsingular real matrix, and let $b, y \in \mathbb{R}^n$ and $m \in \mathbb{N}$.
Then the GMRES iterate with starting vector $y$ and at most $m$ steps minimizes the residual
norm $\|b - Ax\|_2$ over $x \in y + \mathcal{K}_m(A, b - Ay)$.

The iterate is `SaadSparse.Chapter06.gmres`, which follows the rule of the book "if
$h_{j+1,j} = 0$ then set $m := j$". This rule stops the Arnoldi process only after
$\mathcal{K}_m$ is exhausted, so the truncated iterate still minimizes over all of
$\mathcal{K}_m$. -/
theorem gmres_isMinResidualIterate (hAu : IsUnit A) (b y : 𝔼) (m : ℕ) :
    Krylov.IsMinResidualIterate (op A) b y m (gmres A b y m) := by
  have hsub : Krylov.subspace (op A) (b - op A y) (mEff A b y m) =
      Krylov.subspace (op A) (b - op A y) m := by
    rw [mEff, grade_v₁]
    rcases le_total m (Krylov.grade (op A) (r₀ A b y)) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Krylov.subspace_eq_of_grade_le (op A) (b - op A y) h]
  have h := gmresFixed_isMinResidualIterate A b y (mEff_le A b y m)
    (isUnit_R_of_isUnit A b y hAu (mEff_le A b y m))
  have hg : gmres A b y m = gmresFixed A b y (mEff A b y m) := rfl
  rw [hg]
  exact ⟨hsub ▸ h.mem, fun z hz => h.min z (hsub ▸ hz)⟩

/-- If $c$ is a coercivity constant of $A$, then $c \|z\| \le \|Az\|$ for every $z$. -/
private theorem mul_norm_le_norm_op {c : ℝ} (hc : (op A).IsCoerciveWith c) (z : 𝔼) :
    c * ‖z‖ ≤ ‖op A z‖ := by
  have h1 : c * ‖z‖ ^ 2 ≤ inner ℝ (op A z) z := by simpa using hc z
  have h2 : (inner ℝ (op A z) z : ℝ) ≤ ‖op A z‖ * ‖z‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) h

/-- Each cycle of GMRES(m) is a minimal-residual iterate over $\mathcal{K}_m$ from the previous
iterate. -/
private theorem restarted_isMinResidualIterate (hAu : IsUnit A) (b x₀ : 𝔼) (m k : ℕ) :
    Krylov.IsMinResidualIterate (op A) b (gmresRestarted A b m x₀ k) m
      (gmresRestarted A b m x₀ (k + 1)) := by
  have h : gmresRestarted A b m x₀ (k + 1) = gmres A b (gmresRestarted A b m x₀ k) m :=
    Function.iterate_succ_apply' _ _ _
  rw [h]
  exact gmres_isMinResidualIterate hAu b _ m

/-- **Theorem 6.30** of [saad2003iterative], the rate. Let $A$ be a real $n \times n$ matrix with
$n \ge 1$ such that $(Ax, x) > 0$ for every nonzero $x \in \mathbb{R}^n$. Let
$\mu = \lambda_{\min}((A + A^T)/2)$ and $\sigma = \|A\|_2$, let $b, x_0 \in \mathbb{R}^n$, and
let $m \ge 1$. If $x_k$ is the iterate of GMRES(m) after $k$ cycles, then for every $k$
$$\|b - Ax_{k+1}\|_2 \le \sqrt{1 - \frac{\mu^2}{\sigma^2}}\ \|b - Ax_k\|_2.$$

The factor is that of (5.15) of the book, since one cycle of GMRES(m) is at least as good as one
minimal-residual step. -/
theorem theorem_6_30_rate [NeZero n] (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) (b x₀ : 𝔼)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ‖b - op A (gmresRestarted A b m x₀ (k + 1))‖ ≤
      Real.sqrt (1 - (⨅ i, (symmPart_isHermitian A).eigenvalues i) ^ 2 / ‖A‖ ^ 2) *
        ‖b - op A (gmresRestarted A b m x₀ k)‖ := by
  have h := Krylov.IsMinResidualIterate.norm_residual_le_of_isCoerciveWith
    (A := LinearMap.toContinuousLinearMap (op A)) (iInf_eigenvalues_symmPart_pos A hA)
    (isCoerciveWith_op A) hm
    (restarted_isMinResidualIterate (isUnit_of_forall_inner_pos A hA) b x₀ m k)
  rwa [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]

/-- **Theorem 6.30** of [saad2003iterative]. Let $A$ be a real $n \times n$ matrix with $n \ge 1$
that is positive definite in the sense of the book: $(Ax, x) > 0$ for every nonzero
$x \in \mathbb{R}^n$, or equivalently $(A + A^T)/2$ is symmetric positive definite. Let
$b, x_0, x_* \in \mathbb{R}^n$ with $Ax_* = b$, and let $m \ge 1$. Then the iterates $x_k$ of
GMRES(m) (Algorithm 6.11) after $k$ cycles converge to $x_*$ as $k \to \infty$.

This is the backbone's `Krylov.restarted_minRes_tendsto`. A cycle of Algorithm 6.11 is a
minimal-residual iterate (`SaadSparse.Chapter06.gmres_isMinResidualIterate`), and coercivity
turns the convergence of the residuals into convergence of the iterates. -/
theorem theorem_6_30 [NeZero n] (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) (b x₀ xstar : 𝔼)
    (hstar : op A xstar = b) {m : ℕ} (hm : 1 ≤ m) :
    Filter.Tendsto (fun k => gmresRestarted A b m x₀ k) Filter.atTop (nhds xstar) := by
  have hc := iInf_eigenvalues_symmPart_pos A hA
  have hco := isCoerciveWith_op A
  have hres : Filter.Tendsto (fun k => ‖b - op A (gmresRestarted A b m x₀ k)‖)
      Filter.atTop (nhds 0) :=
    Krylov.restarted_minRes_tendsto (A := LinearMap.toContinuousLinearMap (op A)) hc hco hm _
      (restarted_isMinResidualIterate (isUnit_of_forall_inner_pos A hA) b x₀ m)
  have hbound : ∀ k, ‖gmresRestarted A b m x₀ k - xstar‖ ≤
      ‖b - op A (gmresRestarted A b m x₀ k)‖ /
        ⨅ i, (symmPart_isHermitian A).eigenvalues i := by
    intro k
    rw [le_div_iff₀ hc]
    calc ‖gmresRestarted A b m x₀ k - xstar‖ * ⨅ i, (symmPart_isHermitian A).eigenvalues i
        = (⨅ i, (symmPart_isHermitian A).eigenvalues i) *
            ‖gmresRestarted A b m x₀ k - xstar‖ := mul_comm _ _
      _ ≤ ‖op A (gmresRestarted A b m x₀ k - xstar)‖ := mul_norm_le_norm_op hco _
      _ = ‖b - op A (gmresRestarted A b m x₀ k)‖ := by rw [map_sub, hstar, norm_sub_rev]
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound
    (by simpa using hres.div_const (⨅ i, (symmPart_isHermitian A).eigenvalues i)))

/-- **Lemma 6.31** of [saad2003iterative]. Let $A$ be a real $n \times n$ matrix, let
$b, x_0 \in \mathbb{R}^n$ with $r_0 = b - Ax_0$, and let $m$ be at most the grade of
$v_1 = r_0/\|r_0\|$, with the triangular factor $R_m$ of the Givens QR factorization of
$\bar H_m$ nonsingular. Then there is a polynomial $q_m$ of degree less than $m$ such that the
$m$-th GMRES iterate is
$$x_m = x_0 + q_m(A) r_0, \qquad b - Ax_m = (I - A q_m(A)) r_0,$$
and $q_m$ minimizes $\|(I - A q(A)) r_0\|_2$ over all polynomials $q$ of degree less than $m$.

The iterate $x_m$ is `SaadSparse.Chapter06.gmresFixed`, the GMRES iterate after exactly $m$
Arnoldi steps, and $R_m$ is `SaadSparse.Chapter06.R`. The two hypotheses make $x_m$ well
defined: the $m$ Arnoldi steps are completed, and the least-squares problem is solved by
$y_m = R_m^{-1} g_m$. -/
theorem lemma_6_31 (b x₀ : 𝔼) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ∃ q : ℝ[X], q.degree < m ∧
      gmresFixed A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) ∧
      ‖b - op A (gmresFixed A b x₀ m)‖ =
        ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (r₀ A b x₀)‖ ∧
      ∀ q' : ℝ[X], q'.degree < m →
        ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (r₀ A b x₀)‖ ≤
          ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q') (r₀ A b x₀)‖ := by
  have hx := gmresFixed_isMinResidualIterate A b x₀ hm hR
  obtain ⟨q, hq, hqe⟩ := (Krylov.mem_subspace_iff_exists_aeval (op A) (b - op A x₀)).1 hx.mem
  have hres : ∀ p : ℝ[X], b - op A (x₀ + Polynomial.aeval (op A) p (r₀ A b x₀)) =
      ((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) p) (r₀ A b x₀) := by
    intro p
    have hr : r₀ A b x₀ = b - op A x₀ := rfl
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply, map_add, hr]
    abel
  have hxeq : gmresFixed A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) :=
    sub_eq_iff_eq_add'.1 hqe.symm
  refine ⟨q, hq, hxeq, by rw [hxeq, hres q], fun q' hq' => ?_⟩
  rw [← hres q, ← hres q', ← hxeq]
  refine hx.min _ ?_
  rw [add_sub_cancel_left]
  exact Krylov.aeval_apply_mem_subspace (op A) _ hq'

end GMRESConvergence

/-! ### Proposition 6.32: diagonalizable matrices -/

section Diagonalizable

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

open scoped Matrix Matrix.Norms.L2Operator

/-- **Proposition 6.32** of [saad2003iterative], the quantity
$$\varepsilon^{(m)} = \min_{p \in \mathbb{P}_m,\ p(0) = 1} \ \max_{i} |p(\lambda_i)|$$
for complex numbers $\lambda_1, \dots, \lambda_n$, where $p$ ranges over the complex polynomials
of degree at most $m$ with $p(0) = 1$.

The minimum is an infimum. For $n = 0$ the maximum over the empty family is $0$, so
$\varepsilon^{(m)} = 0$. -/
noncomputable def epsMin (lam : Fin n → ℂ) (m : ℕ) : ℝ :=
  ⨅ p : {p : ℂ[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (lam i)‖

private theorem degree_one_le (m : ℕ) : (1 : ℂ[X]).degree ≤ (m : WithBot ℕ) :=
  Polynomial.natDegree_le_iff_degree_le.1 (by simp)

private instance nonempty_consistent (m : ℕ) :
    Nonempty {p : ℂ[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
  ⟨⟨1, degree_one_le m, by simp⟩⟩

private theorem aeval_diagonal (d : Fin n → ℂ) (p : ℂ[X]) :
    Polynomial.aeval (Matrix.diagonal d) p = Matrix.diagonal fun i => p.eval (d i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Matrix.diagonal_add]; simp
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Polynomial.eval_monomial]

private theorem aeval_conj {P Q D : Matrix (Fin n) (Fin n) ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (p : ℂ[X]) : Polynomial.aeval (P * D * Q) p = P * Polynomial.aeval D p * Q := by
  have hpow : ∀ k : ℕ, (P * D * Q) ^ k = P * D ^ k * Q := by
    intro k
    induction k with
    | zero => simp [hPQ]
    | succ k ih =>
      calc (P * D * Q) ^ (k + 1) = P * D ^ k * Q * (P * D * Q) := by rw [pow_succ, ih]
        _ = P * D ^ k * (Q * P) * D * Q := by simp only [mul_assoc]
        _ = P * D ^ (k + 1) * Q := by rw [hQP, mul_one, pow_succ, mul_assoc P (D ^ k) D]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hpow k]
    simp only [mul_assoc]
    rw [← mul_assoc, Algebra.commutes, mul_assoc]

private theorem norm_op_apply_le (A : Matrix (Fin n) (Fin n) ℂ) (x : 𝔼) :
    ‖op A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  exact (LinearMap.toContinuousLinearMap (op A)).le_opNorm x

private theorem norm_le_iSup (d : Fin n → ℂ) : ‖d‖ ≤ ⨆ i, ‖d i‖ :=
  (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg (d i))).2
    fun i => le_ciSup (Finite.bddAbove_range fun j => ‖d j‖) i

/-- Let $A = X \Lambda X^{-1}$ be a complex $n \times n$ matrix with $X$ nonsingular and $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$. Then for every polynomial $p$ and every
$y \in \mathbb{C}^n$,
$$\|p(A) y\|_2 \le \|X\|_2 \|X^{-1}\|_2 \max_i |p(\lambda_i)|\ \|y\|_2.$$

This is the surface ingredient of Proposition 6.32. The backbone's `norm_aeval_apply_le_of_conj`
covers the case of a symmetric diagonal factor; here $\Lambda$ is complex, and $p(\Lambda)$ is
the diagonal matrix with entries $p(\lambda_i)$. -/
theorem norm_aeval_diagonal_mulVec_le {A : Matrix (Fin n) (Fin n) ℂ}
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X) (lam : Fin n → ℂ)
    (hA : A = X * Matrix.diagonal lam * X⁻¹) (p : ℂ[X]) (y : 𝔼) :
    ‖Polynomial.aeval (op A) p y‖ ≤ ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖y‖ := by
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  have hp : Polynomial.aeval A p = X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹ := by
    rw [hA, aeval_conj (Matrix.mul_nonsing_inv X hdet) (Matrix.nonsing_inv_mul X hdet),
      aeval_diagonal]
  have hdiag : ‖Matrix.diagonal fun i => p.eval (lam i)‖ ≤ ⨆ i, ‖p.eval (lam i)‖ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact norm_le_iSup _
  have hsub : ‖X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹‖ ≤
      ‖X‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖X⁻¹‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hdiag (norm_nonneg X)))
      (norm_nonneg _))
  rw [← op_aeval, hp]
  calc ‖op (X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹) y‖
      ≤ ‖X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹‖ * ‖y‖ := norm_op_apply_le _ _
    _ ≤ ‖X‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖X⁻¹‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right hsub (norm_nonneg _)
    _ = ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖y‖ := by ring

/-- **Proposition 6.32** of [saad2003iterative]. Let $A = X \Lambda X^{-1}$ be a complex
$n \times n$ matrix with $X$ nonsingular and $\Lambda = \operatorname{diag}(\lambda_1, \dots,
\lambda_n)$. Let $b, x_0 \in \mathbb{C}^n$ with $r_0 = b - Ax_0$, and let $m$ be at most the
grade of $v_1 = r_0/\|r_0\|$, with the triangular factor $R_m$ of the Givens QR factorization of
$\bar H_m$ nonsingular. Then the residual of the $m$-th GMRES iterate $x_m$ satisfies
$$\|b - Ax_m\|_2 \le \kappa_2(X)\, \varepsilon^{(m)} \|r_0\|_2, \qquad \kappa_2(X) = \|X\|_2
  \|X^{-1}\|_2.$$

The iterate $x_m$ is `SaadSparse.Chapter06.gmresFixed`, and the hypotheses on $m$ and $R_m$ are
those of `SaadSparse.Chapter06.lemma_6_31`. -/
theorem proposition_6_32 {A : Matrix (Fin n) (Fin n) ℂ} (b x₀ : 𝔼) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (lam : Fin n → ℂ) (hA : A = X * Matrix.diagonal lam * X⁻¹) {m : ℕ}
    (hm : m ≤ grade A (v₁ A b x₀)) (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ ≤ ‖X‖ * ‖X⁻¹‖ * epsMin lam m * ‖r₀ A b x₀‖ := by
  have hx := gmresFixed_isMinResidualIterate A b x₀ hm hR
  have key : ∀ p : {p : ℂ[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1},
      ‖b - op A (gmresFixed A b x₀ m)‖ ≤
        ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * ⨆ i, ‖p.1.eval (lam i)‖ := by
    intro p
    calc ‖b - op A (gmresFixed A b x₀ m)‖ ≤ ‖Polynomial.aeval (op A) p.1 (r₀ A b x₀)‖ :=
          hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2
      _ ≤ ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.1.eval (lam i)‖) * ‖r₀ A b x₀‖ :=
          norm_aeval_diagonal_mulVec_le X hX lam hA p.1 (r₀ A b x₀)
      _ = ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * ⨆ i, ‖p.1.eval (lam i)‖ := by ring
  have hgoal : ‖b - op A (gmresFixed A b x₀ m)‖ ≤
      ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * epsMin lam m := le_mul_ciInf (by positivity) key
  exact hgoal.trans_eq (by rw [epsMin]; ring)

/-- **Corollary 6.33** of [saad2003iterative]. Let $A = X \Lambda X^{-1}$ be a complex $n \times n$
matrix with $X$ nonsingular and $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$.
Let $c, d \in \mathbb{C}$ with $d \neq 0$ and $\rho \ge 1$, and assume that all eigenvalues
$\lambda_i$ are enclosed in the ellipse $E(c, d, a)$ and that the region it encloses excludes
the origin. Let $b, x_0 \in \mathbb{C}^n$ with $r_0 = b - Ax_0$, and let $m$ be at most the
grade of $v_1 = r_0/\|r_0\|$, with $R_m$ nonsingular. Then the residual of the $m$-th GMRES
iterate $x_m$ satisfies
$$\|b - Ax_m\|_2 \le \kappa_2(X)\, \frac{C_m(a/d)}{|C_m(c/d)|}\, \|r_0\|_2, \qquad \frac{a}{d} =
  \frac{\rho + \rho^{-1}}{2}.$$

The region is `SaadSparse.Chapter06.filledEllipse c d ρ`. The book takes the spectrum inside the
ellipse, while (6.119)–(6.120) bound $|\hat C_m|$ on the ellipse. The step between the two,
which the book leaves implicit, is the maximum modulus principle on the filled ellipse,
`Polynomial.norm_eval_le_of_forall_mem_ellipse`. The hypothesis that the origin is outside makes
$C_m(c/d) \neq 0$, so that $\hat C_m$ with $\gamma = 0$ is a competitor in $\varepsilon^{(m)}$. -/
theorem corollary_6_33 {A : Matrix (Fin n) (Fin n) ℂ} (b x₀ : 𝔼) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (lam : Fin n → ℂ) (hA : A = X * Matrix.diagonal lam * X⁻¹) {c d : ℂ}
    (hd : d ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) (hlam : ∀ i, lam i ∈ filledEllipse c d ρ)
    (h0 : (0 : ℂ) ∉ filledEllipse c d ρ) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ ≤
      ‖X‖ * ‖X⁻¹‖ * ((C m).eval ((ρ + ρ⁻¹) / 2) / ‖(Ccomplex m).eval (c / d)‖) *
        ‖r₀ A b x₀‖ := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le one_pos hρ
  have hne : (Ccomplex m).eval ((c - 0) / d) ≠ 0 :=
    Polynomial.Chebyshev.eval_T_sub_div_ne_zero_of_notMem_filledEllipse m hρ hd h0
  have hbdd : BddAbove ((fun z => ‖(ChatComplex m c d 0).eval z‖) '' Set.ellipse c d ρ) :=
    ((Set.isCompact_ellipse c d hρ0).image
      (ChatComplex m c d 0).continuous.norm).bddAbove
  have hle : ∀ z ∈ Set.ellipse c d ρ,
      ‖(ChatComplex m c d 0).eval z‖ ≤
        sSup ((fun z => ‖(ChatComplex m c d 0).eval z‖) '' Set.ellipse c d ρ) :=
    fun z hz => le_csSup hbdd ⟨z, hz, rfl⟩
  have hMnonneg : 0 ≤ sSup ((fun z => ‖(ChatComplex m c d 0).eval z‖) '' Set.ellipse c d ρ) :=
    (norm_nonneg _).trans (hle _ (Set.vertex_mem_ellipse c d hρ0.le))
  -- `ε^{(m)}` is at most the maximum of `|Ĉ_m|` over the filled ellipse, hence over the ellipse
  have hchain : epsMin lam m ≤ (C m).eval ((ρ + ρ⁻¹) / 2) / ‖(Ccomplex m).eval (c / d)‖ := by
    have hMval : sSup ((fun z => ‖(ChatComplex m c d 0).eval z‖) '' ellipse c d ρ) =
        (C m).eval ((ρ + ρ⁻¹) / 2) / ‖(Ccomplex m).eval (c / d)‖ := by
      rw [ellipse_max_Chat m hρ hd hne, sub_zero]
    rw [← hMval]
    refine le_trans (ciInf_le ⟨0, ?_⟩
      ⟨ChatComplex m c d 0, Polynomial.Chebyshev.shiftedComplex_degree_le m c d 0,
        Polynomial.Chebyshev.shiftedComplex_eval_self m hd hne⟩) ?_
    · rintro y ⟨p, rfl⟩
      dsimp only
      exact Real.iSup_nonneg fun i => norm_nonneg _
    · exact Real.iSup_le
        (fun i => Polynomial.norm_eval_le_of_forall_mem_ellipse hρ hle (hlam i)) hMnonneg
  calc ‖b - op A (gmresFixed A b x₀ m)‖
      ≤ ‖X‖ * ‖X⁻¹‖ * epsMin lam m * ‖r₀ A b x₀‖ :=
        proposition_6_32 b x₀ X hX lam hA hm hR
    _ ≤ ‖X‖ * ‖X⁻¹‖ * ((C m).eval ((ρ + ρ⁻¹) / 2) / ‖(Ccomplex m).eval (c / d)‖) *
          ‖r₀ A b x₀‖ := by gcongr

end Diagonalizable

end SaadSparse.Chapter06
