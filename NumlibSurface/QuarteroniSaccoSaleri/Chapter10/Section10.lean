/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.FiniteDifference.Derivative
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 10.10: Approximation of function derivatives

This module formalizes Section 10.10 of [quarteroni2000numerical]. On the uniform grid
$x_k = a + kh$ the approximations $u_i$ of $f'(x_i)$ are the solutions of the difference scheme
(10.57),
$$h \sum_{k=-m}^{m} \alpha_k u_{i-k} = \sum_{k=-m'}^{m'} \beta_k f(x_{i-k}).$$
Section 10.10.1 treats the classical explicit choices: the forward, centred and backward differences
(10.59), (10.61) and (10.63) with their mean-value errors (10.60), (10.62) and (10.64), and the
second centred difference (10.65)–(10.66) for $f''$. Section 10.10.2 treats the implicit (compact)
family (10.67). The Taylor expansion of its consistency error (10.68) gives the order conditions
$2\alpha + 1 = \beta + \gamma$, $6\alpha = \beta + 4\gamma$ and $10\alpha = \beta + 16\gamma$, and
the unique scheme (10.69) of order six. Section 10.10.3 treats the pseudo-spectral derivative
$\mathcal{D}_n f = (\Pi^{GL}_{n,w} f)'$ at the Chebyshev–Gauss–Lobatto nodes of (10.21), with the
differentiation matrix (10.72)–(10.73).

The proofs specialize `Numlib.FiniteDifference.Derivative`: the difference quotients
`FiniteDifference.forwardDiff`, `FiniteDifference.backwardDiff`, `FiniteDifference.centredDiff` and
`FiniteDifference.secondCentredDiff` with their mean-value errors, the consistency error
`FiniteDifference.compactError` with `FiniteDifference.compactError_expansion`, and the
differentiation matrix `Lagrange.derivMatrix` with `Lagrange.eval_derivative_interpolate_node` and
`Lagrange.chebyshevLobattoDerivMatrix_apply`.

## Main definitions

* Equation (10.57), `QuarteroniSaccoSaleri.Chapter10.equation_10_57`: the difference scheme, as a
  relation at one index $i$ between $u : \mathbb{Z} \to \mathbb{R}$ and the nodal values of $f$.
* Section 10.10.3, `QuarteroniSaccoSaleri.Chapter10.pseudoSpectralDerivative`: the pseudo-spectral
  derivative $\mathcal{D}_n f$, the derivative of the interpolant of $f$ at the nodes of (10.21).

## Main results

* Equations (10.59)–(10.60), `QuarteroniSaccoSaleri.Chapter10.equation_10_60`: the forward
  difference is an instance of (10.57), with error $-(h/2) f''(\xi_i)$.
* Equations (10.61)–(10.62), `QuarteroniSaccoSaleri.Chapter10.equation_10_62`: the centred
  difference is an instance of (10.57), with error $-(h^2/6) f'''(\xi_i)$.
* Equations (10.63)–(10.64), `QuarteroniSaccoSaleri.Chapter10.equation_10_64`: the backward
  difference is an instance of (10.57), with error $(h/2) f''(\xi_i)$.
* Equations (10.65)–(10.66), `QuarteroniSaccoSaleri.Chapter10.equation_10_66`: the error of the
  second centred difference.
* Equations (10.67)–(10.68), `QuarteroniSaccoSaleri.Chapter10.equation_10_68`: the consistency error
  of the compact scheme and its Taylor expansion up to $O(h^6)$.
* Equation (10.69), `QuarteroniSaccoSaleri.Chapter10.equation_10_69`: the order conditions and the
  unique compact scheme of order six.
* Section 10.10.3, `QuarteroniSaccoSaleri.Chapter10.degree_pseudoSpectralDerivative_lt`:
  $\mathcal{D}_n f \in \mathbb{P}_{n-1}$.
* Equation (10.72), `QuarteroniSaccoSaleri.Chapter10.equation_10_72`: $(\mathcal{D}_n f)(\bar x_i) =
  \sum_j f(\bar x_j) \bar l_j'(\bar x_i)$, that is $f' = Df$ at the nodes, and $D^2 f = D(Df)$.
* Equation (10.73), `QuarteroniSaccoSaleri.Chapter10.equation_10_73`: the entries of $D$.

## Conventions

* As in Section 10.3, the Chebyshev–Gauss–Lobatto nodes are the book's $\bar x_j = -\cos(j\pi/n)$
  (`QuarteroniSaccoSaleri.Chapter10.chebyshevLobattoNode`). They are the negatives of Mathlib's
  `Polynomial.Chebyshev.node`, so the differentiation matrix at the book's nodes is the negative of
  the backbone's matrix (`Lagrange.derivMatrix_neg`).
* The grid is $x_k = a + kh$ with $k \in \mathbb{Z}$ and any step $h > 0$. The book sets
  $h = (b - a)/n$.

## Implementation notes

* The estimate (10.71) needs two further tools. The derivative of the projection error is estimated
  by the Sturm–Liouville argument of (10.22), one order lower. The Chebyshev coefficients of
  $(P_n f)'$ are sums of the type $\sum_{k > n,\, k - j \text{ odd}} 2k \hat f_k$, and the Legendre
  coefficients are $\sum_{k > n,\, k - j \text{ odd}} (2j + 1) \hat f_k$; the identity behind them
  is `Polynomial.integral_derivative_legendre_mul_legendre`. The derivative of the aliasing error
  $\Pi_n f - P_n f \in \mathbb{P}_n$ is estimated by the inverse (Markov) inequality
  $\|p'\|_w \le C n^2 \|p\|_w$ on $\mathbb{P}_n$. Its Legendre case, with the constant $n(n+1)$, is
  `Polynomial.integral_derivative_sq_le`; the case of the Chebyshev weight is not in the library.
  Only a bound of Marcinkiewicz–Zygmund type $\|\Pi_n g\|_w \le C (\|g\|_w + n^{-1} \|g'\|_w)$ makes
  the inverse inequality cost exactly one power of $n$ and gives the printed $n^{1-m}$. With the
  elementary aliasing bound $n^{1/2-m}$ of Section 10.3, the derivative estimate is only
  $n^{5/2-m}$.

## Deviations from the source

* **Equations (10.57), (10.59)–(10.64)** (generalization). The stencil can be placed at any
  integer index on an infinite grid. The Taylor remainder results assume positive spacing and
  explicit smoothness on the stencil. The one-sided formulas also assume differentiability at
  the endpoint where Lean uses the unrestricted derivative.
* **Equations (10.68)–(10.69)** (reading). `equation_10_68` and `equation_10_69` use $C^7$ near
  the expansion point for their sixth-order remainder statements. The printed Taylor argument
  starts with $C^5([a,b])$.
* **Section 10.10.3 and equation (10.72)** (generalization). The pseudo-spectral derivative and
  its matrix formula allow arbitrary nodal data and $n=0$. The degree bound for positive $n$ is
  $\leq n-1$. The last clause of `equation_10_72` states matrix associativity for $D^2v=D(Dv)$,
  without identifying either side with direct evaluation of the second derivative of the
  interpolation polynomial.
* **The expansion of the consistency error in Section 10.10.2** (typo). The printed expansion has a
  spurious factor $1/2$ on both $h^2$ terms. The order conditions that the book derives from it are
  correct. See `QuarteroniSaccoSaleri.Chapter10.equation_10_68`.
* **Equation (10.68)** (typo). The display prints $-\alpha f_{i+1}^{(1)}$ where (10.67) has
  $+\alpha u_{i+1}$. See `QuarteroniSaccoSaleri.Chapter10.equation_10_68`.
* **Equations (10.65)–(10.66)** (generalization). The book assumes $f \in C^4([a, b])$. The library
  assumes only that $f$ is of class $C^4$ on $[x_{i-1}, x_{i+1}]$. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_66`.

## Not formalized

* **Equation (10.71)**, the estimate $\|f' - \mathcal{D}_n f\|_w \le C n^{1-m} \|f\|_{m,w}$ for
  $m \ge 2$, with the norm (10.23). The book quotes it from Canuto, Hussaini, Quarteroni and Zang
  (1988) without proof. It is the $H^1$ form of (10.22), and it depends on the spectral
  approximation estimates that `NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03` does not
  formalize.
* **The discussion of wave numbers in Section 10.10.2.** It is prose.
* **The boundary closure of the compact scheme.** It is prose.
* **Example 10.4.** It is a numerical experiment.
-/

open Asymptotics Filter Matrix Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {a h : ℝ} {f : ℝ → ℝ} {i : ℤ} {n : ℕ}

/-! ### Equation (10.57): the general difference scheme -/

/-- **Equation (10.57)** of [quarteroni2000numerical]. Let $m, m' \in \mathbb{N}$, let
$\alpha, \beta : \mathbb{Z} \to \mathbb{R}$ be coefficients, let
$f : \mathbb{R} \to \mathbb{R}$, $a, h \in \mathbb{R}$, and let $x_k = a + kh$. A sequence
$u : \mathbb{Z} \to \mathbb{R}$ of approximations of $f'(x_k)$ **satisfies the difference
scheme** at the index $i \in \mathbb{Z}$ if
$$h \sum_{k=-m}^{m} \alpha_k u_{i-k} = \sum_{k=-m'}^{m'} \beta_k f(x_{i-k}).$$

The predicate is stated at one index $i$, where the whole stencil is available. If $m \neq 0$,
the values $u_i$ are the solution of a linear system.

**Generalization.** The stencil is defined at any integer index and real spacing. The source
starts with a finite positive-spacing grid. -/
def equation_10_57 (m m' : ℕ) (α β : ℤ → ℝ) (f : ℝ → ℝ) (a h : ℝ) (u : ℤ → ℝ) (i : ℤ) : Prop :=
  h * ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), α k * u (i - k)
    = ∑ k ∈ Finset.Icc (-(m' : ℤ)) (m' : ℤ), β k * f (a + ((i - k : ℤ) : ℝ) * h)

/-- A sum over the integers $k$ with $0 \le k \le 0$ is the term at $k = 0$. -/
private theorem sum_icc_zero (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ), g k = g 0 := by
  rw [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]

/-- A sum over the integers $k$ with $-1 \le k \le 1$ is the sum of the terms at $k = -1, 0, 1$. -/
private theorem sum_icc_one (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ), g k = g (-1) + g 0 + g 1 := by
  rw [Nat.cast_one, show Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-! ### Section 10.10.1: classical finite difference methods -/

/-- **Equations (10.59)–(10.60)** of [quarteroni2000numerical], the forward difference. Let $h > 0$,
$a \in \mathbb{R}$, $i \in \mathbb{Z}$ and $x_k = a + kh$. Let $f : \mathbb{R} \to \mathbb{R}$
be of class $C^2$ on $[x_i, x_{i+1}]$ and differentiable at $x_i$. The approximations
$u^{FD}_k = (f(x_{k+1}) - f(x_k))/h$ satisfy the scheme (10.57) at $i$ with $m = 0$,
$\alpha_0 = 1$, $m' = 1$, $\beta_{-1} = 1$, $\beta_0 = -1$ and $\beta_1 = 0$. Moreover there is
$\xi_i \in (x_i, x_{i+1})$ with
$$f'(x_i) - u^{FD}_i = -\frac{h}{2} f''(\xi_i).$$

The coefficients $\alpha_k$ and $\beta_k$ that the statement does not list are $0$. The quotient
is `FiniteDifference.forwardDiff`.

**Reading.** The theorem uses positive spacing, smoothness on the one-sided stencil, and
differentiability at the endpoint of that stencil to use the ordinary derivative there. -/
theorem equation_10_60 (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (a + i * h) (a + i * h + h)))
    (hd : DifferentiableAt ℝ f (a + i * h)) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 1 else if k = 0 then -1 else 0) f a h
        (fun j => FiniteDifference.forwardDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h) (a + i * h + h),
        deriv f (a + i * h) - FiniteDifference.forwardDiff f h (a + i * h)
          = -(h / 2) * iteratedDeriv 2 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_forwardDiff_eq hh hf hd⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.forwardDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) + 1) * h = a + i * h + h by ring]
  field_simp
  ring

/-- **Equations (10.61)–(10.62)** of [quarteroni2000numerical], the centred difference. Let $h > 0$,
$a \in \mathbb{R}$, $i \in \mathbb{Z}$ and $x_k = a + kh$. Let $f : \mathbb{R} \to \mathbb{R}$
be of class $C^3$ on $[x_{i-1}, x_{i+1}]$. The approximations
$u^{CD}_k = (f(x_{k+1}) - f(x_{k-1}))/(2h)$ satisfy the scheme (10.57) at $i$ with $m = 0$,
$\alpha_0 = 1$, $m' = 1$, $\beta_{-1} = 1/2$, $\beta_0 = 0$ and $\beta_1 = -1/2$. Moreover there
is $\xi_i \in (x_{i-1}, x_{i+1})$ with
$$f'(x_i) - u^{CD}_i = -\frac{h^2}{6} f'''(\xi_i),$$
so the centred difference is a second-order approximation of $f'(x_i)$.

The coefficients $\alpha_k$ and $\beta_k$ that the statement does not list are $0$. The quotient
is `FiniteDifference.centredDiff`.

**Reading.** The smoothness assumption applies on the local two-sided stencil, and the mean-
value point lies in its interior. -/
theorem equation_10_62 (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc (a + i * h - h) (a + i * h + h))) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 1 / 2 else if k = 0 then 0 else -(1 / 2)) f a h
        (fun j => FiniteDifference.centredDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h - h) (a + i * h + h),
        deriv f (a + i * h) - FiniteDifference.centredDiff f h (a + i * h)
          = -(h ^ 2 / 6) * iteratedDeriv 3 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_centredDiff_eq hh hf⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.centredDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) + 1) * h = a + i * h + h by ring,
    show a + ((i : ℝ) - 1) * h = a + i * h - h by ring]
  field_simp
  ring

/-- **Equations (10.63)–(10.64)** of [quarteroni2000numerical], the backward difference. Let
$h > 0$, $a \in \mathbb{R}$, $i \in \mathbb{Z}$ and $x_k = a + kh$. Let
$f : \mathbb{R} \to \mathbb{R}$ be of class $C^2$ on $[x_{i-1}, x_i]$ and differentiable at
$x_i$. The approximations $u^{BD}_k = (f(x_k) - f(x_{k-1}))/h$ satisfy the scheme (10.57) at $i$
with $m = 0$, $\alpha_0 = 1$, $m' = 1$, $\beta_{-1} = 0$, $\beta_0 = 1$ and $\beta_1 = -1$.
Moreover there is $\xi_i \in (x_{i-1}, x_i)$ with
$$f'(x_i) - u^{BD}_i = \frac{h}{2} f''(\xi_i).$$

The coefficients $\alpha_k$ and $\beta_k$ that the statement does not list are $0$. The quotient
is `FiniteDifference.backwardDiff`.

**Reading.** The theorem uses positive spacing, smoothness on the one-sided stencil, and
differentiability at the endpoint of that stencil to use the ordinary derivative there. -/
theorem equation_10_64 (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (a + i * h - h) (a + i * h)))
    (hd : DifferentiableAt ℝ f (a + i * h)) :
    equation_10_57 0 1 (fun k => if k = 0 then 1 else 0)
        (fun k => if k = -1 then 0 else if k = 0 then 1 else -1) f a h
        (fun j => FiniteDifference.backwardDiff f h (a + j * h)) i ∧
      ∃ ξ ∈ Ioo (a + i * h - h) (a + i * h),
        deriv f (a + i * h) - FiniteDifference.backwardDiff f h (a + i * h)
          = (h / 2) * iteratedDeriv 2 f ξ := by
  refine ⟨?_, FiniteDifference.deriv_sub_backwardDiff_eq hh hf hd⟩
  rw [equation_10_57, sum_icc_zero, sum_icc_one]
  simp only [FiniteDifference.backwardDiff_apply, sub_zero, sub_neg_eq_add]
  norm_num
  rw [show a + ((i : ℝ) - 1) * h = a + i * h - h by ring]
  field_simp
  ring

/-- **Equations (10.65)–(10.66)** of [quarteroni2000numerical], the second centred difference. Let
$h > 0$, $a \in \mathbb{R}$, $i \in \mathbb{Z}$ and $x_k = a + kh$. Let
$f : \mathbb{R} \to \mathbb{R}$ be of class $C^4$ on $[x_{i-1}, x_{i+1}]$. Then the
approximation $u''_i = (f(x_{i+1}) - 2f(x_i) + f(x_{i-1}))/h^2$ of $f''(x_i)$ satisfies, for
some $\theta_i, \omega_i \in (0, 1)$,
$$f''(x_i) - u''_i = -\frac{h^2}{24} \bigl(f^{(4)}(x_i + \theta_i h) + f^{(4)}(x_i - \omega_i
  h)\bigr),$$
so it is a second-order approximation of $f''(x_i)$.

**Generalization.** The book assumes $f \in C^4([a, b])$. Here $f$ needs to be of class $C^4$
only on $[x_{i-1}, x_{i+1}]$.

The quotient is `FiniteDifference.secondCentredDiff`. -/
theorem equation_10_66 (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (a + i * h - h) (a + i * h + h))) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∃ ω ∈ Ioo (0 : ℝ) 1,
      iteratedDeriv 2 f (a + i * h) - FiniteDifference.secondCentredDiff f h (a + i * h)
        = -(h ^ 2 / 24) * (iteratedDeriv 4 f (a + i * h + θ * h)
          + iteratedDeriv 4 f (a + i * h - ω * h)) :=
  FiniteDifference.iteratedDeriv_two_sub_secondCentredDiff_eq hh hf

/-! ### Section 10.10.2: compact finite differences -/

/-- **Equations (10.67)–(10.68)** of [quarteroni2000numerical], with the expansion of the
consistency error. Let $\alpha, \beta, \gamma, x \in \mathbb{R}$, and write
$f_{i+k} = f(x + kh)$ and $f^{(1)}_{i+k} = f'(x + kh)$. The compact scheme
$$\alpha u_{i-1} + u_i + \alpha u_{i+1} = \frac{\beta}{2h} (f_{i+1} - f_{i-1}) +
  \frac{\gamma}{4h} (f_{i+2} - f_{i-2})$$
has the consistency error, obtained when $f'$ is put in place of $u$,
$$\sigma_i(h) = \alpha f^{(1)}_{i-1} + f^{(1)}_i + \alpha f^{(1)}_{i+1} - \Bigl(\frac{\beta}{2h}
  (f_{i+1} - f_{i-1}) + \frac{\gamma}{4h} (f_{i+2} - f_{i-2})\Bigr)$$
for every $h$. If $f$ is of class $C^7$ at $x$, then as $h \to 0$ with $h \neq 0$
$$\sigma_i(h) = (2\alpha + 1 - \beta - \gamma) f^{(1)}_i + h^2 \Bigl(\alpha - \frac{\beta}{6} -
  \frac{2\gamma}{3}\Bigr) f^{(3)}_i + h^4 \Bigl(\frac{\alpha}{12} - \frac{\beta}{120} -
  \frac{2\gamma}{15}\Bigr) f^{(5)}_i + O(h^6).$$

**Typo.** The display (10.68) prints $-\alpha f^{(1)}_{i+1}$ for the term $+\alpha u_{i+1}$ of
(10.67). The two $h^2$ terms of the printed expansion carry a spurious factor $1/2$. The order
conditions that the book derives from the expansion are correct.

The consistency error is `FiniteDifference.compactError`. At $h = 0$ the quotients use the Lean
convention $0^{-1} = 0$. The expansion is `FiniteDifference.compactError_expansion`, stated with
`Asymptotics.IsBigO` along the punctured neighbourhood of $0$.

**Reading.** The sixth-order error bound uses $C^7$ near the expansion point. The source starts
its Taylor argument with $C^5([a,b])$. -/
theorem equation_10_68 {α β γ x : ℝ} (hf : ContDiffAt ℝ 7 f x) :
    (∀ h : ℝ, FiniteDifference.compactError α β γ f x h
        = α * deriv f (x - h) + deriv f x + α * deriv f (x + h)
          - (β / (2 * h) * (f (x + h) - f (x - h))
            + γ / (4 * h) * (f (x + 2 * h) - f (x - 2 * h)))) ∧
      (fun h => FiniteDifference.compactError α β γ f x h
          - ((2 * α + 1 - β - γ) * deriv f x
            + h ^ 2 * (α - β / 6 - 2 * γ / 3) * iteratedDeriv 3 f x
            + h ^ 4 * (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x))
        =O[𝓝[≠] 0] fun h => h ^ 6 :=
  ⟨fun _ => rfl, FiniteDifference.compactError_expansion hf⟩

/-- **Equation (10.69)** of [quarteroni2000numerical], with the order conditions of Section 10.10.2.
Let $\alpha, \beta, \gamma, x \in \mathbb{R}$, and let $f : \mathbb{R} \to \mathbb{R}$ be of
class $C^7$ at $x$. Setting the coefficients of $f^{(1)}_i$, $f^{(3)}_i$ and $f^{(5)}_i$ in the
expansion of the consistency error to zero gives the conditions $2\alpha + 1 = \beta + \gamma$
(order 2), $6\alpha = \beta + 4\gamma$ (order 4) and $10\alpha = \beta + 16\gamma$ (order 6). If
all three conditions hold, then:
* the consistency error is $\sigma_i(h) = O(h^6)$ as $h \to 0$, $h \neq 0$;
* $\alpha = 1/3$, $\beta = 14/9$ and $\gamma = 1/9$, so the scheme of order six is unique;
* the fourth-order scheme $\alpha = 1/4$, $\beta = 3/2$, $\gamma = 0$ has
  $\sigma_i(h) = O(h^4)$;
* the scheme $\alpha = \gamma = 0$, $\beta = 1$ has $\sigma_i(h) = f'(x) - (f(x + h) - f(x -
  h))/(2h)$ for every $h$, which is the error of the centred difference (10.61).

The last two conclusions do not use the three conditions, but the Lean statement has them as
hypotheses of the whole theorem.

The book also remarks that there are infinitely many schemes of order 2 and of order 4, and that
the traditional finite differences are the case $\alpha = 0$. These remarks are not stated here
beyond the two schemes above.

**Reading.** The sixth-order error bound uses $C^7$ near the expansion point. The source starts
its Taylor argument with $C^5([a,b])$. -/
theorem equation_10_69 {α β γ x : ℝ} (h₁ : 2 * α + 1 = β + γ) (h₂ : 6 * α = β + 4 * γ)
    (h₃ : 10 * α = β + 16 * γ) (hf : ContDiffAt ℝ 7 f x) :
    ((fun h => FiniteDifference.compactError α β γ f x h) =O[𝓝[≠] 0] fun h => h ^ 6) ∧
      (α = 1 / 3 ∧ β = 14 / 9 ∧ γ = 1 / 9) ∧
      ((fun h => FiniteDifference.compactError (1 / 4) (3 / 2) 0 f x h)
        =O[𝓝[≠] 0] fun h => h ^ 4) ∧
      ∀ h : ℝ, FiniteDifference.compactError 0 1 0 f x h
        = deriv f x - FiniteDifference.centredDiff f h x :=
  ⟨FiniteDifference.compactError_isBigO_pow_six h₁ h₂ h₃ hf,
    FiniteDifference.order_six_unique h₁ h₂ h₃,
    FiniteDifference.compactError_isBigO_pow_four (by norm_num) (by norm_num) hf,
    fun h => FiniteDifference.compactError_zero_one_zero h⟩

/-! ### Section 10.10.3: the pseudo-spectral derivative -/

/-- **Section 10.10.3** of [quarteroni2000numerical], the pseudo-spectral derivative. For
$n \in \mathbb{N}$ and $f : \mathbb{R} \to \mathbb{R}$, the **pseudo-spectral derivative**
$\mathcal{D}_n f = (\Pi^{GL}_{n,w} f)'$ is the derivative of the polynomial that interpolates
$f$ at the $n + 1$ Chebyshev–Gauss–Lobatto nodes $\bar x_j = -\cos(j\pi/n)$, $j = 0, \dots, n$,
of (10.21).

The book takes $f \in C^0([-1, 1])$. The definition uses only the values of $f$ at the nodes.
The interpolant is `Lagrange.interpolate` at the nodes
`QuarteroniSaccoSaleri.Chapter10.chebyshevLobattoNode n j`.

**Generalization.** Extends the algebraic derivative of the interpolant to all nodal data and
$n=0$. -/
noncomputable def pseudoSpectralDerivative (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  derivative (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
    fun j => f (chebyshevLobattoNode n j))

/-- **Section 10.10.3** of [quarteroni2000numerical], the degree of the pseudo-spectral derivative.
For $n \ge 1$ and $f : \mathbb{R} \to \mathbb{R}$, the polynomial $\mathcal{D}_n f$ has degree
less than $n$, that is $\mathcal{D}_n f \in \mathbb{P}_{n-1}$.

**Reading.** The degree is at most $n-1$ and can be lower. The source calls it a polynomial of
degree $n-1$. -/
theorem degree_pseudoSpectralDerivative_lt (hn : n ≠ 0) (f : ℝ → ℝ) :
    (pseudoSpectralDerivative n f).degree < (n : ℕ) := by
  have hdq : (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hd := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1))))
      (v := fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      (r := fun j : Fin (n + 1) => f (chebyshevLobattoNode n j))
      (injective_chebyshevLobattoNode hn).injOn
    simpa using hd
  rw [pseudoSpectralDerivative]
  rcases eq_or_ne (Lagrange.interpolate Finset.univ
      (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)) 0 with h0 | h0
  · rw [h0, derivative_zero, degree_zero]
    simp
  · rw [degree_eq_natDegree h0] at hdq
    have h1 : (Lagrange.interpolate Finset.univ
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)).natDegree < n + 1 := by exact_mod_cast hdq
    refine lt_of_lt_of_le (degree_derivative_lt h0) ?_
    rw [degree_eq_natDegree h0]
    exact_mod_cast Nat.lt_succ_iff.mp h1

/-- **Equation (10.72)** of [quarteroni2000numerical], the pseudo-spectral differentiation matrix.
Let $n \in \mathbb{N}$, $f : \mathbb{R} \to \mathbb{R}$, and let $\bar l_0, \dots, \bar l_n$ be
the Lagrange basis polynomials at the nodes $\bar x_0, \dots, \bar x_n$. For $i = 0, \dots, n$
the value of $\mathcal{D}_n f$ at a node is
$$(\mathcal{D}_n f)(\bar x_i) = \sum_{j=0}^{n} f(\bar x_j) \bar l_j'(\bar x_i).$$
With the matrix $D_{ij} = \bar l_j'(\bar x_i)$ this is $f' = Df$, where $f$ and $f'$ are the
vectors of the nodal values of $f$ and of $\mathcal{D}_n f$. The second-order pseudo-spectral
derivative is $D^2 f = D(Df)$ for every vector $f$.

The matrix $D$ is `Lagrange.derivMatrix` at the nodes.

**Generalization.** The first-derivative formula holds for all nodal data and includes $n=0$.
The final identity uses matrix associativity. It does not identify the result with the nodal
values of the second derivative of the interpolant. -/
theorem equation_10_72 (n : ℕ) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
        = ∑ j : Fin (n + 1), f (chebyshevLobattoNode n j)
          * (derivative (Lagrange.basis Finset.univ
              (fun j : Fin (n + 1) => chebyshevLobattoNode n j) j)).eval
              (chebyshevLobattoNode n i) ∧
      (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
        = (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
            *ᵥ fun j => f (chebyshevLobattoNode n j)) i ∧
      ∀ v : Fin (n + 1) → ℝ,
        Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ^ 2 *ᵥ v
          = Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
            *ᵥ (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) *ᵥ v) := by
  have hmat : (pseudoSpectralDerivative n f).eval (chebyshevLobattoNode n i)
      = (Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
          *ᵥ fun j => f (chebyshevLobattoNode n j)) i :=
    by
      rw [pseudoSpectralDerivative]
      exact Lagrange.eval_derivative_interpolate_node
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        (fun j => f (chebyshevLobattoNode n j)) i
  refine ⟨?_, hmat, fun v => ?_⟩
  · rw [hmat, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [Lagrange.derivMatrix_apply, mul_comm]
  · rw [sq, Matrix.mulVec_mulVec]

/-- **Equation (10.73)** of [quarteroni2000numerical], the entries of $D$. Let $n \ge 1$, let
$\bar x_j = -\cos(j\pi/n)$ be the Chebyshev–Gauss–Lobatto nodes, and let $d_0 = d_n = 2$ and
$d_j = 1$ for $0 < j < n$ be the factors of Section 10.3. Then for $0 \le l, j \le n$
$$D_{lj} = \begin{cases} \dfrac{d_l}{d_j} \dfrac{(-1)^{l+j}}{\bar x_l - \bar x_j} & l \neq j,
  \\[1ex] -\dfrac{\bar x_j}{2(1 - \bar x_j^2)} & 1 \le l = j \le n - 1, \\[1ex] -\dfrac{2n^2 +
  1}{6} & l = j = 0, \\[1ex] \dfrac{2n^2 + 1}{6} & l = j = n. \end{cases}$$

The factor $d_j$ is `Polynomial.Chebyshev.lobattoFactor n j`. The proof specializes
`Lagrange.chebyshevLobattoDerivMatrix_apply`. -/
theorem equation_10_73 (hn : n ≠ 0) (l j : Fin (n + 1)) :
    Lagrange.derivMatrix (fun j : Fin (n + 1) => chebyshevLobattoNode n j) l j
      = if l = j then
          (if (j : ℕ) = 0 then -((2 * (n : ℝ) ^ 2 + 1) / 6)
            else if (j : ℕ) = n then (2 * (n : ℝ) ^ 2 + 1) / 6
            else -chebyshevLobattoNode n j / (2 * (1 - chebyshevLobattoNode n j ^ 2)))
        else Chebyshev.lobattoFactor n l / Chebyshev.lobattoFactor n j * (-1) ^ ((l : ℕ) + j)
          / (chebyshevLobattoNode n l - chebyshevLobattoNode n j) := by
  have hneg : (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      = -fun j : Fin (n + 1) => Chebyshev.node n j := by
    funext k
    simp [chebyshevLobattoNode, Chebyshev.node]
  have hval : ∀ k : Fin (n + 1), chebyshevLobattoNode n k = -Chebyshev.node n k := fun k => by
    simp [chebyshevLobattoNode, Chebyshev.node]
  rw [hneg, Lagrange.derivMatrix_neg, Matrix.neg_apply,
    Lagrange.chebyshevLobattoDerivMatrix_apply hn]
  simp only [hval, neg_sub_neg, neg_neg, neg_sq]
  split_ifs
  · ring
  · ring
  · ring
  · rw [← neg_sub (Chebyshev.node n l) (Chebyshev.node n j), div_neg]

end QuarteroniSaccoSaleri.Chapter10
