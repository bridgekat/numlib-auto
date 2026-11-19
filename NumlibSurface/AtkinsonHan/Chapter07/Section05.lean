/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Numlib.Analysis.Fourier.Aliasing
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Analysis.Sobolev.Periodic.Smooth
import Numlib.Approximation.MvPolynomial

/-!
# Atkinson and Han, Section 7.5: Periodic Sobolev spaces

This module formalizes Sections 7.5.1–7.5.3 of [han2009theoretical], together with Definition 7.5.8
and the minimax error (7.5.30) of Section 7.5.5. The source defines the periodic Sobolev space
$H^s(2\pi)$, for real $s$, by the decay of Fourier coefficients. A formal series
$\varphi = \sum_{m \in \mathbb{Z}} a_m \psi_m$ with $\psi_m(x) = (2\pi)^{-1/2} e^{imx}$ belongs to
$H^s(2\pi)$ when
$$\|\varphi\|_{*,s}^2 = |a_0|^2 + \sum_{|m| > 0} |m|^{2s} |a_m|^2 < \infty.$$
So $H^s(2\pi)$ is a weighted $\ell^2(\mathbb{Z})$, and no domain, boundary or weak derivative
enters. The module proves the characterization of $H^s(2\pi)$ and its equivalence with the classical
norm for integer $s$, the embedding into continuous functions for $s > 1/2$, the density and
compactness of the inclusions $H^s(2\pi) \subseteq H^t(2\pi)$ for $s > t$, the error bounds of the
trapezoidal rule, of Simpson's rule and of trigonometric interpolation, the duality of
$H^{-t}(2\pi)$ with $H^t(2\pi)$, and the convergence of the best approximation by spherical
polynomials on the unit sphere of $\mathbb{R}^3$.

The space $H^s(2\pi)$ is `PeriodicSobolev s` of `Numlib.Analysis.Sobolev.Periodic`. The
interpolation bound uses the aliasing argument of `Numlib.Analysis.Fourier.Aliasing`, and the
spherical polynomials use `Numlib.Approximation.MvPolynomial`.

## Main definitions

* Equation (7.5.1), `AtkinsonHan.Chapter07.psi` and `AtkinsonHan.Chapter07.eval`: the orthonormal
  functions $\psi_m(x) = (2\pi)^{-1/2} e^{imx}$ and the sum $\varphi(x) = \sum_m a_m \psi_m(x)$ of a
  series.
* Definition 7.5.1, `PeriodicSobolev`, with `AtkinsonHan.Chapter07.definition_7_5_1_norm` and
  `AtkinsonHan.Chapter07.definition_7_5_1_inner`: the space $H^s(2\pi)$, its norm (7.5.2) and its
  inner product.
* Equation (7.5.12), `AtkinsonHan.Chapter07.trapezoid`: the trapezoidal rule
  $T_k(\varphi) = h \sum_{j=1}^k \varphi(jh)$ with $h = 2\pi / k$.
* Definition 7.5.8, `AtkinsonHan.Chapter07.definition_7_5_8`: the space $\mathbb{S}_N$ of spherical
  polynomials of degree at most $N$ on the unit sphere $U \subseteq \mathbb{R}^3$.
* Equation (7.5.30), `AtkinsonHan.Chapter07.equation_7_5_30`: the minimax error $\rho_N(g) = \inf_{p
  \in \mathbb{S}_N} \|g - p\|_\infty$ for $g \in C(U)$.

## Main results

* Theorem 7.5.2, `AtkinsonHan.Chapter07.theorem_7_5_2`: $H^s(2\pi)$ is the set of series (7.5.1)
  with $\|\varphi\|_{*,s} < \infty$.
* Theorem 7.5.2, `AtkinsonHan.Chapter07.theorem_7_5_2_norm_equiv` and
  `AtkinsonHan.Chapter07.theorem_7_5_2_smooth`: for an integer $k \ge 0$, $\|\varphi\|_{*,k}^2 \le
  \|\varphi\|_{H^k}^2 \le (k + 1) \|\varphi\|_{*,k}^2$, on the coefficient side and for a
  $2\pi$-periodic $C^k$ function.
* Proposition 7.5.4, `AtkinsonHan.Chapter07.proposition_7_5_4_bound` and
  `AtkinsonHan.Chapter07.proposition_7_5_4`: for $s > 1/2$ the series (7.5.1) converges to a
  continuous $2\pi$-periodic function, with the bounds (7.5.10) and (7.5.11).
* Proposition 7.5.5, `AtkinsonHan.Chapter07.proposition_7_5_5`: for $s > t$ the inclusion
  $H^s(2\pi) \to H^t(2\pi)$ has dense range and is compact.
* Proposition 7.5.6, `AtkinsonHan.Chapter07.proposition_7_5_6`: the trapezoidal rule satisfies
  $|I(\varphi) - T_k(\varphi)| \le \sqrt{4\pi\zeta(2s)} \, k^{-s} \|\varphi\|_{*,s}$ (7.5.13).
* Theorem 7.5.7, `AtkinsonHan.Chapter07.theorem_7_5_7`: the trigonometric interpolant satisfies
  $\|\varphi - \mathcal{I}_n \varphi\|_{*,r} \le \sqrt{1 + 2\zeta(2s)} \, n^{r-s} \|\varphi\|_{*,s}$
  for $0 \le r \le s$ and $s > 1/2$ (7.5.15).
* Equation (7.5.30), `AtkinsonHan.Chapter07.equation_7_5_30_tendsto_zero`: $\rho_N(g) \to 0$ for
  every $g \in C(U)$.
* Exercise 7.5.1, `AtkinsonHan.Chapter07.exercise_7_5_1`: the proof of Proposition 7.5.5.
* Exercise 7.5.2, `AtkinsonHan.Chapter07.exercise_7_5_2`: the trigonometric polynomials are dense in
  $H^s(2\pi)$ for every real $s$.
* Exercise 7.5.3, `AtkinsonHan.Chapter07.exercise_7_5_3`: Simpson's rule satisfies the bound
  (7.5.13) with the constant $\frac{5}{3} \sqrt{4\pi\zeta(2s)}$.
* Exercise 7.5.4, `AtkinsonHan.Chapter07.exercise_7_5_4`: every $\eta \in H^{-t}(2\pi)$ is a bounded
  linear functional on $H^t(2\pi)$ under the pairing (7.5.6), of norm at most $\|\eta\|_{*,-t}$.

## Notation

* $a_m$: the $m$-th coefficient `PeriodicSobolev.coeff φ m` of $\varphi \in H^s(2\pi)$.
* $\zeta(r) = \sum_{n \ge 1} n^{-r}$: the Riemann zeta function on the reals, `zetaReal`.

## Conventions

* The backbone sums a series against the characters `periodicChar (2 * π) m x` $= e^{imx}$, which
  are not normalized. The source uses $\psi_m = (2\pi)^{-1/2} e^{imx}$. The norm $\|\cdot\|_{*,s}$
  is a norm on the coefficient sequence and does not see the factor $(2\pi)^{-1/2}$, but every
  statement about the function does. `AtkinsonHan.Chapter07.eval` carries this factor, so `eval φ`
  is the function $\varphi(x)$ of the source, and the bounds have the constants of the source.
* The inner product of Mathlib is conjugate-linear in its first argument, the opposite of the
  convention of the source. So the inner product $(\varphi, \rho)_{*,s}$ of the source is
  `inner ℂ ρ φ`.

## Implementation notes

* `PeriodicSobolev s` is a sequence space, not a space of functions, because for $s < 0$ an element
  is only a formal series. For $s \le 1/2$ the series need not converge, and
  `AtkinsonHan.Chapter07.eval` has no meaning there.
* The polynomial functions on a compact set $D \subseteq \mathbb{R}^\iota$ form a subalgebra of
  $C(D, \mathbb{R})$ that separates points. This general fact is proved privately in this module,
  for the use in Section 7.5.5.
* The library has the harmonic polynomials (`Numlib.Analysis.HarmonicPolynomial`) and the Legendre
  polynomials on $[-1, 1]$ (`Numlib.Approximation.OrthogonalPolynomial`), but no associated Legendre
  functions and no surface measure on the sphere $S^2$.

## Deviations from the source

* **Equations (7.5.1)–(7.5.2)** (scope). The Fourier expansion is realized by a totalized
  series, with value zero when the series is not summable. The source allows coefficients
  representing distributions for which ordinary pointwise evaluation is unavailable.
  The formal Fourier norm equivalence with the classical derivative norm is stated at
  integer orders.
* **Proposition 7.5.4** (scope). Regularity is established in the case of continuity
  ($k=0$). The source also states higher continuous derivatives.
* **Theorem 7.5.7** (generalization). The interpolation bound uses a constant depending on $s$
  alone, uniformly over $0 \le r \le s$. See `AtkinsonHan.Chapter07.theorem_7_5_7`.
* **Exercises 7.5.3 and 7.5.4** (scope). The Simpson estimate gives an explicit error
  constant. The dual pairing allows all real orders, with complex conjugation in the
  second argument as in the printed formula.

## Not formalized

* **Equations (7.5.3)–(7.5.5), the distributional derivative $\mathcal{D}$.** Its description
  $\mathcal{D}\varphi = i \sum_m m a_m \psi_m$ on the coefficients is used, in the form of the
  classical norm on the Fourier side, but the operator itself, its norm $1$ and its unique extension
  from the trigonometric polynomials are not built, because nothing else here uses them.
* **Proposition 7.5.4 for $k > 0$.** Only the case $k = 0$, convergence to a continuous function, is
  formalized.
* **Example 7.5.3, the square wave.** The $2\pi$-periodic square wave, equal to $0$ on
  $((2k-1)\pi, 2k\pi)$ and to $1$ on $(2k\pi, (2k+1)\pi)$, has the Fourier series $\frac{1}{2} -
  \frac{i}{\pi} \sum_{k \ge 0} (2k+1)^{-1} [e^{(2k+1)it} - e^{-(2k+1)it}]$, and its distributional
  derivative is the Dirac comb $\sum_j (-1)^j \delta(t - \pi j)$, where
  $\delta[\varphi] = \varphi(0)$ on $H^s(2\pi)$ for $s > 1/2$. The statement needs the operator
  $\mathcal{D} : H^s(2\pi) \to H^{s-1}(2\pi)$, and Mathlib has no distributions on the circle.
* **Section 7.5.4, the operator $\mathcal{A}$ with the logarithmic kernel (7.5.16).** The source
  obtains its symbol $a_m / |m|$ from complex function theory that it does not reproduce.
* **Definition 7.5.9, the spherical harmonics, and (7.5.20)–(7.5.22).** These are the identity of
  the span of the spherical harmonics of degree at most $N$ with $\mathbb{S}_N$ (7.5.20), the
  dimension $\dim \mathbb{S}_N = (N + 1)^2$ (7.5.21), and the orthonormal basis of $L^2(U)$ in terms
  of the Legendre polynomials and the associated Legendre functions (7.5.22). The source quotes
  (7.5.20) and (7.5.21) without proof, and a statement needs the harmonic homogeneous polynomials
  restricted to the sphere, the associated Legendre functions and a surface measure on $S^2$.
* **Theorem 7.5.10, Ragozin's rate, and (7.5.31)–(7.5.33).** The rate is $\rho_N(g) \le c_k
  H_{k,\gamma}(g) N^{-(k+\gamma)}$ for $g \in C^{k,\gamma}(U)$ and $N \ge 1$, where
  $H_{k,\gamma}(g)$ is the Hölder constant of the derivatives of order $k$ in local surface
  coordinates; the $L^2(U)$ rate (7.5.32) and the uniform rate
  $\|g - P_N g\|_\infty \le c N^{-(k+\gamma-1/2)}$ (7.5.33) follow from it. The source quotes these
  results without proof, and they need the Hölder spaces $C^{k,\gamma}(U)$ on the sphere and the
  spherical harmonics.
* **The rest of Section 7.5.5.** The Laplace expansion (7.5.23)–(7.5.28), the orthogonal projection
  $P_N : L^2(U) \to \mathbb{S}_N$ with its norm $\|P_N\| = (\sqrt{8/\pi} + \delta_N) \sqrt{N}$
  (7.5.29), and the Sobolev spaces $H^r(U)$ need the same surface measure and spherical harmonics.
-/

open Filter Metric Set Topology Quadrature
open scoped ComplexConjugate ENNReal InnerProductSpace Real

namespace AtkinsonHan.Chapter07

/-! ### The normalization constant -/

/-- The constant $\sqrt{2\pi}$ satisfies $1 \le \sqrt{2\pi}$, so the functions $\psi_m$ of the
source are bounded by $1$. -/
theorem one_le_sqrt_two_pi : (1 : ℝ) ≤ √(2 * π) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])

/-- The constant $\sqrt{2\pi}$ is positive. -/
theorem sqrt_two_pi_pos : 0 < √(2 * π) := by linarith [one_le_sqrt_two_pi]

/-- The normalization factor satisfies $(2\pi)^{-1/2} \le 1$. -/
theorem inv_sqrt_two_pi_le_one : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_sqrt_two_pi

/-- **Equation (7.5.1)** of [han2009theoretical], the orthonormal functions. For $m \in \mathbb{Z}$
and real $x$,
$$\psi_m(x) = (2\pi)^{-1/2} e^{imx}.$$

The function $e^{imx}$ is the backbone character `periodicChar (2 * π) m x`. -/
noncomputable def psi (m : ℤ) (x : ℝ) : ℂ := (√(2 * π))⁻¹ * periodicChar (2 * π) m x

/-- Each function $\psi_m$ has the constant modulus $|\psi_m(x)| = (2\pi)^{-1/2}$. -/
@[simp]
theorem norm_psi (m : ℤ) (x : ℝ) : ‖psi m x‖ = (√(2 * π))⁻¹ := by
  rw [psi, norm_mul, norm_periodicChar, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

variable {s t : ℝ}

/-- **Equation (7.5.1)** of [han2009theoretical], the sum of a series. For $\varphi \in H^s(2\pi)$
with coefficients $a_m$ and real $x$,
$$\varphi(x) = (2\pi)^{-1/2} \sum_{m \in \mathbb{Z}} a_m e^{imx}.$$

This is the backbone sum `PeriodicSobolev.eval (2 * π) φ x` times $(2\pi)^{-1/2}$. The sum is a
`tsum`, so it is $0$ when the series is not summable; for $s > 1/2$ the series converges
absolutely.

**Reading.** Uses a totalized sum even for coefficients defining distributions.
-/
noncomputable def eval (φ : PeriodicSobolev s) (x : ℝ) : ℂ :=
  (√(2 * π))⁻¹ * PeriodicSobolev.eval (2 * π) φ x

/-- **Equation (7.5.1)** of [han2009theoretical]. For $\varphi \in H^s(2\pi)$ and real $x$,
$$\varphi(x) = \sum_{m \in \mathbb{Z}} a_m \psi_m(x),$$
where $\varphi(x)$ is `AtkinsonHan.Chapter07.eval φ x` and $a_m$ are the coefficients of
$\varphi$.

**Reading.** Expansion is unconditional in the totalized sum sense.
-/
theorem eval_eq_tsum (φ : PeriodicSobolev s) (x : ℝ) :
    eval φ x = ∑' m : ℤ, φ.coeff m * psi m x := by
  rw [eval, PeriodicSobolev.eval, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [psi]; ring

/-! ### Definition 7.5.1 and Theorem 7.5.2 -/

/-- **Definition 7.5.1** of [han2009theoretical], the norm (7.5.2). For real $s$ and
$\varphi \in H^s(2\pi)$ with coefficients $a_m$,
$$\|\varphi\|_{*,s}^2 = |a_0|^2 + \sum_{|m| > 0} |m|^{2s} |a_m|^2,$$
and the series on the right converges.

The norm $\|\varphi\|_{*,s}$ is the norm of `PeriodicSobolev s`, and the statement is a
`HasSum`. -/
theorem definition_7_5_1_norm (s : ℝ) (φ : PeriodicSobolev s) :
    HasSum (fun m : ℤ => if m = 0 then ‖φ.coeff 0‖ ^ 2
      else |(m : ℝ)| ^ (2 * s) * ‖φ.coeff m‖ ^ 2) (‖φ‖ ^ 2) := by
  refine (PeriodicSobolev.hasSum_norm_sq φ).congr_fun fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ite_eq_right hm, mul_pow, periodicSobolevWeight_sq s hm]

/-- **Definition 7.5.1** of [han2009theoretical], the inner product. For real $s$ and
$\varphi, \rho \in H^s(2\pi)$ with coefficients $a_m$ and $b_m$,
$$(\varphi, \rho)_{*,s} = a_0 \overline{b_0} + \sum_{|m| > 0} |m|^{2s} a_m \overline{b_m}.$$

The inner product of Mathlib is conjugate-linear in its first argument, the opposite of the
convention of the source, so $(\varphi, \rho)_{*,s}$ is `inner ℂ ρ φ`. -/
theorem definition_7_5_1_inner (s : ℝ) (φ ρ : PeriodicSobolev s) :
    (inner ℂ ρ φ : ℂ) = ∑' m : ℤ, (if m = 0 then φ.coeff 0 * conj (ρ.coeff 0)
      else (|(m : ℝ)| ^ (2 * s) : ℝ) * (φ.coeff m * conj (ρ.coeff m))) := by
  rw [PeriodicSobolev.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [mul_comm]
  · rw [ite_eq_right hm, ← Complex.ofReal_pow, periodicSobolevWeight_sq s hm]
    ring

/-- **Theorem 7.5.2** of [han2009theoretical], the characterization. Let $s$ be real and let
$(a_m)_{m \in \mathbb{Z}}$ be complex numbers. There is $\varphi \in H^s(2\pi)$ with the
coefficients $a_m$ if and only if
$$|a_0|^2 + \sum_{|m| > 0} |m|^{2s} |a_m|^2 < \infty.$$

The condition is the summability of $(w_s(m) |a_m|)^2$, where $w_s(0) = 1$ and $w_s(m) = |m|^s$
for $m \neq 0$ is `periodicSobolevWeight s m`. -/
theorem theorem_7_5_2 (s : ℝ) (a : ℤ → ℂ) :
    (∃ φ : PeriodicSobolev s, φ.coeff = a) ↔
      Summable fun m : ℤ => (periodicSobolevWeight s m * ‖a m‖) ^ 2 := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact (PeriodicSobolev.hasSum_norm_sq φ).summable
  · intro ha
    refine ⟨PeriodicSobolev.ofCoeff s a (memℓp_two_iff.2 (ha.congr fun m => ?_)),
      PeriodicSobolev.coeff_ofCoeff _ _ _⟩
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s m).le]

/-- **Definition 7.5.1** of [han2009theoretical], the classical norm. For an integer $k \ge 0$ and
$\varphi \in H^k(2\pi)$ with coefficients $a_m$, the square of the classical Sobolev norm is
$$\|\varphi\|_{H^k}^2 = \sum_{m \in \mathbb{Z}} \Big(\sum_{j=0}^{k} |m|^{2j}\Big) |a_m|^2.$$

This is $\sum_{j \le k} \|\varphi^{(j)}\|_{L^2}^2$ written on the Fourier side: differentiation
multiplies the $m$-th coefficient by $im$, by (7.5.3), and Parseval's identity turns
$\|\varphi^{(j)}\|_{L^2}^2$ into $\sum_m |m|^{2j} |a_m|^2$. At $m = 0$ the inner sum is $1$. The
outer sum is a `tsum`, so it is $0$ when the series is not summable. -/
noncomputable def classicalNormSq (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) : ℝ :=
  ∑' m : ℤ, (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2

/-- For an integer $k \ge 0$ and $m \in \mathbb{Z}$, the weight $w_k$ of (7.5.2) satisfies
$$w_k(m)^2 \le \sum_{j=0}^{k} |m|^{2j} \le (k + 1) \, w_k(m)^2,$$
where $w_k(0) = 1$ and $w_k(m) = |m|^k$ for $m \neq 0$.

This symbol inequality gives the norm equivalence of Theorem 7.5.2. -/
theorem weight_sq_le_sum_le (k : ℕ) (m : ℤ) :
    periodicSobolevWeight (k : ℝ) m ^ 2 ≤ ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j) ∧
      ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
        ≤ ((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hone : ∑ j ∈ Finset.range (k + 1), |((0 : ℤ) : ℝ)| ^ (2 * j) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b _ hb
        have h2b : 2 * b ≠ 0 := by omega
        simp [h2b]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h
    rw [hone, periodicSobolevWeight_zero, one_pow]
    exact ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  · have habs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(m : ℝ)| := by rw [Int.cast_abs]
    have hw : periodicSobolevWeight (k : ℝ) m ^ 2 = |(m : ℝ)| ^ (2 * k) := by
      rw [periodicSobolevWeight_sq _ hm,
        show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hmono : ∀ j ∈ Finset.range (k + 1),
        |(m : ℝ)| ^ (2 * j) ≤ |(m : ℝ)| ^ (2 * k) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact pow_le_pow_right₀ habs (by omega)
    rw [hw]
    constructor
    · exact Finset.single_le_sum (f := fun j => |(m : ℝ)| ^ (2 * j))
        (fun j _ => by positivity) (Finset.self_mem_range_succ k)
    · calc ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
          ≤ ∑ _j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * k) := Finset.sum_le_sum hmono
        _ = ((k : ℝ) + 1) * |(m : ℝ)| ^ (2 * k) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring

/-- **Theorem 7.5.2** of [han2009theoretical], the norm equivalence. Let $k \ge 0$ be an integer and
let $\varphi \in H^k(2\pi)$. Then
$$\|\varphi\|_{*,k}^2 \le \|\varphi\|_{H^k}^2 \le (k + 1) \|\varphi\|_{*,k}^2,$$
where $\|\varphi\|_{H^k}$ is the classical norm `AtkinsonHan.Chapter07.classicalNormSq`.

The proof sums the inequality `AtkinsonHan.Chapter07.weight_sq_le_sum_le` against $|a_m|^2$.

**Reading.** The explicit standard norm comparison is only at integer order.
-/
theorem theorem_7_5_2_norm_equiv (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) :
    ‖φ‖ ^ 2 ≤ classicalNormSq k φ ∧ classicalNormSq k φ ≤ ((k : ℝ) + 1) * ‖φ‖ ^ 2 := by
  have hns := PeriodicSobolev.hasSum_norm_sq φ
  have hterm : ∀ m : ℤ, (periodicSobolevWeight (k : ℝ) m * ‖φ.coeff m‖) ^ 2
      = periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2 := fun m => by ring
  have hns' : HasSum (fun m : ℤ => periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2)
      (‖φ‖ ^ 2) := hns.congr_fun fun m => (hterm m).symm
  have hupper : HasSum (fun m : ℤ => (((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2)
      * ‖φ.coeff m‖ ^ 2) (((k : ℝ) + 1) * ‖φ‖ ^ 2) :=
    (hns'.mul_left ((k : ℝ) + 1)).congr_fun fun m => by ring
  have hnn : ∀ m : ℤ, (0 : ℝ) ≤ (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j))
      * ‖φ.coeff m‖ ^ 2 := fun m =>
    mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
  have hmid : Summable fun m : ℤ =>
      (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le hnn (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [classicalNormSq, ← hns'.tsum_eq]
    refine hns'.summable.tsum_le_tsum (fun m => ?_) hmid
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).1 (by positivity)
  · rw [classicalNormSq, ← hupper.tsum_eq]
    refine hmid.tsum_le_tsum (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)

/-- Let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^k$, and let $\varphi$ be
its sequence of Fourier coefficients $\hat f_m = \frac{1}{2\pi} \int_0^{2\pi} f(x) e^{-imx} \,
dx$. Then the classical norm of $\varphi$ on the Fourier side is
$$\|\varphi\|_{H^k}^2 = \frac{1}{2\pi} \sum_{j=0}^{k} \|f^{(j)}\|_{L^2(0, 2\pi)}^2.$$

This connects `AtkinsonHan.Chapter07.classicalNormSq` with the norm of a function, by Parseval's
identity for each derivative and $\widehat{f^{(j)}}_m = (im)^j \hat f_m$. The sequence $\varphi$
is `PeriodicSobolev.ofSmooth hf hd`. Its coefficients are taken against $e^{imx}$ and not
against $\psi_m$, so $\|f\|_{L^2(0, 2\pi)}^2 = 2\pi \sum_m |\hat f_m|^2$, and this is the source
of the factor $1/(2\pi)$. -/
theorem classicalNormSq_ofSmooth {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) {k : ℕ}
    (hd : ContDiff ℝ k f) :
    classicalNormSq k (PeriodicSobolev.ofSmooth hf hd)
      = (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f := by
  rw [classicalNormSq, PeriodicSobolev.coeff_ofSmooth]
  exact (PeriodicSobolev.hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd).tsum_eq

/-- **Theorem 7.5.2** of [han2009theoretical], for smooth functions. Let
$f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class $C^k$, with the classical norm
$\|f\|_{H^k}^2 = \sum_{j=0}^{k} \|f^{(j)}\|_{L^2(0, 2\pi)}^2$, and let $\varphi$ be its sequence
of Fourier coefficients $\hat f_m = \frac{1}{2\pi} \int_0^{2\pi} f(x) e^{-imx} \, dx$. Then
$$\|\varphi\|_{*,k}^2 \le \frac{1}{2\pi} \|f\|_{H^k}^2 \le (k + 1) \|\varphi\|_{*,k}^2.$$

The sequence $\varphi$ is `PeriodicSobolev.ofSmooth hf hd`, and $\|f\|_{H^k}^2$ is
`PeriodicSobolev.derivNormSq k f`. The factor $1/(2\pi)$ comes from the coefficients against
$e^{imx}$; see `AtkinsonHan.Chapter07.classicalNormSq_ofSmooth`.

**Reading.** Explicit equivalence with the classical derivative norm on smooth functions at integer
order.
-/
theorem theorem_7_5_2_smooth {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) {k : ℕ}
    (hd : ContDiff ℝ k f) :
    ‖PeriodicSobolev.ofSmooth hf hd‖ ^ 2 ≤ (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f ∧
      (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f
        ≤ ((k : ℝ) + 1) * ‖PeriodicSobolev.ofSmooth hf hd‖ ^ 2 := by
  rw [← classicalNormSq_ofSmooth hf hd]
  exact theorem_7_5_2_norm_equiv k _

/-! ### Section 7.5.2: the embedding results -/

/-- **Equation (7.5.10)** of [han2009theoretical]. Let $s > 1/2$ and $\varphi \in H^s(2\pi)$ with
coefficients $a_m$. Then for every real $x$,
$$|\varphi(x)| \le |a_0| + \sqrt{2\zeta(2s)} \, \|\varphi\|_{*,s}.$$

Here $\varphi(x)$ is `AtkinsonHan.Chapter07.eval φ x`, and `zetaReal` is the function $\zeta$. -/
theorem proposition_7_5_4_bound (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval φ x‖ ≤ ‖φ.coeff 0‖ + √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hb := PeriodicSobolev.norm_eval_le_tsum_norm_coeff hs (2 * π) φ x
  have hle := PeriodicSobolev.tsum_norm_coeff_le hs φ
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [hb.trans hle]

/-- **Proposition 7.5.4** of [han2009theoretical], the case $k = 0$, with the bound (7.5.11). Let
$s > 1/2$ and $\varphi \in H^s(2\pi)$. Then the series (7.5.1) converges to a continuous
function of period $2\pi$, and for every real $x$,
$$|\varphi(x)| \le \big[1 + \sqrt{2\zeta(2s)}\big] \|\varphi\|_{*,s}.$$

Here $\varphi(x)$ is `AtkinsonHan.Chapter07.eval φ x`, and `zetaReal` is the function $\zeta$.

**Reading.** Proves only the continuous case with the same explicit uniform bound.
-/
theorem proposition_7_5_4 (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Continuous (eval φ) ∧ Function.Periodic (eval φ) (2 * π) ∧
      ∀ x, ‖eval φ x‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ := by
  refine ⟨continuous_const.mul (PeriodicSobolev.continuous_eval hs (2 * π) φ),
    fun x => by rw [eval, eval, PeriodicSobolev.eval_periodic (by positivity) φ x], fun x => ?_⟩
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [PeriodicSobolev.norm_eval_le hs (2 * π) φ x]

/-- **Proposition 7.5.5** of [han2009theoretical]. Let $t < s$ be real. The inclusion
$H^s(2\pi) \to H^t(2\pi)$ has dense range and is a compact operator.

The inclusion is `PeriodicSobolev.inclL`, which keeps the coefficients. Exercise 7.5.1 asks for
this proof; see `AtkinsonHan.Chapter07.exercise_7_5_1`. -/
theorem proposition_7_5_5 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  ⟨PeriodicSobolev.denseRange_inclL h.le, PeriodicSobolev.isCompactOperator_inclL h⟩

/-- **Exercise 7.5.1** of [han2009theoretical]. Let $t < s$ be real. The inclusion
$H^s(2\pi) \to H^t(2\pi)$ has dense range and is a compact operator.

The exercise asks for the proof of Proposition 7.5.5, `AtkinsonHan.Chapter07.proposition_7_5_5`. -/
theorem exercise_7_5_1 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  proposition_7_5_5 h

/-- **Exercise 7.5.2** of [han2009theoretical]. For every real $s$, the space $\mathbb{T}$ of
trigonometric polynomials (7.5.4), the finite linear combinations of the $\psi_m$, is dense in
$H^s(2\pi)$.

The space $\mathbb{T}$ is the span of the coordinate series `PeriodicSobolev.basisElt s m`,
whose coefficient is $1$ at $m$ and $0$ elsewhere. -/
theorem exercise_7_5_2 (s : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (PeriodicSobolev.basisElt s)) :
      Submodule ℂ (PeriodicSobolev s)) : Set (PeriodicSobolev s)) :=
  PeriodicSobolev.dense_span_basisElt s

/-! ### Section 7.5.3: the approximation results -/

/-- **Section 7.5.3** of [han2009theoretical], the integral. For $\varphi \in H^s(2\pi)$,
$$I(\varphi) = \int_0^{2\pi} \varphi(x) \, dx,$$
where $\varphi(x)$ is `AtkinsonHan.Chapter07.eval φ x`. -/
noncomputable def integral (φ : PeriodicSobolev s) : ℂ := ∫ x in (0 : ℝ)..(2 * π), eval φ x

/-- **Equation (7.5.12)** of [han2009theoretical], the trapezoidal rule. For an integer $k$ and
$\varphi \in H^s(2\pi)$,
$$T_k(\varphi) = h \sum_{j=1}^{k} \varphi(jh), \qquad h = \frac{2\pi}{k}.$$

For a periodic integrand the two end points carry the same value, so the half weights at the
ends merge into one full weight. At $k = 0$ the rule is $0$. -/
noncomputable def trapezoid (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  PeriodicSobolev.trapezoidSum (2 * π) k (eval φ)

private theorem trapezoidSum_const_mul (T : ℝ) (k : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    PeriodicSobolev.trapezoidSum T k (fun x => c * f x)
      = c * PeriodicSobolev.trapezoidSum T k f := by
  rw [PeriodicSobolev.trapezoidSum, PeriodicSobolev.trapezoidSum, ← Finset.mul_sum]
  ring

/-- For $\varphi \in H^s(2\pi)$ and an integer $k$, the quadrature error $I(\varphi) - T_k(\varphi)$
in the normalization of the source is $(2\pi)^{-1/2}$ times the quadrature error of the backbone
sum `PeriodicSobolev.eval (2 * π) φ`. -/
theorem integral_sub_trapezoid (φ : PeriodicSobolev s) (k : ℕ) :
    integral φ - trapezoid k φ = (√(2 * π))⁻¹ *
      ((∫ x in (0 : ℝ)..(2 * π), PeriodicSobolev.eval (2 * π) φ x)
        - PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ)) := by
  have h1 : integral φ = (√(2 * π))⁻¹ * ∫ x in (0 : ℝ)..(2 * π),
      PeriodicSobolev.eval (2 * π) φ x := by
    rw [integral]
    simp only [eval]
    rw [intervalIntegral.integral_const_mul]
  have h2 : trapezoid k φ = (√(2 * π))⁻¹ *
      PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ) := by
    rw [trapezoid, show eval φ = fun x => (√(2 * π))⁻¹ *
      PeriodicSobolev.eval (2 * π) φ x from rfl, trapezoidSum_const_mul]
  rw [h1, h2, mul_sub]

/-- **Proposition 7.5.6** of [han2009theoretical], the bound (7.5.13). Let $s > 1/2$, let $k \ge 1$
be an integer and let $\varphi \in H^s(2\pi)$. Then
$$|I(\varphi) - T_k(\varphi)| \le \sqrt{4\pi\zeta(2s)} \, k^{-s} \|\varphi\|_{*,s}.$$

So the trapezoidal rule converges at the rate $k^{-s}$ on $H^s(2\pi)$, and it is very accurate
for a smooth periodic integrand. Here $\zeta$ is `zetaReal`. -/
theorem proposition_7_5_6 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - trapezoid k φ‖ ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hbb := PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le hs
    (by positivity : (0 : ℝ) < 2 * π) hk φ
  have hsq : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
  have h4 : √(4 * π * zetaReal (2 * s)) = √(2 * π) * √(2 * zetaReal (2 * s)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    congr 1
    ring
  rw [integral_sub_trapezoid, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left hbb (by positivity)) (le_of_eq ?_)
  calc (√(2 * π))⁻¹ * (2 * π * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖))
      = ((√(2 * π))⁻¹ * (√(2 * π) * √(2 * π)))
        * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by rw [hsq]; ring
    _ = √(2 * π) * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by
        rw [inv_mul_cancel_left₀ (ne_of_gt sqrt_two_pi_pos)]
    _ = √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by rw [h4]; ring

/-- **Theorem 7.5.7** of [han2009theoretical], the bound (7.5.15). Let $s > 1/2$, let
$0 \le r \le s$, let $n \ge 1$ be an integer and let $\varphi \in H^s(2\pi)$. Let
$\mathcal{I}_n \varphi$ be the trigonometric polynomial of degree at most $n$ that agrees with
$\varphi$ at the $2n + 1$ nodes $t_j = 2\pi j / (2n + 1)$. Then
$\mathcal{I}_n \varphi(t_j) = \varphi(t_j)$ for $0 \le j < 2n + 1$, and
$$\|\varphi - \mathcal{I}_n \varphi\|_{*,r} \le \sqrt{1 + 2\zeta(2s)} \, n^{r-s}
  \|\varphi\|_{*,s}.$$

**Generalization.** The book allows the constant to depend on $s$ and $r$. The explicit
constant $\sqrt{1 + 2\zeta(2s)}$ works uniformly over $0 \le r \le s$.

The interpolant $\mathcal{I}_n \varphi$ is `PeriodicSobolev.trigInterp r n φ`, an element of
$H^r(2\pi)$, and $\varphi$ is read in $H^r(2\pi)$ through `PeriodicSobolev.incl`. The source
refers to Kress for the proof. The proof here is the aliasing argument of
`Numlib.Analysis.Fourier.Aliasing`: the coefficients of $\mathcal{I}_n \varphi$ on the window
$-n, \dots, n$ are $a_m + \sum_{j \neq 0} a_{m + j(2n+1)}$, they vanish outside it, and the
Cauchy–Schwarz inequality against $\sum_{j \neq 0} |m + j(2n+1)|^{-2s}$ bounds the tails. -/
theorem theorem_7_5_7 (hs : 1 / 2 < s) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) {n : ℕ} (hn : 1 ≤ n)
    (φ : PeriodicSobolev s) :
    (∀ j < 2 * n + 1, eval (PeriodicSobolev.trigInterp r n φ) (angleNode (2 * n + 1) j)
        = eval φ (angleNode (2 * n + 1) j)) ∧
      ‖PeriodicSobolev.incl hrs φ - PeriodicSobolev.trigInterp r n φ‖
        ≤ √(1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (r - s) * ‖φ‖ :=
  ⟨fun j hj => by rw [eval, eval, PeriodicSobolev.eval_trigInterp_angleNode r n φ hj],
    PeriodicSobolev.norm_incl_sub_trigInterp_le hs hr hrs hn φ⟩

/-- **Simpson's rule** of Exercise 7.5.3 of [han2009theoretical]. For an integer $k$ and
$\varphi \in H^s(2\pi)$, Simpson's rule on one period with $2k$ subintervals of length
$h = \pi / k$ and the nodes $x_i = ih$ is
$$S_{2k}(\varphi) = \frac{h}{3} \Big[4 \sum_{j=1}^{k} \varphi(x_{2j-1}) + 2 \sum_{j=1}^{k}
  \varphi(x_{2j})\Big].$$

For a periodic integrand the two end points coincide, so the end weights $1$ merge into the
weight $2$ at $x_{2k}$. -/
noncomputable def simpson (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  ((π / k : ℝ) / 3 : ℝ) *
    (4 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / k))
      + 2 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / k)))

private theorem sum_range_two_mul (f : ℕ → ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), f i = ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- For an integer $k \ge 1$ and $\varphi \in H^s(2\pi)$, Simpson's rule is the Richardson
combination $S_{2k}(\varphi) = (4 T_{2k}(\varphi) - T_k(\varphi)) / 3$ of two trapezoidal rules.

The identity holds for any integrand, and it turns the trapezoidal bound (7.5.13) into the bound
of Exercise 7.5.3. -/
theorem simpson_eq (k : ℕ) (hk : 0 < k) (φ : PeriodicSobolev s) :
    simpson k φ = (4 * trapezoid (2 * k) φ - trapezoid k φ) / 3 := by
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hstep2 : 2 * π / ((2 * k : ℕ) : ℝ) = π / (k : ℝ) := by push_cast; field_simp
  have hstep1 : 2 * π / ((k : ℕ) : ℝ) = 2 * (π / (k : ℝ)) := by ring
  have hT2 : trapezoid (2 * k) φ
      = ((π / (k : ℝ) : ℝ) : ℂ)
        * ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep2]
  have hT1 : trapezoid k φ
      = ((2 * (π / (k : ℝ)) : ℝ) : ℂ)
        * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep1]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => congrArg (eval φ) (by ring))
  have hsplit : ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))
      = (∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / (k : ℝ))))
        + ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [sum_range_two_mul (fun i => eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))) k,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 by push_cast; ring,
      show ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 by push_cast; ring]
  rw [simpson, hT2, hT1, hsplit]
  push_cast
  ring

/-- **Exercise 7.5.3** of [han2009theoretical]. Let $s > 1/2$, let $k \ge 1$ be an integer and let
$\varphi \in H^s(2\pi)$. Then
$$|I(\varphi) - S_{2k}(\varphi)| \le \frac{5}{3} \sqrt{4\pi\zeta(2s)} \, k^{-s}
  \|\varphi\|_{*,s}.$$

Since $S_{2k} = (4 T_{2k} - T_k) / 3$, the error is $(4 (I - T_{2k}) - (I - T_k)) / 3$, and
$(2k)^{-s} \le k^{-s}$. Here $S_{2k}$ is `AtkinsonHan.Chapter07.simpson k`.

**Reading.** Gives explicit error constant at rate k to the power minus s.
-/
theorem exercise_7_5_3 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - simpson k φ‖ ≤ 5 / 3 * √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hspos : (0 : ℝ) < s := by linarith
  have h2k : (0 : ℕ) < 2 * k := by omega
  have hb1 := proposition_7_5_6 hs hk φ
  have hb2 := proposition_7_5_6 hs h2k φ
  have hrate : ((2 * k : ℕ) : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-s) := by
    have hkp : (0 : ℝ) < (k : ℝ) ^ s :=
      Real.rpow_pos_of_pos (by exact_mod_cast hk) s
    have hle : (k : ℝ) ^ s ≤ ((2 * k : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity)
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]) hspos.le
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), inv_eq_one_div,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le hkp hle
  have hb2' : ‖integral φ - trapezoid (2 * k) φ‖
      ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
    refine hb2.trans ?_
    have := mul_le_mul_of_nonneg_left hrate (Real.sqrt_nonneg (4 * π * zetaReal (2 * s)))
    exact mul_le_mul_of_nonneg_right this (norm_nonneg φ)
  have hsplit : integral φ - simpson k φ
      = (4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)) / 3 := by
    rw [simpson_eq k hk φ]
    ring
  rw [hsplit, norm_div, Complex.norm_ofNat]
  have hnum : ‖4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)‖
      ≤ 4 * ‖integral φ - trapezoid (2 * k) φ‖ + ‖integral φ - trapezoid k φ‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
    norm_num
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- **Exercise 7.5.4** of [han2009theoretical]. Let $t$ be real and let $\eta \in H^{-t}(2\pi)$ have
coefficients $b_m$. The pairing (7.5.6),
$$\ell[\varphi] = \sum_{m \in \mathbb{Z}} a_m \overline{b_m}$$
for $\varphi \in H^t(2\pi)$ with coefficients $a_m$, is a bounded linear functional on
$H^t(2\pi)$ with $\|\ell\| \le \|\eta\|_{*,-t}$.

The functional is `PeriodicSobolev.dualPairing t η`. The statement holds for every real $t$.

**Reading.** Allows every real order while proving boundedness of the same conjugated pairing.
-/
theorem exercise_7_5_4 (t : ℝ) (η : PeriodicSobolev (-t)) :
    (∀ φ : PeriodicSobolev t,
        PeriodicSobolev.dualPairing t η φ = ∑' m : ℤ, φ.coeff m * conj (η.coeff m)) ∧
      ‖PeriodicSobolev.dualPairing t η‖ ≤ ‖η‖ :=
  ⟨fun _ => rfl, PeriodicSobolev.norm_dualPairing_le t η⟩

/-!
### Section 7.5.5: spherical polynomials

This part formalizes Definition 7.5.8, the minimax error (7.5.30), and the convergence
$\rho_N(g) \to 0$ that the source derives from the Stone–Weierstrass theorem. The rest of Section
7.5.5 is not formalized; the module doc comment lists it. The convergence uses the fact that the
polynomial functions on a compact set $D \subseteq \mathbb{R}^\iota$ form a subalgebra of
$C(D, \mathbb{R})$ that separates points. This general fact belongs beside `Approximation.mvPolyLE`,
and it is private here because Section 7.5.5 is its only use.
-/

section StoneWeierstrass

variable {ι : Type*} (D : Set (ι → ℝ))

/-- Restriction of polynomials to $D$ is multiplicative: the restriction of $pq$ is the product of
the restrictions of $p$ and $q$. -/
private theorem toContinuousMapOn_mul (p q : MvPolynomial ι ℝ) :
    Approximation.toContinuousMapOn D (p * q) =
      Approximation.toContinuousMapOn D p * Approximation.toContinuousMapOn D q := by
  ext x; simp

/-- The polynomial functions on $D$, the union of the spaces `Approximation.mvPolyLE D N` over $N$,
form a subalgebra of $C(D, \mathbb{R})$. -/
private noncomputable def polyAlgebra : Subalgebra ℝ C(D, ℝ) where
  carrier := {f | ∃ N, f ∈ Approximation.mvPolyLE D N}
  mul_mem' := by
    rintro f g ⟨N, hf⟩ ⟨M, hg⟩
    rw [Approximation.mem_mvPolyLE_iff] at hf hg
    obtain ⟨p, hp, rfl⟩ := hf
    obtain ⟨q, hq, rfl⟩ := hg
    refine ⟨N + M, Approximation.mem_mvPolyLE_iff.2
      ⟨p * q, ?_, toContinuousMapOn_mul D p q⟩⟩
    exact (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)
  add_mem' := by
    rintro f g ⟨N, hf⟩ ⟨M, hg⟩
    exact ⟨max N M, Submodule.add_mem _ (Approximation.mvPolyLE_mono (le_max_left N M) hf)
      (Approximation.mvPolyLE_mono (le_max_right N M) hg)⟩
  algebraMap_mem' r := ⟨0, Approximation.mem_mvPolyLE_iff.2
    ⟨MvPolynomial.C r, by simp, by ext x; simp⟩⟩

/-- The polynomial functions on $D$ separate the points of $D$, because each coordinate is a
polynomial of degree one. -/
private theorem polyAlgebra_separatesPoints : (polyAlgebra D).SeparatesPoints := by
  rintro x y hxy
  have hne : (x : ι → ℝ) ≠ (y : ι → ℝ) := fun h => hxy (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  refine ⟨_, ⟨Approximation.toContinuousMapOn D (MvPolynomial.X i), ⟨1, ?_⟩, rfl⟩, ?_⟩
  · exact Approximation.mem_mvPolyLE_iff.2 ⟨MvPolynomial.X i, by simp, rfl⟩
  · simpa using hi

/-- The Stone–Weierstrass theorem on a compact set $D \subseteq \mathbb{R}^\iota$: every
$g \in C(D, \mathbb{R})$ is uniformly within $\varepsilon > 0$ of a polynomial function of some
degree. -/
private theorem exists_mem_mvPolyLE_near [CompactSpace D] (g : C(D, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∃ f ∈ Approximation.mvPolyLE D N, ‖f - g‖ < ε := by
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (polyAlgebra D) (polyAlgebra_separatesPoints D) g ε hε
  obtain ⟨N, hN⟩ := f.2
  exact ⟨N, f, hN, hf⟩

end StoneWeierstrass

/-- **Section 7.5.5** of [han2009theoretical], the unit sphere
$$U = \{(x, y, z) \in \mathbb{R}^3 : x^2 + y^2 + z^2 = 1\}.$$

The points are coordinate vectors in `Fin 3 → ℝ`, so that `MvPolynomial.eval` applies to them
directly. The sup norm of `Fin 3 → ℝ` gives the same topology as the Euclidean norm, so
`C(unitSphere, ℝ)` is the space $C(U)$ of the source. -/
def unitSphere : Set (Fin 3 → ℝ) := {x | ∑ i, x i ^ 2 = 1}

/-- A point $x \in \mathbb{R}^3$ lies in $U$ if and only if $x_0^2 + x_1^2 + x_2^2 = 1$. -/
theorem mem_unitSphere_iff {x : Fin 3 → ℝ} : x ∈ unitSphere ↔ ∑ i, x i ^ 2 = 1 := Iff.rfl

/-- The unit sphere $U$ is closed. -/
theorem isClosed_unitSphere : IsClosed unitSphere :=
  isClosed_eq (by fun_prop) continuous_const

/-- The unit sphere $U$ is contained in the closed unit ball of the sup norm. -/
theorem unitSphere_subset_closedBall : unitSphere ⊆ closedBall 0 1 := by
  intro x hx
  have hx' : ∑ j, x j ^ 2 = 1 := hx
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [hx'] at hle
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- The unit sphere $U$ is compact, because it is closed and contained in the unit cube. -/
theorem isCompact_unitSphere : IsCompact unitSphere :=
  Metric.isCompact_of_isClosed_isBounded isClosed_unitSphere
    (Metric.isBounded_closedBall.subset unitSphere_subset_closedBall)

instance compactSpace_unitSphere : CompactSpace unitSphere :=
  isCompact_iff_compactSpace.1 isCompact_unitSphere

/-- **Definition 7.5.8** of [han2009theoretical]. For an integer $N \ge 0$, the space $\mathbb{S}_N$
of **spherical polynomials of degree at most $N$** is the set of restrictions to the unit sphere
$U \subseteq \mathbb{R}^3$ of the polynomials (7.5.19) in $(x, y, z)$ of total degree at most
$N$. It is a subspace of $C(U)$.

The definition is `Approximation.mvPolyLE` for $D = U$, the same construction that gives the
space $\Pi_n^d \subseteq C(D)$ of Chapter 14. The dimension count
$\dim \mathbb{S}_N = (N + 1)^2$ of (7.5.21) is not formalized;
`AtkinsonHan.Chapter07.finrank_definition_7_5_8_le` gives an upper bound only. -/
noncomputable def definition_7_5_8 (N : ℕ) : Submodule ℝ C(unitSphere, ℝ) :=
  Approximation.mvPolyLE unitSphere N

/-- **Definition 7.5.8** of [han2009theoretical], unfolded. A function $f \in C(U)$ lies in
$\mathbb{S}_N$ if and only if there is a polynomial $p$ in $(x, y, z)$ of total degree at most
$N$ with $f(x) = p(x)$ for all $x \in U$. -/
theorem mem_definition_7_5_8 {N : ℕ} {f : C(unitSphere, ℝ)} :
    f ∈ definition_7_5_8 N ↔ ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ N ∧
      ∀ x : unitSphere, f x = MvPolynomial.eval (x : Fin 3 → ℝ) p := by
  rw [definition_7_5_8, Approximation.mem_mvPolyLE_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun _ => rfl⟩
  · rintro ⟨p, hp, hf⟩
    exact ⟨p, hp, by ext x; exact (hf x).symm⟩

/-- The spaces of spherical polynomials increase: $\mathbb{S}_N \subseteq \mathbb{S}_M$ for
$N \le M$. -/
theorem definition_7_5_8_mono : Monotone definition_7_5_8 := fun _ _ h =>
  Approximation.mvPolyLE_mono h

/-- Every constant function on $U$ lies in $\mathbb{S}_N$ for every $N$. -/
theorem const_mem_definition_7_5_8 (c : ℝ) (N : ℕ) :
    ContinuousMap.const unitSphere c ∈ definition_7_5_8 N :=
  mem_definition_7_5_8.2 ⟨MvPolynomial.C c, by simp, by simp⟩

instance finiteDimensional_definition_7_5_8 (N : ℕ) :
    FiniteDimensional ℝ (definition_7_5_8 N) :=
  inferInstanceAs (Module.Finite ℝ ((MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map
    (Approximation.toContinuousMapOn unitSphere)))

/-- For every $N$,
$$\dim \mathbb{S}_N \le \binom{N + 3}{3},$$
the dimension of the space of polynomials of degree at most $N$ in three variables, because
$\mathbb{S}_N$ is the image of this space under restriction.

The source states the equality $\dim \mathbb{S}_N = (N + 1)^2$ (7.5.21), which is smaller,
because restriction to $U$ has a large kernel
(`AtkinsonHan.Chapter07.not_injective_toContinuousMapOn_unitSphere`). The equality is not
formalized; it needs the decomposition into the spherical harmonics of Definition 7.5.9. -/
theorem finrank_definition_7_5_8_le (N : ℕ) :
    Module.finrank ℝ (definition_7_5_8 N) ≤ (N + 3).choose 3 := by
  have h := Submodule.finrank_map_le (Approximation.toContinuousMapOn unitSphere)
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N)
  have he := MvPolynomial.finrank_restrictTotalDegree (Fin 3) N ℝ
  simp only [Fintype.card_fin] at he
  rw [he] at h
  exact h

/-- The remark after Definition 7.5.8: the polynomial $x^2 + y^2 + z^2$ restricts to the constant
$1$ on $U$, so a polynomial of degree $N$ can restrict to a spherical polynomial of lower
degree. -/
theorem toContinuousMapOn_normSq_unitSphere :
    Approximation.toContinuousMapOn unitSphere
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2) = 1 := by
  ext x
  have hx : ∑ i, (x : Fin 3 → ℝ) i ^ 2 = 1 := x.2
  rw [Fin.sum_univ_three] at hx
  change MvPolynomial.eval (x : Fin 3 → ℝ)
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2) = 1
  simp only [map_add, map_pow, MvPolynomial.eval_X]
  linarith

/-- Restriction of polynomials in three variables to $U$ is not injective, because
$x^2 + y^2 + z^2 - 1$ is a nonzero polynomial that restricts to $0$.

So `Approximation.finrank_mvPolyLE`, which needs a set with nonempty interior, does not apply to
$U$, and `AtkinsonHan.Chapter07.finrank_definition_7_5_8_le` is only an inequality. -/
theorem not_injective_toContinuousMapOn_unitSphere :
    ¬ Function.Injective (Approximation.toContinuousMapOn unitSphere) := by
  intro h
  have key : (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2
      : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C 1 := by
    apply h
    rw [toContinuousMapOn_normSq_unitSphere]
    ext x
    simp
  have h0 := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) key
  simp at h0

/-- **Equation (7.5.30)** of [han2009theoretical]. For an integer $N \ge 0$ and $g \in C(U)$, the
**minimax error** of the approximation of $g$ by spherical polynomials of degree at most $N$ is
$$\rho_N(g) = \inf_{p \in \mathbb{S}_N} \|g - p\|_\infty.$$

The definition is the distance `Metric.infDist` from $g$ to $\mathbb{S}_N$ in $C(U)$. -/
noncomputable def equation_7_5_30 (N : ℕ) (g : C(unitSphere, ℝ)) : ℝ :=
  Metric.infDist g (definition_7_5_8 N : Set C(unitSphere, ℝ))

/-- The minimax error is nonnegative: $\rho_N(g) \ge 0$. -/
theorem equation_7_5_30_nonneg (N : ℕ) (g : C(unitSphere, ℝ)) : 0 ≤ equation_7_5_30 N g :=
  Metric.infDist_nonneg

/-- For every $g \in C(U)$, the minimax error $\rho_N(g)$ decreases in $N$, because the spaces
$\mathbb{S}_N$ increase. -/
theorem equation_7_5_30_antitone (g : C(unitSphere, ℝ)) :
    Antitone fun N => equation_7_5_30 N g := fun _ _ h =>
  Metric.infDist_le_infDist_of_subset (definition_7_5_8_mono h) ⟨0, Submodule.zero_mem _⟩

/-- **Equation (7.5.30)** of [han2009theoretical], convergence. For every $g \in C(U)$,
$$\rho_N(g) \to 0 \quad \text{as } N \to \infty.$$

The source records this after (7.5.30), with the remark that it follows from the
Stone–Weierstrass theorem, Theorem 3.1.2. The polynomial functions on $U$ form a subalgebra of
$C(U)$ that contains the constants and separates points, so it is dense; each of its elements
lies in some $\mathbb{S}_N$, and $\rho_N(g)$ decreases in $N$. This is the qualitative part of
Theorem 7.5.10, whose rate is not formalized. -/
theorem equation_7_5_30_tendsto_zero (g : C(unitSphere, ℝ)) :
    Tendsto (fun N => equation_7_5_30 N g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, f, hfN, hf⟩ := exists_mem_mvPolyLE_near unitSphere g hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : equation_7_5_30 N g ≤ ‖f - g‖ := by
    have hmem : f ∈ (definition_7_5_8 N : Set C(unitSphere, ℝ)) := hfN
    have := Metric.infDist_le_dist_of_mem (x := g) hmem
    rwa [dist_eq_norm, norm_sub_rev] at this
  have h2 : equation_7_5_30 n g ≤ equation_7_5_30 N g := equation_7_5_30_antitone g hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (equation_7_5_30_nonneg n g)]
  linarith

end AtkinsonHan.Chapter07
