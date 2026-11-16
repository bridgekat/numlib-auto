/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.Aliasing
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.Sobolev.Periodic.Smooth

/-!
# Quarteroni, Sacco and Saleri, Section 10.9: Fourier trigonometric polynomials

This module formalizes Section 10.9 of [quarteroni2000numerical]. On $(0, 2\pi)$ the Fourier
polynomials are $\varphi_k(x) = e^{ikx}$, and a function $f \in L^2(0, 2\pi)$ has the Fourier series
$\sum_k \hat f_k \varphi_k$ with $\hat f_k = \frac{1}{2\pi} \int_0^{2\pi} f(x) e^{-ikx} \, dx$
(10.48). For even $N$ the truncation $f_N^* = \sum_{k=-N/2}^{N/2-1} \hat f_k \varphi_k$ (10.50) is
the best $L^2$ approximation of $f$ in the space $S_N$ spanned by these $N$ exponentials. On the
nodes $x_j = jh$, $h = 2\pi/N$, the discrete scalar product $(f, g)_N = h \sum_{j=0}^{N-1} f(x_j)
\overline{g(x_j)}$ (10.51) gives the discrete Fourier coefficients $\tilde f_k$ (10.52) and the
discrete Fourier series $\Pi^F_N f(x) = \sum_{k=0}^{N-1} \tilde f_k e^{i(k - N/2)x}$ (10.53), which
interpolates $f$ at the nodes.

The module states the discrete orthogonality of Lemma 10.1, the interpolation property with the
matrices $T$ and $C = T^{-1}$ of the discrete Fourier transform (DFT) and its inverse (IDFT)
(10.55), the discrete least-squares property of $\Pi^F_N f$, four error estimates for $C^s$ periodic
functions, the Lanczos smoothing factors (10.56), and the radix-2 step of the fast Fourier transform
(Section 10.9.2). The proofs specialize `Numlib.Analysis.Fourier.DFT`,
`Numlib.Analysis.Fourier.Aliasing`, `Numlib.Analysis.Sobolev.Periodic.Smooth` and
`Numlib.Analysis.Normed.Module.BestApprox`.

## Main definitions

* Equation (10.50), `QuarteroniSaccoSaleri.Chapter10.trigTruncation`: the truncation $f_N^*$ of
  order $N$ of the Fourier series.
* Equation (10.51), `QuarteroniSaccoSaleri.Chapter10.equation_10_51`: the discrete scalar product
  $(f, g)_N$; `QuarteroniSaccoSaleri.Chapter10.trigDiscreteNorm` is the discrete norm $\|f\|_N$.
* Equation (10.52), `QuarteroniSaccoSaleri.Chapter10.equation_10_52`: the discrete Fourier
  coefficients $\tilde f_k$.
* Equation (10.53), `QuarteroniSaccoSaleri.Chapter10.discreteSeries`: the discrete Fourier series
  $\Pi^F_N f$.
* The root of unity of (10.52), `QuarteroniSaccoSaleri.Chapter10.principalRoot`:
  $W_N = e^{-2\pi i/N}$.
* The matrices after (10.55), `QuarteroniSaccoSaleri.Chapter10.dftMatrix` and
  `QuarteroniSaccoSaleri.Chapter10.idftMatrix`: the matrices $T$ of the DFT and $C$ of the IDFT.
* Equation (10.56), `QuarteroniSaccoSaleri.Chapter10.equation_10_56`: the Lanczos smoothing factors
  $\sigma_k$.

## Main results

* Equation (10.48), `QuarteroniSaccoSaleri.Chapter10.equation_10_48` and
  `QuarteroniSaccoSaleri.Chapter10.equation_10_48_hasSum`: the formula for $\hat f_k$, and the
  convergence of the Fourier series of $f \in L^2(0, 2\pi)$ to $f$ in $L^2$.
* Equation (10.49), `QuarteroniSaccoSaleri.Chapter10.equation_10_49`: the coefficients
  $\hat f_k = a_k + i b_k$ in real form.
* The remark after (10.49), `QuarteroniSaccoSaleri.Chapter10.equation_10_49_conj`:
  $\hat f_{-k} = \overline{\hat f_k}$ for real $f$.
* Section 10.9, least-squares optimality,
  `QuarteroniSaccoSaleri.Chapter10.trigTruncation_isBestApprox`: $f_N^*$ is the best $L^2$
  approximation of $f$ in $S_N$.
* Equation (10.52), `QuarteroniSaccoSaleri.Chapter10.equation_10_52_eq_discreteInner`:
  $\tilde f_k = (f, \tilde\varphi_k)_N / 2\pi$ with $\tilde\varphi_k(x) = e^{i(k - N/2)x}$.
* Lemma 10.1, `QuarteroniSaccoSaleri.Chapter10.lemma_10_1`:
  $(\varphi_l, \varphi_j)_N = 2\pi \delta_{jl}$ for $0 \le l, j \le N - 1$ (10.54).
* Equation (10.55), `QuarteroniSaccoSaleri.Chapter10.equation_10_55`: $\Pi^F_N f(x_j) = f(x_j)$, and
  $f(x_j) = \sum_k \tilde f_k W_N^{-(k - N/2)j}$.
* The DFT and IDFT after (10.55), `QuarteroniSaccoSaleri.Chapter10.equation_10_55_dft`,
  `QuarteroniSaccoSaleri.Chapter10.equation_10_55_idft` and
  `QuarteroniSaccoSaleri.Chapter10.equation_10_55_inv`: $\tilde f = T f$, $f = C \tilde f$ at the
  nodes, and $CT = I$.
* Section 10.9, discrete least-squares property,
  `QuarteroniSaccoSaleri.Chapter10.interp_isBestApprox_discrete`:
  $\|f - \Pi^F_N f\|_N \le \|f - g\|_N$.
* Section 10.9, interpolation estimates, `QuarteroniSaccoSaleri.Chapter10.fourier_interp_error` and
  `QuarteroniSaccoSaleri.Chapter10.fourier_interp_error_sup`:
  $\|f - \Pi^F_N f\|_{L^2} \le C N^{-s} \|f\|_s$ and
  $\max |f - \Pi^F_N f| \le C N^{1/2 - s} \|f\|_s$ for $f$ periodic of class $C^s$, $s \ge 1$.
* Section 10.9, quadrature estimates, `QuarteroniSaccoSaleri.Chapter10.fourier_discreteInner_error`,
  `QuarteroniSaccoSaleri.Chapter10.fourier_trapezoid_error_sobolev` and
  `QuarteroniSaccoSaleri.Chapter10.fourier_trapezoid_error`: $|(f, v_N) - (f, v_N)_N| \le C N^{-s}
  \|f\|_s \|v_N\|_{L^2}$ for $v_N \in S_N$, and at $v_N = 1$ the error bound $C N^{-s} \|f\|_s$ of
  the composite trapezoidal rule.
* Section 10.9.2, `QuarteroniSaccoSaleri.Chapter10.fft_radix_two`: the Cooley–Tukey splitting of a
  transform of even order.

## Proof outline

The book quotes the four error estimates from Canuto, Hussaini, Quarteroni and Zang without proof.
Here they are proved. The Fourier coefficients of a $C^s$ periodic function $f$ form an element
$\phi$ of the coefficient-form Sobolev space $H^s$ with $\|\phi\| \le (2\pi)^{-1/2} \|f\|_s$. The
aliasing formula $\tilde f_k - \hat f_k = \sum_{m \neq 0} \hat f_{k + mN}$ then bounds the error in
$\ell^2$ and in $\ell^1$ over the window of frequencies.

## Conventions

* The book takes $N$ even. In Lean, $N/2$ is the natural-number quotient `N / 2`, and the
  definitions accept every $N$.
* The nodes are $x_j = 2\pi j / N$ (`Quadrature.angleNode N j`), and $h = 2\pi/N$.
* The window of frequencies is `DFT.window N`, the integers $k$ with $-N/2 \le k \le N/2 - 1$. The
  space $S_N$ is the set of trigonometric polynomials `DFT.windowTrigPoly N c` with frequencies in
  this window.
* The norm $\|f\|_s = \bigl(\sum_{k \le s} \|f^{(k)}\|^2_{L^2(0, 2\pi)}\bigr)^{1/2}$ of the book is
  the square root of `PeriodicSobolev.derivNormSq s f`.

## Implementation notes

* A complex function on $(0, 2\pi)$ in the $L^2$ statements is a function on the circle
  `AddCircle (2 * π)`. The space $L^2(0, 2\pi)$ is
  `MeasureTheory.Lp ℂ 2 AddCircle.haarAddCircle`. The Fourier coefficients are Mathlib's
  `fourierCoeff`, whose normalization
  $\frac{1}{2\pi} \int_0^{2\pi}$ is that of (10.48).
* The discrete statements use functions $\mathbb{R} \to \mathbb{C}$. The coefficients and the series
  are `DFT.coeff` and `DFT.interp` at the window offset $m = -N/2$, and the matrices of (10.55) are
  built from `Matrix.dft`.
* The constants of the error estimates are explicit but not sharp. The book leaves them unspecified.
  They are $\sqrt{1 + 2\zeta(2s)}\, 2^s$, $2^{s+1} \sqrt{2\zeta(2s)} / \sqrt{2\pi}$,
  $\sqrt{2\zeta(2s)}\, 2^s$ and $\sqrt{4\pi\zeta(2s)}$, with $\zeta$ the real zeta function
  `zetaReal`.

## Deviations from the source

* **Equations (10.50) and (10.52)** (typo). The book writes the coefficients as
  $(f, \tilde\varphi_k)/2\pi$ and $(f, \tilde\varphi_k)_N/2\pi$ with
  $\tilde\varphi_k = e^{-i(k - N/2)x}$, which gives the wrong sign in the exponent. The library uses
  $\tilde\varphi_k = e^{i(k - N/2)x}$. See
  `QuarteroniSaccoSaleri.Chapter10.equation_10_52_eq_discreteInner`.
* **Equation (10.55) and the matrix $C$** (correction). The book prints
  $C_{jk} = W_N^{-(j - N/2)k}$, which does not invert $T$. The library uses
  $C_{jk} = W_N^{-(k - N/2)j}$. See `QuarteroniSaccoSaleri.Chapter10.idftMatrix`.
* **The discrete least-squares property** (generalization). The book compares $\Pi^F_N f$ with every
  $g \in S_N$. The library compares it with every function $g$. See
  `QuarteroniSaccoSaleri.Chapter10.interp_isBestApprox_discrete`.

## Not formalized

* **The Gibbs phenomenon (Section 10.9.1).** The book describes it and does not state it as a
  result.
* **The operation count of the FFT.** It is a statement about an algorithm.
-/

open AddCircle Complex Finset Matrix MeasureTheory Quadrature

open scoped Real ComplexConjugate

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### Equations (10.48)–(10.49): the Fourier series -/

/-- **Equation (10.48)** of [quarteroni2000numerical], the Fourier coefficients. Let
$f : (0, 2\pi) \to \mathbb{C}$, read as a function on the circle $\mathbb{R}/2\pi\mathbb{Z}$,
and let $k \in \mathbb{Z}$. The $k$-th Fourier coefficient of $f$ is
$$\hat f_k = \frac{1}{2\pi} \int_0^{2\pi} f(x) e^{-ikx} \, dx.$$

The coefficient is Mathlib's `fourierCoeff` on `AddCircle (2 * π)`. The proof specializes
`fourierCoeff_eq_intervalIntegral`. -/
theorem equation_10_48 (f : AddCircle (2 * π) → ℂ) (k : ℤ) :
    fourierCoeff f k
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..2 * π, f x * Complex.exp (-(k * x * I)) := by
  rw [fourierCoeff_eq_intervalIntegral f k 0, zero_add, Complex.real_smul]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul, mul_comm]
  congr 2
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  field_simp

/-- **Equation (10.48)** of [quarteroni2000numerical], the Fourier series. For every
$f \in L^2(0, 2\pi)$ the Fourier series converges to $f$ in $L^2(0, 2\pi)$:
$$f = \sum_{k \in \mathbb{Z}} \hat f_k \varphi_k, \qquad \varphi_k(x) = e^{ikx}.$$

Here $L^2(0, 2\pi)$ is `MeasureTheory.Lp ℂ 2 AddCircle.haarAddCircle`, and $\varphi_k$ is
`fourierLp 2 k`. The proof specializes Mathlib's `hasSum_fourier_series_L2`. -/
theorem equation_10_48_hasSum (f : Lp ℂ 2 (@haarAddCircle (2 * π) _)) :
    HasSum (fun k : ℤ => fourierCoeff f k • fourierLp 2 k) f :=
  hasSum_fourier_series_L2 f

/-- A function $f$ on the circle $\mathbb{R}/2\pi\mathbb{Z}$ that is integrable for the Haar measure
lifts to a function on $\mathbb{R}$ that is interval integrable on $[0, 2\pi]$. This supports
(10.49), `QuarteroniSaccoSaleri.Chapter10.equation_10_49`. -/
theorem intervalIntegrable_of_integrable_haarAddCircle {f : AddCircle (2 * π) → ℂ}
    (hf : Integrable f haarAddCircle) :
    IntervalIntegrable (fun x : ℝ => f x) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  have hf' : Integrable f volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have := (AddCircle.measurePreserving_mk (2 * π) 0).integrable_comp hf'.aestronglyMeasurable
  rw [zero_add] at this
  exact this.mpr hf'

/-- **Equation (10.49)** of [quarteroni2000numerical]. Let $f : (0, 2\pi) \to \mathbb{C}$ be
integrable, read as a function on the circle $\mathbb{R}/2\pi\mathbb{Z}$, and write
$f = \alpha + i\beta$ with $\alpha$ and $\beta$ real. Then for every $k \in \mathbb{Z}$ the
Fourier coefficient is $\hat f_k = a_k + i b_k$ with
$$a_k = \frac{1}{2\pi} \int_0^{2\pi} (\alpha \cos kx + \beta \sin kx) \, dx, \qquad b_k =
  \frac{1}{2\pi} \int_0^{2\pi} (-\alpha \sin kx + \beta \cos kx) \, dx.$$

The proof expands $e^{-ikx} = \cos kx - i \sin kx$ in (10.48). -/
theorem equation_10_49 {f : AddCircle (2 * π) → ℂ} (hf : Integrable f haarAddCircle) (k : ℤ) :
    fourierCoeff f k
      = ((1 / (2 * π) * ∫ x in (0 : ℝ)..2 * π,
            ((f x).re * Real.cos (k * x) + (f x).im * Real.sin (k * x)) : ℝ) : ℂ)
        + I * ((1 / (2 * π) * ∫ x in (0 : ℝ)..2 * π,
            (-(f x).re * Real.sin (k * x) + (f x).im * Real.cos (k * x)) : ℝ) : ℂ) := by
  have hint := intervalIntegrable_of_integrable_haarAddCircle hf
  have hsplit : ∀ x : ℝ, f x * Complex.exp (-(k * x * I))
      = (((f x).re * Real.cos (k * x) + (f x).im * Real.sin (k * x) : ℝ) : ℂ)
        + I * ((-(f x).re * Real.sin (k * x) + (f x).im * Real.cos (k * x) : ℝ) : ℂ) := by
    intro x
    rw [show -((k : ℂ) * x * I) = (-(k * x) : ℝ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    apply Complex.ext <;> simp <;> ring
  have hre : IntervalIntegrable (fun x : ℝ => (f x).re) volume 0 (2 * π) :=
    ⟨hint.1.re, hint.2.re⟩
  have him : IntervalIntegrable (fun x : ℝ => (f x).im) volume 0 (2 * π) :=
    ⟨hint.1.im, hint.2.im⟩
  have h1r : IntervalIntegrable
      (fun x : ℝ => (f x).re * Real.cos (k * x) + (f x).im * Real.sin (k * x)) volume 0 (2 * π) :=
    (hre.mul_continuousOn (by fun_prop)).add (him.mul_continuousOn (by fun_prop))
  have h2r : IntervalIntegrable
      (fun x : ℝ => -(f x).re * Real.sin (k * x) + (f x).im * Real.cos (k * x)) volume 0 (2 * π) :=
    (hre.neg.mul_continuousOn (by fun_prop)).add (him.mul_continuousOn (by fun_prop))
  have h1 : IntervalIntegrable (fun x : ℝ =>
      (((f x).re * Real.cos (k * x) + (f x).im * Real.sin (k * x) : ℝ) : ℂ)) volume 0 (2 * π) :=
    ⟨h1r.1.ofReal, h1r.2.ofReal⟩
  have h2 : IntervalIntegrable (fun x : ℝ =>
      ((-(f x).re * Real.sin (k * x) + (f x).im * Real.cos (k * x) : ℝ) : ℂ)) volume 0 (2 * π) :=
    ⟨h2r.1.ofReal, h2r.2.ofReal⟩
  rw [equation_10_48]
  simp only [hsplit]
  rw [intervalIntegral.integral_add h1 (h2.const_mul I), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- **The remark after (10.49)** of [quarteroni2000numerical]. Let $f : (0, 2\pi) \to \mathbb{C}$ be
real-valued, read as a function on the circle $\mathbb{R}/2\pi\mathbb{Z}$. Then
$\hat f_{-k} = \overline{\hat f_k}$ for every $k \in \mathbb{Z}$.

Conjugation of the integrand of (10.48) changes $e^{-ikx}$ into $e^{ikx}$ and does not change
$f$. -/
theorem equation_10_49_conj {f : AddCircle (2 * π) → ℂ} (hf : ∀ x, (f x).im = 0) (k : ℤ) :
    fourierCoeff f (-k) = conj (fourierCoeff f k) := by
  simp only [fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, fourier_neg, Complex.conj_eq_iff_im.mpr (hf x)]

/-! ### Equation (10.50): the truncation of order $N$ and its least-squares optimality -/

/-- **Equation (10.50)** of [quarteroni2000numerical]. For $f \in L^2(0, 2\pi)$ and even $N$, the
**truncation of order $N$** of the Fourier series of $f$ is
$$f_N^*(x) = \sum_{k=-N/2}^{N/2-1} \hat f_k e^{ikx},$$
an element of $L^2(0, 2\pi)$.

The sum runs over `DFT.window N`, the $N$ integers that start at $-\lfloor N/2 \rfloor$, so the
definition also applies to odd $N$. -/
noncomputable def trigTruncation (N : ℕ) (f : Lp ℂ 2 (@haarAddCircle (2 * π) _)) :
    Lp ℂ 2 (@haarAddCircle (2 * π) _) :=
  ∑ k ∈ DFT.window N, fourierCoeff f k • fourierLp 2 k

/-- **Section 10.9** of [quarteroni2000numerical], the least-squares optimality of the truncation of
order $N$. Let $f \in L^2(0, 2\pi)$, let $N \in \mathbb{N}$, and let $S_N$ be the span of
$e^{ikx}$ for $-N/2 \le k \le N/2 - 1$. Then $f_N^* \in S_N$ and
$$\|f - f_N^*\|_{L^2} = \min_{g \in S_N} \|f - g\|_{L^2}.$$

The statement is `IsBestApprox` for the span of the functions `fourierLp 2 k`, $k$ in
`DFT.window N`. The proof shows that $f_N^*$ is the orthogonal projection of $f$ onto $S_N$: by
the orthonormality of the Fourier system, $f - f_N^*$ is orthogonal to every $e^{ikx}$ in the
window, and the theorem of Pythagoras gives the bound. -/
theorem trigTruncation_isBestApprox (N : ℕ) (f : Lp ℂ 2 (@haarAddCircle (2 * π) _)) :
    IsBestApprox (SetLike.coe (Submodule.span ℂ (fourierLp 2 ''
        (DFT.window N : Set ℤ))))
      f (trigTruncation N f) := by
  set W : Finset ℤ := DFT.window N with hW
  set K : Submodule ℂ (Lp ℂ 2 (@haarAddCircle (2 * π) _)) :=
    Submodule.span ℂ (fourierLp 2 '' (W : Set ℤ)) with hK
  have hmem : trigTruncation N f ∈ K := by
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨k, hk, rfl⟩
  -- the residual is orthogonal to every element of the window, hence to `S_N`
  have horth : ∀ j ∈ W, inner ℂ (fourierLp 2 j) (f - trigTruncation N f) = 0 := by
    intro j hj
    have hon := orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * π))
    have hrepr : inner ℂ (fourierLp 2 j) f = fourierCoeff f j := by
      rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]
    rw [inner_sub_right, trigTruncation, inner_sum, hrepr, Finset.sum_eq_single j
      (fun k _ hk => by rw [inner_smul_right, hon, ite_eq_right (Ne.symm hk), mul_zero])
      (fun h => absurd hj h), inner_smul_right, hon, ite_eq_left rfl, mul_one, sub_self]
  have horthK : ∀ g ∈ K, inner ℂ g (f - trigTruncation N f) = 0 := by
    intro g hg
    have hle : K ≤ (ℂ ∙ (f - trigTruncation N f))ᗮ := by
      rw [hK, Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth j hj
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hg)
  refine ⟨hmem, fun g hg => ?_⟩
  have h0 : inner ℂ (f - trigTruncation N f) (trigTruncation N f - g) = 0 := by
    rw [← inner_conj_symm, horthK _ (K.sub_mem hmem hg), map_zero]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_sub_cancel] at hpyth
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [sq, sq, hpyth]
  linarith [mul_self_nonneg ‖trigTruncation N f - g‖]

/-! ### Equations (10.51)–(10.53): the discrete scalar product and the discrete Fourier series -/

/-- **Equation (10.51)** of [quarteroni2000numerical]. For $N \in \mathbb{N}$ and
$f, g : \mathbb{R} \to \mathbb{C}$, the **discrete scalar product** is
$$(f, g)_N = h \sum_{j=0}^{N-1} f(x_j) \overline{g(x_j)}, \qquad h = \frac{2\pi}{N}, \quad x_j =
  jh.$$

The node $x_j$ is `Quadrature.angleNode N j`. -/
noncomputable def equation_10_51 (N : ℕ) (f g : ℝ → ℂ) : ℂ :=
  ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N, f (angleNode N j) * conj (g (angleNode N j))

/-- **Section 10.9** of [quarteroni2000numerical], the discrete norm. For $N \in \mathbb{N}$ and
$f : \mathbb{R} \to \mathbb{C}$, the **discrete norm** is $\|f\|_N = (f, f)_N^{1/2}$, with the
discrete scalar product (10.51).

In Lean it is the real square root of the real part of $(f, f)_N$. The number $(f, f)_N$ is real
and nonnegative. -/
noncomputable def trigDiscreteNorm (N : ℕ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (equation_10_51 N f f).re

/-- **Equation (10.52)** of [quarteroni2000numerical]. For even $N$, $f : \mathbb{R} \to \mathbb{C}$
and $k = 0, \dots, N - 1$, the **discrete Fourier coefficients** are
$$\tilde f_k = \frac{1}{N} \sum_{j=0}^{N-1} f(x_j) W_N^{(k - N/2)j}, \qquad W_N = e^{-2\pi
  i/N}.$$

The definition is `DFT.coeff` at the window offset $m = -N/2$. The index $k$ is a natural
number, and the definition gives a value for every $k$. -/
noncomputable def equation_10_52 (N : ℕ) (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  DFT.coeff N (-((N / 2 : ℕ) : ℤ)) f k

/-- **Equation (10.53)** of [quarteroni2000numerical]. For even $N$ and
$f : \mathbb{R} \to \mathbb{C}$, the **discrete Fourier series of order $N$** is
$$\Pi^F_N f(x) = \sum_{k=0}^{N-1} \tilde f_k e^{i(k - N/2)x}.$$

The definition is `DFT.interp` at the window offset $m = -N/2$. -/
noncomputable def discreteSeries (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  DFT.interp N (-((N / 2 : ℕ) : ℤ)) f x

/-- **Equation (10.52)** of [quarteroni2000numerical], as a discrete scalar product. Let $N \ge 1$,
$f : \mathbb{R} \to \mathbb{C}$ and $k \in \mathbb{N}$. Then
$$\tilde f_k = \frac{(f, \tilde\varphi_k)_N}{2\pi}, \qquad \tilde\varphi_k(x) = e^{i(k -
  N/2)x}.$$

**Typo.** The book prints $\tilde\varphi_k = e^{-i(k - N/2)x}$. With the scalar product
$(f, g)_N = h \sum_j f(x_j) \overline{g(x_j)}$ of (10.51), this gives the wrong sign in the
exponent. The same misprint appears in (10.50) for the continuous scalar product
$(f, g) = \int_0^{2\pi} f \bar g$. -/
theorem equation_10_52_eq_discreteInner {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) (k : ℕ) :
    equation_10_52 N f k
      = equation_10_51 N f
          (fun x => Complex.exp ((((k : ℤ) - (N / 2 : ℕ) : ℤ) : ℂ) * x * I)) / (2 * π) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [equation_10_52, DFT.coeff_def, equation_10_51]
  have hterm : ∀ j : ℕ,
      conj (Complex.exp ((((k : ℤ) - (N / 2 : ℕ) : ℤ) : ℂ) * (angleNode N j : ℝ) * I))
        = Complex.exp (-((((k : ℤ) + -((N / 2 : ℕ) : ℤ) : ℤ) : ℂ) * (angleNode N j : ℝ) * I)) := by
    intro j
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hterm]
  push_cast
  field_simp
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf

/-- **Lemma 10.1** of [quarteroni2000numerical]. Let $N \ge 1$ and $0 \le l, j \le N - 1$. The
Fourier polynomials $\varphi_l = e^{ilx}$ and $\varphi_j = e^{ijx}$ satisfy (10.54):
$$(\varphi_l, \varphi_j)_N = h \sum_{k=0}^{N-1} e^{i(l - j)kh} = 2\pi \delta_{jl}.$$

The proof specializes `DFT.sum_exp_sub_angleNode`, which is `Quadrature.sum_exp_angleNode` at
$p = l - j$. -/
theorem lemma_10_1 {N : ℕ} (hN : 0 < N) {l j : ℕ} (hl : l < N) (hj : j < N) :
    equation_10_51 N (fun x => Complex.exp (l * x * I)) (fun x => Complex.exp (j * x * I))
      = if j = l then (2 * π : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [equation_10_51]
  have hterm : ∀ k : ℕ, Complex.exp (l * (angleNode N k : ℝ) * I)
      * conj (Complex.exp (j * (angleNode N k : ℝ) * I))
      = Complex.exp ((((l : ℤ) - j : ℤ) : ℂ) * (angleNode N k : ℝ) * I) := by
    intro k
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, map_natCast, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, DFT.sum_exp_sub_angleNode hN hl hj]
  by_cases h : j = l
  · rw [ite_eq_left h.symm, ite_eq_left h]
    push_cast
    field_simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]

/-! ### Equation (10.55): the interpolation property, the DFT and the IDFT -/

/-- **Equation (10.55)** of [quarteroni2000numerical], with the interpolation property. Let
$N \ge 1$, $f : \mathbb{R} \to \mathbb{C}$ and $0 \le j \le N - 1$. Then
$\Pi^F_N f(x_j) = f(x_j)$, and
$$f(x_j) = \sum_{k=0}^{N-1} \tilde f_k W_N^{-(k - N/2)j}, \qquad W_N = e^{-2\pi i/N}.$$

**Correction.** The book puts the shift by $N/2$ on the wrong index and prints
$W_N^{-(j - N/2)k}$. The book's own derivation $\Pi^F_N f(x_j) = \sum_k \tilde f_k e^{ikjh}
e^{-ijhN/2}$ gives the exponent $-(k - N/2)j$. The two forms differ by the factor $(-1)^{j-k}$.
See `QuarteroniSaccoSaleri.Chapter10.idftMatrix`.

The proof specializes `DFT.interp_angleNode`. -/
theorem equation_10_55 {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) {j : ℕ} (hj : j < N) :
    discreteSeries N f (angleNode N j) = f (angleNode N j) ∧
      f (angleNode N j) = ∑ k ∈ range N, equation_10_52 N f k
        * Complex.exp (-(2 * π * I / N)) ^ (-((((k : ℤ) - (N / 2 : ℕ) : ℤ)) * j)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨DFT.interp_angleNode hN _ f hj, ?_⟩
  conv_lhs => rw [← DFT.interp_angleNode hN (-((N / 2 : ℕ) : ℤ)) f hj]
  rw [DFT.interp_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [equation_10_52]
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  simp only [angleNode]
  push_cast
  field_simp
  ring

/-- **Equation (10.52)** of [quarteroni2000numerical], the root of unity. For $N \in \mathbb{N}$,
the principal $N$-th root of unity of the book is $W_N = e^{-2\pi i/N}$. -/
noncomputable def principalRoot (N : ℕ) : ℂ := Complex.exp (-(2 * π * I / N))

/-- **The matrix $T$ after (10.55)** of [quarteroni2000numerical]. For $N \in \mathbb{N}$, the
matrix $T \in \mathbb{C}^{N \times N}$ of the **discrete Fourier transform** has the entries
$$T_{kj} = \frac{1}{N} W_N^{(k - N/2)j}, \qquad 0 \le k, j \le N - 1.$$
-/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k j : Fin N =>
    (N : ℂ)⁻¹ * principalRoot N ^ ((((k : ℕ) : ℤ) - (N / 2 : ℕ)) * ((j : ℕ) : ℤ))

/-- **The matrix $C$ after (10.55)** of [quarteroni2000numerical]. For $N \in \mathbb{N}$, the
matrix $C \in \mathbb{C}^{N \times N}$ of the **inverse discrete Fourier transform** has the
entries
$$C_{jk} = W_N^{-(k - N/2)j}, \qquad 0 \le j, k \le N - 1.$$

**Correction.** The book prints $C_{jk} = W_N^{-(j - N/2)k}$. This differs from the entry above
by the factor $(-1)^{j-k}$, and that matrix does not invert $T$. The entry here follows from the
book's derivation of (10.55), and Program 89 of the book implements it. See
`QuarteroniSaccoSaleri.Chapter10.equation_10_55_inv`. -/
noncomputable def idftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k : Fin N =>
    principalRoot N ^ (-(((((k : ℕ) : ℤ) - (N / 2 : ℕ)) * ((j : ℕ) : ℤ))))

/-- For $N \ge 1$, $p \in \mathbb{Z}$ and $j \in \mathbb{N}$, the powers of $W_N$ are the values of
an exponential at the nodes: $W_N^{pj} = e^{-ipx_j}$. This supports the matrix forms of (10.55). -/
theorem principalRoot_zpow_mul {N : ℕ} (hN : 0 < N) (p : ℤ) (j : ℕ) :
    principalRoot N ^ (p * (j : ℤ)) = Complex.exp (-((p : ℂ) * (angleNode N j : ℝ) * I)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [principalRoot, ← Complex.exp_int_mul]
  congr 1
  simp only [angleNode]
  push_cast
  field_simp

/-- **The DFT after (10.55)** of [quarteroni2000numerical], as a product of a matrix and a vector.
For $N \ge 1$ and $f : \mathbb{R} \to \mathbb{C}$, the vector of the discrete Fourier
coefficients is
$$(\tilde f_k)_{k=0}^{N-1} = T \, (f(x_j))_{j=0}^{N-1}.$$
-/
theorem equation_10_55_dft {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) :
    (fun k : Fin N => equation_10_52 N f k)
      = dftMatrix N *ᵥ fun j : Fin N => f (angleNode N j) := by
  funext k
  rw [Matrix.mulVec_apply_eq_sum, equation_10_52, DFT.coeff_def, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dftMatrix, Matrix.of_apply, principalRoot_zpow_mul hN]
  push_cast
  ring_nf

/-- **The IDFT after (10.55)** of [quarteroni2000numerical], as a product of a matrix and a vector.
For $N \ge 1$ and $f : \mathbb{R} \to \mathbb{C}$, the interpolation property (10.55) in matrix
form is
$$(f(x_j))_{j=0}^{N-1} = C \, (\tilde f_k)_{k=0}^{N-1}.$$
-/
theorem equation_10_55_idft {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) :
    (fun j : Fin N => f (angleNode N j))
      = idftMatrix N *ᵥ fun k : Fin N => equation_10_52 N f k := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum, (equation_10_55 hN f j.isLt).2, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [idftMatrix, Matrix.of_apply, principalRoot, mul_comm]

/-- **$C = T^{-1}$ after (10.55)** of [quarteroni2000numerical]. For $N \ge 1$ the matrices of the
IDFT and the DFT satisfy $CT = I$, so $C = T^{-1}$.

The proof writes both matrices through $F_N$ = `Matrix.dft N` with $\omega = W_N^{-1}$:
$C = \operatorname{diag}(\omega^{-Nj/2}) F_N$ and $T = N^{-1} F_N^H
\operatorname{diag}(\omega^{Nj/2})$. Then $F_N F_N^H = N I$ (`Matrix.dft_mul_conjTranspose_dft`)
gives the result. -/
theorem equation_10_55_inv {N : ℕ} (hN : 0 < N) : idftMatrix N * dftMatrix N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set ω : ℂ := Complex.exp (2 * π * I / N) with hω
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hW : principalRoot N = ω⁻¹ := by
    rw [principalRoot, hω, ← Complex.exp_neg]
  set m : ℤ := -((N / 2 : ℕ) : ℤ) with hm
  -- the two matrices through `Matrix.dft`
  have hC : idftMatrix N = Matrix.diagonal (fun j : Fin N => ω ^ (m * (j : ℕ))) * Matrix.dft N := by
    ext j k
    rw [idftMatrix, Matrix.of_apply, Matrix.diagonal_mul, Matrix.dft_apply, hW, _root_.inv_zpow',
      neg_neg, hm, ← zpow_natCast, ← zpow_add₀ hω0]
    congr 1
    push_cast
    ring
  have hT : dftMatrix N = (N : ℂ)⁻¹ •
      ((Matrix.dft N)ᴴ * Matrix.diagonal (fun j : Fin N => ω ^ (-(m * (j : ℕ))))) := by
    ext k j
    rw [dftMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_diagonal,
      Matrix.conjTranspose_dft_apply, hW, _root_.inv_zpow', smul_eq_mul, hm, inv_pow,
      ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hω0]
    congr 2
    push_cast
    ring
  rw [hC, hT, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.dft N),
    Matrix.dft_mul_conjTranspose_dft, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hN', one_smul, Matrix.diagonal_mul_diagonal]
  ext j k
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · rw [← zpow_add₀ hω0, add_neg_cancel, zpow_zero]
  · rfl

/-! ### The discrete least-squares property -/

/-- **Section 10.9** of [quarteroni2000numerical], the discrete least-squares property of
$\Pi^F_N f$. Let $N \ge 1$ and $f, g : \mathbb{R} \to \mathbb{C}$. Then
$$\|f - \Pi^F_N f\|_N \le \|f - g\|_N.$$

**Generalization.** The book states the inequality for $g \in S_N$. It holds for every $g$,
because $f - \Pi^F_N f$ vanishes at every node, so its discrete norm is $0$. -/
theorem interp_isBestApprox_discrete {N : ℕ} (hN : 0 < N) (f g : ℝ → ℂ) :
    trigDiscreteNorm N (fun x => f x - discreteSeries N f x) ≤
      trigDiscreteNorm N (fun x => f x - g x) := by
  have h0 : trigDiscreteNorm N (fun x => f x - discreteSeries N f x) = 0 := by
    rw [trigDiscreteNorm, equation_10_51]
    have : ∀ j ∈ range N, (f (angleNode N j) - discreteSeries N f (angleNode N j))
        * conj (f (angleNode N j) - discreteSeries N f (angleNode N j)) = 0 := by
      intro j hj
      rw [discreteSeries, DFT.interp_angleNode hN _ f (Finset.mem_range.mp hj), sub_self,
        zero_mul]
    rw [Finset.sum_eq_zero this, mul_zero, Complex.zero_re, Real.sqrt_zero]
  rw [h0]
  exact Real.sqrt_nonneg _

/-! ### The interpolation and quadrature estimates -/

private theorem half_lt_of_one_le {s : ℕ} (hs : 1 ≤ s) : (1 : ℝ) / 2 < (s : ℝ) := by
  have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- **Section 10.9** of [quarteroni2000numerical], the $L^2$ interpolation error estimate. Let
$s \ge 1$ be an integer, let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class
$C^s$, and let $N \ge 1$. Then
$$\|f - \Pi^F_N f\|_{L^2(0, 2\pi)} \le C N^{-s} \|f\|_s, \qquad \|f\|_s = \Bigl(\sum_{k=0}^{s}
  \|f^{(k)}\|^2_{L^2(0, 2\pi)}\Bigr)^{1/2},$$
with $C = \sqrt{1 + 2\zeta(2s)}\, 2^s$.

The book quotes the estimate from Canuto, Hussaini, Quarteroni and Zang (1988), chapter 2, and
leaves $C$ unspecified. Here $\zeta$ is `zetaReal`, and $\|f\|_s^2$ is
`PeriodicSobolev.derivNormSq s f`. Let $\phi$ be the coefficient sequence of $f$, which is
`PeriodicSobolev.ofSmooth`. It lies in $H^s$ with $\|\phi\| \le (2\pi)^{-1/2} \|f\|_s$, and its
series sums to $f$. Then
`PeriodicSobolev.sqrt_intervalIntegral_norm_eval_sub_interp_sq_le` bounds the error by the
aliasing and truncation tails. -/
theorem fourier_interp_error {s : ℕ} (hs : 1 ≤ s) {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * π)) (hd : ContDiff ℝ s f) {N : ℕ} (hN : 0 < N) :
    √(∫ x in (0 : ℝ)..2 * π, ‖f x - discreteSeries N f x‖ ^ 2)
      ≤ √(1 + 2 * zetaReal (2 * s)) * 2 ^ s * (N : ℝ) ^ (-(s : ℝ))
        * √(PeriodicSobolev.derivNormSq s f) := by
  have h := PeriodicSobolev.sqrt_intervalIntegral_norm_eval_sub_interp_sq_le
    (half_lt_of_one_le hs) hN (PeriodicSobolev.ofSmooth hf hd)
  rw [PeriodicSobolev.eval_ofSmooth hf hs hd] at h
  have hb := PeriodicSobolev.norm_ofSmooth_le hf hs hd
  have hsqrt : √(2 * π * (1 + 2 * zetaReal (2 * s))) * (√(2 * π))⁻¹
      = √(1 + 2 * zetaReal (2 * s)) := by
    rw [Real.sqrt_mul (by positivity), mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne', one_mul]
  simp only [discreteSeries]
  rw [← Real.rpow_natCast]
  calc √(∫ x in (0 : ℝ)..2 * π,
          ‖f x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) f x‖ ^ 2)
      ≤ √(2 * π * (1 + 2 * zetaReal (2 * s))) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (-(s : ℝ))
          * ‖PeriodicSobolev.ofSmooth hf hd‖ := h
    _ ≤ √(2 * π * (1 + 2 * zetaReal (2 * s))) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (-(s : ℝ))
          * ((√(2 * π))⁻¹ * √(PeriodicSobolev.derivNormSq s f)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← hsqrt]; ring

/-- **Section 10.9** of [quarteroni2000numerical], the maximum-norm interpolation error estimate.
Let $s \ge 1$ be an integer, let $f : \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and of class
$C^s$, and let $N \ge 1$. Then for every $x \in \mathbb{R}$
$$|f(x) - \Pi^F_N f(x)| \le C N^{1/2 - s} \|f\|_s, \qquad C = \frac{2^{s+1}
  \sqrt{2\zeta(2s)}}{\sqrt{2\pi}},$$
with the norm $\|f\|_s$ of `QuarteroniSaccoSaleri.Chapter10.fourier_interp_error`.

The book states the bound for $\max_{0 \le x \le 2\pi} |f(x) - \Pi^F_N f(x)|$. The bound at
every $x$ is equivalent. The error is a trigonometric series, bounded by the sum of the moduli
of its coefficients. The $\ell^1$ aliasing bound over the window and the $\ell^1$ tail outside
it give the estimate (`PeriodicSobolev.norm_eval_sub_interp_le`). The extra factor $\sqrt N$
compared with the $L^2$ estimate comes from the Cauchy–Schwarz inequality over the $N$
frequencies of the window. -/
theorem fourier_interp_error_sup {s : ℕ} (hs : 1 ≤ s) {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * π)) (hd : ContDiff ℝ s f) {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ‖f x - discreteSeries N f x‖
      ≤ 2 * √(2 * zetaReal (2 * s)) * 2 ^ s / √(2 * π) * (N : ℝ) ^ (1 / 2 - (s : ℝ))
        * √(PeriodicSobolev.derivNormSq s f) := by
  have h := PeriodicSobolev.norm_eval_sub_interp_le
    (half_lt_of_one_le hs) hN (PeriodicSobolev.ofSmooth hf hd) x
  rw [PeriodicSobolev.eval_ofSmooth hf hs hd] at h
  have hb := PeriodicSobolev.norm_ofSmooth_le hf hs hd
  simp only [discreteSeries]
  rw [← Real.rpow_natCast]
  calc ‖f x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) f x‖
      ≤ 2 * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (1 / 2 - (s : ℝ))
          * ‖PeriodicSobolev.ofSmooth hf hd‖ := h
    _ ≤ 2 * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (1 / 2 - (s : ℝ))
          * ((√(2 * π))⁻¹ * √(PeriodicSobolev.derivNormSq s f)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- **Section 10.9** of [quarteroni2000numerical], the quadrature error estimate for the discrete
scalar product. Let $s \ge 1$ be an integer, let $f : \mathbb{R} \to \mathbb{C}$ be
$2\pi$-periodic and of class $C^s$, and let $N \ge 1$. Let $v_N \in S_N$, that is
$v_N(x) = \sum_{k=-N/2}^{N/2-1} c_k e^{ikx}$ for some coefficients $c_k \in \mathbb{C}$. Then
$$|(f, v_N) - (f, v_N)_N| \le C N^{-s} \|f\|_s \|v_N\|_{L^2(0, 2\pi)}, \qquad C =
  \sqrt{2\zeta(2s)}\, 2^s,$$
where $(f, g) = \int_0^{2\pi} f \bar g$, $(f, g)_N$ is the discrete scalar product (10.51), and
$\|f\|_s$ is the norm of `QuarteroniSaccoSaleri.Chapter10.fourier_interp_error`.

The book quotes the estimate from Canuto, Hussaini, Quarteroni and Zang (1988). The polynomial
$v_N$ is `DFT.windowTrigPoly N c`. The discrete orthogonality changes the difference into $2\pi
\sum_k (\hat f_k - \tilde f_k) \overline{c_k}$, and the $\ell^2$ aliasing bound and the
Cauchy–Schwarz inequality bound it
(`PeriodicSobolev.norm_intervalIntegral_sub_discreteInner_le`). -/
theorem fourier_discreteInner_error {s : ℕ} (hs : 1 ≤ s) {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * π)) (hd : ContDiff ℝ s f) {N : ℕ} (hN : 0 < N) (c : ℤ → ℂ) :
    ‖(∫ x in (0 : ℝ)..2 * π, f x * conj (DFT.windowTrigPoly N c x))
        - equation_10_51 N f (DFT.windowTrigPoly N c)‖
      ≤ √(2 * zetaReal (2 * s)) * 2 ^ s * (N : ℝ) ^ (-(s : ℝ))
        * √(PeriodicSobolev.derivNormSq s f)
        * √(∫ x in (0 : ℝ)..2 * π, ‖DFT.windowTrigPoly N c x‖ ^ 2) := by
  have h := PeriodicSobolev.norm_intervalIntegral_sub_discreteInner_le
    (half_lt_of_one_le hs) hN (PeriodicSobolev.ofSmooth hf hd) c
  rw [PeriodicSobolev.eval_ofSmooth hf hs hd] at h
  have hb := PeriodicSobolev.norm_ofSmooth_le hf hs hd
  have hpos : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  rw [equation_10_51, ← Real.rpow_natCast]
  calc ‖(∫ x in (0 : ℝ)..2 * π, f x * conj (DFT.windowTrigPoly N c x))
        - ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N,
            f (angleNode N j) * conj (DFT.windowTrigPoly N c (angleNode N j))‖
      ≤ √(2 * π) * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (-(s : ℝ))
          * ‖PeriodicSobolev.ofSmooth hf hd‖
          * √(∫ x in (0 : ℝ)..2 * π, ‖DFT.windowTrigPoly N c x‖ ^ 2) := h
    _ ≤ √(2 * π) * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ (s : ℝ) * (N : ℝ) ^ (-(s : ℝ))
          * ((√(2 * π))⁻¹ * √(PeriodicSobolev.derivNormSq s f))
          * √(∫ x in (0 : ℝ)..2 * π, ‖DFT.windowTrigPoly N c x‖ ^ 2) := by gcongr
    _ = _ := by field_simp

/-- **Section 10.9** of [quarteroni2000numerical], the quadrature error estimate for the composite
trapezoidal rule, in coefficient form. Let $s > 1/2$ be real, let $N \ge 1$, and let
$\phi \in H^s$ be a sequence of Fourier coefficients in the coefficient-form periodic Sobolev
space. Let $f(x) = \sum_m \phi_m e^{imx}$ be the $2\pi$-periodic function that $\phi$ defines.
Then
$$\Bigl|\int_0^{2\pi} f(x) \, dx - h \sum_{j=0}^{N-1} f(x_j)\Bigr| \le 2\pi \sqrt{2\zeta(2s)}\,
  N^{-s} \|\phi\|_{H^s}.$$

This is the estimate of `QuarteroniSaccoSaleri.Chapter10.fourier_discreteInner_error` at
$v_N = 1$. The space $H^s$ is `PeriodicSobolev s`, and $f$ is `PeriodicSobolev.eval (2 * π) φ`.
The proof specializes `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le`, whose
trapezoidal sum runs over the nodes $x_1, \dots, x_N$. By periodicity this sum equals the sum
over $x_0, \dots, x_{N-1}$. `QuarteroniSaccoSaleri.Chapter10.fourier_trapezoid_error` restates
the estimate in the norm $\|f\|_s$ of the book. -/
theorem fourier_trapezoid_error_sobolev {s : ℝ} (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ‖(∫ x in (0 : ℝ)..2 * π, PeriodicSobolev.eval (2 * π) φ x)
        - ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N, PeriodicSobolev.eval (2 * π) φ (angleNode N j)‖
      ≤ 2 * π * √(2 * zetaReal (2 * s)) * (N : ℝ) ^ (-s) * ‖φ‖ := by
  have h := PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le hs Real.two_pi_pos hN φ
  have hper := PeriodicSobolev.eval_periodic (s := s) Real.two_pi_pos.ne' φ
  -- the trapezoidal sum over `x_1, …, x_N` is the sum over `x_0, …, x_{N-1}` by periodicity
  have hsum : PeriodicSobolev.trapezoidSum (2 * π) N (PeriodicSobolev.eval (2 * π) φ)
      = ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N, PeriodicSobolev.eval (2 * π) φ (angleNode N j) := by
    rw [PeriodicSobolev.trapezoidSum]
    congr 1
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp only [angleNode]
      push_cast
      ring
    · rw [angleNode, Nat.cast_zero, mul_zero, zero_div, ← hper 0, zero_add]
      congr 1
      push_cast
      field_simp
  rw [hsum] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Section 10.9** of [quarteroni2000numerical], the composite trapezoidal error for a smooth
periodic integrand. Let $s \ge 1$ be an integer, let $f : \mathbb{R} \to \mathbb{C}$ be
$2\pi$-periodic and of class $C^s$, and let $N \ge 1$. Then the composite trapezoidal rule,
which is the discrete scalar product (10.51) at $v_N = 1$, satisfies
$$\Bigl|\int_0^{2\pi} f(x) \, dx - h \sum_{j=0}^{N-1} f(x_j)\Bigr| \le \sqrt{4\pi\zeta(2s)}\,
  N^{-s} \|f\|_s,$$
with the norm $\|f\|_s$ of `QuarteroniSaccoSaleri.Chapter10.fourier_interp_error`.

The book quotes the estimate from Canuto, Hussaini, Quarteroni and Zang (1988). The proof
applies `QuarteroniSaccoSaleri.Chapter10.fourier_trapezoid_error_sobolev` to the coefficient
sequence `PeriodicSobolev.ofSmooth` of $f$. This series sums to $f$
(`PeriodicSobolev.eval_ofSmooth`), and its norm is at most $(2\pi)^{-1/2} \|f\|_s$
(`PeriodicSobolev.norm_ofSmooth_le`). -/
theorem fourier_trapezoid_error {s : ℕ} (hs : 1 ≤ s) {f : ℝ → ℂ}
    (hf : Function.Periodic f (2 * π)) (hd : ContDiff ℝ s f) {N : ℕ} (hN : 0 < N) :
    ‖(∫ x in (0 : ℝ)..2 * π, f x) - ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N, f (angleNode N j)‖
      ≤ √(4 * π * zetaReal (2 * s)) * (N : ℝ) ^ (-(s : ℝ))
        * √(PeriodicSobolev.derivNormSq s f) := by
  have h := fourier_trapezoid_error_sobolev (half_lt_of_one_le hs) hN
    (PeriodicSobolev.ofSmooth hf hd)
  rw [PeriodicSobolev.eval_ofSmooth hf hs hd] at h
  refine h.trans ?_
  have hb := PeriodicSobolev.norm_ofSmooth_le hf hs hd
  have hsqrt : 2 * π * √(2 * zetaReal (2 * s)) * (√(2 * π))⁻¹
      = √(4 * π * zetaReal (2 * s)) := by
    have h2 : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    have hpos : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have h3 : 2 * π * (√(2 * π))⁻¹ = √(2 * π) := by
      rw [mul_inv_eq_iff_eq_mul₀ hpos.ne', h2]
    calc 2 * π * √(2 * zetaReal (2 * s)) * (√(2 * π))⁻¹
        = (2 * π * (√(2 * π))⁻¹) * √(2 * zetaReal (2 * s)) := by ring
      _ = √(2 * π) * √(2 * zetaReal (2 * s)) := by rw [h3]
      _ = √(4 * π * zetaReal (2 * s)) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          ring
  calc 2 * π * √(2 * zetaReal (2 * s)) * (N : ℝ) ^ (-(s : ℝ)) * ‖PeriodicSobolev.ofSmooth hf hd‖
      ≤ 2 * π * √(2 * zetaReal (2 * s)) * (N : ℝ) ^ (-(s : ℝ))
        * ((√(2 * π))⁻¹ * √(PeriodicSobolev.derivNormSq s f)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← hsqrt]; ring

/-! ### Equation (10.56): Lanczos smoothing -/

/-- **Equation (10.56)** of [quarteroni2000numerical]. For $N \in \mathbb{N}$ and
$k = 0, \dots, N - 1$, the **Lanczos smoothing factors** are
$$\sigma_k = \frac{\sin(2(k - N/2)\pi/N)}{2(k - N/2)\pi/N}, \qquad \sigma_{N/2} = 1.$$

The value $\sigma_{N/2} = 1$ removes the singularity. The factors act on the coefficients as
$\hat f_k \mapsto \sigma_k \hat f_k$ and reduce the coefficients of high order. -/
noncomputable def equation_10_56 (N k : ℕ) : ℝ :=
  if (k : ℤ) = (N / 2 : ℕ) then 1
  else Real.sin (2 * ((k : ℝ) - (N / 2 : ℕ)) * π / N) / (2 * ((k : ℝ) - (N / 2 : ℕ)) * π / N)

/-! ### Section 10.9.2: the fast Fourier transform -/

/-- **Section 10.9.2** of [quarteroni2000numerical], the recursive FFT identity (the Cooley–Tukey
step). Let $N = 2M$, $\omega = e^{2\pi i/N}$, and $y \in \mathbb{C}^N$. Let $\hat y = F_N^H y$
be the conjugate DFT, $\hat y_k = \sum_{j} \omega^{-jk} y_j$. Let $E = F_M^H (y_{2m})_m$ and
$O = F_M^H (y_{2m+1})_m$ be the transforms of order $M$ of the samples with even and odd index.
Then for $0 \le k < M$
$$\hat y_k = E_k + \omega^{-k} O_k, \qquad \hat y_{k+M} = E_k - \omega^{-k} O_k.$$

This is the identity $p(x) = p_e(x^2) + x p_o(x^2)$ of the book at the $N$-th roots of unity.
The matrix $F_N$ is `Matrix.dft N`, and the proof specializes `Matrix.dft_radix_two` and
`Matrix.dft_radix_two_add`. The transform $T$ of the book is $N^{-1}$ times this conjugate DFT
applied to the modulated samples $(-1)^j f(x_j)$ (`DFT.coeff_eq_dft_mulVec`, whose modulation
$\omega^{-mj}$ is $(-1)^j$ at $m = -N/2$). -/
theorem fft_radix_two {M : ℕ} (y : Fin (2 * M) → ℂ) (k : Fin M) :
    ((Matrix.dft (2 * M))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
        = ((Matrix.dft M)ᴴ *ᵥ fun m : Fin M => y ⟨2 * (m : ℕ), by omega⟩) k
          + (Complex.exp (2 * π * I / (2 * M)))⁻¹ ^ (k : ℕ)
            * ((Matrix.dft M)ᴴ *ᵥ fun m : Fin M => y ⟨2 * (m : ℕ) + 1, by omega⟩) k ∧
      ((Matrix.dft (2 * M))ᴴ *ᵥ y) ⟨(k : ℕ) + M, by omega⟩
        = ((Matrix.dft M)ᴴ *ᵥ fun m : Fin M => y ⟨2 * (m : ℕ), by omega⟩) k
          - (Complex.exp (2 * π * I / (2 * M)))⁻¹ ^ (k : ℕ)
            * ((Matrix.dft M)ᴴ *ᵥ fun m : Fin M => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  ⟨Matrix.dft_radix_two y k, Matrix.dft_radix_two_add y k⟩

end QuarteroniSaccoSaleri.Chapter10
