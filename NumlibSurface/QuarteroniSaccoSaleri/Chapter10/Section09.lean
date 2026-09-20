import Numlib.Analysis.Fourier.Aliasing
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.Sobolev.Periodic.Smooth

/-!
# Quarteroni–Sacco–Saleri §10.9: Fourier trigonometric polynomials

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.9.

The Fourier polynomials `φ_k(x) = e^{ikx}` on `(0, 2π)`, the Fourier series of `f ∈ L²(0, 2π)`
(10.48) with its coefficients in real form (10.49), the truncation of order `N` over the window
`-N/2 ≤ k ≤ N/2 − 1` (10.50) and its least-squares optimality, the discrete scalar product
(10.51), the discrete Fourier coefficients and the discrete Fourier series (10.52)–(10.53),
Lemma 10.1, the interpolation property with the DFT/IDFT pair and their matrices (10.55), the
discrete least-squares property of the interpolant, the Lanczos smoothing factors (10.56) and the
radix-2 step of the FFT (§10.9.2).

Complex-valued functions on `(0, 2π)` are functions on the circle `AddCircle (2π)`, `L²(0, 2π)`
is `Lp ℂ 2 haarAddCircle`, and the Fourier coefficients are Mathlib's `fourierCoeff`, whose
normalization `(1/2π) ∫_0^{2π}` is the book's (10.48). The discrete side is `DFT.coeff` and
`DFT.interp` of `Numlib/Analysis/Fourier/DFT` at the book's window offset `m = −N/2`, and the
matrices of (10.55) are built from `Matrix.dft`.

## Main definitions

* `trigTruncation N f` — the truncation of order `N`, `f_N^* = ∑_{k=-N/2}^{N/2-1} f̂_k e^{ikx}`.
* `equation_10_51 N f g` — the discrete scalar product `(f, g)_N`; `trigDiscreteNorm N f` is
  `‖f‖_N`.
* `equation_10_52 N f k` and `discreteSeries N f` — the discrete Fourier coefficients `f̃_k` and
  the discrete Fourier series `Π^F_N f`.
* `dftMatrix N`, `idftMatrix N` — the matrices `T` and `C` of the DFT and the IDFT.
* `equation_10_56 N k` — the Lanczos smoothing factors `σ_k`.

## Main results

* `equation_10_48`, `equation_10_48_hasSum` — the Fourier coefficients and the `L²` convergence
  of the Fourier series.
* `equation_10_49`, `equation_10_49_conj` — the coefficients in real form, and `f̂_{-k} = conj f̂_k`
  for real `f`.
* `trigTruncation_isBestApprox` — the least-squares optimality of the truncation.
* `equation_10_52_eq_discreteInner` — (10.52) as `f̃_k = (f, φ̃_k)_N / 2π`.
* `lemma_10_1` — the discrete orthogonality (10.54).
* `equation_10_55`, `equation_10_55_dft`, `equation_10_55_idft`, `equation_10_55_inv` — the
  interpolation property, the DFT and IDFT as matrix–vector products, and `C = T⁻¹`.
* `interp_isBestApprox_discrete` — the discrete least-squares property of `Π^F_N f`.
* `fourier_interp_error`, `fourier_interp_error_sup` — the two interpolation estimates
  `‖f − Π^F_N f‖_{L²} ≤ C N^{-s} ‖f‖_s` and `max |f − Π^F_N f| ≤ C N^{1/2−s} ‖f‖_s` for `f`
  `2π`-periodic of class `C^s`, `s ≥ 1`.
* `fourier_discreteInner_error`, `fourier_trapezoid_error` — the quadrature estimates
  `|(f, v_N) − (f, v_N)_N| ≤ C N^{-s} ‖f‖_s ‖v_N‖` for `v_N ∈ S_N` and, at `v_N = 1`, the
  composite trapezoidal error `|∫_0^{2π} f − h ∑_j f(x_j)| ≤ C N^{-s} ‖f‖_s`, in the book's norm
  `‖f‖_s = (∑_{k≤s} ‖f^{(k)}‖²_{L²})^{1/2}` (`PeriodicSobolev.derivNormSq`).
* `fourier_trapezoid_error_sobolev` — the trapezoidal estimate in coefficient form, on a
  periodic function with `H^s` coefficients.
* `fft_radix_two` — the Cooley–Tukey splitting of a transform of even order.

## Errata

* (10.50) and (10.52) write the coefficients as `(f, φ̃_k)/2π` and `(f, φ̃_k)_N/2π` with
  `φ̃_k = e^{-i(k − N/2)x}`. With the scalar product `(f, g) = ∫ f conj g` of the section this is
  `∫ f e^{+i(k − N/2)x}`, the wrong sign; the function in the scalar product is
  `φ̃_k = e^{i(k − N/2)x}`, and that is what `equation_10_52_eq_discreteInner` states.
* (10.55) and the matrix `C` carry the window shift on the wrong index: from the book's own
  derivation `Π^F_N f(x_j) = ∑_k f̃_k e^{ikjh} e^{-ijhN/2}`, the inverse transform is
  `f(x_j) = ∑_k f̃_k W_N^{-(k − N/2) j}`, so `C_{jk}` reads `W_N^{-(k − N/2) j}`; the printed
  `W_N^{-(j − N/2) k}` differs by the factor `(−1)^{j−k}`, and that `C` would not invert `T`.
  Program 89 implements the corrected formula.

## The estimates

The four estimates the book quotes from Canuto–Hussaini–Quarteroni–Zang without proof are proved
through the backbone: the bridge `PeriodicSobolev.ofSmooth` of
`Numlib/Analysis/Sobolev/Periodic/Smooth` puts the Fourier coefficients of a `C^s` periodic `f`
into the coefficient-form space `PeriodicSobolev s` with `‖φ‖ ≤ (2π)^{-1/2} ‖f‖_s`, and the
aliasing bounds of `Numlib/Analysis/Fourier/Aliasing` estimate `f̃_k − f̂_k = ∑_{m ≠ 0} f̂_{k+mN}`
in `ℓ²` and `ℓ¹` over the window. The constants are explicit (`√(1 + 2ζ(2s)) 2^s`,
`2^{s+1} √(2ζ(2s))/√(2π)`, `√(2ζ(2s)) 2^s`, `√(4π ζ(2s))`) but not sharp; the book leaves `C`
unspecified. The space `S_N` is the set of trigonometric polynomials `DFT.windowTrigPoly N c` over
the window `−N/2 ≤ k ≤ N/2 − 1`.

## Not formalized

The Gibbs phenomenon (§10.9.1) is described, not stated, and gets no node; the operation count of
the FFT is algorithmic.
-/

open AddCircle Complex Finset Matrix MeasureTheory Quadrature

open scoped Real ComplexConjugate

namespace QuarteroniSaccoSaleri.Chapter10

/-! ### (10.48)–(10.49): the Fourier series -/

/-- **(10.48), the Fourier coefficients.** For `f : (0, 2π) → ℂ`, read as a function on the
circle `AddCircle (2π)`, the Fourier coefficients are
`f̂_k = (1/2π) ∫_0^{2π} f(x) e^{-ikx} dx`; Mathlib's `fourierCoeff` at `T = 2π`, by
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

/-- **(10.48), the Fourier series.** For `f ∈ L²(0, 2π)`, the Fourier series `∑_k f̂_k φ_k`
converges to `f` in `L²`: Mathlib's `hasSum_fourier_series_L2`. -/
theorem equation_10_48_hasSum (f : Lp ℂ 2 (@haarAddCircle (2 * π) _)) :
    HasSum (fun k : ℤ => fourierCoeff f k • fourierLp 2 k) f :=
  hasSum_fourier_series_L2 f

/-- Integrability on the circle gives interval integrability of the lift on `[0, 2π]`. -/
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

/-- **(10.49).** Writing `f = α + iβ` with `α, β` real, the Fourier coefficients of an integrable
`f` are `f̂_k = a_k + i b_k` with

`a_k = (1/2π) ∫_0^{2π} (α cos kx + β sin kx) dx`, `b_k = (1/2π) ∫_0^{2π} (−α sin kx + β cos kx) dx`,

by expanding `e^{-ikx} = cos kx − i sin kx` in (10.48). -/
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

/-- **The remark after (10.49).** For a real-valued `f`, `f̂_{-k} = conj (f̂_k)`: conjugating the
integrand of (10.48) turns `e^{-ikx}` into `e^{ikx}` and leaves `f` alone. -/
theorem equation_10_49_conj {f : AddCircle (2 * π) → ℂ} (hf : ∀ x, (f x).im = 0) (k : ℤ) :
    fourierCoeff f (-k) = conj (fourierCoeff f k) := by
  simp only [fourierCoeff, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, fourier_neg, Complex.conj_eq_iff_im.mpr (hf x)]

/-! ### (10.50): the truncation of order `N` and its least-squares optimality -/

/-- **The truncation of order `N` (10.50)**: for even `N`,
`f_N^*(x) = ∑_{k=-N/2}^{N/2-1} f̂_k e^{ikx}`, the partial sum of the Fourier series over the window
`DFT.window N` of `N` frequencies starting at `−N/2`, as an element of `L²(0, 2π)`. -/
noncomputable def trigTruncation (N : ℕ) (f : Lp ℂ 2 (@haarAddCircle (2 * π) _)) :
    Lp ℂ 2 (@haarAddCircle (2 * π) _) :=
  ∑ k ∈ DFT.window N, fourierCoeff f k • fourierLp 2 k

/-- **The least-squares optimality of the truncation** (the unnumbered statement after (10.50)):
with `S_N = span {e^{ikx} : −N/2 ≤ k ≤ N/2 − 1}`, `‖f − f_N^*‖_{L²} = min_{g ∈ S_N} ‖f − g‖_{L²}`.
The truncation is the orthogonal projection of `f` onto `S_N`: `f − f_N^*` is orthogonal to every
`e^{ikx}` of the window by the orthonormality of the Fourier system (`orthonormal_fourier`,
`fourierBasis_repr`), and Pythagoras' theorem does the rest. -/
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

/-! ### (10.51)–(10.53): the discrete scalar product and the discrete Fourier series -/

/-- **(10.51), the discrete scalar product**: `(f, g)_N = h ∑_{j=0}^{N-1} f(x_j) conj (g(x_j))` with
`h = 2π/N` and the nodes `x_j = jh` (`Quadrature.angleNode N j`). -/
noncomputable def equation_10_51 (N : ℕ) (f g : ℝ → ℂ) : ℂ :=
  ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ range N, f (angleNode N j) * conj (g (angleNode N j))

/-- The discrete norm `‖f‖_N = (f, f)_N^{1/2}` attached to (10.51). -/
noncomputable def trigDiscreteNorm (N : ℕ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (equation_10_51 N f f).re

/-- **(10.52), the discrete Fourier coefficients**: for even `N`,
`f̃_k = (1/N) ∑_{j=0}^{N-1} f(x_j) W_N^{(k − N/2) j}`, `W_N = e^{-2πi/N}`, `k = 0, …, N − 1` — the
coefficients `DFT.coeff` of the backbone over the window starting at `m = −N/2`. -/
noncomputable def equation_10_52 (N : ℕ) (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  DFT.coeff N (-((N / 2 : ℕ) : ℤ)) f k

/-- **(10.53), the discrete Fourier series of order `N`**:
`Π^F_N f(x) = ∑_{k=0}^{N-1} f̃_k e^{i(k − N/2)x}`, the backbone's `DFT.interp` at the window offset
`−N/2`. -/
noncomputable def discreteSeries (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  DFT.interp N (-((N / 2 : ℕ) : ℤ)) f x

/-- **(10.52) as a discrete scalar product**: `f̃_k = (f, φ̃_k)_N / 2π` with
`φ̃_k(x) = e^{i(k − N/2)x}` — the book prints `φ̃_k = e^{-i(k − N/2)x}`, which with the scalar
product `(f, g)_N = h ∑ f conj g` of (10.51) would give the wrong sign in the exponent. -/
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

/-- **Lemma 10.1, (10.54).** For `0 ≤ l, j ≤ N − 1` the Fourier polynomials `φ_l = e^{ilx}` are
orthogonal for the discrete scalar product:
`(φ_l, φ_j)_N = h ∑_{k=0}^{N-1} e^{i(l−j)kh} = 2π δ_{jl}`.
The backbone's `DFT.sum_exp_sub_angleNode`, i.e. `Quadrature.sum_exp_angleNode` at `p = l − j`. -/
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

/-! ### (10.55): the interpolation property, the DFT and the IDFT -/

/-- **The interpolation property and (10.55).** `Π^F_N f(x_j) = f(x_j)` for `j = 0, …, N − 1`,
that is `f(x_j) = ∑_{k=0}^{N-1} f̃_k e^{i(k − N/2) x_j} = ∑_k f̃_k W_N^{-(k − N/2) j}` (with the
window shift on the coefficient index; see the module doc for the misprint). The backbone's
`DFT.interp_angleNode`. -/
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

/-- The principal `N`-th root of unity of the book, `W_N = exp(−2πi/N)`. -/
noncomputable def principalRoot (N : ℕ) : ℂ := Complex.exp (-(2 * π * I / N))

/-- **The matrix `T` of the DFT** (after (10.55)): `T_{kj} = (1/N) W_N^{(k − N/2) j}`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k j : Fin N =>
    (N : ℂ)⁻¹ * principalRoot N ^ ((((k : ℕ) : ℤ) - (N / 2 : ℕ)) * ((j : ℕ) : ℤ))

/-- **The matrix `C` of the IDFT** (after (10.55)), in the corrected form
`C_{jk} = W_N^{-(k − N/2) j}`; the book prints `W_N^{-(j − N/2) k}`. -/
noncomputable def idftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k : Fin N =>
    principalRoot N ^ (-(((((k : ℕ) : ℤ) - (N / 2 : ℕ)) * ((j : ℕ) : ℤ))))

/-- The powers of `W_N` are the modulations at the nodes: `W_N^{p j} = e^{-i p x_j}`. -/
theorem principalRoot_zpow_mul {N : ℕ} (hN : 0 < N) (p : ℤ) (j : ℕ) :
    principalRoot N ^ (p * (j : ℤ)) = Complex.exp (-((p : ℂ) * (angleNode N j : ℝ) * I)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [principalRoot, ← Complex.exp_int_mul]
  congr 1
  simp only [angleNode]
  push_cast
  field_simp

/-- **The DFT as a matrix–vector product**: `{f̃_k} = T {f(x_j)}`. -/
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

/-- **The IDFT as a matrix–vector product**: `{f(x_j)} = C {f̃_k}`, the interpolation property
(10.55) in matrix form. -/
theorem equation_10_55_idft {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) :
    (fun j : Fin N => f (angleNode N j))
      = idftMatrix N *ᵥ fun k : Fin N => equation_10_52 N f k := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum, (equation_10_55 hN f j.isLt).2, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [idftMatrix, Matrix.of_apply, principalRoot, mul_comm]

/-- **`C = T⁻¹`**: the matrices of the IDFT and the DFT are inverse to each other. Through the
backbone's `Matrix.dft`: `C = diag(ω^{-N j/2}) · F_N` and `T = N⁻¹ F_Nᴴ · diag(ω^{N j/2})` with
`ω = W_N⁻¹`, and `F_N F_Nᴴ = N I` (`Matrix.dft_mul_conjTranspose_dft`). -/
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

/-- **The discrete least-squares property of `Π^F_N f`** (the unnumbered statement after (10.55)):
`‖f − Π^F_N f‖_N ≤ ‖f − g‖_N` for every `g` — in particular for every `g ∈ S_N` — because the
interpolant has discrete error `0`: `f − Π^F_N f` vanishes at every node. -/
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

/-- **The `L²` interpolation estimate of §10.9.** For `f` `2π`-periodic of class `C^s`, `s ≥ 1`,

`‖f − Π^F_N f‖_{L²(0,2π)} ≤ C N^{-s} ‖f‖_s`, `‖f‖_s = (∑_{k≤s} ‖f^{(k)}‖²_{L²(0,2π)})^{1/2}`,

with `C = √(1 + 2ζ(2s)) 2^s`. The coefficient sequence `φ = PeriodicSobolev.ofSmooth` of `f`
lies in `H^s` with `‖φ‖ ≤ (2π)^{-1/2} ‖f‖_s`, its series sums to `f`, and the backbone's
`PeriodicSobolev.sqrt_intervalIntegral_norm_eval_sub_interp_sq_le` bounds the error of the
discrete Fourier series by the aliasing and truncation tails. Quoted by the book from
[CHQZ88], chapter 2. -/
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

/-- **The sup-norm interpolation estimate of §10.9.** For `f` `2π`-periodic of class `C^s`,
`s ≥ 1`, `max_{0 ≤ x ≤ 2π} |f(x) − Π^F_N f(x)| ≤ C N^{1/2−s} ‖f‖_s` with
`C = 2^{s+1} √(2ζ(2s)) / √(2π)`: the error is a trigonometric series bounded by the sum of the
moduli of its coefficients, the `ℓ¹` aliasing bound over the window and the `ℓ¹` tail outside it
(`PeriodicSobolev.norm_eval_sub_interp_le`), whose extra `√N` over the `L²` estimate is the
Cauchy–Schwarz inequality over the `N` frequencies of the window. Stated at every `x`, which
covers the maximum over `[0, 2π]`. -/
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

/-- **The discrete scalar product estimate of §10.9.** For `f` `2π`-periodic of class `C^s`,
`s ≥ 1`, and every `v_N ∈ S_N` — every trigonometric polynomial
`v_N = ∑_{k=-N/2}^{N/2-1} c_k e^{ikx}`, that is `DFT.windowTrigPoly N c` —

`|(f, v_N) − (f, v_N)_N| ≤ C N^{-s} ‖f‖_s ‖v_N‖_{L²(0,2π)}`,

with `(f, g) = ∫_0^{2π} f conj g`, the discrete scalar product (10.51) and `C = √(2ζ(2s)) 2^s`.
Expanding `v_N`, the discrete orthogonality turns the difference into
`2π ∑_k (f̂_k − f̃_k) conj c_k`, which the `ℓ²` aliasing bound and Cauchy–Schwarz control
(`PeriodicSobolev.norm_intervalIntegral_sub_discreteInner_le`). Quoted by the book from
[CHQZ88]. -/
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

/-- **The quadrature estimate of §10.9 in coefficient form**, at `v_N = 1`, the composite
trapezoidal rule: for a `2π`-periodic `f = eval (2π) φ` given by Fourier coefficients
`φ ∈ H^s`, `s > 1/2` (the coefficient-form Sobolev space `PeriodicSobolev s` of
`Numlib/Analysis/Sobolev/Periodic`), `|∫_0^{2π} f − h ∑_{j<N} f(x_j)| ≤ C N^{-s} ‖φ‖_{H^s}` with
`C = 2π √(2 ζ(2s))`. The backbone's `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le`,
whose trapezoidal sum runs over the nodes `x_1, …, x_N`, which by periodicity is the book's sum
over `x_0, …, x_{N-1}`. `fourier_trapezoid_error` restates it in the book's norm
`‖f‖_s = (∑_{k≤s} ‖f^{(k)}‖²)^{1/2}` through `PeriodicSobolev.ofSmooth`. -/
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

/-- **The quadrature estimate of §10.9 at `v_N = 1`, in the book's norm**: for a `2π`-periodic `f`
of class `C^s`, `s ≥ 1`, the composite trapezoidal rule (10.51) satisfies

`|∫_0^{2π} f − h ∑_{j<N} f(x_j)| ≤ C N^{-s} ‖f‖_s`, `‖f‖_s = (∑_{k≤s} ‖f^{(k)}‖²_{L²(0,2π)})^{1/2}`,

with `C = √(4π ζ(2s))`. The coefficient-form estimate `fourier_trapezoid_error_sobolev` applied
to the coefficient sequence `PeriodicSobolev.ofSmooth` of `f`, whose series sums to `f`
(`PeriodicSobolev.eval_ofSmooth`) and whose norm is at most `(2π)^{-1/2} ‖f‖_s`
(`PeriodicSobolev.norm_ofSmooth_le`). The book quotes the estimate from [CHQZ88]. -/
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

/-! ### (10.56): Lanczos smoothing -/

/-- **(10.56), the Lanczos smoothing factors** `σ_k = sin(2(k − N/2)π/N) / (2(k − N/2)π/N)`,
`k = 0, …, N − 1`, with `σ_{N/2} = 1` at the removable singularity; they are applied as
`f̂_k ↦ σ_k f̂_k` to attenuate the higher-order coefficients. -/
noncomputable def equation_10_56 (N k : ℕ) : ℝ :=
  if (k : ℤ) = (N / 2 : ℕ) then 1
  else Real.sin (2 * ((k : ℝ) - (N / 2 : ℕ)) * π / N) / (2 * ((k : ℝ) - (N / 2 : ℕ)) * π / N)

/-! ### §10.9.2: the fast Fourier transform -/

/-- **The Cooley–Tukey step (§10.9.2).** A conjugate DFT `ŷ = F_{2M}ᴴ y` of even order `N = 2M`
is assembled from the two transforms `E`, `O` of order `M` of the even- and odd-indexed samples:
`ŷ_k = E_k + ω^{-k} O_k` and `ŷ_{k+M} = E_k − ω^{-k} O_k` for `k < M`, `ω = e^{2πi/N}` — the
book's `p(x) = p_e(x²) + x p_o(x²)` evaluated at the roots of unity of order `N`. The backbone's
`Matrix.dft_radix_two` and `Matrix.dft_radix_two_add`; the book's transform `T` is `N⁻¹` times this
conjugate DFT applied to the modulated samples `(−1)^j f(x_j)` (`DFT.coeff_eq_dft_mulVec`, whose
modulation `ω^{-mj}` is `(−1)^j` at `m = −N/2`). -/
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
