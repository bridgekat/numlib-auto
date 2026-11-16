/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.RootsOfUnity.Complex
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Operator.Compact

/-!
# Periodic Sobolev spaces

For a real number $s$, the periodic Sobolev space $H^s$ (`PeriodicSobolev s`) is a space of formal
Fourier series $\sum_{m \in \mathbb{Z}} a_m e^{2 \pi i m x / T}$, graded by the decay of the
coefficients. With the weight $w_s(0) = 1$ and $w_s(m) = |m|^s$ for $m \ne 0$, the coefficients
$a_m$ of an element $\varphi \in H^s$ satisfy
$$\|\varphi\|^2 = \sum_{m \in \mathbb{Z}} w_s(m)^2 |a_m|^2 = |a_0|^2 + \sum_{m \neq 0} |m|^{2s}
  |a_m|^2 < \infty.$$
No domain, boundary or weak derivative enters the definition: $H^s$ is a weighted
$\ell^2(\mathbb{Z}, \mathbb{C})$. For $s > 1/2$ the coefficients are absolutely summable, so the
series converges uniformly. Its sum `PeriodicSobolev.eval T φ` is a continuous function of period
$T$ on the line, for any period $T$; the period is a parameter of the passage to functions, not of
the space. Below, $\zeta(r) = \sum_{n \ge 1} n^{-r}$ is the Riemann zeta function at a real $r > 1$.

The module expresses the norm and the inner product of $H^s$ through the coefficients and proves,
for $s > 1/2$, the embedding into the continuous functions, $\sup_x |\varphi(x)| \le (1 + \sqrt{2
\zeta(2s)}) \|\varphi\|$. The inclusion $H^s \to H^t$ for $t \le s$ has dense range, and it is
compact for $t < s$. The trapezoidal rule $T_k$ with $k$ points is spectrally accurate on these
series: $|\int_0^T \varphi - T_k(\varphi)| \le T k^{-s} \sqrt{2 \zeta(2s)} \|\varphi\|$. The module
also proves Parseval's identity for the sum of the series, the density of the trigonometric
polynomials in $H^s$ for every $s$, and the duality pairing between $H^t$ and $H^{-t}$. The periodic
Sobolev spaces and these results are in [han2009theoretical], §7.5, for the period $2\pi$.

## Main definitions

* `zetaReal`: the value $\zeta(r) = \sum_{n \ge 1} n^{-r}$ of the Riemann zeta function at a real
  $r > 1$, equal to `riemannZeta` by `ofReal_zetaReal`.
* `periodicSobolevWeight`: the weight $w_s(m)$, equal to $1$ at $m = 0$ and to $|m|^s$ elsewhere.
* `PeriodicSobolev`: the space $H^s$, with the coefficients `PeriodicSobolev.coeff`.
* `PeriodicSobolev.inclL`: the inclusion $H^s \to H^t$ for $t \le s$.
* `PeriodicSobolev.truncL`: the truncation $H^s \to H^t$ to a finite set of frequencies.
* `periodicChar`: the character $x \mapsto e^{2 \pi i m x / T}$.
* `PeriodicSobolev.eval`: the sum of the series as a function on the line.
* `PeriodicSobolev.trapezoidSum`: the trapezoidal rule $T_k(f) = (T / k) \sum_{j=1}^{k} f(jT/k)$ for
  a function of period $T$.
* `PeriodicSobolev.dualPairing`: the bounded linear functional on $H^t$ given by an element of
  $H^{-t}$.

## Main results

* `PeriodicSobolev.hasSum_norm_sq` and `PeriodicSobolev.inner_eq_tsum`: the norm and the inner
  product through the coefficients.
* `PeriodicSobolev.tsum_norm_coeff_le`: for $s > 1/2$, $\sum_m |a_m| \le |a_0| + \sqrt{2 \zeta(2s)}
  \|\varphi\|$; this is the Sobolev embedding into the continuous functions in coefficient form.
* `PeriodicSobolev.tsum_norm_coeff_mul_le`: for $s > 1/2$, $\sum_{j \ne 0} |a_{jk}| \le k^{-s}
  \sqrt{2 \zeta(2s)} \|\varphi\|$, the same Cauchy–Schwarz bound along the multiples of $k$.
* `PeriodicSobolev.norm_eval_le`, `PeriodicSobolev.continuous_eval` and
  `PeriodicSobolev.eval_periodic`: for $s > 1/2$, the sum of the series is a continuous function of
  period $T$ with $\sup_x |\varphi(x)| \le (1 + \sqrt{2 \zeta(2s)}) \|\varphi\|$.
* `PeriodicSobolev.denseRange_inclL` and `PeriodicSobolev.isCompactOperator_inclL`: the inclusion
  $H^s \to H^t$ has dense range, and it is compact when $t < s$.
* `sum_periodicChar`: the trapezoidal sum of $e^{2 \pi i m x / T}$ over $k$ equally spaced points of
  a period is $k$ if $k \mid m$ and $0$ otherwise.
* `PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le`: for $s > 1/2$, $|\int_0^T \varphi -
  T_k(\varphi)| \le T k^{-s} \sqrt{2 \zeta(2s)} \|\varphi\|$.
* `fourierCoeff_tsum_smul_fourier` and `intervalIntegral_norm_tsum_smul_fourier_sq`: an absolutely
  convergent trigonometric series on `AddCircle T` has the Fourier coefficients that it was built
  from, and it satisfies Parseval's identity.
* `PeriodicSobolev.fourierCoeff_lift_eval` and `PeriodicSobolev.intervalIntegral_norm_eval_sq`: for
  $s > 1/2$, the Fourier coefficients of the sum of the series are the $a_m$, and
  $\int_0^T |\varphi|^2 = T \sum_m |a_m|^2$.
* `PeriodicSobolev.dense_span_basisElt`: the trigonometric polynomials are dense in $H^s$ for every
  $s$.
* `PeriodicSobolev.norm_tsum_coeff_mul_conj_le`: $|\sum_m a_m \overline{b_m}| \le \|\varphi\|_{H^t}
  \|\eta\|_{H^{-t}}$.

## Proof outline

The embedding and the quadrature bound are the Cauchy–Schwarz inequality against
$\sum_{m \ne 0} |m|^{-2s} = 2 \zeta(2s)$, which converges because $2s > 1$. For the quadrature
bound, the trapezoidal sum of $e^{2 \pi i m x / T}$ vanishes unless $k \mid m$, so the quadrature
error is $-T$ times the tail $\sum_{j \ne 0} a_{jk}$ of the coefficients along the multiples of $k$.
The inclusion $H^s \to H^t$ is compact for $t < s$ because it is the limit in operator norm of its
truncations to the frequencies in $[-n, n]$, at the rate $(n + 1)^{t - s}$.

## Implementation notes

* `PeriodicSobolev s` is `lp (fun _ : ℤ => ℂ) 2`. An element $u$ stands for the series with the
  coefficients $a_m = u_m / w_s(m)$. So the Hilbert space structure, the completeness and Parseval's
  identity come from `lp` unchanged, and the grading is entirely in `PeriodicSobolev.coeff`.
* For $s < 0$ the elements are not functions, because the series need not converge in any usual
  sense. Therefore the space is a sequence space and not a subtype of an $L^2$ space.
* The coefficients here are those of the system $e^{2 \pi i m x / T}$. The book [han2009theoretical]
  uses the period $2\pi$ and the orthonormal system $\psi_m(x) = (2\pi)^{-1/2} e^{imx}$, so its
  coefficients are $\sqrt{2\pi}$ times the coefficients here, and its norm of a series is
  $\sqrt{2\pi}$ times the norm here. The definition of the space does not depend on this constant,
  but the identification with the coefficients of the book does; it is made in the surface library
  for [han2009theoretical].
* Mathlib's inner product is conjugate-linear in its first argument.
-/

open Filter Metric Set Topology
open scoped ComplexConjugate ENNReal InnerProductSpace Real

/-! ### The Riemann zeta function on the real axis -/

/-- For a real number $r$, `zetaReal r` is
$$\zeta(r) = \sum_{n \in \mathbb{N}} (n^r)^{-1},$$
the Riemann zeta function at a real argument. For $r \ne 0$ the term at $n = 0$ is
$(0^r)^{-1} = 0$, so the sum is the sum over $n \ge 1$. For $r > 1$ the value agrees with
`riemannZeta` (`ofReal_zetaReal`). For $r \le 1$ the series diverges, and the value is $0$. -/
noncomputable def zetaReal (r : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) ^ r)⁻¹

/-- For a real number $r > 1$, the series $\sum_{n \in \mathbb{N}} (n^r)^{-1}$ converges. -/
theorem summable_inv_nat_rpow {r : ℝ} (hr : 1 < r) : Summable fun n : ℕ => ((n : ℝ) ^ r)⁻¹ :=
  Real.summable_nat_rpow_inv.2 hr

/-- For every real $r$, $\zeta(r) \ge 0$. -/
theorem zetaReal_nonneg (r : ℝ) : 0 ≤ zetaReal r :=
  tsum_nonneg fun _ => by positivity

/-- For a real number $r > 1$, `zetaReal r` equals the value `riemannZeta r` of the Riemann zeta
function, as a complex number. -/
theorem ofReal_zetaReal {r : ℝ} (hr : 1 < r) : (zetaReal r : ℂ) = riemannZeta (r : ℂ) := by
  have hre : 1 < (r : ℂ).re := by simpa using hr
  rw [zeta_eq_tsum_one_div_nat_cpow hre, zetaReal, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, one_div]

/-- For a real number $r > 1$,
$$\sum_{m \in \mathbb{Z}} (|m|^r)^{-1} = 2 \zeta(r).$$
The term at $m = 0$ is $(0^r)^{-1} = 0$, so the sum is the sum over $m \ne 0$. -/
theorem hasSum_int_inv_abs_rpow {r : ℝ} (hr : 1 < r) :
    HasSum (fun m : ℤ => (|(m : ℝ)| ^ r)⁻¹) (2 * zetaReal r) := by
  have hr0 : r ≠ 0 := by linarith
  have hz : HasSum (fun n : ℕ => ((n : ℝ) ^ r)⁻¹) (zetaReal r) := (summable_inv_nat_rpow hr).hasSum
  set f : ℤ → ℝ := fun m => (|(m : ℝ)| ^ r)⁻¹ with hf
  have h₁ : HasSum (fun n : ℕ => f n) (zetaReal r) := hz.congr_fun fun n => by simp [hf]
  have h₂ : HasSum (fun n : ℕ => f (-n)) (zetaReal r) := hz.congr_fun fun n => by simp [hf]
  have hf0 : f 0 = 0 := by simp [hf, Real.zero_rpow hr0]
  have h := h₁.of_nat_of_neg h₂
  rw [hf0, sub_zero, ← two_mul] at h
  exact h

/-! ### Norms in $\ell^2$ -/

namespace lp

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

/-- **Parseval's identity in $\ell^2$.** For $f \in \ell^2(\iota, E)$,
$$\sum_{i} \|f_i\|^2 = \|f\|^2.$$
-/
theorem hasSum_norm_sq (f : lp E 2) : HasSum (fun i => ‖f i‖ ^ 2) (‖f‖ ^ 2) := by
  have := lp.hasSum_norm (E := E) (p := 2) (by norm_num) f
  simpa using this

/-- For $f \in \ell^2(\iota, E)$, the norm is $\|f\| = \big( \sum_i \|f_i\|^2 \big)^{1/2}$. -/
theorem norm_eq_sqrt_tsum_norm_sq (f : lp E 2) : ‖f‖ = √(∑' i, ‖f i‖ ^ 2) := by
  rw [(hasSum_norm_sq f).tsum_eq, Real.sqrt_sq (norm_nonneg f)]

end lp

/-! ### The weight -/

/-- The **weight** of the periodic Sobolev norm of order $s \in \mathbb{R}$, for $m \in \mathbb{Z}$:
$$w_s(m) = \begin{cases} 1, & m = 0, \\ |m|^s, & m \ne 0. \end{cases}$$

The value $1$ at $m = 0$ makes the weight positive for every $s$, and hence makes the norm of
$H^s$ a norm. Every other index carries the factor $|m|^s$ that grades the scale. -/
noncomputable def periodicSobolevWeight (s : ℝ) (m : ℤ) : ℝ :=
  if m = 0 then 1 else |(m : ℝ)| ^ s

/-- The weight at $m = 0$ is $w_s(0) = 1$. -/
@[simp]
theorem periodicSobolevWeight_zero (s : ℝ) : periodicSobolevWeight s 0 = 1 := ite_eq_left rfl

/-- For $m \ne 0$, the weight is $w_s(m) = |m|^s$. -/
theorem periodicSobolevWeight_of_ne_zero {m : ℤ} (s : ℝ) (hm : m ≠ 0) :
    periodicSobolevWeight s m = |(m : ℝ)| ^ s := ite_eq_right hm

/-- The weight is positive: $w_s(m) > 0$ for all $s$ and $m$. -/
theorem periodicSobolevWeight_pos (s : ℝ) (m : ℤ) : 0 < periodicSobolevWeight s m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero s hm]
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 hm)) s

/-- The weight is nonzero: $w_s(m) \ne 0$ for all $s$ and $m$. -/
theorem periodicSobolevWeight_ne_zero (s : ℝ) (m : ℤ) : periodicSobolevWeight s m ≠ 0 :=
  (periodicSobolevWeight_pos s m).ne'

/-- The weight of order $0$ is $w_0(m) = 1$ for every $m$. -/
@[simp]
theorem periodicSobolevWeight_zero_exponent (m : ℤ) : periodicSobolevWeight 0 m = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero 0 hm, Real.rpow_zero]

/-- The weight is monotone in the order: if $t \le s$, then $w_t(m) \le w_s(m)$ for every
$m \in \mathbb{Z}$. This gives the inclusion $H^s \subseteq H^t$. -/
theorem periodicSobolevWeight_le {s t : ℝ} (h : t ≤ s) (m : ℤ) :
    periodicSobolevWeight t m ≤ periodicSobolevWeight s m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero t hm, periodicSobolevWeight_of_ne_zero s hm]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hm) h

/-! ### The space -/

/-- The **periodic Sobolev space** $H^s$ of order $s \in \mathbb{R}$: the space of formal Fourier
series $\sum_m a_m e_m$ with
$$|a_0|^2 + \sum_{m \neq 0} |m|^{2s} |a_m|^2 < \infty.$$
It is a complex inner product space with
$$\langle \varphi, \rho \rangle = \overline{a_0} \, b_0 + \sum_{m \neq 0} |m|^{2s} \,
  \overline{a_m} \, b_m,$$
where $a_m$ and $b_m$ are the coefficients of $\varphi$ and $\rho$.

The type is `lp (fun _ : ℤ => ℂ) 2`. An element $u$ stands for the series with the coefficients
$a_m = u_m / w_s(m)$, where $w_s$ is `periodicSobolevWeight`. Then the norm of $u$ in $\ell^2$
is the weighted norm above, and the Hilbert space structure is the one of $\ell^2$.
`PeriodicSobolev.coeff` reads the coefficients, and `PeriodicSobolev.ofCoeff` builds an element
from its coefficients. For $s < 0$ an element is only a formal series: its coefficients can
grow, and it is not a function. For this reason the space is a sequence space and not a subtype
of an $L^2$ space. -/
def PeriodicSobolev (_s : ℝ) : Type := lp (fun _ : ℤ => ℂ) 2

namespace PeriodicSobolev

variable {s t : ℝ}

noncomputable instance : NormedAddCommGroup (PeriodicSobolev s) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℤ => ℂ) 2))

noncomputable instance : InnerProductSpace ℂ (PeriodicSobolev s) :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun _ : ℤ => ℂ) 2))

instance : CompleteSpace (PeriodicSobolev s) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℤ => ℂ) 2))

/-- The **weighted coefficient sequence** of $\varphi \in H^s$, as an element of
$\ell^2(\mathbb{Z}, \mathbb{C})$: its $m$-th entry is $w_s(m) a_m$. It is a linear isometric
equivalence.

On the underlying data this map is the identity. It keeps the two readings of the same sequence
apart, and it carries the lemmas about `lp` to $H^s$. -/
noncomputable def toLp (s : ℝ) : PeriodicSobolev s ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearIsometryEquiv.refl ℂ (lp (fun _ : ℤ => ℂ) 2)

/-- The weighted coefficient sequence of $\varphi$ has the norm $\|\varphi\|$. -/
@[simp]
theorem norm_toLp (φ : PeriodicSobolev s) : ‖toLp s φ‖ = ‖φ‖ := (toLp s).norm_map φ

/-- The $m$-th **Fourier coefficient** $a_m$ of $\varphi \in H^s$. -/
noncomputable def coeff (φ : PeriodicSobolev s) (m : ℤ) : ℂ :=
  (periodicSobolevWeight s m : ℂ)⁻¹ * toLp s φ m

/-- The $m$-th entry of the weighted coefficient sequence of $\varphi$ is $w_s(m) a_m$. -/
theorem toLp_apply (φ : PeriodicSobolev s) (m : ℤ) :
    toLp s φ m = periodicSobolevWeight s m * coeff φ m := by
  rw [coeff, ← mul_assoc, mul_inv_cancel₀ (by
    exact_mod_cast periodicSobolevWeight_ne_zero s m), one_mul]

/-- The $m$-th entry of the weighted coefficient sequence of $\varphi$ has the norm $w_s(m) |a_m|$.
-/
theorem norm_toLp_apply (φ : PeriodicSobolev s) (m : ℤ) :
    ‖toLp s φ m‖ = periodicSobolevWeight s m * ‖coeff φ m‖ := by
  rw [toLp_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (periodicSobolevWeight_pos s m).le]

/-- An element of $H^s$ is determined by its coefficients. -/
theorem coeff_injective : Function.Injective (coeff (s := s)) := by
  intro φ ρ h
  refine (toLp s).injective (lp.ext (funext fun m => ?_))
  rw [toLp_apply, toLp_apply, h]

/-- The coefficients of $0 \in H^s$ are all $0$. -/
@[simp]
theorem coeff_zero (s : ℝ) : coeff (0 : PeriodicSobolev s) = 0 := by
  funext m; simp [coeff]

/-- The coefficients of $\varphi + \rho$ are the sums of the coefficients of $\varphi$ and $\rho$.
-/
@[simp]
theorem coeff_add (φ ρ : PeriodicSobolev s) : coeff (φ + ρ) = coeff φ + coeff ρ := by
  funext m; simp [coeff, mul_add]

/-- The coefficients of $c \varphi$, for $c \in \mathbb{C}$, are $c$ times the coefficients of
$\varphi$. -/
@[simp]
theorem coeff_smul (c : ℂ) (φ : PeriodicSobolev s) : coeff (c • φ) = c • coeff φ := by
  funext m; simp [coeff]; ring

/-- The coefficients of $\varphi - \rho$ are the differences of the coefficients of $\varphi$ and
$\rho$. -/
@[simp]
theorem coeff_sub (φ ρ : PeriodicSobolev s) : coeff (φ - ρ) = coeff φ - coeff ρ := by
  funext m; simp [coeff, mul_sub]

/-- **Parseval's identity for the periodic Sobolev norm.** For $\varphi \in H^s$ with coefficients
$a_m$,
$$\sum_{m \in \mathbb{Z}} \big( w_s(m) |a_m| \big)^2 = \|\varphi\|^2,$$
where $w_s(0) = 1$ and $w_s(m) = |m|^s$ for $m \ne 0$. This is the defining property of the
space. -/
theorem hasSum_norm_sq (φ : PeriodicSobolev s) :
    HasSum (fun m : ℤ => (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) (‖φ‖ ^ 2) := by
  have h := lp.hasSum_norm_sq (toLp s φ)
  simpa only [norm_toLp_apply, norm_toLp] using h

/-- For $\varphi \in H^s$, $\|\varphi\|^2 = \sum_{m \in \mathbb{Z}} \big( w_s(m) |a_m| \big)^2$. -/
theorem norm_sq_eq_tsum (φ : PeriodicSobolev s) :
    ‖φ‖ ^ 2 = ∑' m : ℤ, (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 :=
  (hasSum_norm_sq φ).tsum_eq.symm

/-- Every coefficient is bounded by the norm: for $\varphi \in H^s$ and $m \in \mathbb{Z}$,
$w_s(m) |a_m| \le \|\varphi\|$. -/
theorem weight_mul_norm_coeff_le (φ : PeriodicSobolev s) (m : ℤ) :
    periodicSobolevWeight s m * ‖coeff φ m‖ ≤ ‖φ‖ := by
  rw [← norm_toLp_apply, ← norm_toLp φ]
  exact lp.norm_apply_le_norm (by norm_num) (toLp s φ) m

/-- For $\varphi, \rho \in H^s$ with coefficients $a_m$ and $b_m$,
$$\langle \varphi, \rho \rangle = \sum_{m \in \mathbb{Z}} w_s(m)^2 \, \overline{a_m} \, b_m.$$

Mathlib's inner product is conjugate-linear in its first argument. This is the opposite of the
convention that is usual in the numerical analysis literature. -/
theorem inner_eq_tsum (φ ρ : PeriodicSobolev s) :
    (inner ℂ φ ρ : ℂ) =
      ∑' m : ℤ, (periodicSobolevWeight s m : ℂ) ^ 2 * (conj (coeff φ m) * coeff ρ m) := by
  rw [← (toLp s).inner_map_map φ ρ, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [RCLike.inner_apply, toLp_apply, toLp_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The element of $H^s$ with the prescribed coefficients $a : \mathbb{Z} \to \mathbb{C}$, given
that $(w_s(m) a_m)_m$ lies in $\ell^2$. -/
noncomputable def ofCoeff (s : ℝ) (a : ℤ → ℂ)
    (ha : Memℓp (fun m => (periodicSobolevWeight s m : ℂ) * a m) 2) : PeriodicSobolev s :=
  (toLp s).symm ⟨_, ha⟩

/-- The coefficients of the element of $H^s$ with prescribed coefficients $a$ are $a$. -/
@[simp]
theorem coeff_ofCoeff (s : ℝ) (a : ℤ → ℂ)
    (ha : Memℓp (fun m => (periodicSobolevWeight s m : ℂ) * a m) 2) :
    coeff (ofCoeff s a ha) = a := by
  funext m
  rw [coeff, ofCoeff, LinearIsometryEquiv.apply_symm_apply]
  change (periodicSobolevWeight s m : ℂ)⁻¹ * ((periodicSobolevWeight s m : ℂ) * a m) = a m
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast periodicSobolevWeight_ne_zero s m), one_mul]

end PeriodicSobolev

/-! ### Cauchy–Schwarz against the weights -/

/-- For $m \ne 0$, $w_s(m)^2 = |m|^{2s}$. -/
theorem periodicSobolevWeight_sq (s : ℝ) {m : ℤ} (hm : m ≠ 0) :
    periodicSobolevWeight s m ^ 2 = |(m : ℝ)| ^ (2 * s) := by
  rw [periodicSobolevWeight_of_ne_zero s hm, ← Real.rpow_natCast (|(m : ℝ)| ^ s) 2,
    ← Real.rpow_mul (abs_nonneg _)]
  norm_num [mul_comm]

/-- A family $f$ lies in $\ell^2$ if and only if $\sum_i \|f_i\|^2$ converges.

`Memℓp` is stated with the real exponent `p.toReal`. Every use of it at $p = 2$ goes through
this lemma, which writes the square as a natural power. -/
theorem memℓp_two_iff {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {f : ∀ i, E i} :
    Memℓp f 2 ↔ Summable fun i => ‖f i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_congr fun i => ?_
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

namespace PeriodicSobolev

variable {s t : ℝ}

/-- The sequence $j \mapsto w_s(jk)^{-1}$ for $j \ne 0$, with the value $0$ at $j = 0$; for
$s > 1/2$ it lies in $\ell^2$ with norm $k^{-s} \sqrt{2 \zeta(2s)}$, and its pairing with the
coefficients along the multiples of $k$ gives both the embedding ($k = 1$) and the quadrature
bound. -/
private noncomputable def invWeightSeq (s : ℝ) (k : ℕ) (j : ℤ) : ℂ :=
  if j = 0 then 0 else ((periodicSobolevWeight s (j * k) : ℂ))⁻¹

private theorem norm_invWeightSeq_sq (s : ℝ) (hs : 0 < s) {k : ℕ} (hk : 0 < k) (j : ℤ) :
    ‖invWeightSeq s k j‖ ^ 2 = ((k : ℝ) ^ (2 * s))⁻¹ * (|(j : ℝ)| ^ (2 * s))⁻¹ := by
  have h2s : (2 : ℝ) * s ≠ 0 := by positivity
  rcases eq_or_ne j 0 with rfl | hj
  · rw [invWeightSeq, ite_eq_left rfl]
    simp [Real.zero_rpow h2s]
  · have hjk : j * (k : ℤ) ≠ 0 := mul_ne_zero hj (by exact_mod_cast hk.ne')
    have habs : |((j * (k : ℤ) : ℤ) : ℝ)| = |(j : ℝ)| * (k : ℝ) := by
      push_cast
      rw [abs_mul, Nat.abs_cast]
    rw [invWeightSeq, ite_eq_right hj, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s _).le, inv_pow,
      periodicSobolevWeight_sq s hjk, habs,
      Real.mul_rpow (abs_nonneg _) (Nat.cast_nonneg k), mul_inv, mul_comm]

private theorem hasSum_norm_invWeightSeq_sq (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    HasSum (fun j : ℤ => ‖invWeightSeq s k j‖ ^ 2)
      (((k : ℝ) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))) :=
  ((hasSum_int_inv_abs_rpow (by linarith : (1 : ℝ) < 2 * s)).mul_left _).congr_fun fun j =>
    norm_invWeightSeq_sq s (by linarith) hk j

/-- The sequence $j \mapsto w_s(jk)^{-1}$, $j \ne 0$, as an element of
$\ell^2(\mathbb{Z}, \mathbb{C})$. -/
private noncomputable def invWeightLp (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨invWeightSeq s k, memℓp_two_iff.2 (hasSum_norm_invWeightSeq_sq hs hk).summable⟩

private theorem norm_invWeightLp (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) :
    ‖invWeightLp hs hk‖ = (k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have he : -(2 * s) * (1 / 2 : ℝ) = -s := by ring
  have hsqrt : √(((k : ℝ) ^ (2 * s))⁻¹) = (k : ℝ) ^ (-s) := by
    rw [← Real.rpow_neg hk0, Real.sqrt_eq_rpow, ← Real.rpow_mul hk0, he]
  have h : HasSum (fun j : ℤ => ‖(invWeightLp hs hk : ℤ → ℂ) j‖ ^ 2)
      (((k : ℝ) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))) := hasSum_norm_invWeightSeq_sq hs hk
  rw [lp.norm_eq_sqrt_tsum_norm_sq, h.tsum_eq, Real.sqrt_mul (by positivity), hsqrt]

private theorem summable_norm_toLp_mul_sq {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    Summable fun j : ℤ => ‖(toLp s φ : ℤ → ℂ) (j * k)‖ ^ 2 :=
  (lp.hasSum_norm_sq (toLp s φ)).summable.comp_injective
    (mul_left_injective₀ (Int.natCast_ne_zero.2 hk.ne'))

/-- The weighted coefficients of $\varphi$ along the multiples of $k$, $j \mapsto w_s(jk) a_{jk}$,
as an element of $\ell^2(\mathbb{Z}, \mathbb{C})$ of norm at most $\|\varphi\|$. -/
private noncomputable def subLp {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun j : ℤ => toLp s φ (j * k), memℓp_two_iff.2 (summable_norm_toLp_mul_sq hk φ)⟩

private theorem subLp_apply {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) (j : ℤ) :
    (subLp hk φ : ℤ → ℂ) j = toLp s φ (j * k) := rfl

private theorem norm_subLp_le {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖subLp hk φ‖ ≤ ‖φ‖ := by
  have h₁ := lp.hasSum_norm_sq (subLp hk φ)
  have h₂ := lp.hasSum_norm_sq (toLp s φ)
  have hle : ‖subLp hk φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [← h₁.tsum_eq, ← norm_toLp φ, ← h₂.tsum_eq]
    refine le_trans (le_of_eq (tsum_congr fun j => ?_))
      (tsum_comp_le_tsum_of_inj h₂.summable (fun _ => by positivity)
        (mul_left_injective₀ (Int.natCast_ne_zero.2 hk.ne')))
    rw [subLp_apply]
    rfl
  nlinarith [norm_nonneg (subLp hk φ), norm_nonneg φ]

/-- The product of the two sequences above at $j$ is $|a_{jk}|$ for $j \ne 0$, and $0$ at $j = 0$.
-/
private theorem norm_invWeightLp_mul_norm_subLp (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k)
    (φ : PeriodicSobolev s) (j : ℤ) :
    ‖(invWeightLp hs hk : ℤ → ℂ) j‖ * ‖(subLp hk φ : ℤ → ℂ) j‖
      = if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [invWeightLp, invWeightSeq]
  · rw [ite_eq_right hj]
    change ‖invWeightSeq s k j‖ * ‖toLp s φ (j * k)‖ = _
    rw [invWeightSeq, ite_eq_right hj, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s _).le, norm_toLp_apply,
      inv_mul_cancel_left₀ (periodicSobolevWeight_ne_zero s _)]

/-- **Cauchy–Schwarz along the multiples of $k$.** Let $s > 1/2$, $k \ge 1$ and $\varphi \in H^s$
with coefficients $a_m$. Then the family $(|a_{jk}|)_{j \ne 0}$, extended by $0$ at $j = 0$, is
summable.

The bound is `PeriodicSobolev.tsum_norm_coeff_mul_le`. At $k = 1$ this gives the absolute
convergence of the series behind (7.5.10) of [han2009theoretical]. For general $k$ the family is
the tail that the trapezoidal rule leaves. -/
theorem summable_norm_coeff_mul (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    Summable fun j : ℤ => if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, -⟩ := lp.tsum_mul_le_mul_norm hpq (invWeightLp hs hk) (subLp hk φ)
  exact hsum.congr (norm_invWeightLp_mul_norm_subLp hs hk φ)

/-- Let $s > 1/2$, $k \ge 1$ and $\varphi \in H^s$ with coefficients $a_m$. Then
$$\sum_{j \ne 0} |a_{jk}| \le k^{-s} \sqrt{2 \zeta(2s)} \, \|\varphi\|.$$
-/
theorem tsum_norm_coeff_mul_le (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ∑' j : ℤ, (if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖)
      ≤ (k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨-, hle⟩ := lp.tsum_mul_le_mul_norm hpq (invWeightLp hs hk) (subLp hk φ)
  rw [funext (norm_invWeightLp_mul_norm_subLp hs hk φ), norm_invWeightLp hs hk] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (norm_subLp_le hk φ) (by positivity))

/-! ### The Sobolev embedding into the continuous functions -/

/-- **The Sobolev embedding in coefficient form.** Let $s > 1/2$ and $\varphi \in H^s$ with
coefficients $a_m$. Then the family $(|a_m|)_{m \ne 0}$, extended by $0$ at $m = 0$, is
summable.

The proof is the Cauchy–Schwarz inequality against $\sum_{m \ne 0} |m|^{-2s} = 2 \zeta(2s)$,
which converges because $2s > 1$. -/
theorem summable_norm_coeff_ne_zero (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => if m = 0 then (0 : ℝ) else ‖coeff φ m‖ :=
  (summable_norm_coeff_mul hs one_pos φ).congr fun m => by simp

/-- Let $s > 1/2$ and $\varphi \in H^s$ with coefficients $a_m$. Then $\sum_{m \ne 0} |a_m| \le
\sqrt{2 \zeta(2s)} \, \|\varphi\|$. -/
theorem tsum_norm_coeff_ne_zero_le (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, (if m = 0 then (0 : ℝ) else ‖coeff φ m‖) ≤ √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have h := tsum_norm_coeff_mul_le hs one_pos φ
  simp only [Nat.cast_one, Real.one_rpow, one_mul, mul_one] at h
  exact h

/-- Let $s > 1/2$ and $\varphi \in H^s$. The family $(|a_m|)_{m \in \mathbb{Z}}$ of the moduli of
all its coefficients, $m = 0$ included, is summable. -/
theorem summable_norm_coeff (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => ‖coeff φ m‖ := by
  refine ((summable_norm_coeff_ne_zero hs φ).add
    (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).summable).congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp [hm]

/-- Let $s > 1/2$ and $\varphi \in H^s$. The family $(a_m)_{m \in \mathbb{Z}}$ of its coefficients
is summable. -/
theorem summable_coeff (hs : 1 / 2 < s) (φ : PeriodicSobolev s) : Summable (coeff φ) :=
  (summable_norm_coeff hs φ).of_norm

/-- Let $s > 1/2$ and $\varphi \in H^s$ with coefficients $a_m$. Then
$$\sum_{m \in \mathbb{Z}} |a_m| \le |a_0| + \sqrt{2 \zeta(2s)} \, \|\varphi\|.$$
This is the bound (7.5.10) of [han2009theoretical]. -/
theorem tsum_norm_coeff_le (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, ‖coeff φ m‖ ≤ ‖coeff φ 0‖ + √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hsplit : ∑' m : ℤ, ‖coeff φ m‖
      = (∑' m : ℤ, (if m = 0 then (0 : ℝ) else ‖coeff φ m‖)) + ‖coeff φ 0‖ := by
    rw [← (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).tsum_eq,
      ← (summable_norm_coeff_ne_zero hs φ).tsum_add (hasSum_ite_eq (0 : ℤ) ‖coeff φ 0‖).summable]
    refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp [hm]
  rw [hsplit]
  have := tsum_norm_coeff_ne_zero_le hs φ
  linarith

/-- Let $s > 1/2$ and $\varphi \in H^s$ with coefficients $a_m$. Then
$$\sum_{m \in \mathbb{Z}} |a_m| \le \big( 1 + \sqrt{2 \zeta(2s)} \big) \|\varphi\|.$$
This is (7.5.10) of [han2009theoretical] together with $|a_0| \le \|\varphi\|$. -/
theorem tsum_norm_coeff_le' (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, ‖coeff φ m‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ := by
  have h0 : ‖coeff φ 0‖ ≤ ‖φ‖ := by
    simpa using weight_mul_norm_coeff_le φ 0
  have := tsum_norm_coeff_le hs φ
  nlinarith [this, h0]

end PeriodicSobolev

/-! ### The scale: the inclusion $H^s \to H^t$ for $t \le s$ -/

namespace PeriodicSobolev

variable {s t : ℝ}

/-- The coefficient map $\varphi \mapsto (a_m)_{m \in \mathbb{Z}}$ as a linear map from $H^s$ to the
sequences $\mathbb{Z} \to \mathbb{C}$.

It serves to apply `map_sum`. The working interface is `PeriodicSobolev.coeff`. -/
noncomputable def coeffₗ (s : ℝ) : PeriodicSobolev s →ₗ[ℂ] (ℤ → ℂ) where
  toFun := coeff
  map_add' := coeff_add
  map_smul' := coeff_smul

/-- The coefficients of a finite sum are the sums of the coefficients. -/
theorem coeff_sum {ι : Type*} (F : Finset ι) (f : ι → PeriodicSobolev s) :
    coeff (∑ i ∈ F, f i) = ∑ i ∈ F, coeff (f i) :=
  map_sum (coeffₗ s) f F

/-- The $m$-th **coordinate series**: the element of $H^s$ whose coefficient is $1$ at $m$ and $0$
elsewhere. Its coefficient family is finitely supported, so it lies in $H^s$ for every $s$. -/
noncomputable def basisElt (s : ℝ) (m : ℤ) : PeriodicSobolev s :=
  ofCoeff s (fun m' => if m' = m then 1 else 0)
    (memℓp_two_iff.2 (summable_of_ne_finset_zero (s := {m}) fun m' hm' => by
      rw [Finset.mem_singleton] at hm'
      simp [hm']))

/-- The coefficient of the $m$-th coordinate series at $m'$ is $1$ if $m' = m$ and $0$ otherwise. -/
@[simp]
theorem coeff_basisElt (s : ℝ) (m m' : ℤ) :
    coeff (basisElt s m) m' = if m' = m then 1 else 0 := by
  rw [basisElt, coeff_ofCoeff]

/-- The $m$-th coefficient $\varphi \mapsto a_m$, as a continuous linear functional on $H^s$ of norm
at most $w_s(m)^{-1}$, which is $|m|^{-s}$ for $m \ne 0$. -/
noncomputable def coeffL (s : ℝ) (m : ℤ) : PeriodicSobolev s →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => coeff φ m
      map_add' := fun φ ρ => by simp
      map_smul' := fun c φ => by simp }
    (periodicSobolevWeight s m)⁻¹ fun φ => by
      rw [inv_mul_eq_div, le_div_iff₀ (periodicSobolevWeight_pos s m), mul_comm]
      exact weight_mul_norm_coeff_le φ m

/-- The functional of the $m$-th coefficient maps $\varphi$ to $a_m$. -/
@[simp]
theorem coeffL_apply (s : ℝ) (m : ℤ) (φ : PeriodicSobolev s) : coeffL s m φ = coeff φ m := rfl

/-- For $t \le s$, the **inclusion** $H^s \to H^t$: the same formal series, as an element of the
larger space $H^t$. -/
noncomputable def incl (h : t ≤ s) (φ : PeriodicSobolev s) : PeriodicSobolev t :=
  ofCoeff t (coeff φ) (memℓp_two_iff.2 (by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (hasSum_norm_sq φ).summable
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (periodicSobolevWeight_pos t m).le]
    have h1 : periodicSobolevWeight t m * ‖coeff φ m‖ ≤ periodicSobolevWeight s m * ‖coeff φ m‖ :=
      mul_le_mul_of_nonneg_right (periodicSobolevWeight_le h m) (norm_nonneg _)
    have h2 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
      mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
    nlinarith))

/-- The inclusion $H^s \to H^t$ does not change the coefficients. -/
@[simp]
theorem coeff_incl (h : t ≤ s) (φ : PeriodicSobolev s) : coeff (incl h φ) = coeff φ :=
  coeff_ofCoeff _ _ _

/-- For $t \le s$ and $\varphi \in H^s$, $\|\varphi\|_{H^t} \le \|\varphi\|_{H^s}$, because
$w_t \le w_s$. -/
theorem norm_incl_le (h : t ≤ s) (φ : PeriodicSobolev s) : ‖incl h φ‖ ≤ ‖φ‖ := by
  have h₁ := hasSum_norm_sq (incl h φ)
  have h₂ := hasSum_norm_sq φ
  have hle : ‖incl h φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [← h₁.tsum_eq, ← h₂.tsum_eq]
    refine h₁.summable.tsum_le_tsum (fun m => ?_) h₂.summable
    rw [coeff_incl]
    have h1 : periodicSobolevWeight t m * ‖coeff φ m‖ ≤ periodicSobolevWeight s m * ‖coeff φ m‖ :=
      mul_le_mul_of_nonneg_right (periodicSobolevWeight_le h m) (norm_nonneg _)
    have h2 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
      mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
    nlinarith
  nlinarith [norm_nonneg (incl h φ), norm_nonneg φ]

/-- The **inclusion** $H^s \to H^t$ for $t \le s$, as a continuous linear map of norm at most $1$.
-/
noncomputable def inclL (h : t ≤ s) : PeriodicSobolev s →L[ℂ] PeriodicSobolev t :=
  LinearMap.mkContinuous
    { toFun := incl h
      map_add' := fun φ ρ => coeff_injective (by simp)
      map_smul' := fun c φ => coeff_injective (by simp) }
    1 fun φ => by simpa using norm_incl_le h φ

/-- The bundled inclusion `PeriodicSobolev.inclL` agrees with the map `PeriodicSobolev.incl`. -/
@[simp]
theorem inclL_apply (h : t ≤ s) (φ : PeriodicSobolev s) : inclL h φ = incl h φ := rfl

/-- For $t \le s$, the inclusion $H^s \to H^t$ has operator norm at most $1$. -/
theorem norm_inclL_le (h : t ≤ s) : ‖inclL h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Let $\rho \in H^s$. If $\langle e_m, \rho \rangle = 0$ for every coordinate series $e_m$,
$m \in \mathbb{Z}$, then $\rho = 0$.

This is the computation behind both `PeriodicSobolev.denseRange_inclL` and
`PeriodicSobolev.dense_span_basisElt`. -/
theorem eq_zero_of_inner_basisElt_eq_zero {ρ : PeriodicSobolev s}
    (h : ∀ m : ℤ, (inner ℂ (basisElt s m) ρ : ℂ) = 0) : ρ = 0 := by
  refine coeff_injective (funext fun m => ?_)
  have hzero := h m
  rw [inner_eq_tsum, tsum_eq_single m fun m' hm' => by simp [hm']] at hzero
  have hw : ((periodicSobolevWeight s m : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast periodicSobolevWeight_ne_zero s m)
  have h0 : ((periodicSobolevWeight s m : ℂ)) ^ 2 * coeff ρ m = 0 := by simpa using hzero
  simpa using (mul_eq_zero.1 h0).resolve_left hw

/-- For $t \le s$, the inclusion $H^s \to H^t$ has **dense range**. This is the first half of
Proposition 7.5.5 of [han2009theoretical].

In a Hilbert space it suffices that only $0$ is orthogonal to the range. The coordinate series
of $H^t$ lie in the range, so an orthogonal element has all coefficients $0$. -/
theorem denseRange_inclL (h : t ≤ s) : DenseRange (inclL h) := by
  have hbot : (LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ρ hρ
    refine eq_zero_of_inner_basisElt_eq_zero fun m => ?_
    have hmem : incl h (basisElt s m) ∈
        LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t) :=
      ⟨basisElt s m, rfl⟩
    have hzero : (inner ℂ (incl h (basisElt s m)) ρ : ℂ) = 0 :=
      Submodule.mem_orthogonal _ _ |>.1 hρ _ hmem
    rwa [show incl h (basisElt s m) = basisElt t m from
      coeff_injective (by funext m'; simp)] at hzero
  have hdense : Dense
      ((LinearMap.range (inclL h : PeriodicSobolev s →ₗ[ℂ] PeriodicSobolev t)) :
        Set (PeriodicSobolev t)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 hbot)
  rw [LinearMap.coe_range] at hdense
  exact hdense

/-! ### Compactness of the inclusion -/

/-- The **truncation** $H^s \to H^t$ to the frequencies in a finite set $F \subseteq \mathbb{Z}$:
$$\varphi \mapsto \sum_{m \in F} a_m e_m,$$
where $e_m$ is the $m$-th coordinate series of $H^t$. It is a finite sum of rank-one operators,
and it is the finite-rank approximation behind the compactness of the inclusion. -/
noncomputable def truncL (s t : ℝ) (F : Finset ℤ) : PeriodicSobolev s →L[ℂ] PeriodicSobolev t :=
  ∑ m ∈ F, (coeffL s m).smulRight (basisElt t m)

/-- The $m$-th coefficient of the truncation of $\varphi$ to $F$ is $a_m$ if $m \in F$ and $0$
otherwise. -/
theorem coeff_truncL (s t : ℝ) (F : Finset ℤ) (φ : PeriodicSobolev s) (m : ℤ) :
    coeff (truncL s t F φ) m = if m ∈ F then coeff φ m else 0 := by
  classical
  simp only [truncL, sum_apply, ContinuousLinearMap.smulRight_apply,
    coeffL_apply, coeff_sum, Finset.sum_apply, coeff_smul, Pi.smul_apply, coeff_basisElt,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq F m fun m' => coeff φ m'

private theorem isCompactOperator_rankOne (f : PeriodicSobolev s →L[ℂ] ℂ)
    (y : PeriodicSobolev t) : IsCompactOperator (f.smulRight y) := by
  have h1 : IsCompactOperator (⇑f) := isCompactOperator_of_locallyCompactSpace_dom f
  have h2 := h1.continuous_comp (g := fun c : ℂ => c • y) (continuous_id.smul continuous_const)
  have heq : ⇑(f.smulRight y) = (fun c : ℂ => c • y) ∘ ⇑f := by
    funext x; simp
  rw [heq]
  exact h2

/-- A truncation $H^s \to H^t$ to a finite set of frequencies is a compact operator, because it is a
finite sum of rank-one operators. -/
theorem isCompactOperator_truncL (s t : ℝ) (F : Finset ℤ) :
    IsCompactOperator (truncL s t F) :=
  Finset.sum_induction _ (fun A : PeriodicSobolev s →L[ℂ] PeriodicSobolev t =>
      IsCompactOperator A)
    (fun _ _ ha hb => ha.add hb) isCompactOperator_zero
    fun _ _ => isCompactOperator_rankOne _ _

/-- Let $t \le s$, $n \in \mathbb{N}$ and $\varphi \in H^s$. The difference between the inclusion
$H^s \to H^t$ and the truncation to the frequencies in $[-n, n]$ satisfies
$$\big\| \varphi - \textstyle\sum_{|m| \le n} a_m e_m \big\|_{H^t} \le (n + 1)^{-(s - t)}
  \|\varphi\|_{H^s}.$$
Outside $[-n, n]$ the weight $w_t$ is smaller than $w_s$ by the factor $(n + 1)^{t - s}$, which
tends to $0$ as $n \to \infty$ exactly when $t < s$. -/
theorem norm_incl_sub_truncL_le (h : t ≤ s) (n : ℕ) (φ : PeriodicSobolev s) :
    ‖incl h φ - truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)) φ‖
      ≤ (((n : ℝ) + 1) ^ (s - t))⁻¹ * ‖φ‖ := by
  classical
  set F : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ) with hFdef
  set c : ℝ := (((n : ℝ) + 1) ^ (s - t))⁻¹ with hcdef
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (s - t) := Real.rpow_pos_of_pos (by positivity) _
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcoeff : ∀ m : ℤ, coeff (incl h φ - truncL s t F φ) m
      = if m ∈ F then 0 else coeff φ m := by
    intro m
    rw [coeff_sub]
    simp only [Pi.sub_apply, coeff_incl, coeff_truncL]
    split <;> simp
  have hterm : ∀ m : ℤ, (periodicSobolevWeight t m * ‖coeff (incl h φ - truncL s t F φ) m‖) ^ 2
      ≤ c ^ 2 * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 := by
    intro m
    rw [hcoeff m]
    by_cases hmF : m ∈ F
    · rw [ite_eq_left hmF]
      have h0 : (periodicSobolevWeight t m * ‖(0 : ℂ)‖) ^ 2 = 0 := by simp
      rw [h0]
      positivity
    · rw [ite_eq_right hmF]
      have hn1 : ((n : ℤ) + 1) ≤ |m| := by
        rw [hFdef, Finset.mem_Icc, not_and_or, not_le, not_le] at hmF
        rcases hmF with hm | hm
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      have habs : ((n : ℝ) + 1) ≤ |(m : ℝ)| := by
        calc ((n : ℝ) + 1) = (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
          _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast hn1
          _ = |(m : ℝ)| := by rw [Int.cast_abs]
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [abs_zero] at hn1
        omega
      have hmpos : (0 : ℝ) < |(m : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hm0)
      have hkey : periodicSobolevWeight t m ≤ c * periodicSobolevWeight s m := by
        rw [hcdef, inv_mul_eq_div, le_div_iff₀ hpos,
          periodicSobolevWeight_of_ne_zero t hm0, periodicSobolevWeight_of_ne_zero s hm0]
        calc |(m : ℝ)| ^ t * ((n : ℝ) + 1) ^ (s - t)
            ≤ |(m : ℝ)| ^ t * |(m : ℝ)| ^ (s - t) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) habs (by linarith : (0 : ℝ) ≤ s - t))
                (Real.rpow_nonneg (abs_nonneg _) t)
          _ = |(m : ℝ)| ^ s := by
              rw [← Real.rpow_add hmpos, show t + (s - t) = s by ring]
      have h1 : 0 ≤ periodicSobolevWeight t m * ‖coeff φ m‖ :=
        mul_nonneg (periodicSobolevWeight_pos t m).le (norm_nonneg _)
      have h2 : periodicSobolevWeight t m * ‖coeff φ m‖
          ≤ c * periodicSobolevWeight s m * ‖coeff φ m‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      nlinarith
  have h₁ := hasSum_norm_sq (incl h φ - truncL s t F φ)
  have h₂ := hasSum_norm_sq φ
  have hsq : ‖incl h φ - truncL s t F φ‖ ^ 2 ≤ (c * ‖φ‖) ^ 2 := by
    rw [← h₁.tsum_eq, mul_pow]
    have hmul : HasSum (fun m : ℤ => c ^ 2 * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2)
        (c ^ 2 * ‖φ‖ ^ 2) := h₂.mul_left _
    have hcmp := h₁.summable.tsum_le_tsum hterm hmul.summable
    rwa [hmul.tsum_eq] at hcmp
  have hnn : (0 : ℝ) ≤ c * ‖φ‖ := mul_nonneg hcpos.le (norm_nonneg φ)
  nlinarith [norm_nonneg (incl h φ - truncL s t F φ), hnn, hsq]

/-- For $t < s$, the inclusion $H^s \to H^t$ is a **compact operator**. This is the second half of
Proposition 7.5.5 of [han2009theoretical].

The inclusion is the limit in operator norm of its truncations to the frequencies in $[-n, n]$,
at the rate $(n + 1)^{t - s}$. -/
theorem isCompactOperator_inclL (h : t < s) : IsCompactOperator (inclL h.le) := by
  refine IsCompactOperator.of_tendsto
    (A := fun n : ℕ => truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)))
    (fun n => isCompactOperator_truncL s t _) ?_
  have hbound : ∀ n : ℕ,
      ‖truncL s t (Finset.Icc (-(n : ℤ)) (n : ℤ)) - inclL h.le‖
        ≤ (((n : ℝ) + 1) ^ (s - t))⁻¹ := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
    rw [sub_apply, ← norm_neg, neg_sub, inclL_apply]
    exact norm_incl_sub_truncL_le h.le n φ
  have hnat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hzero : Filter.Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ (s - t))⁻¹)
      Filter.atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < s - t)).comp hnat).inv_tendsto_atTop
  exact squeeze_zero (fun n => norm_nonneg _) hbound hzero

end PeriodicSobolev

/-! ### The characters of the circle, read on the line -/

/-- The $m$-th **character** of the circle of circumference $T$, read as a function on the line:
$$e_m(x) = e^{2 \pi i m x / T}.$$
It is the $m$-th term of a Fourier series up to the coefficient. The results below use only
`norm_periodicChar` and `sum_periodicChar`. -/
noncomputable def periodicChar (T : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I * m * x / T)

/-- The character is $e_m(x) = \exp(i \theta)$ with the real number $\theta = 2 \pi m x / T$. -/
theorem periodicChar_eq (T : ℝ) (m : ℤ) (x : ℝ) :
    periodicChar T m x = Complex.exp (((2 * π * m * x / T : ℝ) : ℂ) * Complex.I) := by
  rw [periodicChar]
  congr 1
  push_cast
  ring

/-- The characters have modulus one: $|e^{2 \pi i m x / T}| = 1$. -/
@[simp]
theorem norm_periodicChar (T : ℝ) (m : ℤ) (x : ℝ) : ‖periodicChar T m x‖ = 1 := by
  rw [periodicChar_eq, Complex.norm_exp_ofReal_mul_I]

/-- The character of index $0$ is the constant $1$. -/
@[simp]
theorem periodicChar_zero (T : ℝ) (x : ℝ) : periodicChar T 0 x = 1 := by
  simp [periodicChar]

/-- Each character $x \mapsto e^{2 \pi i m x / T}$ is continuous. -/
theorem continuous_periodicChar (T : ℝ) (m : ℤ) : Continuous (periodicChar T m) :=
  Complex.continuous_exp.comp (by fun_prop)

/-- For $T \ne 0$, the characters $x \mapsto e^{2 \pi i m x / T}$ have period $T$. -/
theorem periodicChar_periodic {T : ℝ} (hT : T ≠ 0) (m : ℤ) :
    Function.Periodic (periodicChar T m) T := by
  intro x
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  rw [periodicChar, periodicChar, show 2 * (π : ℂ) * Complex.I * m * ((x + T : ℝ) : ℂ) / T
      = 2 * (π : ℂ) * Complex.I * m * x / T + (m : ℂ) * (2 * (π : ℂ) * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The trapezoidal sum of a character.** Let $T \ne 0$, $k \ge 1$ and $m \in \mathbb{Z}$. Then
$$\sum_{j=0}^{k-1} e^{2 \pi i m (j + 1) / k} = \begin{cases} k, & k \mid m, \\ 0, &
  \text{otherwise}, \end{cases}$$
where the left side is $\sum_{j=0}^{k-1} e_m((j + 1) T / k)$ for the character $e_m$ of period
$T$. This is (7.5.14) of [han2009theoretical].

The left side is a geometric sum of $k$-th roots of unity, degenerate exactly on the multiples
of $k$. This is the whole content of the quadrature bound. -/
theorem sum_periodicChar {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) (m : ℤ) :
    ∑ j ∈ Finset.range k, periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ)))
      = if (k : ℤ) ∣ m then (k : ℂ) else 0 := by
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  have hk' : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set ζ : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I / (k : ℂ)) with hζdef
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  set z : ℂ := ζ ^ (m : ℤ) with hzdef
  have hterm : ∀ j : ℕ, periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ))) = z ^ (j + 1) := by
    intro j
    rw [hzdef, hζdef, ← Complex.exp_int_mul, periodicChar, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  have hzk : z ^ k = 1 := by
    rw [hzdef, hζdef, ← Complex.exp_int_mul, ← Complex.exp_nat_mul,
      show (k : ℂ) * ((m : ℂ) * (2 * (π : ℂ) * Complex.I / (k : ℂ)))
        = (m : ℂ) * (2 * (π : ℂ) * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I m
  by_cases hdvd : (k : ℤ) ∣ m
  · have hz1 : z = 1 := (hprim.zpow_eq_one_iff_dvd m).2 hdvd
    rw [ite_eq_left hdvd]
    simp [hz1]
  · have hz1 : z ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd m).1 h)
    rw [ite_eq_right hdvd]
    have hgeom : ∑ j ∈ Finset.range k, z ^ (j + 1) = z * ∑ j ∈ Finset.range k, z ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hgeom, geom_sum_eq hz1, hzk, sub_self, zero_div, mul_zero]

/-! ### The sum of the series, and the trapezoidal rule -/

namespace PeriodicSobolev

variable {s : ℝ}

/-- The **sum of the Fourier series** of $\varphi \in H^s$, read with period $T$:
$$\varphi(x) = \sum_{m \in \mathbb{Z}} a_m e^{2 \pi i m x / T}.$$
For $s > 1/2$ the coefficients are absolutely summable, so the series converges uniformly, and
the sum is a continuous function of period $T$. For $s \le 1/2$ the series need not converge,
and where it does not, the value is $0$.

The period is a parameter of this passage to functions, not of the space. -/
noncomputable def eval (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) : ℂ :=
  ∑' m : ℤ, coeff φ m * periodicChar T m x

/-- For $s > 1/2$, the series $\sum_m a_m e^{2 \pi i m x / T}$ converges at every $x$. -/
theorem summable_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    Summable fun m : ℤ => coeff φ m * periodicChar T m x :=
  Summable.of_norm ((summable_norm_coeff hs φ).congr fun m => by
    rw [norm_mul, norm_periodicChar, mul_one])

/-- For $s > 1/2$, the series $\sum_m a_m e^{2 \pi i m x / T}$ has the sum
`PeriodicSobolev.eval T φ x`. -/
theorem hasSum_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    HasSum (fun m : ℤ => coeff φ m * periodicChar T m x) (eval T φ x) :=
  (summable_eval hs T φ x).hasSum

/-- For $s > 1/2$, $|\varphi(x)| \le \sum_m |a_m|$ at every $x$, because the characters have modulus
one. Every uniform bound on the sum of the series follows from this one. -/
theorem norm_eval_le_tsum_norm_coeff (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval T φ x‖ ≤ ∑' m : ℤ, ‖coeff φ m‖ := by
  refine le_trans (norm_tsum_le_tsum_norm ((summable_norm_coeff hs φ).congr fun m => by
    rw [norm_mul, norm_periodicChar, mul_one])) (le_of_eq (tsum_congr fun m => ?_))
  rw [norm_mul, norm_periodicChar, mul_one]

/-- Let $s > 1/2$ and $\varphi \in H^s$. Then for every real $x$,
$$|\varphi(x)| \le \big( 1 + \sqrt{2 \zeta(2s)} \big) \|\varphi\|,$$
so the embedding of $H^s$ into the bounded functions is continuous. This corresponds to the
bound (7.5.11) of Proposition 7.5.4 of [han2009theoretical] at $k = 0$, with the normalization
of this module. -/
theorem norm_eval_le (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval T φ x‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ :=
  (norm_eval_le_tsum_norm_coeff hs T φ x).trans (tsum_norm_coeff_le' hs φ)

/-- For $s > 1/2$, the sum of the series is a continuous function, because the convergence is
uniform. With `PeriodicSobolev.eval_periodic`, this is the statement $\varphi \in C_p(T)$ of
Proposition 7.5.4 of [han2009theoretical]. -/
theorem continuous_eval (hs : 1 / 2 < s) (T : ℝ) (φ : PeriodicSobolev s) :
    Continuous (eval T φ) :=
  continuous_tsum (fun m => continuous_const.mul (continuous_periodicChar T m))
    (summable_norm_coeff hs φ) fun m x => by rw [norm_mul, norm_periodicChar, mul_one]

/-- For $T \ne 0$, the sum of the series $\sum_m a_m e^{2 \pi i m x / T}$ has period $T$. -/
theorem eval_periodic {T : ℝ} (hT : T ≠ 0) (φ : PeriodicSobolev s) :
    Function.Periodic (eval T φ) T := fun x =>
  tsum_congr fun m => by rw [periodicChar_periodic hT m x]

/-! ### The integral over a period -/

/-- Let $s > 1/2$, $T > 0$ and $\varphi \in H^s$. The integral over one period picks out the
constant term:
$$\int_0^T \varphi(x) \, dx = T a_0.$$
-/
theorem intervalIntegral_eval (hs : 1 / 2 < s) {T : ℝ} (hT : 0 < T) (φ : PeriodicSobolev s) :
    (∫ x in (0 : ℝ)..T, eval T φ x) = T * coeff φ 0 := by
  have hvol : (MeasureTheory.volume.real (Set.Ioc (0 : ℝ) T)) = T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT.le]
  have hint : ∀ m : ℤ, MeasureTheory.IntegrableOn
      (fun x : ℝ => coeff φ m * periodicChar T m x) (Set.Ioc 0 T) := fun m =>
    (continuous_const.mul (continuous_periodicChar T m)).integrableOn_Ioc
  have hnorm : ∀ m : ℤ, (∫ x in Set.Ioc (0 : ℝ) T, ‖coeff φ m * periodicChar T m x‖)
      = ‖coeff φ m‖ * T := by
    intro m
    simp only [norm_mul, norm_periodicChar, mul_one]
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul, mul_comm]
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T))
    (F := fun (m : ℤ) (x : ℝ) => coeff φ m * periodicChar T m x) hint
    (((summable_norm_coeff hs φ).mul_right T).congr fun m => (hnorm m).symm)
  have hterm : ∀ m : ℤ, (∫ x in Set.Ioc (0 : ℝ) T, coeff φ m * periodicChar T m x)
      = if m = 0 then (T : ℂ) * coeff φ 0 else 0 := by
    intro m
    rw [← intervalIntegral.integral_of_le hT.le]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [ite_eq_left rfl]
      simp only [periodicChar_zero, mul_one, intervalIntegral.integral_const, sub_zero]
      simp [Complex.real_smul]
    · rw [ite_eq_right hm]
      have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
      have hc : (2 * (π : ℂ) * Complex.I * m / T) ≠ 0 := by
        refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
          Complex.I_ne_zero) ?_) hT'
        · exact_mod_cast Real.pi_ne_zero
        · exact_mod_cast hm
      have hrw : ∀ x : ℝ, coeff φ m * periodicChar T m x
          = coeff φ m * Complex.exp ((2 * (π : ℂ) * Complex.I * m / T) * x) := by
        intro x
        rw [periodicChar]
        ring_nf
      rw [intervalIntegral.integral_congr (g := fun x : ℝ => coeff φ m *
          Complex.exp ((2 * (π : ℂ) * Complex.I * m / T) * x)) fun x _ => hrw x,
        intervalIntegral.integral_const_mul, integral_exp_mul_complex hc,
        show (2 * (π : ℂ) * Complex.I * m / T) * (T : ℂ)
          = (m : ℂ) * (2 * (π : ℂ) * Complex.I) by field_simp,
        Complex.exp_int_mul_two_pi_mul_I]
      simp
  rw [funext hterm] at hsum
  rw [intervalIntegral.integral_of_le hT.le]
  exact ((hasSum_ite_eq (0 : ℤ) ((T : ℂ) * coeff φ 0)).unique hsum).symm

/-! ### The trapezoidal rule -/

/-- The **trapezoidal rule** for a function $f$ of period $T$, with $k$ points:
$$T_k(f) = h \sum_{j=1}^{k} f(jh), \qquad h = T / k.$$
For a periodic $f$ the two endpoints of the interval carry the same value. So the half weights
at the ends merge into one full weight, and the rule is an equally weighted sum. For $k = 0$ the
value is $0$. -/
noncomputable def trapezoidSum (T : ℝ) (k : ℕ) (f : ℝ → ℂ) : ℂ :=
  ((T / (k : ℝ) : ℝ) : ℂ) * ∑ j ∈ Finset.range k, f (((j : ℝ) + 1) * (T / (k : ℝ)))

/-- Let $s > 1/2$, $T \ne 0$, $k \ge 1$ and $\varphi \in H^s$. The trapezoidal sum of the series is
$T$ times the sum of its coefficients along the multiples of $k$:
$$T_k(\varphi) = T \sum_{j \in \mathbb{Z}} a_{jk}.$$
This aliasing formula is behind Proposition 7.5.6 of [han2009theoretical]. -/
theorem trapezoidSum_eval (hs : 1 / 2 < s) {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k)
    (φ : PeriodicSobolev s) :
    trapezoidSum T k (eval T φ) = T * ∑' j : ℤ, coeff φ (j * k) := by
  classical
  have hk' : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set g : ℤ → ℂ := fun m => if (k : ℤ) ∣ m then coeff φ m else 0 with hgdef
  have hsub : Function.support g ⊆ Set.range fun j : ℤ => j * (k : ℤ) := by
    intro m hm
    by_cases hd : (k : ℤ) ∣ m
    · obtain ⟨d, rfl⟩ := hd
      exact ⟨d, by ring⟩
    · exact absurd (show g m = 0 by simp [hgdef, hd]) (Function.mem_support.1 hm)
  have hstep : HasSum (fun m : ℤ => (k : ℂ) * g m)
      (∑ j ∈ Finset.range k, eval T φ (((j : ℝ) + 1) * (T / (k : ℝ)))) := by
    have h := hasSum_sum (s := Finset.range k)
      (f := fun (j : ℕ) (m : ℤ) => coeff φ m * periodicChar T m (((j : ℝ) + 1) * (T / (k : ℝ))))
      (a := fun j : ℕ => eval T φ (((j : ℝ) + 1) * (T / (k : ℝ))))
      fun j _ => hasSum_eval hs T φ _
    refine h.congr_fun fun m => ?_
    rw [← Finset.mul_sum, sum_periodicChar hT hk m, hgdef]
    by_cases hd : (k : ℤ) ∣ m <;> simp [hd, mul_comm]
  have hgsum : ∑' m : ℤ, g m = ∑' j : ℤ, coeff φ (j * k) := by
    refine ((mul_left_injective₀ (Int.natCast_ne_zero.2 hk.ne')).tsum_eq hsub).symm.trans
      (tsum_congr fun j => ?_)
    simp only [hgdef]
    rw [ite_eq_left (dvd_mul_left (k : ℤ) j)]
  rw [trapezoidSum, ← hstep.tsum_eq, tsum_mul_left, hgsum]
  push_cast
  field_simp

/-- The **trapezoidal rule is spectrally accurate** on smooth periodic integrands. Let $s > 1/2$,
$T > 0$, $k \ge 1$ and $\varphi \in H^s$. Then
$$\Big| \int_0^T \varphi(x) \, dx - T_k(\varphi) \Big| \le T \, k^{-s} \sqrt{2 \zeta(2s)} \,
  \|\varphi\|.$$
This is Proposition 7.5.6 of [han2009theoretical]. For the period $T = 2\pi$ the norm of
$\varphi$ in the book is $\sqrt{2\pi} \, \|\varphi\|$, and the bound becomes
$\sqrt{4 \pi \zeta(2s)} \, k^{-s}$ times that norm, which is the bound (7.5.13).

By (7.5.14) the error is exactly $-T$ times the tail $\sum_{j \ne 0} a_{jk}$, and the
Cauchy–Schwarz inequality along the multiples of $k$ bounds the tail. -/
theorem norm_intervalIntegral_sub_trapezoidSum_le (hs : 1 / 2 < s) {T : ℝ} (hT : 0 < T)
    {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖(∫ x in (0 : ℝ)..T, eval T φ x) - trapezoidSum T k (eval T φ)‖
      ≤ T * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by
  have hnormtail : ∀ j : ℤ, ‖(if j = 0 then (0 : ℂ) else coeff φ (j * k))‖
      = if j = 0 then (0 : ℝ) else ‖coeff φ (j * k)‖ := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]
  have htailnorm : Summable fun j : ℤ => ‖(if j = 0 then (0 : ℂ) else coeff φ (j * k))‖ :=
    (summable_norm_coeff_mul hs hk φ).congr fun j => (hnormtail j).symm
  have htailsum : Summable fun j : ℤ => (if j = 0 then (0 : ℂ) else coeff φ (j * k)) :=
    Summable.of_norm htailnorm
  have hS : Summable fun j : ℤ => coeff φ (j * k) :=
    (summable_coeff hs φ).comp_injective (mul_left_injective₀ (Int.natCast_ne_zero.2 hk.ne'))
  have hsplit : ∑' j : ℤ, coeff φ (j * k)
      = coeff φ 0 + ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k)) := by
    refine hS.hasSum.unique ?_
    refine ((hasSum_ite_eq (0 : ℤ) (coeff φ 0)).add htailsum.hasSum).congr_fun fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]
  rw [intervalIntegral_eval hs hT φ, trapezoidSum_eval hs hT.ne' hk φ, hsplit,
    show (T : ℂ) * coeff φ 0 - (T : ℂ) * (coeff φ 0 +
        ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k)))
      = -((T : ℂ) * ∑' j : ℤ, (if j = 0 then (0 : ℂ) else coeff φ (j * k))) by ring,
    norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
  refine mul_le_mul_of_nonneg_left ?_ hT.le
  exact le_trans (norm_tsum_le_tsum_norm htailnorm)
    (le_trans (le_of_eq (tsum_congr hnormtail)) (tsum_norm_coeff_mul_le hs hk φ))

end PeriodicSobolev

/-! ### Periodic functions on the line, lifted to the circle -/

namespace Function.Periodic

variable {F : Type*} {T : ℝ} [hT : Fact (0 < T)]

omit hT in
/-- Let $f = g$ be $T$-periodic functions. Then their lifts to `AddCircle T` are equal, whatever the
proofs of periodicity. -/
theorem lift_congr {f g : ℝ → F} (h : f = g) (hf : Periodic f T) (hg : Periodic g T) :
    hf.lift = hg.lift := by
  subst h
  rfl

/-- For $T > 0$ and a $T$-periodic function $f$, the lift of $f$ to `AddCircle T` agrees with
`AddCircle.liftIoc T a f` for every $a$. -/
theorem lift_eq_liftIoc {f : ℝ → F} (hf : Periodic f T) (a : ℝ) :
    hf.lift = AddCircle.liftIoc T a f := by
  funext t
  rw [← AddCircle.coe_equivIoc (y := t), lift_coe,
    AddCircle.liftIoc_coe_apply (AddCircle.equivIoc T a t).2]

omit hT in
/-- The lift of a continuous periodic function to the circle is continuous. -/
theorem continuous_lift [TopologicalSpace F] {f : ℝ → F} (hf : Periodic f T)
    (hc : Continuous f) : Continuous hf.lift :=
  continuous_coinduced_dom.mpr hc

/-- For $T > 0$ and a $T$-periodic function $f : \mathbb{R} \to \mathbb{C}$, the $n$-th Fourier
coefficient of the lift of $f$ to `AddCircle T` is the Fourier coefficient of $f$ on $[0, T]$,
`fourierCoeffOn`. -/
theorem fourierCoeff_lift_eq_fourierCoeffOn {f : ℝ → ℂ} (hf : Periodic f T) (n : ℤ) :
    fourierCoeff hf.lift n = fourierCoeffOn (lt_add_of_pos_right 0 hT.out) f n := by
  rw [lift_eq_liftIoc hf 0, fourierCoeff_liftIoc_eq]

end Function.Periodic

/-!
### Absolutely convergent trigonometric series on the circle

An absolutely summable coefficient family $c : \mathbb{Z} \to \mathbb{C}$ sums to a continuous
function $t \mapsto \sum_m c_m e_m(t)$ on the circle `AddCircle T`, where $e_m$ is `fourier m`. Its
Fourier coefficients are the $c_m$, and Parseval's identity reads $\sum_m |c_m|^2 = T^{-1} \int_0^T
|\sum_m c_m e_m|^2$. This is the function side of `PeriodicSobolev.eval`.
-/

section TrigSeries

open AddCircle MeasureTheory

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in
/-- If $\sum_m |c_m| < \infty$, then $t \mapsto \sum_m c_m e_m(t)$ is continuous on `AddCircle T`,
where $e_m$ is `fourier m`. -/
theorem continuous_tsum_smul_fourier {c : ℤ → ℂ} (hc : Summable fun m => ‖c m‖) :
    Continuous fun t : AddCircle T => ∑' m : ℤ, c m • fourier m t := by
  refine continuous_tsum (fun m => (map_continuous (fourier m)).const_smul (c m)) hc
    fun m t => ?_
  rw [norm_smul, norm_fourier_apply, mul_one]

/-- **The Fourier coefficients of an absolutely convergent trigonometric series are its
coefficients.** Let $T > 0$ and $\sum_m |c_m| < \infty$. Then the $n$-th Fourier coefficient of
$t \mapsto \sum_m c_m e_m(t)$ on `AddCircle T` is $c_n$.

The series converges uniformly, so the integral that defines the Fourier coefficient can be
taken term by term, and `fourierCoeff_fourier` keeps the $n$-th term alone. -/
theorem fourierCoeff_tsum_smul_fourier {c : ℤ → ℂ} (hc : Summable fun m => ‖c m‖) (n : ℤ) :
    fourierCoeff (fun t : AddCircle T => ∑' m : ℤ, c m • fourier m t) n = c n := by
  set F : ℤ → AddCircle T → ℂ := fun m t => fourier (-n) t • (c m • fourier m t) with hF
  have hnorm : ∀ m t, ‖F m t‖ = ‖c m‖ := by
    intro m t
    simp only [hF, norm_smul, norm_fourier_apply, one_mul, mul_one]
  have hint : ∀ m, Integrable (F m) haarAddCircle := fun m =>
    ((map_continuous (fourier (-n))).smul ((map_continuous (fourier m)).const_smul
      (c m))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable fun m => ∫ t, ‖F m t‖ ∂haarAddCircle := by
    refine hc.congr fun m => ?_
    simp only [hnorm, integral_const, probReal_univ, one_smul]
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hterm : ∀ m, ∫ t, F m t ∂haarAddCircle = if m = n then c m else 0 := by
    intro m
    have : ∫ t, F m t ∂haarAddCircle = c m * fourierCoeff (T := T) (fourier m) n := by
      rw [fourierCoeff, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hF, smul_eq_mul]
      ring
    rw [this, fourierCoeff_fourier, Pi.single_apply]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero]
  rw [fourierCoeff]
  have hswap : ∀ t : AddCircle T, fourier (-n) t • ∑' m, c m • fourier m t = ∑' m, F m t := by
    intro t
    rw [← tsum_const_smul'' (fourier (-n) t)]
  simp_rw [hswap]
  rw [← h.tsum_eq]
  simp_rw [hterm]
  rw [tsum_ite_eq]

/-- For $T > 0$ and a function $F$ on `AddCircle T` with values in a real normed space $E$, the
integral against the Haar probability measure is the average over one period:
$$\int F \, d\mathrm{haar} = T^{-1} \int_0^T F(x) \, dx.$$
-/
theorem integral_haarAddCircle_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : AddCircle T → E) :
    ∫ t, F t ∂haarAddCircle = T⁻¹ • ∫ x in (0 : ℝ)..T, F x := by
  rw [integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T 0 F, zero_add]

/-- **Parseval's identity for a continuous function on the circle.** For $T > 0$ and a continuous
function $G$ on `AddCircle T` with complex values,
$$\sum_{i \in \mathbb{Z}} |\hat G_i|^2 = \int |G|^2 \, d\mathrm{haar},$$
where the integral is against the Haar probability measure.

The proof goes through the image of $G$ in $L^2$ of the Haar measure. -/
theorem hasSum_sq_fourierCoeff_of_continuous {G : AddCircle T → ℂ} (hG : Continuous G) :
    HasSum (fun i : ℤ => ‖fourierCoeff G i‖ ^ 2)
      (∫ t : AddCircle T, ‖G t‖ ^ 2 ∂haarAddCircle) := by
  have h := hasSum_sq_fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ ⟨G, hG⟩)
  simp_rw [fourierCoeff_toLp] at h
  convert h using 1
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := @haarAddCircle T _) (𝕜 := ℂ)
    ⟨G, hG⟩] with t ht
  rw [ht]
  rfl

/-- Parseval's identity for a continuous function $G$ on the circle `AddCircle T`, with the integral
over a period:
$$\sum_{i \in \mathbb{Z}} |\hat G_i|^2 = T^{-1} \int_0^T |G(x)|^2 \, dx.$$
-/
theorem hasSum_sq_fourierCoeff_of_continuous' {G : AddCircle T → ℂ} (hG : Continuous G) :
    HasSum (fun i : ℤ => ‖fourierCoeff G i‖ ^ 2) (T⁻¹ * ∫ x in (0 : ℝ)..T, ‖G x‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeff_of_continuous hG
  rwa [integral_haarAddCircle_eq_intervalIntegral (fun t : AddCircle T => ‖G t‖ ^ 2),
    smul_eq_mul] at h

/-- **Parseval's identity for an absolutely convergent trigonometric series.** Let $T > 0$ and
$\sum_m |c_m| < \infty$. Then
$$\int_0^T \Big| \sum_{m \in \mathbb{Z}} c_m e_m(x) \Big|^2 dx = T \sum_{m \in \mathbb{Z}}
  |c_m|^2,$$
where $e_m$ is `fourier m` on `AddCircle T`. -/
theorem intervalIntegral_norm_tsum_smul_fourier_sq {c : ℤ → ℂ} (hc : Summable fun m => ‖c m‖) :
    ∫ x in (0 : ℝ)..T, ‖∑' m : ℤ, c m • fourier m (x : AddCircle T)‖ ^ 2
      = T * ∑' m : ℤ, ‖c m‖ ^ 2 := by
  have h := (hasSum_sq_fourierCoeff_of_continuous' (T := T)
    (continuous_tsum_smul_fourier hc)).tsum_eq
  simp_rw [fourierCoeff_tsum_smul_fourier hc] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hT.out.ne', one_mul]

end TrigSeries

/-! ### The sum of the series on the circle, and its Fourier coefficients -/

namespace PeriodicSobolev

open AddCircle MeasureTheory

variable {s : ℝ}

/-- The character $x \mapsto e^{2 \pi i m x / T}$ on the line is `fourier m` on `AddCircle T`,
evaluated at the image of $x$. -/
theorem periodicChar_eq_fourier (T : ℝ) (m : ℤ) (x : ℝ) :
    periodicChar T m x = fourier m (x : AddCircle T) := by
  rw [fourier_coe_apply, periodicChar]

/-- The sum of the series of $\varphi \in H^s$ at $x$ is $\sum_m a_m e_m(x)$, where $e_m$ is
`fourier m` on `AddCircle T`. -/
theorem eval_eq_tsum_smul_fourier (T : ℝ) (φ : PeriodicSobolev s) (x : ℝ) :
    eval T φ x = ∑' m : ℤ, coeff φ m • fourier m (x : AddCircle T) := by
  simp_rw [eval, periodicChar_eq_fourier, smul_eq_mul]

variable {T : ℝ} [hT : Fact (0 < T)]

/-- For $T > 0$, the lift to `AddCircle T` of the sum of the series of $\varphi$ is the
trigonometric series $t \mapsto \sum_m a_m e_m(t)$ with the same coefficients, where $e_m$ is
`fourier m`. -/
theorem lift_eval (φ : PeriodicSobolev s) :
    (eval_periodic hT.out.ne' φ).lift
      = fun t : AddCircle T => ∑' m : ℤ, coeff φ m • fourier m t := by
  funext t
  induction t using QuotientAddGroup.induction_on with
  | H x => exact eval_eq_tsum_smul_fourier T φ x

/-- **The Fourier coefficients of the sum of the series are its coefficients.** Let $s > 1/2$,
$T > 0$ and $\varphi \in H^s$. Then the $n$-th Fourier coefficient of the lift of the sum of the
series to `AddCircle T` is $a_n$.

This connects `PeriodicSobolev` with Mathlib's `fourierCoeff`. -/
theorem fourierCoeff_lift_eval (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (n : ℤ) :
    fourierCoeff (eval_periodic hT.out.ne' φ).lift n = coeff φ n := by
  rw [lift_eval]
  exact fourierCoeff_tsum_smul_fourier (summable_norm_coeff hs φ) n

/-- For $s > 1/2$ and $T > 0$, the Fourier coefficients of the lift of the sum of the series to
`AddCircle T` are summable. -/
theorem summable_fourierCoeff_lift_eval (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Summable (fourierCoeff (eval_periodic hT.out.ne' φ).lift) :=
  (summable_coeff hs φ).congr fun n => (fourierCoeff_lift_eval hs φ n).symm

/-- **Parseval's identity for the sum of the series.** Let $s > 1/2$, $T > 0$ and $\varphi \in H^s$.
Then
$$\int_0^T |\varphi(x)|^2 \, dx = T \sum_{m \in \mathbb{Z}} |a_m|^2.$$
-/
theorem intervalIntegral_norm_eval_sq (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    ∫ x in (0 : ℝ)..T, ‖eval T φ x‖ ^ 2 = T * ∑' m : ℤ, ‖coeff φ m‖ ^ 2 := by
  simp_rw [eval_eq_tsum_smul_fourier T φ]
  exact intervalIntegral_norm_tsum_smul_fourier_sq (summable_norm_coeff hs φ)

end PeriodicSobolev

/-! ### Density of the coordinate series, and the duality pairing -/

/-- The weights of opposite orders are reciprocal: $w_t(m) \, w_{-t}(m) = 1$ for all $t$ and $m$.
This is why $H^{-t}$ is the dual of $H^t$. -/
theorem periodicSobolevWeight_mul_neg (t : ℝ) (m : ℤ) :
    periodicSobolevWeight t m * periodicSobolevWeight (-t) m = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [periodicSobolevWeight_of_ne_zero t hm, periodicSobolevWeight_of_ne_zero (-t) hm,
      ← Real.rpow_add (abs_pos.2 (Int.cast_ne_zero.2 hm)), add_neg_cancel, Real.rpow_zero]

namespace PeriodicSobolev

variable {s t : ℝ}

/-- **The trigonometric polynomials are dense in $H^s$**, for every real $s$: the linear span of the
coordinate series $e_m$, $m \in \mathbb{Z}$, is dense.

In a Hilbert space it suffices that only $0$ is orthogonal to them. -/
theorem dense_span_basisElt (s : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (basisElt s)) : Submodule ℂ (PeriodicSobolev s)) :
      Set (PeriodicSobolev s)) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 (Submodule.eq_bot_iff _ |>.2 fun ρ hρ => ?_))
  refine eq_zero_of_inner_basisElt_eq_zero fun m => ?_
  exact Submodule.mem_orthogonal _ _ |>.1 hρ _ (Submodule.subset_span ⟨m, rfl⟩)

/-! ### The duality pairing -/

/-- For $\varphi \in H^t$ and $\eta \in H^{-t}$ with coefficients $a_m$ and $b_m$, the product of
the $m$-th entries of their weighted coefficient sequences has the modulus
$|a_m \overline{b_m}|$. -/
theorem norm_toLp_mul_norm_toLp (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t))
    (m : ℤ) : ‖toLp t φ m‖ * ‖toLp (-t) η m‖ = ‖coeff φ m * conj (coeff η m)‖ := by
  rw [norm_toLp_apply, norm_toLp_apply, norm_mul, RCLike.norm_conj]
  calc periodicSobolevWeight t m * ‖coeff φ m‖ * (periodicSobolevWeight (-t) m * ‖coeff η m‖)
      = (periodicSobolevWeight t m * periodicSobolevWeight (-t) m)
        * (‖coeff φ m‖ * ‖coeff η m‖) := by ring
    _ = ‖coeff φ m‖ * ‖coeff η m‖ := by rw [periodicSobolevWeight_mul_neg, one_mul]

/-- **The duality pairing.** For $\varphi \in H^t$ and $\eta \in H^{-t}$ with coefficients $a_m$ and
$b_m$, the series $\sum_m a_m \overline{b_m}$ converges absolutely. This is (7.5.6)–(7.5.7) of
[han2009theoretical]. -/
theorem summable_coeff_mul_conj (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t)) :
    Summable fun m : ℤ => coeff φ m * conj (coeff η m) := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, -⟩ := lp.tsum_mul_le_mul_norm hpq (toLp t φ) (toLp (-t) η)
  exact Summable.of_norm (hsum.congr fun m => norm_toLp_mul_norm_toLp t φ η m)

/-- For $\varphi \in H^t$ and $\eta \in H^{-t}$ with coefficients $a_m$ and $b_m$,
$$\Big| \sum_{m \in \mathbb{Z}} a_m \overline{b_m} \Big| \le \|\varphi\|_{H^t} \,
  \|\eta\|_{H^{-t}}.$$
This is (7.5.7) of [han2009theoretical], where the two norms are written $\|\varphi\|_{*,t}$ and
$\|\eta\|_{*,-t}$. -/
theorem norm_tsum_coeff_mul_conj_le (t : ℝ) (φ : PeriodicSobolev t) (η : PeriodicSobolev (-t)) :
    ‖∑' m : ℤ, coeff φ m * conj (coeff η m)‖ ≤ ‖φ‖ * ‖η‖ := by
  have hpq : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  obtain ⟨hsum, hle⟩ := lp.tsum_mul_le_mul_norm hpq (toLp t φ) (toLp (-t) η)
  rw [funext fun m => norm_toLp_mul_norm_toLp t φ η m] at hsum hle
  rw [norm_toLp, norm_toLp] at hle
  exact (norm_tsum_le_tsum_norm hsum).trans hle

/-- **The duality pairing as a bounded linear functional.** Each $\eta \in H^{-t}$ with coefficients
$b_m$ acts on $H^t$ by
$$\varphi \mapsto \sum_{m \in \mathbb{Z}} a_m \overline{b_m},$$
with norm at most $\|\eta\|$. -/
noncomputable def dualPairing (t : ℝ) (η : PeriodicSobolev (-t)) : PeriodicSobolev t →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∑' m : ℤ, coeff φ m * conj (coeff η m)
      map_add' := fun φ ρ => by
        rw [← (summable_coeff_mul_conj t φ η).tsum_add (summable_coeff_mul_conj t ρ η)]
        exact tsum_congr fun m => by simp [add_mul]
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun m => by simp [mul_assoc] }
    ‖η‖ fun φ => by
      rw [mul_comm]
      exact norm_tsum_coeff_mul_conj_le t φ η

/-- The functional of $\eta \in H^{-t}$ maps $\varphi$ to $\sum_m a_m \overline{b_m}$. -/
@[simp]
theorem dualPairing_apply (t : ℝ) (η : PeriodicSobolev (-t)) (φ : PeriodicSobolev t) :
    dualPairing t η φ = ∑' m : ℤ, coeff φ m * conj (coeff η m) := rfl

/-- The functional of $\eta \in H^{-t}$ on $H^t$ has norm at most $\|\eta\|$. With the Riesz
representation theorem, this makes $H^{-t}$ the dual of $H^t$. -/
theorem norm_dualPairing_le (t : ℝ) (η : PeriodicSobolev (-t)) : ‖dualPairing t η‖ ≤ ‖η‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg η) _

end PeriodicSobolev
