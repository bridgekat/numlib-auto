/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Logarithm
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Numlib.Analysis.Calculus.IteratedDeriv.Analytic
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic

/-!
# The primary functional calculus of analytic functions

This module treats power series, the exponential, the logarithm, derivatives along a ray,
composition, and the Taylor truncation bound for the primary functional calculus $f(a)$ = `pfc f a`
of `Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic`. Its main result is Theorem
9.1.2 of [golub2013matrix]: if $f(z) = \sum_k c_k (z - z_0)^k$ on a disc that contains the spectrum
of $a$, then $\sum_k c_k (a - z_0)^k = f(a)$. The truncation error of this series is bounded as in
Theorem 9.2.3 of [golub2013matrix]. The module also proves the composition rule
$(g \circ f)(a) = g(f(a))$ and that $\exp$ and $\log$ of the calculus agree with Mathlib's series.

## Main results

* `HasFPowerSeriesOnBall.hasSum_taylorJet`: inside the ball of convergence of a power series
  $\sum_k c_k (z - z_0)^k$, the Taylor coefficients at $z$ are the re-expanded series
  $\sum_k c_k \binom{k}{j} (z - z_0)^{k - j}$.
* `hasSum_pfc`: Theorem 9.1.2 of [golub2013matrix]. If $f$ has the power series
  $\sum_k c_k (z - z_0)^k$ on a ball that contains the spectrum of $a$, then
  $\sum_k c_k (a - z_0)^k = f(a)$; `tendsto_sum_pfc` is the form with partial sums.
* `pfc_exp_eq_normedSpace_exp`, `pfc_log_eq_normedSpace_log`: the calculus agrees with Mathlib's
  series exponential and logarithm.
* `hasFPowerSeriesOnBall_ofScalars_of_hasSum`, `Complex.hasFPowerSeriesOnBall_log_one`,
  `Complex.hasFPowerSeriesOnBall_log_one_sub`: scalar power series that serve as input to
  `hasSum_pfc`.
* `hasDerivAt_pfc_smul`: $\frac{d}{ds} f(sa) = a f'(sa)$.
* `pfc_comp`: the composition rule $(g \circ f)(a) = g(f(a))$ (Higham, *Functions of Matrices*,
  Theorem 1.17).
* `norm_pfc_sub_sum_le`: Theorem 9.2.3 of [golub2013matrix], the Taylor truncation bound.

## Proof outline

Everything is proved from the spectral decomposition `pfc_eq_sum_spectralIdempotent`: a statement
about $f(a)$ becomes finitely many statements about the scalar Taylor coefficients
$f^{(j)}(\lambda)/j!$, $j < m_\lambda$. The composition rule uses `iteratedDeriv_comp_congr` of
`Numlib.Analysis.Calculus.IteratedDeriv.Lemmas`: the derivatives of a composition depend only on the
derivatives of the factors, by the Faà di Bruno formula. The truncation bound is Taylor's formula
with integral remainder along $s \mapsto f(sa)$; the integral form, not the mean-value form, gives
the factor $1/(q + 1)!$ of the source.

## Implementation notes

* No norm on the algebra is needed for the statements on series: `HasSum` is taken in any
  topological algebra with continuous operations, for example `Matrix n n ℂ` with its product
  topology.
-/

open Polynomial Hermite Filter Topology
open scoped ENNReal Nat

section Series

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- **Taylor coefficients of a power series inside its ball.** Let $\mathbb{K}$ be a complete
nontrivially normed field of characteristic zero, and let $f : \mathbb{K} \to \mathbb{K}$ have
the power series $\sum_k c_k (z - z_0)^k$ on the ball of radius $r \in [0, \infty]$ about $z_0$.
Then at every $z$ of this ball and for every $j$,
$$\frac{f^{(j)}(z)}{j!} = \sum_k c_k \binom{k}{j} (z - z_0)^{k - j},$$
and the series converges.

Here $c_k$ is `p.coeff k`, and $k - j$ is the truncated subtraction of natural numbers; the
terms with $k < j$ vanish because $\binom{k}{j} = 0$. -/
theorem HasFPowerSeriesOnBall.hasSum_taylorJet [CharZero 𝕜] {f : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r)
    {z : 𝕜} (hz : z ∈ Metric.eball z₀ r) (j : ℕ) :
    HasSum (fun k => p.coeff k * ((k.choose j : 𝕜) * (z - z₀) ^ (k - j))) (taylorJet f z j) := by
  obtain ⟨q, hq, hcoeff⟩ := hf.exists_hasFPowerSeriesOnBall_iteratedDeriv j
  have hy : z - z₀ ∈ Metric.eball (0 : 𝕜) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hz
  have h := (hq.hasSum hy).div_const (j ! : 𝕜)
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff, add_sub_cancel,
    smul_eq_mul] at h
  have hj : (j ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  set F : ℕ → 𝕜 := fun k => p.coeff k * ((k.choose j : 𝕜) * (z - z₀) ^ (k - j))
  have hzero : ∑ i ∈ Finset.range j, F i = 0 := Finset.sum_eq_zero fun i hi => by
    simp [F, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  refine (hasSum_nat_add_iff' (f := F) (g := taylorJet f z j) j).mp ?_
  rw [hzero, sub_zero]
  convert h using 1
  · ext n
    simp only [F]
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.add_sub_cancel]
    push_cast
    field_simp
  · rfl

omit [CompleteSpace 𝕜] in
/-- Let $\mathbb{K}$ be a nontrivially normed field and $c : \mathbb{N} \to \mathbb{K}$. If
$\sum_k c_k z^k = f(z)$ for every $z \in \mathbb{K}$, then $f$ has the power series
$\sum_k c_k z^k$ on the ball of infinite radius about $0$. -/
theorem hasFPowerSeriesOnBall_ofScalars_of_hasSum {f : 𝕜 → 𝕜} {c : ℕ → 𝕜}
    (h : ∀ z, HasSum (fun k => c k * z ^ k) (f z)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕜 c) 0 ⊤ where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r _ => ?_
    obtain ⟨z, hz⟩ := NormedField.exists_lt_norm 𝕜 r
    have hlim := (h z).summable.tendsto_atTop_zero.norm
    simp only [norm_zero, norm_mul, norm_pow] at hlim
    refine le_trans (ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 hz.le : r ≤ ‖z‖₊)) ?_
    refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
    simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm] using hlim
  r_pos := ENNReal.zero_lt_top
  hasSum := fun {y} _ => by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h y

end Series

section HasSum

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
  [Ring A] [Algebra 𝕜 A]

omit [CompleteSpace 𝕜] in
/-- The Taylor coefficients of $(X - z_0)^k$ at $\lambda$ are
$\binom{k}{j} (\lambda - z_0)^{k - j}$. -/
private theorem taylorJet_sub_pow (z₀ l : 𝕜) (k j : ℕ) :
    taylorJet (fun z => ((X - C z₀) ^ k).eval z) l j = (k.choose j : 𝕜) * (l - z₀) ^ (k - j) := by
  rw [taylorJet_polynomial, taylor_pow, map_sub, taylor_X, taylor_C,
    show X + C l - C z₀ = X + C (l - z₀) by rw [map_sub]; ring, coeff_X_add_C_pow, mul_comm]

/-- **Power series of the primary functional calculus** (Theorem 9.1.2 of [golub2013matrix]). Let
$\mathbb{K}$ be a complete nontrivially normed field of characteristic zero, and let $A$ be a
topological $\mathbb{K}$-algebra with continuous addition, multiplication and scalar
multiplication. Let $f$ have the power series $\sum_k c_k (z - z_0)^k$ on the ball of radius $r$
about $z_0$, and let $a \in A$ be integral over $\mathbb{K}$, with a split minimal polynomial
and with spectrum in this ball. Then the series below converges in $A$, and
$$\sum_k c_k (a - z_0)^k = f(a).$$

Here $f(a)$ is `pfc f a`, and the convergence is `HasSum`, that is, unconditional convergence. -/
theorem hasSum_pfc [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul 𝕜 A] {f : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r)
    {a : A} (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (hσ : spectrum 𝕜 a ⊆ Metric.eball z₀ r) :
    HasSum (fun k => p.coeff k • (a - algebraMap 𝕜 A z₀) ^ k) (pfc f a) := by
  classical
  have hterm : ∀ k, p.coeff k • (a - algebraMap 𝕜 A z₀) ^ k =
      ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
        ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
          (p.coeff k * ((k.choose j : 𝕜) * (l - z₀) ^ (k - j))) •
            ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
    intro k
    have h1 : (a - algebraMap 𝕜 A z₀) ^ k = pfc (fun z => ((X - C z₀) ^ k).eval z) a := by
      rw [pfc_polynomial ha hs]
      simp
    rw [h1, pfc_eq_sum_spectralIdempotent ha hs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, taylorJet_sub_pow]
  simp_rw [hterm]
  rw [pfc_eq_sum_spectralIdempotent ha hs]
  refine hasSum_sum fun l hl => hasSum_sum fun j _ => ?_
  have hl' : l ∈ spectrum 𝕜 a := spectrum.mem_of_mem_roots_minpoly (Multiset.mem_toFinset.mp hl)
  exact (hf.hasSum_taylorJet (hσ hl') j).smul_const _

/-- The power series of the primary functional calculus with partial sums. Let $\mathbb{K}$ be a
complete nontrivially normed field of characteristic zero, and let $A$ be a topological
$\mathbb{K}$-algebra with continuous addition, multiplication and scalar multiplication. Let $f$
have the power series $\sum_k c_k (z - z_0)^k$ on the ball of radius $r$ about $z_0$, and let
$a \in A$ be integral over $\mathbb{K}$, with a split minimal polynomial and with spectrum in
this ball. Then
$$\sum_{k < N} c_k (a - z_0)^k \to f(a) \qquad (N \to \infty).$$
-/
theorem tendsto_sum_pfc [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul 𝕜 A]
    {f : 𝕜 → 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {a : A} (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) (hσ : spectrum 𝕜 a ⊆ Metric.eball z₀ r) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, p.coeff k • (a - algebraMap 𝕜 A z₀) ^ k) atTop
      (𝓝 (pfc f a)) :=
  (hasSum_pfc hf ha hs hσ).tendsto_sum_nat

end HasSum

section Complex

variable {A : Type*} [Ring A] [Algebra ℂ A] [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousSMul ℂ A] [T2Space A]

/-- **Agreement with Mathlib's exponential.** Let $A$ be a Hausdorff topological
$\mathbb{C}$-algebra with continuous addition, multiplication and scalar multiplication, and let
$a \in A$ be integral over $\mathbb{C}$. Then the primary functional calculus of the complex
exponential at $a$ is the exponential series `NormedSpace.exp a`.

No norm on $A$ is needed. The minimal polynomial splits because $\mathbb{C}$ is algebraically
closed. -/
theorem pfc_exp_eq_normedSpace_exp {a : A} (ha : IsIntegral ℂ a) :
    pfc Complex.exp a = NormedSpace.exp a := by
  have hf : HasFPowerSeriesOnBall Complex.exp
      (FormalMultilinearSeries.ofScalars ℂ fun n => (n ! : ℂ)⁻¹) 0 ⊤ := by
    rw [Complex.exp_eq_exp_ℂ, ← NormedSpace.expSeries_eq_ofScalars]
    exact NormedSpace.exp_hasFPowerSeriesOnBall
  have h := hasSum_pfc hf ha (IsAlgClosed.splits _) (by simp)
  simp only [FormalMultilinearSeries.coeff_ofScalars, map_zero, sub_zero] at h
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact h.tsum_eq.symm

/-- The power series of the complex logarithm at $1$: $\log z = \sum_{n \ge 1} \frac{(-1)^{n+1}}{n}
(z - 1)^n$ on the open disc of radius $1$ about $1$. The coefficient at $n = 0$ is $0$. -/
theorem Complex.hasFPowerSeriesOnBall_log_one :
    HasFPowerSeriesOnBall Complex.log
      (FormalMultilinearSeries.ofScalars ℂ fun n => ((-1) ^ (n + 1) / n : ℂ)) 1 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun n => ?_
    have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast (ENNReal.coe_lt_one_iff.mp hr).le
    calc ‖FormalMultilinearSeries.ofScalars ℂ (fun n => ((-1) ^ (n + 1) / n : ℂ)) n‖ * (r : ℝ) ^ n
        ≤ 1 * 1 := by
          gcongr
          · rw [FormalMultilinearSeries.ofScalars_norm]
            simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · simp
            · exact div_le_one_of_le₀ (by exact_mod_cast hn) (Nat.cast_nonneg _)
          · exact pow_le_one₀ r.2 hr1
      _ = 1 := one_mul 1
  r_pos := one_pos
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < 1 := by
      have : ‖y‖ₑ < 1 := by simpa [Metric.mem_eball, edist_zero_right] using hy
      rwa [← ofReal_norm, ENNReal.ofReal_lt_one] at this
    convert Complex.hasSum_taylorSeries_log hy' using 1
    · ext n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
      ring

/-- The power series of $z \mapsto \log(1 - z)$ at $0$: $\log(1 - z) = -\sum_{k \ge 1} z^k / k$ on
the open unit disc. The coefficient at $k = 0$ is $0$. -/
theorem Complex.hasFPowerSeriesOnBall_log_one_sub :
    HasFPowerSeriesOnBall (fun z => Complex.log (1 - z))
      (FormalMultilinearSeries.ofScalars ℂ fun k => -((k : ℂ)⁻¹)) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun k => ?_
    have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast (ENNReal.coe_lt_one_iff.mp hr).le
    calc ‖FormalMultilinearSeries.ofScalars ℂ (fun k => -((k : ℂ)⁻¹)) k‖ * (r : ℝ) ^ k
        ≤ 1 * 1 := by
          gcongr
          · rw [FormalMultilinearSeries.ofScalars_norm, norm_neg, norm_inv, Complex.norm_natCast]
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp
            · exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
          · exact pow_le_one₀ r.2 hr1
      _ = 1 := one_mul 1
  r_pos := one_pos
  hasSum := fun {y} hy => by
    have hy' : ‖y‖ < 1 := by
      have : ‖y‖ₑ < 1 := by simpa [Metric.mem_eball, edist_zero_right] using hy
      rwa [← ofReal_norm, ENNReal.ofReal_lt_one] at this
    convert (Complex.hasSum_taylorSeries_neg_log hy').neg using 1
    · ext k
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      ring
    · simp

/-- **Agreement with Mathlib's logarithm series near $1$.** Let $A$ be a Hausdorff topological
$\mathbb{C}$-algebra with continuous addition, multiplication and scalar multiplication, and let
$a \in A$ be integral over $\mathbb{C}$. If every $\mu$ in the spectrum of $a$ satisfies
$|\mu - 1| < 1$, then the primary functional calculus of the principal complex logarithm at $a$
is the series `NormedSpace.log a`, that is, $\sum_{n \ge 1} \frac{(-1)^{n+1}}{n} (a - 1)^n$. -/
theorem pfc_log_eq_normedSpace_log {a : A} (ha : IsIntegral ℂ a)
    (hσ : ∀ μ ∈ spectrum ℂ a, ‖μ - 1‖ < 1) :
    pfc Complex.log a = NormedSpace.log a := by
  have h := hasSum_pfc Complex.hasFPowerSeriesOnBall_log_one ha (IsAlgClosed.splits _)
    fun μ hμ => by
      rw [Metric.mem_eball, edist_eq_enorm_sub, ← ofReal_norm, ENNReal.ofReal_lt_one]
      exact hσ μ hμ
  simp only [FormalMultilinearSeries.coeff_ofScalars, map_one] at h
  rw [NormedSpace.log_eq_tsum ℂ]
  exact h.tsum_eq.symm

end Complex

section Derivative

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The derivative of the coefficient $s \mapsto s^j f^{(j)}(s\lambda)/j!$ of `pfc_smul`. -/
private theorem hasDerivAt_coeff_smul {f : 𝕜 → 𝕜} {t l : 𝕜} (hf : AnalyticAt 𝕜 f (t * l))
    (j : ℕ) :
    HasDerivAt (fun s : 𝕜 => s ^ j * taylorJet f (s * l) j)
      ((j : 𝕜) * t ^ (j - 1) * taylorJet f (t * l) j +
        t ^ j * (l * (iteratedDeriv (j + 1) f (t * l) / (j ! : 𝕜)))) t := by
  have h1 : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f (t * l)) (t * l) := by
    have hd : DifferentiableAt 𝕜 (iteratedDeriv j f) (t * l) := by
      rw [iteratedDeriv_eq_iterate]
      exact (hf.iterated_deriv j).differentiableAt
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt
  have h2 : HasDerivAt (fun s => taylorJet f (s * l) j)
      (iteratedDeriv (j + 1) f (t * l) * l / (j ! : 𝕜)) t := by
    have := HasDerivAt.div_const (HasDerivAt.comp t h1 (hasDerivAt_mul_const l)) (j ! : 𝕜)
    simpa [taylorJet, Function.comp_def] using this
  have h3 := HasDerivAt.mul (hasDerivAt_pow j t) h2
  convert h3 using 1
  ring

/-- **The derivative along a ray.** Let $\mathbb{K}$ be a complete nontrivially normed field of
characteristic zero, let $A$ be a normed $\mathbb{K}$-algebra, let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial, and let $t \in \mathbb{K}$. If $f$ is analytic at
$t\mu$ for every $\mu$ in the spectrum of $a$, then $s \mapsto f(sa)$ is differentiable at
$s = t$, with
$$\frac{d}{ds} f(sa) \Big|_{s = t} = a\, f'(ta).$$
The case $t = 0$ is included.

Here $f'(ta)$ is the primary functional calculus of `deriv f` at $ta$. -/
theorem hasDerivAt_pfc_smul {a : A} (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    {f : 𝕜 → 𝕜} {t : 𝕜} (hf : ∀ μ ∈ spectrum 𝕜 a, AnalyticAt 𝕜 f (t * μ)) :
    HasDerivAt (fun s : 𝕜 => pfc f (s • a)) (a * pfc (deriv f) (t • a)) t := by
  classical
  have hroot : ∀ l ∈ (minpoly 𝕜 a).roots.toFinset, l ∈ spectrum 𝕜 a := fun l hl =>
    spectrum.mem_of_mem_roots_minpoly (Multiset.mem_toFinset.mp hl)
  rw [show (fun s : 𝕜 => pfc f (s • a)) = fun s => ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        (s ^ j * taylorJet f (s * l) j) •
          ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) from
    funext fun s => pfc_smul ha hs s f]
  refine (HasDerivAt.fun_sum fun l hl => HasDerivAt.fun_sum fun j _ =>
    HasDerivAt.smul_const (hasDerivAt_coeff_smul (hf l (hroot l hl)) j)
      ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l)).congr_deriv ?_
  rw [pfc_smul ha hs t (deriv f), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  -- the coefficients of `a f'(t a)` on the basis `(a - l)ʲ E_l`
  have haX : ∀ j, a * ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) =
      l • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) +
        (a - algebraMap 𝕜 A l) ^ (j + 1) * spectralIdempotent a l := fun j => by
    rw [show a * ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) =
        (algebraMap 𝕜 A l + (a - algebraMap 𝕜 A l)) *
          ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) by rw [add_sub_cancel],
      add_mul, ← mul_assoc (a - _), ← pow_succ', Algebra.smul_def]
  set g : ℕ → A := fun j => ((j : 𝕜) * t ^ (j - 1) * taylorJet f (t * l) j) •
    ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l)
  have hshift : ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l), g j =
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        (t ^ j * taylorJet (deriv f) (t * l) j) •
          ((a - algebraMap 𝕜 A l) ^ (j + 1) * spectralIdempotent a l) := by
    have e1 := Finset.sum_range_succ' g ((minpoly 𝕜 a).rootMultiplicity l)
    have e2 := Finset.sum_range_succ g ((minpoly 𝕜 a).rootMultiplicity l)
    have hg0 : g 0 = 0 := by simp [g]
    have hgm : g ((minpoly 𝕜 a).rootMultiplicity l) = 0 := by
      simp only [g, pow_mul_spectralIdempotent ha hs l, smul_zero]
    rw [hgm, add_zero] at e2
    rw [hg0, add_zero, e2] at e1
    rw [e1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, taylorJet, Nat.add_sub_cancel, Nat.factorial_succ, ← iteratedDeriv_succ']
    congr 1
    push_cast
    field_simp
  rw [show ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
      ((j : 𝕜) * t ^ (j - 1) * taylorJet f (t * l) j +
        t ^ j * (l * (iteratedDeriv (j + 1) f (t * l) / (j ! : 𝕜)))) •
          ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) =
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l), g j +
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        ((t ^ j * taylorJet (deriv f) (t * l) j) * l) •
          ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, ← add_smul, taylorJet, ← iteratedDeriv_succ']
    congr 1
    ring, hshift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, haX, smul_add, smul_smul, add_comm]

end Derivative

/-! ### Composition -/

section Composition

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [Ring A] [Algebra 𝕜 A]

/-- **The composition rule** (Higham, *Functions of Matrices*, Theorem 1.17). Let $\mathbb{K}$ be a
nontrivially normed field of characteristic zero, and let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial. Let $f$ be $C^{m_\lambda - 1}$ on the spectrum of
$a$ (`ContDiffOnSpectrum`), and let $g$ be $C^{m_\lambda - 1}$ at $f(\lambda)$ for every root
$\lambda$ of the minimal polynomial of $a$, where $m_\lambda$ is the multiplicity of $\lambda$.
Then
$$(g \circ f)(a) = g(f(a)).$$

The minimal polynomial of $f(a)$ divides $\prod_\lambda (X - f(\lambda))^{m_\lambda}$. If $P$
and $G$ are interpolants of $f$ and $g$, the derivatives of $G \circ P$ at the eigenvalues are
those of $g \circ f$ (`iteratedDeriv_comp_congr`). -/
theorem pfc_comp {a : A} (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) {f g : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) g (f μ)) :
    pfc (g ∘ f) a = pfc g (pfc f a) := by
  classical
  set R := (minpoly 𝕜 a).roots
  set P := interpolateJet R (taylorJet f)
  have hP := isJetInterpolant_interpolateJet R (taylorJet f)
  have hPd := isJetInterpolant_taylorJet_iff.mp hP
  have hPeval : ∀ l ∈ R, P.eval l = f l := fun l hl => by
    simpa using hPd l hl 0 (Multiset.count_pos.mpr hl)
  have hb : pfc f a = aeval a P := by rw [pfc_def]
  set S := R.map f
  -- the minimal polynomial of `f(a)` divides the nodal polynomial of `S`
  have hdvd : minpoly 𝕜 (pfc f a) ∣ nodalMultiset S := by
    refine minpoly.dvd 𝕜 _ ?_
    rw [hb, ← aeval_comp, nodalMultiset, multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    have hR : nodalMultiset R ∣ (R.map fun l => (X - C (f l)).comp P).prod := by
      rw [nodalMultiset]
      refine Multiset.prod_dvd_prod_of_dvd _ _ fun l hl => ?_
      rw [sub_comp, X_comp, C_comp, ← hPeval l hl]
      exact X_sub_C_dvd_sub_C_eval
    obtain ⟨r, hr⟩ := (minpoly_dvd_nodalMultiset_roots ha hs).trans hR
    simp only [Function.comp_def]
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  set G := interpolateJet S (taylorJet g)
  have hG := isJetInterpolant_taylorJet_iff.mp (isJetInterpolant_interpolateJet S (taylorJet g))
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd (isJetInterpolant_interpolateJet S (taylorJet g)),
    hb, ← aeval_comp]
  refine pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_roots ha hs)
    (isJetInterpolant_taylorJet_iff.mpr fun l hl j hj => ?_)
  replace hj : j < R.count l := hj
  have hcount : R.count l ≤ S.count (f l) := by
    rw [Multiset.count_eq_card_filter_eq, Multiset.count_map]
    exact Multiset.card_le_card (Multiset.monotone_filter_right R fun x hx => by rw [hx])
  have hm : R.count l = (minpoly 𝕜 a).rootMultiplicity l := count_roots _
  have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ((minpoly 𝕜 a).rootMultiplicity l - 1 : ℕ) := by
    exact_mod_cast (by omega : j ≤ _)
  refine (show ((derivative^[j]) (G.comp P)).eval l =
      iteratedDeriv j (fun z => (G.comp P).eval z) l by rw [iteratedDeriv_eval]).trans ?_
  have hcomp : (fun z => (G.comp P).eval z) = (fun z => G.eval z) ∘ fun z => P.eval z := by
    ext z
    simp
  rw [hcomp]
  have hpoly : ∀ (Q : 𝕜[X]) (n : WithTop ℕ∞), ContDiff 𝕜 n fun z => Q.eval z := fun Q n => by
    simpa [coe_aeval_eq_eval] using Q.contDiff_aeval (𝕜 := 𝕜) n
  refine iteratedDeriv_comp_congr (hpoly P _).contDiffAt ((hf l hl).of_le hj')
    (hpoly G _).contDiffAt ?_ (fun k hk => ?_) (fun k hk => ?_)
  · rw [hPeval l hl]
    exact (hg l hl).of_le hj'
  · rw [iteratedDeriv_eval]
    exact hPd l hl k (by omega)
  · rw [hPeval l hl, iteratedDeriv_eval]
    exact hG (f l) (Multiset.mem_map_of_mem f hl) k (by omega)

end Composition

/-! ### The Taylor truncation bound -/

section TaylorBound

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Let $\mathbb{K}$ be a nontrivially normed field, let $B$ be a $\mathbb{K}$-algebra, and let
$a \in B$ be integral over $\mathbb{K}$ with a split minimal polynomial. For every
$g : \mathbb{K} \to \mathbb{K}$, the primary functional calculus of $g$ at $0 \cdot a$ is
$g(0) \cdot 1$. -/
theorem pfc_zero_smul {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [Ring B] [Algebra 𝕜 B] {a : B}
    (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (g : 𝕜 → 𝕜) :
    pfc g ((0 : 𝕜) • a) = algebraMap 𝕜 B (g 0) := by
  classical
  rw [pfc_smul ha hs, ← mul_one (algebraMap 𝕜 B (g 0)), ← sum_spectralIdempotent ha hs,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hm : 0 < (minpoly 𝕜 a).rootMultiplicity l := by
    rw [← count_roots]
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hl)
  rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [zero_pow hj]) (by simp [hm])]
  simp [Algebra.smul_def]

/-- The $k$-th derivative $a^k f^{(k)}(ta)$ of $t \mapsto f(ta)$ along the real segment. -/
private noncomputable def rayDeriv (f : ℂ → ℂ) (a : A) (k : ℕ) (t : ℝ) : A :=
  a ^ k * pfc (iteratedDeriv k f) ((t : ℂ) • a)

omit [CompleteSpace A] in
private theorem hasDerivAt_rayDeriv {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 r) {a : A} (ha : IsIntegral ℂ a)
    (hσ : spectrum ℂ a ⊆ Metric.eball 0 r) (k : ℕ) {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    HasDerivAt (rayDeriv f a k) (rayDeriv f a (k + 1) t) t := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  have han : ∀ μ ∈ spectrum ℂ a, AnalyticAt ℂ (iteratedDeriv k f) ((t : ℂ) * μ) := by
    intro μ hμ
    rw [iteratedDeriv_eq_iterate]
    refine AnalyticAt.iterated_deriv (hf.analyticAt_of_mem ?_) k
    have h := hσ hμ
    simp only [Metric.mem_eball, edist_zero_right] at h ⊢
    refine lt_of_le_of_lt ?_ h
    rw [enorm_mul]
    calc ‖(t : ℂ)‖ₑ * ‖μ‖ₑ ≤ 1 * ‖μ‖ₑ := by
          gcongr
          rw [← ofReal_norm, ENNReal.ofReal_le_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ht.1]
          exact ht.2
      _ = ‖μ‖ₑ := one_mul _
  have h := (hasDerivAt_pfc_smul ha (IsAlgClosed.splits _) han).scomp t
    Complex.ofRealCLM.hasDerivAt
  simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h
  have h2 := h.const_mul (a ^ k)
  rw [← mul_assoc, ← pow_succ, ← iteratedDeriv_succ] at h2
  exact h2

omit [CompleteSpace A] in
private theorem continuousOn_rayDeriv {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 r) {a : A} (ha : IsIntegral ℂ a)
    (hσ : spectrum ℂ a ⊆ Metric.eball 0 r) (k : ℕ) :
    ContinuousOn (rayDeriv f a k) (Set.uIcc 0 1) := fun _ ht =>
  (hasDerivAt_rayDeriv hf ha hσ k ht).continuousAt.continuousWithinAt

/-- Taylor's formula with integral remainder for $t \mapsto f(ta)$ on $[0, 1]$. -/
private theorem rayDeriv_taylor {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 r) {a : A} (ha : IsIntegral ℂ a)
    (hσ : spectrum ℂ a ⊆ Metric.eball 0 r) (q : ℕ) :
    rayDeriv f a 0 1 - ∑ k ∈ Finset.range (q + 1), ((k ! : ℝ)⁻¹) • rayDeriv f a k 0 =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ q / q ! : ℝ) • rayDeriv f a (q + 1) t := by
  induction q with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, pow_zero, div_one]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_rayDeriv hf ha hσ 0 ht)
      ((continuousOn_rayDeriv hf ha hσ 1).intervalIntegrable)]
  | succ q ih =>
    have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (1 - t) ^ (q + 1) / (q + 1)! )
        (-((1 - t) ^ q / q !)) t := by
      intro t _
      have := ((hasDerivAt_pow (q + 1) (1 - t)).comp t
        ((hasDerivAt_id t).const_sub 1)).div_const ((q + 1)! : ℝ)
      refine this.congr_deriv ?_
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu
      (fun t ht => hasDerivAt_rayDeriv hf ha hσ (q + 1) ht)
      ((by fun_prop : Continuous fun t : ℝ => -((1 - t) ^ q / q !)).intervalIntegrable _ _)
      ((continuousOn_rayDeriv hf ha hσ (q + 2)).intervalIntegrable)
    simp only [sub_self, zero_pow (Nat.succ_ne_zero q), zero_div, zero_smul, sub_zero, one_pow,
      neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add] at hparts
    rw [Finset.sum_range_succ, ← sub_sub, ih, hparts]
    simp only [one_div]
    abel_nf

/-- **The Taylor truncation bound** (Theorem 9.2.3 of [golub2013matrix]). Let $A$ be a complex
Banach algebra, let $f$ have the power series $\sum_k \alpha_k z^k$ on the ball of radius $r$
about $0$, and let $a \in A$ be integral over $\mathbb{C}$ with spectrum in this ball. Let
$q \in \mathbb{N}$ and $M \in \mathbb{R}$, and suppose that
$$\|a^{q+1} f^{(q+1)}(sa)\| \le M \qquad \text{for all } s \in [0, 1].$$
Then
$$\Big\| f(a) - \sum_{k=0}^{q} \alpha_k a^k \Big\| \le \frac{M}{(q + 1)!}.$$

The bound of the source for matrices of order $n$ has an additional factor $n$; the bound here
has no such factor. The proof is Taylor's formula with integral remainder for $s \mapsto f(sa)$,
whose derivatives are $a^k f^{(k)}(sa)$ (`hasDerivAt_pfc_smul`). Here $f^{(q+1)}(sa)$ is the
primary functional calculus of `iteratedDeriv (q + 1) f` at $sa$. -/
theorem norm_pfc_sub_sum_le {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) {a : A} (ha : IsIntegral ℂ a)
    (hσ : spectrum ℂ a ⊆ Metric.eball 0 r) (q : ℕ) {M : ℝ}
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖a ^ (q + 1) * pfc (iteratedDeriv (q + 1) f) ((s : ℂ) • a)‖ ≤ M) :
    ‖pfc f a - ∑ k ∈ Finset.range (q + 1), p.coeff k • a ^ k‖ ≤ M / (q + 1)! := by
  have hs := IsAlgClosed.splits (minpoly ℂ a)
  have h1 : rayDeriv f a 0 1 = pfc f a := by simp [rayDeriv]
  have hcoeff : ∀ k, ((k ! : ℝ)⁻¹) • rayDeriv f a k 0 = p.coeff k • a ^ k := by
    intro k
    have hjet : taylorJet f 0 k = p.coeff k := by
      have h := hf.hasSum_taylorJet (z := 0) (by simpa using hf.r_pos) k
      refine h.unique ?_
      convert hasSum_single k (fun n hn => ?_) using 1
      · simp
      · rcases lt_or_gt_of_ne hn with h' | h'
        · simp [Nat.choose_eq_zero_of_lt h']
        · simp [(Nat.sub_pos_of_lt h').ne']
    simp only [rayDeriv, Complex.ofReal_zero, pfc_zero_smul ha hs]
    rw [← hjet, taylorJet, ← Algebra.commutes, ← Algebra.smul_def,
      ← algebraMap_smul ℂ ((k ! : ℝ)⁻¹), smul_smul]
    congr 1
    simp [div_eq_inv_mul]
  rw [← h1, show ∑ k ∈ Finset.range (q + 1), p.coeff k • a ^ k =
    ∑ k ∈ Finset.range (q + 1), ((k ! : ℝ)⁻¹) • rayDeriv f a k 0 from
    Finset.sum_congr rfl fun k _ => (hcoeff k).symm, rayDeriv_taylor hf ha hσ q]
  have hint : ∫ t in (0 : ℝ)..1, ((1 - t) ^ q / q ! : ℝ) * M = M / (q + 1)! := by
    have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => -((1 - t) ^ (q + 1) / (q + 1)! * M))
          ((1 - t) ^ q / q ! * M) t := by
      intro t _
      have := (((hasDerivAt_pow (q + 1) (1 - t)).comp t
        ((hasDerivAt_id t).const_sub 1)).div_const ((q + 1)! : ℝ) |>.mul_const M).neg
      refine this.congr_deriv ?_
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hu
      ((by fun_prop : Continuous fun t : ℝ => (1 - t) ^ q / q ! * M).intervalIntegrable _ _)]
    simp
    ring
  rw [← hint]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
    (intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun t ht => ?_)
  · exact ((by fun_prop : Continuous fun t : ℝ => ((1 - t) ^ q / q ! : ℝ)).continuousOn.smul
      (continuousOn_rayDeriv hf ha hσ (q + 1))).norm.intervalIntegrable
  · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) ^ q / q ! * M).intervalIntegrable _ _
  · have h0 : 0 ≤ (1 - t) ^ q / q ! := div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) q)
      (Nat.cast_nonneg _)
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hM t ht) h0

end TaylorBound
