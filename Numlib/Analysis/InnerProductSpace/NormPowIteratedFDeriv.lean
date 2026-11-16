/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Derivatives of all orders of a power of the norm

Let $E$ be a real inner product space and let $\lambda$ be a real number. This module studies the
derivatives $D^j(\|\cdot\|^\lambda)$ of the function $x \mapsto \|x\|^\lambda$, everywhere including
the origin, with sharp bounds on their operator norms. Write
$$\pi_j(\lambda) = \lambda (\lambda - 1) \cdots (\lambda - j + 1) = \prod_{i < j} (\lambda - i).$$
The main result is (B.4.1) of Lemma B.4.1 of [cartis2022evaluation]: for $j \le \lambda$ and
$x \neq 0$, the operator norm of $D^j(\|\cdot\|^\lambda)(x)$ is
$\pi_j(\lambda) \|x\|^{\lambda - j}$, and the bound $\le$ holds also at $x = 0$ when $j < \lambda$.
The functions $\|s\|^{p+1}$ and $\|s\|^{p+\beta}$ are the regularization terms of adaptive
regularization models, such as $\sigma / (p+1)! \, \|s\|^{p+1}$.

For real exponents the module proves an averaging identity on a finite-dimensional space, an
integral formula for the derivatives, the operator-norm bound and its equality case, smoothness of
class $C^j$ for $j < \lambda$ with vanishing derivatives at the origin, the radial values (B.4.2),
and the convexity statements of Lemma B.4.1. For natural exponents $r$, the form in which
regularized models are written, it proves that $\|s\|^r$ is of class $C^{r-1}$, that
$D^\ell(\|\cdot\|^r)(s)$ has operator norm at most $r! / (r - \ell)! \, \|s\|^{r - \ell}$, that
$D^{r-1}(\|\cdot\|^r)$ is $r!$-Lipschitz, and the Taylor remainder bound
$|\|s + d\|^r - T_{r-1}(s, d)| \le \|d\|^r$.

## Main results

* `exists_integral_abs_inner_rpow_eq`: on a finite-dimensional space, $\int_{\|\omega\| < 1}
  |\langle y, \omega \rangle|^\lambda \, d\omega = \kappa \|y\|^\lambda$ for a constant
  $\kappa > 0$.
* `iteratedFDeriv_normRpow_eq_integral`: for $j \le \lambda$,
  $D^j(\|\cdot\|^\lambda)(x)[v_1, \dots, v_j]$ is $\pi_j(\lambda) / \kappa$ times the integral over
  the unit ball of $|\langle x, \omega \rangle|^{\lambda - j} \operatorname{sign}(\langle x, \omega
  \rangle)^j \prod_i \langle v_i, \omega \rangle$.
* `norm_iteratedFDeriv_normRpow_le`, `norm_iteratedFDeriv_normRpow`: (B.4.1),
  $\|D^j(\|\cdot\|^\lambda)(x)\| \le \pi_j(\lambda) \|x\|^{\lambda - j}$ for $j \le \lambda$, with
  equality for $x \neq 0$, on any real inner product space.
* `contDiff_normRpow_of_lt`, `iteratedFDeriv_normRpow_zero`: $\|\cdot\|^\lambda$ is of class $C^j$
  for $j < \lambda$, and its derivatives of these orders vanish at the origin.
* `iteratedFDeriv_normRpow_apply_self`: (B.4.2), the radial values $D^j(\|\cdot\|^\lambda)(x)[x]^j =
  \pi_j(\lambda) \|x\|^\lambda$.
* `not_norm_iteratedFDeriv_normRpow_eq_radial`: for $p = 1$ and $\beta = 1/2$, the operator norm of
  $D^{p+1}(\|\cdot\|^{p+\beta})(x)$ at a unit vector $x$ of $\mathbb{R}^2$ exceeds the radial value
  $\beta (p + \beta)! \, \|x\|^{\beta - 1}$.
* `convexOn_iteratedFDeriv_normRpow`: the convexity statements of Lemma B.4.1.
* `contDiff_norm_pow`, `contDiff_norm_pow_of_even`, `contDiffAt_norm_pow`: $\|\cdot\|^r$ is of class
  $C^{r-1}$, analytic for even $r$, and analytic away from the origin.
* `iteratedFDeriv_norm_pow_apply_self`, `norm_iteratedFDeriv_norm_pow_le`,
  `norm_iteratedFDeriv_norm_pow`, `abs_iteratedFDeriv_norm_pow_apply_le`:
  $\|D^\ell(\|\cdot\|^r)(s)\| \le r! / (r - \ell)! \, \|s\|^{r - \ell}$ for $\ell \le r$, with the
  equality cases.
* `iteratedFDerivLipschitzOn_norm_pow`: $D^{r-1}(\|\cdot\|^r)$ is $r!$-Lipschitz, which is (B.4.3)
  for $\beta = 1$.
* `abs_norm_pow_sub_taylorPolynomial_le`: $|\|s + d\|^r - T_{r-1}(s, d)| \le \|d\|^r$.

## Proof outline

The operator norm in (B.4.1) does not follow from a maximization in the radial direction, because
the terms of (B.4.9) have mixed signs. Instead, on a finite-dimensional space, the rotation
invariance of Lebesgue measure on the unit ball gives $\|y\|^\lambda = \kappa^{-1} \int_{\|\omega\|
< 1} |\langle y, \omega \rangle|^\lambda \, d\omega$. Differentiation $j \le \lambda$ times under
the integral sign gives the integral formula: at each step the integrand is Lipschitz in $y$,
because the current exponent is at least $1$, and it is differentiable off a null hyperplane. The
weighted inequality of arithmetic and geometric means with the weights $(\lambda - j)/\lambda,
1/\lambda, \dots, 1/\lambda$, integrated over the ball, then gives the operator-norm bound with the
sharp constant $\pi_j(\lambda)$. So no result on symmetric multilinear forms, such as Banach's
theorem, is needed. A general inner product space reduces to the finite-dimensional span of the
point and the arguments. Smoothness at the origin follows from the bound, with an explicit Taylor
series.

## Implementation notes

* The number $\pi_j(\lambda)$ is written `∏ i ∈ Finset.range j, (lam - i)` in the statements.
* The power $\|x\|^\lambda$ for real $\lambda$ is `Real.rpow`, with $0^0 = 1$ and $0^\lambda = 0$
  for $\lambda \neq 0$. The power $\|s\|^r$ for natural $r$ is the monoid power.
* The generalized factorial $(k + \beta)!$ is `holderFactorial k β`.
* Integrals are with respect to the Lebesgue measure `volume` of a finite-dimensional real inner
  product space, over the open unit ball `Metric.ball 0 1`.
* The reduction to a finite-dimensional subspace is `Submodule.iteratedFDeriv_comp_subtypeL_apply`,
  and the Taylor series at the origin is `NormPowIteratedFDeriv.taylorNormRpow` with
  `NormPowIteratedFDeriv.hasFTaylorSeriesUpTo_normRpow`.
-/

open Filter Metric MeasureTheory Module Set Topology
open scoped Nat RealInnerProductSpace

namespace NormPowIteratedFDeriv

/-- The signed power $\operatorname{sgnPow}_{a,k}(u) = |u|^a \operatorname{sign}(u)^k$ for
$a \in \mathbb{R}$, $k \in \mathbb{N}$ and $u \in \mathbb{R}$. It is the profile in one variable
of the derivatives of $\|\cdot\|^\lambda$. -/
noncomputable def sgnPow (a : ℝ) (k : ℕ) (u : ℝ) : ℝ := |u| ^ a * (SignType.sign u : ℝ) ^ k

/-- The definition of the signed power: $\operatorname{sgnPow}_{a,k}(u) = |u|^a
\operatorname{sign}(u)^k$. -/
theorem sgnPow_def (a : ℝ) (k : ℕ) (u : ℝ) : sgnPow a k u = |u| ^ a * (SignType.sign u : ℝ) ^ k :=
  rfl

/-- A power of a sign has absolute value at most $1$: $|\operatorname{sign}(u)^k| \le 1$. -/
theorem abs_sign_pow_le (k : ℕ) (u : ℝ) : |(SignType.sign u : ℝ) ^ k| ≤ 1 := by
  rw [abs_pow]
  refine pow_le_one₀ (abs_nonneg _) ?_
  rcases lt_trichotomy u 0 with h | h | h <;> simp [sign_neg, sign_pos, h]

/-- The signed power is bounded by the power: $|\operatorname{sgnPow}_{a,k}(u)| \le |u|^a$. -/
theorem abs_sgnPow_le (a : ℝ) (k : ℕ) (u : ℝ) : |sgnPow a k u| ≤ |u| ^ a := by
  rw [sgnPow, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) a)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg u) a) (abs_sign_pow_le k u)

/-- The sign function $\mathbb{R} \to \mathbb{R}$ is measurable, because it is monotone. -/
theorem measurable_sign_real : Measurable fun u : ℝ ↦ (SignType.sign u : ℝ) := by
  refine Monotone.measurable fun u v huv ↦ ?_
  rcases lt_trichotomy u 0 with hu | hu | hu <;> rcases lt_trichotomy v 0 with hv | hv | hv <;>
    simp [sign_neg, sign_pos, hu, hv] <;> linarith

/-- The signed power $u \mapsto |u|^a \operatorname{sign}(u)^k$ is measurable. -/
theorem measurable_sgnPow (a : ℝ) (k : ℕ) : Measurable (sgnPow a k) :=
  (continuous_abs.measurable.pow_const a).mul (measurable_sign_real.pow_const k)

/-- At every $u \neq 0$, the signed power has the derivative
$$\frac{d}{du} \big( |u|^a \operatorname{sign}(u)^k \big) = a \, |u|^{a-1}
  \operatorname{sign}(u)^{k+1}.$$
-/
theorem hasDerivAt_sgnPow (a : ℝ) (k : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (sgnPow a k) (a * sgnPow (a - 1) (k + 1) u) u := by
  rcases hu.lt_or_gt with hu | hu
  · have hev : sgnPow a k =ᶠ[𝓝 u] fun t ↦ (-t) ^ a * (-1) ^ k := by
      filter_upwards [Iio_mem_nhds hu] with t ht
      simp [sgnPow, sign_neg (show t < 0 from ht), abs_of_neg (show t < 0 from ht)]
    have h := (((hasDerivAt_id u).neg).rpow_const (p := a) (Or.inl (by simp; linarith))).mul_const
      ((-1 : ℝ) ^ k)
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [sgnPow, sign_neg hu, abs_of_neg hu, SignType.coe_neg, SignType.coe_one, Pi.neg_apply,
      id_eq]
    ring
  · have hev : sgnPow a k =ᶠ[𝓝 u] fun t ↦ t ^ a := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      simp [sgnPow, sign_pos (show 0 < t from ht), abs_of_pos (show 0 < t from ht)]
    refine ((Real.hasDerivAt_rpow_const (Or.inl hu.ne')).congr_of_eventuallyEq hev).congr_deriv ?_
    simp [sgnPow, sign_pos hu, abs_of_pos hu]

/-- For $a > 0$, the signed power $u \mapsto |u|^a \operatorname{sign}(u)^k$ is continuous, also at
$0$, where it vanishes. -/
theorem continuous_sgnPow {a : ℝ} (ha : 0 < a) (k : ℕ) : Continuous (sgnPow a k) := by
  refine continuous_iff_continuousAt.2 fun u ↦ ?_
  rcases eq_or_ne u 0 with rfl | hu
  · have h0 : sgnPow a k 0 = 0 := by simp [sgnPow, Real.zero_rpow ha.ne']
    rw [ContinuousAt, h0]
    exact squeeze_zero_norm (a := fun t ↦ |t| ^ a) (fun t ↦ abs_sgnPow_le a k t) (by
      simpa [Real.zero_rpow ha.ne'] using
        ((continuous_abs.rpow_const fun _ ↦ Or.inr ha.le).tendsto (0 : ℝ)))
  · exact (hasDerivAt_sgnPow a k hu).continuousAt

/-- A mean value inequality on $[-R, R]$ for a function differentiable off $0$. Let
$g \colon \mathbb{R} \to \mathbb{R}$ be continuous, with derivative $g'(t)$ at every $t \neq 0$,
and let $|g'(t)| \le L$ for all $t \neq 0$ with $|t| \le R$. Then $|g(u) - g(v)| \le L |u - v|$
for all $u, v$ with $|u|, |v| \le R$. -/
theorem abs_sub_le_of_hasDerivAt_ne_zero {g g' : ℝ → ℝ} (hc : Continuous g)
    (hd : ∀ t ≠ 0, HasDerivAt g (g' t) t) {L R : ℝ} (hb : ∀ t, t ≠ 0 → |t| ≤ R → |g' t| ≤ L)
    {u v : ℝ} (hu : |u| ≤ R) (hv : |v| ≤ R) : |g u - g v| ≤ L * |u - v| := by
  -- the case of an interval not containing `0` in its interior
  have key : ∀ u v : ℝ, |u| ≤ R → |v| ≤ R → v ≤ u → (0 ≤ v ∨ u ≤ 0) →
      |g u - g v| ≤ L * |u - v| := by
    intro u v hu hv hvu h0
    rcases hvu.eq_or_lt with rfl | hvu
    · simp
    obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope g g' hvu hc.continuousOn
      fun x hx ↦ hd x (by rcases h0 with h0 | h0 <;> [linarith [hx.1]; linarith [hx.2]])
    have hc0 : c ≠ 0 := by rcases h0 with h0 | h0 <;> [linarith [hc'.1]; linarith [hc'.2]]
    have hcR : |c| ≤ R := abs_le.2 ⟨by linarith [(abs_le.1 hv).1, hc'.1],
      by linarith [(abs_le.1 hu).2, hc'.2]⟩
    have hpos : 0 < u - v := sub_pos.2 hvu
    rw [eq_div_iff hpos.ne'] at hcd
    rw [← hcd, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hb c hc0 hcR) hpos.le
  -- reduce to `v ≤ u`, then split at `0`
  wlog hvu : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (le_of_not_ge hvu)
  by_cases h0 : 0 ≤ v ∨ u ≤ 0
  · exact key u v hu hv hvu h0
  push Not at h0
  have h0R : |(0 : ℝ)| ≤ R := by rw [abs_zero]; exact (abs_nonneg _).trans hu
  calc |g u - g v| ≤ |g u - g 0| + |g 0 - g v| := abs_sub_le _ _ _
    _ ≤ L * |u - 0| + L * |0 - v| :=
        add_le_add (key u 0 hu h0R h0.2.le (Or.inl le_rfl)) (key 0 v h0R hv h0.1.le (Or.inr le_rfl))
    _ = L * |u - v| := by
        rw [sub_zero, zero_sub, abs_neg, abs_of_pos h0.2, abs_of_neg h0.1,
          abs_of_pos (by linarith)]
        ring

/-- For $a \ge 1$, the signed power is $a R^{a-1}$-Lipschitz on $[-R, R]$: if $|u|, |v| \le R$, then
$$\big| |u|^a \operatorname{sign}(u)^k - |v|^a \operatorname{sign}(v)^k \big| \le a R^{a-1} |u -
  v|.$$
-/
theorem abs_sgnPow_sub_le {a : ℝ} (ha : 1 ≤ a) (k : ℕ) {R u v : ℝ} (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |sgnPow a k u - sgnPow a k v| ≤ a * R ^ (a - 1) * |u - v| := by
  refine abs_sub_le_of_hasDerivAt_ne_zero (continuous_sgnPow (by linarith) k)
    (fun t ht ↦ hasDerivAt_sgnPow a k ht) (fun t _ ht ↦ ?_) hu hv
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a)]
  refine mul_le_mul_of_nonneg_left ((abs_sgnPow_le _ _ t).trans ?_) (by linarith)
  exact Real.rpow_le_rpow (abs_nonneg t) ht (by linarith)

end NormPowIteratedFDeriv

/-! ### Elementary estimates -/

section Elementary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- On the open unit ball, $|\langle y, \omega \rangle| \le \|y\|$. -/
theorem abs_inner_le_of_mem_ball {y ω : E} (hω : ω ∈ ball (0 : E) 1) : |⟪y, ω⟫| ≤ ‖y‖ := by
  have : ‖ω‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hω).le
  calc |⟪y, ω⟫| ≤ ‖y‖ * ‖ω‖ := abs_real_inner_le_norm y ω
    _ ≤ ‖y‖ := mul_le_of_le_one_right (norm_nonneg y) this

/-- For all $y$ and $\omega$, $|\langle y, \omega \rangle| = \|y\| \, |\langle \|y\|^{-1} y, \omega
\rangle|$. This holds also for $y = 0$, where Lean sets $\|0\|^{-1} = 0$. -/
theorem abs_inner_eq_norm_mul (y ω : E) : |⟪y, ω⟫| = ‖y‖ * |⟪‖y‖⁻¹ • y, ω⟫| := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [real_inner_smul_left, abs_mul, abs_inv, abs_norm, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 hy), one_mul]

/-- The normalization $\|y\|^{-1} y$ has norm at most $1$. It is $0$ for $y = 0$, because Lean sets
$\|0\|^{-1} = 0$. -/
theorem norm_inv_smul_self_le (y : E) : ‖‖y‖⁻¹ • y‖ ≤ 1 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]

/-- The map $z \mapsto \langle z, \omega \rangle$ has the derivative
$h \mapsto \langle \omega, h \rangle$ at every point; this derivative is `innerSL ℝ ω`. -/
theorem hasFDerivAt_inner_left (ω y : E) :
    HasFDerivAt (fun z : E ↦ ⟪z, ω⟫) (innerSL ℝ ω) y := by
  have h := (innerSL ℝ ω).hasFDerivAt (x := y)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp [real_inner_comm]

/-- For $v_1, \dots, v_j \in E$, the map $\omega \mapsto \prod_i \langle v_i, \omega \rangle$ is
continuous. -/
theorem continuous_prod_inner {j : ℕ} (v : Fin j → E) : Continuous fun ω : E ↦ ∏ i, ⟪v i, ω⟫ :=
  continuous_finsetProd _ fun _ _ ↦ continuous_const.inner continuous_id

/-- On the open unit ball, $|\prod_i \langle v_i, \omega \rangle| \le \prod_i \|v_i\|$. -/
theorem abs_prod_inner_le {j : ℕ} (v : Fin j → E) {ω : E} (hω : ω ∈ ball (0 : E) 1) :
    |∏ i, ⟪v i, ω⟫| ≤ ∏ i, ‖v i‖ := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ abs_inner_le_of_mem_ball hω

/-- The weighted inequality of arithmetic and geometric means in the form that the derivatives of
$\|\cdot\|^\lambda$ use. Let $a \ge 0$ and $j \in \mathbb{N}$ with $a + j = \lambda > 0$, let
$s \ge 0$, and let $t_1, \dots, t_j \ge 0$. Then
$$s^a \prod_i t_i \le \frac{a}{\lambda} s^\lambda + \sum_i \frac{1}{\lambda} t_i^\lambda.$$
-/
theorem rpow_mul_prod_le_of_add_eq {a lam : ℝ} {j : ℕ} (ha : 0 ≤ a) (hlam : a + j = lam)
    (hpos : 0 < lam) {s : ℝ} (hs : 0 ≤ s) {t : Fin j → ℝ} (ht : ∀ i, 0 ≤ t i) :
    s ^ a * ∏ i, t i ≤ a / lam * s ^ lam + ∑ i, lam⁻¹ * t i ^ lam := by
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin (j + 1)))
    (Fin.cons (a / lam) fun _ ↦ lam⁻¹) (Fin.cons (s ^ lam) fun i ↦ t i ^ lam) ?_ ?_ ?_
  · simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
    have hmul : lam * (a / lam) = a := by field_simp
    rw [← Real.rpow_mul hs, hmul] at h
    simpa only [Real.rpow_rpow_inv (ht _) hpos.ne'] using h
  · intro i _
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simpa using div_nonneg ha hpos.le
    · simpa using hpos.le
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    linarith
  · intro i _
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simpa using Real.rpow_nonneg hs lam
    · simpa using Real.rpow_nonneg (ht i) lam

/-- For $j \le \lambda$, the number $\pi_j(\lambda) = \lambda (\lambda - 1) \cdots (\lambda - j +
1)$ is nonnegative. -/
theorem prod_range_sub_nonneg {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) :
    0 ≤ ∏ i ∈ Finset.range j, (lam - i) :=
  Finset.prod_nonneg fun i hi ↦ by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.1 hi
    linarith

end NormPowIteratedFDeriv

end Elementary

/-! ### The averaging identity -/

section Averaging

open NormPowIteratedFDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace NormPowIteratedFDeriv

/-- On a finite-dimensional space, a measurable function $g$ with $\|g(\omega)\| \le C$ on the open
unit ball is integrable on the open unit ball. -/
theorem integrableOn_ball_of_le {F : Type*} [NormedAddCommGroup F] {g : E → F}
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hb : ∀ ω ∈ ball (0 : E) 1, ‖g ω‖ ≤ C) :
    IntegrableOn g (ball (0 : E) 1) :=
  Measure.integrableOn_of_bounded measure_ball_lt_top.ne hg
    (ae_restrict_of_forall_mem measurableSet_ball hb)

omit [FiniteDimensional ℝ E] in
/-- The map $\omega \mapsto |\langle y, \omega \rangle|^a$ is measurable. -/
theorem measurable_abs_inner_rpow (y : E) (a : ℝ) : Measurable fun ω : E ↦ |⟪y, ω⟫| ^ a :=
  (continuous_abs.comp (continuous_const.inner continuous_id)).measurable.pow_const a

/-- For $a \ge 0$, the map $\omega \mapsto |\langle y, \omega \rangle|^a$ is integrable on the open
unit ball. -/
theorem integrableOn_abs_inner_rpow (y : E) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun ω : E ↦ |⟪y, ω⟫| ^ a) (ball (0 : E) 1) :=
  integrableOn_ball_of_le (measurable_abs_inner_rpow y a).aestronglyMeasurable (‖y‖ ^ a)
    fun ω hω ↦ by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) a)]
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_inner_le_of_mem_ball hω) ha

/-- Rotation invariance: for unit vectors $e$ and $u$ of a finite-dimensional real inner product
space, $\int_{\|\omega\| < 1} |\langle u, \omega \rangle|^\lambda \, d\omega = \int_{\|\omega\|
< 1} |\langle e, \omega \rangle|^\lambda \, d\omega$. -/
theorem integral_abs_inner_rpow_eq_of_norm_eq (lam : ℝ) {e u : E} (he : ‖e‖ = 1) (hu : ‖u‖ = 1) :
    ∫ ω in ball (0 : E) 1, |⟪u, ω⟫| ^ lam = ∫ ω in ball (0 : E) 1, |⟪e, ω⟫| ^ lam := by
  set T : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (e - u))ᗮ.reflection with hT
  have hTe : T e = u := Submodule.reflection_sub (he.trans hu.symm)
  have hpre : (T : E → E) ⁻¹' ball (0 : E) 1 = ball (0 : E) 1 := by
    rw [LinearIsometryEquiv.preimage_ball, map_zero]
  have h := T.measurePreserving.setIntegral_preimage_emb T.toHomeomorph.measurableEmbedding
    (fun ω ↦ |⟪u, ω⟫| ^ lam) (ball (0 : E) 1)
  rw [hpre] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_ball fun ω _ ↦ ?_
  rw [← hTe, LinearIsometryEquiv.inner_map_map]

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- **Averaging identity.** Let $E$ be a finite-dimensional real inner product space, and let
$\lambda \ge 0$. Then there is a constant $\kappa > 0$ such that for every $y \in E$,
$$\int_{\|\omega\| < 1} |\langle y, \omega \rangle|^\lambda \, d\omega = \kappa \,
  \|y\|^\lambda.$$

The integral is over the open unit ball with respect to Lebesgue measure. The constant $\kappa$
is the value of the integral at any unit vector, and the identity comes from the rotation
invariance of Lebesgue measure. -/
theorem exists_integral_abs_inner_rpow_eq {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ κ > 0, ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- on the zero space every `y` is `0` and the integrand is constant
    refine ⟨volume.real (ball (0 : E) 1), ?_, fun y ↦ ?_⟩
    · exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    · rw [Subsingleton.elim y 0]
      simp [mul_comm]
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  refine ⟨∫ ω in ball (0 : E) 1, |⟪e, ω⟫| ^ lam, ?_, fun y ↦ ?_⟩
  · change 0 < _
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun ω ↦ Real.rpow_nonneg (abs_nonneg _) lam)
      (integrableOn_abs_inner_rpow e hlam)]
    have hU : IsOpen ({ω : E | 0 < ⟪e, ω⟫} ∩ ball (0 : E) 1) :=
      (isOpen_lt continuous_const (continuous_const.inner continuous_id)).inter isOpen_ball
    have hne : ((1 / 2 : ℝ) • e) ∈ {ω : E | 0 < ⟪e, ω⟫} ∩ ball (0 : E) 1 := by
      refine ⟨?_, ?_⟩
      · simp [real_inner_smul_right, he]
      · simp [norm_smul, he]
        norm_num
    refine (hU.measure_pos volume ⟨_, hne⟩).trans_le (measure_mono ?_)
    rintro ω ⟨hω, hb⟩
    refine ⟨?_, hb⟩
    simp only [Function.mem_support]
    exact (Real.rpow_pos_of_pos (abs_pos.2 (ne_of_gt hω)) lam).ne'
  · rcases eq_or_ne y 0 with rfl | hy
    · rcases hlam.eq_or_lt with h0 | h0
      · simp [← h0]
      · simp [Real.zero_rpow h0.ne']
    have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
    rw [← integral_abs_inner_rpow_eq_of_norm_eq lam he hu, mul_comm, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun ω _ ↦ ?_
    rw [abs_inner_eq_norm_mul y ω, Real.mul_rpow (norm_nonneg _) (abs_nonneg _)]

namespace NormPowIteratedFDeriv

/-- For $x \neq 0$, the hyperplane $\{\omega : \langle x, \omega \rangle = 0\}$ is a null set for
Lebesgue measure. -/
theorem ae_inner_ne_zero {x : E} (hx : x ≠ 0) : ∀ᵐ ω ∂(volume : Measure E), ⟪x, ω⟫ ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have h := Measure.addHaar_submodule (volume : Measure E) (LinearMap.ker (innerₛₗ ℝ x)) ?_
  · convert h using 2
    ext ω
    simp
  intro htop
  have : x ∈ LinearMap.ker (innerₛₗ ℝ x) := htop ▸ Submodule.mem_top
  simp [hx] at this

omit [FiniteDimensional ℝ E] in
/-- The map $\omega \mapsto |\langle x, \omega \rangle|^a \prod_i |\langle v_i, \omega \rangle|$ is
measurable. -/
theorem measurable_abs_inner_rpow_mul_prod (x : E) (a : ℝ) {j : ℕ} (v : Fin j → E) :
    Measurable fun ω : E ↦ |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫| :=
  (measurable_abs_inner_rpow x a).mul <| Finset.measurable_prod _ fun _ _ ↦
    (continuous_abs.comp (continuous_const.inner continuous_id)).measurable

/-- For $a \ge 0$, the map $\omega \mapsto |\langle x, \omega \rangle|^a \prod_i |\langle v_i,
\omega \rangle|$ is integrable on the open unit ball. -/
theorem integrableOn_abs_inner_rpow_mul_prod (x : E) {a : ℝ} (ha : 0 ≤ a) {j : ℕ}
    (v : Fin j → E) :
    IntegrableOn (fun ω : E ↦ |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|) (ball (0 : E) 1) := by
  refine integrableOn_ball_of_le (measurable_abs_inner_rpow_mul_prod x a v).aestronglyMeasurable
    (‖x‖ ^ a * ∏ i, ‖v i‖) fun ω hω ↦ ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) a)
    (Finset.prod_nonneg fun i _ ↦ abs_nonneg _))]
  exact mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) (abs_inner_le_of_mem_ball hω) ha)
    (Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ abs_inner_le_of_mem_ball hω)
    (Finset.prod_nonneg fun i _ ↦ abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) a)

/-- **The Hölder step.** Let $E$ be a finite-dimensional real inner product space, let
$\kappa \ge 0$ satisfy $\int_{\|\omega\| < 1} |\langle y, \omega \rangle|^\lambda \, d\omega =
\kappa \|y\|^\lambda$ for all $y$, and let $a \ge 0$ and $j \in \mathbb{N}$ with
$a + j = \lambda > 0$. Then for all $x, v_1, \dots, v_j \in E$,
$$\int_{\|\omega\| < 1} |\langle x, \omega \rangle|^a \prod_i |\langle v_i, \omega \rangle| \,
  d\omega \le \kappa \, \|x\|^a \prod_i \|v_i\|.$$
The proof reduces by homogeneity to vectors of norm at most $1$, and then integrates the
weighted inequality of arithmetic and geometric means. -/
theorem integral_abs_inner_rpow_mul_prod_le {lam a κ : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (hlam : a + j = lam) (hpos : 0 < lam) (hκ0 : 0 ≤ κ)
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (x : E)
    (v : Fin j → E) :
    ∫ ω in ball (0 : E) 1, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫| ≤ κ * (‖x‖ ^ a * ∏ i, ‖v i‖) := by
  set xh : E := ‖x‖⁻¹ • x
  set vh : Fin j → E := fun i ↦ ‖v i‖⁻¹ • v i
  set c : ℝ := ‖x‖ ^ a * ∏ i, ‖v i‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) a)
    (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
  have hpt : ∀ ω, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|
      = c * (|⟪xh, ω⟫| ^ a * ∏ i, |⟪vh i, ω⟫|) := by
    intro ω
    rw [abs_inner_eq_norm_mul x ω, Real.mul_rpow (norm_nonneg _) (abs_nonneg _),
      Finset.prod_congr rfl fun i _ ↦ abs_inner_eq_norm_mul (v i) ω, Finset.prod_mul_distrib, hc]
    ring
  have hle : ∀ y : E, ‖‖y‖⁻¹ • y‖ ^ lam ≤ 1 := fun y ↦
    Real.rpow_le_one (norm_nonneg _) (norm_inv_smul_self_le y) hpos.le
  have hint : ∀ y : E, IntegrableOn (fun ω : E ↦ |⟪y, ω⟫| ^ lam) (ball (0 : E) 1) :=
    fun y ↦ integrableOn_abs_inner_rpow y hpos.le
  calc ∫ ω in ball (0 : E) 1, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|
      = c * ∫ ω in ball (0 : E) 1, |⟪xh, ω⟫| ^ a * ∏ i, |⟪vh i, ω⟫| := by
        rw [← integral_const_mul]
        simp_rw [hpt]
    _ ≤ c * ∫ ω in ball (0 : E) 1,
          (a / lam * |⟪xh, ω⟫| ^ lam + ∑ i, lam⁻¹ * |⟪vh i, ω⟫| ^ lam) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono
          (integrableOn_abs_inner_rpow_mul_prod xh ha vh)
          (((hint xh).const_mul _).add (integrable_finsetSum _ fun i _ ↦
            (hint (vh i)).const_mul _)) fun ω ↦ ?_) hc0
        exact rpow_mul_prod_le_of_add_eq ha hlam hpos (abs_nonneg _) fun i ↦ abs_nonneg _
    _ = c * (a / lam * (κ * ‖xh‖ ^ lam) + ∑ i, lam⁻¹ * (κ * ‖vh i‖ ^ lam)) := by
        rw [integral_add ((hint xh).const_mul _) (integrable_finsetSum _ fun i _ ↦
          (hint (vh i)).const_mul _), integral_finsetSum _ fun i _ ↦ (hint (vh i)).const_mul _,
          integral_const_mul, hκ]
        simp_rw [integral_const_mul, hκ]
    _ ≤ c * (a / lam * (κ * 1) + ∑ _i : Fin j, lam⁻¹ * (κ * 1)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ (Finset.sum_le_sum fun i _ ↦ ?_)) hc0
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle x) hκ0)
            (div_nonneg ha hpos.le)
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle (v i)) hκ0)
            (inv_nonneg.2 hpos.le)
    _ = κ * c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp
        rw [← hlam]
        ring

/-- **Differentiation under the integral.** Let $E$ be a finite-dimensional real inner product
space, let $a \ge 1$ and $k \in \mathbb{N}$, let $P \colon E \to \mathbb{R}$ be continuous with
$|P(\omega)| \le C$ on the open unit ball, and let $y \neq 0$. Then the vector-valued map
$\omega \mapsto a |\langle y, \omega \rangle|^{a-1} \operatorname{sign}(\langle y, \omega
\rangle)^{k+1} P(\omega) \, \langle \omega, \cdot \rangle$ is integrable on the open unit ball,
and the function
$$z \mapsto \int_{\|\omega\| < 1} |\langle z, \omega \rangle|^a \operatorname{sign}(\langle z,
  \omega \rangle)^k P(\omega) \, d\omega$$
has at $y$ the derivative
$$h \mapsto \int_{\|\omega\| < 1} a |\langle y, \omega \rangle|^{a-1}
  \operatorname{sign}(\langle y, \omega \rangle)^{k+1} P(\omega) \langle \omega, h \rangle \,
  d\omega.$$
The integrand is Lipschitz in $z$, and differentiable off the null hyperplane
$\langle y, \cdot \rangle = 0$. -/
theorem hasFDerivAt_integral_sgnPow_mul {a : ℝ} (ha : 1 ≤ a) (k : ℕ) {P : E → ℝ}
    (hP : Continuous P) {C : ℝ} (hPC : ∀ ω ∈ ball (0 : E) 1, |P ω| ≤ C) {y : E} (hy : y ≠ 0) :
    Integrable (fun ω ↦ (a * sgnPow (a - 1) (k + 1) ⟪y, ω⟫ * P ω) • innerSL ℝ ω)
        (volume.restrict (ball (0 : E) 1)) ∧
      HasFDerivAt (fun z ↦ ∫ ω in ball (0 : E) 1, sgnPow a k ⟪z, ω⟫ * P ω)
        (∫ ω in ball (0 : E) 1, (a * sgnPow (a - 1) (k + 1) ⟪y, ω⟫ * P ω) • innerSL ℝ ω) y := by
  have hmeas : ∀ z : E, Measurable fun ω : E ↦ sgnPow a k ⟪z, ω⟫ * P ω := fun z ↦
    ((measurable_sgnPow a k).comp (continuous_const.inner continuous_id).measurable).mul
      hP.measurable
  set R : ℝ := ‖y‖ + 1
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (bound := fun _ ↦ a * R ^ (a - 1) * C)
    (ball_mem_nhds y one_pos) (fun z _ ↦ (hmeas z).aestronglyMeasurable) ?_ ?_ ?_ ?_ ?_
  · refine integrableOn_ball_of_le (hmeas y).aestronglyMeasurable (‖y‖ ^ a * C) fun ω hω ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_sgnPow_le a k _).trans (Real.rpow_le_rpow (abs_nonneg _)
      (abs_inner_le_of_mem_ball hω) (by linarith))) (hPC ω hω) (abs_nonneg _)
      (Real.rpow_nonneg (norm_nonneg _) a)
  · exact ((((measurable_sgnPow (a - 1) (k + 1)).comp (continuous_const.inner
      continuous_id).measurable).const_mul a).mul hP.measurable).aestronglyMeasurable.smul
      (innerSL ℝ).continuous.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_ball fun ω hω z hz ↦ ?_
    have hz' : ‖z‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' z y
      have : ‖z - y‖ < 1 := by simpa [dist_eq_norm] using hz
      linarith
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    have h1 : |sgnPow a k ⟪z, ω⟫ - sgnPow a k ⟪y, ω⟫| ≤ a * R ^ (a - 1) * ‖z - y‖ := by
      refine (abs_sgnPow_sub_le ha k ((abs_inner_le_of_mem_ball hω).trans hz')
        ((abs_inner_le_of_mem_ball hω).trans (by linarith))).trans ?_
      rw [← inner_sub_left]
      exact mul_le_mul_of_nonneg_left (abs_inner_le_of_mem_ball hω)
        (mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _))
    calc |sgnPow a k ⟪z, ω⟫ - sgnPow a k ⟪y, ω⟫| * |P ω|
        ≤ (a * R ^ (a - 1) * ‖z - y‖) * C :=
          mul_le_mul h1 (hPC ω hω) (abs_nonneg _) (by positivity)
      _ = a * R ^ (a - 1) * C * ‖z - y‖ := by ring
  · exact integrableOn_ball_of_le aestronglyMeasurable_const |a * R ^ (a - 1) * C|
      fun _ _ ↦ le_rfl
  · refine ae_restrict_of_ae ((ae_inner_ne_zero hy).mono fun ω hω ↦ ?_)
    have h := ((hasDerivAt_sgnPow a k hω).comp_hasFDerivAt y (hasFDerivAt_inner_left ω y)).mul_const
      (P ω)
    refine h.congr_fderiv ?_
    ext h'
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring

/-- The integral formula of `iteratedFDeriv_normRpow_eq_integral` at points $x \neq 0$. Let $E$ be a
finite-dimensional real inner product space, and let $\kappa \neq 0$ satisfy $\int_{\|\omega\| <
1} |\langle y, \omega \rangle|^\lambda \, d\omega = \kappa \|y\|^\lambda$ for all $y$. Then for
$j \le \lambda$, $x \neq 0$ and $v_1, \dots, v_j \in E$,
$D^j(\|\cdot\|^\lambda)(x)[v_1, \dots, v_j]$ is $\pi_j(\lambda) / \kappa$ times the integral
over the open unit ball of $|\langle x, \omega \rangle|^{\lambda - j}
\operatorname{sign}(\langle x, \omega \rangle)^j \prod_i \langle v_i, \omega \rangle$. This is
the inductive core of the general formula. -/
theorem iteratedFDeriv_normRpow_eq_integral_of_ne_zero {lam κ : ℝ}
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (hκ0 : κ ≠ 0) :
    ∀ (j : ℕ), (j : ℝ) ≤ lam → ∀ {x : E}, x ≠ 0 → ∀ v : Fin j → E,
      iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x v
        = (∏ i ∈ Finset.range j, (lam - i)) / κ *
          ∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪x, ω⟫ * ∏ i, ⟪v i, ω⟫ := by
  intro j
  induction j with
  | zero =>
    intro _ x _ v
    simp only [iteratedFDeriv_zero_apply, Finset.range_zero, Finset.prod_empty, CharP.cast_eq_zero,
      sub_zero, Finset.univ_eq_empty, mul_one, sgnPow, pow_zero, hκ]
    field_simp
  | succ j ih =>
    intro hj x hx v
    have hj' : (j : ℝ) ≤ lam := by push_cast at hj; linarith
    have ha : 1 ≤ lam - j := by push_cast at hj; linarith
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam)) x :=
      ((contDiffOn_normRpow lam (j + 1)).contDiffAt (isOpen_compl_singleton.mem_nhds hx))
        |>.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    have hev : (fun y ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) y (Fin.tail v)) =ᶠ[𝓝 x]
        fun y ↦ (∏ i ∈ Finset.range j, (lam - i)) / κ *
          ∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪y, ω⟫ * ∏ i, ⟪Fin.tail v i, ω⟫ :=
      eventually_of_mem (isOpen_compl_singleton.mem_nhds hx) fun y hy ↦ ih hj' hy _
    obtain ⟨hint, hder⟩ := hasFDerivAt_integral_sgnPow_mul ha j (continuous_prod_inner (Fin.tail v))
      (fun ω hω ↦ abs_prod_inner_le (Fin.tail v) hω) hx
    rw [hev.fderiv_eq, (hder.const_mul _).fderiv, smul_apply,
      ContinuousLinearMap.integral_apply hint]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [Finset.prod_range_succ, Fin.prod_univ_succ, Fin.tail, Nat.cast_succ,
      show lam - j - 1 = lam - (j + 1) by ring, real_inner_comm ω (v 0)]
    field_simp

/-- Let $E$ be a finite-dimensional real inner product space, let $\kappa \ge 0$ satisfy
$\int_{\|\omega\| < 1} |\langle y, \omega \rangle|^\lambda \, d\omega = \kappa \|y\|^\lambda$
for all $y$, and let $a \ge 0$ and $j \in \mathbb{N}$ with $a + j = \lambda > 0$. If
$g \colon E \to \mathbb{R}$ satisfies $|g(\omega)| \le |\langle x, \omega \rangle|^a$ for all
$\omega$, then
$$\Big| \int_{\|\omega\| < 1} g(\omega) \prod_i \langle v_i, \omega \rangle \, d\omega \Big| \le
  \kappa \, \|x\|^a \prod_i \|v_i\|.$$
-/
theorem abs_integral_mul_prod_le {lam a κ : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (hlam : a + j = lam) (hpos : 0 < lam) (hκ0 : 0 ≤ κ)
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) {g : E → ℝ}
    (x : E) (hg : ∀ ω, |g ω| ≤ |⟪x, ω⟫| ^ a) (v : Fin j → E) :
    |∫ ω in ball (0 : E) 1, g ω * ∏ i, ⟪v i, ω⟫| ≤ κ * (‖x‖ ^ a * ∏ i, ‖v i‖) := by
  refine abs_integral_le_integral_abs.trans <| (integral_mono_of_nonneg
    (ae_of_all _ fun ω ↦ abs_nonneg _) (integrableOn_abs_inner_rpow_mul_prod x ha v)
    (ae_of_all _ fun ω ↦ ?_)).trans (integral_abs_inner_rpow_mul_prod_le ha hlam hpos hκ0 hκ x v)
  simp only
  rw [abs_mul, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_right (hg ω) (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- On a finite-dimensional real inner product space, for $j \le \lambda$ and $x \neq 0$,
$$\|D^j(\|\cdot\|^\lambda)(x)\| \le \pi_j(\lambda) \, \|x\|^{\lambda - j}.$$
The general case is `norm_iteratedFDeriv_normRpow_le`. -/
theorem norm_iteratedFDeriv_normRpow_le_of_finiteDimensional {lam : ℝ} {j : ℕ}
    (hj : (j : ℝ) ≤ lam) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  have hlam0 : 0 ≤ lam := (Nat.cast_nonneg j).trans hj
  rcases hlam0.eq_or_lt with hlam | hlam
  · have hj0 : j = 0 := by exact_mod_cast le_antisymm (hlam ▸ hj) (Nat.cast_nonneg j)
    subst hj0
    simp [← hlam]
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨κ, hκpos, hκ⟩ := exists_integral_abs_inner_rpow_eq (E := E) hlam0
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (prod_range_sub_nonneg hj) (Real.rpow_nonneg (norm_nonneg _) _)) fun v ↦ ?_
  rw [Real.norm_eq_abs, iteratedFDeriv_normRpow_eq_integral_of_ne_zero hκ hκpos.ne' j hj hx v,
    abs_mul, abs_div, abs_of_nonneg (prod_range_sub_nonneg hj), abs_of_pos hκpos]
  have h := abs_integral_mul_prod_le (sub_nonneg.2 hj) (by ring) hlam hκpos.le hκ x
    (g := fun ω ↦ sgnPow (lam - j) j ⟪x, ω⟫) (fun ω ↦ abs_sgnPow_le _ _ _) v
  calc (∏ i ∈ Finset.range j, (lam - i)) / κ *
        |∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪x, ω⟫ * ∏ i, ⟪v i, ω⟫|
      ≤ (∏ i ∈ Finset.range j, (lam - i)) / κ * (κ * (‖x‖ ^ (lam - j) * ∏ i, ‖v i‖)) :=
        mul_le_mul_of_nonneg_left h (div_nonneg (prod_range_sub_nonneg hj) hκpos.le)
    _ = _ := by field_simp


end Averaging

/-! ### Reduction to finite-dimensional subspaces -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- Let $E$ be a real inner product space, let $K$ be a subspace, let $s \subseteq E$ be open, and
let $f \colon E \to \mathbb{R}$ be of class $C^n$ on $s$. Then for every $x \in K$ with
$x \in s$ and all $v_1, \dots, v_n \in K$, the $n$-th derivative of the restriction $f|_K$ is
the restriction of the $n$-th derivative of $f$:
$$D^n(f|_K)(x)[v_1, \dots, v_n] = D^n f(x)[v_1, \dots, v_n].$$
-/
theorem _root_.Submodule.iteratedFDeriv_comp_subtypeL_apply (K : Submodule ℝ E) {f : E → ℝ}
    {s : Set E}
    (hs : IsOpen s) {n : ℕ} (hf : ContDiffOn ℝ n f s) {x : K} (hx : (x : E) ∈ s)
    (v : Fin n → K) :
    iteratedFDeriv ℝ n (fun y : K ↦ f y) x v = iteratedFDeriv ℝ n f x fun i ↦ (v i : E) := by
  have hpo : IsOpen (K.subtypeL ⁻¹' s) := hs.preimage K.subtypeL.continuous
  have h1 := K.subtypeL.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hpo.uniqueDiffOn hx
    le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpo hx] at h1
  rw [K.coe_subtypeL, Submodule.coe_subtype, iteratedFDerivWithin_of_isOpen n hs hx] at h1
  have h2 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ K) ℝ ↦ T v) h1
  simpa [Function.comp_def] using h2

/-- For $x, v_1, \dots, v_n \in E$, there is a finite-dimensional subspace of $E$ that contains $x$
and all $v_i$. -/
theorem exists_finiteDimensional_submodule (x : E) {n : ℕ} (v : Fin n → E) :
    ∃ K : Submodule ℝ E, FiniteDimensional ℝ K ∧ x ∈ K ∧ ∀ i, v i ∈ K :=
  ⟨Submodule.span ℝ (insert x (Set.range v)),
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range v).insert x),
    Submodule.subset_span (Set.mem_insert _ _),
    fun i ↦ Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- On any real inner product space, for $j \le \lambda$ and $x \neq 0$,
$$\|D^j(\|\cdot\|^\lambda)(x)\| \le \pi_j(\lambda) \, \|x\|^{\lambda - j}.$$
The proof restricts to the finite-dimensional span of $x$ and the arguments. This is the case
$x \neq 0$ of `norm_iteratedFDeriv_normRpow_le`. -/
theorem norm_iteratedFDeriv_normRpow_le_of_ne_zero {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (prod_range_sub_nonneg hj) (Real.rpow_nonneg (norm_nonneg _) _)) fun v ↦ ?_
  obtain ⟨K, hK, hxK, hvK⟩ := exists_finiteDimensional_submodule x v
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have hx' : (⟨x, hxK⟩ : K) ≠ 0 := by simpa using hx
  have h := K.iteratedFDeriv_comp_subtypeL_apply isOpen_compl_singleton (contDiffOn_normRpow lam j)
    (x := ⟨x, hxK⟩) hx (fun i ↦ ⟨v i, hvK i⟩)
  simp only at h
  rw [← h]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_normRpow_le_of_finiteDimensional hj hx')
    (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)

namespace NormPowIteratedFDeriv

/-- Let $E$ be a real inner product space, let $F$ be a real normed space, and let
$g \colon E \to F$ satisfy $\|g(y)\| \le C \|y\|^b$ for all $y$, where $b > 1$. Then $g$ has the
derivative $0$ at the origin. -/
theorem _root_.hasFDerivAt_zero_of_norm_le_rpow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {C b : ℝ} (hb : 1 < b) (hg : ∀ y, ‖g y‖ ≤ C * ‖y‖ ^ b) :
    HasFDerivAt g (0 : E →L[ℝ] F) 0 := by
  have hg0 : g 0 = 0 := by
    simpa [Real.zero_rpow (by linarith : b ≠ 0)] using hg 0
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, hg0, sub_zero, zero_apply]
  have h1 : (fun y : E ↦ ‖y‖ ^ (b - 1)) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff]
    have h := (continuous_norm.rpow_const (p := b - 1) fun _ ↦ Or.inr (by linarith)).tendsto (0 : E)
    rwa [norm_zero, Real.zero_rpow (by linarith : b - 1 ≠ 0)] at h
  have h2 := h1.mul_isBigO (Asymptotics.isBigO_refl (fun y : E ↦ ‖y‖) (𝓝 0))
  have h3 : (fun y : E ↦ ‖y‖ ^ b) =o[𝓝 0] fun y ↦ y := by
    refine (Asymptotics.isLittleO_norm_right.1 ?_)
    refine h2.congr' (Eventually.of_forall fun y ↦ ?_) (Eventually.of_forall fun y ↦ one_mul _)
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.zero_rpow (by linarith : b ≠ 0), Real.zero_rpow (by linarith : b - 1 ≠ 0)]
    · change ‖y‖ ^ (b - 1) * ‖y‖ = ‖y‖ ^ b
      rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hy), sub_add_cancel]
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound C
    (Eventually.of_forall fun y ↦ ?_)) h3
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact hg y

open Classical in
/-- The Taylor series of $\|\cdot\|^\lambda$ that proves its smoothness at the origin. At a point
$y \neq 0$, its term of order $m$ is the derivative $D^m(\|\cdot\|^\lambda)(y)$. At $y = 0$, its
terms of positive order are $0$, and its term of order $0$ is the value $\|0\|^\lambda$. -/
noncomputable def taylorNormRpow (lam : ℝ) (y : E) : FormalMultilinearSeries ℝ E ℝ :=
  fun m ↦ if y = 0 ∧ m ≠ 0 then 0 else iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) y

/-- At $y \neq 0$, the term of order $m$ of `NormPowIteratedFDeriv.taylorNormRpow` is
$D^m(\|\cdot\|^\lambda)(y)$. -/
theorem taylorNormRpow_of_ne_zero (lam : ℝ) {y : E} (hy : y ≠ 0) (m : ℕ) :
    taylorNormRpow lam y m = iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) y := by
  simp [taylorNormRpow, hy]

/-- For $\lambda > 0$, all terms of `NormPowIteratedFDeriv.taylorNormRpow` at the origin are $0$. -/
theorem taylorNormRpow_zero {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    taylorNormRpow lam (0 : E) m = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · ext v
    simp [taylorNormRpow, Real.zero_rpow hlam.ne']
  · simp [taylorNormRpow, hm]

/-- For $\lambda > 0$ and $m \le \lambda$, the term of order $m$ of
`NormPowIteratedFDeriv.taylorNormRpow` at $y$ has norm at most
$\pi_m(\lambda) \|y\|^{\lambda - m}$. -/
theorem norm_taylorNormRpow_le {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : (m : ℝ) ≤ lam) (y : E) :
    ‖taylorNormRpow lam y m‖ ≤ (∏ i ∈ Finset.range m, (lam - i)) * ‖y‖ ^ (lam - m) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [taylorNormRpow_zero hlam, norm_zero]
    exact mul_nonneg (prod_range_sub_nonneg hm) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [taylorNormRpow_of_ne_zero lam hy]
    exact norm_iteratedFDeriv_normRpow_le_of_ne_zero hm hy

/-- For $n < \lambda$, `NormPowIteratedFDeriv.taylorNormRpow` is a Taylor series of
$\|\cdot\|^\lambda$ up to order $n$ on the whole space. Each term of order $m < n$ is
differentiable at the origin with derivative $0$, because it is $O(\|y\|^{\lambda - m})$ with
$\lambda - m > 1$, and each term of order $m \le n$ is continuous there. -/
theorem hasFTaylorSeriesUpTo_normRpow {lam : ℝ} {n : ℕ} (hn : (n : ℝ) < lam) :
    HasFTaylorSeriesUpTo n (fun y : E ↦ ‖y‖ ^ lam) (taylorNormRpow lam) := by
  have hlam : 0 < lam := (Nat.cast_nonneg n).trans_lt hn
  have hsmooth : ∀ {y : E}, y ≠ 0 → ContDiffAt ℝ (n + 1 : ℕ) (fun y : E ↦ ‖y‖ ^ lam) y :=
    fun hy ↦ (contDiffOn_normRpow lam (n + 1)).contDiffAt (isOpen_compl_singleton.mem_nhds hy)
  have hev : ∀ {y : E}, y ≠ 0 → ∀ m,
      (fun z ↦ taylorNormRpow lam z m) =ᶠ[𝓝 y] iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) :=
    fun hy m ↦ eventually_of_mem (isOpen_compl_singleton.mem_nhds hy) fun z hz ↦
      taylorNormRpow_of_ne_zero lam hz m
  refine ⟨fun y ↦ ?_, fun m hm y ↦ ?_, fun m hm ↦ ?_⟩
  · simp [taylorNormRpow]
  · have hm' : m < n := by exact_mod_cast hm
    rcases eq_or_ne y 0 with rfl | hy
    · rw [taylorNormRpow_zero hlam]
      have h0 : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) ℝ).curryLeft = 0 := by
        ext; simp
      rw [h0]
      have hmlam : (m : ℝ) ≤ lam := by
        have : (m : ℝ) < n := by exact_mod_cast hm'
        linarith
      refine hasFDerivAt_zero_of_norm_le_rpow (C := ∏ i ∈ Finset.range m, (lam - i))
        (b := lam - m) ?_ fun z ↦ ?_
      · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm'
        linarith
      · exact norm_taylorNormRpow_le hlam hmlam z
    · have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam)) y :=
        (hsmooth hy).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_lt hm')
      refine (hd.hasFDerivAt.congr_of_eventuallyEq (hev hy m)).congr_fderiv ?_
      rw [fderiv_iteratedFDeriv, taylorNormRpow_of_ne_zero lam hy]
      ext h v
      simp
  · have hm' : m ≤ n := by exact_mod_cast hm
    have hmlam : (m : ℝ) < lam := lt_of_le_of_lt (by exact_mod_cast hm') hn
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    rcases eq_or_ne y 0 with rfl | hy
    · rw [ContinuousAt, taylorNormRpow_zero hlam]
      refine squeeze_zero_norm (fun z ↦ norm_taylorNormRpow_le hlam hmlam.le z) ?_
      simpa [Real.zero_rpow (sub_pos.2 hmlam).ne'] using
        (((continuous_norm.rpow_const fun _ ↦ Or.inr (sub_pos.2 hmlam).le).const_mul
          (∏ i ∈ Finset.range m, (lam - i))).tendsto (0 : E))
    · exact ((hsmooth hy).continuousAt_iteratedFDeriv (by exact_mod_cast
        (hm'.trans (Nat.le_succ n) : m ≤ n + 1))).congr (hev hy m).symm

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- **Smoothness of $\|\cdot\|^\lambda$ on the whole space.** Let $E$ be a real inner product space,
let $\lambda \in \mathbb{R}$, and let $j \in \mathbb{N}$ with $j < \lambda$. Then the function
$x \mapsto \|x\|^\lambda$ is of class $C^j$ on $E$, including the origin. -/
theorem contDiff_normRpow_of_lt {lam : ℝ} {j : ℕ} (hj : (j : ℝ) < lam) :
    ContDiff ℝ j (fun y : E ↦ ‖y‖ ^ lam) :=
  (hasFTaylorSeriesUpTo_normRpow hj).contDiff

open NormPowIteratedFDeriv in
/-- Let $E$ be a real inner product space, let $\lambda \in \mathbb{R}$, and let $i \in \mathbb{N}$
with $i < \lambda$. Then the derivative of order $i$ of $x \mapsto \|x\|^\lambda$ vanishes at
the origin:
$$D^i(\|\cdot\|^\lambda)(0) = 0.$$
-/
theorem iteratedFDeriv_normRpow_zero {lam : ℝ} {i : ℕ} (hi : (i : ℝ) < lam) :
    iteratedFDeriv ℝ i (fun y : E ↦ ‖y‖ ^ lam) 0 = 0 := by
  rw [← (hasFTaylorSeriesUpTo_normRpow hi).eq_iteratedFDeriv le_rfl,
    taylorNormRpow_zero ((Nat.cast_nonneg i).trans_lt hi)]

/-- **Sharp operator-norm bound on the derivatives of $\|\cdot\|^\lambda$.** Let $E$ be a real inner
product space, let $\lambda \in \mathbb{R}$, let $j \in \mathbb{N}$ with $j \le \lambda$, and
let $x \in E$ with $x \neq 0$ or $j < \lambda$. Then
$$\|D^j(\|\cdot\|^\lambda)(x)\| \le \lambda (\lambda - 1) \cdots (\lambda - j + 1) \,
  \|x\|^{\lambda - j}.$$
This is (B.4.1) of Lemma B.4.1 of [cartis2022evaluation]. At $x = 0$ with $j < \lambda$ both
sides are $0$.

On a finite-dimensional subspace, the derivative is an average of $|\langle x, \omega
\rangle|^{\lambda - j} \operatorname{sign}(\langle x, \omega \rangle)^j \prod_i \langle v_i,
\omega \rangle$ over the unit ball (`iteratedFDeriv_normRpow_eq_integral`), and a weighted
inequality of arithmetic and geometric means, of Hölder type, bounds this average. -/
theorem norm_iteratedFDeriv_normRpow_le {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0 ∨ (j : ℝ) < lam) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [iteratedFDeriv_normRpow_zero (hx.resolve_left (not_not.2 rfl)), norm_zero]
    exact mul_nonneg (NormPowIteratedFDeriv.prod_range_sub_nonneg hj)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · exact norm_iteratedFDeriv_normRpow_le_of_ne_zero hj hx0

/-- Let $E$ be a real inner product space, let $j \in \mathbb{N}$ with $j \le \lambda$, and let
$x \in E$ with $x \neq 0$ or $j < \lambda$. Then for every $v \in E$,
$$|D^j(\|\cdot\|^\lambda)(x)[v]^j| \le \lambda (\lambda - 1) \cdots (\lambda - j + 1) \,
  \|x\|^{\lambda - j} \|v\|^j.$$
This is the diagonal form of `norm_iteratedFDeriv_normRpow_le`. -/
theorem abs_iteratedFDeriv_normRpow_apply_le {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0 ∨ (j : ℝ) < lam) (v : E) :
    |iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ v)|
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) * ‖v‖ ^ j := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_normRpow_le hj hx)
    (pow_nonneg (norm_nonneg _) _)

namespace NormPowIteratedFDeriv

/-- The number $\pi_j(\lambda) = \lambda (\lambda - 1) \cdots (\lambda - j + 1)$ is the descending
Pochhammer polynomial of degree $j$ evaluated at $\lambda$. -/
theorem prod_range_sub_eq_descPochhammer (lam : ℝ) (j : ℕ) :
    ∏ i ∈ Finset.range j, (lam - i) = (descPochhammer ℝ j).eval lam := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.prod_range_succ, ih, descPochhammer_succ_eval]

/-- For natural numbers $n$ and $k$, $\prod_{i < k} (n - i) = n (n - 1) \cdots (n - k + 1)$ is the
descending factorial `n.descFactorial k`. Both sides are $0$ for $k > n$. -/
theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ Finset.range k, ((n : ℝ) - i) = n.descFactorial k := by
  rw [prod_range_sub_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-- For natural numbers $k \le n$, the descending factorial `n.descFactorial k` equals
$n! / (n - k)!$ in $\mathbb{R}$. -/
theorem descFactorial_eq_div (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = n ! / (n - k) ! := by
  rw [eq_div_iff (by positivity), mul_comm, ← Nat.cast_mul, Nat.factorial_mul_descFactorial hk]

end NormPowIteratedFDeriv

/-- Let $j \le p$ be natural numbers and let $\beta \in \mathbb{R}$. Then the generalized factorial
satisfies
$$(p + \beta)! = (p + \beta)(p + \beta - 1) \cdots (p + \beta - j + 1) \cdot (p - j + \beta)!.$$

The generalized factorial $(k + \beta)!$ is `holderFactorial k β`. -/
theorem holderFactorial_eq_prod_range_mul {p j : ℕ} (hj : j ≤ p) (β : ℝ) :
    holderFactorial p β
      = (∏ i ∈ Finset.range j, ((p : ℝ) + β - i)) * holderFactorial (p - j) β := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), Finset.prod_range_succ]
    obtain ⟨k, hk⟩ : ∃ k, p - j = k + 1 := ⟨p - j - 1, by omega⟩
    rw [hk, holderFactorial_succ, show p - (j + 1) = k by omega]
    have : (k : ℝ) + 1 = p - j := by
      have : ((k + 1 : ℕ) : ℝ) = ((p - j : ℕ) : ℝ) := by rw [hk]
      push_cast [Nat.cast_sub (show j ≤ p by omega)] at this
      exact this
    rw [this]
    ring

/-- **The factorial ratio of Lemma B.4.1** of [cartis2022evaluation]. Let $j \le p$ be natural
numbers and let $\beta > -1$. Then
$$\frac{(p + \beta)!}{(p - j + \beta)!} = \pi_j(p + \beta) = \prod_{i < j} (p + \beta - i).$$

The generalized factorial $(k + \beta)!$ is `holderFactorial k β`. The hypothesis $\beta > -1$
makes the denominator nonzero. -/
theorem holderFactorial_div_holderFactorial_sub {p j : ℕ} (hj : j ≤ p) {β : ℝ} (hβ : -1 < β) :
    holderFactorial p β / holderFactorial (p - j) β = ∏ i ∈ Finset.range j, ((p : ℝ) + β - i) := by
  have hpos : 0 < holderFactorial (p - j) β := by
    induction p - j with
    | zero => simp
    | succ k ih =>
      rw [holderFactorial_succ]
      exact mul_pos ih (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  rw [holderFactorial_eq_prod_range_mul hj β, mul_div_cancel_right₀ _ hpos.ne']

/-- For $p \in \mathbb{N}$ and $\beta \in \mathbb{R}$, $\prod_{i = 0}^{p} (p + \beta - i) = \beta \,
(p + \beta)!$, where $(p + \beta)!$ is `holderFactorial p β`. -/
theorem prod_fin_succ_eq_mul_holderFactorial (p : ℕ) (β : ℝ) :
    ∏ i : Fin (p + 1), ((p : ℝ) + β - i) = β * holderFactorial p β := by
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ (p : ℝ) + β - i), Finset.prod_range_succ,
    holderFactorial_eq_prod_range_mul (le_refl p) β, Nat.sub_self, holderFactorial_zero,
    mul_one]
  ring

namespace NormPowIteratedFDeriv

end NormPowIteratedFDeriv

end General

/-! ### The integral formula and the Lipschitz bound in finite dimension -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open NormPowIteratedFDeriv in
/-- **Integral formula for the derivatives of $\|\cdot\|^\lambda$.** Let $E$ be a finite-dimensional
real inner product space, let $\lambda, \kappa \in \mathbb{R}$ with $\kappa \neq 0$, and assume
that
$$\int_{\|\omega\| < 1} |\langle y, \omega \rangle|^\lambda \, d\omega = \kappa \, \|y\|^\lambda
  \quad \text{for all } y \in E,$$
as given by `exists_integral_abs_inner_rpow_eq`. Let $j \in \mathbb{N}$ with $j \le \lambda$,
and let $x \in E$ with $x \neq 0$ or $j < \lambda$. Then for all $v_1, \dots, v_j \in E$,
$$D^j(\|\cdot\|^\lambda)(x)[v_1, \dots, v_j] = \frac{\pi_j(\lambda)}{\kappa} \int_{\|\omega\| <
  1} |\langle x, \omega \rangle|^{\lambda - j} \operatorname{sign}(\langle x, \omega \rangle)^j
  \prod_i \langle v_i, \omega \rangle \, d\omega.$$

The integral is over the open unit ball with respect to Lebesgue measure. The proof
differentiates under the integral sign, one order at a time. -/
theorem iteratedFDeriv_normRpow_eq_integral {lam κ : ℝ}
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (hκ0 : κ ≠ 0)
    {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E} (hx : x ≠ 0 ∨ (j : ℝ) < lam) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x v
      = (∏ i ∈ Finset.range j, (lam - i)) / κ *
        ∫ ω in ball (0 : E) 1,
          |⟪x, ω⟫| ^ (lam - j) * (SignType.sign ⟪x, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hlt := hx.resolve_left (not_not.2 rfl)
    rw [iteratedFDeriv_normRpow_zero hlt]
    simp [Real.zero_rpow (sub_pos.2 hlt).ne']
  · exact iteratedFDeriv_normRpow_eq_integral_of_ne_zero hκ hκ0 j hj hx0 v

namespace NormPowIteratedFDeriv

/-- On a finite-dimensional real inner product space, for all $x, y, v_1, \dots, v_j$,
$$|D^j(\|\cdot\|^{j+1})(x)[v] - D^j(\|\cdot\|^{j+1})(y)[v]| \le (j + 1)! \, \|x - y\| \prod_i
  \|v_i\|.$$
This is the finite-dimensional core of `iteratedFDerivLipschitzOn_norm_pow`. -/
theorem abs_iteratedFDeriv_normRpow_sub_le_of_finiteDimensional (j : ℕ) (x y : E)
    (v : Fin j → E) :
    |iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) x v
        - iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) y v|
      ≤ (j + 1)! * ‖x - y‖ * ∏ i, ‖v i‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, abs_zero]
    positivity
  have : Nontrivial E := ⟨⟨x - y, 0, sub_ne_zero.2 hxy⟩⟩
  set lam : ℝ := (j : ℝ) + 1
  have hlam : 0 < lam := by positivity
  have hjl : (j : ℝ) < lam := lt_add_one _
  obtain ⟨κ, hκpos, hκ⟩ := exists_integral_abs_inner_rpow_eq (E := E) hlam.le
  have hsub : lam - j = 1 := by ring
  have hc : ∏ i ∈ Finset.range j, (lam - i) = (j + 1)! := by
    have h := prod_range_natCast_sub (j + 1) j
    rw [descFactorial_eq_div _ _ (Nat.le_succ j), show j + 1 - j = 1 by omega, Nat.factorial_one,
      Nat.cast_one, div_one] at h
    simpa [lam] using h
  have hint : ∀ z : E, Integrable (fun ω ↦ |⟪z, ω⟫| ^ (lam - j) *
      (SignType.sign ⟪z, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫) (volume.restrict (ball (0 : E) 1)) := by
    intro z
    refine integrableOn_ball_of_le ((((measurable_sgnPow (lam - j) j).comp
      (continuous_const.inner continuous_id).measurable).mul
      (continuous_prod_inner v).measurable).aestronglyMeasurable) (‖z‖ ^ (lam - j) *
        ∏ i, ‖v i‖) fun ω hω ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_sgnPow_le _ _ _).trans (Real.rpow_le_rpow (abs_nonneg _)
      (abs_inner_le_of_mem_ball hω) (by rw [hsub]; exact zero_le_one)))
      (abs_prod_inner_le v hω) (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [iteratedFDeriv_normRpow_eq_integral hκ hκpos.ne' hjl.le (Or.inr hjl),
    iteratedFDeriv_normRpow_eq_integral hκ hκpos.ne' hjl.le (Or.inr hjl), ← mul_sub,
    ← integral_sub (hint x) (hint y), hc, abs_mul, abs_div, abs_of_pos hκpos,
    Nat.abs_cast]
  have h := abs_integral_mul_prod_le (a := 1) zero_le_one (by ring) hlam hκpos.le hκ (x - y)
    (g := fun ω ↦ sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) (fun ω ↦ ?_) v
  · simp only [Real.rpow_one] at h
    rw [show (fun ω ↦ |⟪x, ω⟫| ^ (lam - j) * (SignType.sign ⟪x, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫ -
        |⟪y, ω⟫| ^ (lam - j) * (SignType.sign ⟪y, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫)
        = fun ω ↦ (sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) * ∏ i, ⟪v i, ω⟫ by
          funext ω; rw [hsub, sgnPow, sgnPow]; ring]
    calc ((j + 1)! : ℝ) / κ *
          |∫ ω in ball (0 : E) 1, (sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) * ∏ i, ⟪v i, ω⟫|
        ≤ (j + 1)! / κ * (κ * (‖x - y‖ * ∏ i, ‖v i‖)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by field_simp
  · have h1 := abs_sgnPow_sub_le (le_refl (1 : ℝ)) j (le_max_left |⟪x, ω⟫| |⟪y, ω⟫|)
      (le_max_right |⟪x, ω⟫| |⟪y, ω⟫|)
    rw [sub_self, Real.rpow_zero, one_mul, one_mul, ← inner_sub_left] at h1
    rwa [Real.rpow_one]

end NormPowIteratedFDeriv

end FiniteDimensional

/-! ### Radial values, the norm, and the Lipschitz bound on any inner product space -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NormPowIteratedFDeriv

/-- **Radial values.** Let $E$ be a real inner product space, let $\lambda \in \mathbb{R}$ and
$j \in \mathbb{N}$, and let $x \neq 0$. Then
$$D^j(\|\cdot\|^\lambda)(x)[x, \dots, x] = \lambda (\lambda - 1) \cdots (\lambda - j + 1) \,
  \|x\|^\lambda.$$
This is (B.4.2) of [cartis2022evaluation]. -/
theorem iteratedFDeriv_normRpow_apply_self (lam : ℝ) (j : ℕ) {x : E} (hx : x ≠ 0) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ x)
      = (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ lam := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxu : (fun _ : Fin j ↦ x) = fun _ ↦ ‖x‖ • (‖x‖⁻¹ • x) := by
    funext
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  rw [hxu, ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_unit lam j hx,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.prod_range,
    ← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hnx, add_sub_cancel]

/-- **The operator norm of the derivatives of $\|\cdot\|^\lambda$.** Let $E$ be a real inner product
space, let $j \in \mathbb{N}$ with $j \le \lambda$, and let $x \neq 0$. Then
$$\|D^j(\|\cdot\|^\lambda)(x)\| = \lambda (\lambda - 1) \cdots (\lambda - j + 1) \,
  \|x\|^{\lambda - j},$$
and the norm is attained in the radial direction. This is (B.4.1) of [cartis2022evaluation] as
an equality.

For $\lambda = j = p + 1$ this gives $\|\nabla^{p+1} \|x\|^{p+1}\| = (p + 1)!$, the case
$\beta = 1$ of (B.4.3). -/
theorem norm_iteratedFDeriv_normRpow {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      = (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  refine le_antisymm (norm_iteratedFDeriv_normRpow_le hj (Or.inl hx)) ?_
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x)
    fun _ ↦ ‖x‖⁻¹ • x
  rw [iteratedFDeriv_normRpow_apply_unit lam j hx, ← Finset.prod_range (fun i ↦ lam - i)] at h
  simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne', Finset.prod_const_one,
    mul_one] at h
  exact (le_abs_self _).trans h

/-- For $j \in \mathbb{N}$, the derivative of order $j$ of $x \mapsto \|x\|^{j+1}$ is
$(j + 1)!$-Lipschitz on the whole space. Here the exponent $j + 1$ is a real number. -/
theorem iteratedFDerivLipschitzOn_normRpow_add_one (j : ℕ) :
    IteratedFDerivLipschitzOn (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) j ((j + 1)! : ℝ) univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x _ y _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  obtain ⟨K, hK, hxK, hvK⟩ := exists_finiteDimensional_submodule x (Fin.cons y v)
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have hyK : y ∈ K := by simpa using hvK 0
  have hvK' : ∀ i, v i ∈ K := fun i ↦ by simpa using hvK i.succ
  have hf : ContDiffOn ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) univ :=
    (contDiff_normRpow_of_lt (lt_add_one _)).contDiffOn
  have hx' := K.iteratedFDeriv_comp_subtypeL_apply isOpen_univ hf (x := ⟨x, hxK⟩) (mem_univ _)
    (fun i ↦ ⟨v i, hvK' i⟩)
  have hy' := K.iteratedFDeriv_comp_subtypeL_apply isOpen_univ hf (x := ⟨y, hyK⟩) (mem_univ _)
    (fun i ↦ ⟨v i, hvK' i⟩)
  simp only at hx' hy'
  rw [sub_apply, ← hx', ← hy', Real.norm_eq_abs]
  exact abs_iteratedFDeriv_normRpow_sub_le_of_finiteDimensional (E := K) j ⟨x, hxK⟩ ⟨y, hyK⟩
    fun i ↦ ⟨v i, hvK' i⟩

end Radial

/-! ### Natural exponents -/

section NaturalPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NormPowIteratedFDeriv

namespace NormPowIteratedFDeriv

omit [InnerProductSpace ℝ E] in
/-- The natural power $\|s\|^r$ equals the real power $\|s\|^{(r : \mathbb{R})}$. -/
theorem norm_pow_eq_normRpow (r : ℕ) :
    (fun s : E ↦ ‖s‖ ^ r) = fun s : E ↦ ‖s‖ ^ (r : ℝ) :=
  funext fun s ↦ (Real.rpow_natCast ‖s‖ r).symm

/-- For natural numbers $\ell \le r$, $\prod_{i < \ell} (r - i) = r! / (r - \ell)!$. -/
theorem prod_range_natCast_sub_eq_div {r ℓ : ℕ} (h : ℓ ≤ r) :
    ∏ i ∈ Finset.range ℓ, ((r : ℝ) - i) = r ! / (r - ℓ) ! := by
  rw [prod_range_natCast_sub, descFactorial_eq_div r ℓ h]

omit [InnerProductSpace ℝ E] in
/-- For natural numbers $\ell \le r$, the real power $\|s\|^{(r : \mathbb{R}) - \ell}$ equals the
natural power $\|s\|^{r - \ell}$. -/
theorem norm_rpow_natCast_sub {r ℓ : ℕ} (h : ℓ ≤ r) (s : E) :
    ‖s‖ ^ ((r : ℝ) - ℓ) = ‖s‖ ^ (r - ℓ) := by
  rw [← Nat.cast_sub h, Real.rpow_natCast]

end NormPowIteratedFDeriv

/-- **Smoothness of $\|\cdot\|^r$ for natural $r$.** Let $E$ be a real inner product space and let
$r \ge 1$ be a natural number. Then the function $s \mapsto \|s\|^r$ is of class $C^{r-1}$ on
$E$. In particular, the regularization term $\|s\|^{p+1}$ is of class $C^p$. -/
theorem contDiff_norm_pow {r : ℕ} (hr : 1 ≤ r) :
    ContDiff ℝ (r - 1 : ℕ) (fun s : E ↦ ‖s‖ ^ r) := by
  rw [norm_pow_eq_normRpow]
  refine contDiff_normRpow_of_lt ?_
  rw [Nat.cast_sub hr]
  simp

/-- Let $E$ be a real inner product space and let $r$ be an even natural number. Then the function
$s \mapsto \|s\|^r$ is analytic on $E$, since $\|s\|^r = (\|s\|^2)^{r/2}$ is a polynomial.

Analyticity is `ContDiff ℝ ⊤`, the class $C^\omega$. -/
theorem contDiff_norm_pow_of_even {r : ℕ} (hr : Even r) :
    ContDiff ℝ ⊤ (fun s : E ↦ ‖s‖ ^ r) := by
  obtain ⟨m, rfl⟩ := hr
  simp_rw [← two_mul, pow_mul]
  exact contDiff_norm_sq ℝ |>.pow m

/-- Let $E$ be a real inner product space and let $r$ be a natural number. Then the function
$s \mapsto \|s\|^r$ is analytic at every $s \neq 0$.

Analyticity is `ContDiffAt ℝ ⊤`, the class $C^\omega$. -/
theorem contDiffAt_norm_pow (r : ℕ) {s : E} (hs : s ≠ 0) :
    ContDiffAt ℝ ⊤ (fun s : E ↦ ‖s‖ ^ r) s :=
  (contDiffAt_norm ℝ hs).pow r

/-- **Radial values for natural exponents.** Let $E$ be a real inner product space, let $\ell \le r$
be natural numbers, and let $s \in E$ with $s \neq 0$ or $\ell < r$. Then
$$D^\ell(\|\cdot\|^r)(s)[s, \dots, s] = \frac{r!}{(r - \ell)!} \|s\|^r.$$
This is (B.4.2) of [cartis2022evaluation] for $\beta = 1$. -/
theorem iteratedFDeriv_norm_pow_apply_self {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs : s ≠ 0 ∨ ℓ < r) :
    iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s (fun _ ↦ s) = r ! / (r - ℓ) ! * ‖s‖ ^ r := by
  rw [norm_pow_eq_normRpow]
  rcases eq_or_ne s 0 with rfl | hs0
  · have hlt := hs.resolve_left (not_not.2 rfl)
    rw [iteratedFDeriv_normRpow_zero (by exact_mod_cast hlt)]
    simp [(Nat.zero_le ℓ).trans_lt hlt |>.ne']
  · rw [iteratedFDeriv_normRpow_apply_self _ _ hs0, prod_range_natCast_sub_eq_div hℓ,
      Real.rpow_natCast]

/-- **Sharp operator-norm bound for natural exponents.** Let $E$ be a real inner product space, let
$\ell \le r$ be natural numbers, and let $s \in E$ with $s \neq 0$ or $\ell < r$. Then
$$\|D^\ell(\|\cdot\|^r)(s)\| \le \frac{r!}{(r - \ell)!} \|s\|^{r - \ell}.$$
This is Lemma B.4.1 of [cartis2022evaluation] for $\beta = 1$. For $s \neq 0$ the bound is an
equality (`norm_iteratedFDeriv_norm_pow`). -/
theorem norm_iteratedFDeriv_norm_pow_le {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E} (hs : s ≠ 0 ∨ ℓ < r) :
    ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ ≤ r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) := by
  rw [norm_pow_eq_normRpow, ← prod_range_natCast_sub_eq_div hℓ, ← norm_rpow_natCast_sub hℓ]
  exact norm_iteratedFDeriv_normRpow_le (by exact_mod_cast hℓ) (by exact_mod_cast hs)

/-- Let $E$ be a real inner product space, let $\ell \le r$ be natural numbers, and let $s \neq 0$.
Then
$$\|D^\ell(\|\cdot\|^r)(s)\| = \frac{r!}{(r - \ell)!} \|s\|^{r - \ell}.$$
This is the equality case of `norm_iteratedFDeriv_norm_pow_le`. -/
theorem norm_iteratedFDeriv_norm_pow {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E} (hs : s ≠ 0) :
    ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ = r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) := by
  rw [norm_pow_eq_normRpow, ← prod_range_natCast_sub_eq_div hℓ, ← norm_rpow_natCast_sub hℓ]
  exact norm_iteratedFDeriv_normRpow (by exact_mod_cast hℓ) hs

/-- Let $E$ be a real inner product space, let $\ell \le r$ be natural numbers, and let $s \in E$
with $s \neq 0$ or $\ell < r$. Then for every $d \in E$,
$$|D^\ell(\|\cdot\|^r)(s)[d]^\ell| \le \frac{r!}{(r - \ell)!} \|s\|^{r - \ell} \|d\|^\ell.$$
This is the diagonal form of `norm_iteratedFDeriv_norm_pow_le`. Equality holds for $d = s$
(`iteratedFDeriv_norm_pow_apply_self`). -/
theorem abs_iteratedFDeriv_norm_pow_apply_le {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs : s ≠ 0 ∨ ℓ < r) (d : E) :
    |iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s (fun _ ↦ d)|
      ≤ r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) * ‖d‖ ^ ℓ := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_norm_pow_le hℓ hs)
    (pow_nonneg (norm_nonneg _) _)

/-- **Lipschitz continuity of $\nabla^{r-1} \|\cdot\|^r$.** Let $E$ be a real inner product space
and let $r \ge 1$ be a natural number. Then the derivative of order $r - 1$ of
$s \mapsto \|s\|^r$ is $r!$-Lipschitz on the whole space:
$$\|D^{r-1}(\|\cdot\|^r)(x) - D^{r-1}(\|\cdot\|^r)(y)\| \le r! \, \|x - y\| \quad \text{for all
  } x, y \in E.$$
This is (B.4.3) of [cartis2022evaluation] for $\beta = 1$.

The Lipschitz condition is `IteratedFDerivLipschitzOn` on `Set.univ`. -/
theorem iteratedFDerivLipschitzOn_norm_pow {r : ℕ} (hr : 1 ≤ r) :
    IteratedFDerivLipschitzOn (fun s : E ↦ ‖s‖ ^ r) (r - 1) (r ! : ℝ) univ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [norm_pow_eq_normRpow, Nat.add_sub_cancel]
  simpa using iteratedFDerivLipschitzOn_normRpow_add_one (E := E) j

/-- **Taylor remainder of $\|\cdot\|^r$.** Let $E$ be a real inner product space and let $r \ge 1$
be a natural number. Then for all $s, d \in E$,
$$\big| \|s + d\|^r - T_{r-1}(s, d) \big| \le \|d\|^r,$$
where $T_{r-1}(s, d) = \sum_{i \le r-1} \frac{1}{i!} D^i(\|\cdot\|^r)(s)[d]^i$ is the Taylor
polynomial of degree $r - 1$ of $\|\cdot\|^r$ at $s$.

The Taylor polynomial is `taylorPolynomial`. -/
theorem abs_norm_pow_sub_taylorPolynomial_le {r : ℕ} (hr : 1 ≤ r) (s d : E) :
    |‖s + d‖ ^ r - taylorPolynomial (fun s : E ↦ ‖s‖ ^ r) (r - 1) s d| ≤ ‖d‖ ^ r := by
  have h := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ ↦ (contDiff_norm_pow (E := E) hr).contDiffAt) (iteratedFDerivLipschitzOn_norm_pow hr)
    (mem_univ s) (mem_univ (s + d))
  rwa [Nat.sub_add_cancel hr, div_self (by positivity), one_mul] at h

/-- For natural numbers $\ell \le r$ and $s$ in the closed unit ball with $s \neq 0$ or $\ell < r$,
$\|D^\ell(\|\cdot\|^r)(s)\| \le r!$. -/
theorem norm_iteratedFDeriv_norm_pow_le_factorial {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs0 : s ≠ 0 ∨ ℓ < r)
    (hs : ‖s‖ ≤ 1) : ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ ≤ r ! := by
  refine (norm_iteratedFDeriv_norm_pow_le hℓ hs0).trans ?_
  have h1 : ‖s‖ ^ (r - ℓ) ≤ 1 := pow_le_one₀ (norm_nonneg _) hs
  have h2 : (r ! : ℝ) / (r - ℓ)! ≤ r ! :=
    div_le_self (by positivity)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  calc (r ! : ℝ) / (r - ℓ)! * ‖s‖ ^ (r - ℓ) ≤ (r ! : ℝ) / (r - ℓ)! * 1 := by gcongr
    _ ≤ r ! := by rw [mul_one]; exact h2


end NaturalPower

/-! ### The operator norm off the radial direction, and convexity (Lemma B.4.1) -/

section Convexity

open NormPowIteratedFDeriv

/-- **The radial value is not the operator norm for fractional $\beta$.** Let $p = 1$ and
$\beta = 1/2$, so that $\lambda = p + \beta = 3/2$, and let $x = e_0 \in \mathbb{R}^2$ be the
first coordinate vector. Then the operator norm of $D^2(\|\cdot\|^{3/2})(x)$ exceeds the radial
value:
$$\beta \, (p + \beta)! \, \|x\|^{\beta - 1} = \frac{3}{4} < \|D^2(\|\cdot\|^{3/2})(x)\|.$$
The derivative in the direction $e_1 \perp x$ is already $3/2$.

The generalized factorial $(p + \beta)!$ is `holderFactorial 1 (1 / 2)`, and $\mathbb{R}^2$ is
`EuclideanSpace ℝ (Fin 2)`. -/
theorem not_norm_iteratedFDeriv_normRpow_eq_radial :
    (1 / 2 : ℝ) * holderFactorial 1 (1 / 2)
        * ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ ^ ((1 / 2 : ℝ) - 1)
      < ‖iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ (3 / 2 : ℝ))
          (EuclideanSpace.single 0 1)‖ := by
  set x : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  set u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have hx : ‖x‖ = 1 := by simp [x]
  have hu : ‖u‖ = 1 := by simp [u]
  have hxu : ⟪x, u⟫ = 0 := by simp [x, u, EuclideanSpace.inner_single_left]
  have hx0 : x ≠ 0 := fun h ↦ by simp [h] at hx
  have h := iteratedFDeriv_normRpow_apply_perp (3 / 2 : ℝ) 2 hx0 hu hxu
  have h2 := iteratedDeriv_one_add_sq_rpow_two_mul (3 / 2 : ℝ) 1
  simp only [mul_one, Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, CharP.cast_eq_zero,
    mul_zero, zero_add, sub_zero, Finset.prod_singleton, one_mul] at h2
  rw [h2, hx, Real.one_rpow, one_mul] at h
  have hle := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ (3 / 2 : ℝ)) x) fun _ ↦ u
  rw [h, hu] at hle
  have hβ : holderFactorial 1 (1 / 2) = 3 / 2 := by
    simp [holderFactorial]
    norm_num
  rw [hβ, hx, Real.one_rpow]
  norm_num at hle ⊢
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- For $\lambda \in \mathbb{R}$ and $m \in \mathbb{N}$, the derivative of odd order $2m + 1$ of the
even function $t \mapsto (1 + t^2)^{\lambda/2}$ vanishes at $0$. -/
theorem iteratedDeriv_one_add_sq_rpow_two_mul_add_one (lam : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, iteratedDeriv_one_add_sq_rpow_succ_succ, ih,
      mul_zero]

/-- For $j \in \mathbb{N}$ with $j \le \lambda + 2$, the derivative of order $j$ of
$t \mapsto (1 + t^2)^{\lambda/2}$ at $0$ is nonnegative. -/
theorem iteratedDeriv_one_add_sq_rpow_nonneg {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam + 2) :
    0 ≤ iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [iteratedDeriv_one_add_sq_rpow_two_mul]
    refine Finset.prod_nonneg fun i _ ↦ mul_nonneg (by positivity) ?_
    have : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
    push_cast at hj
    linarith
  · rw [iteratedDeriv_one_add_sq_rpow_two_mul_add_one]

/-- Let $x \neq 0$ and let $d$ be orthogonal to $x$. Then
$$D^j(\|\cdot\|^\lambda)(x)[d]^j = \|x\|^{\lambda - j} \, h^{(j)}(0) \, \|d\|^j, \qquad h(t) =
  (1 + t^2)^{\lambda/2}.$$
-/
theorem iteratedFDeriv_normRpow_apply_of_inner_eq_zero (lam : ℝ) (j : ℕ) {x d : E}
    (hx : x ≠ 0) (hxd : ⟪x, d⟫ = 0) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ d)
      = ‖x‖ ^ (lam - j) * iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 * ‖d‖ ^ j := by
  obtain ⟨K, hK, hxK, hdK⟩ := exists_finiteDimensional_submodule x fun _ : Fin 1 ↦ d
  have h := K.iteratedFDeriv_comp_subtypeL_apply isOpen_compl_singleton (contDiffOn_normRpow lam j)
    (x := ⟨x, hxK⟩) hx (fun _ ↦ ⟨d, hdK 0⟩)
  simp only at h
  rw [← h]
  set x' : K := ⟨x, hxK⟩
  set d' : K := ⟨d, hdK 0⟩
  have hx' : x' ≠ 0 := by simpa [x'] using hx
  change iteratedFDeriv ℝ j (fun y : K ↦ ‖y‖ ^ lam) x' (fun _ ↦ d')
    = ‖x'‖ ^ (lam - j) * _ * ‖d'‖ ^ j
  rcases eq_or_ne d' 0 with hd | hd
  · rcases j.eq_zero_or_pos with rfl | hj
    · simp
    · rw [hd, ContinuousMultilinearMap.map_coord_zero _ ⟨0, hj⟩ rfl, norm_zero,
        zero_pow hj.ne', mul_zero]
  have hnd : 0 < ‖d'‖ := norm_pos_iff.2 hd
  have hu : ‖‖d'‖⁻¹ • d'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnd.ne']
  have hxu : ⟪x', ‖d'‖⁻¹ • d'⟫ = 0 := by
    rw [real_inner_smul_right]
    change ‖d'‖⁻¹ * ⟪x, d⟫ = 0
    rw [hxd, mul_zero]
  have hdu : (fun _ : Fin j ↦ d') = fun _ ↦ ‖d'‖ • (‖d'‖⁻¹ • d') := by
    funext
    rw [smul_smul, mul_inv_cancel₀ hnd.ne', one_smul]
  rw [hdu, ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_perp lam j hx' hu
    hxu, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end NormPowIteratedFDeriv

/-- **The convexity statements of Lemma B.4.1** of [cartis2022evaluation]. Let $E$ be a real inner
product space, let $\lambda \in \mathbb{R}$, let $j \in \mathbb{N}$ with $j \le \lambda + 2$,
and let $x \in E$ with $x \neq 0$. Then:

(a) on the orthogonal complement of $x$, the map $d \mapsto D^j(\|\cdot\|^\lambda)(x)[d]^j$ is
convex;

(b) if $j$ is even and $j \le \lambda + 1$, the map $t \mapsto D^j(\|\cdot\|^\lambda)(x)[t x]^j$
is convex on $\mathbb{R}$.

In (a) the map is $c \|d\|^j$ with $c = \|x\|^{\lambda - j} h^{(j)}(0) \ge 0$ and
$h(t) = (1 + t^2)^{\lambda/2}$, and $c = 0$ for odd $j$. In (b) the map is $t \mapsto t^j \,
\lambda (\lambda - 1) \cdots (\lambda - j + 1) \, \|x\|^\lambda$. For $\lambda = p + \beta$, the
range $j \le \lambda + 1$ of (b) covers the derivatives of orders $j \le p + 1$ that the lemma
is about. Beyond this range the coefficient $\lambda (\lambda - 1) \cdots (\lambda - j + 1)$ can
be negative. -/
theorem convexOn_iteratedFDeriv_normRpow {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam + 2) {x : E}
    (hx : x ≠ 0) :
    ConvexOn ℝ ((ℝ ∙ x)ᗮ : Set E)
        (fun d ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ d)) ∧
      (Even j → (j : ℝ) ≤ lam + 1 → ConvexOn ℝ univ
        (fun t : ℝ ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ t • x))) := by
  refine ⟨?_, fun hje hj1 ↦ ?_⟩
  · have hc : 0 ≤ ‖x‖ ^ (lam - j) * iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (iteratedDeriv_one_add_sq_rpow_nonneg hj)
    refine (((convexOn_norm (ℝ ∙ x)ᗮ.convex).pow fun d _ ↦ norm_nonneg d) j).smul hc
      |>.congr fun d hd ↦ ?_
    rw [iteratedFDeriv_normRpow_apply_of_inner_eq_zero lam j hx
      ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hd)]
    simp [smul_eq_mul, mul_assoc]
  · have hπ : 0 ≤ ∏ i ∈ Finset.range j, (lam - i) := Finset.prod_nonneg fun i hi ↦ by
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.1 hi
      linarith
    refine (hje.convexOn_pow.smul (mul_nonneg hπ (Real.rpow_nonneg (norm_nonneg x) lam)))
      |>.congr fun t _ ↦ ?_
    simp only [smul_eq_mul]
    rw [ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_self lam j hx,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring

end Convexity
