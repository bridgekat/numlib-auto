/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, with the `Lp` lemmas beside
`Mathlib.MeasureTheory.Function.LpSpace.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Integrals over a bounded interval

This file collects facts about functions on a compact interval $[a, b]$ and their integrals over the
open interval $(a, b)$, for use in numerical analysis and in the theory of differential equations.
The endpoints do not matter for integrability or for the value of an integral, and a function
continuous on $[a, b]$ is in $L^\infty(a, b)$ and $L^2(a, b)$ and is determined by its class there.
The file proves the Cauchy–Schwarz inequality for integrals of products, the classical Poincaré
inequality $\int_a^b v^2 \le \frac{(b - a)^2}{2} \int_a^b (v')^2$ for $v(a) = 0$, and the weighted
mean value theorem $\int_a^b K f = f(\xi) \int_a^b K$ for $K \ge 0$, with $\xi$ in the open interval
when $\int_a^b K > 0$. This form of the mean value theorem is what the Peano-kernel error formulas
of quadrature rules need.

The file also proves the fundamental theorem of calculus on $(0, T]$ for a function with a limit at
$0^+$, the passage from bounded integrals on $(0, T]$ to integrability on $(0, \infty)$, a
one-variable estimate $\int_I |f|^P \le t^P \int_J |f'|^P$ for a function that vanishes at the left
end of an interval of length $t$, the approximation of an integrable nonnegative weight by
continuous nonnegative functions in $L^1$, and the fact that a real polynomial whose square has
integral $0$ over a nondegenerate interval is $0$.

## Main results

* `MeasureTheory.IntegrableOn.integrableOn_Icc_of_Ioo`,
  `MeasureTheory.IntegrableOn.intervalIntegrable_of_Ioo`: integrability on $(a, b)$ gives
  integrability on $[a, b]$ and between any two points of $[a, b]$.
* `intervalIntegral.integral_congr_Ioo`, `intervalIntegral.integral_congr_ae_Ioo_of_mem`,
  `intervalIntegral.integral_eq_setIntegral_Ioo`: interval integrals depend only on the integrand
  almost everywhere on $(a, b)$, and $\int_a^b F = \int_{(a, b)} F$.
* `intervalIntegral.integral_fold_neg`: $\int_{-a}^a H = \int_0^a (H(t) + H(-t)) \, dt$.
* `ContinuousOn.memLp_top_restrict_Ioo`, `ContinuousOn.memLp_two_restrict_Ioo`, `eqOn_Icc_of_ae_eq`:
  a function continuous on $[a, b]$ is in $L^\infty(a, b)$ and $L^2(a, b)$, and is determined on
  $[a, b]$ by its class.
* `MeasureTheory.L2.norm_sq_eq_integral_sq`: $\|f\|^2 = \int f^2 \, d\mu$ in a real $L^2(\mu)$.
* `MeasureTheory.abs_integral_mul_le_sqrt_mul_sqrt`,
  `intervalIntegral.integral_mul_le_sqrt_mul_sqrt`,
  `intervalIntegral.sq_integral_mul_le_of_continuousOn`: the Cauchy–Schwarz inequality for integrals
  of products.
* `intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero`: the classical Poincaré
  inequality.
* `intervalIntegral.hasDerivWithinAt_integral_Ici`, `intervalIntegral.continuousOn_integral_Icc`:
  the primitive of a function continuous on $[a, b]$ is continuous on $[a, b]$ and has the right
  derivative $p(t)$ at $t \in [a, b)$.
* `intervalIntegral.exists_integral_mul_eq_mul_integral`,
  `intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral`: the weighted mean value theorem,
  with $\xi \in [a, b]$, and with $\xi \in (a, b)$ when $\int_a^b K > 0$.
* `intervalIntegral.exists_continuous_nonneg_integral_abs_sub_le`: an integrable nonnegative weight
  is within any distance in $L^1(a, b)$ of a continuous nonnegative function.
* `integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg`: if $\varphi' = -g \le 0$ on $(0, \infty)$,
  $\varphi \ge 0$ and $\varphi(t) \to L$ as $t \to 0^+$, then $\varphi(T) + \int_0^T g = L$.
* `lintegral_enorm_rpow_le_of_hasDerivAt`: the one-variable estimate behind the estimate on a strip.
* `Polynomial.eq_zero_of_integral_mul_self_eq_zero`: a real polynomial $p$ with $\int_u^v p^2 = 0$
  and $u < v$ is $0$.

## Implementation notes

* An integral over $(a, b)$ is the integral for the measure `volume.restrict (Ioo a b)`, and
  $L^2(a, b)$ is `Lp ℝ 2 (volume.restrict (Ioo a b))`.
* The approximation of a weight in $L^1$ is the step by which a Gronwall lemma in integral form with
  an integrable weight follows from the version with a continuous weight.
-/

open Filter MeasureTheory Set Topology intervalIntegral
open scoped ENNReal Interval

/-! ### Integrability on $(a, b)$ and on $[a, b]$ -/

section Integrability

variable {a b : ℝ} {w : ℝ → ℝ}

/-- If $w \colon \mathbb{R} \to \mathbb{R}$ is integrable on $(a, b)$, then $w$ is integrable on
$[a, b]$. -/
theorem MeasureTheory.IntegrableOn.integrableOn_Icc_of_Ioo (hw : IntegrableOn w (Ioo a b)) :
    IntegrableOn w (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := w) (μ := volume) (a := a) (b := b) enorm_ne_top
    enorm_ne_top).2 hw

/-- If $w \colon \mathbb{R} \to \mathbb{R}$ is integrable on $(a, b)$, then $w$ is interval
integrable between any two points $x, y \in [a, b]$. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_of_Ioo (hw : IntegrableOn w (Ioo a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : IntervalIntegrable w volume x y :=
  (hw.integrableOn_Icc_of_Ioo.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable

/-- Let $a \le b$, let $w \colon \mathbb{R} \to \mathbb{R}$ be integrable on $(a, b)$, and let
$c \in \mathbb{R}$. Then the function $x \mapsto c + \int_a^x w(t) \, dt$ is continuous on
$[a, b]$. -/
theorem intervalIntegral.continuousOn_integral_of_integrableOn_Ioo (hab : a ≤ b)
    (hw : IntegrableOn w (Ioo a b)) (c : ℝ) :
    ContinuousOn (fun x ↦ c + ∫ t in a..x, w t) (Icc a b) :=
  continuousOn_const.add (by
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (f := w) (a := a) (b := b)
      (by simpa [uIcc_of_le hab] using hw.integrableOn_Icc_of_Ioo))

end Integrability

/-! ### The endpoints do not matter -/

namespace intervalIntegral

variable {a b : ℝ}

/-- Let $a \le b$. If $g(t) = h(t)$ for every $t \in (a, b)$, then $\int_a^b g = \int_a^b h$. -/
theorem integral_congr_Ioo {g h : ℝ → ℝ} (hab : a ≤ b) (hgh : ∀ t ∈ Ioo a b, g t = h t) :
    ∫ t in a..b, g t = ∫ t in a..b, h t :=
  integral_congr_Ioo_of_le hab hgh

/-- If $f = g$ almost everywhere on $(a, b)$, then $\int_s^t f = \int_s^t g$ for all
$s, t \in [a, b]$. -/
theorem integral_congr_ae_Ioo_of_mem {f g : ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (Ioo a b)] g) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ r in s..t, f r = ∫ r in s..t, g r := by
  refine intervalIntegral.integral_congr_ae ?_
  have ha : ∀ᵐ r : ℝ, r ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ r : ℝ, r ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 h, ha, hb] with r hr hra hrb hrI
  have hr' : r ∈ Icc a b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hrI)
  exact hr ⟨lt_of_le_of_ne hr'.1 (Ne.symm hra), lt_of_le_of_ne hr'.2 hrb⟩

/-- Let $a \le b$ and $F \colon \mathbb{R} \to \mathbb{R}$. Then
$\int_a^b F(x) \, dx = \int_{(a, b)} F(x) \, dx$. -/
theorem integral_eq_setIntegral_Ioo (hab : a ≤ b) (F : ℝ → ℝ) :
    ∫ x in a..b, F x = ∫ x in Ioo a b, F x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end intervalIntegral

/-! ### Symmetric intervals -/

/-- **Folding a symmetric interval onto its right half.** Let $E$ be a real normed space, and let
$H \colon \mathbb{R} \to E$ be interval integrable on $[-a, 0]$ and on $[0, a]$. Then
$$\int_{-a}^{a} H(t) \, dt = \int_0^a \big(H(t) + H(-t)\big) \, dt.$$
-/
theorem intervalIntegral.integral_fold_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : ℝ → E} {a : ℝ} (h₁ : IntervalIntegrable H volume (-a) 0)
    (h₂ : IntervalIntegrable H volume 0 a) :
    ∫ t in -a..a, H t = ∫ t in (0 : ℝ)..a, (H t + H (-t)) := by
  have h₃ : IntervalIntegrable (fun t => H (-t)) volume 0 a := by
    simpa using ((IntervalIntegrable.iff_comp_neg (a := -a) (b := 0)).mp h₁).symm
  rw [intervalIntegral.integral_add h₂ h₃, intervalIntegral.integral_comp_neg H, neg_zero,
    add_comm, intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

/-! ### Continuous functions on $[a, b]$ in $L^p(a, b)$ -/

section Lp

variable {a b : ℝ}

/-- Let $a < b$. If $g_1$ and $g_2$ are continuous on $[a, b]$ and $g_1 = g_2$ almost everywhere on
$(a, b)$, then $g_1 = g_2$ on $[a, b]$. -/
theorem eqOn_Icc_of_ae_eq (hab : a < b) {g₁ g₂ : ℝ → ℝ} (h₁ : ContinuousOn g₁ (Icc a b))
    (h₂ : ContinuousOn g₂ (Icc a b)) (h : g₁ =ᵐ[volume.restrict (Ioo a b)] g₂) :
    EqOn g₁ g₂ (Icc a b) :=
  Measure.eqOn_of_ae_eq (by rwa [← restrict_Ioo_eq_restrict_Icc (μ := volume)]) h₁ h₂
    (by rw [interior_Icc, closure_Ioo hab.ne])

/-- A function $g \colon \mathbb{R} \to \mathbb{R}$ continuous on $[a, b]$ is in $L^\infty(a, b)$.
-/
theorem ContinuousOn.memLp_top_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g ⊤ (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact memLp_top_of_bound ((hg.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦
      hC x (Ioo_subset_Icc_self hx)))

/-- A function $g \colon \mathbb{R} \to \mathbb{R}$ continuous on $[a, b]$ is in $L^2(a, b)$. -/
theorem ContinuousOn.memLp_two_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g 2 (volume.restrict (Ioo a b)) :=
  hg.memLp_top_restrict_Ioo.mono_exponent le_top

/-- If $g \colon \mathbb{R} \to \mathbb{R}$ is continuous on $[a, b]$ and $f \in L^2(a, b)$, then
$x \mapsto g(x) f(x)$ is integrable on $(a, b)$. -/
theorem MeasureTheory.integrableOn_continuousOn_mul {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    IntegrableOn (fun x ↦ g x * f x) (Ioo a b) :=
  IntegrableOn.continuousOn_mul_of_subset hg ((Lp.memLp f).integrable one_le_two) isCompact_Icc
    measurableSet_Ioo Ioo_subset_Icc_self

/-- For every measure $\mu$ and every $f$ in the space $L^2(\mu)$ of real functions,
$\|f\|^2 = \int f^2 \, d\mu$. -/
theorem MeasureTheory.L2.norm_sq_eq_integral_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- For every $f \in L^2(a, b)$, $\|f\|^2 = \int_{(a, b)} |f(x)|^2 \, dx$. This is
`MeasureTheory.L2.norm_sq_eq_integral_sq` for the interval. -/
theorem norm_sq_eq_integral_sq (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ‖f‖ ^ 2 = ∫ x in Ioo a b, |f x| ^ 2 := by
  simp_rw [L2.norm_sq_eq_integral_sq, sq_abs]

/-- Let $a \le b$, let $f \in L^2(a, b)$, and let $C \ge 0$ with $|f| \le C$ almost everywhere on
$(a, b)$. Then $\|f\| \le \sqrt{b - a} \, C$. -/
theorem MeasureTheory.Lp.norm_le_sqrt_mul_of_ae_bound (hab : a ≤ b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ C) : ‖f‖ ≤ Real.sqrt (b - a) * C := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq_integral_sq,
    mul_pow, Real.sq_sqrt (sub_nonneg.2 hab)]
  calc ∫ x in Ioo a b, |f x| ^ 2 ≤ ∫ _ in Ioo a b, C ^ 2 := by
        refine integral_mono_ae ?_ (integrableOn_const (by simp)) ?_
        · have := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
          simpa [Real.norm_eq_abs] using this
        · filter_upwards [h] with x hx
          exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    _ = (b - a) * C ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]

/-- Let $f, g, h \in L^2(a, b)$ and $c, d \ge 0$. If $|f| \le c (|g| + d |h|)$ almost everywhere on
$(a, b)$, then $\|f\| \le c (\|g\| + d \|h\|)$. -/
theorem MeasureTheory.Lp.norm_le_of_abs_le (f g h : Lp ℝ 2 (volume.restrict (Ioo a b))) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hle : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ c * (|g x| + d * |h x|)) :
    ‖f‖ ≤ c * (‖g‖ + d * ‖h‖) := by
  set k : Lp ℝ 2 (volume.restrict (Ioo a b)) := c • (|g| + d • |h|) with hk
  have hfk : |f| ≤ |k| := by
    rw [← Lp.coeFn_le]
    filter_upwards [hle, Lp.coeFn_abs f, Lp.coeFn_abs k, Lp.coeFn_smul c (|g| + d • |h|),
      Lp.coeFn_add |g| (d • |h|), Lp.coeFn_smul d |h|, Lp.coeFn_abs g, Lp.coeFn_abs h]
      with x h1 h2 h3 h4 h5 h6 h7 h8
    rw [h2, h3, hk, h4, Pi.smul_apply, h5, Pi.add_apply, h6, Pi.smul_apply, h7, h8, smul_eq_mul,
      smul_eq_mul]
    refine h1.trans (le_abs_self _)
  calc ‖f‖ ≤ ‖k‖ := HasSolidNorm.solid hfk
    _ ≤ c * (‖g‖ + d * ‖h‖) := by
        rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_abs_eq_norm, norm_smul, norm_abs_eq_norm, Real.norm_eq_abs, abs_of_nonneg hd]

end Lp

/-! ### The Cauchy–Schwarz inequality for integrals of products -/

section CauchySchwarz

/-- **The Cauchy–Schwarz inequality for the integral of a product.** Let $\mu$ be a measure and let
$f, g \in L^2(\mu)$ be real. Then
$$\Big|\int f g \, d\mu\Big| \le \Big(\int f^2 \, d\mu\Big)^{1/2} \Big(\int g^2 \,
  d\mu\Big)^{1/2}.$$

This is Hölder's inequality for the conjugate exponents $2$ and $2$. -/
theorem MeasureTheory.abs_integral_mul_le_sqrt_mul_sqrt {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ y, f y * g y ∂μ| ≤ √(∫ y, f y ^ 2 ∂μ) * √(∫ y, g y ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by
    simp [ENNReal.ofReal_ofNat]
  have key := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hpq
    (by rwa [h2]) (by rwa [h2])
  have hrw : ∀ h : X → ℝ, (∫ y, ‖h y‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = √(∫ y, h y ^ 2 ∂μ) := by
    intro h
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ‖h y‖ ^ (2 : ℝ) = h y ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [hrw f, hrw g] at key
  refine le_trans (abs_integral_le_integral_abs) (le_trans (le_of_eq ?_) key)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [abs_mul, Real.norm_eq_abs]

variable {u v : ℝ} {f g : ℝ → ℝ}

/-- **The Cauchy–Schwarz inequality for interval integrals.** Let $u \le v$, and let
$f, g \colon \mathbb{R} \to \mathbb{R}$ be such that $f$, $f^2$, $g$ and $g^2$ are interval
integrable on $[u, v]$. Then
$$\int_u^v f g \le \Big(\int_u^v f^2\Big)^{1/2} \Big(\int_u^v g^2\Big)^{1/2}.$$

This is Hölder's inequality for the conjugate exponents $2$ and $2$. -/
theorem intervalIntegral.integral_mul_le_sqrt_mul_sqrt (huv : u ≤ v)
    (hf : IntervalIntegrable f volume u v) (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume u v)
    (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume u v) :
    ∫ s in u..v, f s * g s ≤ √(∫ s in u..v, f s ^ 2) * √(∫ s in u..v, g s ^ 2) := by
  have hfm : MemLp f 2 (volume.restrict (Ioc u v)) :=
    (memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).2 hf2.1
  have hgm : MemLp g 2 (volume.restrict (Ioc u v)) :=
    (memLp_two_iff_integrable_sq hg.1.aestronglyMeasurable).2 hg2.1
  have key := MeasureTheory.abs_integral_mul_le_sqrt_mul_sqrt hfm hgm
  rw [intervalIntegral.integral_of_le huv, intervalIntegral.integral_of_le huv,
    intervalIntegral.integral_of_le huv]
  exact (le_abs_self _).trans key

/-- **The Cauchy–Schwarz inequality for interval integrals** of continuous functions. Let $a \le b$,
and let $f$ and $g$ be continuous on $[a, b]$. Then
$$\Big(\int_a^b f g\Big)^2 \le \Big(\int_a^b f^2\Big) \Big(\int_a^b g^2\Big).$$

The proof uses the nonnegativity of $\int_a^b (\lambda f + g)^2$ for every $\lambda$ and the
sign of the discriminant of this quadratic in $\lambda$. -/
theorem intervalIntegral.sq_integral_mul_le_of_continuousOn {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, f t ^ 2) * ∫ t in a..b, g t ^ 2 := by
  have hff : IntervalIntegrable (fun t => f t ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab
  have hgg : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab
  have hfg : IntervalIntegrable (fun t => f t * g t) volume a b :=
    (hf.mul hg).intervalIntegrable_of_Icc hab
  have hexp : ∀ l : ℝ, (∫ t in a..b, (l * f t + g t) ^ 2)
      = (∫ t in a..b, f t ^ 2) * (l * l) + 2 * (∫ t in a..b, f t * g t) * l
        + ∫ t in a..b, g t ^ 2 := by
    intro l
    have hcongr : ∀ t ∈ uIcc a b, (l * f t + g t) ^ 2
        = l ^ 2 * f t ^ 2 + (2 * l) * (f t * g t) + g t ^ 2 := fun t _ => by ring
    rw [integral_congr hcongr, integral_add ((hff.const_mul _).add (hfg.const_mul _)) hgg,
      integral_add (hff.const_mul _) (hfg.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have hnn : ∀ l : ℝ, 0 ≤ (∫ t in a..b, f t ^ 2) * (l * l)
      + 2 * (∫ t in a..b, f t * g t) * l + ∫ t in a..b, g t ^ 2 := by
    intro l
    rw [← hexp l]
    exact integral_nonneg hab fun t _ => sq_nonneg _
  have hd := discrim_le_zero hnn
  rw [discrim] at hd
  nlinarith [hd]

/-- If $f$, $f^2$, $g$ and $g^2$ are interval integrable on $[u, v]$, then $fg$ is interval
integrable on $[u, v]$. -/
theorem intervalIntegrable_mul_of_sq (hf : IntervalIntegrable f volume u v)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume u v) (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume u v) :
    IntervalIntegrable (fun s => f s * g s) volume u v :=
  ⟨((memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).2 hf2.1).integrable_mul
      ((memLp_two_iff_integrable_sq hg.1.aestronglyMeasurable).2 hg2.1),
    ((memLp_two_iff_integrable_sq hf.2.aestronglyMeasurable).2 hf2.2).integrable_mul
      ((memLp_two_iff_integrable_sq hg.2.aestronglyMeasurable).2 hg2.2)⟩

/-- If $g$ and $g^2$ are interval integrable on $[u, v]$ and $p$ is continuous on the closed
interval between $u$ and $v$, then $(g - p)^2$ is interval integrable on $[u, v]$. -/
theorem intervalIntegrable_sub_sq {p : ℝ → ℝ} (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume u v) (hp : ContinuousOn p [[u, v]]) :
    IntervalIntegrable (fun s => (g s - p s) ^ 2) volume u v := by
  have : (fun s => (g s - p s) ^ 2) = fun s => g s ^ 2 - 2 * (g s * p s) + p s ^ 2 := by
    funext s; ring
  rw [this]
  exact (hg2.sub ((hg.mul_continuousOn hp).const_mul 2)).add (hp.pow 2).intervalIntegrable

end CauchySchwarz

/-! ### The Poincaré inequality on an interval, classical form -/

/-- **The Cauchy–Schwarz inequality for the increment of a $C^1$ function.** Let $a \le b$, let $v$
and $v'$ be continuous on $[a, b]$, and let $v$ have the derivative $v'(x)$ at every
$x \in (a, b)$. Then
$$\big(v(b) - v(a)\big)^2 \le (b - a) \int_a^b v'(x)^2 \, dx.$$

The proof applies `intervalIntegral.sq_integral_mul_le_of_continuousOn` to
$v(b) - v(a) = \int_a^b v' \cdot 1$. This is the pointwise step of the Poincaré inequality
`intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero`. -/
theorem intervalIntegral.sq_sub_le_mul_integral_sq_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    {v vx : ℝ → ℝ} (hv : ContinuousOn v (Icc a b)) (hvx : ContinuousOn vx (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt v (vx x) x) :
    (v b - v a) ^ 2 ≤ (b - a) * ∫ x in a..b, vx x ^ 2 := by
  have hftc : ∫ x in a..b, vx x = v b - v a :=
    integral_eq_sub_of_hasDerivAt_of_le hab hv hd (hvx.intervalIntegrable_of_Icc hab)
  have hcs := intervalIntegral.sq_integral_mul_le_of_continuousOn hab (f := fun _ => (1 : ℝ))
    (g := vx) continuousOn_const hvx
  simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hcs
  rwa [hftc] at hcs

/-- **The Poincaré inequality on an interval, classical form.** Let $a \le b$, let $v$ and $v'$ be
continuous on $[a, b]$, let $v$ have the derivative $v'(x)$ at every $x \in (a, b)$, and let
$v(a) = 0$. Then
$$\int_a^b v(x)^2 \, dx \le \frac{(b - a)^2}{2} \int_a^b v'(x)^2 \, dx.$$

Since $v(y) = \int_a^y v'$, the Cauchy–Schwarz inequality gives
$v(y)^2 \le (y - a) \int_a^b (v')^2$, and $\int_a^b (y - a) \, dy = (b - a)^2/2$. The constant
is the square of the constant $C_P = (b - a)/\sqrt{2}$ in (12.16) of [quarteroni2000numerical]. -/
theorem intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero {a b : ℝ} (hab : a ≤ b)
    {v vx : ℝ → ℝ} (hv : ContinuousOn v (Icc a b)) (hvx : ContinuousOn vx (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt v (vx x) x) (hva : v a = 0) :
    (∫ x in a..b, v x ^ 2) ≤ (b - a) ^ 2 / 2 * ∫ x in a..b, vx x ^ 2 := by
  set K := ∫ x in a..b, vx x ^ 2 with hK
  have hbound : ∀ y ∈ Icc a b, v y ^ 2 ≤ (y - a) * K := by
    intro y hy
    have hcs := intervalIntegral.sq_sub_le_mul_integral_sq_of_hasDerivAt hy.1
      (hv.mono (Icc_subset_Icc le_rfl hy.2)) (hvx.mono (Icc_subset_Icc le_rfl hy.2))
      fun x hx => hd x ⟨hx.1, lt_of_lt_of_le hx.2 hy.2⟩
    rw [hva, sub_zero] at hcs
    have i1 : IntervalIntegrable (fun x => vx x ^ 2) volume a y :=
      ((hvx.mono (Icc_subset_Icc le_rfl hy.2)).pow 2).intervalIntegrable_of_Icc hy.1
    have i2 : IntervalIntegrable (fun x => vx x ^ 2) volume y b :=
      ((hvx.mono (Icc_subset_Icc hy.1 le_rfl)).pow 2).intervalIntegrable_of_Icc hy.2
    have h3 : (∫ x in a..y, vx x ^ 2) ≤ K := by
      have hsp : (∫ x in a..b, vx x ^ 2)
          = (∫ x in a..y, vx x ^ 2) + ∫ x in y..b, vx x ^ 2 :=
        (integral_add_adjacent_intervals i1 i2).symm
      have hnn : (0 : ℝ) ≤ ∫ x in y..b, vx x ^ 2 := integral_nonneg hy.2 fun x _ => sq_nonneg _
      rw [hK, hsp]
      linarith
    have hya : 0 ≤ y - a := sub_nonneg.2 hy.1
    nlinarith [hcs, h3, hya]
  have hint1 : IntervalIntegrable (fun x => v x ^ 2) volume a b :=
    (hv.pow 2).intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable (fun x => (x - a) * K) volume a b :=
    ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _
  have hmono := integral_mono_on hab hint1 hint2 hbound
  have hlin : (∫ x in a..b, (x - a) * K) = (b - a) ^ 2 / 2 * K := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      (continuous_id'.intervalIntegrable _ _) intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hlin] at hmono
  exact hmono

/-! ### Primitives, and the mean value theorems for integrals -/

namespace intervalIntegral

variable {a b t : ℝ} {K f : ℝ → ℝ}

/-- **The fundamental theorem of calculus** in the form that a comparison argument on $[a, b)$
needs. Let $p$ be continuous on $[a, b]$ and let $t \in [a, b)$. Then the primitive
$u \mapsto \int_a^u p(s) \, ds$ has the right derivative $p(t)$ at $t$. -/
theorem hasDerivWithinAt_integral_Ici {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b))
    (ht : t ∈ Ico a b) : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Ici t) t := by
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  have hint : IntervalIntegrable p volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (hp.mono (Icc_subset_Icc_right ht.2.le)).integrableOn_Icc
  have : Fact (t ∈ Icc a b) := ⟨ht'⟩
  have h : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Icc a b) t :=
    integral_hasDerivWithinAt_right hint
      (hp.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hp t ht')
  exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- If $p$ is continuous on $[a, b]$, then its primitive $u \mapsto \int_a^u p(s) \, ds$ is
continuous on $[a, b]$. -/
theorem continuousOn_integral_Icc {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b)) :
    ContinuousOn (fun u => ∫ s in a..u, p s) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · have h := continuousOn_primitive_interval (a := a) (b := b) (μ := volume) (f := p)
      (by rw [uIcc_of_le hab]; exact hp.integrableOn_Icc)
    rwa [uIcc_of_le hab] at h
  · simp [Icc_eq_empty_of_lt hab]

/-- **The weighted mean value theorem for integrals.** Let $a \le b$, let $K$ and $f$ be continuous
on $[a, b]$, and let $K \ge 0$ on $[a, b]$. Then there is $\xi \in [a, b]$ with
$$\int_a^b K(t) f(t) \, dt = f(\xi) \int_a^b K(t) \, dt.$$

The integral lies between the extreme values of $f$ times $\int_a^b K$, and the intermediate
value theorem gives $\xi$. -/
theorem exists_integral_mul_eq_mul_integral (hab : a ≤ b) (hK : ContinuousOn K (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) :
    ∃ ξ ∈ Icc a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab
  have hlow : f p * ∫ t in a..b, K t ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * ∫ t in a..b, K t := by
    have := integral_mono_on hab hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hpq : uIcc p q ⊆ Icc a b := uIcc_subset_Icc hp hq
  obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_uIcc
    ((hf.mono hpq).mul continuousOn_const) (mem_uIcc_of_le hlow hhigh)
  exact ⟨ξ, hpq hξ, hξval.symm⟩

/-- Let $a < b$, let $K$ be continuous on $[a, b]$ with $K \ge 0$ on $[a, b]$, and let $K(c) > 0$
for some $c \in (a, b)$. Then $\int_a^b K > 0$. -/
theorem integral_pos_of_continuousOn_of_nonneg (hab : a < b) (hK : ContinuousOn K (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) {c : ℝ} (hc : c ∈ Ioo a b) (hKc : 0 < K c) :
    0 < ∫ t in a..b, K t := by
  have hcont : ContinuousAt K c :=
    hK.continuousAt (Icc_mem_nhds hc.1 hc.2)
  obtain ⟨δ, hδ, hδpos⟩ : ∃ δ > 0, ∀ t, |t - c| < δ → 0 < K t := by
    have := (hcont.eventually (lt_mem_nhds hKc))
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, h⟩ := this
    exact ⟨δ, hδ, fun t ht => h (by rwa [Real.dist_eq])⟩
  set ε := min δ (min (c - a) (b - c)) with hε
  have hε0 : 0 < ε := lt_min hδ (lt_min (by linarith [hc.1]) (by linarith [hc.2]))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεa : ε ≤ c - a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b - c := (min_le_right _ _).trans (min_le_right _ _)
  have hKint : IntervalIntegrable K volume a b := hK.intervalIntegrable_of_Icc hab.le
  have hsub : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable K volume u v :=
    fun u v hu huv hv => hKint.mono_set
      (by rw [uIcc_of_le huv, uIcc_of_le hab.le]; exact Icc_subset_Icc hu hv)
  have h1 : IntervalIntegrable K volume a (c - ε) := hsub _ _ le_rfl (by linarith) (by linarith)
  have h2 : IntervalIntegrable K volume (c - ε) (c + ε) :=
    hsub _ _ (by linarith) (by linarith) (by linarith)
  have h3 : IntervalIntegrable K volume (c + ε) b := hsub _ _ (by linarith) (by linarith) le_rfl
  rw [← integral_add_adjacent_intervals (h1.trans h2) h3,
    ← integral_add_adjacent_intervals h1 h2]
  have hmid : 0 < ∫ t in c - ε..c + ε, K t := by
    refine intervalIntegral_pos_of_pos_on h2 (fun t ht => hδpos t ?_) (by linarith)
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hleft : 0 ≤ ∫ t in a..c - ε, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨ht.1, by linarith [ht.2]⟩
  have hright : 0 ≤ ∫ t in c + ε..b, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨by linarith [ht.1], ht.2⟩
  linarith

/-- **The weighted mean value theorem, with $\xi$ in the open interval.** Let $a < b$, let $K$ and
$f$ be continuous on $[a, b]$, let $K \ge 0$ on $[a, b]$, and let $\int_a^b K > 0$. Then there
is $\xi \in (a, b)$ with
$$\int_a^b K(t) f(t) \, dt = f(\xi) \int_a^b K(t) \, dt.$$

If the mean value of $f$ lies strictly between the extreme values of $f$, the intermediate value
theorem gives an interior $\xi$. If it is equal to an extreme value, then $f$ takes that value
wherever $K \neq 0$, and $K \neq 0$ at some interior point because its integral is positive. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) (hKpos : 0 < ∫ t in a..b, K t) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  set I : ℝ := ∫ t in a..b, K t with hI
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab.le⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab.le
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab.le
  have hlow : f p * I ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab.le (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * I := by
    have := integral_mono_on hab.le hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  -- a continuous nonnegative function with zero integral vanishes inside
  have hvanish : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) → (∀ t ∈ Icc a b, 0 ≤ g t) →
      (∫ t in a..b, g t) = 0 → ∀ t ∈ Ioo a b, g t = 0 := by
    intro g hgc hg hgint t ht
    by_contra hne
    have hpos : 0 < g t := lt_of_le_of_ne (hg t (Ioo_subset_Icc_self ht)) (Ne.symm hne)
    exact absurd hgint (integral_pos_of_continuousOn_of_nonneg hab hgc hg ht hpos).ne'
  -- `K` is nonzero at some interior point, because its integral is positive
  obtain ⟨ξ₀, hξ₀, hKξ₀⟩ : ∃ ξ ∈ Ioo a b, K ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    have : (∫ t in a..b, K t) = 0 := by
      rw [integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
          fun t ht => hall t ht]
      simp
    exact absurd this hKpos.ne'
  -- an extreme value is attained where `K` does not vanish
  have hextreme : ∀ c, (∫ t in a..b, K t * f t) = f c * I → c ∈ Icc a b →
      ((∀ t ∈ Icc a b, f c ≤ f t) ∨ ∀ t ∈ Icc a b, f t ≤ f c) →
      ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * I := by
    intro c hc hcmem hext
    refine ⟨ξ₀, hξ₀, ?_⟩
    suffices hfξ : f ξ₀ = f c by rw [hfξ, hc]
    rcases hext with hext | hext
    · have e : (fun t => K t * (f t - f c)) = fun t => K t * f t - K t * f c := by
        funext t; ring
      have h := hvanish (fun t => K t * (f t - f c)) (hK.mul (hf.sub continuousOn_const))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub hKf (hKc (f c)), integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
    · have e : (fun t => K t * (f c - f t)) = fun t => K t * f c - K t * f t := by
        funext t; ring
      have h := hvanish (fun t => K t * (f c - f t)) (hK.mul (continuousOn_const.sub hf))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub (hKc (f c)) hKf, integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
  -- the mean value of `f` is either strictly between the extremes or one of them
  set μ : ℝ := (∫ t in a..b, K t * f t) / I with hμ
  have hμI : (∫ t in a..b, K t * f t) = μ * I := by
    rw [hμ, div_mul_cancel₀ _ hKpos.ne']
  have hpμ : f p ≤ μ := by rw [hμ, le_div_iff₀ hKpos]; exact hlow
  have hμq : μ ≤ f q := by rw [hμ, div_le_iff₀ hKpos]; exact hhigh
  rcases eq_or_lt_of_le hpμ with hpμ' | hpμ'
  · exact hextreme p (by rw [hμI, hpμ']) hp (Or.inl fun t ht => hmin ht)
  rcases eq_or_lt_of_le hμq with hμq' | hμq'
  · exact hextreme q (by rw [hμI, hμq']) hq (Or.inr fun t ht => hmax ht)
  -- strictly between: the intermediate value theorem on the open interval between `p` and `q`
  have hpq : p ≠ q := fun h => by rw [h] at hpμ'; linarith
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo hlt.le
      (hf.mono (Icc_subset_Icc hp.1 hq.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hp.1 hξ.1, lt_of_lt_of_le hξ.2 hq.2⟩, by rw [hμI, hξval]⟩
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo' hlt.le
      (hf.mono (Icc_subset_Icc hq.1 hp.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hq.1 hξ.1, lt_of_lt_of_le hξ.2 hp.2⟩, by rw [hμI, hξval]⟩

/-- **The weighted mean value theorem, with $\xi$ in the open interval**, for a nonpositive kernel.
Let $a < b$, let $K$ and $f$ be continuous on $[a, b]$, let $K \le 0$ on $[a, b]$, and let
$\int_a^b K < 0$. Then there is $\xi \in (a, b)$ with $\int_a^b K f = f(\xi) \int_a^b K$. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnp : ∀ t ∈ Icc a b, K t ≤ 0) (hKneg : (∫ t in a..b, K t) < 0) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  obtain ⟨ξ, hξ, h⟩ := exists_mem_Ioo_integral_mul_eq_mul_integral (K := fun t => -K t) hab
    hK.neg hf (fun t ht => neg_nonneg.2 (hKnp t ht)) (by rw [integral_neg]; linarith)
  refine ⟨ξ, hξ, ?_⟩
  have e : (fun t => -K t * f t) = fun t => -(K t * f t) := by funext t; ring
  rw [e, integral_neg, integral_neg] at h
  linarith

/-- Let $a \le b$, let $p$ be interval integrable on $[a, b]$ with $p \ge 0$ on $[a, b]$, and let
$\varepsilon > 0$. Then there is a continuous function $q \colon \mathbb{R} \to \mathbb{R}$ with
$q \ge 0$ everywhere and
$$\int_a^b |p(s) - q(s)| \, ds \le \varepsilon.$$

The proof applies the density of continuous functions in $L^1$
(`MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le`) to the restriction of $p$
to $(a, b]$, and then truncates at $0$. The truncation does not increase the distance to a
nonnegative function. -/
theorem exists_continuous_nonneg_integral_abs_sub_le {p : ℝ → ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ → ℝ, Continuous q ∧ (∀ s, 0 ≤ q s) ∧ ∫ s in a..b, |p s - q s| ≤ ε := by
  have hP : MeasureTheory.Integrable ((Ioc a b).indicator p) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp)
  obtain ⟨q₀, -, hq₀, hq₀c, hq₀i⟩ := hP.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨fun s => max (q₀ s) 0, hq₀c.max continuous_const, fun s => le_max_right _ _, ?_⟩
  have hpI : MeasureTheory.IntegrableOn p (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp
  have hqI : MeasureTheory.IntegrableOn (fun s => max (q₀ s) 0) (Ioc a b) volume :=
    (hq₀c.max continuous_const).integrableOn_Ioc
  calc ∫ s in a..b, |p s - max (q₀ s) 0|
      = ∫ s in Ioc a b, |p s - max (q₀ s) 0| := integral_of_le hab
    _ ≤ ∫ s in Ioc a b, ‖(Ioc a b).indicator p s - q₀ s‖ := by
        refine MeasureTheory.setIntegral_mono_on (hpI.sub hqI).abs
          (hP.sub hq₀i).norm.integrableOn measurableSet_Ioc fun s hs => ?_
        rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
        have h0 : 0 ≤ p s := hp0 s (Ioc_subset_Icc_self hs)
        calc |p s - max (q₀ s) 0| = |max (p s) 0 - max (q₀ s) 0| := by rw [max_eq_left h0]
          _ ≤ |p s - q₀ s| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ∫ s, ‖(Ioc a b).indicator p s - q₀ s‖ :=
        MeasureTheory.setIntegral_le_integral (hP.sub hq₀i).norm
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ε := hq₀

end intervalIntegral

/-!
### The fundamental theorem on $(0, T]$ with a limit at $0^+$, and integrability on $(0, \infty)$
-/

/-- **The fundamental theorem of calculus on $(0, T]$** for a function with a nonpositive continuous
derivative. Let $T > 0$, and let $\varphi, g \colon \mathbb{R} \to \mathbb{R}$ be such that, for
every $t > 0$, $\varphi$ has the derivative $-g(t)$ at $t$, $g(t) \ge 0$ and $\varphi(t) \ge 0$.
Let $g$ be continuous on $(0, \infty)$, and let $\varphi(t) \to L$ as $t \to 0^+$. Then $g$ is
integrable on $(0, T]$ and
$$\varphi(T) + \int_0^T g(t) \, dt = L.$$

The integrability comes from $\int_\varepsilon^T g = \varphi(\varepsilon) - \varphi(T) \le
\varphi(\varepsilon)$, which is bounded for small $\varepsilon > 0$. The identity comes from the
fundamental theorem of calculus with one-sided limits. Every energy identity of the heat
equation follows this pattern: integrate over $[\varepsilon, T]$, then let $\varepsilon \to 0$. -/
theorem integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg {φ g : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hφ : ∀ t, 0 < t → HasDerivAt φ (-(g t)) t) (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (hgc : ContinuousOn g (Ioi 0)) (hφ0 : ∀ t, 0 < t → 0 ≤ φ t)
    (hL : Tendsto φ (𝓝[>] 0) (𝓝 L)) :
    IntegrableOn g (Ioc 0 T) ∧ φ T + ∫ t in (0 : ℝ)..T, g t = L := by
  -- the identity on `[ε, T]`
  have hint : ∀ ε, 0 < ε → ε ≤ T → ∫ t in ε..T, g t = φ ε - φ T := by
    intro ε hε hεT
    have hI : IntervalIntegrable (fun t ↦ -(g t)) volume ε T :=
      (hgc.mono fun t ht ↦ by
        rw [uIcc_of_le hεT] at ht
        exact hε.trans_le ht.1).neg.intervalIntegrable
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ) (f' := fun t ↦ -(g t))
      (fun t ht ↦ hφ t (by
        rw [uIcc_of_le hεT] at ht
        exact hε.trans_le ht.1)) hI
    rw [intervalIntegral.integral_neg] at this
    linarith
  -- integrability on `(0, T]`
  have hgi : IntegrableOn g (Ioc 0 T) := by
    have hIoc : ∀ n : ℕ, IntegrableOn g (Ioc (T / (n + 1)) T) := fun n ↦ by
      have hpos : 0 < T / (n + 1) := by positivity
      exact (hgc.mono fun t (ht : t ∈ Icc _ T) ↦ hpos.trans_le ht.1).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have ha : Tendsto (fun n : ℕ ↦ T / (n + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
      rw [mul_zero] at this
      exact this.congr fun n ↦ mul_one_div T _
    have ha' : Tendsto (fun n : ℕ ↦ T / (n + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨ha, Eventually.of_forall fun n ↦
        (by positivity : (0 : ℝ) < T / (n + 1))⟩
    have hev : ∀ᶠ n : ℕ in atTop, φ (T / (n + 1)) ≤ L + 1 :=
      (hL.comp ha').eventually (Iic_mem_nhds (by linarith))
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := L + 1)
      (a := fun n : ℕ ↦ T / (n + 1)) hIoc ha (hev.mono fun n hn ↦ ?_)
    have hpos : 0 < T / (n + 1) := by positivity
    have hle' : T / (n + 1) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : ∫ x in Ioc (T / (n + 1)) T, ‖g x‖ = ∫ x in T / (n + 1)..T, g x := by
      rw [intervalIntegral.integral_of_le hle']
      exact setIntegral_congr_fun measurableSet_Ioc fun x hx ↦
        Real.norm_of_nonneg (hg0 x (hpos.trans hx.1))
    rw [h1, hint _ hpos hle']
    linarith [hφ0 T hT]
  refine ⟨hgi, ?_⟩
  -- the identity on `(0, T)` by the fundamental theorem of calculus with limits
  have hI : IntervalIntegrable (fun t ↦ -(g t)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact hgi.neg
  have hTl : Tendsto φ (𝓝[<] T) (𝓝 (φ T)) :=
    (hφ T hT).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT (f := φ)
    (f' := fun t ↦ -(g t)) (fun t ht ↦ hφ t ht.1) hI hL hTl
  rw [intervalIntegral.integral_neg] at this
  linarith

/-- **From bounded integrals on $(0, T]$ to integrability on $(0, \infty)$.** Let
$g \colon \mathbb{R} \to \mathbb{R}$ satisfy $g(t) \ge 0$ for $t > 0$, let $g$ be integrable on
$(0, T]$ for every $T > 0$, and let $\int_0^T g \le L$ for every $T > 0$. Then $g$ is integrable
on $(0, \infty)$ and $\int_{(0, \infty)} g \le L$. -/
theorem integrableOn_Ioi_and_integral_le_of_forall_integral_le {g : ℝ → ℝ} {L : ℝ}
    (hg0 : ∀ t, 0 < t → 0 ≤ g t) (hfi : ∀ T, 0 < T → IntegrableOn g (Ioc 0 T))
    (hle : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, g t ≤ L) :
    IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t ≤ L := by
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hgi : IntegrableOn g (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded L 0 (b := fun n : ℕ ↦ (n : ℝ) + 1)
      (fun n ↦ hfi ((n : ℝ) + 1) (by positivity)) hb (Eventually.of_forall fun n ↦ ?_)
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    refine (le_of_eq ?_).trans (hle ((n : ℝ) + 1) (by positivity))
    rw [intervalIntegral.integral_of_le hn, intervalIntegral.integral_of_le hn]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ Real.norm_of_nonneg (hg0 t ht.1)
  refine ⟨hgi, le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hgi hb)
    (Eventually.of_forall fun n ↦ hle ((n : ℝ) + 1) (by positivity))⟩

/-- The reparametrization $t \mapsto 1 - t$ of $[0, 1]$ preserves integrals:
$\int_0^1 g(1 - t) \, dt = \int_0^1 g(t) \, dt$ for every $g \colon \mathbb{R} \to \mathbb{R}$. -/
theorem _root_.intervalIntegral.integral_comp_one_sub (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, g (1 - t) = ∫ t in (0 : ℝ)..1, g t := by
  have := intervalIntegral.integral_comp_sub_left g (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at this
  exact this

/-- Translation of an integral over a half-line. Let $G$ be a real normed space, let
$\varphi \colon \mathbb{R} \to G$, and let $a \in \mathbb{R}$. Then
$$\int_{(0, \infty)} \varphi(a + s) \, ds = \int_{(a, \infty)} \varphi(t) \, dt.$$
-/
theorem integral_Ioi_comp_add_left {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : ℝ → G) (a : ℝ) : ∫ s in Ioi (0 : ℝ), φ (a + s) = ∫ t in Ioi a, φ t := by
  have h := integral_add_left_eq_self (μ := volume) (fun t ↦ (Ioi a).indicator φ t) a
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext s
  rw [← Set.indicator_comp_right (fun s ↦ a + s) (g := φ) (s := Ioi a),
    Set.preimage_const_add_Ioi, sub_self]
  rfl

/-- **The one-variable estimate behind the estimate on a strip.** Let
$f \colon \mathbb{R} \to \mathbb{R}$ be differentiable with a continuous derivative $f'$, let
$t > 0$, let $f(a) = 0$, and let $P \ge 1$. Let $I, J \subseteq (a, a + t)$ be sets with
$(a, s] \subseteq J$ for every $s \in I$. Then
$$\int_I |f(s)|^P \, ds \le t^P \int_J |f'(\tau)|^P \, d\tau,$$
as an inequality of lower Lebesgue integrals.

On $I$, $f(s) = \int_a^s f'$ is bounded by $\int_J |f'|$. Hölder's inequality
(`MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) bounds this by
$|J|^{1 - 1/P} (\int_J |f'|^P)^{1/P}$, and the measures of $I$ and $J$ are at most $t$. -/
theorem lintegral_enorm_rpow_le_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {a t : ℝ} (ht : 0 < t) (hfa : f a = 0) {I J : Set ℝ}
    (hI : I ⊆ Ioo a (a + t)) (hJ : J ⊆ Ioo a (a + t)) (hIJ : ∀ s ∈ I, Ioc a s ⊆ J)
    {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ s in I, ‖f s‖ₑ ^ P ≤ ENNReal.ofReal t ^ P * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hvol : volume (Ioo a (a + t)) = ENNReal.ofReal t := by
    rw [Real.volume_Ioo, add_sub_cancel_left]
  have hm : AEStronglyMeasurable f' (volume.restrict J) := hf'.aestronglyMeasurable
  -- Hölder on `J`
  have hH : ∫⁻ τ in J, ‖f' τ‖ₑ
      ≤ (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) ^ (1 / P) * ENNReal.ofReal t ^ (1 - 1 / P) := by
    have h1P : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hP
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict J) (f := f')
      (p := 1) (q := ENNReal.ofReal P) h1P hm
    rw [eLpNorm_one_eq_lintegral_enorm hm, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using hP0) ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hP0.le,
      ENNReal.toReal_one, div_one, Measure.restrict_apply_univ] at h
    refine h.trans ?_
    gcongr
    · rw [sub_nonneg, div_le_one hP0]
      exact hP
    · exact (measure_mono hJ).trans hvol.le
  -- the pointwise bound on `I`
  have hpt : ∀ s ∈ I, ‖f s‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
    intro s hs
    have has : a ≤ s := (hI hs).1.le
    have e : f s = ∫ τ in a..s, f' τ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hf τ)
        (hf'.intervalIntegrable _ _), hfa, sub_zero]
    have h1 : ‖f s‖ₑ ≤ ∫⁻ τ in J, ‖f' τ‖ₑ := by
      rw [e, intervalIntegral.integral_of_le has]
      exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set (hIJ s hs))
    calc ‖f s‖ₑ ^ P
        ≤ ((∫⁻ τ in J, ‖f' τ‖ₑ ^ P) ^ (1 / P) * ENNReal.ofReal t ^ (1 - 1 / P)) ^ P :=
          ENNReal.rpow_le_rpow (h1.trans hH) hP0.le
      _ = ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_cancel hP0.ne', ENNReal.rpow_one, mul_comm]
          congr 2
          field_simp
  calc ∫⁻ s in I, ‖f s‖ₑ ^ P
      ≤ ∫⁻ _ in I, ENNReal.ofReal t ^ (P - 1) * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal t ^ (P - 1) * (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) * volume I :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal t ^ (P - 1) * (∫⁻ τ in J, ‖f' τ‖ₑ ^ P) * ENNReal.ofReal t := by
        gcongr
        exact (measure_mono hI).trans hvol.le
    _ = ENNReal.ofReal t ^ P * ∫⁻ τ in J, ‖f' τ‖ₑ ^ P := by
        have e : ENNReal.ofReal t ^ P = ENNReal.ofReal t * ENNReal.ofReal t ^ (P - 1) := by
          conv_lhs => rw [show P = 1 + (P - 1) by ring]
          rw [ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top, ENNReal.rpow_one]
        rw [e]
        ring

/-! ### Polynomials -/

/-- Let $u < v$ and let $p$ be a real polynomial. If $\int_u^v p(s)^2 \, ds = 0$, then $p = 0$. -/
theorem Polynomial.eq_zero_of_integral_mul_self_eq_zero {u v : ℝ} (huv : u < v) {p : Polynomial ℝ}
    (h : ∫ s in u..v, p.eval s * p.eval s = 0) : p = 0 := by
  by_contra hp
  -- a nonzero polynomial does not vanish on the whole interval
  have hroot : ∃ c ∈ Icc u v, p.eval c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hp (p.eq_zero_of_infinite_isRoot ((Icc_infinite huv).mono fun c hc => hall c hc))
  obtain ⟨c, hc, hc0⟩ := hroot
  have hpos : 0 < ∫ s in u..v, p.eval s * p.eval s :=
    integral_pos huv (p.continuous.mul p.continuous).continuousOn
      (fun s _ => mul_self_nonneg _) ⟨c, hc, mul_self_pos.2 hc0⟩
  exact hpos.ne' h
