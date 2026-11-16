/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.MeanInequalities
import Numlib.Variational.Minimization

/-!
# The energy of the regularized $p$-Laplacian

For $1 < p < \infty$, the boundary value problem
$$-\operatorname{div}\bigl[(1 + |\nabla u|^2)^{p/2 - 1} \nabla u\bigr] = f \text{ in } \Omega,
  \qquad u = 0 \text{ on } \partial\Omega,$$
of (8.8.1)–(8.8.2) of [han2009theoretical] is the Euler equation of the energy
$$E(v) = \frac1p \int_\Omega (1 + |\nabla v|^2)^{p/2} \, dx - \langle f, v \rangle \qquad (8.8.10)$$
on $W_0^{1,p}(\Omega)$. This module studies the integral term with the gradient replaced by a
general function. The **kernel** is $\rho_p(\xi) = (1 + \|\xi\|^2)^{p/2}$ on a real inner product
space $F$, and the **energy** is $\Phi_p(G) = \int \rho_p(G(x)) \, d\mu(x)$ for $G \in L^p(\mu; F)$
on a finite measure space. The properties of $E$ that §8.8 of [han2009theoretical] needs are
properties of $\Phi_p$ composed with the bounded linear injective map $v \mapsto \nabla v$.

The bounds $\|\xi\|^p \le \rho_p(\xi) \le 2^p(1 + \|\xi\|^p)$ give the integrability of
$\rho_p \circ G$, the lower bound $\int \|G\|^p \, d\mu \le \Phi_p(G)$ behind the coercivity of
Lemma 8.8.1, and the upper bound $\Phi_p(G) \le 2^p(\mu(X) + \int \|G\|^p \, d\mu)$ behind the
continuity of Lemma 8.8.2. The kernel is strictly convex for $p > 1$, which gives the strict
convexity of $\Phi_p$ of Lemma 8.8.3. The Gâteaux derivative of Lemma 8.8.4 is
$$\frac{d}{dt} \Phi_p(G + tH) \Big|_{t = 0} = p \int (1 + \|G\|^2)^{p/2 - 1} \langle G, H \rangle \,
  d\mu.$$

## Main definitions

* `PLaplacian.kernel`: the kernel $\rho_p(\xi) = (1 + \|\xi\|^2)^{p/2}$.
* `PLaplacian.derivWeight`: the weight $(1 + \|\xi\|^2)^{p/2 - 1}$ of the derivative of the kernel.
* `PLaplacian.kernelBound`: the bound $(1 + s^2)^{(p - 1)/2}$ on the derivative of the kernel.
* `PLaplacian.energy`: the energy $\Phi_p(G) = \int \rho_p(G(x)) \, d\mu(x)$.

## Main results

* `PLaplacian.norm_rpow_le_kernel`, `PLaplacian.kernel_le`: $\|\xi\|^p \le \rho_p(\xi) \le 2^p(1 +
  \|\xi\|^p)$ for $p \ge 0$.
* `PLaplacian.strictConvexOn_kernel`: $\rho_p$ is strictly convex for $p > 1$.
* `PLaplacian.integrable_kernel_comp`: $\rho_p \circ G$ is integrable for $G \in L^p$.
* `PLaplacian.integral_norm_rpow_le_energy`, `PLaplacian.energy_le`: the lower and upper bounds of
  $\Phi_p$.
* `PLaplacian.energy_combo_le`, `PLaplacian.energy_combo_lt`: $\Phi_p$ is convex, and strictly
  convex along two functions that differ on a set of positive measure.
* `PLaplacian.hasDerivAt_energy_line`: the Gâteaux derivative of $\Phi_p$.
* `PLaplacian.memLp_derivWeight_mul`: for a real function $g$ with $|g| \le \|G\|$, the function
  $(1 + \|G\|^2)^{p/2 - 1} g$ lies in $L^{p'}$, so the derivative is a bounded functional of
  $H \in L^p$.

## Proof outline

The kernel is $\rho_p(\xi) = \|(1, \xi)\|^p$ for the $\ell^2$ norm on $\mathbb{R} \times F$, and
$\|\cdot\|^p$ is strictly convex on a strictly convex space for $p > 1$; this gives the strict
convexity. The continuity of Lemma 8.8.2 follows from the upper bound, because a convex function
that is bounded above near every point is continuous (`ConvexOn.continuousOn_tfae`). The derivative
is computed by dominated convergence, with the dominating function
$p (1 + (\|G\| + \|H\|)^2)^{(p - 1)/2} \|H\|$, which is integrable by Young's inequality.

## Implementation notes

* The exponent is a real number $p$ in the pointwise statements, and `p : ℝ≥0∞` with `p.toReal` in
  the statements about integrals, as `MeasureTheory.MemLp` requires.
* The strict convexity of $\|\cdot\|^p$ is `strictConvexOn_norm_rpow` of
  `Numlib.Analysis.Convex.StrictConvexSpace`.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal InnerProductSpace Topology

noncomputable section

namespace PLaplacian

/-! ### The kernel $\rho_p(\xi) = (1 + \|\xi\|^2)^{p/2}$ -/

section Kernel

variable {F : Type*} [NormedAddCommGroup F]

/-- **The kernel** of the energy (8.8.10) of the regularized $p$-Laplacian: for a real exponent $p$
and $\xi$ in a normed space $F$,
$$\rho_p(\xi) = (1 + \|\xi\|^2)^{p/2}.$$
-/
def kernel (p : ℝ) (ξ : F) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (p / 2)

/-- The kernel is positive: $\rho_p(\xi) > 0$ for every real $p$ and every $\xi$. -/
theorem kernel_pos (p : ℝ) (ξ : F) : 0 < kernel p ξ :=
  Real.rpow_pos_of_pos (by positivity) _

/-- The kernel is nonnegative: $\rho_p(\xi) \ge 0$ for every real $p$ and every $\xi$. -/
theorem kernel_nonneg (p : ℝ) (ξ : F) : 0 ≤ kernel p ξ := (kernel_pos p ξ).le

/-- For every real $p$, the kernel $\rho_p$ is continuous. -/
theorem continuous_kernel (p : ℝ) : Continuous (kernel p : F → ℝ) :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦
    Or.inl (show (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 by positivity)

/-- For $p \ge 0$ and every $\xi$, $\|\xi\|^p \le \rho_p(\xi)$, because the term $1$ only increases
the base. -/
theorem norm_rpow_le_kernel {p : ℝ} (hp : 0 ≤ p) (ξ : F) : ‖ξ‖ ^ p ≤ kernel p ξ := by
  have h : ‖ξ‖ ^ p = (‖ξ‖ ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [h, kernel]
  exact Real.rpow_le_rpow (by positivity) (by linarith [sq_nonneg ‖ξ‖]) (by positivity)

/-- For $p \ge 0$ and every $\xi$, $\rho_p(\xi) \le 2^p (1 + \|\xi\|^p)$, because
$1 + \|\xi\|^2 \le (1 + \|\xi\|)^2$. -/
theorem kernel_le {p : ℝ} (hp : 0 ≤ p) (ξ : F) : kernel p ξ ≤ 2 ^ p * (1 + ‖ξ‖ ^ p) := by
  have h1 : kernel p ξ ≤ (1 + ‖ξ‖) ^ p := by
    have e : (1 + ‖ξ‖) ^ p = ((1 + ‖ξ‖) ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    rw [e, kernel]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg ξ]) (by positivity)
  exact h1.trans (Real.one_add_rpow_le (norm_nonneg ξ) hp)

/-- For every real $p$, the kernel is $\rho_p(\xi) = \|(1, \xi)\|^p$, with the $\ell^2$ norm on
$\mathbb{R} \times F$. -/
theorem kernel_eq_norm_rpow (p : ℝ) (ξ : F) :
    kernel p ξ = ‖WithLp.toLp 2 ((1 : ℝ), ξ)‖ ^ p := by
  have h : ‖WithLp.toLp 2 ((1 : ℝ), ξ)‖ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp
  rw [kernel, ← h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

variable [InnerProductSpace ℝ F]

/-- **The kernel is strictly convex.** Let $F$ be a real inner product space and $p > 1$. Then
$\rho_p$ is strictly convex on $F$. This is Exercise 5.3.13 of [han2009theoretical], the
pointwise part of Lemma 8.8.3.

The kernel is $\rho_p(\xi) = \|(1, \xi)\|^p$ on the strictly convex space $\mathbb{R} \times F$
with the $\ell^2$ norm, and $\xi \mapsto (1, \xi)$ is injective and affine. -/
theorem strictConvexOn_kernel {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ univ (kernel p : F → ℝ) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab ↦ ?_⟩
  have h := (strictConvexOn_norm_rpow (V := WithLp 2 (ℝ × F)) hp).2
    (mem_univ (WithLp.toLp 2 (1, x)))
    (mem_univ (WithLp.toLp 2 (1, y))) (fun h ↦ hxy (by simpa using congrArg (fun z ↦ z.snd) h))
    ha hb hab
  have e : a • WithLp.toLp 2 ((1 : ℝ), x) + b • WithLp.toLp 2 ((1 : ℝ), y)
      = WithLp.toLp 2 ((1 : ℝ), a • x + b • y) := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
    congr 1
    ext
    · simp [hab]
    · simp
  rw [e] at h
  simpa only [kernel_eq_norm_rpow, smul_eq_mul] using h

/-- Let $F$ be a real inner product space and $p \ge 1$. Then $\rho_p$ is convex on $F$. -/
theorem convexOn_kernel {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ univ (kernel p : F → ℝ) := by
  rcases hp.lt_or_eq with h | h
  · exact (strictConvexOn_kernel h).convexOn
  · subst h
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    simp only [kernel_eq_norm_rpow, Real.rpow_one, smul_eq_mul]
    have e : a • WithLp.toLp 2 ((1 : ℝ), x) + b • WithLp.toLp 2 ((1 : ℝ), y)
        = WithLp.toLp 2 ((1 : ℝ), a • x + b • y) := by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
      congr 1
      ext
      · simp [hab]
      · simp
    rw [← e]
    calc ‖a • WithLp.toLp 2 ((1 : ℝ), x) + b • WithLp.toLp 2 ((1 : ℝ), y)‖
        ≤ ‖a • WithLp.toLp 2 ((1 : ℝ), x)‖ + ‖b • WithLp.toLp 2 ((1 : ℝ), y)‖ := norm_add_le _ _
      _ = a * ‖WithLp.toLp 2 ((1 : ℝ), x)‖ + b * ‖WithLp.toLp 2 ((1 : ℝ), y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

/-! ### The derivative of the kernel along a line, and its bound -/

/-- The weight $w_p(\xi) = (1 + \|\xi\|^2)^{p/2 - 1}$ of the derivative of the kernel. It is the
coefficient of the regularized $p$-Laplacian $-\operatorname{div}\bigl[(1 + |\nabla u|^2)^{p/2 -
1} \nabla u\bigr]$. -/
def derivWeight (p : ℝ) (ξ : F) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (p / 2 - 1)

omit [InnerProductSpace ℝ F] in
/-- The weight is positive: $(1 + \|\xi\|^2)^{p/2 - 1} > 0$ for every real $p$ and every $\xi$. -/
theorem derivWeight_pos (p : ℝ) (ξ : F) : 0 < derivWeight p ξ :=
  Real.rpow_pos_of_pos (by positivity) _

omit [InnerProductSpace ℝ F] in
/-- For every real $p$, the weight $\xi \mapsto (1 + \|\xi\|^2)^{p/2 - 1}$ is continuous. -/
theorem continuous_derivWeight (p : ℝ) : Continuous (derivWeight p : F → ℝ) :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦
    Or.inl (show (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 by positivity)

/-- The bound $(1 + s^2)^{(p - 1)/2}$ on the derivative of the kernel at a point of norm $s$. -/
def kernelBound (p s : ℝ) : ℝ := (1 + s ^ 2) ^ ((p - 1) / 2)

/-- The bound is positive: $(1 + s^2)^{(p - 1)/2} > 0$ for all real $p$ and $s$. -/
theorem kernelBound_pos (p s : ℝ) : 0 < kernelBound p s :=
  Real.rpow_pos_of_pos (by positivity) _

/-- For every real $p$, the bound $s \mapsto (1 + s^2)^{(p - 1)/2}$ is continuous. -/
theorem continuous_kernelBound (p : ℝ) : Continuous (kernelBound p) :=
  (continuous_const.add (continuous_id.pow 2)).rpow_const fun s ↦
    Or.inl (show (1 + s ^ 2 : ℝ) ≠ 0 by positivity)

/-- For $p \ge 1$ and $0 \le s \le t$, $(1 + s^2)^{(p - 1)/2} \le (1 + t^2)^{(p - 1)/2}$. -/
theorem kernelBound_le_kernelBound {p s t : ℝ} (hp : 1 ≤ p) (hs : 0 ≤ s) (hst : s ≤ t) :
    kernelBound p s ≤ kernelBound p t :=
  Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)

/-- Let $p$ and $q$ be Hölder conjugate exponents: $p, q > 0$ and $1/p + 1/q = 1$. Then for every
real $s$, the $q$-th power of the bound is the kernel of $s$:
$$\bigl((1 + s^2)^{(p - 1)/2}\bigr)^q = (1 + s^2)^{p/2}.$$
-/
theorem kernelBound_rpow_conj {p q s : ℝ} (hpq : p.HolderConjugate q) :
    kernelBound p s ^ q = kernel p (s : ℝ) := by
  rw [kernelBound, kernel, ← Real.rpow_mul (by positivity), Real.norm_eq_abs, sq_abs]
  congr 1
  have h := hpq.sub_one_mul_conj
  field_simp
  linarith

/-- **The derivative of the kernel along a line.** Let $F$ be a real inner product space,
$p \in \mathbb{R}$ and $\xi, \eta \in F$. Then for every $t \in \mathbb{R}$
$$\frac{d}{dt} \rho_p(\xi + t\eta) = p \, (1 + \|\xi + t\eta\|^2)^{p/2 - 1} \langle \xi + t\eta,
  \eta \rangle.$$
-/
theorem hasDerivAt_kernel_line (p : ℝ) (ξ η : F) (t : ℝ) :
    HasDerivAt (fun s ↦ kernel p (ξ + s • η))
      (p * derivWeight p (ξ + t • η) * ⟪ξ + t • η, η⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s ↦ ξ + s • η) η t := by
    simpa using ((hasDerivAt_id t).smul_const η).const_add ξ
  have h2 : HasDerivAt (fun s ↦ 1 + ‖ξ + s • η‖ ^ 2) (2 * ⟪ξ + t • η, η⟫_ℝ) t := by
    simpa using h1.norm_sq.const_add 1
  have h3 := h2.rpow_const (p := p / 2) (Or.inl (by positivity))
  refine h3.congr_deriv ?_
  rw [derivWeight]
  ring

omit [InnerProductSpace ℝ F] in
/-- For every real $p$ and every $\zeta$, $(1 + \|\zeta\|^2)^{p/2 - 1} \|\zeta\| \le (1 +
\|\zeta\|^2)^{(p - 1)/2}$. -/
theorem derivWeight_mul_norm_le (p : ℝ) (ζ : F) :
    derivWeight p ζ * ‖ζ‖ ≤ kernelBound p ‖ζ‖ := by
  have hw := derivWeight_pos p ζ
  have hnorm : ‖ζ‖ ≤ (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc ‖ζ‖ = √(‖ζ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(1 + ‖ζ‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
  calc derivWeight p ζ * ‖ζ‖ ≤ derivWeight p ζ * (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hnorm hw.le
    _ = kernelBound p ‖ζ‖ := by
      rw [derivWeight, kernelBound, ← Real.rpow_add (by positivity)]
      congr 1
      ring

/-- Let $F$ be a real inner product space and $p \ge 0$. Then for all $\zeta, \eta \in F$
$$\bigl|p \, (1 + \|\zeta\|^2)^{p/2 - 1} \langle \zeta, \eta \rangle\bigr| \le p \, (1 +
  \|\zeta\|^2)^{(p - 1)/2} \|\eta\|,$$
because $\|\zeta\| \le (1 + \|\zeta\|^2)^{1/2}$. This bounds the derivative of the kernel. -/
theorem abs_derivWeight_mul_inner_le {p : ℝ} (hp : 0 ≤ p) (ζ η : F) :
    |p * derivWeight p ζ * ⟪ζ, η⟫_ℝ| ≤ p * kernelBound p ‖ζ‖ * ‖η‖ := by
  have hw := derivWeight_pos p ζ
  have hkey := derivWeight_mul_norm_le p ζ
  calc |p * derivWeight p ζ * ⟪ζ, η⟫_ℝ| = p * derivWeight p ζ * |⟪ζ, η⟫_ℝ| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ p * derivWeight p ζ * (‖ζ‖ * ‖η‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ζ η) (by positivity)
    _ = p * (derivWeight p ζ * ‖ζ‖) * ‖η‖ := by ring
    _ ≤ p * kernelBound p ‖ζ‖ * ‖η‖ := by gcongr

end Kernel

/-! ### The energy $\Phi_p(G) = \int \rho_p(G(x)) \, d\mu(x)$ -/

section Energy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Type*} [NormedAddCommGroup F]
  {p : ℝ≥0∞} {G H : X → F}

/-- **The energy** of a function $G : X \to F$ on a measure space $(X, \mu)$, for
$p \in [0, \infty]$:
$$\Phi_p(G) = \int (1 + \|G(x)\|^2)^{p/2} \, d\mu(x).$$
With $G = \nabla v$ this is the integral term of (8.8.10) of [han2009theoretical].

The exponent is `p.toReal`, so $p = \infty$ gives the exponent $0$. The integral is the Bochner
integral, which is $0$ when the integrand is not integrable. -/
def energy (p : ℝ≥0∞) (μ : Measure X) (G : X → F) : ℝ := ∫ x, kernel p.toReal (G x) ∂μ

/-- For every real $r$, if $G$ is almost everywhere strongly measurable, then so is
$x \mapsto \rho_r(G(x))$. -/
theorem aestronglyMeasurable_kernel_comp (r : ℝ) (hG : AEStronglyMeasurable G μ) :
    AEStronglyMeasurable (fun x ↦ kernel r (G x)) μ :=
  (continuous_kernel r).comp_aestronglyMeasurable hG

/-- **The kernel of an $L^p$ function is integrable.** Let $\mu$ be a finite measure,
$1 \le p < \infty$, and $G \in L^p(\mu; F)$. Then $x \mapsto \rho_p(G(x))$ is integrable. This
is Exercise 8.8.2 of [han2009theoretical].

It follows from $\rho_p(\xi) \le 2^p (1 + \|\xi\|^p)$. -/
theorem integrable_kernel_comp [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hG : MemLp G p μ) :
    Integrable (fun x ↦ kernel p.toReal (G x)) μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hint : Integrable (fun x ↦ 2 ^ p.toReal * (1 + ‖G x‖ ^ p.toReal)) μ :=
    ((integrable_const (1 : ℝ)).add (hG.integrable_norm_rpow hp0 hp')).const_mul _
  refine hint.mono' (aestronglyMeasurable_kernel_comp _ hG.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (kernel_nonneg _ _)]
  exact kernel_le ENNReal.toReal_nonneg _

/-- The energy is nonnegative: $\Phi_p(G) \ge 0$ for every $p$, every measure $\mu$ and every
function $G$. -/
theorem energy_nonneg (p : ℝ≥0∞) (μ : Measure X) (G : X → F) : 0 ≤ energy p μ G :=
  integral_nonneg fun _ ↦ kernel_nonneg _ _

/-- **The lower bound behind coercivity.** Let $\mu$ be a finite measure, $1 \le p < \infty$, and
$G \in L^p(\mu; F)$. Then
$$\int \|G\|^p \, d\mu \le \Phi_p(G).$$
This is the estimate behind the coercivity of Lemma 8.8.1 of [han2009theoretical]. -/
theorem integral_norm_rpow_le_energy [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hG : MemLp G p μ) : ∫ x, ‖G x‖ ^ p.toReal ∂μ ≤ energy p μ G :=
  integral_mono (hG.integrable_norm_rpow (zero_lt_one.trans_le hp).ne' hp')
    (integrable_kernel_comp hp hp' hG) fun _ ↦ norm_rpow_le_kernel ENNReal.toReal_nonneg _

/-- **The upper bound behind continuity.** Let $\mu$ be a finite measure on $X$, $1 \le p < \infty$,
and $G \in L^p(\mu; F)$. Then
$$\Phi_p(G) \le 2^p \Bigl(\mu(X) + \int \|G\|^p \, d\mu\Bigr).$$
This is the estimate behind the continuity of Lemma 8.8.2 of [han2009theoretical]. -/
theorem energy_le [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hG : MemLp G p μ) :
    energy p μ G ≤ 2 ^ p.toReal * (μ.real univ + ∫ x, ‖G x‖ ^ p.toReal ∂μ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hint := hG.integrable_norm_rpow hp0 hp'
  calc energy p μ G ≤ ∫ x, 2 ^ p.toReal * (1 + ‖G x‖ ^ p.toReal) ∂μ :=
        integral_mono (integrable_kernel_comp hp hp' hG)
          (((integrable_const (1 : ℝ)).add hint).const_mul _)
          fun x ↦ kernel_le ENNReal.toReal_nonneg _
    _ = 2 ^ p.toReal * (μ.real univ + ∫ x, ‖G x‖ ^ p.toReal ∂μ) := by
        rw [integral_const_mul, integral_add (integrable_const _) hint, integral_const,
          smul_eq_mul, mul_one]

variable [InnerProductSpace ℝ F]

/-- **Convexity of the energy.** Let $F$ be a real inner product space, $\mu$ a finite measure,
$1 \le p < \infty$, and $G, H \in L^p(\mu; F)$. Then for $a, b \ge 0$ with $a + b = 1$
$$\Phi_p(aG + bH) \le a \, \Phi_p(G) + b \, \Phi_p(H).$$
This is the convexity half of Lemma 8.8.3 of [han2009theoretical]. -/
theorem energy_combo_le [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hG : MemLp G p μ)
    (hH : MemLp H p μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    energy p μ (a • G + b • H) ≤ a * energy p μ G + b * energy p μ H := by
  have hr : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have hGH : MemLp (a • G + b • H) p μ := (hG.const_smul a).add (hH.const_smul b)
  calc energy p μ (a • G + b • H)
      ≤ ∫ x, (a * kernel p.toReal (G x) + b * kernel p.toReal (H x)) ∂μ := by
        refine integral_mono (integrable_kernel_comp hp hp' hGH)
          (((integrable_kernel_comp hp hp' hG).const_mul a).add
            ((integrable_kernel_comp hp hp' hH).const_mul b)) fun x ↦ ?_
        have := (convexOn_kernel hr).2 (mem_univ (G x)) (mem_univ (H x)) ha hb hab
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    _ = a * energy p μ G + b * energy p μ H := by
        rw [integral_add ((integrable_kernel_comp hp hp' hG).const_mul a)
          ((integrable_kernel_comp hp hp' hH).const_mul b), integral_const_mul, integral_const_mul]
        rfl

/-- **Strict convexity of the energy.** Let $F$ be a real inner product space, $\mu$ a finite
measure, $1 < p < \infty$, and $G, H \in L^p(\mu; F)$ such that $G \neq H$ on a set of positive
measure. Then for $a, b > 0$ with $a + b = 1$
$$\Phi_p(aG + bH) < a \, \Phi_p(G) + b \, \Phi_p(H).$$
This is Lemma 8.8.3 of [han2009theoretical].

The pointwise gap $a \rho_p(G(x)) + b \rho_p(H(x)) - \rho_p(aG(x) + bH(x))$ is nonnegative, and
it is positive where $G(x) \neq H(x)$, so its integral is positive
(`integral_pos_iff_support_of_nonneg`). -/
theorem energy_combo_lt [IsFiniteMeasure μ] (hp : 1 < p) (hp' : p ≠ ⊤) (hG : MemLp G p μ)
    (hH : MemLp H p μ) (hne : ¬ G =ᵐ[μ] H) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    energy p μ (a • G + b • H) < a * energy p μ G + b * energy p μ H := by
  have hp1 : 1 ≤ p := hp.le
  have hr : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp').2 hp
  have hGH : MemLp (a • G + b • H) p μ := (hG.const_smul a).add (hH.const_smul b)
  have hIG := integrable_kernel_comp hp1 hp' hG
  have hIH := integrable_kernel_comp hp1 hp' hH
  have hIGH := integrable_kernel_comp hp1 hp' hGH
  -- the pointwise gap
  have hD0 : ∀ x, 0 ≤ a * kernel p.toReal (G x) + b * kernel p.toReal (H x)
      - kernel p.toReal ((a • G + b • H) x) := fun x ↦ by
    have := (convexOn_kernel hr.le).2 (mem_univ (G x)) (mem_univ (H x)) ha.le hb.le hab
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at this ⊢
    linarith
  have h12 : Integrable (fun x ↦ a * kernel p.toReal (G x) + b * kernel p.toReal (H x)) μ :=
    (hIG.const_mul a).add (hIH.const_mul b)
  have hDint : Integrable (fun x ↦ a * kernel p.toReal (G x) + b * kernel p.toReal (H x)
      - kernel p.toReal ((a • G + b • H) x)) μ := h12.sub hIGH
  have hsupp : {x | G x ≠ H x} ⊆ Function.support fun x ↦ a * kernel p.toReal (G x)
      + b * kernel p.toReal (H x) - kernel p.toReal ((a • G + b • H) x) := by
    intro x hx
    have := (strictConvexOn_kernel hr).2 (mem_univ (G x)) (mem_univ (H x)) hx ha hb hab
    simp only [smul_eq_mul] at this
    simp only [Function.mem_support, Pi.add_apply, Pi.smul_apply]
    linarith
  have hpos : 0 < μ (Function.support fun x ↦ a * kernel p.toReal (G x)
      + b * kernel p.toReal (H x) - kernel p.toReal ((a • G + b • H) x)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [pos_iff_ne_zero]
    intro h0
    exact hne (ae_iff.2 h0)
  have hint := (integral_pos_iff_support_of_nonneg hD0 hDint).2 hpos
  rw [integral_sub h12 hIGH, integral_add (hIG.const_mul a) (hIH.const_mul b), integral_const_mul,
    integral_const_mul] at hint
  change 0 < a * energy p μ G + b * energy p μ H - energy p μ (a • G + b • H) at hint
  linarith

end Energy

/-! ### The Gâteaux derivative of the energy -/

section Derivative

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {p : ℝ≥0∞} {G H : X → F}

/-- If $1 < p < \infty$ in $[0, \infty]$, then the real number `p.toReal` is greater than $1$. -/
theorem one_lt_toReal (hp : 1 < p) (hp' : p ≠ ⊤) : 1 < p.toReal := by
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp').2 hp

omit [InnerProductSpace ℝ F] in
/-- **The dominating function of Lemma 8.8.4 is integrable.** Let $F$ be a normed space, $\mu$ a
finite measure, $1 < p < \infty$, and $G, H \in L^p(\mu; F)$. Then
$$x \mapsto (1 + (\|G(x)\| + \|H(x)\|)^2)^{(p - 1)/2} \, \|H(x)\|$$
is integrable.

The proof uses Young's inequality $ab \le a^{p'}/p' + b^p/p$ with $a^{p'} = (1 + (\|G\| +
\|H\|)^2)^{p/2} \le 2^p(1 + (\|G\| + \|H\|)^p)$. The source states that the right-hand side is
in $L^1(\Omega)$ by the Hölder inequality. -/
theorem integrable_kernelBound_mul [IsFiniteMeasure μ] (hp : 1 < p) (hp' : p ≠ ⊤)
    (hG : MemLp G p μ) (hH : MemLp H p μ) :
    Integrable (fun x ↦ kernelBound p.toReal (‖G x‖ + ‖H x‖) * ‖H x‖) μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hr : 1 < p.toReal := one_lt_toReal hp hp'
  have hpq : p.toReal.HolderConjugate (Real.conjExponent p.toReal) :=
    Real.HolderConjugate.conjExponent hr
  have hq : 0 < Real.conjExponent p.toReal := hpq.symm.pos
  have hs : MemLp (fun x ↦ ‖G x‖ + ‖H x‖) p μ := hG.norm.add hH.norm
  have hsint : Integrable (fun x ↦ (‖G x‖ + ‖H x‖) ^ p.toReal) μ :=
    (hs.integrable_norm_rpow hp0 hp').congr (Eventually.of_forall fun x ↦ by
      simp only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))])
  have hHint : Integrable (fun x ↦ ‖H x‖ ^ p.toReal) μ := hH.integrable_norm_rpow hp0 hp'
  have hdom : Integrable (fun x ↦ 2 ^ p.toReal * (1 + (‖G x‖ + ‖H x‖) ^ p.toReal)
      / Real.conjExponent p.toReal + ‖H x‖ ^ p.toReal / p.toReal) μ :=
    ((((integrable_const (1 : ℝ)).add hsint).const_mul _).div_const _).add (hHint.div_const _)
  have hmeas : AEStronglyMeasurable (fun x ↦ kernelBound p.toReal (‖G x‖ + ‖H x‖) * ‖H x‖) μ :=
    ((continuous_kernelBound _).comp_aestronglyMeasurable hs.aestronglyMeasurable).mul
      hH.aestronglyMeasurable.norm
  refine hdom.mono' hmeas (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (kernelBound_pos _ _).le (norm_nonneg _))]
  calc kernelBound p.toReal (‖G x‖ + ‖H x‖) * ‖H x‖
      ≤ kernelBound p.toReal (‖G x‖ + ‖H x‖) ^ Real.conjExponent p.toReal
          / Real.conjExponent p.toReal + ‖H x‖ ^ p.toReal / p.toReal :=
        Real.young_inequality_of_nonneg (kernelBound_pos _ _).le (norm_nonneg _) hpq.symm
    _ ≤ 2 ^ p.toReal * (1 + (‖G x‖ + ‖H x‖) ^ p.toReal) / Real.conjExponent p.toReal
          + ‖H x‖ ^ p.toReal / p.toReal := by
        gcongr
        rw [kernelBound_rpow_conj hpq]
        have := kernel_le (F := ℝ) (zero_le_one.trans hr.le) (‖G x‖ + ‖H x‖)
        rwa [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at this

/-- **The Gâteaux derivative of the energy.** Let $F$ be a real inner product space, $\mu$ a finite
measure, $1 < p < \infty$, and $G, H \in L^p(\mu; F)$. Then $t \mapsto \Phi_p(G + tH)$ is
differentiable at $t = 0$, with
$$\frac{d}{dt} \Phi_p(G + tH) \Big|_{t = 0} = p \int (1 + \|G\|^2)^{p/2 - 1} \langle G, H
  \rangle \, d\mu.$$
This is Lemma 8.8.4 of [han2009theoretical], the integral term of (8.8.11).

The proof is dominated convergence (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on
$|t| < 1$, with the dominating function $p (1 + (\|G\| + \|H\|)^2)^{(p - 1)/2} \|H\|$ of
`PLaplacian.integrable_kernelBound_mul`. -/
theorem hasDerivAt_energy_line [IsFiniteMeasure μ] (hp : 1 < p) (hp' : p ≠ ⊤) (hG : MemLp G p μ)
    (hH : MemLp H p μ) :
    HasDerivAt (fun t : ℝ ↦ energy p μ (G + t • H))
      (∫ x, p.toReal * derivWeight p.toReal (G x) * ⟪G x, H x⟫_ℝ ∂μ) 0 := by
  have hr : 1 < p.toReal := one_lt_toReal hp hp'
  have hr0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hGm := hG.aestronglyMeasurable
  have hHm := hH.aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (s := ball 0 1) (F := fun t x ↦ kernel p.toReal (G x + t • H x))
    (F' := fun t x ↦ p.toReal * derivWeight p.toReal (G x + t • H x) * ⟪G x + t • H x, H x⟫_ℝ)
    (bound := fun x ↦ p.toReal * (kernelBound p.toReal (‖G x‖ + ‖H x‖) * ‖H x‖))
    (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t ↦
      aestronglyMeasurable_kernel_comp _ (hGm.add (hHm.const_smul t)))
    ((integrable_kernel_comp hp.le hp' hG).congr (Eventually.of_forall fun x ↦ by simp))
    ((aestronglyMeasurable_const.mul ((continuous_derivWeight _).comp_aestronglyMeasurable
      (hGm.add (hHm.const_smul (0 : ℝ))))).mul
        (AEStronglyMeasurable.inner (hGm.add (hHm.const_smul (0 : ℝ))) hHm))
    (Eventually.of_forall fun x t ht ↦ ?_)
    ((integrable_kernelBound_mul hp hp' hG hH).const_mul _)
    (Eventually.of_forall fun x t _ ↦ hasDerivAt_kernel_line p.toReal (G x) (H x) t)
  · have h2 := key.2
    simp only [zero_smul, add_zero] at h2
    exact h2
  · -- the bound on the derivative for `|t| < 1`
    rw [Real.norm_eq_abs]
    refine (abs_derivWeight_mul_inner_le hr0 _ _).trans ?_
    rw [mul_assoc]
    gcongr
    refine kernelBound_le_kernelBound hr.le (norm_nonneg _) ?_
    calc ‖G x + t • H x‖ ≤ ‖G x‖ + ‖t • H x‖ := norm_add_le _ _
      _ = ‖G x‖ + |t| * ‖H x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖G x‖ + 1 * ‖H x‖ := by
        gcongr
        exact (mem_ball_zero_iff.1 ht).le
      _ = ‖G x‖ + ‖H x‖ := by rw [one_mul]

omit [InnerProductSpace ℝ F] in
/-- **The bound lies in $L^{p'}$.** Let $\mu$ be a finite measure, $1 < p < \infty$, $p'$ the
conjugate exponent, and $G \in L^p(\mu; F)$. Then $x \mapsto (1 + \|G(x)\|^2)^{(p - 1)/2}$ lies
in $L^{p'}(\mu)$.

Its $p'$-th power is $(1 + \|G\|^2)^{p/2}$, which is integrable. The exponent $p'$ is
`ENNReal.conjExponent p`. -/
theorem memLp_kernelBound [IsFiniteMeasure μ] (hp : 1 < p) (hp' : p ≠ ⊤) (hG : MemLp G p μ) :
    MemLp (fun x ↦ kernelBound p.toReal ‖G x‖) (ENNReal.conjExponent p) μ := by
  have hr : 1 < p.toReal := one_lt_toReal hp hp'
  have hconj : p.HolderConjugate (ENNReal.conjExponent p) := .conjExponent hp.le
  have hq1 : 1 ≤ ENNReal.conjExponent p := ENNReal.HolderConjugate.one_le _ p
  have hq0 : ENNReal.conjExponent p ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hqt : ENNReal.conjExponent p ≠ ⊤ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one _ p).2 hp.ne'
  have hqr : 0 < (ENNReal.conjExponent p).toReal := ENNReal.toReal_pos hq0 hqt
  have hrq : p.toReal.HolderConjugate (ENNReal.conjExponent p).toReal :=
    ENNReal.HolderTriple.toReal 1 (zero_lt_one.trans hr) hqr
  have hmeas : AEStronglyMeasurable (fun x ↦ kernelBound p.toReal ‖G x‖) μ :=
    (continuous_kernelBound _).comp_aestronglyMeasurable hG.aestronglyMeasurable.norm
  rw [← integrable_norm_rpow_iff hmeas hq0 hqt]
  refine (integrable_kernel_comp hp.le hp' hG).congr (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [Real.norm_of_nonneg (kernelBound_pos _ _).le, kernelBound_rpow_conj hrq]
  simp [kernel]

omit [InnerProductSpace ℝ F] in
/-- **The weight of the $p$-Laplacian lies in $L^{p'}$.** Let $\mu$ be a finite measure,
$1 < p < \infty$, $p'$ the conjugate exponent, $G \in L^p(\mu; F)$, and let
$g : X \to \mathbb{R}$ be almost everywhere strongly measurable with $|g(x)| \le \|G(x)\|$ for
all $x$. Then $x \mapsto (1 + \|G(x)\|^2)^{p/2 - 1} g(x)$ lies in $L^{p'}(\mu)$.

This makes $H \mapsto \int (1 + \|G\|^2)^{p/2 - 1} \langle G, H \rangle \, d\mu$ a bounded
functional of $H \in L^p$, which is the Gâteaux derivative of Lemma 8.8.4 of
[han2009theoretical] as an element of the dual space. -/
theorem memLp_derivWeight_mul [IsFiniteMeasure μ] (hp : 1 < p) (hp' : p ≠ ⊤) (hG : MemLp G p μ)
    {g : X → ℝ} (hg : AEStronglyMeasurable g μ) (hle : ∀ x, |g x| ≤ ‖G x‖) :
    MemLp (fun x ↦ derivWeight p.toReal (G x) * g x) (ENNReal.conjExponent p) μ := by
  refine (memLp_kernelBound hp hp' hG).of_le
    (((continuous_derivWeight _).comp_aestronglyMeasurable hG.aestronglyMeasurable).mul hg)
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (kernelBound_pos _ _).le, Real.norm_eq_abs, abs_mul,
    abs_of_pos (derivWeight_pos _ _)]
  calc derivWeight p.toReal (G x) * |g x| ≤ derivWeight p.toReal (G x) * ‖G x‖ :=
        mul_le_mul_of_nonneg_left (hle x) (derivWeight_pos _ _).le
    _ ≤ kernelBound p.toReal ‖G x‖ := derivWeight_mul_norm_le _ _

end Derivative

/-! ### Almost everywhere congruence -/

section Auxiliary

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Type*} [NormedAddCommGroup F]
  {p : ℝ≥0∞} {G H : X → F}

/-- The energy depends only on the almost everywhere class of the function: if $G = H$ almost
everywhere, then $\Phi_p(G) = \Phi_p(H)$. -/
theorem energy_congr_ae (p : ℝ≥0∞) (h : G =ᵐ[μ] H) : energy p μ G = energy p μ H :=
  integral_congr_ae (h.mono fun _ hx ↦ by simp only [hx])

end Auxiliary

end PLaplacian
