/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Integral operators with a square-integrable kernel

Let $\mu$ be an s-finite measure on a measurable space $X$, and let
$k \colon X \times X \to \mathbb{R}$ be square-integrable for the product measure $\mu \otimes \mu$.
Write $B = \left( \iint k(x, y)^2 \, d\mu(x) \, d\mu(y) \right)^{1/2}$ for the $L^2$ norm of the
kernel. The formula
$$(Kv)(x) = \int k(x, y) \, v(y) \, d\mu(y)$$
defines a bounded linear operator $K$ on $L^2(\mu)$ with $\|K\| \le B$, and the adjoint of $K$ is
the operator of the transposed kernel $k^T(x, y) = k(y, x)$. This is the classical Hilbert–Schmidt
integral operator of [han2009theoretical], Example 2.6.1 and §2.8.3; see also [kress1989linear], §4.

When $\mu$ is separable, the map $k \mapsto K$ is injective up to null sets. As a consequence, $K$
is self-adjoint if and only if $k(x, y) = k(y, x)$ for $\mu \otimes \mu$-almost every $(x, y)$.

## Main definitions

* `IntegralOperator.l2KernelCLM`: the bounded operator $K$ on $L^2(\mu)$ of a square-integrable
  kernel $k$.

## Main results

* `IntegralOperator.l2KernelCLM_apply_ae`: $(Kv)(x) = \int k(x, y) v(y) \, d\mu(y)$ for almost every
  $x$.
* `IntegralOperator.norm_l2KernelCLM_le`: $\|K\| \le B$.
* `IntegralOperator.adjoint_l2KernelCLM`: the adjoint of $K$ is the operator of the transposed
  kernel.
* `IntegralOperator.isSelfAdjoint_l2KernelCLM`: if $k$ is symmetric almost everywhere, then $K$ is
  self-adjoint.
* `IntegralOperator.ae_eq_zero_of_l2KernelCLM_eq_zero`: for a separable measure, $K = 0$ implies
  $k = 0$ almost everywhere.
* `IntegralOperator.isSelfAdjoint_l2KernelCLM_iff`: for a separable measure, $K$ is self-adjoint if
  and only if $k$ is symmetric almost everywhere.

## Proof outline

The Cauchy–Schwarz inequality on the row $k(x, \cdot)$ gives $|(Kv)(x)|^2 \le \left( \int k(x, y)^2
\, d\mu(y) \right) \|v\|^2$, and the Fubini theorem integrates the squared row norms to $B^2$. The
adjoint identity is the Fubini theorem for the double integral $\iint k(x, y) v(y) w(x)$. For the
injectivity, if $K = 0$, then almost every row of $k$ is orthogonal to a countable dense subset of
$L^2(\mu)$, so it is zero.

## Implementation notes

* An element of `Lp ℝ 2 μ` is an equivalence class of functions modulo null sets, so the defining
  formula of $K$ holds only almost everywhere.
* `IntegralOperator.norm_lp_eq_sqrt_integral_sq` and `MeasureTheory.L2.inner_eq_integral_mul` write
  the norm and the inner product of `Lp ℝ 2 μ` as ordinary integrals, and
  `MeasureTheory.abs_integral_mul_le_sqrt_mul_sqrt` is the Cauchy–Schwarz inequality for two
  square-integrable real functions. With these, the statements are integral inequalities, not
  statements about `eLpNorm`.
* The separability of $\mu$ is Mathlib's `MeasureTheory.IsSeparable`. It makes $L^2(\mu)$ separable.
  It holds when the σ-algebra of $X$ is countably generated, in particular for $L^2(a, b)$.
* The module `Numlib.IntegralEquations.Basic` defines a different operator: the integral operator of
  a continuous kernel on the space of continuous functions on a compact space. Its norm is the
  largest row integral $\max_x \int |k(x, y)| \, d\mu(y)$, not the $L^2$ norm of $k$.
-/

open Filter MeasureTheory Real

namespace IntegralOperator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- For $f \in L^2(\mu)$, the norm is the integral
$$\|f\| = \left( \int f(x)^2 \, d\mu(x) \right)^{1/2}.$$
-/
theorem norm_lp_eq_sqrt_integral_sq (f : Lp ℝ 2 μ) : ‖f‖ = √(∫ x, f x ^ 2 ∂μ) := by
  have h := real_inner_self_eq_norm_mul_norm f
  rw [MeasureTheory.L2.inner_def] at h
  have h2 : ∫ x, (inner ℝ (f x) (f x) : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq]
  rw [h2, ← sq] at h
  rw [h, Real.sqrt_sq (norm_nonneg f)]

/-! ### Rows of a square-integrable kernel -/

variable [SFinite μ] {k : X × X → ℝ}

/-- If $k \in L^2(\mu \otimes \mu)$, then for $\mu$-almost every $x$ the row $y \mapsto k(x, y)$ is
in $L^2(\mu)$. -/
theorem ae_memLp_row (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 μ := by
  filter_upwards [hk.aestronglyMeasurable.prodMk_left, hk.integrable_sq.prod_right_ae]
    with x hm hi using (memLp_two_iff_integrable_sq hm).2 hi

/-- If $k \in L^2(\mu \otimes \mu)$, then the squared row norm $x \mapsto \int k(x, y)^2 \, d\mu(y)$
is $\mu$-integrable. -/
theorem integrable_integral_sq_row (hk : MemLp k 2 (μ.prod μ)) :
    Integrable (fun x => ∫ y, k (x, y) ^ 2 ∂μ) μ :=
  hk.integrable_sq.integral_prod_left

/-- If $k \in L^2(\mu \otimes \mu)$, then
$$\int \left( \int k(x, y)^2 \, d\mu(y) \right) d\mu(x) = \int k^2 \, d(\mu \otimes \mu).$$
This is the Fubini theorem for $k^2$. The right side is $B^2$, the square of the bound in
Example 2.6.1 of [han2009theoretical]. -/
theorem integral_integral_sq (hk : MemLp k 2 (μ.prod μ)) :
    ∫ x, (∫ y, k (x, y) ^ 2 ∂μ) ∂μ = ∫ p, k p ^ 2 ∂(μ.prod μ) :=
  integral_integral hk.integrable_sq

/-- If $k \in L^2(\mu \otimes \mu)$, then the row norm $x \mapsto \left( \int k(x, y)^2 \, d\mu(y)
\right)^{1/2}$ is in $L^2(\mu)$. -/
theorem memLp_sqrt_integral_sq_row (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun x => √(∫ y, k (x, y) ^ 2 ∂μ)) 2 μ := by
  have hI := integrable_integral_sq_row hk
  have hmeas : AEStronglyMeasurable (fun x => √(∫ y, k (x, y) ^ 2 ∂μ)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hI.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 (hI.congr ?_)
  refine Filter.Eventually.of_forall fun x => ?_
  exact (Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)).symm

/-- If $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, then for $\mu$-almost every $x$ the
function $y \mapsto k(x, y) v(y)$ is $\mu$-integrable. -/
theorem ae_integrable_row_mul (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * v y) μ := by
  filter_upwards [ae_memLp_row hk] with x hx
  exact hx.integrable_mul hv

/-! ### The operator -/

/-- If $k \in L^2(\mu \otimes \mu)$ and $v$ is almost everywhere strongly measurable, then
$x \mapsto \int k(x, y) v(y) \, d\mu(y)$ is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_l2Kernel (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ}
    (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => ∫ y, k (x, y) * v y ∂μ) μ :=
  (hk.aestronglyMeasurable.mul hv.comp_snd).integral_prod_right'

/-- If $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, then for $\mu$-almost every $x$,
$$\left| \int k(x, y) v(y) \, d\mu(y) \right| \le \left( \int k(x, y)^2 \, d\mu(y) \right)^{1/2}
  \left( \int v^2 \, d\mu \right)^{1/2}.$$
This is the Cauchy–Schwarz inequality for the row $k(x, \cdot)$. -/
theorem abs_integral_row_mul_le (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∀ᵐ x ∂μ, |∫ y, k (x, y) * v y ∂μ| ≤ √(∫ y, k (x, y) ^ 2 ∂μ) * √(∫ y, v y ^ 2 ∂μ) := by
  filter_upwards [ae_memLp_row hk] with x hx
  exact MeasureTheory.abs_integral_mul_le_sqrt_mul_sqrt hx hv

/-- If $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, then for $\mu$-almost every $x$,
$$\left( \int k(x, y) v(y) \, d\mu(y) \right)^2 \le \left( \int k(x, y)^2 \, d\mu(y) \right)
  \int v^2 \, d\mu.$$
-/
theorem ae_sq_l2Kernel_le (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∀ᵐ x ∂μ, (∫ y, k (x, y) * v y ∂μ) ^ 2 ≤ (∫ y, k (x, y) ^ 2 ∂μ) * ∫ y, v y ^ 2 ∂μ := by
  filter_upwards [abs_integral_row_mul_le hk hv] with x hx
  have hA : (0 : ℝ) ≤ ∫ y, k (x, y) ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  have hB : (0 : ℝ) ≤ ∫ y, v y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  calc (∫ y, k (x, y) * v y ∂μ) ^ 2 = |∫ y, k (x, y) * v y ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (√(∫ y, k (x, y) ^ 2 ∂μ) * √(∫ y, v y ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hx 2
    _ = (∫ y, k (x, y) ^ 2 ∂μ) * ∫ y, v y ^ 2 ∂μ := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- If $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, then
$x \mapsto \int k(x, y) v(y) \, d\mu(y)$ is in $L^2(\mu)$. -/
theorem memLp_l2Kernel (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    MemLp (fun x => ∫ y, k (x, y) * v y ∂μ) 2 μ := by
  have hmeas := aestronglyMeasurable_l2Kernel hk hv.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' ((integrable_integral_sq_row hk).mul_const (∫ y, v y ^ 2 ∂μ))
    (hmeas.pow 2) ?_
  filter_upwards [ae_sq_l2Kernel_le hk hv] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

/-- If $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, then
$$\int \left( \int k(x, y) v(y) \, d\mu(y) \right)^2 d\mu(x) \le \left( \int k^2 \, d(\mu
  \otimes \mu) \right) \int v^2 \, d\mu.$$
This is the square of the bound $\|K\| \le B$. -/
theorem integral_sq_l2Kernel_le (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∫ x, (∫ y, k (x, y) * v y ∂μ) ^ 2 ∂μ ≤ (∫ p, k p ^ 2 ∂(μ.prod μ)) * ∫ y, v y ^ 2 ∂μ := by
  rw [← integral_integral_sq hk, ← integral_mul_const]
  exact integral_mono_ae (memLp_l2Kernel hk hv).integrable_sq
    ((integrable_integral_sq_row hk).mul_const _) (ae_sq_l2Kernel_le hk hv)

/-- The linear map $v \mapsto \left( x \mapsto \int k(x, y) v(y) \, d\mu(y) \right)$ on $L^2(\mu)$,
for $k \in L^2(\mu \otimes \mu)$. It is the linear map of `IntegralOperator.l2KernelCLM`. -/
noncomputable def l2KernelLM (hk : MemLp k 2 (μ.prod μ)) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun v := (memLp_l2Kernel hk (Lp.memLp v)).toLp _
  map_add' v w := by
    ext
    filter_upwards [MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp (v + w))),
      Lp.coeFn_add ((memLp_l2Kernel hk (Lp.memLp v)).toLp
        (fun x => ∫ y, k (x, y) * v y ∂μ))
        ((memLp_l2Kernel hk (Lp.memLp w)).toLp (fun x => ∫ y, k (x, y) * w y ∂μ)),
      MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp v)),
      MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp w)),
      ae_integrable_row_mul hk (Lp.memLp v), ae_integrable_row_mul hk (Lp.memLp w)]
      with x h1 h2 h3 h4 hiv hiw
    rw [h1, h2, Pi.add_apply, h3, h4, ← integral_add hiv hiw]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add v w] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c v := by
    ext
    filter_upwards [MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp (c • v))),
      Lp.coeFn_smul c ((memLp_l2Kernel hk (Lp.memLp v)).toLp
        (fun x => ∫ y, k (x, y) * v y ∂μ)),
      MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp v))] with x h1 h2 h3
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c v] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    ring

/-- For $k \in L^2(\mu \otimes \mu)$ and $v \in L^2(\mu)$, the function
`IntegralOperator.l2KernelLM hk v` is equal to $x \mapsto \int k(x, y) v(y) \, d\mu(y)$ almost
everywhere. -/
theorem coeFn_l2KernelLM (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℝ 2 μ) :
    l2KernelLM hk v =ᵐ[μ] fun x => ∫ y, k (x, y) * v y ∂μ :=
  MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp v))

/-- Let $\mu$ be an s-finite measure on $X$ and let $k \in L^2(\mu \otimes \mu)$. The **integral
operator** of $k$ is the bounded linear operator $K$ on $L^2(\mu)$ given by
$$(Kv)(x) = \int k(x, y) \, v(y) \, d\mu(y).$$

The operator is built with the bound $B = \left( \int k^2 \, d(\mu \otimes \mu) \right)^{1/2}$,
so $\|K\| \le B$ (`IntegralOperator.norm_l2KernelCLM_le`). The argument `hk` is the proof that
$k$ is square-integrable. The formula holds for almost every $x$
(`IntegralOperator.l2KernelCLM_apply_ae`). -/
noncomputable def l2KernelCLM (hk : MemLp k 2 (μ.prod μ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2KernelLM hk).mkContinuous (√(∫ p, k p ^ 2 ∂(μ.prod μ))) <| by
    intro v
    rw [norm_lp_eq_sqrt_integral_sq, norm_lp_eq_sqrt_integral_sq,
      ← Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)]
    refine Real.sqrt_le_sqrt (le_trans (le_of_eq ?_) (integral_sq_l2Kernel_le hk (Lp.memLp v)))
    exact integral_congr_ae ((coeFn_l2KernelLM hk v).mono fun x hx => by simp only [hx])

/-- Let $\mu$ be an s-finite measure on $X$, and let $k \in L^2(\mu \otimes \mu)$ and
$v \in L^2(\mu)$. Then for $\mu$-almost every $x$,
$$(Kv)(x) = \int k(x, y) \, v(y) \, d\mu(y),$$
where $K$ is `IntegralOperator.l2KernelCLM hk`. -/
theorem l2KernelCLM_apply_ae (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℝ 2 μ) :
    l2KernelCLM hk v =ᵐ[μ] fun x => ∫ y, k (x, y) * v y ∂μ :=
  coeFn_l2KernelLM hk v

/-- Let $\mu$ be an s-finite measure on $X$, and let $k \in L^2(\mu \otimes \mu)$. The integral
operator $K$ of $k$ satisfies
$$\|K\| \le \left( \iint k(x, y)^2 \, d\mu(x) \, d\mu(y) \right)^{1/2}.$$
This is the bound $\|K\| \le B$ of [han2009theoretical], Example 2.6.1 and (2.8.13).

The double integral is the integral of $k^2$ for the product measure $\mu \otimes \mu$. -/
theorem norm_l2KernelCLM_le (hk : MemLp k 2 (μ.prod μ)) :
    ‖l2KernelCLM hk‖ ≤ √(∫ p, k p ^ 2 ∂(μ.prod μ)) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-! ### The adjoint -/

/-- If $k \in L^2(\mu \otimes \mu)$, then the transposed kernel $(x, y) \mapsto k(y, x)$ is in
$L^2(\mu \otimes \mu)$. -/
theorem memLp_swapKernel (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun p : X × X => k (p.2, p.1)) 2 (μ.prod μ) :=
  hk.comp_measurePreserving Measure.measurePreserving_swap

omit [SFinite μ] in
/-- If $k \in L^2(\mu \otimes \mu)$ and $v, w \in L^2(\mu)$, then the function
$(x, y) \mapsto k(x, y) v(y) w(x)$ is integrable for $\mu \otimes \mu$. This makes the Fubini
step in `IntegralOperator.adjoint_l2KernelCLM` valid. -/
theorem integrable_kernel_mul_prod (hk : MemLp k 2 (μ.prod μ)) {v w : X → ℝ}
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    Integrable (fun p : X × X => k p * (v p.2 * w p.1)) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (fun p : X × X => k p * (v p.2 * w p.1)) (μ.prod μ) :=
    hk.aestronglyMeasurable.mul (hv.aestronglyMeasurable.comp_snd.mul
      hw.aestronglyMeasurable.comp_fst)
  have hsq : Integrable (fun p : X × X => (v p.2 * w p.1) ^ 2) (μ.prod μ) :=
    (hw.integrable_sq.mul_prod hv.integrable_sq).congr
      (Eventually.of_forall fun p => by ring)
  refine Integrable.mono' ((hk.integrable_sq.add hsq).div_const 2) hmeas ?_
  refine Eventually.of_forall fun p => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|k p| - |v p.2 * w p.1|), sq_abs (k p), sq_abs (v p.2 * w p.1)]

/-- Let $\mu$ be an s-finite measure on $X$, let $k \in L^2(\mu \otimes \mu)$, let $K$ be its
integral operator, and let $K^T$ be the integral operator of the transposed kernel
$k^T(x, y) = k(y, x)$. Then the adjoint of $K$ on $L^2(\mu)$ is
$$K^* = K^T.$$
This is [han2009theoretical], Example 2.6.1 and (2.8.14).

For $v, w \in L^2(\mu)$, both $\langle Kv, w \rangle$ and $\langle v, K^T w \rangle$ are equal
to the double integral $\iint k(x, y) v(y) w(x)$, by the Fubini theorem. -/
theorem adjoint_l2KernelCLM (hk : MemLp k 2 (μ.prod μ)) :
    ContinuousLinearMap.adjoint (l2KernelCLM hk) = l2KernelCLM (memLp_swapKernel hk) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun w v => ?_).symm
  have hF : Integrable (Function.uncurry fun a b => k (a, b) * (v b * w a)) (μ.prod μ) :=
    integrable_kernel_mul_prod hk (Lp.memLp v) (Lp.memLp w)
  have hswap := integral_integral_swap hF
  rw [L2.inner_eq_integral_mul, L2.inner_eq_integral_mul]
  have hL : ∫ z, (l2KernelCLM (memLp_swapKernel hk) w) z * v z ∂μ
      = ∫ b, ∫ a, k (a, b) * (v b * w a) ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [l2KernelCLM_apply_ae (memLp_swapKernel hk) w] with z hz
    rw [hz, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun a => by ring)
  have hR : ∫ z, w z * (l2KernelCLM hk v) z ∂μ
      = ∫ a, ∫ b, k (a, b) * (v b * w a) ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [l2KernelCLM_apply_ae hk v] with z hz
    rw [hz, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun b => by ring)
  rw [hL, hR, hswap]

/-- If $k, k' \in L^2(\mu \otimes \mu)$ and $k = k'$ almost everywhere for $\mu \otimes \mu$, then
$k$ and $k'$ have the same integral operator. -/
theorem l2KernelCLM_congr {k' : X × X → ℝ} (hk : MemLp k 2 (μ.prod μ))
    (hk' : MemLp k' 2 (μ.prod μ)) (h : k =ᵐ[μ.prod μ] k') :
    l2KernelCLM hk = l2KernelCLM hk' := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext
  filter_upwards [l2KernelCLM_apply_ae hk v, l2KernelCLM_apply_ae hk' v,
    Measure.ae_ae_of_ae_prod h] with x h1 h2 h3
  rw [h1, h2]
  exact integral_congr_ae (h3.mono fun y hy => by simp only [hy])

/-- Let $\mu$ be an s-finite measure on $X$, and let $k \in L^2(\mu \otimes \mu)$. If
$k(x, y) = k(y, x)$ for $\mu \otimes \mu$-almost every $(x, y)$, then the integral operator of
$k$ is self-adjoint on $L^2(\mu)$.

This is the direction of [han2009theoretical], Example 2.6.1, that identifies a self-adjoint
integral operator. It follows from `IntegralOperator.adjoint_l2KernelCLM`. -/
theorem isSelfAdjoint_l2KernelCLM (hk : MemLp k 2 (μ.prod μ))
    (hsymm : ∀ᵐ p ∂(μ.prod μ), k p = k (p.2, p.1)) : IsSelfAdjoint (l2KernelCLM hk) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_l2KernelCLM hk]
  exact l2KernelCLM_congr (memLp_swapKernel hk) hk (hsymm.mono fun p hp => hp.symm)

/-! ### Injectivity of the map from kernels to operators -/

/-- Let $\mu$ be an s-finite measure on $X$, and let $k_1, k_2 \in L^2(\mu \otimes \mu)$. Then the
integral operator of $k_1 - k_2$ is the integral operator of $k_1$ minus the integral operator
of $k_2$. -/
theorem l2KernelCLM_sub {k₁ k₂ : X × X → ℝ} (hk₁ : MemLp k₁ 2 (μ.prod μ))
    (hk₂ : MemLp k₂ 2 (μ.prod μ)) :
    l2KernelCLM (hk₁.sub hk₂) = l2KernelCLM hk₁ - l2KernelCLM hk₂ := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext
  filter_upwards [l2KernelCLM_apply_ae (hk₁.sub hk₂) v, Lp.coeFn_sub (l2KernelCLM hk₁ v)
    (l2KernelCLM hk₂ v), l2KernelCLM_apply_ae hk₁ v, l2KernelCLM_apply_ae hk₂ v,
    ae_integrable_row_mul hk₁ (Lp.memLp v), ae_integrable_row_mul hk₂ (Lp.memLp v)]
    with x h1 h2 h3 h4 hi1 hi2
  have hsubapp : (l2KernelCLM hk₁ - l2KernelCLM hk₂) v
      = l2KernelCLM hk₁ v - l2KernelCLM hk₂ v := rfl
  rw [h1, hsubapp, h2, Pi.sub_apply, h3, h4, ← integral_sub hi1 hi2]
  exact integral_congr_ae (Eventually.of_forall fun y => by simp [sub_mul])

variable [MeasureTheory.IsSeparable μ]

/-- Let $\mu$ be an s-finite separable measure on $X$, and let $k \in L^2(\mu \otimes \mu)$. If the
integral operator of $k$ is zero, then $k = 0$ almost everywhere for $\mu \otimes \mu$.

Almost every row of $k$ is orthogonal to a countable dense subset of $L^2(\mu)$, so it is
orthogonal to all of $L^2(\mu)$ and is zero. Separability is `MeasureTheory.IsSeparable μ`,
which makes $L^2(\mu)$ separable. -/
theorem ae_eq_zero_of_l2KernelCLM_eq_zero (hk : MemLp k 2 (μ.prod μ))
    (h : l2KernelCLM hk = 0) : k =ᵐ[μ.prod μ] 0 := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Lp ℝ 2 μ)
  have hzero : ∀ v : Lp ℝ 2 μ, ∀ᵐ x ∂μ, ∫ y, k (x, y) * v y ∂μ = 0 := by
    intro v
    have hv : (l2KernelCLM hk v : X → ℝ) =ᵐ[μ] 0 := by
      rw [h]
      simpa using Lp.coeFn_zero ℝ 2 μ
    filter_upwards [l2KernelCLM_apply_ae hk v, hv] with x h1 h2
    rw [← h1]
    exact h2
  have hD : ∀ᵐ x ∂μ, ∀ v ∈ D, ∫ y, k (x, y) * v y ∂μ = 0 :=
    (ae_ball_iff hDcount).2 fun v _ => hzero v
  have hrow : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, k (x, y) = 0 := by
    filter_upwards [ae_memLp_row hk, hD] with x hxL2 hxD
    have hinner : ∀ v : Lp ℝ 2 μ, (inner ℝ (hxL2.toLp _) v : ℝ) = ∫ y, k (x, y) * v y ∂μ := by
      intro v
      rw [L2.inner_eq_integral_mul]
      exact integral_congr_ae ((MemLp.coeFn_toLp hxL2).mono fun y hy => by simp only [hy])
    have hcont : Continuous fun v : Lp ℝ 2 μ => (inner ℝ (hxL2.toLp _) v : ℝ) :=
      continuous_const.inner continuous_id
    have hall : (fun v : Lp ℝ 2 μ => (inner ℝ (hxL2.toLp _) v : ℝ)) = fun _ => 0 :=
      Continuous.ext_on hDdense hcont continuous_const
        fun v hv => (hinner v).trans (hxD v hv)
    have hr0 : (hxL2.toLp fun y => k (x, y)) = 0 :=
      inner_self_eq_zero.1 (congrFun hall (hxL2.toLp _))
    filter_upwards [MemLp.coeFn_toLp hxL2, hr0 ▸ Lp.coeFn_zero ℝ 2 μ] with y hy1 hy2
    rw [← hy1, hy2]
    rfl
  obtain ⟨k₀, hk₀meas, hkk₀⟩ := hk.aestronglyMeasurable
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, k₀ (x, y) = 0 := by
    filter_upwards [hrow, Measure.ae_ae_of_ae_prod hkk₀] with x h1 h2
    filter_upwards [h1, h2] with y hy1 hy2
    rw [← hy2, hy1]
  have hmeas : MeasurableSet {p : X × X | k₀ p = 0} :=
    hk₀meas.measurableSet_eq_fun stronglyMeasurable_const
  have hk₀zero : ∀ᵐ p ∂(μ.prod μ), k₀ p = 0 := (Measure.ae_prod_iff_ae_ae hmeas).2 hae
  filter_upwards [hkk₀, hk₀zero] with p hp1 hp2
  rw [hp1]
  exact hp2

/-- Let $\mu$ be an s-finite separable measure on $X$, and let $k \in L^2(\mu \otimes \mu)$. Then
the integral operator of $k$ is self-adjoint on $L^2(\mu)$ if and only if
$$k(x, y) = k(y, x) \quad \text{for } \mu \otimes \mu\text{-almost every } (x, y).$$

The implication from a symmetric kernel is `IntegralOperator.isSelfAdjoint_l2KernelCLM`, and it
does not need separability. The converse uses
`IntegralOperator.ae_eq_zero_of_l2KernelCLM_eq_zero` for the kernel $k - k^T$, and this needs
the separability of $\mu$. -/
theorem isSelfAdjoint_l2KernelCLM_iff (hk : MemLp k 2 (μ.prod μ)) :
    IsSelfAdjoint (l2KernelCLM hk) ↔ ∀ᵐ p ∂(μ.prod μ), k p = k (p.2, p.1) := by
  refine ⟨fun hsa => ?_, isSelfAdjoint_l2KernelCLM hk⟩
  have hswap := memLp_swapKernel hk
  have heq : l2KernelCLM hswap = l2KernelCLM hk := by
    rw [← adjoint_l2KernelCLM hk]
    exact ContinuousLinearMap.isSelfAdjoint_iff'.mp hsa
  have hsub : l2KernelCLM (hswap.sub hk) = 0 := by
    rw [l2KernelCLM_sub hswap hk, heq, sub_self]
  have := ae_eq_zero_of_l2KernelCLM_eq_zero (hswap.sub hk) hsub
  filter_upwards [this] with p hp
  have hp' : k (p.2, p.1) - k p = 0 := hp
  linarith [hp']

end IntegralOperator
