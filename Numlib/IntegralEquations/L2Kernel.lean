import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Integral operators with a square-integrable kernel

For a kernel `k` that is square-integrable on the product `μ × μ`, the formula
`K v (x) = ∫ k (x, y) v y ∂μ` defines a bounded operator on `L²(μ)` whose norm is at most the
`L²` norm `B` of the kernel, and whose adjoint is the operator of the transposed kernel
`(x, y) ↦ k (y, x)`. This is the classical Hilbert–Schmidt integral operator; see
[han2009theoretical], Example 2.6.1 and §2.8.3, and [kress1989linear], §4.
`Numlib/IntegralEquations/Basic` builds the companion operator on `C(X, ℝ)` for a *continuous*
kernel, which is a different object: its bound is the row `L¹` norm, not the `L²` norm of `k`.

## Main statements

* `IntegralOperator.l2KernelCLM` — the operator itself, with `IntegralOperator.l2KernelCLM_apply_ae`
  the defining formula (an `L²` element is an a.e.-class, so the formula holds almost everywhere).
* `IntegralOperator.norm_l2KernelCLM_le` — `‖K‖ ≤ √(∫∫ k²)`. Cauchy–Schwarz on the row `k (x, ·)`
  bounds `|K v (x)|²` by `(∫ k (x, y)² ∂μ) ‖v‖²`, and Fubini integrates the row norms to `B²`.
* `IntegralOperator.adjoint_l2KernelCLM` — the adjoint is the operator of the transposed kernel,
  by Fubini on `∫∫ k (x, y) v y w x`.
* `IntegralOperator.isSelfAdjoint_l2KernelCLM` and
  `IntegralOperator.isSelfAdjoint_l2KernelCLM_iff` — the operator is self-adjoint exactly when the
  kernel is symmetric almost everywhere. The forward direction of the `iff` is the injectivity of
  `k ↦ l2KernelCLM hk` (`IntegralOperator.ae_eq_zero_of_l2KernelCLM_eq_zero`), which asks that the
  measure be separable, so that `L²(μ)` has a countable dense subset; that holds automatically
  when the space is countably generated, in particular for `L²(a, b)`.

Along the way, `IntegralOperator.abs_integral_mul_le_sqrt_mul_sqrt` is the Cauchy–Schwarz
inequality for a product of two square-integrable real functions, and
`IntegralOperator.norm_lp_eq_sqrt_integral_sq` and `IntegralOperator.real_inner_lp_eq` read the
norm and the inner product of `Lp ℝ 2 μ` as ordinary integrals, which is what makes the
statements below quantifier-free integral inequalities rather than `eLpNorm` manipulations.
-/

open Filter MeasureTheory Real

namespace IntegralOperator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for the integral of a product**: for square-integrable real `f` and `g`,
`|∫ f g| ≤ √(∫ f²) √(∫ g²)`. This is Hölder's inequality at the conjugate pair `(2, 2)`. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
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

/-- The norm of an element of `L²(μ)` as an ordinary integral, `‖f‖ = √(∫ f²)`. -/
theorem norm_lp_eq_sqrt_integral_sq (f : Lp ℝ 2 μ) : ‖f‖ = √(∫ x, f x ^ 2 ∂μ) := by
  have h := real_inner_self_eq_norm_mul_norm f
  rw [MeasureTheory.L2.inner_def] at h
  have h2 : ∫ x, (inner ℝ (f x) (f x) : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq]
  rw [h2, ← sq] at h
  rw [h, Real.sqrt_sq (norm_nonneg f)]

/-- The inner product of `L²(μ)` as an ordinary integral, `⟪f, g⟫ = ∫ f g`. -/
theorem real_inner_lp_eq (f g : Lp ℝ 2 μ) : (inner ℝ f g : ℝ) = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm])

/-! ### Rows of a square-integrable kernel -/

variable [SFinite μ] {k : X × X → ℝ}

/-- Almost every row `k (x, ·)` of a square-integrable kernel is square-integrable. -/
theorem ae_memLp_row (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 μ := by
  filter_upwards [hk.aestronglyMeasurable.prodMk_left, hk.integrable_sq.prod_right_ae]
    with x hm hi using (memLp_two_iff_integrable_sq hm).2 hi

/-- The squared `L²` norm of the row `k (x, ·)` is an integrable function of `x`. -/
theorem integrable_integral_sq_row (hk : MemLp k 2 (μ.prod μ)) :
    Integrable (fun x => ∫ y, k (x, y) ^ 2 ∂μ) μ :=
  hk.integrable_sq.integral_prod_left

/-- Fubini for the squared kernel: integrating the squared row norms recovers `∫∫ k²`,
the square of the bound `B` of [han2009theoretical], Example 2.6.1. -/
theorem integral_integral_sq (hk : MemLp k 2 (μ.prod μ)) :
    ∫ x, (∫ y, k (x, y) ^ 2 ∂μ) ∂μ = ∫ p, k p ^ 2 ∂(μ.prod μ) :=
  integral_integral hk.integrable_sq

/-- The row `L²` norm `x ↦ √(∫ k (x, y)² ∂μ)` is itself square-integrable. -/
theorem memLp_sqrt_integral_sq_row (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun x => √(∫ y, k (x, y) ^ 2 ∂μ)) 2 μ := by
  have hI := integrable_integral_sq_row hk
  have hmeas : AEStronglyMeasurable (fun x => √(∫ y, k (x, y) ^ 2 ∂μ)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hI.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 (hI.congr ?_)
  refine Filter.Eventually.of_forall fun x => ?_
  exact (Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)).symm

/-- For almost every `x` the integrand `y ↦ k (x, y) v y` of the operator is integrable. -/
theorem ae_integrable_row_mul (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * v y) μ := by
  filter_upwards [ae_memLp_row hk] with x hx
  exact hx.integrable_mul hv

/-! ### The operator -/

/-- The image `x ↦ ∫ k (x, y) v y ∂μ` of a measurable function is measurable. -/
theorem aestronglyMeasurable_l2Kernel (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ}
    (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => ∫ y, k (x, y) * v y ∂μ) μ :=
  (hk.aestronglyMeasurable.mul hv.comp_snd).integral_prod_right'

/-- Cauchy–Schwarz on the row: `|∫ k (x, y) v y ∂μ| ≤ √(∫ k (x, y)² ∂μ) √(∫ v²)`. -/
theorem abs_integral_row_mul_le (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∀ᵐ x ∂μ, |∫ y, k (x, y) * v y ∂μ| ≤ √(∫ y, k (x, y) ^ 2 ∂μ) * √(∫ y, v y ^ 2 ∂μ) := by
  filter_upwards [ae_memLp_row hk] with x hx
  exact abs_integral_mul_le_sqrt_mul_sqrt hx hv

/-- The squared form of the row bound, which is what integrates in `x`. -/
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

/-- The image of a square-integrable function under an `L²` kernel is square-integrable. -/
theorem memLp_l2Kernel (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    MemLp (fun x => ∫ y, k (x, y) * v y ∂μ) 2 μ := by
  have hmeas := aestronglyMeasurable_l2Kernel hk hv.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' ((integrable_integral_sq_row hk).mul_const (∫ y, v y ^ 2 ∂μ))
    (hmeas.pow 2) ?_
  filter_upwards [ae_sq_l2Kernel_le hk hv] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

/-- `∫ (K v)² ≤ (∫∫ k²) ∫ v²`: the squared operator bound, before taking square roots. -/
theorem integral_sq_l2Kernel_le (hk : MemLp k 2 (μ.prod μ)) {v : X → ℝ} (hv : MemLp v 2 μ) :
    ∫ x, (∫ y, k (x, y) * v y ∂μ) ^ 2 ∂μ ≤ (∫ p, k p ^ 2 ∂(μ.prod μ)) * ∫ y, v y ^ 2 ∂μ := by
  rw [← integral_integral_sq hk, ← integral_mul_const]
  exact integral_mono_ae (memLp_l2Kernel hk hv).integrable_sq
    ((integrable_integral_sq_row hk).mul_const _) (ae_sq_l2Kernel_le hk hv)

/-- The linear map underlying `IntegralOperator.l2KernelCLM`. -/
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

/-- The defining formula for `IntegralOperator.l2KernelLM`, valid almost everywhere. -/
theorem coeFn_l2KernelLM (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℝ 2 μ) :
    l2KernelLM hk v =ᵐ[μ] fun x => ∫ y, k (x, y) * v y ∂μ :=
  MemLp.coeFn_toLp (memLp_l2Kernel hk (Lp.memLp v))

/-- **The integral operator of a square-integrable kernel.** For `k ∈ L²(μ × μ)` the map
`v ↦ (x ↦ ∫ k (x, y) v y ∂μ)` is a bounded operator on `L²(μ)`, of norm at most the `L²`
norm of `k` (`IntegralOperator.norm_l2KernelCLM_le`). -/
noncomputable def l2KernelCLM (hk : MemLp k 2 (μ.prod μ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2KernelLM hk).mkContinuous (√(∫ p, k p ^ 2 ∂(μ.prod μ))) <| by
    intro v
    rw [norm_lp_eq_sqrt_integral_sq, norm_lp_eq_sqrt_integral_sq,
      ← Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)]
    refine Real.sqrt_le_sqrt (le_trans (le_of_eq ?_) (integral_sq_l2Kernel_le hk (Lp.memLp v)))
    exact integral_congr_ae ((coeFn_l2KernelLM hk v).mono fun x hx => by simp only [hx])

/-- **The defining formula** `K v (x) = ∫ k (x, y) v y ∂μ`, valid for almost every `x`. -/
theorem l2KernelCLM_apply_ae (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℝ 2 μ) :
    l2KernelCLM hk v =ᵐ[μ] fun x => ∫ y, k (x, y) * v y ∂μ :=
  coeFn_l2KernelLM hk v

/-- **The operator norm is at most the `L²` norm of the kernel**, `‖K‖ ≤ B` with
`B = √(∫∫ k (x, y)²)`. This is the bound of [han2009theoretical], Example 2.6.1 and (2.8.13). -/
theorem norm_l2KernelCLM_le (hk : MemLp k 2 (μ.prod μ)) :
    ‖l2KernelCLM hk‖ ≤ √(∫ p, k p ^ 2 ∂(μ.prod μ)) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-! ### The adjoint -/

/-- The transposed kernel `(x, y) ↦ k (y, x)` is square-integrable when `k` is. -/
theorem memLp_swapKernel (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (fun p : X × X => k (p.2, p.1)) 2 (μ.prod μ) :=
  hk.comp_measurePreserving Measure.measurePreserving_swap

omit [SFinite μ] in
/-- The function `(x, y) ↦ k (x, y) v y w x` is integrable on the product, which is what makes
the Fubini step of the adjoint identity legitimate. -/
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

/-- **The adjoint of an `L²` kernel operator is the operator of the transposed kernel**:
`(K_k)† = K_{kᵀ}` with `kᵀ (x, y) = k (y, x)`. Both sides pair with `v` and `w` to the same
double integral `∫∫ k (x, y) v y w x`, so the identity is Fubini.
This is [han2009theoretical], Example 2.6.1 and (2.8.14). -/
theorem adjoint_l2KernelCLM (hk : MemLp k 2 (μ.prod μ)) :
    ContinuousLinearMap.adjoint (l2KernelCLM hk) = l2KernelCLM (memLp_swapKernel hk) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun w v => ?_).symm
  have hF : Integrable (Function.uncurry fun a b => k (a, b) * (v b * w a)) (μ.prod μ) :=
    integrable_kernel_mul_prod hk (Lp.memLp v) (Lp.memLp w)
  have hswap := integral_integral_swap hF
  rw [real_inner_lp_eq, real_inner_lp_eq]
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

/-- Kernels equal almost everywhere give the same operator. -/
theorem l2KernelCLM_congr {k' : X × X → ℝ} (hk : MemLp k 2 (μ.prod μ))
    (hk' : MemLp k' 2 (μ.prod μ)) (h : k =ᵐ[μ.prod μ] k') :
    l2KernelCLM hk = l2KernelCLM hk' := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext
  filter_upwards [l2KernelCLM_apply_ae hk v, l2KernelCLM_apply_ae hk' v,
    Measure.ae_ae_of_ae_prod h] with x h1 h2 h3
  rw [h1, h2]
  exact integral_congr_ae (h3.mono fun y hy => by simp only [hy])

/-- **A kernel symmetric almost everywhere gives a self-adjoint operator**, by
`IntegralOperator.adjoint_l2KernelCLM`. This is the direction of [han2009theoretical],
Example 2.6.1 that is used to recognise a self-adjoint integral operator. -/
theorem isSelfAdjoint_l2KernelCLM (hk : MemLp k 2 (μ.prod μ))
    (hsymm : ∀ᵐ p ∂(μ.prod μ), k p = k (p.2, p.1)) : IsSelfAdjoint (l2KernelCLM hk) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_l2KernelCLM hk]
  exact l2KernelCLM_congr (memLp_swapKernel hk) hk (hsymm.mono fun p hp => hp.symm)

/-! ### Injectivity of the kernel-to-operator map -/

/-- The operator of a difference of kernels is the difference of the operators. -/
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

/-- **An `L²` kernel whose operator vanishes is null.** Every row of the kernel is orthogonal to a
countable dense subset of `L²(μ)`, hence to all of it, hence zero. -/
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
      rw [real_inner_lp_eq]
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

/-- **An `L²` kernel operator is self-adjoint exactly when its kernel is symmetric almost
everywhere.** The implication that matters in practice is the easy one,
`IntegralOperator.isSelfAdjoint_l2KernelCLM`; the converse is the injectivity of
`k ↦ l2KernelCLM hk`, which is `IntegralOperator.ae_eq_zero_of_l2KernelCLM_eq_zero` and needs the
measure to be separable, so that `L²(μ)` has a countable dense subset. -/
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
