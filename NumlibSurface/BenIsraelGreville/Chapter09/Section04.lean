/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section03
import Numlib.IntegralEquations.L2Kernel
import Numlib.Analysis.Normed.Operator.Compact
import Numlib.Analysis.Normed.Operator.Compact.Banach
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Module

/-!
# Generalized inverses of linear integral operators

Section 9.4 of [benIsrael2003generalized] applies Fredholm theory to
second-kind integral equations with complex square-integrable kernels.

## Deviations from the source

* For complex scalars in properties (b)–(c), the adjoint uses both the
  conjugated parameter and the conjugate-transpose kernel.
* In **Exercise 22(b)** the adjoint solution space uses the conjugates
  of the second factors of the separated kernel.
* The integral representations hold almost everywhere, as required for
  equality of vectors in (L^2).
-/

noncomputable section

namespace BenIsraelGreville.Chapter09

open Filter MeasureTheory Set InnerProductSpace
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace

section Kernel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable {k : X × X → ℂ} {v : X → ℂ}

private theorem ae_integrable_complexKernel_row
    (hk : MemLp k 2 (μ.prod μ)) (hv : MemLp v 2 μ) :
    ∀ᵐ s ∂μ, Integrable (fun t => k (s, t) * v t) μ := by
  filter_upwards [hk.aestronglyMeasurable.prodMk_left,
    IntegralOperator.ae_integrable_row_mul hk.norm hv.norm] with s hs hi
  refine Integrable.mono' hi (hs.mul hv.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun t => norm_mul _ _ |>.le

omit [SFinite μ] in
private theorem norm_complexKernel_row_le (k : X × X → ℂ) (v : X → ℂ) (s : X) :
    ‖∫ t, k (s, t) * v t ∂μ‖ ≤ ∫ t, ‖k (s, t)‖ * ‖v t‖ ∂μ := by
  simpa only [norm_mul] using
    (norm_integral_le_integral_norm (μ := μ) (fun t => k (s, t) * v t))

private theorem memLp_complexKernel_apply (hk : MemLp k 2 (μ.prod μ)) (hv : MemLp v 2 μ) :
    MemLp (fun s => ∫ t, k (s, t) * v t ∂μ) 2 μ := by
  apply (IntegralOperator.memLp_l2Kernel hk.norm hv.norm).mono'
  · exact (hk.aestronglyMeasurable.mul hv.aestronglyMeasurable.comp_snd).integral_prod_right'
  · exact Eventually.of_forall (norm_complexKernel_row_le k v)

private def complexKernelApply (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (memLp_complexKernel_apply hk (Lp.memLp v)).toLp _

private theorem complexKernelApply_ae (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℂ 2 μ) :
    complexKernelApply hk v =ᵐ[μ] fun s => ∫ t, k (s, t) * v t ∂μ :=
  MemLp.coeFn_toLp (memLp_complexKernel_apply hk (Lp.memLp v))

private def complexKernelLM (hk : MemLp k 2 (μ.prod μ)) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := complexKernelApply hk
  map_add' v w := by
    apply Lp.ext
    filter_upwards [complexKernelApply_ae hk (v + w),
      Lp.coeFn_add (complexKernelApply hk v) (complexKernelApply hk w),
      complexKernelApply_ae hk v, complexKernelApply_ae hk w,
      ae_integrable_complexKernel_row hk (Lp.memLp v),
      ae_integrable_complexKernel_row hk (Lp.memLp w)] with s hsum hab hv hw hiv hiw
    rw [hsum, hab, Pi.add_apply, hv, hw, ← integral_add hiv hiw]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add v w] with t ht
    rw [ht, Pi.add_apply, mul_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [complexKernelApply_ae hk (c • v), Lp.coeFn_smul c (complexKernelApply hk v),
      complexKernelApply_ae hk v] with s h1 h2 h3
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c v] with t ht
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring

private theorem norm_complexKernelLM_le (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℂ 2 μ) :
    ‖complexKernelLM hk v‖ ≤ Real.sqrt (∫ p, ‖k p‖ ^ 2 ∂(μ.prod μ)) * ‖v‖ := by
  let w : Lp ℝ 2 μ := (Lp.memLp v).norm.toLp _
  have hw : w =ᵐ[μ] fun t => ‖v t‖ := MemLp.coeFn_toLp (Lp.memLp v).norm
  have hnorm : ‖w‖ = ‖v‖ := by
    rw [show w = (Lp.memLp v).norm.toLp _ from rfl, Lp.norm_toLp,
      eLpNorm_norm _ (Lp.memLp v).aestronglyMeasurable]
    rfl
  let K := IntegralOperator.l2KernelCLM hk.norm
  have hpoint : ∀ s : X, (∫ t, ‖k (s, t)‖ * w t ∂μ) =
      ∫ t, ‖k (s, t)‖ * ‖v t‖ ∂μ := fun s =>
    integral_congr_ae (hw.mono fun t ht => congrArg (‖k (s, t)‖ * ·) ht)
  have hbound : ‖complexKernelLM hk v‖ ≤ ‖K w‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [complexKernelApply_ae hk v, IntegralOperator.l2KernelCLM_apply_ae hk.norm w]
      with s hs ht
    change ‖complexKernelApply hk v s‖ ≤ ‖K w s‖
    rw [hs, ht, hpoint]
    exact (norm_complexKernel_row_le k v s).trans (le_abs_self _)
  exact hbound.trans ((K.le_opNorm w).trans (by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right
      (IntegralOperator.norm_l2KernelCLM_le hk.norm) (norm_nonneg _)))

/-- **Equation (30)** of [benIsrael2003generalized], Chapter 9.
A complex square-integrable kernel defines a bounded operator on `L²`. -/
def fredholmIntegralOperator (hk : MemLp k 2 (μ.prod μ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (complexKernelLM hk).mkContinuous _ (norm_complexKernelLM_le hk)

/-- The integral operator acts by integration against the second variable
for almost every first coordinate. -/
theorem fredholmIntegralOperator_apply_ae (hk : MemLp k 2 (μ.prod μ)) (v : Lp ℂ 2 μ) :
    fredholmIntegralOperator hk v =ᵐ[μ] fun s => ∫ t, k (s, t) * v t ∂μ :=
  complexKernelApply_ae hk v

/-- The operator norm is bounded by the `L²` norm of the kernel. -/
theorem norm_fredholmIntegralOperator_le (hk : MemLp k 2 (μ.prod μ)) :
    ‖fredholmIntegralOperator hk‖ ≤ Real.sqrt (∫ p, ‖k p‖ ^ 2 ∂(μ.prod μ)) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-- The coefficient operator of the Fredholm equation of the second kind. -/
def fredholmSecondKind (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  1 - z • fredholmIntegralOperator hk

/-- **Equation (30)** of [benIsrael2003generalized], Chapter 9.
The bounded operator gives the second-kind equation pointwise almost everywhere. -/
theorem fredholmSecondKind_apply_ae (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) (v : Lp ℂ 2 μ) :
    fredholmSecondKind hk z v =ᵐ[μ] fun s => v s - z * ∫ t, k (s, t) * v t ∂μ := by
  change (v - z • fredholmIntegralOperator hk v : Lp ℂ 2 μ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_sub v (z • fredholmIntegralOperator hk v),
    Lp.coeFn_smul z (fredholmIntegralOperator hk v), fredholmIntegralOperator_apply_ae hk v]
    with s h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, smul_eq_mul]

/-- The kernel of the Hilbert-space adjoint is obtained by swapping the
two variables and conjugating its values. -/
def adjointKernel (k : X × X → ℂ) (p : X × X) : ℂ :=
  conj (k p.swap)

/-- Swapping and conjugating the kernel preserves square integrability. -/
theorem memLp_adjointKernel (hk : MemLp k 2 (μ.prod μ)) :
    MemLp (adjointKernel k) 2 (μ.prod μ) :=
  (hk.comp_measurePreserving Measure.measurePreserving_swap).star

omit [SFinite μ] in
private theorem integrable_complexKernel_mul_prod (hk : MemLp k 2 (μ.prod μ))
    (v w : Lp ℂ 2 μ) :
    Integrable (fun p : X × X => k p * (v p.2 * conj (w p.1))) (μ.prod μ) := by
  apply Integrable.mono' (IntegralOperator.integrable_kernel_mul_prod hk.norm
    (Lp.memLp v).norm (Lp.memLp w).norm)
  · exact hk.aestronglyMeasurable.mul ((Lp.memLp v).aestronglyMeasurable.comp_snd.mul
      (Lp.memLp w).aestronglyMeasurable.comp_fst.star)
  · exact Eventually.of_forall fun p => by simp

/-- **Fredholm property (b)** of [benIsrael2003generalized], Chapter 9.
The adjoint of the bounded integral operator has the conjugate-transpose kernel. -/
theorem fredholmIntegralOperator_adjoint (hk : MemLp k 2 (μ.prod μ)) :
    (fredholmIntegralOperator hk).adjoint = fredholmIntegralOperator (memLp_adjointKernel hk) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun w v => ?_).symm
  have hF : Integrable (Function.uncurry fun a b => k (a, b) * (v b * conj (w a)))
      (μ.prod μ) := integrable_complexKernel_mul_prod hk v w
  have hs := integral_integral_swap hF
  simp only [L2.inner_def, RCLike.inner_apply]
  have hL : (∫ t, v t * conj (fredholmIntegralOperator (memLp_adjointKernel hk) w t) ∂μ)
      = ∫ b, ∫ a, k (a, b) * (v b * conj (w a)) ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [fredholmIntegralOperator_apply_ae (memLp_adjointKernel hk) w] with t ht
    rw [ht, ← integral_conj, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun a => by simp [adjointKernel]; ring)
  have hR : (∫ s, fredholmIntegralOperator hk v s * conj (w s) ∂μ)
      = ∫ a, ∫ b, k (a, b) * (v b * conj (w a)) ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [fredholmIntegralOperator_apply_ae hk v] with s hs
    rw [hs, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => by ring)
  rw [hL, hR, hs]

/-- **Fredholm property (b)** of [benIsrael2003generalized], Chapter 9.
The adjoint of the second-kind coefficient conjugates the scalar parameter. -/
theorem fredholmSecondKind_adjoint (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) :
    (fredholmSecondKind hk z).adjoint = fredholmSecondKind (memLp_adjointKernel hk) (conj z) := by
  unfold fredholmSecondKind
  have hid : (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).adjoint = 1 := by
    simpa [ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.adjoint_id (𝕜 := ℂ) (E := Lp ℂ 2 μ))
  rw [map_sub, map_smulₛₗ, hid, fredholmIntegralOperator_adjoint]

/-- Replacing a kernel by an almost-everywhere equal representative preserves its operator. -/
theorem fredholmIntegralOperator_congr {l : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hl : MemLp l 2 (μ.prod μ)) (hkl : k =ᵐ[μ.prod μ] l) :
    fredholmIntegralOperator hk = fredholmIntegralOperator hl := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [fredholmIntegralOperator_apply_ae hk v,
    fredholmIntegralOperator_apply_ae hl v, Measure.ae_ae_of_ae_prod hkl] with s hs ht hh
  rw [hs, ht]
  exact integral_congr_ae (hh.mono fun t ht => congrArg (· * v t) ht)

/-- The (L^2) kernel construction is additive. -/
theorem fredholmIntegralOperator_add {l : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (hl : MemLp l 2 (μ.prod μ)) :
    fredholmIntegralOperator (hk.add hl) =
      fredholmIntegralOperator hk + fredholmIntegralOperator hl := by
  apply ContinuousLinearMap.ext
  intro v
  rw [add_apply]
  apply Lp.ext
  filter_upwards [fredholmIntegralOperator_apply_ae (hk.add hl) v,
    Lp.coeFn_add (fredholmIntegralOperator hk v) (fredholmIntegralOperator hl v),
    fredholmIntegralOperator_apply_ae hk v, fredholmIntegralOperator_apply_ae hl v,
    ae_integrable_complexKernel_row hk (Lp.memLp v),
    ae_integrable_complexKernel_row hl (Lp.memLp v)]
    with s hs hsum hv hw hi hj
  rw [hs, hsum, Pi.add_apply, hv, hw, ← integral_add hi hj]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only [Pi.add_apply, add_mul])

/-- Multiplication of the kernel by a scalar multiplies its operator by the same scalar. -/
theorem fredholmIntegralOperator_smul (hk : MemLp k 2 (μ.prod μ)) (c : ℂ) :
    fredholmIntegralOperator (hk.const_smul c) = c • fredholmIntegralOperator hk := by
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply]
  apply Lp.ext
  filter_upwards [fredholmIntegralOperator_apply_ae (hk.const_smul c) v,
    Lp.coeFn_smul c (fredholmIntegralOperator hk v), fredholmIntegralOperator_apply_ae hk v]
    with s hs ht hu
  rw [hs, ht, Pi.smul_apply, hu, smul_eq_mul, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp [mul_assoc])

/-- Sending the (L^2) class of a kernel to its operator is a bounded linear map. -/
def fredholmKernelToOperator : Lp ℂ 2 (μ.prod μ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := fun q => fredholmIntegralOperator (Lp.memLp q)
      map_add' := fun q r => by
        rw [← fredholmIntegralOperator_add]
        exact fredholmIntegralOperator_congr _ _ (Lp.coeFn_add q r)
      map_smul' := fun c q => by
        rw [RingHom.id_apply, ← fredholmIntegralOperator_smul]
        exact fredholmIntegralOperator_congr _ _ (Lp.coeFn_smul c q) }
    1 (by
      intro q
      rw [one_mul]
      refine (norm_fredholmIntegralOperator_le (Lp.memLp q)).trans (le_of_eq ?_)
      let r := (Lp.memLp q).norm.toLp (fun p => ‖q p‖)
      have hr := IntegralOperator.norm_lp_eq_sqrt_integral_sq r
      have hrnorm : ‖r‖ = ‖q‖ := by
        rw [show r = (Lp.memLp q).norm.toLp _ from rfl, Lp.norm_toLp,
          eLpNorm_norm _ (Lp.memLp q).aestronglyMeasurable]
        rfl
      rw [hrnorm] at hr
      rw [hr]
      congr 1
      exact integral_congr_ae ((MemLp.coeFn_toLp (Lp.memLp q).norm).mono fun p hp => by
        change ‖q p‖ ^ 2 = r p ^ 2
        exact (congrArg (fun t : ℝ => t ^ 2) hp).symm))


/-- A separated kernel representing a rank-one operator on (L^2). -/
def rankOneKernel (u v : Lp ℂ 2 μ) (p : X × X) : ℂ :=
  u p.1 * conj (v p.2)

omit [SFinite μ] in
/-- The product of two (L^2) vectors in different variables is an (L^2) kernel. -/
theorem memLp_rankOneKernel (u v : Lp ℂ 2 μ) :
    MemLp (rankOneKernel u v) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).2
  · simpa [rankOneKernel, mul_pow] using
      (Lp.memLp u).norm.integrable_sq.mul_prod (Lp.memLp v).norm.integrable_sq
  · exact (Lp.memLp u).aestronglyMeasurable.comp_fst.mul
      (Lp.memLp v).aestronglyMeasurable.comp_snd.star

/-- Separated kernels act as rank-one operators. -/
theorem fredholmIntegralOperator_rankOneKernel (u v : Lp ℂ 2 μ) :
    fredholmIntegralOperator (memLp_rankOneKernel u v) = rankOne ℂ u v := by
  apply ContinuousLinearMap.ext
  intro w
  rw [rankOne_apply]
  apply Lp.ext
  filter_upwards [fredholmIntegralOperator_apply_ae (memLp_rankOneKernel u v) w,
    Lp.coeFn_smul (inner ℂ v w) u] with s hs ht
  rw [hs, ht, Pi.smul_apply, smul_eq_mul, L2.inner_def]
  simp only [RCLike.inner_apply, rankOneKernel, mul_comm _ (u s), ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

omit [SFinite μ] in
private theorem isCompactOperator_rankOneLp (u v : Lp ℂ 2 μ) :
    IsCompactOperator (rankOne ℂ u v) := by
  have hle : (rankOne ℂ u v).range ≤ ℂ ∙ u := by
    rintro _ ⟨w, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨inner ℂ v w, rfl⟩
  let : FiniteDimensional ℂ (rankOne ℂ u v).range :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact IsCompactOperator.of_finiteDimensional_range _

end Kernel

section FiniteMeasure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private theorem ae_eq_prod_fst {f g : X → ℂ} (h : f =ᵐ[μ] g) :
    (fun p : X × X => f p.1) =ᵐ[μ.prod μ] (fun p => g p.1) :=
  (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h

omit [IsFiniteMeasure μ] in
private theorem ae_eq_prod_snd {f g : X → ℂ} (h : f =ᵐ[μ] g) :
    (fun p : X × X => f p.2) =ᵐ[μ.prod μ] (fun p => g p.2) :=
  (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h

private def rectangularKernels : Set (Lp ℂ 2 (μ.prod μ)) :=
  {q | ∃ (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t),
    q = indicatorConstLp 2 (hs.prod ht) (measure_ne_top _ _) (1 : ℂ)}

omit [IsFiniteMeasure μ] in
private theorem ae_eq_zero_of_rectangle_integrals {q : X × X → ℂ}
    (hq : Integrable q (μ.prod μ))
    (hrect : ∀ s t : Set X, MeasurableSet s → MeasurableSet t →
      ∫ p in s ×ˢ t, q p ∂(μ.prod μ) = 0) :
    q =ᵐ[μ.prod μ] 0 := by
  have hu : (∫ p, q p ∂(μ.prod μ)) = 0 := by
    simpa using hrect univ univ MeasurableSet.univ MeasurableSet.univ
  have hAll : ∀ S, MeasurableSet S → ∫ p in S, q p ∂(μ.prod μ) = 0 := by
    intro S hS
    induction S, hS using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic S hS =>
      obtain ⟨s, hs, t, ht, rfl⟩ := hS
      exact hrect s t hs ht
    | compl S hS hzero =>
      rw [← integral_add_compl hS hq, hzero, zero_add] at hu
      exact hu
    | iUnion S hdis hmeas hzero =>
      rw [integral_iUnion hmeas hdis hq.integrableOn]
      simp [hzero]
  exact hq.ae_eq_zero_of_forall_setIntegral_eq_zero fun S hS _ => hAll S hS

private theorem rectangularKernels_span_dense :
    (Submodule.span ℂ (rectangularKernels (μ := μ))).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro q hq
  apply Lp.ext
  apply (ae_eq_zero_of_rectangle_integrals ((Lp.memLp q).integrable (by norm_num)) ?_).trans
    (Lp.coeFn_zero ℂ 2 (μ.prod μ)).symm
  intro s t hs ht
  rw [← L2.inner_indicatorConstLp_one (hs.prod ht) (measure_ne_top _ _)]
  exact (Submodule.mem_orthogonal _ _).mp hq _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨s, t, hs, ht, rfl⟩))

private theorem rectangularKernels_isCompact {q : Lp ℂ 2 (μ.prod μ)}
    (hq : q ∈ rectangularKernels) :
    IsCompactOperator (fredholmKernelToOperator q) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hq
  let u : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top _ _) 1
  let v : Lp ℂ 2 μ := indicatorConstLp 2 ht (measure_ne_top _ _) 1
  have he : (⇑(indicatorConstLp 2 (hs.prod ht) (measure_ne_top (μ.prod μ) _) (1 : ℂ))) =ᵐ[μ.prod μ]
      rankOneKernel u v := by
    filter_upwards [indicatorConstLp_coeFn (μ := μ.prod μ) (p := 2) (hs := hs.prod ht)
        (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
      ae_eq_prod_fst (indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hs)
        (hμs := measure_ne_top _ _) (c := (1 : ℂ))),
      ae_eq_prod_snd (indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := ht)
        (hμs := measure_ne_top _ _) (c := (1 : ℂ)))]
      with p hp hu hv
    change indicatorConstLp 2 (hs.prod ht) (measure_ne_top (μ.prod μ) _) (1 : ℂ) p =
      u p.1 * conj (v p.2)
    change u p.1 = s.indicator (fun _ => (1 : ℂ)) p.1 at hu
    change v p.2 = t.indicator (fun _ => (1 : ℂ)) p.2 at hv
    rw [hp, hu, hv]
    by_cases hps : p.1 ∈ s <;> by_cases hpt : p.2 ∈ t <;> simp [hps, hpt]
  change IsCompactOperator (fredholmIntegralOperator (Lp.memLp _))
  rw [fredholmIntegralOperator_congr _ (memLp_rankOneKernel u v) he,
    fredholmIntegralOperator_rankOneKernel]
  exact isCompactOperator_rankOneLp u v

/-- Square-integrable kernels on a finite measure space act by compact operators. -/
theorem isCompactOperator_fredholmIntegralOperator {k : X × X → ℂ}
    (hk : MemLp k 2 (μ.prod μ)) :
    IsCompactOperator (fredholmIntegralOperator hk) := by
  let S := (compactOperator (RingHom.id ℂ) (Lp ℂ 2 μ) (Lp ℂ 2 μ)).comap
    (fredholmKernelToOperator (μ := μ)).toLinearMap
  have hSclosed : IsClosed (S : Set (Lp ℂ 2 (μ.prod μ))) :=
    isClosed_setOfPred_isCompactOperator.preimage (fredholmKernelToOperator (μ := μ)).continuous
  have hS : Submodule.span ℂ (rectangularKernels (μ := μ)) ≤ S :=
    Submodule.span_le.mpr fun _ h => rectangularKernels_isCompact h
  have htop : S = ⊤ := by
    apply top_unique
    rw [← rectangularKernels_span_dense (μ := μ)]
    exact Submodule.topologicalClosure_minimal _ hS hSclosed
  have hm : hk.toLp k ∈ S := htop ▸ Submodule.mem_top
  change IsCompactOperator (fredholmIntegralOperator (Lp.memLp (hk.toLp k))) at hm
  rwa [fredholmIntegralOperator_congr _ hk (MemLp.coeFn_toLp hk)] at hm

end FiniteMeasure


section KernelComposition

open scoped TensorProduct

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

local notation "H" => Lp ℂ 2 μ
local notation "K₂" => Lp ℂ 2 (μ.prod μ)

omit [IsFiniteMeasure μ] in
private theorem memLp_productKernel (u v : H) :
    MemLp (fun p : X × X => u p.1 * v p.2) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).2
  · simpa [mul_pow] using
      (Lp.memLp u).norm.integrable_sq.mul_prod (Lp.memLp v).norm.integrable_sq
  · exact (Lp.memLp u).aestronglyMeasurable.comp_fst.mul (Lp.memLp v).aestronglyMeasurable.comp_snd

private def productKernel (u v : H) : K₂ := (memLp_productKernel u v).toLp _

omit [IsFiniteMeasure μ] in
private theorem productKernel_ae (u v : H) :
    productKernel u v =ᵐ[μ.prod μ] fun p => u p.1 * v p.2 :=
  MemLp.coeFn_toLp (memLp_productKernel u v)

private def productKernelBilinear : H →ₗ[ℂ] H →ₗ[ℂ] K₂ where
  toFun u :=
    { toFun := productKernel u
      map_add' := fun v w => by
        apply Lp.ext
        filter_upwards [productKernel_ae u (v + w), productKernel_ae u v,
          productKernel_ae u w, ae_eq_prod_snd (Lp.coeFn_add v w),
          Lp.coeFn_add (productKernel u v) (productKernel u w)] with p hp hv hw hsum hab
        rw [hp, hab, Pi.add_apply, hv, hw]
        change (u p.1 * (v + w) p.2) = u p.1 * v p.2 + u p.1 * w p.2
        rw [hsum, Pi.add_apply, mul_add]
      map_smul' := fun c v => by
        apply Lp.ext
        filter_upwards [productKernel_ae u (c • v), productKernel_ae u v,
          ae_eq_prod_snd (Lp.coeFn_smul c v), Lp.coeFn_smul c (productKernel u v)]
          with p hp hv hcv hab
        rw [RingHom.id_apply, hp, hab, Pi.smul_apply, hv]
        change u p.1 * (c • v) p.2 = c * (u p.1 * v p.2)
        rw [hcv, Pi.smul_apply, smul_eq_mul]
        ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    apply Lp.ext
    filter_upwards [productKernel_ae (u + v) w, productKernel_ae u w,
      productKernel_ae v w, ae_eq_prod_fst (Lp.coeFn_add u v),
      Lp.coeFn_add (productKernel u w) (productKernel v w)] with p hp hu hv hsum hab
    rw [hp, hab, Pi.add_apply, hu, hv]
    change ((u + v) p.1 * w p.2) = u p.1 * w p.2 + v p.1 * w p.2
    rw [hsum, Pi.add_apply, add_mul]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
    apply Lp.ext
    filter_upwards [productKernel_ae (c • u) v, productKernel_ae u v,
      ae_eq_prod_fst (Lp.coeFn_smul c u), Lp.coeFn_smul c (productKernel u v)] with p hp hu hcu hab
    rw [hp, hab, Pi.smul_apply, hu]
    change (c • u) p.1 * v p.2 = c * (u p.1 * v p.2)
    rw [hcu, Pi.smul_apply, smul_eq_mul, mul_assoc]

private def tensorKernelLinear : H ⊗[ℂ] H →ₗ[ℂ] K₂ :=
  TensorProduct.lift productKernelBilinear

omit [IsFiniteMeasure μ] in
private theorem tensorKernelLinear_tmul (u v : H) :
    tensorKernelLinear (u ⊗ₜ[ℂ] v) = productKernel u v := rfl

private theorem inner_productKernel (u v a b : H) :
    inner ℂ (productKernel u v) (productKernel a b) = inner ℂ u a * inner ℂ v b := by
  simp only [L2.inner_def, RCLike.inner_apply]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [productKernel_ae u v, productKernel_ae a b] with p hp hq
  change (productKernel a b) p * conj ((productKernel u v) p) =
    (a p.1 * conj (u p.1)) * (b p.2 * conj (v p.2))
  rw [hp, hq, map_mul]
  ring

private theorem inner_tensorKernelLinear (g h : H ⊗[ℂ] H) :
    inner ℂ (tensorKernelLinear g) (tensorKernelLinear h) = inner ℂ g h := by
  induction g using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
  | tmul u v =>
    induction h using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | tmul a b =>
      rw [tensorKernelLinear_tmul, tensorKernelLinear_tmul, TensorProduct.inner_tmul,
        inner_productKernel]

private def tensorKernel : H ⊗[ℂ] H →ₗᵢ[ℂ] K₂ :=
  tensorKernelLinear.isometryOfInner inner_tensorKernelLinear

private theorem tensorKernel_tmul (u v : H) : tensorKernel (u ⊗ₜ[ℂ] v) = productKernel u v := rfl

private theorem denseRange_tensorKernel : DenseRange (tensorKernel (μ := μ)) := by
  let D := (tensorKernel (μ := μ)).toLinearMap.range
  have hspan : Submodule.span ℂ (rectangularKernels (μ := μ)) ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, t, hs, ht, rfl⟩
    let u : H := indicatorConstLp 2 hs (measure_ne_top μ _) (1 : ℂ)
    let v : H := indicatorConstLp 2 ht (measure_ne_top μ _) (1 : ℂ)
    refine ⟨u ⊗ₜ v, ?_⟩
    change productKernel u v = _
    apply Lp.ext
    have hu : u =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
    have hv : v =ᵐ[μ] t.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
    have he : (indicatorConstLp 2 (hs.prod ht) (measure_ne_top (μ.prod μ) _) (1 : ℂ)) =ᵐ[μ.prod μ]
        (s ×ˢ t).indicator (fun _ => 1) := indicatorConstLp_coeFn
    filter_upwards [productKernel_ae u v, ae_eq_prod_fst hu, ae_eq_prod_snd hv, he]
      with p hp h₁ h₂ h₃
    rw [hp, h₁, h₂, h₃]
    by_cases hps : p.1 ∈ s <;> by_cases hpt : p.2 ∈ t <;> simp [hps, hpt]
  have htop : D.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← rectangularKernels_span_dense (μ := μ)]
    exact Submodule.topologicalClosure_mono hspan
  change Dense (D : Set K₂)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop]
  rfl

private theorem fredholmKernelToOperator_productKernel (u v : H) :
    fredholmKernelToOperator (productKernel u v) = rankOne ℂ u (star v) := by
  have he : (productKernel u v : X × X → ℂ) =ᵐ[μ.prod μ] rankOneKernel u (star v) := by
    filter_upwards [productKernel_ae u v, ae_eq_prod_snd (Lp.coeFn_star v)] with p hp hs
    change (productKernel u v) p = u p.1 * conj ((star v) p.2)
    change (star v : H) p.2 = conj (v p.2) at hs
    rw [hp, hs, starRingEnd_self_apply]
  change fredholmIntegralOperator (Lp.memLp (productKernel u v)) = _
  rw [fredholmIntegralOperator_congr _ (memLp_rankOneKernel u (star v)) he,
    fredholmIntegralOperator_rankOneKernel]

private def tensorLeftComposition (B : H →L[ℂ] H) : H ⊗[ℂ] H →ₗ[ℂ] K₂ :=
  tensorKernel.toLinearMap.comp (B.rTensor H).toLinearMap

private theorem norm_tensorLeftComposition_le (B : H →L[ℂ] H) (q : H ⊗[ℂ] H) :
    ‖tensorLeftComposition B q‖ ≤ ‖B‖ * ‖tensorKernel q‖ := by
  change ‖tensorKernel (B.rTensor H q)‖ ≤ ‖B‖ * ‖tensorKernel q‖
  simp only [LinearIsometry.norm_map]
  exact ((B.rTensor H).le_opNorm q).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_rTensor_le (G := H) B) (norm_nonneg _))

/-- Left composition by a bounded operator lifts to the space of
square-integrable kernels. -/
def fredholmKernelLeftComposition (B : H →L[ℂ] H) : K₂ →L[ℂ] K₂ :=
  (tensorLeftComposition B).extendOfNorm tensorKernel.toLinearMap

/-- Postcomposing a square-integrable kernel operator by a bounded
operator is represented by a square-integrable kernel. -/
theorem fredholmKernelToOperator_leftComposition (B : H →L[ℂ] H) (q : K₂) :
    fredholmKernelToOperator (fredholmKernelLeftComposition B q) =
      B * fredholmKernelToOperator q := by
  refine denseRange_tensorKernel.induction_on q
    (isClosed_eq (fredholmKernelToOperator.continuous.comp
      (fredholmKernelLeftComposition B).continuous)
      (continuous_const.mul fredholmKernelToOperator.continuous)) ?_
  intro t
  have hExt : fredholmKernelLeftComposition B (tensorKernel t) = tensorLeftComposition B t :=
    LinearMap.extendOfNorm_eq denseRange_tensorKernel ⟨‖B‖, norm_tensorLeftComposition_le B⟩ t
  rw [hExt]
  suffices ∀ r : H ⊗[ℂ] H, fredholmKernelToOperator (tensorLeftComposition B r) =
      B * fredholmKernelToOperator (tensorKernel r) from this t
  intro r
  induction r using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  | tmul u v =>
    change fredholmKernelToOperator (tensorKernel (B u ⊗ₜ v)) =
      B * fredholmKernelToOperator (tensorKernel (u ⊗ₜ v))
    rw [tensorKernel_tmul, tensorKernel_tmul, fredholmKernelToOperator_productKernel,
      fredholmKernelToOperator_productKernel, ContinuousLinearMap.mul_def, comp_rankOne]

end KernelComposition

section Fredholm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {k : X × X → ℂ}

local notation "H" => Lp ℂ 2 μ

set_option maxHeartbeats 600000 in
-- The compact-operator theorem elaborates through the complex L² range coercions.
private theorem fredholmSecondKind_isClosed_range (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) :
    IsClosed ((fredholmSecondKind hk z).range : Set H) := by
  have hc : IsCompactOperator (⇑(z • fredholmIntegralOperator hk)) :=
    (isCompactOperator_fredholmIntegralOperator hk).smul z
  simpa only [fredholmSecondKind, one_smul] using
    hc.isClosed_range_smul_sub (K := z • fredholmIntegralOperator hk)
      (μ := (1 : ℂ)) one_ne_zero

set_option maxHeartbeats 600000 in
-- The compact-kernel theorem elaborates through powers of the complex L² operator.
private theorem fredholmSecondKind_finiteDimensional_ker (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) :
    FiniteDimensional ℂ (fredholmSecondKind hk z).ker := by
  have hc : IsCompactOperator (⇑(z • fredholmIntegralOperator hk)) :=
    (isCompactOperator_fredholmIntegralOperator hk).smul z
  have h := hc.finiteDimensional_ker_pow (K := z • fredholmIntegralOperator hk)
    (μ := (1 : ℂ)) one_ne_zero 1
  have heq : ((1 : ℂ) • (1 : H →L[ℂ] H) - z • fredholmIntegralOperator hk) ^ (1 : ℕ)
      = fredholmSecondKind hk z := by simp [fredholmSecondKind]
  rw [heq] at h
  exact h

/-- **Equations (31) and (33)** of [benIsrael2003generalized], Chapter 9.
The two null spaces have the same finite dimension and the two ranges
are closed, with each range the orthogonal complement of the other kernel. -/
theorem fredholm_nullity_range (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) :
    let T := fredholmSecondKind hk z
    FiniteDimensional ℂ T.ker ∧ FiniteDimensional ℂ T.adjoint.ker ∧
      Module.finrank ℂ T.ker = Module.finrank ℂ T.adjoint.ker ∧
      IsClosed (T.range : Set H) ∧ IsClosed (T.adjoint.range : Set H) ∧
      T.range = T.adjoint.kerᗮ ∧ T.adjoint.range = T.kerᗮ := by
  intro T
  have hTd : FiniteDimensional ℂ T.ker := fredholmSecondKind_finiteDimensional_ker hk z
  have hTc : IsClosed (T.range : Set H) := fredholmSecondKind_isClosed_range hk z
  have hA : T.adjoint = fredholmSecondKind (memLp_adjointKernel hk) (conj z) :=
    fredholmSecondKind_adjoint hk z
  have hAd : FiniteDimensional ℂ T.adjoint.ker :=
    hA ▸ fredholmSecondKind_finiteDimensional_ker (memLp_adjointKernel hk) (conj z)
  have hAc : IsClosed (T.adjoint.range : Set H) :=
    hA ▸ fredholmSecondKind_isClosed_range (memLp_adjointKernel hk) (conj z)
  let : CompleteSpace T.range := completeSpace_coe_iff_isComplete.2 hTc.isComplete
  let : CompleteSpace T.adjoint.range := completeSpace_coe_iff_isComplete.2 hAc.isComplete
  have hc : IsCompactOperator (⇑(z • fredholmIntegralOperator hk)) :=
    (isCompactOperator_fredholmIntegralOperator hk).smul z
  have hindex := hc.index_smul_one_sub (T := z • fredholmIntegralOperator hk)
    (μ := (1 : ℂ)) one_ne_zero
  simp only [one_smul] at hindex
  change (T : H →ₗ[ℂ] H).index = 0 at hindex
  rw [LinearMap.index_eq_finrank_sub, sub_eq_zero] at hindex
  have hquot : Module.finrank ℂ (H ⧸ T.range) = Module.finrank ℂ T.adjoint.ker := by
    rw [← ContinuousLinearMap.orthogonal_range]
    exact LinearEquiv.finrank_eq T.range.quotientEquivOrthogonal.toLinearEquiv
  rw [hquot] at hindex
  refine ⟨hTd, hAd, by exact_mod_cast hindex, hTc, hAc, ?_, ?_⟩
  · rw [← ContinuousLinearMap.orthogonal_range, Submodule.orthogonal_orthogonal]
  · have h := ContinuousLinearMap.orthogonal_range T.adjoint
    rw [ContinuousLinearMap.adjoint_adjoint T] at h
    rw [← h, Submodule.orthogonal_orthogonal]

/-- **Fredholm property (d)** of [benIsrael2003generalized], Chapter 9.
A regular value is a parameter for which the homogeneous equation has
only the zero solution. The parameter zero is always regular. -/
def IsFredholmRegularValue (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) : Prop :=
  (fredholmSecondKind hk z).ker = ⊥

/-- **Fredholm property (e)** of [benIsrael2003generalized], Chapter 9.
At a characteristic value there is a nonzero homogeneous solution. -/
theorem not_isFredholmRegularValue_iff (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) :
    ¬IsFredholmRegularValue hk z ↔ ∃ x : H, x ≠ 0 ∧ fredholmSecondKind hk z x = 0 := by
  unfold IsFredholmRegularValue
  rw [Submodule.eq_bot_iff]
  push Not
  exact exists_congr fun _ => and_comm

/-- The Fredholm parameter is the reciprocal of the usual eigenvalue
of the integral operator. -/
theorem not_isFredholmRegularValue_iff_reciprocal (hk : MemLp k 2 (μ.prod μ))
    {z : ℂ} (hz : z ≠ 0) :
    ¬IsFredholmRegularValue hk z ↔
      ∃ x : H, x ≠ 0 ∧ fredholmIntegralOperator hk x = z⁻¹ • x := by
  rw [not_isFredholmRegularValue_iff]
  refine exists_congr fun x => and_congr_right_iff.mpr fun _ => ?_
  change x - z • fredholmIntegralOperator hk x = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    calc
      fredholmIntegralOperator hk x = z⁻¹ • (z • fredholmIntegralOperator hk x) :=
        (inv_smul_smul₀ hz _).symm
      _ = z⁻¹ • x := congrArg (z⁻¹ • ·) h.symm
  · intro h
    rw [h, smul_inv_smul₀ hz]

/-- **Fredholm property (d)** of [benIsrael2003generalized], Chapter 9.
At a regular value the second-kind coefficient is a continuous linear
equivalence, so every right-hand side has a unique solution. -/
theorem exists_fredholmSolutionEquiv (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    (hz : IsFredholmRegularValue hk z) :
    ∃ e : H ≃L[ℂ] H, e.toContinuousLinearMap = fredholmSecondKind hk z := by
  let T := fredholmSecondKind hk z
  change T.ker = ⊥ at hz
  have hT := fredholm_nullity_range hk z
  change FiniteDimensional ℂ T.ker ∧ FiniteDimensional ℂ T.adjoint.ker ∧
    Module.finrank ℂ T.ker = Module.finrank ℂ T.adjoint.ker ∧
    IsClosed (T.range : Set H) ∧ IsClosed (T.adjoint.range : Set H) ∧
    T.range = T.adjoint.kerᗮ ∧ T.adjoint.range = T.kerᗮ at hT
  obtain ⟨_, hd, hdim, _, _, hR, _⟩ := hT
  have hA : T.adjoint.ker = ⊥ := by
    rw [hz, finrank_bot] at hdim
    let : FiniteDimensional ℂ T.adjoint.ker := hd
    exact Submodule.finrank_eq_zero.mp hdim.symm
  have hr : T.range = ⊤ := by rw [hR, hA]; simp
  exact ⟨ContinuousLinearEquiv.ofBijective T hz hr, ContinuousLinearEquiv.coe_ofBijective T hz hr⟩

/-- **Equations (32) and (34)** of [benIsrael2003generalized], Chapter 9.
A resolvent kernel gives a two-sided bounded inverse in the form
(I+zR). -/
def IsFredholmResolvent (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) : Prop :=
  let T := fredholmSecondKind hk z
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  T * B = 1 ∧ B * T = 1

/-- A two-sided resolvent can exist only at a regular parameter. -/
theorem isFredholmRegularValue_of_resolvent (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) (hR : IsFredholmResolvent hk z hr) :
    IsFredholmRegularValue hk z := by
  let T := fredholmSecondKind hk z
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  change T.ker = ⊥
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  have h (w : H) : B (T w) = w := DFunLike.congr_fun hR.2 w
  exact (h x).symm.trans ((congrArg B hxy).trans (h y))

/-- **Equations (32) and (34)** of [benIsrael2003generalized], Chapter 9.
Every regular value admits a square-integrable resolvent kernel. -/
theorem fredholm_resolvent_exists (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    (hz : IsFredholmRegularValue hk z) :
    ∃ (r : X × X → ℂ) (hr : MemLp r 2 (μ.prod μ)), IsFredholmResolvent hk z hr := by
  obtain ⟨e, he⟩ := exists_fredholmSolutionEquiv hk z hz
  let B := e.symm.toContinuousLinearMap
  have hTB : fredholmSecondKind hk z * B = 1 := by
    rw [← he]
    apply ContinuousLinearMap.ext
    exact e.apply_symm_apply
  have hBT : B * fredholmSecondKind hk z = 1 := by
    rw [← he]
    apply ContinuousLinearMap.ext
    exact e.symm_apply_apply
  let q := fredholmKernelLeftComposition B (hk.toLp k)
  have hkernel : fredholmIntegralOperator (Lp.memLp q) = B * fredholmIntegralOperator hk := by
    change fredholmKernelToOperator (fredholmKernelLeftComposition B (hk.toLp k)) = _
    rw [fredholmKernelToOperator_leftComposition]
    congr 1
    exact fredholmIntegralOperator_congr _ _ (MemLp.coeFn_toLp hk)
  have hB : 1 + z • fredholmIntegralOperator (Lp.memLp q) = B := by
    rw [hkernel]
    apply ContinuousLinearMap.ext
    intro x
    have h := DFunLike.congr_fun hBT x
    change B (x - z • fredholmIntegralOperator hk x) = x at h
    rw [map_sub, map_smul] at h
    change x + z • B (fredholmIntegralOperator hk x) = B x
    calc
      x + z • B (fredholmIntegralOperator hk x) =
        (B x - z • B (fredholmIntegralOperator hk x)) + z • B (fredholmIntegralOperator hk x) :=
        congrArg (· + z • B (fredholmIntegralOperator hk x)) h.symm
      _ = B x := sub_add_cancel _ _
  refine ⟨q, Lp.memLp q, ?_⟩
  change fredholmSecondKind hk z * (1 + z • fredholmIntegralOperator (Lp.memLp q)) = 1 ∧
    (1 + z • fredholmIntegralOperator (Lp.memLp q)) * fredholmSecondKind hk z = 1
  rw [hB]
  exact ⟨hTB, hBT⟩

/-- **Equation (34)** of [benIsrael2003generalized], Chapter 9.
The kernel of the resolvent gives the unique solution in (L^2),
with its integral formula holding almost everywhere. -/
theorem fredholm_solution_resolvent (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ))
    (hR : IsFredholmResolvent hk z hr) (y : H) :
    ∃ x : H, fredholmSecondKind hk z x = y ∧
      (∀ w : H, fredholmSecondKind hk z w = y → w = x) ∧
      x =ᵐ[μ] fun s => y s + z * ∫ t, r (s, t) * y t ∂μ := by
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  let x := B y
  change fredholmSecondKind hk z * B = 1 ∧ B * fredholmSecondKind hk z = 1 at hR
  refine ⟨x, DFunLike.congr_fun hR.1 y, ?_, ?_⟩
  · intro w hw
    have h := DFunLike.congr_fun hR.2 w
    change B (fredholmSecondKind hk z w) = w at h
    rw [hw] at h
    exact h.symm
  · change (y + z • fredholmIntegralOperator hr y : H) =ᵐ[μ] _
    filter_upwards [Lp.coeFn_add y (z • fredholmIntegralOperator hr y),
      Lp.coeFn_smul z (fredholmIntegralOperator hr y), fredholmIntegralOperator_apply_ae hr y]
      with s h₁ h₂ h₃
    rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, smul_eq_mul]

/-- **Equations (33) and (35)** of [benIsrael2003generalized], Chapter 9.
An equation is consistent exactly when its right-hand side is orthogonal
to the adjoint null space. From a particular solution all solutions are
obtained by adding a homogeneous solution. -/
theorem fredholm_alternative (hk : MemLp k 2 (μ.prod μ)) (z : ℂ) (y : H) :
    let T := fredholmSecondKind hk z
    ((∃ x : H, T x = y) ↔ ∀ u ∈ T.adjoint.ker, inner ℂ u y = 0) ∧
      (∀ x₀ : H, T x₀ = y → ∀ x : H, T x = y ↔ ∃ v ∈ T.ker, x = x₀ + v) := by
  intro T
  have hR : T.range = T.adjoint.kerᗮ := (fredholm_nullity_range hk z).2.2.2.2.2.1
  constructor
  · change y ∈ T.range ↔ _
    rw [hR, Submodule.mem_orthogonal]
  · intro x₀ hx₀ x
    constructor
    · intro hx
      refine ⟨x - x₀, ?_, by abel⟩
      change T (x - x₀) = 0
      rw [map_sub, hx, hx₀, sub_self]
    · rintro ⟨v, hv, rfl⟩
      change T v = 0 at hv
      rw [map_add, hx₀, hv, add_zero]

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 9.
A pseudoresolvent produces a solution for every consistent right-hand side. -/
def IsFredholmPseudoresolvent (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) : Prop :=
  let T := fredholmSecondKind hk z
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  ∀ y ∈ T.range, T (B y) = y

/-- **Exercise 19** of [benIsrael2003generalized], Chapter 9.
The pseudoresolvent condition is the inner-inverse identity. -/
theorem isFredholmPseudoresolvent_iff (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) :
    IsFredholmPseudoresolvent hk z hr ↔
      fredholmSecondKind hk z * (1 + z • fredholmIntegralOperator hr) *
        fredholmSecondKind hk z = fredholmSecondKind hk z := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact h _ ⟨x, rfl⟩
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    exact DFunLike.congr_fun h x

end Fredholm


section KernelsAndExercises

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {k : X × X → ℂ}

local notation "H" => Lp ℂ 2 μ
local notation "K₂" => Lp ℂ 2 (μ.prod μ)

/-- The operator of an (L^2) class agrees with the operator of the chosen kernel. -/
theorem fredholmKernelToOperator_toLp (hk : MemLp k 2 (μ.prod μ)) :
    fredholmKernelToOperator (hk.toLp k) = fredholmIntegralOperator hk :=
  fredholmIntegralOperator_congr _ _ (MemLp.coeFn_toLp hk)

/-- A square-integrable kernel whose operator vanishes is zero almost everywhere. -/
theorem ae_eq_zero_of_fredholmIntegralOperator_eq_zero (hk : MemLp k 2 (μ.prod μ))
    (hK : fredholmIntegralOperator hk = 0) : k =ᵐ[μ.prod μ] 0 := by
  have hI := hk.integrable (by norm_num)
  apply ae_eq_zero_of_rectangle_integrals hI
  intro s t hs ht
  rw [setIntegral_prod k hI.integrableOn]
  let v : H := indicatorConstLp 2 ht (measure_ne_top μ _) (1 : ℂ)
  have hv : v =ᵐ[μ] t.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
  have hz : fredholmIntegralOperator hk v =ᵐ[μ] (0 : X → ℂ) := by
    rw [hK, zero_apply]
    exact Lp.coeFn_zero ℂ 2 μ
  have hz' : ∀ᵐ x ∂μ, (∫ y in t, k (x, y) ∂μ) = 0 := by
    filter_upwards [fredholmIntegralOperator_apply_ae hk v, hz] with x ha hb
    have hr : (∫ y, k (x, y) * v y ∂μ) = ∫ y in t, k (x, y) ∂μ := by
      rw [← integral_indicator ht]
      apply integral_congr_ae
      filter_upwards [hv] with y hy
      change k (x, y) * v y = t.indicator (fun z => k (x, z)) y
      rw [hy]
      by_cases hyt : y ∈ t <;> simp [hyt]
    rw [← hr, ← ha]
    exact hb
  rw [integral_congr_ae (ae_restrict_of_ae hz')]
  simp

/-- The integral operator determines the (L^2) class of its kernel. -/
theorem fredholmKernelToOperator_injective :
    Function.Injective (fredholmKernelToOperator (μ := μ)) := by
  intro q r h
  have hzero : fredholmKernelToOperator (q - r) = 0 := by rw [map_sub, h, sub_self]
  apply sub_eq_zero.mp
  apply Lp.ext
  exact (ae_eq_zero_of_fredholmIntegralOperator_eq_zero (Lp.memLp (q - r)) hzero).trans
    (Lp.coeFn_zero ℂ 2 (μ.prod μ)).symm

/-- At a nonzero regular parameter a two-sided resolvent determines
a unique kernel up to equality almost everywhere. -/
theorem fredholm_resolvent_ae_unique (hk : MemLp k 2 (μ.prod μ)) {z : ℂ} (hz : z ≠ 0)
    {r s : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) (hs : MemLp s 2 (μ.prod μ))
    (hR : IsFredholmResolvent hk z hr) (hS : IsFredholmResolvent hk z hs) :
    r =ᵐ[μ.prod μ] s := by
  let A := fredholmSecondKind hk z
  let B := (1 + z • fredholmIntegralOperator hr : H →L[ℂ] H)
  let C := (1 + z • fredholmIntegralOperator hs : H →L[ℂ] H)
  change A * B = 1 ∧ B * A = 1 at hR
  change A * C = 1 ∧ C * A = 1 at hS
  have hBC : B = C := by
    calc
      B = B * (A * C) := by rw [hS.1, mul_one]
      _ = C := by rw [← mul_assoc, hR.2, one_mul]
  have hop : fredholmIntegralOperator hr = fredholmIntegralOperator hs := by
    have h := add_left_cancel hBC
    exact smul_right_injective (H →L[ℂ] H) hz h
  have hh : hr.toLp r = hs.toLp s := by
    apply fredholmKernelToOperator_injective
    simpa only [fredholmKernelToOperator_toLp] using hop
  exact (MemLp.coeFn_toLp hr).symm.trans (hh ▸ MemLp.coeFn_toLp hs)

/-- A separated kernel class represents the rank-one operator defined
by the outer product of its two vectors. -/
def rankOneKernelClass (u v : H) : K₂ :=
  (memLp_rankOneKernel u v).toLp _

/-- The operator associated with the separated kernel is the corresponding rank-one operator. -/
theorem fredholmKernelToOperator_rankOneKernelClass (u v : H) :
    fredholmKernelToOperator (rankOneKernelClass u v) = rankOne ℂ u v := by
  rw [rankOneKernelClass, fredholmKernelToOperator_toLp, fredholmIntegralOperator_rankOneKernel]

/-- **Equation (35)** of [benIsrael2003generalized], Chapter 9.
A finite basis of the homogeneous null space parametrizes all solutions. -/
theorem fredholm_alternative_basis (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (fredholmSecondKind hk z).ker)
    {y x₀ : H} (hx₀ : fredholmSecondKind hk z x₀ = y) (x : H) :
    fredholmSecondKind hk z x = y ↔
      ∃ c : ι → ℂ, x = x₀ + ∑ i, c i • (b i : H) := by
  rw [(fredholm_alternative hk z y).2 x₀ hx₀ x]
  constructor
  · rintro ⟨v, hv, rfl⟩
    let w : (fredholmSecondKind hk z).ker := ⟨v, hv⟩
    refine ⟨fun i => b.repr w i, ?_⟩
    congr 1
    have h := congrArg (fun a : (fredholmSecondKind hk z).ker => (a : H)) (b.sum_repr w)
    change ((∑ i, b.repr w i • b i : (fredholmSecondKind hk z).ker) : H) = v at h
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
  · rintro ⟨c, rfl⟩
    exact ⟨_, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2, rfl⟩

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 9.
A product kernel (u(s)v(t)) with (int uv=0) has square zero.
Every scalar is a regular value, and the original kernel is a resolvent. -/
theorem exercise_9_21 (u v : H) (huv : (∫ t, u t * v t ∂μ) = 0) (z : ℂ) :
    let hk := memLp_productKernel u v
    IsFredholmRegularValue hk z ∧ IsFredholmResolvent hk z hk := by
  intro hk
  have hK : fredholmIntegralOperator hk = rankOne ℂ u (star v) := by
    rw [← fredholmKernelToOperator_toLp hk]
    exact fredholmKernelToOperator_productKernel u v
  have hinner : inner ℂ (star v) u = 0 := by
    rw [L2.inner_def, ← huv]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with t ht
    change u t * conj ((star v : H) t) = u t * v t
    change (star v : H) t = conj (v t) at ht
    rw [ht, starRingEnd_self_apply]
  let K := fredholmIntegralOperator hk
  have hKK : K * K = 0 := by
    change fredholmIntegralOperator hk * fredholmIntegralOperator hk = 0
    rw [hK, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hinner, zero_smul]
  have hsolve : IsFredholmResolvent hk z hk := by
    change (1 - z • K) * (1 + z • K) = 1 ∧ (1 + z • K) * (1 - z • K) = 1
    have hsquare : (z • K) * (z • K) = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      have hw := DFunLike.congr_fun hKK w
      change K (K w) = 0 at hw
      change z • K (z • K w) = 0
      rw [map_smul, hw, smul_zero, smul_zero]
    constructor
    · rw [sub_mul, one_mul, mul_add, mul_one, hsquare, add_zero, add_sub_cancel_right]
    · rw [mul_sub, mul_one, add_mul, one_mul, hsquare, add_zero, add_sub_cancel_right]
  exact ⟨isFredholmRegularValue_of_resolvent hk z hk hsolve, hsolve⟩

end KernelsAndExercises

section Hurwitz

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {k : X × X → ℂ}

local notation "H" => Lp ℂ 2 μ
local notation "K₂" => Lp ℂ 2 (μ.prod μ)

/-- **Exercise 18**, Equation (36), of [benIsrael2003generalized], Chapter 9.
The Hurwitz modification subtracts the finite sum of the paired null-space
basis kernels divided by the characteristic parameter. -/
def fredholmHurwitzKernel (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).ker)
    (c : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).adjoint.ker) : K₂ :=
  hk.toLp k - z⁻¹ • ∑ i, rankOneKernelClass (c i : H) (b i : H)

private theorem fredholmSecondKind_hurwitz_eq (hk : MemLp k 2 (μ.prod μ)) {z : ℂ} (hz : z ≠ 0)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).ker)
    (c : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).adjoint.ker) :
    fredholmSecondKind (Lp.memLp (fredholmHurwitzKernel hk z b c)) z =
      fredholmSecondKind hk z + ∑ i, rankOne ℂ (c i : H) (b i : H) := by
  change 1 - z • fredholmKernelToOperator (fredholmHurwitzKernel hk z b c) = _
  simp only [fredholmHurwitzKernel, map_sub, map_smul, map_sum, fredholmKernelToOperator_toLp,
    fredholmKernelToOperator_rankOneKernelClass, fredholmSecondKind, smul_sub, smul_inv_smul₀ hz]
  abel

omit [IsFiniteMeasure μ] in
private theorem rankOne_sum_basis_apply {ι : Type*} [Fintype ι] (A : Submodule ℂ H)
    (b : OrthonormalBasis ι ℂ A) (c : ι → H) (i : ι) :
    (∑ j, rankOne ℂ (c j) (b j : H)) (b i : H) = c i := by
  classical
  simp only [sum_apply, rankOne_apply]
  have h (j : ι) : inner ℂ (b j : H) (b i : H) = if j = i then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal j i
  simp_rw [h, ite_smul, one_smul, zero_smul]
  simp

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 9.
The Hurwitz modification is regular at the characteristic value. Its
ordinary resolvent is a pseudoresolvent of the original equation and
pairs the chosen adjoint null-space basis with the original basis. -/
theorem exercise_9_18 (hk : MemLp k 2 (μ.prod μ)) {z : ℂ} (hz : z ≠ 0)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).ker)
    (c : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).adjoint.ker) :
    IsFredholmRegularValue (Lp.memLp (fredholmHurwitzKernel hk z b c)) z ∧
      ∃ (r : X × X → ℂ) (hr : MemLp r 2 (μ.prod μ)),
        IsFredholmResolvent (Lp.memLp (fredholmHurwitzKernel hk z b c)) z hr ∧
        IsFredholmPseudoresolvent hk z hr ∧
        (∀ x ∈ (fredholmSecondKind hk z).adjoint.range,
          (1 + z • fredholmIntegralOperator hr : H →L[ℂ] H) (fredholmSecondKind hk z x) = x) ∧
        (∀ i, (1 + z • fredholmIntegralOperator hr : H →L[ℂ] H) (c i : H) = (b i : H)) := by
  let A := fredholmSecondKind hk z
  let U : H →L[ℂ] H := ∑ i, rankOne ℂ (c i : H) (b i : H)
  let V : H →L[ℂ] H := ∑ i, rankOne ℂ (b i : H) (c i : H)
  let q₀ := fredholmHurwitzKernel hk z b c
  have hA₀ : fredholmSecondKind (Lp.memLp q₀) z = A + U :=
    fredholmSecondKind_hurwitz_eq hk hz b c
  have hRange : A.range = A.adjoint.kerᗮ := (fredholm_nullity_range hk z).2.2.2.2.2.1
  have hAdjRange : A.adjoint.range = A.kerᗮ := (fredholm_nullity_range hk z).2.2.2.2.2.2
  have hU (i : ι) : U (b i : H) = c i := rankOne_sum_basis_apply _ b (fun i => c i) i
  have hV (i : ι) : V (c i : H) = b i := rankOne_sum_basis_apply _ c (fun i => b i) i
  have hU_apply (x : H) : U x = ∑ i, inner ℂ (b i : H) x • (c i : H) := by
    simp only [U, sum_apply, rankOne_apply]
  have hU_range (x : H) : U x ∈ A.adjoint.ker := by
    rw [hU_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (c i).2
  have hU_zero (x : H) (hx : x ∈ A.kerᗮ) : U x = 0 := by
    rw [hU_apply]
    have h (i : ι) : inner ℂ (b i : H) x = 0 := (Submodule.mem_orthogonal _ _).mp hx _ (b i).2
    simp [h]
  have hV_U (x : H) (hx : x ∈ A.ker) : V (U x) = x := by
    rw [hU_apply, map_sum]
    simp only [map_smul, hV]
    have h := congrArg Subtype.val (b.sum_repr' (⟨x, hx⟩ : A.ker))
    simpa using h
  have hreg : IsFredholmRegularValue (Lp.memLp q₀) z := by
    unfold IsFredholmRegularValue
    rw [hA₀, Submodule.eq_bot_iff]
    intro x hx
    change A x + U x = 0 at hx
    have hAx : A x ∈ A.adjoint.kerᗮ := hRange ▸ LinearMap.mem_range_self A.toLinearMap x
    have hUx : A x ∈ A.adjoint.ker :=
      (eq_neg_of_add_eq_zero_left hx).symm ▸ Submodule.neg_mem _ (hU_range x)
    have hA0 : A x = 0 :=
      (Submodule.disjoint_def.mp A.adjoint.ker.orthogonal_disjoint) _ hUx hAx
    have hU0 : U x = 0 := by simpa only [hA0, zero_add] using hx
    have h := hV_U x (show x ∈ A.ker from hA0)
    rwa [hU0, map_zero, eq_comm] at h
  obtain ⟨r, hr, hR⟩ := fredholm_resolvent_exists (Lp.memLp q₀) z hreg
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  have hB (x : H) : B ((A + U) x) = x := by
    have he := hR.2
    change B * fredholmSecondKind (Lp.memLp q₀) z = 1 at he
    rw [hA₀] at he
    exact DFunLike.congr_fun he x
  have hleft (x : H) (hx : x ∈ A.adjoint.range) : B (A x) = x := by
    simpa only [add_apply, hU_zero x (hAdjRange ▸ hx), add_zero] using hB x
  refine ⟨hreg, r, hr, hR, ?_, hleft, ?_⟩
  · rintro y ⟨x, rfl⟩
    let : FiniteDimensional ℂ A.ker := (fredholm_nullity_range hk z).1
    let v := x - A.ker.starProjection x
    have hv : v ∈ A.adjoint.range := hAdjRange.symm ▸ A.ker.sub_starProjection_mem_orthogonal x
    have he : A v = A x := by
      have hp : A (A.ker.starProjection x) = 0 := A.ker.starProjection_apply_mem x
      simp [v, hp]
    change A (B (A x)) = A x
    rw [← he, hleft v hv]
  · intro i
    have hb : A (b i : H) = 0 := (b i).2
    change B (c i : H) = b i
    simpa only [add_apply, hb, hU i, zero_add] using hB (b i : H)

/-- **Exercise 19**, Equation (37), of [benIsrael2003generalized], Chapter 9.
Adding any finite linear combination of the paired null-space products
preserves the pseudoresolvent property. -/
theorem exercise_9_19_perturbation (hk : MemLp k 2 (μ.prod μ)) (z : ℂ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).ker)
    (c : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).adjoint.ker)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ)) (hR : IsFredholmPseudoresolvent hk z hr)
    (w : ι → ι → ℂ) :
    let q := hr.toLp r + ∑ i, ∑ j, w i j • rankOneKernelClass (b i : H) (c j : H)
    IsFredholmPseudoresolvent hk z (Lp.memLp q) := by
  intro q
  let A := fredholmSecondKind hk z
  let D : H →L[ℂ] H := ∑ i, ∑ j, w i j • rankOne ℂ (b i : H) (c j : H)
  have hq : fredholmKernelToOperator q = fredholmIntegralOperator hr + D := by
    simp [q, D, map_sum, fredholmKernelToOperator_toLp, fredholmKernelToOperator_rankOneKernelClass]
  have hD (y : H) : A (D y) = 0 := by
    simp only [D, sum_apply, smul_apply, rankOne_apply, map_sum, map_smul]
    have hb (i : ι) : A (b i : H) = 0 := (b i).2
    simp [hb]
  intro y hy
  change A ((1 + z • fredholmKernelToOperator q : H →L[ℂ] H) y) = y
  rw [hq]
  have he : (1 + z • (fredholmIntegralOperator hr + D) : H →L[ℂ] H) y =
      (1 + z • fredholmIntegralOperator hr : H →L[ℂ] H) y + z • D y := by
    simp only [smul_add, add_assoc, add_apply, smul_apply]
  rw [he, map_add, map_smul, hD, smul_zero, add_zero]
  exact hR y hy

/-- **Exercise 20**, Equations (41)–(42), of [benIsrael2003generalized], Chapter 9.
Subtracting the opposite basis kernels from the Hurwitz resolvent gives
the maximal Tseng inverse of the original second-kind operator. -/
theorem exercise_9_20 (hk : MemLp k 2 (μ.prod μ)) {z : ℂ} (hz : z ≠ 0)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).ker)
    (c : OrthonormalBasis ι ℂ (fredholmSecondKind hk z).adjoint.ker)
    {r : X × X → ℂ} (hr : MemLp r 2 (μ.prod μ))
    (hB : IsFredholmResolvent (Lp.memLp (fredholmHurwitzKernel hk z b c)) z hr) :
    let q := hr.toLp r - z⁻¹ • ∑ i, rankOneKernelClass (b i : H) (c i : H)
    (1 + z • fredholmKernelToOperator q : H →L[ℂ] H).toLinearMap.toPMap ⊤ =
      maximalTsengInverse ((fredholmSecondKind hk z).toLinearMap.toPMap ⊤) := by
  intro q
  let A := fredholmSecondKind hk z
  let U : H →L[ℂ] H := ∑ i, rankOne ℂ (c i : H) (b i : H)
  let V : H →L[ℂ] H := ∑ i, rankOne ℂ (b i : H) (c i : H)
  let B : H →L[ℂ] H := 1 + z • fredholmIntegralOperator hr
  have hq : (1 + z • fredholmKernelToOperator q : H →L[ℂ] H) = B - V := by
    simp only [q, V, B, map_sub, map_smul, map_sum, fredholmKernelToOperator_toLp,
      fredholmKernelToOperator_rankOneKernelClass, smul_sub, smul_inv_smul₀ hz]
    abel
  have hBA : B * (A + U) = 1 := by
    have h := hB.2
    change B * fredholmSecondKind (Lp.memLp (fredholmHurwitzKernel hk z b c)) z = 1 at h
    rwa [fredholmSecondKind_hurwitz_eq hk hz b c] at h
  have hA : A.range = A.adjoint.kerᗮ := (fredholm_nullity_range hk z).2.2.2.2.2.1
  have hAadj : A.adjoint.range = A.kerᗮ := (fredholm_nullity_range hk z).2.2.2.2.2.2
  have hRangeClosed : IsClosed (A.range : Set H) := fredholmSecondKind_isClosed_range hk z
  have hB_apply (x : H) : B ((A + U) x) = x := DFunLike.congr_fun hBA x
  have hInv : B - V = boundedMoorePenroseInverse A hRangeClosed := by
    apply (theorem_3e A hRangeClosed (B - V)).mp
    constructor
    · intro x hx
      have hUx : U x = 0 := by
        have hx' : x ∈ A.kerᗮ := hAadj ▸ hx
        have h (i : ι) : inner ℂ (b i : H) x = 0 := (Submodule.mem_orthogonal _ _).mp hx' _ (b i).2
        simp [U, sum_apply, rankOne_apply, h]
      have hVx : V (A x) = 0 := by
        have hm : A x ∈ A.adjoint.kerᗮ := hA ▸ LinearMap.mem_range_self A.toLinearMap x
        have h (i : ι) : inner ℂ (c i : H) (A x) = 0 :=
          (Submodule.mem_orthogonal _ _).mp hm _ (c i).2
        simp [V, sum_apply, rankOne_apply, h]
      have h := hB_apply x
      simpa only [sub_apply, hVx, sub_zero] using
        (show B (A x) = x by simpa only [add_apply, hUx, add_zero] using h)
    · intro y hy
      have hBasis (i : ι) : (B - V) (c i : H) = 0 := by
        rw [sub_apply, rankOne_sum_basis_apply _ c (fun i => b i)]
        have hU (i : ι) : U (b i : H) = c i := rankOne_sum_basis_apply _ b (fun i => c i) i
        have hb : A (b i : H) = 0 := (b i).2
        have h : B (c i : H) = b i := by
          simpa only [add_apply, hb, hU i, zero_add] using hB_apply (b i : H)
        rw [h, sub_self]
      have hsum := congrArg (fun w : A.adjoint.ker => (w : H))
        (c.sum_repr' (⟨y, hy⟩ : A.adjoint.ker))
      change ((∑ i, inner ℂ (c i) (⟨y, hy⟩ : A.adjoint.ker) • c i : A.adjoint.ker) : H) = y at hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      rw [← hsum, map_sum]
      simp [hBasis]
  rw [hq, hInv]
  exact boundedMoorePenroseInverse_asPartial A hRangeClosed

end Hurwitz

/-- Lebesgue measure restricted to the bounded interval in Equation (30). -/
def fredholmIntervalMeasure (a b : ℝ) : Measure ℝ := volume.restrict (Icc a b)

instance (a b : ℝ) : IsFiniteMeasure (fredholmIntervalMeasure a b) where
  measure_univ_lt_top := by
    rw [fredholmIntervalMeasure, Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top

section DegenerateKernels

open scoped Matrix TensorProduct

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι]

local notation "H" => Lp ℂ 2 μ
local notation "K₂" => Lp ℂ 2 (μ.prod μ)

/-- **Exercise 22**, Equation (43), of [benIsrael2003generalized], Chapter 9.
A degenerate kernel is a finite sum of products of two (L^2) vectors. -/
def fredholmDegenerateKernel (f g : ι → H) : K₂ :=
  ∑ i, productKernel (f i) (g i)

/-- **Exercise 22** of [benIsrael2003generalized], Chapter 9.
Every square-integrable kernel can be approximated in (L^2) by
degenerate kernels. -/
theorem exists_fredholmDegenerateKernel_near (q : K₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (f g : Fin n → H), ‖q - fredholmDegenerateKernel f g‖ < ε := by
  obtain ⟨t, h⟩ := Metric.denseRange_iff.mp (denseRange_tensorKernel (μ := μ)) q ε hε
  obtain ⟨n, f, g, ht⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨n, f, g, ?_⟩
  rw [dist_eq_norm, ht, map_sum] at h
  simpa only [tensorKernel_tmul, fredholmDegenerateKernel] using h

/-- The operator of a degenerate kernel is the sum of its rank-one terms. -/
theorem fredholmKernelToOperator_degenerate (f g : ι → H) :
    fredholmKernelToOperator (fredholmDegenerateKernel f g) =
      ∑ i, rankOne ℂ (f i) (star (g i)) := by
  simp only [fredholmDegenerateKernel, map_sum, fredholmKernelToOperator_productKernel]

/-- **Exercise 22(a)** of [benIsrael2003generalized], Chapter 9.
The finite matrix for the degenerate integral equation. -/
def fredholmDegenerateMatrix (f g : ι → H) : Matrix ι ι ℂ :=
  Matrix.of fun i j => inner ℂ (star (g i)) (f j)

omit [IsFiniteMeasure μ] [Fintype ι] in
/-- Its entries are the integrals of (f_j(s)g_i(s)). -/
theorem fredholmDegenerateMatrix_apply (f g : ι → H) (i j : ι) :
    fredholmDegenerateMatrix f g i j = ∫ s, f j s * g i s ∂μ := by
  rw [fredholmDegenerateMatrix, Matrix.of_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (g i)] with x hx
  change f j x * conj ((star (g i) : H) x) = f j x * g i x
  change (star (g i) : H) x = conj (g i x) at hx
  rw [hx, starRingEnd_self_apply]

/-- **Exercise 22(a)** of [benIsrael2003generalized], Chapter 9.
A nonzero characteristic parameter of the degenerate kernel is the
reciprocal of an eigenvalue of its finite matrix. -/
theorem exercise_9_22a (f g : ι → H) {z : ℂ} (hz : z ≠ 0) :
    ¬IsFredholmRegularValue (Lp.memLp (fredholmDegenerateKernel f g)) z ↔
      ∃ w : ι → ℂ, w ≠ 0 ∧ (fredholmDegenerateMatrix f g) *ᵥ w = z⁻¹ • w := by
  rw [not_isFredholmRegularValue_iff_reciprocal _ hz]
  change (∃ x : H, x ≠ 0 ∧ fredholmKernelToOperator (fredholmDegenerateKernel f g) x = z⁻¹ • x) ↔ _
  rw [fredholmKernelToOperator_degenerate]
  let K : H →L[ℂ] H := ∑ i, rankOne ℂ (f i) (star (g i))
  let M := fredholmDegenerateMatrix f g
  let L (x : H) : ι → ℂ := fun i => inner ℂ (star (g i)) x
  let U (w : ι → ℂ) : H := ∑ i, w i • f i
  have hK (x : H) : K x = U (L x) := by simp only [K, U, L, sum_apply, rankOne_apply]
  have hM (w : ι → ℂ) : M *ᵥ w = L (U w) := by
    funext i
    simp only [M, fredholmDegenerateMatrix, L, U, Matrix.mulVec, dotProduct, Matrix.of_apply,
      inner_sum, inner_smul_right, mul_comm]
  constructor
  · rintro ⟨x, hx, he⟩
    change K x = z⁻¹ • x at he
    refine ⟨L x, ?_, ?_⟩
    · intro hzero
      have he' := he
      rw [hK, hzero] at he'
      have hU : U 0 = 0 := by simp [U]
      rw [hU, eq_comm, smul_eq_zero] at he'
      exact hx (he'.resolve_left (inv_ne_zero hz))
    · rw [hM, ← hK, he]
      funext i
      simp [L, inner_smul_right]
  · rintro ⟨w, hw, he⟩
    change M *ᵥ w = z⁻¹ • w at he
    rw [hM] at he
    refine ⟨U w, ?_, ?_⟩
    · intro hzero
      rw [hzero] at he
      have hL : L 0 = 0 := by funext i; simp [L]
      rw [hL, eq_comm, smul_eq_zero] at he
      exact hw (he.resolve_left (inv_ne_zero hz))
    · change K (U w) = z⁻¹ • U w
      rw [hK, he]
      simp [U, Finset.smul_sum, smul_smul]

/-- **Exercise 22(b)** of [benIsrael2003generalized], Chapter 9.
Eigenfunctions belong to the span of the first factors. For the adjoint,
they belong to the span of the conjugates of the second factors. -/
theorem exercise_9_22b (f g : ι → H) {η : ℂ} (hη : η ≠ 0) (x : H) :
    let K := fredholmKernelToOperator (fredholmDegenerateKernel f g)
    (K x = η • x → x ∈ Submodule.span ℂ (range f)) ∧
      (K.adjoint x = η • x → x ∈ Submodule.span ℂ (range fun i => star (g i))) := by
  intro K
  have hK : K = ∑ i, rankOne ℂ (f i) (star (g i)) :=
    fredholmKernelToOperator_degenerate f g
  have hA : K.adjoint = ∑ i, rankOne ℂ (star (g i)) (f i) := by
    rw [hK, map_sum]
    simp only [adjoint_rankOne]
  have h (u v : ι → H) (he : (∑ i, rankOne ℂ (u i) (v i)) x = η • x) :
      x ∈ Submodule.span ℂ (range u) := by
    have hm : (∑ i, rankOne ℂ (u i) (v i)) x ∈ Submodule.span ℂ (range u) := by
      simp only [sum_apply, rankOne_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
    rw [he] at hm
    have hh := Submodule.smul_mem (Submodule.span ℂ (range u)) η⁻¹ hm
    rwa [inv_smul_smul₀ hη] at hh
  exact ⟨fun he => h f (fun i => star (g i)) (hK ▸ he),
    fun he => h (fun i => star (g i)) f (hA ▸ he)⟩

end DegenerateKernels

section PolynomialKernels

local notation "μ₁" => fredholmIntervalMeasure (-1) 1
local notation "H₁" => Lp ℂ 2 μ₁
local notation "K₁" => Lp ℂ 2 (Measure.prod μ₁ μ₁)

/-- The constant one vector on the example interval. -/
def fredholmIntervalOne : H₁ := (memLp_const (1 : ℂ)).toLp (fun _ => 1)

/-- The constant vector is represented by the function one. -/
theorem fredholmIntervalOne_ae : fredholmIntervalOne =ᵐ[μ₁] (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp (memLp_const 1)

private theorem memLp_intervalCoordinate : MemLp (fun t : ℝ => (t : ℂ)) 2 μ₁ := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))]
    with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ht

/-- The coordinate vector on the example interval. -/
def fredholmIntervalCoordinate : H₁ :=
  memLp_intervalCoordinate.toLp (fun t : ℝ => (t : ℂ))

/-- The coordinate vector is represented by the identity function. -/
theorem fredholmIntervalCoordinate_ae : fredholmIntervalCoordinate =ᵐ[μ₁] fun t : ℝ => (t : ℂ) :=
  MemLp.coeFn_toLp memLp_intervalCoordinate

private theorem interval_integral_one : ∫ _ : ℝ, (1 : ℂ) ∂μ₁ = 2 := by
  rw [integral_const, Measure.real, fredholmIntervalMeasure, Measure.restrict_apply_univ,
    Real.volume_Icc]
  norm_num

private theorem interval_integral_coordinate : ∫ t : ℝ, (t : ℂ) ∂μ₁ = 0 := by
  calc
    ∫ t : ℝ, (t : ℂ) ∂μ₁ = Complex.ofReal (∫ t : ℝ, t ∂μ₁) :=
      integral_ofReal (f := fun t : ℝ => t)
    _ = 0 := by
      rw [fredholmIntervalMeasure, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_id]
      norm_num

private theorem interval_integral_coordinate_sq : ∫ t : ℝ, (t : ℂ) ^ 2 ∂μ₁ = (2 : ℂ) / 3 := by
  simp_rw [← Complex.ofReal_pow]
  calc
    ∫ t : ℝ, ((t ^ 2 : ℝ) : ℂ) ∂μ₁ = Complex.ofReal (∫ t : ℝ, t ^ 2 ∂μ₁) :=
      integral_ofReal (f := fun t : ℝ => t ^ 2)
    _ = (2 : ℂ) / 3 := by
      rw [fredholmIntervalMeasure, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_pow]
      norm_num

private theorem interval_inner_uu : inner ℂ fredholmIntervalOne fredholmIntervalOne = 2 := by
  rw [L2.inner_def, ← interval_integral_one]
  apply integral_congr_ae
  filter_upwards [fredholmIntervalOne_ae] with t ht
  change fredholmIntervalOne t * conj (fredholmIntervalOne t) = 1
  simp [ht]

private theorem interval_inner_uv : inner ℂ fredholmIntervalOne fredholmIntervalCoordinate = 0 := by
  rw [L2.inner_def, ← interval_integral_coordinate]
  apply integral_congr_ae
  filter_upwards [fredholmIntervalOne_ae, fredholmIntervalCoordinate_ae] with t ht hu
  change fredholmIntervalCoordinate t * conj (fredholmIntervalOne t) = (t : ℂ)
  simp [ht, hu]

private theorem interval_inner_vu : inner ℂ fredholmIntervalCoordinate fredholmIntervalOne = 0 := by
  rw [← inner_conj_symm, interval_inner_uv, map_zero]

private theorem interval_inner_vv :
    inner ℂ fredholmIntervalCoordinate fredholmIntervalCoordinate = (2 : ℂ) / 3 := by
  rw [L2.inner_def, ← interval_integral_coordinate_sq]
  apply integral_congr_ae
  filter_upwards [fredholmIntervalCoordinate_ae] with t ht
  change fredholmIntervalCoordinate t * conj (fredholmIntervalCoordinate t) = (t : ℂ) ^ 2
  rw [ht, Complex.conj_ofReal, pow_two]

/-- The polynomial two-variable kernel (a+b s+c t+d s t) on the example interval. -/
def fredholmPolynomialKernel (a b c d : ℂ) : K₁ :=
  a • rankOneKernelClass fredholmIntervalOne fredholmIntervalOne +
  b • rankOneKernelClass fredholmIntervalCoordinate fredholmIntervalOne +
  c • rankOneKernelClass fredholmIntervalOne fredholmIntervalCoordinate +
  d • rankOneKernelClass fredholmIntervalCoordinate fredholmIntervalCoordinate

private theorem rankOneKernelClass_ae (u v : H₁) :
    rankOneKernelClass u v =ᵐ[Measure.prod μ₁ μ₁] rankOneKernel u v :=
  MemLp.coeFn_toLp (memLp_rankOneKernel u v)

set_option maxHeartbeats 700000 in
-- The product-space L² representatives require several simultaneous almost-everywhere rewrites.
/-- The four separated terms give the stated polynomial almost everywhere. -/
theorem fredholmPolynomialKernel_ae (a b c d : ℂ) :
    fredholmPolynomialKernel a b c d =ᵐ[Measure.prod μ₁ μ₁]
      fun p => a + b * (p.1 : ℂ) + c * (p.2 : ℂ) + d * (p.1 : ℂ) * (p.2 : ℂ) := by
  let u := fredholmIntervalOne
  let v := fredholmIntervalCoordinate
  let A := rankOneKernelClass u u
  let B := rankOneKernelClass v u
  let C := rankOneKernelClass u v
  let D := rankOneKernelClass v v
  change (a • A + b • B + c • C + d • D : K₁) =ᵐ[Measure.prod μ₁ μ₁] _
  filter_upwards [Lp.coeFn_add (a • A + b • B + c • C) (d • D),
    Lp.coeFn_add (a • A + b • B) (c • C), Lp.coeFn_add (a • A) (b • B),
    Lp.coeFn_smul a A, Lp.coeFn_smul b B, Lp.coeFn_smul c C, Lp.coeFn_smul d D,
    rankOneKernelClass_ae u u, rankOneKernelClass_ae v u,
    rankOneKernelClass_ae u v, rankOneKernelClass_ae v v,
    ae_eq_prod_fst fredholmIntervalOne_ae, ae_eq_prod_snd fredholmIntervalOne_ae,
    ae_eq_prod_fst fredholmIntervalCoordinate_ae, ae_eq_prod_snd fredholmIntervalCoordinate_ae]
    with p h₁ h₂ h₃ ha hb hc hd hA hB hC hD hu₁ hu₂ hv₁ hv₂
  rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, Pi.add_apply,
    ha, hb, hc, hd, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    hA, hB, hC, hD]
  simp only [rankOneKernel, smul_eq_mul]
  change (u p.1 = 1) at hu₁
  change (u p.2 = 1) at hu₂
  change (v p.1 = (p.1 : ℂ)) at hv₁
  change (v p.2 = (p.2 : ℂ)) at hv₂
  simp only [hu₁, hu₂, hv₁, hv₂, map_one, mul_one, one_mul, Complex.conj_ofReal]
  ring

private def polynomialOp (a b c d : ℂ) : H₁ →L[ℂ] H₁ :=
  fredholmKernelToOperator (fredholmPolynomialKernel a b c d)

private theorem polynomialOp_apply (a b c d : ℂ) (x : H₁) :
    polynomialOp a b c d x =
      (a * inner ℂ fredholmIntervalOne x + c * inner ℂ fredholmIntervalCoordinate x) •
        fredholmIntervalOne +
      (b * inner ℂ fredholmIntervalOne x + d * inner ℂ fredholmIntervalCoordinate x) •
        fredholmIntervalCoordinate := by
  simp only [polynomialOp, fredholmPolynomialKernel, map_add, map_smul,
    fredholmKernelToOperator_rankOneKernelClass, add_apply, smul_apply, rankOne_apply]
  module

private theorem polynomialOp_mul (a b c d e f g h : ℂ) :
    polynomialOp a b c d * polynomialOp e f g h =
      polynomialOp (2 * a * e + (2 / 3) * c * f) (2 * b * e + (2 / 3) * d * f)
        (2 * a * g + (2 / 3) * c * h) (2 * b * g + (2 / 3) * d * h) := by
  apply ContinuousLinearMap.ext
  intro x
  change polynomialOp a b c d (polynomialOp e f g h x) = _
  simp only [polynomialOp_apply, inner_add_right, inner_smul_right,
    interval_inner_uu, interval_inner_uv, interval_inner_vu, interval_inner_vv,
    mul_zero, zero_add, add_zero]
  module

private theorem polynomialOp_add_smul (a b c d e f g h z : ℂ) :
    polynomialOp a b c d + z • polynomialOp e f g h =
      polynomialOp (a + z * e) (b + z * f) (c + z * g) (d + z * h) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply, smul_apply, polynomialOp_apply]
  module

private theorem inverse_pair_of_resolvent_identities {K R : H₁ →L[ℂ] H₁} (z : ℂ)
    (hL : R = K + z • (K * R)) (hR : R = K + z • (R * K)) :
    (1 - z • K) * (1 + z • R) = 1 ∧ (1 + z • R) * (1 - z • K) = 1 := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change x + z • R x - z • K (x + z • R x) = x
    have h : R x = K x + z • K (R x) := DFunLike.congr_fun hL x
    rw [map_add, map_smul, ← h, add_sub_cancel_right]
  · apply ContinuousLinearMap.ext
    intro x
    change x - z • K x + z • R (x - z • K x) = x
    have h : R x = K x + z • R (K x) := DFunLike.congr_fun hR x
    rw [map_sub, map_smul, show R x - z • R (K x) = K x by rw [h, add_sub_cancel_right],
      sub_add_cancel]

/-- **Exercise 23** of [benIsrael2003generalized], Chapter 9.
For $z \ne 1/2$, the resolvent of $1+3st$ is $(1+3st)/(1-2z)$. -/
theorem exercise_9_23_resolvent (z : ℂ) (hz : 1 - 2 * z ≠ 0) :
    let q := fredholmPolynomialKernel 1 0 0 3
    let r := fredholmPolynomialKernel (1 - 2 * z)⁻¹ 0 0 (3 * (1 - 2 * z)⁻¹)
    IsFredholmResolvent (Lp.memLp q) z (Lp.memLp r) := by
  intro q r
  let h := (1 - 2 * z)⁻¹
  change (1 - z • polynomialOp 1 0 0 3) *
      (1 + z • polynomialOp h 0 0 (3 * h)) = 1 ∧
    (1 + z • polynomialOp h 0 0 (3 * h)) *
      (1 - z • polynomialOp 1 0 0 3) = 1
  apply inverse_pair_of_resolvent_identities
  · rw [polynomialOp_mul, polynomialOp_add_smul]
    congr 1 <;> dsimp [h] <;> field_simp [hz] <;> ring
  · rw [polynomialOp_mul, polynomialOp_add_smul]
    congr 1 <;> dsimp [h] <;> field_simp [hz] <;> ring

private theorem interval_inner_one (y : H₁) : inner ℂ fredholmIntervalOne y = ∫ t, y t ∂μ₁ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fredholmIntervalOne_ae] with t ht
  change y t * conj (fredholmIntervalOne t) = y t
  simp [ht]

private theorem interval_inner_coordinate (y : H₁) :
    inner ℂ fredholmIntervalCoordinate y = ∫ t : ℝ, (t : ℂ) * y t ∂μ₁ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fredholmIntervalCoordinate_ae] with t ht
  change y t * conj (fredholmIntervalCoordinate t) = (t : ℂ) * y t
  simp [ht, mul_comm]

/-- **Exercise 23**, the characteristic case of (44) of
[benIsrael2003generalized], Chapter 9. At parameter (1/2) solvability
requires both moments to vanish. All solutions differ from the right-hand
side by an affine function. -/
theorem exercise_9_23_characteristic (x y : H₁) :
    let q := fredholmPolynomialKernel 1 0 0 3
    fredholmSecondKind (Lp.memLp q) (1 / 2) x = y ↔
      (∫ t, y t ∂μ₁) = 0 ∧ (∫ t : ℝ, (t : ℂ) * y t ∂μ₁) = 0 ∧
      ∃ a b : ℂ, x = y + a • fredholmIntervalOne + b • fredholmIntervalCoordinate := by
  intro q
  let T := fredholmSecondKind (Lp.memLp q) (1 / 2)
  have hT (w : H₁) : T w =
      w - ((1 / 2 : ℂ) * inner ℂ fredholmIntervalOne w) • fredholmIntervalOne -
        ((3 / 2 : ℂ) * inner ℂ fredholmIntervalCoordinate w) • fredholmIntervalCoordinate := by
    change w - (1 / 2 : ℂ) • polynomialOp 1 0 0 3 w = _
    rw [polynomialOp_apply]
    module
  have hu (w : H₁) : inner ℂ fredholmIntervalOne (T w) = 0 := by
    simp only [hT, inner_sub_right, inner_smul_right, interval_inner_uu, interval_inner_uv]
    ring
  have hv (w : H₁) : inner ℂ fredholmIntervalCoordinate (T w) = 0 := by
    simp only [hT, inner_sub_right, inner_smul_right, interval_inner_vu, interval_inner_vv]
    ring
  have hTu : T fredholmIntervalOne = 0 := by
    rw [hT, interval_inner_uu, interval_inner_vu]
    norm_num
  have hTv : T fredholmIntervalCoordinate = 0 := by
    rw [hT, interval_inner_uv, interval_inner_vv]
    norm_num
  change T x = y ↔ _
  rw [← interval_inner_one, ← interval_inner_coordinate]
  constructor
  · rintro rfl
    refine ⟨hu x, hv x, (1 / 2 : ℂ) * inner ℂ fredholmIntervalOne x,
      (3 / 2 : ℂ) * inner ℂ fredholmIntervalCoordinate x, ?_⟩
    rw [hT]
    abel
  · rintro ⟨h₁, h₂, a, b, rfl⟩
    rw [map_add, map_add, map_smul, map_smul, hTu, hTv, smul_zero, smul_zero,
      add_zero, add_zero, hT, h₁, h₂, mul_zero, mul_zero, zero_smul, zero_smul,
      sub_zero, sub_zero]

/-- **Exercise 23** of [benIsrael2003generalized], Chapter 9.
The only characteristic parameter for (1+3st) is (1/2). -/
theorem exercise_9_23_regular_iff (z : ℂ) :
    let q := fredholmPolynomialKernel 1 0 0 3
    IsFredholmRegularValue (Lp.memLp q) z ↔ z ≠ 1 / 2 := by
  intro q
  constructor
  · intro hr hz
    subst z
    have hy : fredholmSecondKind (Lp.memLp q) (1 / 2) fredholmIntervalOne = 0 := by
      apply (exercise_9_23_characteristic fredholmIntervalOne 0).mpr
      refine ⟨?_, ?_, 1, 0, by simp⟩
      · rw [← interval_inner_one, inner_zero_right]
      · rw [← interval_inner_coordinate, inner_zero_right]
    have ho : fredholmIntervalOne ∈ (fredholmSecondKind (Lp.memLp q) (1 / 2)).ker := hy
    change (fredholmSecondKind (Lp.memLp q) (1 / 2)).ker = ⊥ at hr
    rw [hr] at ho
    have hn := interval_inner_uu
    rw [show fredholmIntervalOne = 0 from ho, inner_zero_left] at hn
    norm_num at hn
  · intro hz
    have h₀ : 1 - 2 * z ≠ 0 := by
      intro h
      apply hz
      linear_combination -(1 / 2 : ℂ) * h
    exact isFredholmRegularValue_of_resolvent _ z _ (exercise_9_23_resolvent z h₀)

/-- **Exercise 24** of [benIsrael2003generalized], Chapter 9.
The Hurwitz-modified kernel $1+s-\sqrt{3}t+3st$ has resolvent
$-1+\sqrt{3}s-3t-3st$ at $z=1/2$. -/
theorem exercise_9_24_resolvent :
    let q := fredholmPolynomialKernel 1 1 (-(Real.sqrt 3 : ℂ)) 3
    let r := fredholmPolynomialKernel (-1) (Real.sqrt 3 : ℂ) (-3) (-3)
    IsFredholmResolvent (Lp.memLp q) (1 / 2) (Lp.memLp r) := by
  intro q r
  let h : ℂ := (Real.sqrt 3 : ℝ)
  change (1 - (1 / 2 : ℂ) • polynomialOp 1 1 (-h) 3) *
      (1 + (1 / 2 : ℂ) • polynomialOp (-1) h (-3) (-3)) = 1 ∧
    (1 + (1 / 2 : ℂ) • polynomialOp (-1) h (-3) (-3)) *
      (1 - (1 / 2 : ℂ) • polynomialOp 1 1 (-h) 3) = 1
  have hs : h ^ 2 = 3 := by
    dsimp [h]
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  apply inverse_pair_of_resolvent_identities
  · rw [polynomialOp_mul, polynomialOp_add_smul]
    congr 1
    all_goals ring_nf
    all_goals rw [hs]
    all_goals try ring
  · rw [polynomialOp_mul, polynomialOp_add_smul]
    congr 1
    all_goals ring_nf
    all_goals rw [hs]

/-- **Exercise 24** of [benIsrael2003generalized], Chapter 9.
The polynomial (1+s+3st) has the sole characteristic value (1/2). -/
theorem exercise_9_24_regular_iff (z : ℂ) :
    let q := fredholmPolynomialKernel 1 1 0 3
    IsFredholmRegularValue (Lp.memLp q) z ↔ z ≠ 1 / 2 := by
  intro q
  let T := fredholmSecondKind (Lp.memLp q) z
  change T.ker = ⊥ ↔ _
  have he (x : H₁) : T x = x -
      z • (inner ℂ fredholmIntervalOne x • fredholmIntervalOne +
        (inner ℂ fredholmIntervalOne x + 3 * inner ℂ fredholmIntervalCoordinate x) •
          fredholmIntervalCoordinate) := by
    change x - z • polynomialOp 1 1 0 3 x = _
    simp only [polynomialOp_apply, one_mul, zero_mul, add_zero]
  constructor
  · intro h hz
    have hTv : T fredholmIntervalCoordinate = 0 := by
      rw [he, hz, interval_inner_uv, interval_inner_vv]
      norm_num [smul_smul]
    have hzv : fredholmIntervalCoordinate = 0 := by
      have hm : fredholmIntervalCoordinate ∈ T.ker := hTv
      rw [h] at hm
      exact hm
    have hn := interval_inner_vv
    rw [hzv, inner_zero_left] at hn
    norm_num at hn
  · intro hz
    rw [Submodule.eq_bot_iff]
    intro x hx
    change T x = 0 at hx
    have hz' : 1 - 2 * z ≠ 0 := by
      intro h
      apply hz
      linear_combination -(1 / 2 : ℂ) * h
    have hu := congrArg (inner ℂ fredholmIntervalOne) hx
    have hv := congrArg (inner ℂ fredholmIntervalCoordinate) hx
    simp only [he, inner_sub_right, inner_smul_right, inner_add_right, inner_zero_right,
      interval_inner_uu, interval_inner_uv, interval_inner_vu, interval_inner_vv,
      mul_zero, zero_add, add_zero] at hu hv
    have hu' : (1 - 2 * z) * inner ℂ fredholmIntervalOne x = 0 := by
      linear_combination hu
    have hu₀ := (mul_eq_zero.mp hu').resolve_left hz'
    rw [hu₀, zero_add] at hv
    have hv' : (1 - 2 * z) * inner ℂ fredholmIntervalCoordinate x = 0 := by
      linear_combination hv
    have hv₀ := (mul_eq_zero.mp hv').resolve_left hz'
    simpa only [he, hu₀, hv₀, mul_zero, add_zero, zero_smul, smul_zero, sub_zero] using hx

/-- At the characteristic value, the two null spaces for (1+s+3st)
are the spans of the coordinate and constant vectors respectively. -/
theorem exercise_9_24_nullSpaces :
    let q := fredholmPolynomialKernel 1 1 0 3
    let T := fredholmSecondKind (Lp.memLp q) (1 / 2)
    T.ker = ℂ ∙ fredholmIntervalCoordinate ∧ T.adjoint.ker = ℂ ∙ fredholmIntervalOne := by
  intro q T
  have hT : T = 1 - (1 / 2 : ℂ) • polynomialOp 1 1 0 3 := rfl
  have hP : (polynomialOp 1 1 0 3).adjoint = polynomialOp 1 0 1 3 := by
    simp [polynomialOp, fredholmPolynomialKernel, map_smulₛₗ, map_ofNat,
      fredholmKernelToOperator_rankOneKernelClass]
  have hA : T.adjoint = 1 - (1 / 2 : ℂ) • polynomialOp 1 0 1 3 := by
    have hId : (1 : H₁ →L[ℂ] H₁).adjoint = 1 := by
      simpa [ContinuousLinearMap.one_def] using (ContinuousLinearMap.adjoint_id (𝕜 := ℂ) (E := H₁))
    rw [hT, map_sub, map_smulₛₗ, hId, hP]
    simp only [map_div₀, map_one, map_ofNat]
  constructor
  · ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    change T x = 0 ↔ _
    constructor
    · intro hx
      have he : x = (1 / 2 : ℂ) • polynomialOp 1 1 0 3 x := by
        rw [hT] at hx
        change x - (1 / 2 : ℂ) • polynomialOp 1 1 0 3 x = 0 at hx
        exact sub_eq_zero.mp hx
      have h := congrArg (inner ℂ fredholmIntervalCoordinate) he
      simp only [polynomialOp_apply, inner_smul_right, inner_add_right,
        interval_inner_vu, interval_inner_vv, one_mul, zero_mul, zero_add, add_zero, mul_zero] at h
      have hU : inner ℂ fredholmIntervalOne x = 0 := by linear_combination -3 * h
      refine ⟨(3 / 2 : ℂ) * inner ℂ fredholmIntervalCoordinate x, ?_⟩
      calc
        _ = (1 / 2 : ℂ) • polynomialOp 1 1 0 3 x := by
          rw [polynomialOp_apply, hU]
          module
        _ = x := he.symm
    · rintro ⟨b, rfl⟩
      rw [map_smul, hT]
      change b • (fredholmIntervalCoordinate -
        (1 / 2 : ℂ) • polynomialOp 1 1 0 3 fredholmIntervalCoordinate) = 0
      rw [polynomialOp_apply, interval_inner_uv, interval_inner_vv]
      norm_num [smul_smul]
  · ext x
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    change T.adjoint x = 0 ↔ _
    constructor
    · intro hx
      have he : x = (1 / 2 : ℂ) • polynomialOp 1 0 1 3 x := by
        rw [hA] at hx
        change x - (1 / 2 : ℂ) • polynomialOp 1 0 1 3 x = 0 at hx
        exact sub_eq_zero.mp hx
      have h := congrArg (inner ℂ fredholmIntervalOne) he
      simp only [polynomialOp_apply, inner_smul_right, inner_add_right,
        interval_inner_uu, interval_inner_uv, one_mul, zero_mul, zero_add, add_zero, mul_zero] at h
      have hV : inner ℂ fredholmIntervalCoordinate x = 0 := by linear_combination -h
      refine ⟨(1 / 2 : ℂ) * inner ℂ fredholmIntervalOne x, ?_⟩
      calc
        _ = (1 / 2 : ℂ) • polynomialOp 1 0 1 3 x := by
          rw [polynomialOp_apply, hV]
          module
        _ = x := he.symm
    · rintro ⟨b, rfl⟩
      rw [map_smul, hA]
      change b • (fredholmIntervalOne - (1 / 2 : ℂ) • polynomialOp 1 0 1 3 fredholmIntervalOne) = 0
      rw [polynomialOp_apply, interval_inner_vu, interval_inner_uu]
      norm_num [smul_smul]

end PolynomialKernels

end BenIsraelGreville.Chapter09
