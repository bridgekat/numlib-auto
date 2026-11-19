/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-vector Sobolev spaces on an interval

A vector Sobolev function has one scalar Sobolev coordinate for each vector
coordinate. Its values and weak derivatives belong to the Hilbert sum of
scalar $L^2(a,b)$ spaces. This file transports the trace and integration
by parts identities to finite vector functions and matrix coefficients.
-/

noncomputable section

open MeasureTheory Set Filter Matrix
open scoped ENNReal Topology InnerProductSpace

/-- The real Hilbert space of square-integrable functions on an interval, with
finitely many coordinates. -/
abbrev IntervalVectorL2 (ι : Type*) [Fintype ι] (a b : ℝ) :=
  PiLp 2 (fun _ : ι => Lp ℝ 2 (volume.restrict (Ioo a b)))

/-- First Sobolev functions on an interval with finitely many real coordinates. -/
abbrev IntervalVectorSobolev (ι : Type*) [Fintype ι] (a b : ℝ) :=
  ι → SobolevInterval 1 a b

section Coordinates

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The value or first derivative of a vector Sobolev function as a vector in $L^2$. -/
def intervalVectorSobolevDeriv (u : IntervalVectorSobolev ι a b) (j : Fin 2) : IntervalVectorL2 ι a b :=
  WithLp.toLp 2 (fun i => SobolevInterval.deriv (u i) j)

/-- Differentiation from the vector Sobolev space to the vector $L^2$ space is continuous linear. -/
def intervalVectorSobolevDerivCLM (j : Fin 2) : IntervalVectorSobolev ι a b →L[ℝ] IntervalVectorL2 ι a b :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (SobolevInterval.derivL 1 a b j).comp (ContinuousLinearMap.proj i))

/-- Evaluation of the continuous linear derivative map. -/
@[simp] theorem intervalVectorSobolevDerivCLM_apply (j : Fin 2) (u : IntervalVectorSobolev ι a b) :
    intervalVectorSobolevDerivCLM j u = intervalVectorSobolevDeriv u j := rfl

/-- The vector of continuous representatives of the Sobolev coordinates. -/
def intervalVectorSobolevRep (u : IntervalVectorSobolev ι a b) (t : ℝ) : ι → ℝ :=
  fun i => SobolevInterval.rep (u i) t

/-- The pointwise values of the scalar $L^2$ representatives. -/
def intervalVectorL2Rep (u : IntervalVectorL2 ι a b) (t : ℝ) : ι → ℝ := fun i => u i t

/-- The vector Sobolev representative is continuous up to the endpoints. -/
theorem continuousOn_intervalVectorSobolevRep (hab : a ≤ b) (u : IntervalVectorSobolev ι a b) :
    ContinuousOn (intervalVectorSobolevRep u) (Icc a b) :=
  continuousOn_pi.mpr fun i => SobolevInterval.continuousOn_rep hab (u i)

/-- The vector $L^2$ value agrees almost everywhere with the vector Sobolev representative. -/
theorem intervalVectorSobolevDeriv_zero_ae_eq_rep (u : IntervalVectorSobolev ι a b) :
    intervalVectorL2Rep (intervalVectorSobolevDeriv u 0) =ᵐ[volume.restrict (Ioo a b)]
      intervalVectorSobolevRep u := by
  have h : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ i,
      SobolevInterval.deriv (u i) 0 t = SobolevInterval.rep (u i) t :=
    eventually_all.mpr (fun i => SobolevInterval.fn_ae_eq_rep (u i))
  exact h.mono fun _ h => funext h

/-- Point evaluation of a vector Sobolev function on the closed interval. -/
def intervalVectorSobolevTraceCLM (hab : a < b) (t : Icc a b) :
    IntervalVectorSobolev ι a b →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => (SobolevInterval.evalCLM hab t).comp (ContinuousLinearMap.proj i)

/-- Evaluation of a Sobolev trace is the value of its continuous representative. -/
@[simp] theorem intervalVectorSobolevTraceCLM_apply (hab : a < b) (t : Icc a b)
    (u : IntervalVectorSobolev ι a b) :
    intervalVectorSobolevTraceCLM hab t u = intervalVectorSobolevRep u t := by
  funext i
  exact SobolevInterval.evalCLM_apply hab t (u i)

private theorem intervalScalarSobolev_inner_add (hab : a < b) (u v : SobolevInterval 1 a b) :
    ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 0⟫_ℝ +
      ⟪SobolevInterval.deriv u 0, SobolevInterval.deriv v 1⟫_ℝ =
    SobolevInterval.rep u b * SobolevInterval.rep v b -
      SobolevInterval.rep u a * SobolevInterval.rep v a := by
  have h := SobolevInterval.integral_deriv_mul_add_mul_deriv hab u v
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at h
  have h₁ : Integrable (fun t => SobolevInterval.deriv u 1 t * SobolevInterval.deriv v 0 t)
      (volume.restrict (Ioo a b)) := by
    simpa only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using
      L2.integrable_inner (𝕜 := ℝ) (SobolevInterval.deriv u 1) (SobolevInterval.deriv v 0)
  have h₂ : Integrable (fun t => SobolevInterval.deriv u 0 t * SobolevInterval.deriv v 1 t)
      (volume.restrict (Ioo a b)) := by
    simpa only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using
      L2.integrable_inner (𝕜 := ℝ) (SobolevInterval.deriv u 0) (SobolevInterval.deriv v 1)
  rw [L2.inner_eq_integral_mul, L2.inner_eq_integral_mul, ← integral_add h₁ h₂, ← h]
  refine integral_congr_ae ?_
  filter_upwards [SobolevInterval.fn_ae_eq_rep u, SobolevInterval.fn_ae_eq_rep v] with t hu hv
  change SobolevInterval.deriv u 0 t = _ at hu
  change SobolevInterval.deriv v 0 t = _ at hv
  rw [hu, hv]

/-- Integration by parts for vector Sobolev functions, with the Hilbert-space
inner products on the left and the endpoint dot products on the right. -/
theorem intervalVectorSobolev_inner_deriv_add (hab : a < b) (u v : IntervalVectorSobolev ι a b) :
    ⟪intervalVectorSobolevDeriv u 1, intervalVectorSobolevDeriv v 0⟫_ℝ +
      ⟪intervalVectorSobolevDeriv u 0, intervalVectorSobolevDeriv v 1⟫_ℝ =
    intervalVectorSobolevRep u b ⬝ᵥ intervalVectorSobolevRep v b -
      intervalVectorSobolevRep u a ⬝ᵥ intervalVectorSobolevRep v a := by
  simp only [PiLp.inner_apply, intervalVectorSobolevDeriv, dotProduct,
    intervalVectorSobolevRep, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => intervalScalarSobolev_inner_add hab (u i) (v i)

end Coordinates

section Coefficients

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℝ}

private theorem continuousCoefficient_bound {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂volume.restrict (Ioo a b), ‖g t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
  exact (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _)

private theorem continuousCoefficient_measurable {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    AEStronglyMeasurable g (volume.restrict (Ioo a b)) :=
  hg.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self

private theorem continuousCoefficient_memLp {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g 2 (volume.restrict (Ioo a b)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, _, hC⟩ := continuousCoefficient_bound hg
  exact MemLp.of_bound (continuousCoefficient_measurable hg) C hC

private theorem deriv_contDiffCoefficient_memLp {g : ℝ → ℝ} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) :
    MemLp (deriv g) 2 (volume.restrict (Ioo a b)) := by
  have h : derivWithin g (Icc a b) =ᵐ[volume.restrict (Ioo a b)] deriv g := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  exact (memLp_congr_ae h).mp
    (continuousCoefficient_memLp (hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl))

/-- A continuously differentiable scalar function on the closed interval, regarded as a
Sobolev function on the open interval. -/
def intervalSobolevOfContDiffOn {g : ℝ → ℝ} (hab : a < b) (hg : ContDiffOn ℝ 1 g (Icc a b)) :
    SobolevInterval 1 a b :=
  SobolevIntervalLp.ofContDiffOn (hg.mono Ioo_subset_Icc_self)
    (continuousCoefficient_memLp hg.continuousOn) (deriv_contDiffCoefficient_memLp hab hg)

/-- The Sobolev representative of a continuously differentiable function agrees with it on
the closed interval. -/
theorem intervalSobolevOfContDiffOn_rep {g : ℝ → ℝ} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) :
    EqOn (SobolevInterval.rep (intervalSobolevOfContDiffOn hab hg)) g (Icc a b) := by
  rw [← SobolevIntervalLp.closure_coe_Ioo hab]
  exact SobolevIntervalLp.rep_ofContDiffOn (SobolevIntervalLp.ordConnected_coe_Ioo a b)
    _ _ _ (by rw [SobolevIntervalLp.closure_coe_Ioo hab]; exact hg.continuousOn)

/-- The weak derivative of a continuously differentiable function equals its classical
derivative almost everywhere. -/
theorem intervalSobolevOfContDiffOn_deriv_ae {g : ℝ → ℝ} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) :
    ⇑(SobolevInterval.deriv (intervalSobolevOfContDiffOn hab hg) 1) =ᵐ[volume.restrict (Ioo a b)]
      deriv g :=
  SobolevIntervalLp.coeFn_deriv_ofContDiffOn_one _ _ _

/-- A matrix with continuously differentiable entries acts on vector Sobolev functions by
pointwise matrix-vector multiplication. -/
def intervalVectorMatrixSobolevMul (A : ℝ → Matrix κ ι ℝ) (hab : a < b)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun t => A t i j) (Icc a b))
    (u : IntervalVectorSobolev ι a b) : IntervalVectorSobolev κ a b :=
  fun i => ∑ j, SobolevIntervalLp.mul (SobolevIntervalLp.ordConnected_coe_Ioo a b)
    (intervalSobolevOfContDiffOn hab (hA i j)) (u j)

/-- Multiplication by a continuously differentiable matrix agrees pointwise with the action
on continuous Sobolev representatives, including at the endpoints. -/
theorem intervalVectorMatrixSobolevMul_rep (A : ℝ → Matrix κ ι ℝ) (hab : a < b)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun t => A t i j) (Icc a b))
    (u : IntervalVectorSobolev ι a b) {t : ℝ} (ht : t ∈ Icc a b) :
    intervalVectorSobolevRep (intervalVectorMatrixSobolevMul A hab hA u) t =
      (A t).mulVec (intervalVectorSobolevRep u t) := by
  funext i
  simp only [intervalVectorSobolevRep, intervalVectorMatrixSobolevMul, Matrix.mulVec, dotProduct]
  rw [show SobolevInterval.rep (∑ j, SobolevIntervalLp.mul
      (SobolevIntervalLp.ordConnected_coe_Ioo a b)
      (intervalSobolevOfContDiffOn hab (hA i j)) (u j)) t =
      ∑ j, SobolevInterval.rep (SobolevIntervalLp.mul
        (SobolevIntervalLp.ordConnected_coe_Ioo a b)
        (intervalSobolevOfContDiffOn hab (hA i j)) (u j)) t by
      simpa only [one_smul, one_mul] using
        SobolevInterval.rep_finset_sum hab Finset.univ (fun _ : ι => (1 : ℝ))
          (fun j => SobolevIntervalLp.mul (SobolevIntervalLp.ordConnected_coe_Ioo a b)
            (intervalSobolevOfContDiffOn hab (hA i j)) (u j)) ht]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (SobolevIntervalLp.rep_mul (SobolevIntervalLp.ordConnected_coe_Ioo a b) _ _
    (by rwa [SobolevIntervalLp.closure_coe_Ioo hab])).trans
      (congrArg (· * SobolevInterval.rep (u j) t) (intervalSobolevOfContDiffOn_rep hab (hA i j) ht))

/-- The weak derivative of a matrix times a vector Sobolev function satisfies the
product rule almost everywhere on the interval. -/
theorem intervalVectorMatrixSobolevMul_deriv_ae (A : ℝ → Matrix κ ι ℝ) (hab : a < b)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun t => A t i j) (Icc a b))
    (u : IntervalVectorSobolev ι a b) :
    intervalVectorL2Rep (intervalVectorSobolevDeriv (intervalVectorMatrixSobolevMul A hab hA u) 1)
      =ᵐ[volume.restrict (Ioo a b)]
    fun t => (A t).mulVec (intervalVectorL2Rep (intervalVectorSobolevDeriv u 1) t) +
      Matrix.mulVec (fun i j => deriv (fun s => A s i j) t) (intervalVectorSobolevRep u t) := by
  let μ := volume.restrict (Ioo a b)
  have h : ∀ i : κ, ∀ᵐ t ∂μ,
      SobolevInterval.deriv (intervalVectorMatrixSobolevMul A hab hA u i) 1 t =
      ∑ j, A t i j * SobolevInterval.deriv (u j) 1 t +
        ∑ j, deriv (fun s => A s i j) t * SobolevInterval.rep (u j) t := by
    intro i
    let w := fun j => SobolevIntervalLp.mul (SobolevIntervalLp.ordConnected_coe_Ioo a b)
      (intervalSobolevOfContDiffOn hab (hA i j)) (u j)
    change ∀ᵐ t ∂μ, (SobolevInterval.derivL 1 a b 1 (∑ j, w j)) t = _
    rw [map_sum]
    have hp : ∀ j, ∀ᵐ t ∂μ, SobolevInterval.deriv (w j) 1 t =
        A t i j * SobolevInterval.deriv (u j) 1 t +
          deriv (fun s => A s i j) t * SobolevInterval.rep (u j) t := by
      intro j
      filter_upwards [SobolevIntervalLp.coeFn_deriv_mul
        (SobolevIntervalLp.ordConnected_coe_Ioo a b)
        (intervalSobolevOfContDiffOn hab (hA i j)) (u j),
        intervalSobolevOfContDiffOn_deriv_ae hab (hA i j),
        ae_restrict_mem (μ := volume) measurableSet_Ioo] with t hmul hderiv ht
      change SobolevInterval.deriv (w j) 1 t =
        SobolevInterval.deriv (intervalSobolevOfContDiffOn hab (hA i j)) 1 t *
          SobolevInterval.rep (u j) t +
        SobolevInterval.rep (intervalSobolevOfContDiffOn hab (hA i j)) t *
          SobolevInterval.deriv (u j) 1 t at hmul
      rw [hmul, hderiv, intervalSobolevOfContDiffOn_rep hab (hA i j) (Ioo_subset_Icc_self ht)]
      exact add_comm _ _
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => SobolevInterval.deriv (w j) 1),
      eventually_all.mpr hp] with t hsum hproducts
    change (∑ j, SobolevInterval.deriv (w j) 1) t = _
    rw [hsum, Finset.sum_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hproducts j
  exact (eventually_all.mpr h).mono fun _ ht => funext ht

/-- Every pair of endpoint vectors is the trace of a vector Sobolev function. -/
theorem exists_intervalVectorSobolev_endpoint_values (hab : a < b) (x y : ι → ℝ) :
    ∃ u : IntervalVectorSobolev ι a b, intervalVectorSobolevRep u a = x ∧
      intervalVectorSobolevRep u b = y := by
  let g (i : ι) (t : ℝ) := x i + ((t - a) / (b - a)) * (y i - x i)
  have hg (i : ι) : ContDiff ℝ 1 (g i) :=
    contDiff_const.add (((contDiff_id.sub contDiff_const).div_const _).mul contDiff_const)
  refine ⟨fun i => intervalSobolevOfContDiffOn hab (hg i).contDiffOn, ?_, ?_⟩
  · funext i
    change SobolevInterval.rep (intervalSobolevOfContDiffOn hab (hg i).contDiffOn) a = x i
    rw [intervalSobolevOfContDiffOn_rep hab (hg i).contDiffOn (left_mem_Icc.2 hab.le)]
    simp [g]
  · funext i
    change SobolevInterval.rep (intervalSobolevOfContDiffOn hab (hg i).contDiffOn) b = y i
    rw [intervalSobolevOfContDiffOn_rep hab (hg i).contDiffOn (right_mem_Icc.2 hab.le)]
    simp [g, sub_ne_zero.mpr hab.ne']

end Coefficients

section MatrixL2

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a b : ℝ}

private abbrev ScalarL2 (a b : ℝ) := Lp ℝ 2 (volume.restrict (Ioo a b))

private theorem continuousCoefficient_mul_memLp {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (u : ScalarL2 a b) :
    MemLp (fun t => g t * u t) 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, _, hC⟩ := continuousCoefficient_bound hg
  exact MemLp.fun_mul (memLp_top_of_bound (continuousCoefficient_measurable hg) C hC)
    (Lp.memLp u)

private def scalarL2Mulₗ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    ScalarL2 a b →ₗ[ℝ] ScalarL2 a b where
  toFun u := (continuousCoefficient_mul_memLp hg u).toLp (fun t => g t * u t)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(continuousCoefficient_mul_memLp hg (u + v)).coeFn_toLp,
      (continuousCoefficient_mul_memLp hg u).coeFn_toLp,
      (continuousCoefficient_mul_memLp hg v).coeFn_toLp, Lp.coeFn_add u v,
      Lp.coeFn_add ((continuousCoefficient_mul_memLp hg u).toLp (fun t => g t * u t))
        ((continuousCoefficient_mul_memLp hg v).toLp (fun t => g t * v t))]
      with t huv hu hv hadd hout
    rw [huv, hadd, hout, Pi.add_apply, Pi.add_apply, hu, hv, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(continuousCoefficient_mul_memLp hg (c • u)).coeFn_toLp,
      (continuousCoefficient_mul_memLp hg u).coeFn_toLp, Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((continuousCoefficient_mul_memLp hg u).toLp (fun t => g t * u t))]
      with t hcu hu hsmul hout
    change _ = (c • (continuousCoefficient_mul_memLp hg u).toLp (fun t => g t * u t)) t
    rw [hcu, hsmul, hout, Pi.smul_apply, Pi.smul_apply, hu]
    simp only [smul_eq_mul]
    ring

private theorem scalarL2Mul_bound (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    ∃ C : ℝ, ∀ u : ScalarL2 a b, ‖scalarL2Mulₗ g hg u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hgC⟩ := continuousCoefficient_bound hg
  refine ⟨C, fun u => ?_⟩
  change ‖(continuousCoefficient_mul_memLp hg u).toLp (fun t => g t * u t)‖ ≤ C * ‖u‖
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (continuousCoefficient_mul_memLp hg u).aestronglyMeasurable
    (g := fun t => u t) (c := C)
    (hgC.mono fun t ht => by rw [norm_mul]; gcongr) (2 : ℝ≥0∞)
  calc
    _ ≤ (ENNReal.ofReal C * eLpNorm u 2 (volume.restrict (Ioo a b))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).eLpNorm_ne_top) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

private def scalarL2MulCLM (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    ScalarL2 a b →L[ℝ] ScalarL2 a b :=
  (scalarL2Mulₗ g hg).mkContinuousOfExistsBound (scalarL2Mul_bound g hg)

private theorem scalarL2MulCLM_ae (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b))
    (u : ScalarL2 a b) :
    ⇑(scalarL2MulCLM g hg u) =ᵐ[volume.restrict (Ioo a b)] fun t => g t * u t :=
  (continuousCoefficient_mul_memLp hg u).coeFn_toLp

private def intervalVectorL2Proj (i : ι) : IntervalVectorL2 ι a b →L[ℝ] ScalarL2 a b :=
  (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap

/-- A continuous matrix on the closed interval gives a bounded linear multiplication
operator between the corresponding vector $L^2$ spaces. -/
def intervalVectorMatrixL2Mul (A : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b)) :
    IntervalVectorL2 ι a b →L[ℝ] IntervalVectorL2 κ a b :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j,
      (scalarL2MulCLM (fun t => A t i j) (hA i j)).comp (intervalVectorL2Proj j))

private theorem intervalVectorMatrixL2Mul_apply_coord (A : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b))
    (u : IntervalVectorL2 ι a b) (i : κ) :
    intervalVectorMatrixL2Mul A hA u i =
      ∑ j, scalarL2MulCLM (fun t => A t i j) (hA i j) (u j) := by
  change (∑ j, (scalarL2MulCLM (fun t => A t i j) (hA i j)).comp (intervalVectorL2Proj j)) u = _
  rw [sum_apply]
  rfl

/-- Multiplication by a continuous matrix on vector $L^2$ acts almost everywhere
by pointwise matrix-vector multiplication. -/
theorem intervalVectorMatrixL2Mul_ae (A : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b))
    (u : IntervalVectorL2 ι a b) :
    intervalVectorL2Rep (intervalVectorMatrixL2Mul A hA u) =ᵐ[volume.restrict (Ioo a b)]
      fun t => (A t).mulVec (intervalVectorL2Rep u t) := by
  have h (i : κ) : ∀ᵐ t ∂volume.restrict (Ioo a b),
      intervalVectorMatrixL2Mul A hA u i t = ∑ j, A t i j * u j t := by
    let F := fun j => scalarL2MulCLM (fun t => A t i j) (hA i j) (u j)
    have hF : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ j, F j t = A t i j * u j t :=
      eventually_all.mpr (fun j => scalarL2MulCLM_ae _ _ _)
    filter_upwards [Lp.coeFn_finsetSum Finset.univ F, hF] with t hsum hterms
    rw [intervalVectorMatrixL2Mul_apply_coord]
    change (∑ j, F j) t = _
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hterms j
  exact (eventually_all.mpr h).mono fun _ ht => funext ht

private theorem scalarL2MulCLM_inner (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b))
    (u v : ScalarL2 a b) :
    ⟪scalarL2MulCLM g hg u, v⟫_ℝ = ⟪u, scalarL2MulCLM g hg v⟫_ℝ := by
  rw [L2.inner_eq_integral_mul, L2.inner_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [scalarL2MulCLM_ae g hg u, scalarL2MulCLM_ae g hg v] with t hu hv
  rw [hu, hv]
  ring

/-- The Hilbert adjoint of multiplication by a continuous real matrix is multiplication
by the pointwise transpose. -/
theorem intervalVectorMatrixL2Mul_transpose_inner (A : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b))
    (u : IntervalVectorL2 ι a b) (v : IntervalVectorL2 κ a b) :
    ⟪intervalVectorMatrixL2Mul A hA u, v⟫_ℝ =
      ⟪u, intervalVectorMatrixL2Mul (fun t => (A t)ᵀ) (fun i j => hA j i) v⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ i, ⟪intervalVectorMatrixL2Mul A hA u i, v i⟫_ℝ) =
    ∑ j, ⟪u j, intervalVectorMatrixL2Mul (fun t => (A t)ᵀ) (fun i j => hA j i) v j⟫_ℝ
  calc
    _ = ∑ i : κ, ∑ j : ι, ⟪u j, scalarL2MulCLM (fun t => A t i j) (hA i j) (v i)⟫_ℝ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalVectorMatrixL2Mul_apply_coord, sum_inner]
      exact Finset.sum_congr rfl fun j _ => scalarL2MulCLM_inner _ _ _ _
    _ = ∑ j : ι, ∑ i : κ, ⟪u j, scalarL2MulCLM (fun t => A t i j) (hA i j) (v i)⟫_ℝ :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := intervalVectorMatrixL2Mul_apply_coord (fun t => (A t)ᵀ)
        (fun i k => hA k i) v j
      calc
        _ = ⟪u j, ∑ i, scalarL2MulCLM (fun t => A t i j) (hA i j) (v i)⟫_ℝ :=
          (inner_sum _ _ _).symm
        _ = _ := (congrArg (fun w : ScalarL2 a b => ⟪u j, w⟫_ℝ) hj).symm

/-- The $L^2$ value of the Sobolev product agrees with the action of the corresponding
bounded multiplication operator. -/
theorem intervalVectorMatrixSobolevMul_deriv_zero (A : ℝ → Matrix κ ι ℝ) (hab : a < b)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun t => A t i j) (Icc a b))
    (u : IntervalVectorSobolev ι a b) :
    intervalVectorSobolevDeriv (intervalVectorMatrixSobolevMul A hab hA u) 0 =
      intervalVectorMatrixL2Mul A (fun i j => (hA i j).continuousOn) (intervalVectorSobolevDeriv u 0) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [intervalVectorSobolevDeriv_zero_ae_eq_rep (intervalVectorMatrixSobolevMul A hab hA u),
    intervalVectorSobolevDeriv_zero_ae_eq_rep u,
    intervalVectorMatrixL2Mul_ae A (fun i j => (hA i j).continuousOn) (intervalVectorSobolevDeriv u 0),
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with t hproduct hu hmul ht
  exact congrFun (hproduct.trans ((intervalVectorMatrixSobolevMul_rep A hab hA u
    (Ioo_subset_Icc_self ht)).trans (hu ▸ hmul.symm))) i

end MatrixL2

section WeakDerivative

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- A vector Sobolev function is determined by its value in vector $L^2$. -/
theorem intervalVectorSobolevDeriv_zero_injective :
    Function.Injective (fun u : IntervalVectorSobolev ι a b => intervalVectorSobolevDeriv u 0) := by
  intro u v h
  funext i
  apply SobolevMultiIndex.fnL_injective
  exact congrArg (fun w : IntervalVectorL2 ι a b => w i) h

/-- Two vectors in interval $L^2$ coincide when their representatives agree almost everywhere. -/
theorem intervalVectorL2_ext {u v : IntervalVectorL2 ι a b}
    (h : intervalVectorL2Rep u =ᵐ[volume.restrict (Ioo a b)] intervalVectorL2Rep v) : u = v := by
  apply PiLp.ext
  intro i
  exact Lp.ext (h.mono fun _ ht => congrFun ht i)

/-- Two vectors in interval $L^2$ give a Sobolev function and its derivative exactly when the
second vector is a weak derivative of the first in every coordinate. -/
theorem exists_intervalVectorSobolev_iff (u v : IntervalVectorL2 ι a b) :
    (∃ z : IntervalVectorSobolev ι a b, intervalVectorSobolevDeriv z 0 = u ∧
      intervalVectorSobolevDeriv z 1 = v) ↔
    ∀ i, HasWeakDerivOn (u i) (v i) (TopologicalSpace.Opens.Ioo a b) := by
  constructor
  · rintro ⟨z, rfl, rfl⟩ i
    exact SobolevIntervalLp.hasWeakDerivOn_fn (z i)
  · intro h
    let w (i : ι) : Fin 2 → ScalarL2 a b := ![u i, v i]
    have hw (i : ι) (j : Fin 2) :
        HasWeakIteratedDerivOn (j : ℕ) (w i 0) (w i j) (TopologicalSpace.Opens.Ioo a b) := by
      fin_cases j
      · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
          ((Lp.memLp (u i)).locallyIntegrableOn (Ω := TopologicalSpace.Opens.Ioo a b) (by norm_num))
      · exact h i
    exact ⟨fun i => SobolevInterval.mk (w i) (hw i),
      PiLp.ext fun _ => rfl, PiLp.ext fun _ => rfl⟩

/-- The first-order Green identity for a real matrix differential expression
$A_1 u' + A_0 u$, with the weak derivative of $A_1^T v$ in the formal adjoint
and the weighted endpoint pairing. -/
theorem intervalVectorMatrix_green (hab : a < b) (A₁ A₀ : ℝ → Matrix ι ι ℝ)
    (hA₁ : ∀ i j, ContDiffOn ℝ 1 (fun t => A₁ t i j) (Icc a b))
    (hA₀ : ∀ i j, ContinuousOn (fun t => A₀ t i j) (Icc a b))
    (u v : IntervalVectorSobolev ι a b) :
    ⟪intervalVectorMatrixL2Mul A₁ (fun i j => (hA₁ i j).continuousOn) (intervalVectorSobolevDeriv u 1) +
      intervalVectorMatrixL2Mul A₀ hA₀ (intervalVectorSobolevDeriv u 0), intervalVectorSobolevDeriv v 0⟫_ℝ -
    ⟪intervalVectorSobolevDeriv u 0,
      -(intervalVectorSobolevDeriv
        (intervalVectorMatrixSobolevMul (fun t => (A₁ t)ᵀ) hab (fun i j => hA₁ j i) v) 1) +
      intervalVectorMatrixL2Mul (fun t => (A₀ t)ᵀ) (fun i j => hA₀ j i) (intervalVectorSobolevDeriv v 0)⟫_ℝ =
    intervalVectorSobolevRep u b ⬝ᵥ (A₁ b)ᵀ.mulVec (intervalVectorSobolevRep v b) -
    intervalVectorSobolevRep u a ⬝ᵥ (A₁ a)ᵀ.mulVec (intervalVectorSobolevRep v a) := by
  let w := intervalVectorMatrixSobolevMul (fun t => (A₁ t)ᵀ) hab (fun i j => hA₁ j i) v
  have hw : intervalVectorSobolevDeriv w 0 =
      intervalVectorMatrixL2Mul (fun t => (A₁ t)ᵀ) (fun i j => (hA₁ j i).continuousOn)
        (intervalVectorSobolevDeriv v 0) :=
    intervalVectorMatrixSobolevMul_deriv_zero (fun t => (A₁ t)ᵀ) hab (fun i j => hA₁ j i) v
  rw [inner_add_left, inner_add_right, inner_neg_right,
    intervalVectorMatrixL2Mul_transpose_inner, intervalVectorMatrixL2Mul_transpose_inner, ← hw]
  have h := intervalVectorSobolev_inner_deriv_add hab u w
  have hb : intervalVectorSobolevRep w b = (A₁ b)ᵀ.mulVec (intervalVectorSobolevRep v b) :=
    intervalVectorMatrixSobolevMul_rep _ hab (fun i j => hA₁ j i) v (right_mem_Icc.2 hab.le)
  have ha : intervalVectorSobolevRep w a = (A₁ a)ᵀ.mulVec (intervalVectorSobolevRep v a) :=
    intervalVectorMatrixSobolevMul_rep _ hab (fun i j => hA₁ j i) v (left_mem_Icc.2 hab.le)
  rw [hb, ha] at h
  change _ - (-⟪intervalVectorSobolevDeriv u 0, intervalVectorSobolevDeriv w 1⟫_ℝ + _) = _
  linarith

end WeakDerivative

section IntervalMatrixActions

variable {κ ι η : Type*} [Fintype κ] [Fintype ι] [Fintype η] {a b : ℝ}

/-- Multiplication by continuous matrix coefficients respects matrix products. -/
theorem intervalVectorMatrixL2Mul_comp
    (A : ℝ → Matrix κ ι ℝ) (B : ℝ → Matrix ι η ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b))
    (hB : ∀ i j, ContinuousOn (fun t => B t i j) (Icc a b))
    (hAB : ∀ i j, ContinuousOn (fun t => (A t * B t) i j) (Icc a b)) :
    (intervalVectorMatrixL2Mul A hA).comp (intervalVectorMatrixL2Mul B hB) =
      intervalVectorMatrixL2Mul (fun t => A t * B t) hAB := by
  ext u : 1
  apply intervalVectorL2_ext
  filter_upwards [intervalVectorMatrixL2Mul_ae A hA (intervalVectorMatrixL2Mul B hB u),
    intervalVectorMatrixL2Mul_ae B hB u,
    intervalVectorMatrixL2Mul_ae (fun t => A t * B t) hAB u] with t h₁ h₂ h₃
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, h₃, Matrix.mulVec_mulVec]

/-- Multiplication by the identity coefficient is the identity on vector
square-integrable functions. -/
theorem intervalVectorMatrixL2Mul_id [DecidableEq ι] :
    intervalVectorMatrixL2Mul (fun _ => (1 : Matrix ι ι ℝ))
      (fun _ _ => continuousOn_const) =
        ContinuousLinearMap.id ℝ (IntervalVectorL2 ι a b) := by
  ext u : 1
  apply intervalVectorL2_ext
  filter_upwards [intervalVectorMatrixL2Mul_ae (fun _ => (1 : Matrix ι ι ℝ))
    (fun _ _ => continuousOn_const) u] with t ht
  rw [ContinuousLinearMap.id_apply, ht, Matrix.one_mulVec]

/-- Two continuous coefficient families that agree on the interval induce
the same operator on interval $L^2$. -/
theorem intervalVectorMatrixL2Mul_congr
    (A B : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b))
    (hB : ∀ i j, ContinuousOn (fun t => B t i j) (Icc a b))
    (he : EqOn A B (Icc a b)) :
    intervalVectorMatrixL2Mul A hA = intervalVectorMatrixL2Mul B hB := by
  ext u : 1
  apply intervalVectorL2_ext
  filter_upwards [intervalVectorMatrixL2Mul_ae A hA u, intervalVectorMatrixL2Mul_ae B hB u,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht ht' hI
  rw [ht, ht', he (Ioo_subset_Icc_self hI)]

/-- Negating the coefficient negates its multiplication action on interval
$L^2$. -/
theorem intervalVectorMatrixL2Mul_neg
    (A : ℝ → Matrix κ ι ℝ)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc a b)) :
    intervalVectorMatrixL2Mul (fun t => -A t) (fun i j => (hA i j).neg) =
      -intervalVectorMatrixL2Mul A hA := by
  ext u : 1
  apply intervalVectorL2_ext
  let v := intervalVectorMatrixL2Mul A hA u
  have hneg : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ i, (-v i : Lp ℝ 2
      (volume.restrict (Ioo a b))) t = -v i t :=
    eventually_all.mpr fun i => Lp.coeFn_neg (v i)
  filter_upwards [intervalVectorMatrixL2Mul_ae (fun t => -A t) (fun i j => (hA i j).neg) u,
    intervalVectorMatrixL2Mul_ae A hA u, hneg] with t h₁ h₂ h₃
  rw [neg_apply, h₁, Matrix.neg_mulVec]
  exact (congrArg Neg.neg h₂.symm).trans (funext h₃).symm

end IntervalMatrixActions
