import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Numlib.IntegralEquations.Basic

/-!
# Integral operators with a weakly singular kernel

`Numlib/IntegralEquations/Basic` builds the integral operator `u ↦ (x ↦ ∫ k (x, y) u y dμ)` on
`C(X, ℝ)` for a *continuous* kernel. The kernels that boundary integral equations produce are not
continuous — `log |x − y|` and `‖x − y‖^{-β}` with `β < d` are the standard ones — but they are
integrable in `y`, and that is enough provided two conditions hold, the ones called (A₁) and (A₂)
in [han2009theoretical], §2.8.1:

* (A₁) the *modulus of continuity in the mean*
  `ω(h) = sup { ∫ |k (x, y) − k (z, y)| dμ y : dist x z ≤ h }` tends to `0` with `h`;
* (A₂) the row `L¹` norms `∫ |k (x, y)| dμ y` are bounded in `x`.

`IntegralOperator.IsAdmissibleKernel` bundles the two, with (A₁) in the equivalent `ε`–`δ` form
that every proof consumes. Both halves of the argument for a continuous kernel then survive:
(A₁) is what makes the image of a continuous function continuous and the image of the unit ball
equicontinuous, and (A₂) is what bounds the operator.

## Main statements

* `IntegralOperator.IsAdmissibleKernel` — the conditions, and `IntegralOperator.kernelModulus` the
  modulus `ω` of (A₁), with `IntegralOperator.IsAdmissibleKernel.tendsto_kernelModulus` its limit.
* `IntegralOperator.admissibleKernelCLM` — the operator on `C(X, ℝ)`, with
  `IntegralOperator.norm_admissibleKernelCLM_le` bounding its norm by
  `IntegralOperator.rowBound`, the supremum of (A₂), and
  `IntegralOperator.IsAdmissibleKernel.abs_admissibleKernelCLM_sub_le` the oscillation estimate
  in terms of `ω`.
* `IntegralOperator.isCompactOperator_admissibleKernelCLM` — **the operator is compact**, by
  Arzelà–Ascoli in the form `ContinuousMap.isCompact_closure_of_forall_norm_le`.
* `IntegralOperator.isAdmissibleKernel_of_continuousMap` — a continuous kernel on a compact metric
  space is admissible, and its operator is `IntegralOperator.kernelCLM`
  (`IntegralOperator.admissibleKernelCLM_eq_kernelCLM`); so this development subsumes the
  continuous case.
* `IntegralOperator.IsAdmissibleKernel.mul_continuousMap` — the splitting rule: an admissible
  kernel times a continuous factor is admissible, which is how a kernel written as a singular
  factor times a smooth one is handled.

The domain is a compact metric space rather than a closed bounded `D ⊆ ℝ^d`: the argument uses
nothing of the ambient space, and the metric enters only through the uniform statement of (A₁).

## Not developed here

The operator norm is only bounded, not computed: `‖K‖ = max_x ∫ |k (x, y)| dμ` — equation (2.8.6)
of [han2009theoretical] — needs a continuous `u` of norm one that nearly realises the sign of a row
of the kernel, and for a merely integrable row that is the density of `C(X, ℝ)` in `L¹(μ)`, which
this project does not have. The continuous-kernel case is `IntegralOperator.norm_kernelCLM`.

Nor is any concrete weakly singular kernel shown to be admissible: verifying (A₁) for
`|x − y|^{-γ}` on an interval is a real integral estimate, not a formality, and is what
[han2009theoretical] Examples 2.8.2 and 2.8.9 rest on.

## References

[han2009theoretical], §2.8.1, equations (2.8.2)–(2.8.6); [kress1989linear], §2, treats the same
conditions under the name of weakly singular kernels.
-/

open Filter MeasureTheory Metric Set Topology

namespace IntegralOperator

section Admissible

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {k : X × X → ℝ}

/-- **An admissible kernel**: one that is integrable in its second variable and satisfies the two
conditions (A₁) and (A₂) of [han2009theoretical], §2.8.1, which together make the integral operator
`u ↦ (x ↦ ∫ k (x, y) u y dμ)` a compact operator on `C(X, ℝ)`.

(A₁) is stated here in the `ε`–`δ` form rather than as a limit of the modulus of continuity
`IntegralOperator.kernelModulus`; the two agree by
`IntegralOperator.IsAdmissibleKernel.tendsto_kernelModulus` and
`IntegralOperator.IsAdmissibleKernel.le_kernelModulus`, and the `ε`–`δ` form is what the proofs
use. -/
structure IsAdmissibleKernel (μ : Measure X) (k : X × X → ℝ) : Prop where
  /-- Every row of the kernel is integrable. -/
  integrable_row : ∀ x, Integrable (fun y => k (x, y)) μ
  /-- Condition (A₂): the row `L¹` norms are bounded. -/
  bddAbove_integral_abs : BddAbove (Set.range fun x => ∫ y, |k (x, y)| ∂μ)
  /-- Condition (A₁): rows at nearby base points are close in `L¹`, uniformly in the base point. -/
  exists_delta : ∀ ε > 0, ∃ δ > 0, ∀ x z : X, dist x z < δ →
    (∫ y, |k (x, y) - k (z, y)| ∂μ) < ε

/-- The bound of condition (A₂) on a kernel: `sup_x ∫ |k (x, y)| dμ`. -/
noncomputable def rowBound (μ : Measure X) (k : X × X → ℝ) : ℝ := ⨆ x, ∫ y, |k (x, y)| ∂μ

namespace IsAdmissibleKernel

variable (hk : IsAdmissibleKernel μ k)
include hk

omit [CompactSpace X] [BorelSpace X] in
/-- Every row `L¹` norm is at most the (A₂) bound. -/
theorem le_rowBound (x : X) : (∫ y, |k (x, y)| ∂μ) ≤ rowBound μ k :=
  le_ciSup hk.bddAbove_integral_abs x

omit [CompactSpace X] [BorelSpace X] in
/-- The (A₂) bound of an admissible kernel is nonnegative. -/
theorem rowBound_nonneg : 0 ≤ rowBound μ k := by
  rcases isEmpty_or_nonempty X with h | h
  · rw [rowBound, Real.iSup_of_isEmpty]
  · exact le_trans (integral_nonneg fun _ => abs_nonneg _) (hk.le_rowBound h.some)

/-- The integrand of the operator attached to an admissible kernel is integrable. -/
theorem integrable_mul (u : C(X, ℝ)) (x : X) : Integrable (fun y => k (x, y) * u y) μ :=
  (hk.integrable_row x).mul_bdd u.continuous.aestronglyMeasurable
    (Eventually.of_forall fun y => u.norm_coe_le_norm y)

omit [CompactSpace X] [BorelSpace X] in
/-- The `L¹` distance between two rows of an admissible kernel. -/
theorem integrable_abs_row_sub (x z : X) : Integrable (fun y => |k (x, y) - k (z, y)|) μ := by
  have h : Integrable (fun y => k (x, y) - k (z, y)) μ :=
    (hk.integrable_row x).sub (hk.integrable_row z)
  exact h.abs

/-- The integral of the operator is bounded by the row `L¹` norm times `‖u‖`. -/
theorem abs_integral_mul_le (u : C(X, ℝ)) (x : X) :
    |∫ y, k (x, y) * u y ∂μ| ≤ (∫ y, |k (x, y)| ∂μ) * ‖u‖ := by
  have hint : Integrable (fun y => |k (x, y)| * ‖u‖) μ := ((hk.integrable_row x).abs).mul_const _
  calc |∫ y, k (x, y) * u y ∂μ| ≤ ∫ y, |k (x, y) * u y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |k (x, y)| * ‖u‖ ∂μ := by
        refine integral_mono (hk.integrable_mul u x).abs hint fun y => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y) (abs_nonneg _)
    _ = (∫ y, |k (x, y)| ∂μ) * ‖u‖ := integral_mul_const _ _

/-- The oscillation of the image of `u` between two base points is at most `‖u‖` times the `L¹`
distance between the two rows of the kernel. -/
theorem abs_integral_mul_sub_le (u : C(X, ℝ)) (x z : X) :
    |(∫ y, k (x, y) * u y ∂μ) - ∫ y, k (z, y) * u y ∂μ|
      ≤ (∫ y, |k (x, y) - k (z, y)| ∂μ) * ‖u‖ := by
  have hsub : (∫ y, k (x, y) * u y ∂μ) - ∫ y, k (z, y) * u y ∂μ
      = ∫ y, (k (x, y) - k (z, y)) * u y ∂μ := by
    rw [← integral_sub (hk.integrable_mul u x) (hk.integrable_mul u z)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hdiff : Integrable (fun y => (k (x, y) - k (z, y)) * u y) μ :=
    ((hk.integrable_row x).sub (hk.integrable_row z)).mul_bdd
      u.continuous.aestronglyMeasurable (Eventually.of_forall fun y => u.norm_coe_le_norm y)
  have hint : Integrable (fun y => |k (x, y) - k (z, y)| * ‖u‖) μ :=
    (hk.integrable_abs_row_sub x z).mul_const _
  rw [hsub]
  calc |∫ y, (k (x, y) - k (z, y)) * u y ∂μ| ≤ ∫ y, |(k (x, y) - k (z, y)) * u y| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, |k (x, y) - k (z, y)| * ‖u‖ ∂μ := by
        refine integral_mono hdiff.abs hint fun y => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y) (abs_nonneg _)
    _ = (∫ y, |k (x, y) - k (z, y)| ∂μ) * ‖u‖ := integral_mul_const _ _

/-- Condition (A₁) makes the image of a continuous function continuous. -/
theorem continuous_integral_mul (u : C(X, ℝ)) :
    Continuous fun x => ∫ y, k (x, y) * u y ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδk⟩ := hk.exists_delta (ε / (‖u‖ + 1)) (by positivity)
  filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
  rw [Real.dist_eq]
  have hlt : (∫ y, |k (x, y) - k (x₀, y)| ∂μ) < ε / (‖u‖ + 1) := hδk x x₀ hx
  have hnn : (0 : ℝ) ≤ ∫ y, |k (x, y) - k (x₀, y)| ∂μ := integral_nonneg fun _ => abs_nonneg _
  calc |(∫ y, k (x, y) * u y ∂μ) - ∫ y, k (x₀, y) * u y ∂μ|
      ≤ (∫ y, |k (x, y) - k (x₀, y)| ∂μ) * ‖u‖ := hk.abs_integral_mul_sub_le u x x₀
    _ ≤ ε / (‖u‖ + 1) * ‖u‖ := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg u)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg u, hε]

end IsAdmissibleKernel

/-- **The integral operator of an admissible kernel** on `C(X, ℝ)`, equation (2.8.2) of
[han2009theoretical]: `u ↦ (x ↦ ∫ k (x, y) u y dμ)`. Condition (A₁) is what makes the image
continuous, so it is needed already to define the operator, and condition (A₂) is what bounds it. -/
noncomputable def admissibleKernelCLM (hk : IsAdmissibleKernel μ k) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun x => ∫ y, k (x, y) * u y ∂μ, hk.continuous_integral_mul u⟩
      map_add' := fun u v => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [← integral_add (hk.integrable_mul u x) (hk.integrable_mul v x)]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)
      map_smul' := fun r u => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring) }
    (rowBound μ k) fun u => by
      rw [ContinuousMap.norm_le _ (mul_nonneg hk.rowBound_nonneg (norm_nonneg u))]
      intro x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk, Real.norm_eq_abs]
      exact le_trans (hk.abs_integral_mul_le u x)
        (mul_le_mul_of_nonneg_right (hk.le_rowBound x) (norm_nonneg u))

/-- The defining formula of `IntegralOperator.admissibleKernelCLM`. -/
@[simp]
theorem admissibleKernelCLM_apply (hk : IsAdmissibleKernel μ k) (u : C(X, ℝ)) (x : X) :
    admissibleKernelCLM hk u x = ∫ y, k (x, y) * u y ∂μ :=
  rfl

/-- The operator norm of an admissible kernel operator is at most `sup_x ∫ |k (x, y)| dμ`. -/
theorem norm_admissibleKernelCLM_le (hk : IsAdmissibleKernel μ k) :
    ‖admissibleKernelCLM hk‖ ≤ rowBound μ k :=
  LinearMap.mkContinuous_norm_le _ hk.rowBound_nonneg _

/-- **An admissible kernel gives a compact operator on `C(X, ℝ)`**: the image of the unit ball is
uniformly bounded by (A₂) and equicontinuous by (A₁), so Arzelà–Ascoli applies exactly as it does
for a continuous kernel. This is the unnumbered conclusion of [han2009theoretical], §2.8.1. -/
theorem isCompactOperator_admissibleKernelCLM (hk : IsAdmissibleKernel μ k) :
    IsCompactOperator (admissibleKernelCLM hk) := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (admissibleKernelCLM hk : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) one_pos).2 ?_
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := ‖admissibleKernelCLM hk‖) ?_ ?_
  · rintro f ⟨u, hu, rfl⟩ x
    calc ‖admissibleKernelCLM hk u x‖ ≤ ‖admissibleKernelCLM hk u‖ :=
          (admissibleKernelCLM hk u).norm_coe_le_norm x
      _ ≤ ‖admissibleKernelCLM hk‖ * ‖u‖ := (admissibleKernelCLM hk).le_opNorm u
      _ ≤ ‖admissibleKernelCLM hk‖ * 1 :=
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hu) (norm_nonneg _)
      _ = ‖admissibleKernelCLM hk‖ := mul_one _
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨δ, hδ, hδk⟩ := hk.exists_delta ε hε
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    rintro ⟨f, u, hu, rfl⟩
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    have hnn : (0 : ℝ) ≤ ∫ y, |k (x₀, y) - k (x, y)| ∂μ := integral_nonneg fun _ => abs_nonneg _
    rw [Real.dist_eq]
    calc |admissibleKernelCLM hk u x₀ - admissibleKernelCLM hk u x|
        ≤ (∫ y, |k (x₀, y) - k (x, y)| ∂μ) * ‖u‖ := hk.abs_integral_mul_sub_le u x₀ x
      _ ≤ (∫ y, |k (x₀, y) - k (x, y)| ∂μ) * 1 := mul_le_mul_of_nonneg_left hu1 hnn
      _ < ε := by
          rw [mul_one]
          exact hδk x₀ x (by rw [dist_comm]; exact mem_ball.1 hx)

/-- The **modulus of continuity in the mean** of a kernel: the supremum of the `L¹` distance
between two rows whose base points are within `h`. -/
noncomputable def kernelModulus (μ : Measure X) (k : X × X → ℝ) (h : ℝ) : ℝ :=
  ⨆ p : {p : X × X // dist p.1 p.2 ≤ h}, ∫ y, |k (p.1.1, y) - k (p.1.2, y)| ∂μ

namespace IsAdmissibleKernel

variable (hk : IsAdmissibleKernel μ k)
include hk

omit [CompactSpace X] [BorelSpace X] in
/-- The `L¹` distance between two rows is at most twice the (A₂) bound, so the family whose
supremum is the modulus of continuity is bounded. -/
theorem integral_abs_row_sub_le (x z : X) :
    (∫ y, |k (x, y) - k (z, y)| ∂μ) ≤ 2 * rowBound μ k := by
  have hI : Integrable (fun y => |k (x, y)| + |k (z, y)|) μ :=
    (hk.integrable_row x).abs.add (hk.integrable_row z).abs
  have h1 : (∫ y, |k (x, y) - k (z, y)| ∂μ) ≤ ∫ y, (|k (x, y)| + |k (z, y)|) ∂μ := by
    refine integral_mono (hk.integrable_abs_row_sub x z) hI fun y => ?_
    rw [sub_eq_add_neg]
    simpa using abs_add_le (k (x, y)) (-k (z, y))
  rw [integral_add (hk.integrable_row x).abs (hk.integrable_row z).abs] at h1
  have hx := hk.le_rowBound x
  have hz := hk.le_rowBound z
  linarith

omit [CompactSpace X] [BorelSpace X] in
/-- The family whose supremum defines the modulus of continuity is bounded above. -/
theorem bddAbove_modulus (h : ℝ) :
    BddAbove (Set.range fun p : {p : X × X // dist p.1 p.2 ≤ h} =>
      ∫ y, |k (p.1.1, y) - k (p.1.2, y)| ∂μ) := by
  refine ⟨2 * rowBound μ k, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact hk.integral_abs_row_sub_le p.1.1 p.1.2

omit [CompactSpace X] [BorelSpace X] in
/-- Every row distance is bounded by the modulus of continuity at the corresponding radius. -/
theorem le_kernelModulus {x z : X} {h : ℝ} (hxz : dist x z ≤ h) :
    (∫ y, |k (x, y) - k (z, y)| ∂μ) ≤ kernelModulus μ k h :=
  le_ciSup (hk.bddAbove_modulus h) (⟨(x, z), hxz⟩ : {p : X × X // dist p.1 p.2 ≤ h})

omit [CompactSpace X] [BorelSpace X] in
/-- The modulus of continuity is nonnegative. -/
theorem kernelModulus_nonneg (h : ℝ) : 0 ≤ kernelModulus μ k h := by
  rcases isEmpty_or_nonempty {p : X × X // dist p.1 p.2 ≤ h} with hE | hE
  · rw [kernelModulus, Real.iSup_of_isEmpty]
  · obtain ⟨⟨p, hp⟩⟩ := hE
    exact le_trans (integral_nonneg fun _ => abs_nonneg _) (hk.le_kernelModulus hp)

omit [CompactSpace X] [BorelSpace X] in
/-- **Condition (A₁)** in the book's own form: the modulus of continuity of an admissible kernel
tends to `0` as the radius does. -/
theorem tendsto_kernelModulus :
    Filter.Tendsto (kernelModulus μ k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδk⟩ := hk.exists_delta (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {h} hh hdist => ?_⟩
  have hh0 : (0 : ℝ) < h := hh
  have hhδ : h < δ := by simpa [Real.dist_eq, abs_of_pos hh0] using hdist
  have hle : kernelModulus μ k h ≤ ε / 2 :=
    Real.iSup_le (fun p => (hδk p.1.1 p.1.2 (lt_of_le_of_lt p.2 hhδ)).le) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hk.kernelModulus_nonneg h)]
  linarith

/-- **Estimate (2.8.5)**: the oscillation of `K u` between two base points is at most the modulus
of continuity of the kernel at their distance, times `‖u‖`. -/
theorem abs_admissibleKernelCLM_sub_le (u : C(X, ℝ)) (x z : X) :
    |admissibleKernelCLM hk u x - admissibleKernelCLM hk u z|
      ≤ kernelModulus μ k (dist x z) * ‖u‖ :=
  le_trans (hk.abs_integral_mul_sub_le u x z)
    (mul_le_mul_of_nonneg_right (hk.le_kernelModulus le_rfl) (norm_nonneg u))

end IsAdmissibleKernel

end Admissible

section ContinuousKernel

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- **A continuous kernel on a compact metric space is admissible**, so the operator and its
compactness specialize to `IntegralOperator.kernelCLM`. Condition (A₁) is the uniform continuity
of `k` on the compact `X × X`. -/
theorem isAdmissibleKernel_of_continuousMap (k : C(X × X, ℝ)) :
    IsAdmissibleKernel μ fun p => k p := by
  have hmnn : (0 : ℝ) ≤ μ.real univ := measureReal_nonneg
  refine ⟨fun x => integrable_kernel_row μ k x, ⟨‖k‖ * μ.real univ, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have h1 : ∫ y, |k (x, y)| ∂μ ≤ ∫ _y : X, ‖k‖ ∂μ :=
      integral_mono (integrable_kernel_row μ k x).abs (integrable_const _)
        fun y => by rw [← Real.norm_eq_abs]; exact k.norm_coe_le_norm _
    simpa [integral_const, smul_eq_mul, mul_comm] using h1
  · intro ε hε
    obtain ⟨δ, hδ, hδk⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous k.continuous)
      (ε / (μ.real univ + 1)) (by positivity)
    refine ⟨δ, hδ, fun x z hxz => ?_⟩
    have hpt : ∀ y : X, |k (x, y) - k (z, y)| ≤ ε / (μ.real univ + 1) := by
      intro y
      have hd : dist ((x, y) : X × X) (z, y) < δ := by
        rw [Prod.dist_eq]
        simpa using hxz
      have hk := hδk hd
      rw [Real.dist_eq] at hk
      exact hk.le
    have hI : Integrable (fun y => |k (x, y) - k (z, y)|) μ :=
      ((integrable_kernel_row μ k x).sub (integrable_kernel_row μ k z)).abs
    calc ∫ y, |k (x, y) - k (z, y)| ∂μ ≤ ∫ _y : X, ε / (μ.real univ + 1) ∂μ :=
          integral_mono hI (integrable_const _) hpt
      _ = μ.real univ * (ε / (μ.real univ + 1)) := by simp [integral_const, smul_eq_mul]
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [hε, hmnn]

/-- The operator of an admissible continuous kernel is `IntegralOperator.kernelCLM`. -/
theorem admissibleKernelCLM_eq_kernelCLM (k : C(X × X, ℝ)) :
    admissibleKernelCLM (isAdmissibleKernel_of_continuousMap μ k) = kernelCLM μ k := by
  ext u x
  rfl

end ContinuousKernel

section Approximation

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasure μ] {k : X × X → ℝ}

/-- **A kernel that continuous kernels approximate uniformly in the row `L¹` norm is admissible.**

This is the practical criterion for admissibility: both (A₁) and (A₂) are stable under a uniform
`L¹` perturbation of the rows, so it is enough to exhibit, for each `ε`, one *continuous* kernel
whose rows are within `ε` of those of `k` in `L¹(μ)`, uniformly in the row index. The continuous
kernel supplies (A₁) through `IntegralOperator.isAdmissibleKernel_of_continuousMap`, that is,
through its uniform continuity on the compact `X × X`.

The route is the one [han2009theoretical] takes for a singular kernel on an interval: regularize
the singularity, estimate the `L¹` distance to the regularization, and let the regularization
parameter go to zero. -/
theorem isAdmissibleKernel_of_forall_exists_continuousMap
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (happrox : ∀ ε > 0, ∃ g : C(X × X, ℝ), ∀ x, (∫ y, |k (x, y) - g (x, y)| ∂μ) ≤ ε) :
    IsAdmissibleKernel μ k := by
  have habs : ∀ (g : C(X × X, ℝ)) (x : X), Integrable (fun y => |k (x, y) - g (x, y)|) μ :=
    fun g x => ((hrow x).sub (integrable_kernel_row μ g x)).abs
  refine ⟨hrow, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := happrox 1 one_pos
    refine ⟨1 + ‖g‖ * μ.real univ, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hpt : ∀ y, |k (x, y)| ≤ |k (x, y) - g (x, y)| + |g (x, y)| := fun y => by
      simpa using abs_add_le (k (x, y) - g (x, y)) (g (x, y))
    have hgint : (∫ y, |g (x, y)| ∂μ) ≤ ‖g‖ * μ.real univ := by
      have h1 : ∫ y, |g (x, y)| ∂μ ≤ ∫ _y : X, ‖g‖ ∂μ :=
        integral_mono (integrable_kernel_row μ g x).abs (integrable_const _)
          fun y => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _
      simpa [integral_const, smul_eq_mul, mul_comm] using h1
    calc ∫ y, |k (x, y)| ∂μ ≤ ∫ y, (|k (x, y) - g (x, y)| + |g (x, y)|) ∂μ :=
          integral_mono (hrow x).abs ((habs g x).add (integrable_kernel_row μ g x).abs) hpt
      _ = (∫ y, |k (x, y) - g (x, y)| ∂μ) + ∫ y, |g (x, y)| ∂μ :=
          integral_add (habs g x) (integrable_kernel_row μ g x).abs
      _ ≤ 1 + ‖g‖ * μ.real univ := add_le_add (hg x) hgint
  · intro ε hε
    obtain ⟨g, hg⟩ := happrox (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hδg⟩ :=
      (isAdmissibleKernel_of_continuousMap μ g).exists_delta (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun x z hxz => ?_⟩
    have hgg : Integrable (fun y => |g (x, y) - g (z, y)|) μ :=
      ((integrable_kernel_row μ g x).sub (integrable_kernel_row μ g z)).abs
    have hpt : ∀ y, |k (x, y) - k (z, y)|
        ≤ |k (x, y) - g (x, y)| + |g (x, y) - g (z, y)| + |k (z, y) - g (z, y)| := by
      intro y
      have h1 := abs_sub_le (k (x, y)) (g (x, y)) (k (z, y))
      have h2 := abs_sub_le (g (x, y)) (g (z, y)) (k (z, y))
      have h3 : |g (z, y) - k (z, y)| = |k (z, y) - g (z, y)| := abs_sub_comm _ _
      linarith
    have h12 : Integrable
        (fun y => |k (x, y) - g (x, y)| + |g (x, y) - g (z, y)|) μ := (habs g x).add hgg
    calc ∫ y, |k (x, y) - k (z, y)| ∂μ
        ≤ ∫ y, (|k (x, y) - g (x, y)| + |g (x, y) - g (z, y)| + |k (z, y) - g (z, y)|) ∂μ :=
          integral_mono ((hrow x).sub (hrow z)).abs (h12.add (habs g z)) hpt
      _ = ((∫ y, |k (x, y) - g (x, y)| ∂μ) + ∫ y, |g (x, y) - g (z, y)| ∂μ)
            + ∫ y, |k (z, y) - g (z, y)| ∂μ := by
          rw [integral_add h12 (habs g z), integral_add (habs g x) hgg]
      _ < ε := by
          have h1 := hg x
          have h2 := hδg x z hxz
          have h3 := hg z
          linarith

/-- **The operator norm of an admissible kernel operator is the largest row integral**,
`‖K‖ = sup_x ∫ |k (x, y)| dμ`, equation (2.8.6) of [han2009theoretical].

`IntegralOperator.norm_admissibleKernelCLM_le` is the easy half. For the other one, testing `K`
against a continuous approximation of the sign of the row `k (x₀, ·)` needs that row to be
approximable by continuous functions in `L¹(μ)`, which for a finite Borel measure on a metric space
is `MeasureTheory.Integrable.exists_boundedContinuous_integral_sub_le`; the sign is then
approximated as in `IntegralOperator.norm_kernelCLM`, by `y ↦ g y / (|g y| + δ)`.

Unlike the continuous case there is no reason for the supremum to be attained, so it is a `⨆` and
not a `max`. -/
theorem norm_admissibleKernelCLM (hk : IsAdmissibleKernel μ k) :
    ‖admissibleKernelCLM hk‖ = rowBound μ k := by
  refine le_antisymm (norm_admissibleKernelCLM_le hk) ?_
  refine Real.iSup_le (fun x₀ => ?_) (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set M : ℝ := μ.real univ with hM
  have hMnn : (0 : ℝ) ≤ M := measureReal_nonneg
  set δ : ℝ := ε / (3 * (M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hgapprox, hgint⟩ :=
    MeasureTheory.Integrable.exists_boundedContinuous_integral_sub_le
      (hk.integrable_row x₀) (ε := ε / 3) (by positivity)
  have hpos : ∀ y : X, (0 : ℝ) < |g y| + δ := fun y => add_pos_of_nonneg_of_pos (abs_nonneg _) hδ
  set w : C(X, ℝ) :=
    { toFun := fun y => g y / (|g y| + δ)
      continuous_toFun := Continuous.div (by fun_prop) (by fun_prop) fun y => (hpos y).ne' }
    with hwdef
  have hwapp : ∀ y : X, w y = g y / (|g y| + δ) := fun _ => rfl
  have hwle : ∀ y : X, |w y| ≤ 1 := by
    intro y
    rw [hwapp, abs_div, abs_of_pos (hpos y), div_le_one (hpos y)]
    linarith [abs_nonneg (g y)]
  have hfg : (∫ y, |k (x₀, y) - g y| ∂μ) ≤ ε / 3 := by
    simpa [Real.norm_eq_abs] using hgapprox
  have hdiff : Integrable (fun y => k (x₀, y) - g y) μ := (hk.integrable_row x₀).sub hgint
  have hfw : Integrable (fun y => k (x₀, y) * w y) μ := hk.integrable_mul w x₀
  have hgw : Integrable (fun y => g y * w y) μ :=
    hgint.mul_bdd w.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hwle y)
  -- the row `L¹` norm of `g` is within `ε / 3` of that of the row of `k`
  have hstep1 : (∫ y, |k (x₀, y)| ∂μ) ≤ (∫ y, |g y| ∂μ) + ε / 3 := by
    have hpt : ∀ y, |k (x₀, y)| ≤ |g y| + |k (x₀, y) - g y| := fun y => by
      have := abs_sub_abs_le_abs_sub (k (x₀, y)) (g y)
      linarith
    have hsum : Integrable (fun y => |g y| + |k (x₀, y) - g y|) μ := hgint.abs.add hdiff.abs
    calc ∫ y, |k (x₀, y)| ∂μ ≤ ∫ y, (|g y| + |k (x₀, y) - g y|) ∂μ :=
          integral_mono (hk.integrable_row x₀).abs hsum hpt
      _ = (∫ y, |g y| ∂μ) + ∫ y, |k (x₀, y) - g y| ∂μ := integral_add hgint.abs hdiff.abs
      _ ≤ (∫ y, |g y| ∂μ) + ε / 3 := by linarith
  -- `w` nearly realises the sign of `g`
  have hstep2 : (∫ y, |g y| ∂μ) - δ * M ≤ ∫ y, g y * w y ∂μ := by
    have hpt : ∀ y, |g y| - δ ≤ g y * w y := by
      intro y
      rw [hwapp, ← mul_div_assoc, le_div_iff₀ (hpos y)]
      nlinarith [abs_mul_abs_self (g y), mul_pos hδ hδ]
    have h1 : (∫ y, (|g y| - δ) ∂μ) ≤ ∫ y, g y * w y ∂μ :=
      integral_mono (hgint.abs.sub (integrable_const δ)) hgw hpt
    rwa [integral_sub hgint.abs (integrable_const δ), integral_const, smul_eq_mul,
      mul_comm M δ] at h1
  -- and it tests the row of `k` almost as well as it tests `g`
  have hstep3 : (∫ y, g y * w y ∂μ) - ε / 3 ≤ ∫ y, k (x₀, y) * w y ∂μ := by
    have hpt : ∀ y, g y * w y - |k (x₀, y) - g y| ≤ k (x₀, y) * w y := by
      intro y
      have h1 : |(k (x₀, y) - g y) * w y| ≤ |k (x₀, y) - g y| := by
        rw [abs_mul]
        nlinarith [abs_nonneg (k (x₀, y) - g y), hwle y, abs_nonneg (w y)]
      have h2 := abs_le.1 h1
      nlinarith [h2.1]
    have hsub : Integrable (fun y => g y * w y - |k (x₀, y) - g y|) μ := hgw.sub hdiff.abs
    have h1 : (∫ y, (g y * w y - |k (x₀, y) - g y|) ∂μ) ≤ ∫ y, k (x₀, y) * w y ∂μ :=
      integral_mono hsub hfw hpt
    rw [integral_sub hgw hdiff.abs] at h1
    linarith
  have hop : (∫ y, k (x₀, y) * w y ∂μ) ≤ ‖admissibleKernelCLM hk‖ := by
    have hwnorm : ‖w‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      exact fun y => by rw [Real.norm_eq_abs]; exact hwle y
    calc ∫ y, k (x₀, y) * w y ∂μ = admissibleKernelCLM hk w x₀ := rfl
      _ ≤ ‖admissibleKernelCLM hk w‖ := (admissibleKernelCLM hk w).apply_le_norm x₀
      _ ≤ ‖admissibleKernelCLM hk‖ * ‖w‖ := (admissibleKernelCLM hk).le_opNorm w
      _ ≤ ‖admissibleKernelCLM hk‖ := by
          nlinarith [norm_nonneg (admissibleKernelCLM hk), norm_nonneg w]
  have hδM : δ * M ≤ ε / 3 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε.le, hMnn]
  linarith

end Approximation

section Splitting

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {k : X × X → ℝ}

/-- **The splitting rule**: an admissible kernel multiplied by a continuous factor is again
admissible. This is what reduces a kernel of the form `k (x, y) = h (x, y) * g (x, y)` with `h`
singular and `g` continuous to the singular factor alone. -/
theorem IsAdmissibleKernel.mul_continuousMap (hk : IsAdmissibleKernel μ k) (g : C(X × X, ℝ)) :
    IsAdmissibleKernel μ fun p => k p * g p := by
  have hgm : ∀ x : X, AEStronglyMeasurable (fun y => g (x, y)) μ := by
    intro x
    exact (g.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hgb : ∀ x : X, ∀ y : X, |g (x, y)| ≤ ‖g‖ := fun x y => by
    rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _
  have hrow : ∀ x : X, Integrable (fun y => k (x, y) * g (x, y)) μ := fun x =>
    (hk.integrable_row x).mul_bdd (hgm x)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb x y)
  refine ⟨hrow, ⟨‖g‖ * rowBound μ k, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have h1 : ∫ y, |k (x, y) * g (x, y)| ∂μ ≤ ∫ y, |k (x, y)| * ‖g‖ ∂μ := by
      refine integral_mono (hrow x).abs ((hk.integrable_row x).abs.mul_const _) fun y => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb x y) (abs_nonneg _)
    rw [integral_mul_const] at h1
    calc ∫ y, |k (x, y) * g (x, y)| ∂μ ≤ (∫ y, |k (x, y)| ∂μ) * ‖g‖ := h1
      _ ≤ ‖g‖ * rowBound μ k := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hk.le_rowBound x) (norm_nonneg g)
  · intro ε hε
    have hgnn : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
    have hMnn : (0 : ℝ) ≤ rowBound μ k := hk.rowBound_nonneg
    obtain ⟨δ₁, hδ₁, hδ₁k⟩ := hk.exists_delta (ε / (2 * (‖g‖ + 1))) (by positivity)
    obtain ⟨δ₂, hδ₂, hδ₂g⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous g.continuous)
      (ε / (2 * (rowBound μ k + 1))) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x z hxz => ?_⟩
    have hx1 : dist x z < δ₁ := lt_of_lt_of_le hxz (min_le_left _ _)
    have hx2 : dist x z < δ₂ := lt_of_lt_of_le hxz (min_le_right _ _)
    have hgdiff : ∀ y : X, |g (x, y) - g (z, y)| ≤ ε / (2 * (rowBound μ k + 1)) := by
      intro y
      have hd : dist ((x, y) : X × X) (z, y) < δ₂ := by
        rw [Prod.dist_eq]
        simpa using hx2
      have h := hδ₂g hd
      rw [Real.dist_eq] at h
      exact h.le
    have hbound : ∀ y : X, |k (x, y) * g (x, y) - k (z, y) * g (z, y)|
        ≤ |k (x, y) - k (z, y)| * ‖g‖
          + |k (z, y)| * (ε / (2 * (rowBound μ k + 1))) := by
      intro y
      have heq : k (x, y) * g (x, y) - k (z, y) * g (z, y)
          = (k (x, y) - k (z, y)) * g (x, y) + k (z, y) * (g (x, y) - g (z, y)) := by ring
      rw [heq]
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgb x y) (abs_nonneg _)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgdiff y) (abs_nonneg _)
    have hI1 : Integrable (fun y => |k (x, y) - k (z, y)| * ‖g‖) μ :=
      (hk.integrable_abs_row_sub x z).mul_const _
    have hI2 : Integrable (fun y => |k (z, y)| * (ε / (2 * (rowBound μ k + 1)))) μ :=
      (hk.integrable_row z).abs.mul_const _
    have hA : (0 : ℝ) ≤ ∫ y, |k (x, y) - k (z, y)| ∂μ := integral_nonneg fun _ => abs_nonneg _
    have hB : (0 : ℝ) ≤ ∫ y, |k (z, y)| ∂μ := integral_nonneg fun _ => abs_nonneg _
    have hAlt : (∫ y, |k (x, y) - k (z, y)| ∂μ) < ε / (2 * (‖g‖ + 1)) := hδ₁k x z hx1
    have hBle : (∫ y, |k (z, y)| ∂μ) ≤ rowBound μ k := hk.le_rowBound z
    calc ∫ y, |k (x, y) * g (x, y) - k (z, y) * g (z, y)| ∂μ
        ≤ ∫ y, (|k (x, y) - k (z, y)| * ‖g‖
            + |k (z, y)| * (ε / (2 * (rowBound μ k + 1)))) ∂μ :=
          integral_mono (((hrow x).sub (hrow z)).abs) (hI1.add hI2) hbound
      _ = (∫ y, |k (x, y) - k (z, y)| ∂μ) * ‖g‖
            + (∫ y, |k (z, y)| ∂μ) * (ε / (2 * (rowBound μ k + 1))) := by
          rw [integral_add hI1 hI2, integral_mul_const, integral_mul_const]
      _ < ε := by
          have hg1 : (0 : ℝ) < ‖g‖ + 1 := by positivity
          have h1 : (∫ y, |k (x, y) - k (z, y)| ∂μ) * ‖g‖ < ε / 2 := by
            rw [div_mul_eq_div_div] at hAlt
            have hlt := (lt_div_iff₀ hg1).1 hAlt
            nlinarith [hA, hgnn, hlt]
          have h2 : (∫ y, |k (z, y)| ∂μ) * (ε / (2 * (rowBound μ k + 1))) ≤ ε / 2 := by
            have hc : (0 : ℝ) ≤ ε / (2 * (rowBound μ k + 1)) := by positivity
            have := mul_le_mul_of_nonneg_right hBle hc
            refine le_trans this ?_
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hε.le, hMnn]
          linarith
end Splitting

end IntegralOperator
