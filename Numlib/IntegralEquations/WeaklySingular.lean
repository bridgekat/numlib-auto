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
* `IntegralOperator.isAdmissibleKernel_of_abs_le_rpow` — **the concrete criterion on an interval**:
  a kernel continuous off the diagonal and bounded by `C |x − y| ^ (-γ)` with `γ < 1` is
  admissible. `IntegralOperator.isAdmissibleKernel_abs_sub_rpow` is the kernel `|x − y| ^ (-γ)`
  itself, and `IntegralOperator.isAdmissibleKernel_log_cos_sub_cos` the logarithmic kernel
  `log |cos x − cos y|` on `[0, π]`.

The domain is a compact metric space rather than a closed bounded `D ⊆ ℝ^d`: the argument uses
nothing of the ambient space, and the metric enters only through the uniform statement of (A₁).

## References

[han2009theoretical], §2.8.1, equations (2.8.2)–(2.8.6); [kress1989linear], §2, treats the same
conditions under the name of weakly singular kernels.
-/

open Filter MeasureTheory Metric Set Topology

open scoped Real

/-! ### The algebraic singularity `|t| ^ r` on the line

Two facts about `t ↦ |t| ^ r` for `-1 < r`, the profile of every singular kernel treated below: it
is interval integrable across its singularity, and its integral over an interval centred at that
singularity is explicit. Mathlib has both for `t ↦ t ^ r`, which at a negative argument is
`|t| ^ r` times `cos (r π)` and so is a different function. -/

/-- The algebraic singularity `t ↦ |t| ^ r` is interval integrable exactly when it is integrable at
the origin, that is, when `-1 < r`. -/
theorem intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun t => |t| ^ r) volume a b := by
  have hpos : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun t => |t| ^ r) volume 0 c := by
    intro c hc
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr
    rw [intervalIntegrable_iff, uIoc_of_le hc] at h ⊢
    exact h.congr_fun (fun t ht => by rw [abs_of_pos ht.1]) measurableSet_Ioc
  have key : ∀ c : ℝ, IntervalIntegrable (fun t => |t| ^ r) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · rw [IntervalIntegrable.iff_comp_neg]
      simpa using hpos (-c) (by linarith)
  exact (key a).symm.trans (key b)

/-- The integral of the algebraic singularity `|t| ^ r` over an interval centred at its singular
point: over `[-s, s]` it is `2 s ^ (r + 1) / (r + 1)`. -/
theorem integral_abs_rpow_neg_self {r : ℝ} (hr : -1 < r) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t in (-s)..s, |t| ^ r = 2 * s ^ (r + 1) / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := by linarith
  have hhalf : ∫ t in (0 : ℝ)..s, |t| ^ r = s ^ (r + 1) / (r + 1) := by
    have h1 : ∫ t in (0 : ℝ)..s, |t| ^ r = ∫ t in (0 : ℝ)..s, t ^ r :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hs] at ht; rw [abs_of_nonneg ht.1]
    rw [h1, integral_rpow (Or.inl hr), Real.zero_rpow hr1, sub_zero]
  have hrefl : ∫ t in (-s)..(0 : ℝ), |t| ^ r = ∫ t in (0 : ℝ)..s, |t| ^ r := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := s) fun t => |t| ^ r
    simpa using h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
      (intervalIntegrable_abs_rpow hr _ _) (intervalIntegrable_abs_rpow hr _ _), hrefl, hhalf]
  ring

/-- A logarithm is dominated by any algebraic singularity at the origin. This crude two-sided form
is what a logarithmic kernel needs in order to fit under an algebraic bound. -/
theorem abs_log_le_two_mul_rpow {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ 2 * (u ^ ((1 : ℝ) / 2) + u ^ (-((1 : ℝ) / 2))) := by
  have h1 : (0 : ℝ) < u ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  have h2 : (0 : ℝ) < u ^ (-((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hu _
  have b1 := Real.log_le_sub_one_of_pos h1
  have b2 := Real.log_le_sub_one_of_pos h2
  rw [Real.log_rpow hu] at b1 b2
  rw [abs_le]
  constructor <;> linarith

/-- **The cosine separates the points of `[0, π]` at least quadratically**:
`2 |x − y|² / π² ≤ |cos x − cos y|`. Both factors of
`cos x − cos y = -2 sin ((x + y)/2) sin ((x − y)/2)` are bounded below by `|x − y| / π`, by Jordan's
inequality applied at `(x + y)/2` or at `π − (x + y)/2`, whichever of the two lies in `[0, π/2]`. -/
theorem two_mul_sq_div_pi_sq_le_abs_cos_sub_cos {x y : ℝ} (hx : x ∈ Icc 0 π) (hy : y ∈ Icc 0 π) :
    2 * |x - y| ^ 2 / π ^ 2 ≤ |Real.cos x - Real.cos y| := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : (0 : ℝ) ≤ (x + y) / 2 := by linarith [hx.1, hy.1]
  have hs2 : (x + y) / 2 ≤ π := by linarith [hx.2, hy.2]
  have hupi : |x - y| ≤ π := abs_le.2 ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  have hA : |x - y| ≤ π * Real.sin ((x + y) / 2) := by
    rcases le_total ((x + y) / 2) (π / 2) with h | h
    · have hm := Real.mul_le_sin hs h
      have hxy : |x - y| ≤ x + y := abs_le.2 ⟨by linarith [hx.1], by linarith [hy.1]⟩
      have key : π * (2 / π * ((x + y) / 2)) = x + y := by field_simp
      linarith [mul_le_mul_of_nonneg_left hm hpi.le]
    · rw [← Real.sin_pi_sub]
      have hm := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ π - (x + y) / 2) (by linarith)
      have hxy : |x - y| ≤ 2 * π - x - y :=
        abs_le.2 ⟨by linarith [hy.2], by linarith [hx.2]⟩
      have key : π * (2 / π * (π - (x + y) / 2)) = 2 * π - x - y := by field_simp; ring
      linarith [mul_le_mul_of_nonneg_left hm hpi.le]
  have habs2 : |(x - y) / 2| = |x - y| / 2 := by rw [abs_div, abs_two]
  have hB : |x - y| ≤ π * |Real.sin ((x - y) / 2)| := by
    have hz : |(x - y) / 2| ≤ π / 2 := by rw [habs2]; linarith
    have hm := Real.mul_abs_le_abs_sin hz
    have key : π * (2 / π * |(x - y) / 2|) = |x - y| := by rw [habs2]; field_simp
    linarith [mul_le_mul_of_nonneg_left hm hpi.le]
  have hsnn : (0 : ℝ) ≤ Real.sin ((x + y) / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hs hs2
  rw [Real.cos_sub_cos]
  have hrw : |(-2 : ℝ) * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)|
      = 2 * Real.sin ((x + y) / 2) * |Real.sin ((x - y) / 2)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hsnn]
    norm_num
  rw [hrw, div_le_iff₀ (by positivity : (0 : ℝ) < π ^ 2)]
  nlinarith [mul_le_mul hA hB (abs_nonneg (x - y)) (by positivity : (0 : ℝ) ≤ π *
    Real.sin ((x + y) / 2)), abs_nonneg (Real.sin ((x - y) / 2)), hsnn, hpi]

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

section AlgebraicSingularity

/-! ### Kernels with an algebraic singularity on the diagonal

The concrete weakly singular kernels of [han2009theoretical] §2.8.1 live on an interval and are
continuous off the diagonal, with `|k (x, y)| ≤ C |x − y| ^ (-γ)` for some `0 < γ < 1`. That alone
makes them admissible, and the two Examples the book gives are instances.

The uniformity in (A₁) — the point the book leaves to the reader — comes out of translation
invariance rather than out of a two-point estimate. Excising the diagonal with a continuous cut-off
leaves a row error bounded by `C ψ (x − y)` for one fixed nonnegative profile `ψ` vanishing away
from the origin, and the substitution `t = x − y` turns the row integral into an integral of `ψ`
over an interval that, whatever `x ∈ [a, b]` is, sits inside one fixed symmetric interval. What is
left to bound is then a single number, `2 C s ^ (1 - γ) / (1 - γ)`, with no `x` in it. -/

variable {a b : ℝ}

/-- Translating a nonnegative integrand by a point of `[a, b]` and integrating over `[a, b]` is
dominated by integrating it over a symmetric interval long enough to contain every translate. This
is what makes an estimate for a difference kernel on an interval uniform in the row index. -/
theorem integral_comp_sub_le {x M : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b) (hM : b - a ≤ M)
    {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf : IntervalIntegrable f volume (-M) M) :
    (∫ y in a..b, f (x - y)) ≤ ∫ t in (-M)..M, f t := by
  rw [intervalIntegral.integral_comp_sub_left f x]
  exact intervalIntegral.integral_mono_interval (by linarith [hx.1]) (by linarith)
    (by linarith [hx.2]) (Eventually.of_forall hf0) hf

/-- **A kernel with an algebraic singularity on the diagonal of an interval is admissible.** If `k`
is continuous off the diagonal of `[a, b] × [a, b]` and `|k (x, y)| ≤ C |x − y| ^ (-γ)` with
`0 < γ < 1`, then `k` satisfies (A₁) and (A₂), so
`IntegralOperator.isCompactOperator_admissibleKernelCLM` makes its integral operator compact on
`C[a, b]`.

Note that the hypothesis at a diagonal point reads `|k (x, x)| ≤ C * 0`, since `0 ^ (-γ) = 0`; so it
also fixes the value of `k` on the diagonal to be `0`. That is the value `|x − y| ^ (-γ)` and
`log |cos x − cos y|` both take there, both being of the form `f (x − y)` for an `f` that Lean's
conventions send to `0` at `0`.

The proof is `IntegralOperator.isAdmissibleKernel_of_forall_exists_continuousMap` applied to the
truncations `k (x, y) * χ |x − y|`, with `χ` a cut-off vanishing on a neighbourhood of the diagonal;
that neighbourhood is where the truncation is continuous for free, and the `L¹` distance to `k`
there is controlled by `IntegralOperator.integral_comp_sub_le` and `integral_abs_rpow_neg_self`. -/
theorem isAdmissibleKernel_of_abs_le_rpow {γ C : ℝ} (hab : a ≤ b) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hC : 0 ≤ C) {k : Icc a b × Icc a b → ℝ}
    (hcont : ContinuousOn k {p : Icc a b × Icc a b | (p.1 : ℝ) ≠ (p.2 : ℝ)})
    (hle : ∀ p : Icc a b × Icc a b, |k p| ≤ C * |(p.1 : ℝ) - (p.2 : ℝ)| ^ (-γ)) :
    IsAdmissibleKernel (iccMeasure a b) k := by
  have hexp : (-1 : ℝ) < -γ := by linarith
  have hone : (0 : ℝ) < 1 - γ := by linarith
  have hdomii : ∀ x : Icc a b,
      IntervalIntegrable (fun y => C * |(x : ℝ) - y| ^ (-γ)) volume a b := by
    intro x
    have h := (intervalIntegrable_abs_rpow hexp ((x : ℝ) - a) ((x : ℝ) - b)).comp_sub_left (x : ℝ)
    simp only [sub_sub_cancel] at h
    exact h.const_mul C
  have hrow : ∀ x : Icc a b, Integrable (fun y : Icc a b => k (x, y)) (iccMeasure a b) := by
    intro x
    have hms : MeasurableSet {y : Icc a b | (y : ℝ) ≠ (x : ℝ)} :=
      (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
    have hcy : ContinuousOn (fun y : Icc a b => k (x, y)) {y : Icc a b | (y : ℝ) ≠ (x : ℝ)} :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) fun y hy hc => hy hc.symm
    have hmeas : AEStronglyMeasurable (fun y : Icc a b => k (x, y)) (iccMeasure a b) := by
      have h := hcy.aestronglyMeasurable (μ := iccMeasure a b) hms
      rwa [restrict_ne_iccMeasure x] at h
    refine Integrable.mono' (integrable_iccMeasure hab (hdomii x)) hmeas
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hle (x, y)
  refine isAdmissibleKernel_of_forall_exists_continuousMap hrow ?_
  intro ε hε
  -- the width of the excised neighbourhood of the diagonal
  set s : ℝ := (ε * (1 - γ) / (2 * C + 1)) ^ (1 / (1 - γ)) with hsdef
  have hu : (0 : ℝ) < ε * (1 - γ) / (2 * C + 1) := by positivity
  have hspos : (0 : ℝ) < s := Real.rpow_pos_of_pos hu _
  have hspow : s ^ (1 - γ) = ε * (1 - γ) / (2 * C + 1) := by
    rw [hsdef, ← Real.rpow_mul hu.le, one_div, inv_mul_cancel₀ hone.ne', Real.rpow_one]
  set r : ℝ := s / 2 with hrdef
  have hrpos : (0 : ℝ) < r := by positivity
  -- the cut-off: `0` on `[0, r]`, `1` beyond `2 r = s`
  set χ : ℝ → ℝ := fun t => min 1 (max 0 (t / r - 1)) with hχdef
  have hχcont : Continuous χ := by fun_prop
  have hχnn : ∀ t, 0 ≤ χ t := fun _ => le_min zero_le_one (le_max_left _ _)
  have hχle : ∀ t, χ t ≤ 1 := fun _ => min_le_left _ _
  have hχ0 : ∀ t, t ≤ r → χ t = 0 := by
    intro t ht
    have h : t / r - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hrpos]; exact ht
    simp only [hχdef, max_eq_left h]
    exact min_eq_right zero_le_one
  have hχ1 : ∀ t, 2 * r ≤ t → χ t = 1 := by
    intro t ht
    have h1 : (1 : ℝ) ≤ t / r - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hrpos]; linarith
    simp only [hχdef]
    exact min_eq_left (le_max_of_le_right h1)
  -- the excised singular profile
  set ψ : ℝ → ℝ := fun t => |t| ^ (-γ) * (1 - χ |t|) with hψdef
  have hψnn : ∀ t, 0 ≤ ψ t := fun t =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by linarith [hχle |t|])
  have hψle : ∀ t, ψ t ≤ |t| ^ (-γ) := by
    intro t
    have h1 : (0 : ℝ) ≤ |t| ^ (-γ) := Real.rpow_nonneg (abs_nonneg _) _
    simp only [hψdef]
    nlinarith [hχnn |t|, hχle |t|]
  have hψ0 : ∀ t, s ≤ |t| → ψ t = 0 := by
    intro t ht
    have h : χ |t| = 1 := hχ1 _ (by rw [hrdef]; linarith)
    simp only [hψdef, h, sub_self, mul_zero]
  have hψii : ∀ p q : ℝ, IntervalIntegrable ψ volume p q := fun p q =>
    (intervalIntegrable_abs_rpow hexp p q).mul_continuousOn
      (continuous_const.sub (hχcont.comp continuous_abs)).continuousOn
  set M : ℝ := max (b - a) s with hMdef
  have hMs : s ≤ M := le_max_right _ _
  have hMba : b - a ≤ M := le_max_left _ _
  have hkey : (∫ t in (-M)..M, ψ t) ≤ 2 * s ^ (1 - γ) / (1 - γ) := by
    have h1 : ∫ t in (-M)..(-s), ψ t = 0 := by
      have heq : Set.EqOn ψ (fun _ => (0 : ℝ)) (uIcc (-M) (-s)) := by
        intro t ht
        rw [uIcc_of_le (by linarith)] at ht
        exact hψ0 t (by rw [abs_of_nonpos (by linarith [ht.2, hspos] : t ≤ 0)]; linarith [ht.2])
      rw [intervalIntegral.integral_congr heq]
      simp
    have h2 : ∫ t in s..M, ψ t = 0 := by
      have heq : Set.EqOn ψ (fun _ => (0 : ℝ)) (uIcc s M) := by
        intro t ht
        rw [uIcc_of_le hMs] at ht
        exact hψ0 t (by rw [abs_of_nonneg (by linarith [ht.1, hspos] : (0 : ℝ) ≤ t)]; exact ht.1)
      rw [intervalIntegral.integral_congr heq]
      simp
    have hsplit : ∫ t in (-M)..M, ψ t = ∫ t in (-s)..s, ψ t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (a := -M) (b := -s) (c := M)
          (hψii _ _) (hψii _ _), h1, zero_add,
        ← intervalIntegral.integral_add_adjacent_intervals (a := -s) (b := s) (c := M)
          (hψii _ _) (hψii _ _), h2, add_zero]
    rw [hsplit]
    calc ∫ t in (-s)..s, ψ t ≤ ∫ t in (-s)..s, |t| ^ (-γ) :=
          intervalIntegral.integral_mono_on (by linarith) (hψii _ _)
            (intervalIntegrable_abs_rpow hexp _ _) fun t _ => hψle t
      _ = 2 * s ^ (-γ + 1) / (-γ + 1) := integral_abs_rpow_neg_self hexp hspos.le
      _ = 2 * s ^ (1 - γ) / (1 - γ) := by rw [show -γ + 1 = 1 - γ by ring]
  refine ⟨⟨fun p => k p * χ |(p.1 : ℝ) - (p.2 : ℝ)|, ?_⟩, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : (p.1 : ℝ) = (p.2 : ℝ)
    · have hU : {q : Icc a b × Icc a b | |(q.1 : ℝ) - (q.2 : ℝ)| < r} ∈ 𝓝 p :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp [hp, hrpos])
      refine ContinuousAt.congr (f := fun _ : Icc a b × Icc a b => (0 : ℝ)) continuousAt_const ?_
      filter_upwards [hU] with q hq
      rw [hχ0 _ hq.le, mul_zero]
    · have hS : {q : Icc a b × Icc a b | (q.1 : ℝ) ≠ (q.2 : ℝ)} ∈ 𝓝 p :=
        (isOpen_ne_fun (by fun_prop) (by fun_prop)).mem_nhds hp
      have hc2 : Continuous fun q : Icc a b × Icc a b => χ |(q.1 : ℝ) - (q.2 : ℝ)| :=
        (hχcont.comp continuous_abs).comp (by fun_prop)
      exact (hcont.continuousAt hS).mul hc2.continuousAt
  · intro x
    simp only [ContinuousMap.coe_mk]
    have hbdd : ∀ y : Icc a b,
        |k (x, y) - k (x, y) * χ (abs ((x : ℝ) - (y : ℝ)))| ≤ C * ψ ((x : ℝ) - (y : ℝ)) := by
      intro y
      set w : ℝ := abs ((x : ℝ) - (y : ℝ)) with hwdef
      have h3 : (0 : ℝ) ≤ 1 - χ w := by linarith [hχle w]
      have h1 : k (x, y) - k (x, y) * χ w = k (x, y) * (1 - χ w) := by ring
      rw [h1, abs_mul, abs_of_nonneg h3]
      calc |k (x, y)| * (1 - χ w) ≤ C * w ^ (-γ) * (1 - χ w) :=
            mul_le_mul_of_nonneg_right (hle (x, y)) h3
        _ = C * ψ ((x : ℝ) - (y : ℝ)) := by simp only [hψdef, ← hwdef]; ring
    have hψint : Integrable (fun y : Icc a b => C * ψ ((x : ℝ) - (y : ℝ))) (iccMeasure a b) := by
      refine integrable_iccMeasure (f := fun t => C * ψ ((x : ℝ) - t)) hab ?_
      have h := (hψii ((x : ℝ) - a) ((x : ℝ) - b)).comp_sub_left (x : ℝ)
      simp only [sub_sub_cancel] at h
      exact h.const_mul C
    have hgint : Integrable (fun y : Icc a b => k (x, y) * χ (abs ((x : ℝ) - (y : ℝ))))
        (iccMeasure a b) :=
      (hrow x).mul_bdd ((hχcont.comp (by fun_prop)).aestronglyMeasurable)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hχnn _)]; exact hχle _)
    calc ∫ y : Icc a b, |k (x, y) - k (x, y) * χ (abs ((x : ℝ) - (y : ℝ)))| ∂iccMeasure a b
        ≤ ∫ y : Icc a b, C * ψ ((x : ℝ) - (y : ℝ)) ∂iccMeasure a b :=
          integral_mono ((hrow x).sub hgint).abs hψint hbdd
      _ = ∫ y in a..b, C * ψ ((x : ℝ) - y) :=
          integral_iccMeasure hab fun t => C * ψ ((x : ℝ) - t)
      _ = C * ∫ y in a..b, ψ ((x : ℝ) - y) := intervalIntegral.integral_const_mul _ _
      _ ≤ C * ∫ t in (-M)..M, ψ t :=
          mul_le_mul_of_nonneg_left (integral_comp_sub_le hab x.2 hMba hψnn (hψii _ _)) hC
      _ ≤ C * (2 * s ^ (1 - γ) / (1 - γ)) := mul_le_mul_of_nonneg_left hkey hC
      _ ≤ ε := by
          rw [hspow]
          have h : C * (2 * (ε * (1 - γ) / (2 * C + 1)) / (1 - γ)) = 2 * C * ε / (2 * C + 1) := by
            field_simp
          rw [h, div_le_iff₀ (by positivity)]
          nlinarith [hε.le, hC]

/-- **The kernel `|x − y| ^ (-γ)` with `0 < γ < 1` is admissible on `C[a, b]`**, which is the
kernel (2.8.14) of [han2009theoretical], Example 2.8.9. The book obtains the compactness of its
operator from the truncations (2.8.15) and Proposition 2.8.7; the route here is the same
truncation, taken inside the (A₁)–(A₂) framework so that the operator itself is the one of
§2.8.1. -/
theorem isAdmissibleKernel_abs_sub_rpow (hab : a ≤ b) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsAdmissibleKernel (iccMeasure a b)
      (fun p : Icc a b × Icc a b => |(p.1 : ℝ) - (p.2 : ℝ)| ^ (-γ)) := by
  refine isAdmissibleKernel_of_abs_le_rpow hab hγ0 hγ1 zero_le_one ?_ fun p => ?_
  · refine ContinuousOn.rpow_const (by fun_prop) fun p hp => Or.inl ?_
    simpa [sub_eq_zero] using hp
  · rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]

/-- **The logarithmic kernel `log |cos x − cos y|` is admissible on `C[0, π]`**, which is
[han2009theoretical], Example 2.8.2. The book factors it as `|x − y| ^ (-1/2)` times a continuous
function and appeals to the splitting rule (2.8.9); the route here reads the same factorisation as
the bound `|log |cos x − cos y|| ≤ C |x − y| ^ (-1/2)`, which
`two_mul_sq_div_pi_sq_le_abs_cos_sub_cos` and `abs_log_le_two_mul_rpow` supply, and which needs no
separate continuity argument at the two ends of the diagonal.

Off the diagonal the kernel is continuous because `Real.injOn_cos` keeps `cos x − cos y` away from
`0`; on the diagonal both sides of the bound are `0`, since `Real.log 0 = 0`. -/
theorem isAdmissibleKernel_log_cos_sub_cos :
    IsAdmissibleKernel (iccMeasure 0 π)
      (fun p : Icc (0 : ℝ) π × Icc (0 : ℝ) π =>
        Real.log |Real.cos (p.1 : ℝ) - Real.cos (p.2 : ℝ)|) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi1 : (1 : ℝ) ≤ π := by linarith [Real.two_le_pi]
  set C : ℝ := (|Real.log 2| + 2 * |Real.log π|) * π + 4 * π + 4 with hCdef
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  refine isAdmissibleKernel_of_abs_le_rpow (γ := (1 : ℝ) / 2) hpi.le (by norm_num) (by norm_num)
    hCnn ?_ ?_
  · intro p hp
    have hne : Real.cos (p.1 : ℝ) - Real.cos (p.2 : ℝ) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun hc => hp (Real.injOn_cos p.1.2 p.2.2 hc)
    have hf : ContinuousAt (fun q : Icc (0 : ℝ) π × Icc (0 : ℝ) π =>
        |Real.cos (q.1 : ℝ) - Real.cos (q.2 : ℝ)|) p := (by fun_prop : Continuous _).continuousAt
    exact (hf.log (abs_ne_zero.2 hne)).continuousWithinAt
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    change abs (Real.log |Real.cos x - Real.cos y|) ≤ C * |x - y| ^ (-((1 : ℝ) / 2))
    rcases eq_or_lt_of_le (abs_nonneg (x - y)) with hu0 | hu0
    · have hxy : x = y := sub_eq_zero.mp (abs_eq_zero.mp hu0.symm)
      subst hxy
      simp [Real.zero_rpow]
    · set u : ℝ := |x - y| with hudef
      have hupi : u ≤ π := abs_le.2 ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
      have hlow : 2 * u ^ 2 / π ^ 2 ≤ |Real.cos x - Real.cos y| :=
        two_mul_sq_div_pi_sq_le_abs_cos_sub_cos hx hy
      have hhigh : |Real.cos x - Real.cos y| ≤ 2 := by
        rw [abs_le]
        constructor <;>
          linarith [Real.neg_one_le_cos x, Real.cos_le_one x, Real.neg_one_le_cos y,
            Real.cos_le_one y]
      have hlowpos : (0 : ℝ) < 2 * u ^ 2 / π ^ 2 := by positivity
      have hcpos : (0 : ℝ) < |Real.cos x - Real.cos y| := lt_of_lt_of_le hlowpos hlow
      have hexpand : Real.log (2 * u ^ 2 / π ^ 2)
          = Real.log 2 + 2 * Real.log u - 2 * Real.log π := by
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
        push_cast
        ring
      have hlog1 : Real.log |Real.cos x - Real.cos y| ≤ Real.log 2 := Real.log_le_log hcpos hhigh
      have hlog2 : Real.log 2 + 2 * Real.log u - 2 * Real.log π
          ≤ Real.log |Real.cos x - Real.cos y| := by
        rw [← hexpand]
        exact Real.log_le_log hlowpos hlow
      have hAbs : abs (Real.log |Real.cos x - Real.cos y|)
          ≤ |Real.log 2| + 2 * |Real.log u| + 2 * |Real.log π| := by
        rw [abs_le]
        constructor <;>
          linarith [le_abs_self (Real.log 2), neg_abs_le (Real.log 2), le_abs_self (Real.log u),
            neg_abs_le (Real.log u), le_abs_self (Real.log π), neg_abs_le (Real.log π)]
      have hnegpos : (0 : ℝ) < u ^ (-((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hu0 _
      have hprod : u * u ^ (-((1 : ℝ) / 2)) = u ^ ((1 : ℝ) / 2) := by
        nth_rewrite 1 [← Real.rpow_one u]
        rw [← Real.rpow_add hu0]
        norm_num
      have h1le : u ^ ((1 : ℝ) / 2) ≤ π * u ^ (-((1 : ℝ) / 2)) := by
        rw [← hprod]
        exact mul_le_mul_of_nonneg_right hupi hnegpos.le
      have hone_le : (1 : ℝ) ≤ π * u ^ (-((1 : ℝ) / 2)) := by
        have hhalf : u ^ ((1 : ℝ) / 2) * u ^ (-((1 : ℝ) / 2)) = 1 := by
          rw [← Real.rpow_add hu0]; norm_num
        have hspi : u ^ ((1 : ℝ) / 2) ≤ π :=
          calc u ^ ((1 : ℝ) / 2) ≤ π ^ ((1 : ℝ) / 2) :=
                Real.rpow_le_rpow hu0.le hupi (by norm_num)
            _ ≤ π ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hpi1 (by norm_num)
            _ = π := Real.rpow_one π
        calc (1 : ℝ) = u ^ ((1 : ℝ) / 2) * u ^ (-((1 : ℝ) / 2)) := hhalf.symm
          _ ≤ π * u ^ (-((1 : ℝ) / 2)) := mul_le_mul_of_nonneg_right hspi hnegpos.le
      have hE : (0 : ℝ) ≤ |Real.log 2| + 2 * |Real.log π| := by positivity
      have hE1 : |Real.log 2| + 2 * |Real.log π|
          ≤ (|Real.log 2| + 2 * |Real.log π|) * π * u ^ (-((1 : ℝ) / 2)) := by
        nlinarith [hE, hone_le, hnegpos]
      have hlu2 : |Real.log u|
          ≤ 2 * (π * u ^ (-((1 : ℝ) / 2)) + u ^ (-((1 : ℝ) / 2))) := by
        linarith [abs_log_le_two_mul_rpow hu0, h1le]
      rw [hCdef]
      nlinarith [hAbs, hE1, hlu2, hnegpos]

end AlgebraicSingularity

end IntegralOperator
