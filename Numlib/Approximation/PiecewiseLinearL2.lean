import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Numlib.Approximation.BestApprox
import Numlib.Approximation.Interpolation
import Numlib.IntegralEquations.Basic

/-!
# The `L²` projection onto the continuous piecewise linear functions

The continuous piecewise linear functions of a partition `a = x₀ < x₁ < ⋯ < x_{n+1} = b`, seen
inside `L²(a, b)`, form a finite-dimensional subspace, and the orthogonal projection onto it is the
**Galerkin projection** of the partition: the best `L²` approximation by piecewise linear
functions.  It is what a Galerkin method for an equation of the second kind discretizes with, and
it is cheaper to control than the interpolation projection of `Numlib/Approximation/Interpolation`,
because an orthogonal projection has norm one whatever the mesh.

Both facts a projection method asks for come from interpolation:

* the projection is at least as good as the interpolant, and a uniform bound is an `L²` bound
  (`IntegralOperator.norm_iccToLp_le`), so `‖f - P_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`;
* hence `P_n → 1` pointwise on the continuous functions, and, the projections having norm one and
  the continuous functions being dense in `L²`, on the whole of `L²(a, b)`.

## Main definitions

* `piecewiseLinearLp a b n x` — the trial space: the span, inside `L²(a, b)`, of the constant
  function and the clamped ramps `piecewiseLinearRamp` of the subintervals, which is the image of
  the range of `piecewiseLinearInterpCLM`.
* `piecewiseLinearProjCLM a b n x` — the orthogonal projection onto it.

## Main statements

* `isIdempotentElem_piecewiseLinearProjCLM` and `norm_piecewiseLinearProjCLM_le_one` — it is a
  projection of norm at most one.
* `norm_sub_piecewiseLinearProjCLM_le` — `‖f - P_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`, the
  approximation property, obtained from `isBestApprox_starProjection` and
  `iccToLp_piecewiseLinearInterpCLM_mem`.
* `tendsto_piecewiseLinearProjCLM` — for a sequence of partitions of vanishing mesh the projections
  converge pointwise to the identity on the whole of `L²(a, b)`.

## References

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009 ([han2009theoretical]), §12.2.3, equations (12.2.18) and
(12.2.19).
-/

open Filter MeasureTheory Topology

open IntegralOperator

variable {a b : ℝ}

/-- **The continuous piecewise linear functions of the partition, inside `L²(a, b)`.**  The span of
the images of the constant `1` and of the clamped ramps of the subintervals, which is exactly the
image under `iccToLp` of the range of `piecewiseLinearInterpCLM`. -/
noncomputable def piecewiseLinearLp (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :=
  Submodule.span ℝ (iccToLp a b '' insert (1 : C(Set.Icc a b, ℝ))
    ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n))

instance (n : ℕ) (x : ℕ → Set.Icc a b) : FiniteDimensional ℝ (piecewiseLinearLp a b n x) :=
  FiniteDimensional.span_of_finite ℝ
    ((((Set.finite_Iic n).image _).insert _).image _)

instance (n : ℕ) (x : ℕ → Set.Icc a b) : (piecewiseLinearLp a b n x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- **The `L²`-orthogonal projection onto the piecewise linear functions of the partition**: the
Galerkin projection of the partition, the `P_n` of [han2009theoretical], §12.2.3. -/
noncomputable def piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b) :=
  (piecewiseLinearLp a b n x).starProjection

/-- The Galerkin projection is a projection. -/
theorem isIdempotentElem_piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsIdempotentElem (piecewiseLinearProjCLM a b n x) :=
  Submodule.isIdempotentElem_starProjection _

/-- **An orthogonal projection has norm at most one**, which is where the Galerkin projection is
cheaper than the interpolation projection `piecewiseLinearInterpCLM`: no Lebesgue constant
enters. -/
theorem norm_piecewiseLinearProjCLM_le_one (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    ‖piecewiseLinearProjCLM a b n x‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- The image of a piecewise linear interpolant lies in the trial space. -/
theorem iccToLp_piecewiseLinearInterpCLM_mem (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    iccToLp a b (piecewiseLinearInterpCLM n x f) ∈ piecewiseLinearLp a b n x := by
  have hgen : ∀ z ∈ insert (1 : C(Set.Icc a b, ℝ))
      ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n),
      iccToLp a b z ∈ piecewiseLinearLp a b n x := fun z hz =>
    Submodule.subset_span ⟨z, hz, rfl⟩
  have hone : iccToLp a b (1 : C(Set.Icc a b, ℝ)) ∈ piecewiseLinearLp a b n x :=
    hgen _ (Set.mem_insert _ _)
  have hramp : ∀ i ∈ Finset.range (n + 1),
      iccToLp a b (piecewiseLinearRamp a b (x i) (x (i + 1))) ∈ piecewiseLinearLp a b n x := by
    intro i hi
    exact hgen _ (Set.mem_insert_of_mem _ ⟨i, Set.mem_Iic.2 (Nat.lt_succ_iff.1
      (Finset.mem_range.1 hi)), rfl⟩)
  have hval : piecewiseLinearInterpCLM n x f
      = f (x 0) • (1 : C(Set.Icc a b, ℝ)) + ∑ i ∈ Finset.range (n + 1),
        (((x (i + 1) : ℝ) - (x i : ℝ))⁻¹ * (f (x (i + 1)) - f (x i))) •
          piecewiseLinearRamp a b (x i) (x (i + 1)) := by
    simp [piecewiseLinearInterpCLM, mul_smul]
  rw [hval, map_add, map_smul, map_sum]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hone) (Submodule.sum_mem _ fun i hi => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hramp i hi)

/-- **The approximation property of the Galerkin projection**: the orthogonal projection is at
least as good as the interpolant, and a uniform bound is an `L²` bound, so

`‖f - P_n f‖_{L²} ≤ ‖f - I_n f‖_{L²} ≤ √(b - a) ‖f - I_n f‖_∞`.

Every uniform-norm bound on piecewise linear interpolation therefore becomes an `L²` bound on the
Galerkin projection, at the cost of one factor `√(b - a)`; [han2009theoretical], §12.2.3,
equation (12.2.18). -/
theorem norm_sub_piecewiseLinearProjCLM_le (hab : a ≤ b) (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    ‖iccToLp a b f - piecewiseLinearProjCLM a b n x (iccToLp a b f)‖
      ≤ √(b - a) * ‖f - piecewiseLinearInterpCLM n x f‖ := by
  have hbest := (isBestApprox_starProjection (piecewiseLinearLp a b n x)
      (iccToLp a b f)).2 _ (iccToLp_piecewiseLinearInterpCLM_mem n x f)
  refine hbest.trans ?_
  rw [← map_sub]
  exact norm_iccToLp_le hab _

/-- **The Galerkin projections of a sequence of partitions of vanishing mesh converge pointwise to
the identity on the whole of `L²(a, b)`**: they do so on the continuous functions by
`norm_sub_piecewiseLinearProjCLM_le` and the convergence of piecewise linear interpolation, they
have norm at most one, and the continuous functions are dense in `L²`.

This is the pointwise convergence that a projection method for an equation of the second kind
needs; [han2009theoretical], §12.2.3, the paragraph following equation (12.2.18). -/
theorem tendsto_piecewiseLinearProjCLM (hab : a ≤ b) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {h : ℕ → ℝ} (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => piecewiseLinearProjCLM a b (N n) (y n) u) atTop (𝓝 u) := by
  have hs0 : (0 : ℝ) ≤ √(b - a) := Real.sqrt_nonneg _
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- a continuous function close to `u` in `L²`
  obtain ⟨v, hv⟩ := Metric.denseRange_iff.1
    (ContinuousMap.toLp_denseRange (p := 2) ℝ (IntegralOperator.iccMeasure a b) ℝ (by simp))
    u (ε / 3) (by linarith)
  -- the interpolation error of that function tends to zero
  have hint : Tendsto (fun n => ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 v) :=
      tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh v
    have h2 : Tendsto (fun n => v - piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 (v - v)) :=
      tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    simpa using h2.norm
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hint) (ε / 3 / (√(b - a) + 1)) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  have hmid : √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ < ε / 3 := by
    have h1 := hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
    have hpos : (0 : ℝ) < √(b - a) + 1 := by positivity
    calc √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖
        ≤ (√(b - a) + 1) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ := by
          nlinarith [norm_nonneg (v - piecewiseLinearInterpCLM (N n) (y n) v)]
      _ < (√(b - a) + 1) * (ε / 3 / (√(b - a) + 1)) := mul_lt_mul_of_pos_left h1 hpos
      _ = ε / 3 := by field_simp
  -- the three-term estimate
  have hproj : ‖piecewiseLinearProjCLM a b (N n) (y n) u
      - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v)‖ ≤ ‖u - iccToLp a b v‖ := by
    rw [← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    nlinarith [norm_piecewiseLinearProjCLM_le_one a b (N n) (y n), norm_nonneg (u - iccToLp a b v),
      norm_nonneg (piecewiseLinearProjCLM a b (N n) (y n))]
  have hd1 : ‖u - iccToLp a b v‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hv
  have hd2 := norm_sub_piecewiseLinearProjCLM_le hab (N n) (y n) v
  rw [dist_eq_norm]
  have hsplit : piecewiseLinearProjCLM a b (N n) (y n) u - u
      = (piecewiseLinearProjCLM a b (N n) (y n) u
          - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))
        - (iccToLp a b v - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))
        - (u - iccToLp a b v) := by abel
  rw [hsplit]
  calc ‖(piecewiseLinearProjCLM a b (N n) (y n) u
          - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))
        - (iccToLp a b v - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))
        - (u - iccToLp a b v)‖
      ≤ ‖(piecewiseLinearProjCLM a b (N n) (y n) u
            - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))
          - (iccToLp a b v - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v))‖
        + ‖u - iccToLp a b v‖ := norm_sub_le _ _
    _ ≤ (‖piecewiseLinearProjCLM a b (N n) (y n) u
            - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v)‖
          + ‖iccToLp a b v - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b v)‖)
        + ‖u - iccToLp a b v‖ := by gcongr; exact norm_sub_le _ _
    _ < ε := by linarith
