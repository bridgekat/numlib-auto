import Numlib.Analysis.Calculus.SpaceTime
import Numlib.Analysis.PDE.Transport
import Numlib.Approximation.BrokenInterpolation
import Numlib.Variational.Evolution

/-!
# Error analysis of the space–time Galerkin methods for the transport equation

The convergence estimates of the continuous and discontinuous Galerkin semi-discretizations of
the transport equation `u_t + a u_x + a₀ u = f` on `(α, β) × (0, T)`
([quarteroni2000numerical] §13.10.1, quoted there from Quarteroni–Valli, *Numerical
Approximation of Partial Differential Equations*, §14.3, without proof), for an exact solution
whose regularity is taken as a hypothesis: `u(·, t) ∈ H^{r+1}(α, β)` and `∂ₜu(·, t) ∈ H^{r+1}(α, β)`
uniformly in `t ∈ [0, T]`.

The argument is the standard one. The **error equation** `IsSemidiscreteGalerkin.sub`: the
difference of the discrete solution `u_h` and any curve `W` differentiable in time solves the
semi-discrete problem again, with the consistency error `⟪∂ₜW, ·⟫ + b_t(W, ·) - F_t` as source and
`u_{0,h} - W(0)` as datum. With `W(t) = Π_h u(·, t)` the nodal interpolant of the exact solution
(`BrokenPolynomial.interp`, which commutes with `∂ₜ` because it is a linear map of the nodal values,
`hasDerivWithinAt_interp`), the source is the interpolation error of `∂ₜu` in `L²` and of `u` in
`H¹`, `O(h^r)` by the estimates of `Numlib/Approximation/BrokenInterpolation`; the stability
estimate `IsSemidiscreteGalerkin.norm_sq_add_integral_le` then bounds the discrete error, and the
triangle inequality finishes. The classical derivative `∂ₓu` of the solution is identified with
the weak derivative of its `H^{r+1}` representative by
`SobolevInterval.ae_eq_deriv_one_of_hasDerivAt`.
-/

open Set Filter Topology intervalIntegral Real MeasureTheory Polynomial TopologicalSpace
open scoped RealInnerProductSpace Interval

noncomputable section

namespace Variational

/-! ### The error equation of a semi-discrete Galerkin method -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **The error equation**: if `u` solves the semi-discrete Galerkin problem for the form `a`
and the source `F`, and `W` is any curve differentiable within `[0, T]` with derivative `W'`,
then `u - W` solves the semi-discrete problem with the source `F t - (⟪W' t, ·⟫ + a t (W t) ·)`
and the initial datum `u₀ - W 0`. With `W` an interpolant or projection of the exact solution
this is the equation for the discrete error `u_h - W`, whose source is the consistency error. -/
theorem IsSemidiscreteGalerkin.sub {a : ℝ → SesqForm ℝ K} {F : ℝ → K →L[ℝ] ℝ} {u₀ : K} {T : ℝ}
    {u : ℝ → K} (h : IsSemidiscreteGalerkin a F u₀ T u) {W W' : ℝ → K}
    (hW : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (W' t) (Icc 0 T) t) :
    IsSemidiscreteGalerkin a (fun t => F t - (innerSL ℝ (W' t) + a t (W t))) (u₀ - W 0) T
      (fun t => u t - W t) := by
  obtain ⟨h0, u', hu'⟩ := h
  refine ⟨by simp only [h0], fun t => u' t - W' t,
    fun t ht => ⟨(hu' t ht).1.sub (hW t ht), fun v => ?_⟩⟩
  have := (hu' t ht).2 v
  simp only [inner_sub_left, map_sub, sub_apply, add_apply, innerSL_apply_apply]
  linarith

/-! ### The time derivative of an interpolant -/

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)]
  {node : Fin n → Fin (r + 1) → ℝ}

/-- Interpolation from time-dependent nodal values is differentiable in time, with the
interpolant of the derivatives of the values as derivative: `ofValuesₗ` is a linear map on a
finite-dimensional space, hence continuous. -/
theorem hasDerivWithinAt_ofValuesₗ (hinj : ∀ i, Function.Injective (node i))
    {c : ℝ → Fin n → Fin (r + 1) → ℝ} {c' : Fin n → Fin (r + 1) → ℝ} {s : Set ℝ} {t : ℝ}
    (hc : ∀ i j, HasDerivWithinAt (fun t => c t i j) (c' i j) s t) :
    HasDerivWithinAt (fun t => BrokenPolynomial.ofValuesₗ x r node hinj (c t))
      (BrokenPolynomial.ofValuesₗ x r node hinj c') s t := by
  have hc' : HasDerivWithinAt c c' s t :=
    hasDerivWithinAt_pi.2 fun i => hasDerivWithinAt_pi.2 fun j => hc i j
  exact (LinearMap.toContinuousLinearMap
    (BrokenPolynomial.ofValuesₗ x r node hinj)).hasFDerivAt.comp_hasDerivWithinAt t hc'

/-- **The interpolant of a time-dependent function is differentiable in time**, with the
interpolant of the time derivative as derivative: if `∂ₜ u(y, t) = ut y t` within `[0, T]` at
every node `y`, then `d/dt Π_h u(·, t) = Π_h ut(·, t)`. -/
theorem hasDerivWithinAt_interp (hnode : BrokenPolynomial.IsNodes x r node) {u ut : ℝ → ℝ → ℝ}
    {T t : ℝ}
    (hu : ∀ y ∈ Icc (x 0) (x (Fin.last n)),
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t) :
    HasDerivWithinAt (fun t => BrokenPolynomial.interp hnode fun y => u y t)
      (BrokenPolynomial.interp hnode fun y => ut y t) (Icc 0 T) t :=
  hasDerivWithinAt_ofValuesₗ hnode.injective fun i j =>
    hu (node i j) (BrokenPolynomial.Icc_panel_subset hx.out.monotone i (hnode.mem i j))

end Variational

/-! ### The classical derivative of an `H¹` function is its weak derivative -/

open SobolevInterval in
/-- If a function `f` continuous on `[a, b]` represents `U ∈ H^{k+1}(a, b)` and has a derivative
`f'` at every point of `(a, b)`, then `f'` is the weak derivative `U'` almost everywhere on
`(a, b)`: `f = c + ∫_a^x U'` on `[a, b]` by the absolutely continuous representative, whose
derivative is `U'` almost everywhere by the Lebesgue differentiation theorem. -/
theorem SobolevInterval.ae_eq_deriv_one_of_hasDerivAt {a b : ℝ} (hab : a < b) {k : ℕ}
    (U : SobolevInterval (k + 1) a b) {f f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hU : fn U =ᵐ[volume.restrict (Ioo a b)] f) (hf' : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y) :
    f' =ᵐ[volume.restrict (Ioo a b)] SobolevInterval.deriv U 1 := by
  have hw : HasWeakDerivOn (fn U) (SobolevInterval.deriv U 1) (Opens.Ioo a b) := by
    have := hasWeakDerivOn_deriv_succ U 0
    rwa [Fin.castSucc_zero, deriv_zero, Fin.succ_zero_eq_one] at this
  have hint : IntegrableOn (SobolevInterval.deriv U 1) (Ioo a b) := integrableOn_deriv U 1
  obtain ⟨g, hg, hUg, hgint⟩ := hw.exists_continuousOn_ae_eq hab hint
  have hfg : EqOn f g (Icc a b) := eqOn_Icc_of_ae_eq hab hf hg (hU.symm.trans hUg)
  have hii : IntervalIntegrable (SobolevInterval.deriv U 1) volume a b :=
    hint.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hii.ae_hasDerivAt_integral] with y hy hyI
  have hyIcc : y ∈ Icc a b := Ioo_subset_Icc_self hyI
  have h1 : HasDerivAt (fun x => g a + ∫ t in a..x, SobolevInterval.deriv U 1 t)
      (SobolevInterval.deriv U 1 y) y :=
    (hy (uIcc_of_le hab.le ▸ hyIcc) a (uIcc_of_le hab.le ▸ left_mem_Icc.2 hab.le)).const_add _
  have hev : f =ᶠ[𝓝 y] fun x => g a + ∫ t in a..x, SobolevInterval.deriv U 1 t := by
    filter_upwards [Icc_mem_nhds hyI.1 hyI.2] with z hz
    rw [hfg hz, ← hgint a (left_mem_Icc.2 hab.le) z hz]
    ring
  exact (hf' y hyI).unique (h1.congr_of_eventuallyEq hev)

namespace Variational

open BrokenPolynomial

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a : ℝ → ℝ}

section FixedTime

variable {a₀ : ℝ → ℝ}

/-- **The consistency error of the transport form at a fixed time.** For the exact solution
`u` of `ut + a ux + a₀ u = f` (pointwise on `[x 0, x n]`), with `ux` almost everywhere equal to
a square integrable `g`, and any broken polynomials `W`, `W'` (the interpolants of `u` and `ut`),
the defect `⟪f, v⟫ - (⟪W', v⟫ + b(W, v))` of the pair `(W, W')` in the semi-discrete equation is
bounded by the three approximation errors: `‖ut - W'‖`, `‖g - W'‖` (weighted by `A ≥ |a|`) and
`‖u - W‖` (weighted by `A₀ ≥ |a₀|`), times `‖v‖`. -/
theorem abs_transport_defect_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hac : ContinuousOn a (Icc (x 0) (x (Fin.last n)))) {A A₀ : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A) (hA₀0 : 0 ≤ A₀)
    (hA₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s| ≤ A₀) {u ux ut f : ℝ → ℝ}
    (huc : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hutc : ContinuousOn ut (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ut y + a y * ux y + a₀ y * u y = f y)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (hux : ux =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] g) (W W' : BrokenPolynomial x r)
    {Eu Eu' Eg : ℝ}
    (hEu : √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (W i).eval s) ^ 2) ≤ Eu)
    (hEu' : √(∑ i, ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) ^ 2) ≤ Eu')
    (hEg : √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (derivative (W i)).eval s) ^ 2) ≤ Eg)
    (v : BrokenPolynomial x r) :
    |pairing f v - (⟪W', v⟫ + transportForm x r ha ha₀ W v)|
      ≤ (Eu' + A * Eg + A₀ * Eu) * ‖v‖ := by
  have hm : Monotone x := hx.out.monotone
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hab : x 0 ≤ x (Fin.last n) := hm (Fin.zero_le _)
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le hab).le
  -- `ux` is square integrable, being `g` almost everywhere
  have hae : ∀ i : Fin n, ux =ᵐ[volume.restrict (Ι (x i.castSucc) (x i.succ))] g := fun i => by
    rw [uIoc_of_le (hle i), Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hb : ∀ᵐ s : ℝ, s ≠ x i.succ := by simp [ae_iff, measure_singleton]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hux, hb] with s hs hsb hsI
    exact hs ⟨(hm (Fin.zero_le _)).trans_lt hsI.1, lt_of_le_of_ne (hsI.2.trans (hm (Fin.le_last _)))
      (fun h => hsb (le_antisymm hsI.2 (h ▸ hm (Fin.le_last _)) |>.symm ▸ rfl))⟩
  have hux_i : ∀ i : Fin n, IntervalIntegrable ux volume (x i.castSucc) (x i.succ) := fun i =>
    (intervalIntegrable_panel hm hg i).congr_ae (hae i).symm
  have hvc : ∀ i : Fin n, ContinuousOn (fun s => (v i).eval s) [[x i.castSucc, x i.succ]] :=
    fun i => (v i).continuous.continuousOn
  have hWc : ∀ (w : BrokenPolynomial x r) (i : Fin n),
      ContinuousOn (fun s => (w i).eval s) [[x i.castSucc, x i.succ]] :=
    fun w i => (w i).continuous.continuousOn
  have hW'c : ∀ (w : BrokenPolynomial x r) (i : Fin n),
      ContinuousOn (fun s => (derivative (w i)).eval s) [[x i.castSucc, x i.succ]] :=
    fun w i => (derivative (w i)).continuous.continuousOn
  -- the defect as a sum of three panel sums
  set S₁ := ∑ i, ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) * (v i).eval s with hS₁
  set S₂ := ∑ i, ∫ s in x i.castSucc..x i.succ,
    a s * (ux s - (derivative (W i)).eval s) * (v i).eval s with hS₂
  set S₃ := ∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * (u s - (W i).eval s) * (v i).eval s
    with hS₃
  have hD : pairing f v - (⟪W', v⟫ + transportForm x r ha ha₀ W v) = S₁ + S₂ + S₃ := by
    rw [pairing_def, ← sum_integral_eval_mul_eq_inner, transportForm_apply, hS₁, hS₂, hS₃,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have I1 : IntervalIntegrable (fun s => ut s * (v i).eval s) volume (x i.castSucc) (x i.succ) :=
      (hutc.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)
    have I2 : IntervalIntegrable (fun s => a s * ux s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((hux_i i).continuousOn_mul (hac.mono (hIcc i))).mul_continuousOn (hvc i)
    have I3 : IntervalIntegrable (fun s => a₀ s * u s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (huc.mono (hIcc i))).mul_continuousOn
        (hvc i)
    have I4 : IntervalIntegrable (fun s => (W' i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) := ((hWc W' i).mul (hvc i)).intervalIntegrable
    have I5 : IntervalIntegrable (fun s => a s * (derivative (W i)).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha i).mul_continuousOn (hW'c W i)).mul_continuousOn (hvc i)
    have I6 : IntervalIntegrable (fun s => a₀ s * (W i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (hWc W i)).mul_continuousOn (hvc i)
    have hf : ∫ s in x i.castSucc..x i.succ, f s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          + (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s := by
      rw [← integral_add I1 I2, ← integral_add (I1.add I2) I3]
      refine integral_congr fun s hs => ?_
      rw [← hpde s (hIcc i hs)]
      ring
    have e1 : ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, (W' i).eval s * (v i).eval s := by
      rw [← integral_sub I1 I4]
      exact integral_congr fun s _ => by ring
    have e2 : ∫ s in x i.castSucc..x i.succ, a s * (ux s - (derivative (W i)).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s := by
      rw [← integral_sub I2 I5]
      exact integral_congr fun s _ => by ring
    have e3 : ∫ s in x i.castSucc..x i.succ, a₀ s * (u s - (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_sub I3 I6]
      exact integral_congr fun s _ => by ring
    have e4 : ∫ s in x i.castSucc..x i.succ,
        (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_add I5 I6]
      exact integral_congr fun s _ => by ring
    rw [hf, e1, e2, e3, e4]
    ring
  -- the three bounds
  have hS₁' : |S₁| ≤ Eu' * ‖v‖ := by
    refine (abs_sum_integral_mul_eval_le (η := fun i s => ut s - (W' i).eval s)
      (fun i => ((hutc.mono (hIcc i)).sub (hWc W' i)).intervalIntegrable)
      (fun i => (((hutc.mono (hIcc i)).sub (hWc W' i)).pow 2).intervalIntegrable) v).trans ?_
    exact mul_le_mul_of_nonneg_right hEu' (norm_nonneg _)
  have hS₂' : |S₂| ≤ A * Eg * ‖v‖ := by
    have e : S₂ = ∑ i, ∫ s in x i.castSucc..x i.succ,
        a s * (g s - (derivative (W i)).eval s) * (v i).eval s := by
      rw [hS₂]
      refine Finset.sum_congr rfl fun i _ => integral_congr_ae_restrict ?_
      filter_upwards [hae i] with s hs
      rw [hs]
    rw [e]
    refine (abs_sum_integral_mul_mul_eval_le ha hA0 hA
      (η := fun i s => g s - (derivative (W i)).eval s)
      (fun i => (intervalIntegrable_panel hm hg i).sub (hW'c W i).intervalIntegrable)
      (fun i => intervalIntegrable_sub_sq (intervalIntegrable_panel hm hg i)
        (intervalIntegrable_panel hm hg2 i) (hW'c W i)) v).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEg hA0) (norm_nonneg _)
  have hS₃' : |S₃| ≤ A₀ * Eu * ‖v‖ := by
    refine (abs_sum_integral_mul_mul_eval_le ha₀ hA₀0 hA₀ (η := fun i s => u s - (W i).eval s)
      (fun i => ((huc.mono (hIcc i)).sub (hWc W i)).intervalIntegrable)
      (fun i => (((huc.mono (hIcc i)).sub (hWc W i)).pow 2).intervalIntegrable) v).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA₀0) (norm_nonneg _)
  rw [hD]
  calc |S₁ + S₂ + S₃| ≤ |S₁| + |S₂| + |S₃| := abs_add_three _ _ _
    _ ≤ Eu' * ‖v‖ + A * Eg * ‖v‖ + A₀ * Eu * ‖v‖ := by linarith
    _ = (Eu' + A * Eg + A₀ * Eu) * ‖v‖ := by ring

end FixedTime

section TimeDependent

variable {a₀ : ℝ → ℝ → ℝ}

/-- `E + √B ≤ √2 √(E² + B)` for `E, B ≥ 0`. -/
private theorem add_sqrt_le_sqrt_two_mul_sqrt {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B) :
    E + √B ≤ √2 * √(E ^ 2 + B) := by
  have hsq : (E + √B) ^ 2 ≤ (√2 * √(E ^ 2 + B)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (add_nonneg (sq_nonneg E) hB), add_sq,
      Real.sq_sqrt hB]
    nlinarith [sq_nonneg (E - √B), Real.sq_sqrt hB]
  exact (pow_le_pow_iff_left₀ (add_nonneg hE (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) two_ne_zero).1 hsq

/-- `√(e² + c) ≤ e + d` for `e, d ≥ 0` and `c ≤ d²`. -/
private theorem sqrt_sq_add_le {e c d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) (hcd : c ≤ d ^ 2) :
    √(e ^ 2 + c) ≤ e + d := by
  calc √(e ^ 2 + c) ≤ √((e + d) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg he hd])
    _ = e + d := Real.sqrt_sq (add_nonneg he hd)

/-- `μ⁻¹ (t Φ²) ≤ (T/μ) Φ²` for `t ≤ T`, `μ > 0`. -/
private theorem inv_mul_le_div_mul {μ t T Φ : ℝ} (hμ : 0 < μ) (ht : t ≤ T) :
    μ⁻¹ * (t * Φ ^ 2) ≤ T / μ * Φ ^ 2 := by
  rw [div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (sq_nonneg Φ)) (inv_pos.2 hμ).le

/-- The final rearrangement: `P + s (X + P + Q) ≤ s (X + 2 P + Q)` for `s ≥ 1`, `P ≥ 0`. -/
private theorem add_mul_le_mul_add {s X P Q : ℝ} (hs : 1 ≤ s) (hP : 0 ≤ P) :
    P + s * (X + P + Q) ≤ s * (X + 2 * P + Q) := by nlinarith

/-- **The error estimate of the continuous Galerkin method for the transport equation**
([quarteroni2000numerical] §13.10.1, quoted there from Quarteroni–Valli §14.3.1 without proof;
here with explicit constants). Let `u` be a classical solution of `u_t + a u_x + a₀ u = f` on
`[x 0, x n] × [0, T]` with `u(x 0, t) = 0`, whose partial derivatives `ux`, `ut` exist within the
strip, with `ut(·, t)` continuous, and which is regular in the sense that
`u(·, t) ∈ H^{r+1}(x 0, x n)` with `|u(·, t)|_{H^{r+1}} ≤ M` and `ut(·, t) ∈ H^{r+1}(x 0, x n)` with
`|ut(·, t)|_{H^{r+1}} ≤ M'`
for every `t ∈ [0, T]`. Let `u_h : [0, T] → V` solve the semi-discrete Galerkin problem on the
space `V = V_h^{in}` of continuous broken polynomials of degree `r` vanishing at `x 0`, with a
discrete source `f_h(t)` that agrees with `f(·, t)` against `V` (its `L²` projection), on a
partition of mesh at most `h` carrying a Lagrange node system of degree `r`. Under the
dissipativity `0 < μ₀ ≤ a₀ - a'/2`, with `|a| ≤ A`, `|a₀| ≤ A₀` and `a(x n) ≥ 0`, for every
`t ∈ [0, T]`

`‖u(t) - u_h(t)‖_{L²} + (∫₀ᵗ a(x n) (u(x n, τ) - u_h(x n, τ))² dτ)^{1/2}
  ≤ √2 (‖u₀ - u_{0,h}‖_{L²} + h^r (2 h M + √(T/μ₀) (A M + h (M' + A₀ M))))`,

where the `L²` norms are panel sums. The proof is the error equation
`IsSemidiscreteGalerkin.sub` with the nodal interpolant `W(t) = Π_h u(·, t)` (which lies in
`V`, commutes with `∂ₜ` by `hasDerivWithinAt_interp`, and interpolates `u` at `x n`), whose
consistency error is bounded by `abs_transport_defect_le` and the interpolation estimates
(`h^{r+1} M'` for `ut`, `h^r M` for `ux`, `h^{r+1} M` for `u`), the dissipative energy estimate
`IsSemidiscreteGalerkin.norm_sq_add_integral_le` for the discrete error `u_h - W`, and the
triangle inequality. The book states the boundary term at the inflow end `α`, where it vanishes
identically since both `u` and `u_h` satisfy the inflow condition; the estimate holds at the
outflow end `β = x n`, which is where the energy identity produces it. -/
theorem cG_error_le (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hβ : 0 ≤ a (x (Fin.last n))) {A A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {u ux ut f : ℝ → ℝ → ℝ}
    (hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y)
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t)
    (hin : ∀ t ∈ Icc 0 T, u (x 0) t = 0) {M M' : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    (hreg' : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => ut y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M')
    {V : Submodule ℝ (BrokenPolynomial x r)}
    (hV : ∀ v, v ∈ V ↔ v ∈ continuous x r ∧ traceRight v ⟨0, hn⟩ = 0)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsLagrangeNodes x r node) {h : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v ∈ V, ⟪fh t, v⟫ = pairing (fun y => f y t) v)
    {u₀h : V} {uh : ℝ → V}
    (huh : IsSemidiscreteGalerkin (fun t => (transportForm x r ha (ha₀ t)).restrict V)
      (fun t => (innerSL ℝ (fh t)).comp V.subtypeL) u₀h T uh)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
          * (u (x (Fin.last n)) τ - traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2)
    ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hm (Fin.castSucc_lt_succ (i := ⟨0, hn⟩)).le)).trans (hmesh ⟨0, hn⟩)
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hM : 0 ≤ M := (apply_nonneg _ _).trans hU₀M
  obtain ⟨U₀', hU₀', hU₀M'⟩ := hreg' 0 hT0
  have hM' : 0 ≤ M' := (apply_nonneg _ _).trans hU₀M'
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have hA₀0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ 0 hT0 (x 0) (left_mem_Icc.2 hab.le))
  have hac : ContinuousOn a (Icc (x 0) (x (Fin.last n))) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))) :=
    fun t ht y hy => (hux y hy t ht).continuousWithinAt
  have hsub : [[(0 : ℝ), t]] ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  -- the interpolation errors, as bounds on square roots
  have hsqrt : ∀ (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) (K : ℝ) (k : ℕ) (X : ℝ),
      X ≤ h ^ (2 * k) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 →
      SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ K → √X ≤ h ^ k * K := by
    intro U K k X hX hUK
    calc √X ≤ √(h ^ (2 * k) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2) :=
          Real.sqrt_le_sqrt hX
      _ = h ^ k * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
          rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity),
            Real.sqrt_sq (apply_nonneg _ _)]
      _ ≤ h ^ k * K := mul_le_mul_of_nonneg_left hUK (by positivity)
  -- the interpolants
  set W : ℝ → BrokenPolynomial x r := fun t => interp hnode.toIsNodes fun y => u y t with hW
  set W' : ℝ → BrokenPolynomial x r := fun t => interp hnode.toIsNodes fun y => ut y t with hW'
  have hWV : ∀ t ∈ Icc 0 T, W t ∈ V := fun t ht => (hV _).2
    ⟨interp_mem_continuous hnode _, by rw [traceRight_interp_zero hnode hn, hin t ht]⟩
  have hut0 : ∀ t ∈ Icc 0 T, ut (x 0) t = 0 := fun t ht => by
    have h1 := hut (x 0) (left_mem_Icc.2 hab.le) t ht
    have h2 : HasDerivWithinAt (fun t => u (x 0) t) 0 (Icc 0 T) t :=
      (hasDerivWithinAt_const t _ (0 : ℝ)).congr (fun s hs => hin s hs) (hin t ht)
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h2
  have hW'V : ∀ t ∈ Icc 0 T, W' t ∈ V := fun t ht => (hV _).2
    ⟨interp_mem_continuous hnode _, by rw [traceRight_interp_zero hnode hn, hut0 t ht]⟩
  -- the interpolants as curves in `V`, clamped to `[0, T]`
  set clamp : ℝ → ℝ := fun t => max 0 (min t T) with hclamp
  have hclampmem : ∀ t, clamp t ∈ Icc 0 T := fun t =>
    ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampeq : ∀ t ∈ Icc 0 T, clamp t = t := fun t ht => by
    simp only [hclamp]; rw [min_eq_left ht.2, max_eq_right ht.1]
  set Wv : ℝ → V := fun t => ⟨W (clamp t), hWV _ (hclampmem t)⟩ with hWv
  set Wv' : ℝ → V := fun t => ⟨W' (clamp t), hW'V _ (hclampmem t)⟩ with hWv'
  have hWvd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Wv (Wv' t) (Icc 0 T) t := fun t ht => by
    have h1 : HasDerivWithinAt W (W' t) (Icc 0 T) t :=
      hasDerivWithinAt_interp hnode.toIsNodes fun y hy => hut y hy t ht
    have h2 : HasDerivWithinAt (fun s => W (clamp s)) (W' t) (Icc 0 T) t :=
      h1.congr (fun s hs => by simp only [hclampeq s hs]) (by simp only [hclampeq t ht])
    have h3 := h2.codRestrict_submodule V (fun s => hWV (clamp s) (hclampmem s)) (hW'V t ht)
    have e : Wv' t = ⟨W' t, hW'V t ht⟩ := Subtype.ext (by simp only [hWv', hclampeq t ht])
    rw [e]
    exact h3
  -- the error equation
  have he := huh.sub hWvd
  -- the consistency error
  set Φ := h ^ (r + 1) * M' + A * (h ^ r * M) + A₀ * (h ^ (r + 1) * M) with hΦ
  have hΦ0 : 0 ≤ Φ := by positivity
  have hG : ∀ s ∈ Icc 0 T, ‖(innerSL ℝ (fh s)).comp V.subtypeL
      - (innerSL ℝ (Wv' s) + ((transportForm x r ha (ha₀ s)).restrict V) (Wv s))‖ ≤ Φ := by
    intro s hs
    refine ContinuousLinearMap.opNorm_le_bound _ hΦ0 fun v => ?_
    obtain ⟨U, hU, hUM⟩ := hreg s hs
    obtain ⟨U', hU', hUM'⟩ := hreg' s hs
    have hg := SobolevInterval.intervalIntegrable_deriv hab.le U 1
    have hg2 := SobolevInterval.intervalIntegrable_deriv_sq hab.le U 1
    have hux_ae : (fun y => ux y s) =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))]
        SobolevInterval.deriv U 1 :=
      SobolevInterval.ae_eq_deriv_one_of_hasDerivAt hab U (huc s hs) hU fun y hy =>
        (hux y (Ioo_subset_Icc_self hy) s hs).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have hEu := hsqrt U M (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc s hs) hU) hUM
    have hEu' := hsqrt U' M' (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U' (hutc s hs) hU')
      hUM'
    have hEg := hsqrt U M r _
      (sum_integral_sq_deriv_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc s hs) hU)
      hUM
    have key := abs_transport_defect_le ha (ha₀ s) hac hA0 hA hA₀0 (hA₀ s hs) (huc s hs)
      (hutc s hs) (fun y hy => hpde y hy s hs) hg hg2 hux_ae (W s) (W' s) hEu hEu' hEg
      (v : BrokenPolynomial x r)
    have e : ((innerSL ℝ (fh s)).comp V.subtypeL
        - (innerSL ℝ (Wv' s) + ((transportForm x r ha (ha₀ s)).restrict V) (Wv s))) v
        = pairing (fun y => f y s) (v : BrokenPolynomial x r)
          - (⟪W' s, (v : BrokenPolynomial x r)⟫ + transportForm x r ha (ha₀ s) (W s) v) := by
      simp only [_root_.sub_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, innerSL_apply_apply, SesqForm.restrict_apply, Submodule.coe_inner,
        hWv, hWv', hclampeq s hs]
      rw [hfh s hs v v.2]
    rw [e, Real.norm_eq_abs]
    exact key
  -- the energy estimate for the discrete error
  have hQc : ContinuousOn (fun s => a (x (Fin.last n))
      * traceLeft ((uh s - Wv s : V) : BrokenPolynomial x r) (Fin.last n) ^ 2) (Icc 0 T) := by
    have hc : Continuous fun v : V => traceLeft (v : BrokenPolynomial x r) (Fin.last n) :=
      (continuous_traceLeft (Fin.last n)).comp continuous_subtype_val
    exact continuousOn_const.mul ((hc.comp_continuousOn he.continuousOn).pow 2)
  have hcoer : ∀ s ∈ Icc 0 T, ∀ v : V, μ₀ * ‖v‖ ^ 2
      + a (x (Fin.last n)) * traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      ≤ (transportForm x r ha (ha₀ s)).restrict V v v := fun s hs v =>
    le_transportForm_restrict ha (ha₀ s) hd hd' hn (hμ₀ s hs) (fun v hv => (hV v).1 hv) v
  have hstab := he.norm_sq_add_integral_le
    (Q := fun _ v => a (x (Fin.last n)) * traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2)
    hμ hQc hcoer (φ := fun _ => Φ) continuousOn_const (fun s hs => hG s hs) ht
  -- the algebra
  set E := ‖uh t - Wv t‖ with hE
  set e0 := ‖u₀h - Wv 0‖ with he0
  set B := ∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
    * traceLeft ((uh τ - Wv τ : V) : BrokenPolynomial x r) (Fin.last n) ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg ht.1 fun s _ => mul_nonneg hβ (sq_nonneg _)
  have hI : B ≤ ∫ τ in (0 : ℝ)..t, (μ₀ * ‖uh τ - Wv τ‖ ^ 2 + a (x (Fin.last n))
      * traceLeft ((uh τ - Wv τ : V) : BrokenPolynomial x r) (Fin.last n) ^ 2) := by
    refine integral_mono_on ht.1 ((hQc.mono hsub).intervalIntegrable) ?_ fun τ _ => ?_
    · exact ((continuousOn_const.mul (he.continuousOn_norm_sq.mono hsub)).add
        (hQc.mono hsub)).intervalIntegrable
    · exact le_add_of_nonneg_left (mul_nonneg hμ.le (sq_nonneg _))
  have hΦint : ∫ τ in (0 : ℝ)..t, Φ ^ 2 = t * Φ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [hΦint] at hstab
  have hmain : E ^ 2 + B ≤ e0 ^ 2 + μ₀⁻¹ * (t * Φ ^ 2) := (add_le_add_right hI _).trans hstab
  have h1 : E + √B ≤ √2 * √(E ^ 2 + B) := add_sqrt_le_sqrt_two_mul_sqrt (norm_nonneg _) hB0
  have h2 : √(E ^ 2 + B) ≤ e0 + √(T / μ₀) * Φ := by
    refine (Real.sqrt_le_sqrt hmain).trans (sqrt_sq_add_le (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hΦ0) ?_)
    rw [mul_pow, Real.sq_sqrt (div_nonneg hT.le hμ.le)]
    exact inv_mul_le_div_mul hμ ht.2
  -- the initial error
  have hg0 : IntervalIntegrable (fun s => u s 0) volume (x 0) (x (Fin.last n)) :=
    ((huc 0 hT0).mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hg02 : IntervalIntegrable (fun s => u s 0 ^ 2) volume (x 0) (x (Fin.last n)) :=
    (((huc 0 hT0).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
  have hEu0 := hsqrt U₀ M (r + 1) _
    (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U₀ (huc 0 hT0) hU₀) hU₀M
  have he0' : e0 ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ,
      (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2) + h ^ (r + 1) * M := by
    have hW0 : ((u₀h - Wv 0 : V) : BrokenPolynomial x r) = (u₀h : BrokenPolynomial x r) - W 0 := by
      simp only [Submodule.coe_sub, hWv, hclampeq 0 hT0]
    have := norm_sub_le_sqrt_add_sqrt hg0 hg02 (u₀h : BrokenPolynomial x r) (W 0)
    rw [he0, ← Submodule.norm_coe, hW0]
    linarith
  -- the error at time `t`
  have hEt : √(∑ i, ∫ s in x i.castSucc..x i.succ,
      (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2) ≤ h ^ (r + 1) * M + E := by
    obtain ⟨U, hU, hUM⟩ := hreg t ht
    have hgt : IntervalIntegrable (fun s => u s t) volume (x 0) (x (Fin.last n)) :=
      ((huc t ht).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hgt2 : IntervalIntegrable (fun s => u s t ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc t ht).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have hEu := hsqrt U M (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc t ht) hU) hUM
    have htri := sqrt_sum_integral_sub_sq_le hgt hgt2 (uh t : BrokenPolynomial x r) (W t)
    have hWt : ‖W t - (uh t : BrokenPolynomial x r)‖ = E := by
      rw [hE, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
      simp only [hWv, hclampeq t ht]
    linarith
  -- the boundary term
  have hbd : ∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
      * (u (x (Fin.last n)) τ - traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2 = B := by
    refine integral_congr fun τ hτ => ?_
    have hτ' : τ ∈ Icc 0 T := hsub hτ
    simp only [Submodule.coe_sub, hWv, hclampeq τ hτ']
    rw [traceLeft_sub, traceLeft_interp_last hnode hn]
    ring
  -- assemble
  rw [hbd]
  have hs2 : 1 ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hΦeq : Φ = h ^ r * (A * M + h * (M' + A₀ * M)) := by rw [hΦ, pow_succ]; ring
  have hpow : h ^ (r + 1) = h ^ r * h := pow_succ h r
  have hsq2 : 0 ≤ √2 := Real.sqrt_nonneg 2
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2) + √B
      ≤ h ^ (r + 1) * M + E + √B := add_le_add hEt le_rfl
    _ ≤ h ^ (r + 1) * M + √2 * √(E ^ 2 + B) := by linarith
    _ ≤ h ^ (r + 1) * M + √2 * (e0 + √(T / μ₀) * Φ) := by gcongr
    _ ≤ h ^ (r + 1) * M + √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2) + h ^ (r + 1) * M
          + √(T / μ₀) * Φ) := by gcongr
    _ ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
        rw [hΦeq, hpow]
        have e : √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
            (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
            + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M))))
            = √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
            (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
            + 2 * (h ^ r * h * M) + √(T / μ₀) * (h ^ r * (A * M + h * (M' + A₀ * M)))) := by
          ring
        rw [e]
        exact add_mul_le_mul_add hs2 (mul_nonneg (mul_nonneg (pow_nonneg hh r) hh) hM)

end TimeDependent

/-! ### The `L²` projection of a time-dependent function commutes with `∂ₜ` -/

/-- A panel integral of a function continuous on the strip `[x 0, x n] × [0, T]` against a
polynomial is continuous in time (dominated convergence). -/
theorem continuousOn_integral_panel_mul {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (i : Fin n) (q : ℝ[X]) :
    ContinuousOn (fun t => ∫ y in x i.castSucc..x i.succ, g y t * q.eval y) (Icc 0 T) := by
  have hm : Monotone x := hx.out.monotone
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hg
  intro t₀ ht₀
  have hle : x i.castSucc ≤ x i.succ := hm (Fin.castSucc_lt_succ (i := i)).le
  have hmemI : ∀ y ∈ Ι (x i.castSucc) (x i.succ), y ∈ Icc (x 0) (x (Fin.last n)) := fun y hy =>
    Icc_panel_subset hm i (by rw [uIoc_of_le hle] at hy; exact Ioc_subset_Icc_self hy)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun y => B * |q.eval y|) ?_ ?_ ?_ ?_
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine ContinuousOn.mul ?_ q.continuous.continuousOn
    intro y hy
    have := hg (y, t) ⟨hmemI y hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const)
      fun z hz => Set.mk_mem_prod (hmemI z hz) ht
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hB (y, t) ⟨hmemI y hy, ht⟩) (abs_nonneg _)
  · exact (q.continuous.abs.intervalIntegrable _ _).const_mul B
  · refine Filter.Eventually.of_forall fun y hy => ?_
    have := hg (y, t₀) ⟨hmemI y hy, ht₀⟩
    exact (ContinuousWithinAt.comp (f := fun z : ℝ => (y, z)) this
      (continuousWithinAt_const.prodMk continuousWithinAt_id)
      fun z hz => Set.mk_mem_prod (hmemI y hy) hz).mul continuousWithinAt_const

/-- The pairing of a function continuous on the strip `[x 0, x n] × [0, T]` with a fixed broken
polynomial is continuous in time. -/
theorem continuousOn_pairing {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (v : BrokenPolynomial x r) :
    ContinuousOn (fun t => pairing (fun y => g y t) v) (Icc 0 T) := by
  simp only [pairing_def]
  exact continuousOn_finsetSum _ fun i _ => continuousOn_integral_panel_mul hg i (v i)

/-- The projection of a function continuous on the strip is continuous in time: it is the sum of
its pairings with an orthonormal basis. -/
theorem continuousOn_proj (hn : 0 < n) {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T)) :
    ContinuousOn (fun t => proj x r fun y => g y t) (Icc 0 T) := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  set b := stdOrthonormalBasis ℝ (BrokenPolynomial x r) with hb
  have hexp : ∀ t ∈ Icc 0 T, (proj x r fun y => g y t)
      = ∑ k, pairing (fun y => g y t) (b k) • b k := by
    intro t ht
    have hgt : IntervalIntegrable (fun y => g y t) volume (x 0) (x (Fin.last n)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab.le]
      intro y hy
      have := hg (y, t) ⟨hy, ht⟩
      exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
        (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
    conv_lhs => rw [← b.sum_repr (proj x r fun y => g y t)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, inner_proj hgt]
  refine ContinuousOn.congr ?_ hexp
  exact continuousOn_finsetSum _ fun k _ => (continuousOn_pairing hg (b k)).smul continuousOn_const

/-- **The fundamental theorem of calculus for the pairing**: if `∂ₜ u = ut` within `[0, T]` with
`ut` continuous on the strip, then for `τ ∈ [0, T]` and every broken polynomial `v`,
`⟪u(·, τ), v⟫ - ⟪u(·, 0), v⟫ = ∫₀^τ ⟪ut(·, s), v⟫ ds`. The fundamental theorem of calculus in `t`
for each `y`, then Fubini on each panel. -/
theorem pairing_sub_eq_integral {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) (v : BrokenPolynomial x r) :
    pairing (fun y => u y τ) v - pairing (fun y => u y 0) v
      = ∫ s in (0 : ℝ)..τ, pairing (fun y => ut y s) v := by
  have hm : Monotone x := hx.out.monotone
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  -- the fundamental theorem of calculus in time, for each `y`
  have hftc : ∀ y ∈ Icc (x 0) (x (Fin.last n)),
      u y τ - u y 0 = ∫ s in (0 : ℝ)..τ, ut y s := by
    intro y hy
    have hcont : ContinuousOn (fun t => u y t) (Icc 0 τ) := fun t ht =>
      (hut y hy t (Icc_subset_Icc le_rfl hτ.2 ht)).continuousWithinAt.mono
        (Icc_subset_Icc le_rfl hτ.2)
    have hderiv : ∀ s ∈ Ioo 0 τ, HasDerivWithinAt (fun t => u y t) (ut y s) (Ioi s) s := fun s hs =>
      (hut y hy s ⟨hs.1.le, hs.2.le.trans hτ.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT_of_mem ⟨hs.1.le, hs.2.trans_le hτ.2⟩)
    have hint : IntervalIntegrable (fun s => ut y s) volume 0 τ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hτ.1]
      intro s hs
      have := hutc (y, s) ⟨hy, Icc_subset_Icc le_rfl hτ.2 hs⟩
      exact ContinuousWithinAt.comp (f := fun z : ℝ => (y, z)) this
        (continuousWithinAt_const.prodMk continuousWithinAt_id)
        fun z hz => Set.mk_mem_prod hy (Icc_subset_Icc le_rfl hτ.2 hz)
    exact (integral_eq_sub_of_hasDeriv_right_of_le hτ.1 hcont hderiv hint).symm
  -- Fubini on each panel
  have hswap : ∀ i : Fin n, ∫ y in x i.castSucc..x i.succ,
      (∫ s in (0 : ℝ)..τ, ut y s) * (v i).eval y
      = ∫ s in (0 : ℝ)..τ, ∫ y in x i.castSucc..x i.succ, ut y s * (v i).eval y := by
    intro i
    have hle : x i.castSucc ≤ x i.succ := hm (Fin.castSucc_lt_succ (i := i)).le
    have hIcc : Ι (x i.castSucc) (x i.succ) ⊆ Icc (x 0) (x (Fin.last n)) := fun y hy =>
      Icc_panel_subset hm i (by rw [uIoc_of_le hle] at hy; exact Ioc_subset_Icc_self hy)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2 * (v i).eval p.1)
        (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T) :=
      hutc.mul ((v i).continuous.comp continuous_fst).continuousOn
    have hint : Integrable (Function.uncurry fun y s => ut y s * (v i).eval y)
        ((volume.restrict (Ι (x i.castSucc) (x i.succ))).prod (volume.restrict (Ioc 0 τ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      refine (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
      exact prod_mono hIcc (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ.2))
    have e1 : ∫ y in x i.castSucc..x i.succ, (∫ s in (0 : ℝ)..τ, ut y s) * (v i).eval y
        = ∫ y in x i.castSucc..x i.succ, ∫ s in Ioc 0 τ, ut y s * (v i).eval y := by
      refine integral_congr fun y _ => ?_
      rw [integral_of_le hτ.1, ← MeasureTheory.integral_mul_const]
    rw [e1, intervalIntegral_integral_swap hint, integral_of_le hτ.1]
  -- the panel integrals of `ut(·, s)` are integrable in `s`
  have hpint : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun s => ∫ y in x i.castSucc..x i.succ, ut y s * (v i).eval y) volume 0 τ := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ.1]
    exact (continuousOn_integral_panel_mul hutc i (v i)).mono (Icc_subset_Icc le_rfl hτ.2)
  simp only [pairing_def]
  rw [← Finset.sum_sub_distrib, intervalIntegral.integral_finsetSum hpint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hIcc : [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) :=
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le (hm (Fin.zero_le _))).le
  rw [← hswap i, ← integral_sub (((huc τ hτ).mono hIcc).intervalIntegrable.mul_continuousOn
    (v i).continuous.continuousOn) (((huc 0 hT0).mono hIcc).intervalIntegrable.mul_continuousOn
    (v i).continuous.continuousOn)]
  refine integral_congr fun y hy => ?_
  rw [← hftc y (hIcc hy)]
  ring

/-- **The projection of a time-dependent function is the integral of the projection of its time
derivative**: `P u(·, τ) = P u(·, 0) + ∫₀^τ P ut(·, s) ds` for `τ ∈ [0, T]`. -/
theorem proj_eq_add_integral (hn : 0 < n) {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    (proj x r fun y => u y τ)
      = (proj x r fun y => u y 0) + ∫ s in (0 : ℝ)..τ, proj x r fun y => ut y s := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have hPc : ContinuousOn (fun s => proj x r fun y => ut y s) (Icc 0 T) := continuousOn_proj hn hutc
  have hPint : IntervalIntegrable (fun s => proj x r fun y => ut y s) volume 0 τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ.1]
    exact hPc.mono (Icc_subset_Icc le_rfl hτ.2)
  have hui : ∀ t ∈ Icc 0 T, IntervalIntegrable (fun y => u y t) volume (x 0) (x (Fin.last n)) :=
    fun t ht => ((huc t ht).mono (uIcc_of_le hab.le).le).intervalIntegrable
  have huti : ∀ s ∈ Icc 0 T,
      IntervalIntegrable (fun y => ut y s) volume (x 0) (x (Fin.last n)) := by
    intro s hs
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    intro y hy
    have := hutc (y, s) ⟨hy, hs⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, s)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz hs
  rw [← sub_eq_iff_eq_add']
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_sub_left, inner_proj (hui τ hτ), inner_proj (hui 0 hT0),
    pairing_sub_eq_integral huc hut hutc hτ v, real_inner_comm, ← innerSL_apply_apply,
    ← (innerSL ℝ v).intervalIntegral_comp_comm hPint]
  refine integral_congr fun s hs => ?_
  rw [uIcc_of_le hτ.1] at hs
  simp only [innerSL_apply_apply]
  rw [real_inner_comm, inner_proj (huti s (Icc_subset_Icc le_rfl hτ.2 hs))]

/-- **The `L²` projection of a time-dependent function is differentiable in time**, with the
projection of the time derivative as derivative: if `∂ₜu = ut` within `[0, T]` at every point of
`[x 0, x n]`, `u(·, t)` is continuous and `ut` is continuous on the strip, then
`d/dt P u(·, t) = P ut(·, t)` within `[0, T]`. The fundamental theorem of calculus for
`P u(·, t) = P u(·, 0) + ∫₀ᵗ P ut(·, s) ds`, whose integrand is continuous. -/
theorem hasDerivWithinAt_proj (hn : 0 < n) {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => proj x r fun y => u y t) (proj x r fun y => ut y t) (Icc 0 T) t := by
  have hPc : ContinuousOn (fun s => proj x r fun y => ut y s) (Icc 0 T) := continuousOn_proj hn hutc
  have hPint : IntervalIntegrable (fun s => proj x r fun y => ut y s) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hPc.mono (Icc_subset_Icc le_rfl ht.2)
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have h1 : HasDerivWithinAt
      (fun τ => (proj x r fun y => u y 0) + ∫ s in (0 : ℝ)..τ, proj x r fun y => ut y s)
      (proj x r fun y => ut y t) (Icc 0 T) t :=
    (integral_hasDerivWithinAt_right hPint
      (hPc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hPc t ht)).const_add _
  exact h1.congr (fun τ hτ => proj_eq_add_integral hn huc hut hutc hτ)
    (proj_eq_add_integral hn huc hut hutc ht)

/-! ### The discontinuous Galerkin method -/

section DGFixedTime

variable {a₀ : ℝ → ℝ}

/-! ### The consistency error of the upwind discontinuous Galerkin form -/

/-- The boundary terms of the discontinuous Galerkin defect, reindexed: with `tl 0 = 0`,
`∑ᵢ c(xᵢ₊₁) e(xᵢ₊₁) tl(xᵢ₊₁) - ∑ᵢ c(xᵢ) e(xᵢ) tr(xᵢ) + c(x₀) e(x₀) tr(x₀)
  = c(xₙ) e(xₙ) tl(xₙ) - ∑_{i ≠ 0} c(xᵢ) e(xᵢ) (tr(xᵢ) - tl(xᵢ))`. -/
private theorem boundary_sum_eq (hn : 0 < n) {c e tl : Fin (n + 1) → ℝ} {tr : Fin n → ℝ}
    (htl : tl 0 = 0) :
    ∑ i : Fin n, c i.succ * e i.succ * tl i.succ - ∑ i : Fin n, c i.castSucc * e i.castSucc * tr i
      + c 0 * e 0 * tr ⟨0, hn⟩
      = c (Fin.last n) * e (Fin.last n) * tl (Fin.last n)
        - ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          c i.castSucc * e i.castSucc * (tr i - tl i.castSucc) := by
  have h1 := Fin.sum_univ_succ fun j : Fin (n + 1) => c j * e j * tl j
  have h2 := Fin.sum_univ_castSucc fun j : Fin (n + 1) => c j * e j * tl j
  rw [htl, mul_zero, zero_add] at h1
  have h3 : ∑ i : Fin n, c i.castSucc * e i.castSucc * (tr i - tl i.castSucc)
      = c 0 * e 0 * (tr ⟨0, hn⟩ - tl 0)
        + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          c i.castSucc * e i.castSucc * (tr i - tl i.castSucc) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    rfl
  rw [htl, sub_zero] at h3
  have h4 : ∑ i : Fin n, c i.castSucc * e i.castSucc * (tr i - tl i.castSucc)
      = ∑ i : Fin n, c i.castSucc * e i.castSucc * tr i
        - ∑ i : Fin n, c i.castSucc * e i.castSucc * tl i.castSucc := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- Reindexing of the node sums: `f(xₙ) + ∑_{i ≠ 0} f(xᵢ) = ∑ᵢ f(xᵢ₊₁)`. -/
private theorem node_sum_eq (hn : 0 < n) (f : Fin (n + 1) → ℝ) :
    f (Fin.last n) + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), f i.castSucc
      = ∑ i : Fin n, f i.succ := by
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  have h3 : ∑ i : Fin n, f i.castSucc
      = f 0 + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), f i.castSucc := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    rfl
  linarith

/-- `c e t ≤ c t²/4 + c e²` for `c ≥ 0`. -/
private theorem mul_mul_le_quarter {c e t : ℝ} (hc : 0 ≤ c) :
    c * e * t ≤ c * t ^ 2 / 4 + c * e ^ 2 := by
  nlinarith [mul_nonneg hc (sq_nonneg (t / 2 - e))]

/-- **The consistency error of the upwind discontinuous Galerkin form at a fixed time.** For the
exact solution `u` of `ut + a ux + a₀ u = f` on `[x 0, x n]` with inflow value `u(x 0) = φ`, the
pair `(W, W') = (P u, P ut)` of `L²` projections has the defect
`(⟪f, v⟫ + a(x 0) φ v⁺(x 0)) - (⟪W', v⟫ + b^{DG}(W, v))` bounded by
`(A₀ + A' + A' h (2 r (r + 1)/h_min)) ‖u - W‖ ‖v‖ + ¼ a(x n) v⁻(x n)² + ¼ ∑_{i ≠ 0} a(xᵢ) [v]ᵢ²
+ ∑ᵢ a(xᵢ₊₁) (u - W)⁻(xᵢ₊₁)²`, where `|a₀| ≤ A₀`, `|a'| ≤ A'`, the panels have lengths in
`[h_min, h]`, and `Eu` bounds the `L²` error `‖u - W‖`. Integration by parts on each panel moves
the derivative from `u - W` onto `a v`, the orthogonality of the projection error to `a(xᵢ) vᵢ'`
leaves `(a - a(xᵢ)) vᵢ'`, bounded through the Lipschitz constant of `a` and the Markov
inequality for `v`, and the boundary terms telescope into the traces of the projection error at
the nodes, absorbed by the jump and outflow terms with the weights `¼`. -/
theorem dg_defect_le (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A' A₀ : ℝ} (hA'0 : 0 ≤ A')
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A') (hA₀0 : 0 ≤ A₀)
    (hA₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s| ≤ A₀) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) {u ux ut f : ℝ → ℝ} {φ : ℝ}
    (huc : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hux : ∀ y ∈ Ioo (x 0) (x (Fin.last n)), HasDerivAt u (ux y) y)
    (hutc : ContinuousOn ut (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ut y + a y * ux y + a₀ y * u y = f y)
    (hφ : u (x 0) = φ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hux_ae : ux =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] g) {Eu : ℝ}
    (hEu : √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (proj x r u i).eval s) ^ 2) ≤ Eu)
    (v : BrokenPolynomial x r) :
    (pairing f v + a (x 0) * φ * traceRight v ⟨0, hn⟩)
        - (⟪proj x r ut, v⟫ + dgUpwindForm x r ha ha₀ (proj x r u) v)
      ≤ (A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * Eu * ‖v‖
        + a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 4
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump v i ^ 2 / 4)
        + ∑ i : Fin n, a (x i.succ) * (u (x i.succ) - (proj x r u i).eval (x i.succ)) ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hlt : ∀ i : Fin n, x i.castSucc < x i.succ := fun i => hx.out (Fin.castSucc_lt_succ (i := i))
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => (hlt i).le
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le hab.le).le
  have hIoo : ∀ i : Fin n, Ioo (x i.castSucc) (x i.succ) ⊆ Ioo (x 0) (x (Fin.last n)) := fun i =>
    Ioo_subset_Ioo (hm (Fin.zero_le _)) (hm (Fin.le_last _))
  have hac : ContinuousOn a (Icc (x 0) (x (Fin.last n))) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have hh : 0 ≤ h := (sub_nonneg.2 (hle ⟨0, hn⟩)).trans (hmesh ⟨0, hn⟩)
  have hEu0 : 0 ≤ Eu := (Real.sqrt_nonneg _).trans hEu
  -- `ux` is square integrable on every panel
  have hae : ∀ i : Fin n, ux =ᵐ[volume.restrict (Ι (x i.castSucc) (x i.succ))] g := fun i => by
    rw [uIoc_of_le (hle i), Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hb : ∀ᵐ s : ℝ, s ≠ x i.succ := by simp [ae_iff, measure_singleton]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hux_ae, hb] with s hs hsb hsI
    exact hs ⟨(hm (Fin.zero_le _)).trans_lt hsI.1, lt_of_le_of_ne (hsI.2.trans (hm (Fin.le_last _)))
      (fun h => hsb (le_antisymm hsI.2 (h ▸ hm (Fin.le_last _)) |>.symm ▸ rfl))⟩
  have hux_i : ∀ i : Fin n, IntervalIntegrable ux volume (x i.castSucc) (x i.succ) := fun i =>
    (intervalIntegrable_panel hm hg i).congr_ae (hae i).symm
  -- the Lipschitz bound of `a`
  have hLip : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ s' ∈ Icc (x 0) (x (Fin.last n)),
      |a s - a s'| ≤ A' * |s - s'| := fun s hs s' hs' => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := a) (f' := deriv a) (C := A') (s := Icc (x 0) (x (Fin.last n)))
      (fun y hy => (hd y hy).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by simpa [Real.norm_eq_abs] using hA' y hy) (convex_Icc _ _) hs' hs
    simpa [Real.norm_eq_abs] using this
  set W := proj x r u with hW
  set W' := proj x r ut with hW'
  set η : Fin n → ℝ → ℝ := fun i s => u s - (W i).eval s with hη
  have hηc : ∀ i, ContinuousOn (η i) [[x i.castSucc, x i.succ]] := fun i =>
    (huc.mono (hIcc i)).sub (W i).continuous.continuousOn
  have hηi : ∀ i, IntervalIntegrable (η i) volume (x i.castSucc) (x i.succ) := fun i =>
    (hηc i).intervalIntegrable
  have hηi2 : ∀ i, IntervalIntegrable (fun s => η i s ^ 2) volume (x i.castSucc) (x i.succ) :=
    fun i => ((hηc i).pow 2).intervalIntegrable
  have hvc : ∀ i : Fin n, ContinuousOn (fun s => (v i).eval s) [[x i.castSucc, x i.succ]] :=
    fun i => (v i).continuous.continuousOn
  -- the pairing of the exact source, and `⟪W', v⟫`
  have hui : IntervalIntegrable u volume (x 0) (x (Fin.last n)) :=
    (huc.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have huti : IntervalIntegrable ut volume (x 0) (x (Fin.last n)) :=
    (hutc.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hW'v : ⟪W', v⟫ = pairing ut v := inner_proj huti v
  -- integration by parts on each panel
  have hibp : ∀ i : Fin n, ∀ (w : ℝ → ℝ) (w' : ℝ → ℝ),
      ContinuousOn w [[x i.castSucc, x i.succ]] →
      (∀ s ∈ Ioo (x i.castSucc) (x i.succ), HasDerivAt w (w' s) s) →
      IntervalIntegrable w' volume (x i.castSucc) (x i.succ) →
      ∫ s in x i.castSucc..x i.succ, a s * w' s * (v i).eval s
        = a (x i.succ) * (v i).eval (x i.succ) * w (x i.succ)
          - a (x i.castSucc) * (v i).eval (x i.castSucc) * w (x i.castSucc)
          - ∫ s in x i.castSucc..x i.succ,
              (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * w s := by
    intro i w w' hw hw' hw'i
    have hU : ContinuousOn (fun s => a s * (v i).eval s) [[x i.castSucc, x i.succ]] :=
      (hac.mono (hIcc i)).mul (hvc i)
    have hUd : ∀ s ∈ Ioo (min (x i.castSucc) (x i.succ)) (max (x i.castSucc) (x i.succ)),
        HasDerivAt (fun s => a s * (v i).eval s)
          (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) s := by
      intro s hs
      rw [min_eq_left (hle i), max_eq_right (hle i)] at hs
      exact (hd s (hIcc i (Ioo_subset_Icc_self.trans (uIcc_of_le (hle i)).symm.subset hs)))
        |>.hasDerivAt.mul ((v i).hasDerivAt s)
    have hwd : ∀ s ∈ Ioo (min (x i.castSucc) (x i.succ)) (max (x i.castSucc) (x i.succ)),
        HasDerivAt w (w' s) s := by
      intro s hs
      rw [min_eq_left (hle i), max_eq_right (hle i)] at hs
      exact hw' s hs
    have hU' : IntervalIntegrable
        (fun s => deriv a s * (v i).eval s + a s * (derivative (v i)).eval s)
        volume (x i.castSucc) (x i.succ) :=
      ((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)
    have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hU hw hUd hwd hU' hw'i
    rw [← key]
    exact integral_congr fun s _ => by ring
  -- the traces of the projection error at the nodes
  set ηm : Fin (n + 1) → ℝ := fun j => u (x j) - traceLeft W j with hηm
  have hηm0 : ηm 0 = φ := by simp only [hηm, traceLeft_zero, sub_zero, hφ]
  have hηms : ∀ i : Fin n, ηm i.succ = η i (x i.succ) := fun i => by
    simp only [hηm, hη, traceLeft_succ]
  -- the per-panel decomposition of the defect
  have hpanel : ∀ i : Fin n,
      (∫ s in x i.castSucc..x i.succ, f s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ,
            (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s)
        - a (x i.castSucc) * jump W i * traceRight v i
      = ((∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s)
        + (a (x i.succ) * ηm i.succ * traceLeft v i.succ
          - a (x i.castSucc) * ηm i.castSucc * traceRight v i) := by
    intro i
    have I1 : IntervalIntegrable (fun s => ut s * (v i).eval s) volume (x i.castSucc) (x i.succ) :=
      (hutc.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)
    have I2 : IntervalIntegrable (fun s => a s * ux s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((hux_i i).continuousOn_mul (hac.mono (hIcc i))).mul_continuousOn (hvc i)
    have I3 : IntervalIntegrable (fun s => a₀ s * u s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (huc.mono (hIcc i))).mul_continuousOn
        (hvc i)
    have I5 : IntervalIntegrable (fun s => a s * (derivative (W i)).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha i).mul_continuousOn
        (derivative (W i)).continuous.continuousOn).mul_continuousOn (hvc i)
    have I6 : IntervalIntegrable (fun s => a₀ s * (W i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn
        (W i).continuous.continuousOn).mul_continuousOn (hvc i)
    have IU : IntervalIntegrable
        (fun s => (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * u s) volume
        (x i.castSucc) (x i.succ) :=
      (((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)).mul_continuousOn (huc.mono (hIcc i))
    have IW : IntervalIntegrable
        (fun s => (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * (W i).eval s)
        volume (x i.castSucc) (x i.succ) :=
      (((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)).mul_continuousOn
        (W i).continuous.continuousOn
    have hf : ∫ s in x i.castSucc..x i.succ, f s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          + (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s := by
      rw [← integral_add I1 I2, ← integral_add (I1.add I2) I3]
      refine integral_congr fun s hs => ?_
      rw [← hpde s (hIcc i hs)]
      ring
    have hu_ibp := hibp i u ux (huc.mono (hIcc i)) (fun s hs => hux s (hIoo i hs)) (hux_i i)
    have hW_ibp := hibp i (fun s => (W i).eval s) (fun s => (derivative (W i)).eval s)
      (W i).continuous.continuousOn (fun s _ => (W i).hasDerivAt s)
      ((derivative (W i)).continuous.intervalIntegrable _ _)
    have e4 : ∫ s in x i.castSucc..x i.succ,
        (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_add I5 I6]
      exact integral_congr fun s _ => by ring
    have e2 : ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_sub I3 I6]
      exact integral_congr fun s _ => by simp only [hη]; ring
    have e3 : (∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        + ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = (∫ s in x i.castSucc..x i.succ,
            (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * u s)
          - ∫ s in x i.castSucc..x i.succ,
            (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * (W i).eval s := by
      rw [← integral_sub IU IW, ← integral_add
        ((((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hηc i)).mul_continuousOn
          (hvc i)))
        (((intervalIntegrable_panel hm ha i).mul_continuousOn (hηc i)).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)]
      exact integral_congr fun s _ => by simp only [hη]; ring
    have etr : traceLeft W i.succ = (W i).eval (x i.succ) := traceLeft_succ W i
    have etr' : traceRight W i = (W i).eval (x i.castSucc) := traceRight_apply W i
    have ejump : jump W i = traceRight W i - traceLeft W i.castSucc := jump_apply W i
    have etl : traceLeft v i.succ = (v i).eval (x i.succ) := traceLeft_succ v i
    have etr'' : traceRight v i = (v i).eval (x i.castSucc) := traceRight_apply v i
    beta_reduce at hW_ibp
    rw [hf, e4, hu_ibp, hW_ibp, e2, ← sub_eq_zero]
    rw [← sub_eq_zero] at e3
    simp only [hηm, hη, etr, etr', ejump, etl, etr''] at e3 ⊢
    linear_combination e3
  -- the defect as the sum of the panel terms
  have hD : (pairing f v + a (x 0) * φ * traceRight v ⟨0, hn⟩)
        - (⟪W', v⟫ + dgUpwindForm x r ha ha₀ W v)
      = ((∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s)
          - ∑ i, ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        - (∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s)
        + (a (x (Fin.last n)) * ηm (Fin.last n) * traceLeft v (Fin.last n)
          - ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            a (x i.castSucc) * ηm i.castSucc * jump v i) := by
    have hbd := boundary_sum_eq hn (c := fun j => a (x j)) (e := ηm) (tl := traceLeft v)
      (tr := traceRight v) (traceLeft_zero v)
    simp only [hηm0, ← jump_apply] at hbd
    rw [hW'v, dgUpwindForm_apply, transportForm_apply, pairing_def, pairing_def, ← hbd]
    have := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpanel i
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
    linear_combination this
  rw [hD]
  -- the three volume terms
  have hS₂ : ∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s
      ≤ A₀ * Eu * ‖v‖ := by
    refine (le_abs_self _).trans ((abs_sum_integral_mul_mul_eval_le ha₀ hA₀0 hA₀ hηi hηi2 v).trans
      ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA₀0) (norm_nonneg _)
  have hS₃ : -∑ i, ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s
      ≤ A' * Eu * ‖v‖ := by
    refine (neg_le_abs _).trans ((abs_sum_integral_mul_mul_eval_le
      ((hd'.mono (uIcc_of_le hab.le).le).intervalIntegrable) hA'0 hA' hηi hηi2 v).trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA'0) (norm_nonneg _)
  have hS₄ : -∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
      ≤ A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by
    -- orthogonality: replace `a` by `a - a(xᵢ)`
    have horth : ∀ i : Fin n,
        -∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = ∫ s in x i.castSucc..x i.succ,
          (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s := by
      intro i
      have hq : (C (a (x i.castSucc)) * derivative (v i)).natDegree ≤ r :=
        (natDegree_C_mul_le _ _).trans ((natDegree_derivative_le _).trans
          (Nat.sub_le_of_le_add ((natDegree_le v i).trans (Nat.le_succ r))))
      have h0 := integral_sub_proj_mul_eq_zero hui i hq
      have hc : IntervalIntegrable (fun s => a s * η i s * (derivative (v i)).eval s) volume
          (x i.castSucc) (x i.succ) :=
        (((hac.mono (hIcc i)).mul (hηc i)).mul (derivative (v i)).continuous.continuousOn)
          |>.intervalIntegrable
      have hc' : IntervalIntegrable
          (fun s => (u s - (proj x r u i).eval s)
            * (C (a (x i.castSucc)) * derivative (v i)).eval s)
          volume (x i.castSucc) (x i.succ) :=
        ((hηc i).mul (C (a (x i.castSucc)) * derivative (v i)).continuous.continuousOn)
          |>.intervalIntegrable
      have e : ∫ s in x i.castSucc..x i.succ,
          (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s
          = (∫ s in x i.castSucc..x i.succ,
              (u s - (proj x r u i).eval s) * (C (a (x i.castSucc)) * derivative (v i)).eval s)
            - ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s := by
        rw [← integral_sub hc' hc]
        refine integral_congr fun s _ => ?_
        simp only [hη, eval_mul, eval_C]
        ring
      rw [e, h0, zero_sub]
    have hK : 0 ≤ 2 * r * (r + 1) / hmin := by positivity
    -- the panel bounds
    have hpan : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ,
        (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s
        ≤ (A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2))
          * (2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2)) := by
      intro i
      have hcη : ContinuousOn (fun s => (a (x i.castSucc) - a s) * η i s)
          [[x i.castSucc, x i.succ]] :=
        (continuousOn_const.sub (hac.mono (hIcc i))).mul (hηc i)
      have h1 := intervalIntegral.integral_mul_le_sqrt_mul_sqrt (hle i)
        (f := fun s => (a (x i.castSucc) - a s) * η i s) (g := fun s => (derivative (v i)).eval s)
        hcη.intervalIntegrable (hcη.pow 2).intervalIntegrable
        ((derivative (v i)).continuous.intervalIntegrable _ _)
        (((derivative (v i)).continuous.pow 2).intervalIntegrable _ _)
      have h2 : ∫ s in x i.castSucc..x i.succ, ((a (x i.castSucc) - a s) * η i s) ^ 2
          ≤ (A' * h) ^ 2 * ∫ s in x i.castSucc..x i.succ, η i s ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        refine integral_mono_on (hle i) (hcη.pow 2).intervalIntegrable ((hηi2 i).const_mul _)
          fun s hs => ?_
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |a (x i.castSucc) - a s| ≤ A' * |x i.castSucc - s| :=
              hLip _ (hIcc i (left_mem_uIcc)) s (hIcc i (uIcc_of_le (hle i) ▸ hs))
          _ ≤ A' * h := by
              refine mul_le_mul_of_nonneg_left ?_ hA'0
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.1)]
              linarith [hs.2, hmesh i]
      have h3 : ∫ s in x i.castSucc..x i.succ, (derivative (v i)).eval s ^ 2
          ≤ (2 * r * (r + 1) / hmin) ^ 2 * ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := by
        refine (integral_derivative_sq_le_panel (hlt i) (natDegree_le v i)).trans
          (mul_le_mul_of_nonneg_right ?_ (integral_nonneg (hle i) fun s _ => sq_nonneg _))
        refine pow_le_pow_left₀ (div_nonneg (by positivity) (sub_nonneg.2 (hle i))) ?_ 2
        exact div_le_div_of_nonneg_left (by positivity) h0 (hminle i)
      refine h1.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg hA'0 hh) (Real.sqrt_nonneg _)))
      · calc √(∫ s in x i.castSucc..x i.succ, ((a (x i.castSucc) - a s) * η i s) ^ 2)
            ≤ √((A' * h) ^ 2 * ∫ s in x i.castSucc..x i.succ, η i s ^ 2) := Real.sqrt_le_sqrt h2
          _ = A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      · calc √(∫ s in x i.castSucc..x i.succ, (derivative (v i)).eval s ^ 2)
            ≤ √((2 * r * (r + 1) / hmin) ^ 2 * ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) :=
              Real.sqrt_le_sqrt h3
          _ = 2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
    have hnn : ∀ i : Fin n, 0 ≤ ∫ s in x i.castSucc..x i.succ, η i s ^ 2 := fun i =>
      integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hnn' : ∀ i : Fin n, 0 ≤ ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := fun i =>
      integral_nonneg (hle i) fun _ _ => sq_nonneg _
    calc -∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = ∑ i, ∫ s in x i.castSucc..x i.succ,
            (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => horth i
      _ ≤ ∑ i, (A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2))
            * (2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2)) :=
          Finset.sum_le_sum fun i _ => hpan i
      _ = A' * h * (2 * r * (r + 1) / hmin) * ∑ i, √(∫ s in x i.castSucc..x i.succ, η i s ^ 2)
            * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ A' * h * (2 * r * (r + 1) / hmin)
            * (√(∑ i, √(∫ s in x i.castSucc..x i.succ, η i s ^ 2) ^ 2)
              * √(∑ i, √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
      _ = A' * h * (2 * r * (r + 1) / hmin)
            * (√(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖) := by
          simp only [Real.sq_sqrt (hnn _), Real.sq_sqrt (hnn' _)]
          rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by
          have := mul_le_mul_of_nonneg_right hEu (norm_nonneg v)
          have hc0 : 0 ≤ A' * h * (2 * r * (r + 1) / hmin) := by positivity
          calc A' * h * (2 * r * (r + 1) / hmin)
                * (√(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖)
              ≤ A' * h * (2 * r * (r + 1) / hmin) * (Eu * ‖v‖) :=
                mul_le_mul_of_nonneg_left this hc0
            _ = A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by ring
  -- the boundary terms
  have hB1 : a (x (Fin.last n)) * ηm (Fin.last n) * traceLeft v (Fin.last n)
      ≤ a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 4
        + a (x (Fin.last n)) * ηm (Fin.last n) ^ 2 :=
    mul_mul_le_quarter (hapos _ (right_mem_Icc.2 hab.le))
  have hB2 : -∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * ηm i.castSucc * jump v i
      ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        (a (x i.castSucc) * jump v i ^ 2 / 4 + a (x i.castSucc) * ηm i.castSucc ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_mul_le_quarter (c := a (x i.castSucc)) (e := ηm i.castSucc) (t := -jump v i)
      (hapos _ (hIcc i left_mem_uIcc))
    rw [neg_sq] at this
    linarith
  have htr : a (x (Fin.last n)) * ηm (Fin.last n) ^ 2
      + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * ηm i.castSucc ^ 2
      = ∑ i : Fin n, a (x i.succ) * (u (x i.succ) - (proj x r u i).eval (x i.succ)) ^ 2 := by
    rw [node_sum_eq hn fun j => a (x j) * ηm j ^ 2]
    exact Finset.sum_congr rfl fun i _ => by rw [hηms]
  rw [Finset.sum_add_distrib] at hB2
  have hsum : (A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * Eu * ‖v‖
      = A₀ * Eu * ‖v‖ + A' * Eu * ‖v‖ + A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by ring
  rw [hsum]
  linarith

/-- **The traces of the projection error at the nodes**, for `U ∈ H^{r+1}(x 0, x n)` with
continuous representative `u` and a node system of degree `r` on a partition with
`h_min ≤ h_i ≤ h`: for points `y i` in the panels and weights `0 ≤ a ≤ A`,
`∑ᵢ a(y i) (u(y i) - (P u)ᵢ(y i))² ≤ 2 A h^{2r+1} |U|² (h/h_min + (1 + 4 r (r + 1) h/h_min)²)`.
The trace inequality `sum_mul_sq_sub_eval_le` with the `L²` and `H¹` errors of the projection.
-/
theorem sum_mul_sq_sub_proj_le (hn : 0 < n) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A) {node : Fin n → Fin (r + 1) → ℝ}
    (hnode : IsNodes x r node) {h hmin : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (h0 : 0 < hmin) (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] u)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ Icc (x i.castSucc) (x i.succ)) :
    ∑ i, a (y i) * (u (y i) - (proj x r u i).eval (y i)) ^ 2
      ≤ 2 * A * h ^ (2 * r + 1) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2
        * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hm : Monotone x := hx.out.monotone
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  set S := SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set P := proj x r u with hP
  have hg := SobolevInterval.intervalIntegrable_deriv hab.le U 1
  have hg2 := SobolevInterval.intervalIntegrable_deriv_sq hab.le U 1
  have hfg : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc (x 0) (x (Fin.last n)),
      u t - u s = ∫ q in s..t, SobolevInterval.deriv U 1 q := fun s hs t ht =>
    SobolevInterval.sub_eq_integral_deriv_one hab U hu hU hs ht
  have htr := sum_mul_sq_sub_eval_le hu hg hg2 hfg hmesh h0 hminle P hy (c := fun i => a (y i))
    hA0 fun i => (le_abs_self _).trans (hA (y i) (Icc_panel_subset hm i (hy i)))
  have hE1 : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2
      ≤ (h ^ (r + 1) * S) ^ 2 := by
    have h1 := sqrt_sum_integral_sq_sub_proj_le_seminorm hn hnode hmesh U hu hU
    have hnn : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        integral_nonneg (hm (Fin.castSucc_lt_succ (i := i)).le) fun _ _ => sq_nonneg _
    rw [← Real.sq_sqrt hnn]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hE2 : ∑ i, ∫ s in x i.castSucc..x i.succ,
      (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2
      ≤ (h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * S) ^ 2 := by
    have h1 := sqrt_sum_integral_sq_deriv_sub_proj_le_seminorm hn hnode hmesh h0 hminle U hu hU
    have hnn : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        integral_nonneg (hm (Fin.castSucc_lt_succ (i := i)).le) fun _ _ => sq_nonneg _
    rw [← Real.sq_sqrt hnn]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  refine htr.trans ?_
  have hρ : 0 ≤ h / hmin := div_nonneg hh h0.le
  calc A * (2 / hmin * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2)
        + 2 * h * ∑ i, ∫ s in x i.castSucc..x i.succ,
          (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2)
      ≤ A * (2 / hmin * (h ^ (r + 1) * S) ^ 2
        + 2 * h * (h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * S) ^ 2) := by
        gcongr
    _ = 2 * A * h ^ (2 * r + 1) * S ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
        rw [show h ^ (2 * r + 1) = (h ^ r) ^ 2 * h by rw [pow_succ, pow_mul'],
          show h ^ (r + 1) = h ^ r * h from pow_succ h r]
        field_simp

end DGFixedTime

section DGTimeDependent

variable {a₀ : ℝ → ℝ → ℝ}

/-- **The constant of the discontinuous Galerkin error estimate.** With `ρ = h / h_min` the
mesh ratio, `K = 2 r (r + 1) ρ` the Markov constant, `Φ₀ = (A₀ + A' + A' K) M` the consistency
constant and `K_tr = 2 A M² (ρ + (1 + 4 r (r + 1) ρ)²)` the trace constant, the bound of
`dG_error_sq_le` is `(16 + 4/μ₀) ‖u₀ - u_{0,h}‖² + dgConst · h^{2r+1}` with
`dgConst = 2 h M² + T (2 h M² + 10 K_tr) + (8 + 2/μ₀) (2 h M² + T (h Φ₀²/μ₀ + 2 K_tr))`. -/
def dgConst (r : ℕ) (A A' A₀ μ₀ T M h hmin : ℝ) : ℝ :=
  2 * h * M ^ 2 + T * (2 * h * M ^ 2 + 10 * (2 * A * M ^ 2
      * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)))
    + (8 + 2 / μ₀) * (2 * h * M ^ 2 + T * (h * ((A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * M)
        ^ 2 / μ₀ + 2 * (2 * A * M ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2))))


/-- `(p + q)² ≤ 2 p² + 2 q²`. -/
private theorem add_sq_le_two_mul {p q : ℝ} : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

/-- `c (j + (p - q))² ≤ 2 c j² + 4 c p² + 4 c q²` for `c ≥ 0`. -/
private theorem mul_sq_add_sub_le {c j p q : ℝ} (hc : 0 ≤ c) :
    c * (j + (p - q)) ^ 2 ≤ 2 * (c * j ^ 2) + 4 * (c * p ^ 2) + 4 * (c * q ^ 2) := by
  nlinarith [mul_nonneg hc (sq_nonneg (j - (p - q))), mul_nonneg hc (sq_nonneg (p + q))]

/-- `c (j - p)² ≤ 2 c j² + 2 c p²` for `c ≥ 0`. -/
private theorem mul_sq_sub_le {c j p : ℝ} (hc : 0 ≤ c) :
    c * (j - p) ^ 2 ≤ 2 * (c * j ^ 2) + 2 * (c * p ^ 2) := by
  nlinarith [mul_nonneg hc (sq_nonneg (j + p))]

/-- The absorption of the error terms by the energy:
`(2/μ₀) N + 4 S + 2 J ≤ (2/μ₀ + 6) (N + B + S + J)` for nonnegative parts. -/
private theorem energy_parts_le {N B S J μ₀ : ℝ} (hμ : 0 < μ₀) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) : 2 / μ₀ * N + 4 * S + 2 * J ≤ (2 / μ₀ + 6) * (N + B + S + J) := by
  have hμ' : 0 ≤ 2 / μ₀ := by positivity
  nlinarith [mul_nonneg hμ' hB, mul_nonneg hμ' hS, mul_nonneg hμ' hJ]

/-- The final rearrangement of `dG_error_sq_le`. -/
private theorem dg_final {Y₀ L Yi P Q G e0 w μ₀ T t : ℝ} (hμ : 0 < μ₀) (htT : t ≤ T)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hG : 0 ≤ G) (he0 : e0 ≤ 2 * Yi + 2 * P)
    (hw : w ≤ e0 + t * G) (hY₀ : Y₀ ≤ 2 * P + 2 * (e0 + t * G))
    (hL : L ≤ t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * w) :
    Y₀ + L ≤ (16 + 4 / μ₀) * Yi
      + (2 * P + T * (2 * P + 10 * Q) + (8 + 2 / μ₀) * (2 * P + T * G)) := by
  have h1 : 0 ≤ 2 / μ₀ + 6 := by positivity
  have h2 : t * G ≤ T * G := mul_le_mul_of_nonneg_right htT hG
  have h3 : t * (2 * P + 10 * Q) ≤ T * (2 * P + 10 * Q) :=
    mul_le_mul_of_nonneg_right htT (by positivity)
  have h4 : (2 / μ₀ + 6) * w ≤ (2 / μ₀ + 6) * (e0 + T * G) :=
    mul_le_mul_of_nonneg_left (hw.trans (by linarith)) h1
  have h5 : (2 / μ₀ + 6) * e0 ≤ (2 / μ₀ + 6) * (2 * Yi + 2 * P) := mul_le_mul_of_nonneg_left he0 h1
  have h6 : (2 / μ₀ + 6) * (e0 + T * G) = (2 / μ₀ + 6) * e0 + (2 / μ₀ + 6) * (T * G) := by ring
  have h7 : (16 + 4 / μ₀) * Yi + (2 * P + T * (2 * P + 10 * Q) + (8 + 2 / μ₀) * (2 * P + T * G))
      = 2 * P + 2 * (2 * Yi + 2 * P) + 2 * (T * G) + T * (2 * P + 10 * Q)
        + ((2 / μ₀ + 6) * (2 * Yi + 2 * P) + (2 / μ₀ + 6) * (T * G)) := by ring
  rw [h7]
  linarith

/-- **The error estimate of the discontinuous Galerkin method for the transport equation, squared
form** ([quarteroni2000numerical] §13.10.1, quoted there from Quarteroni–Valli §14.3.3 without
proof; here with explicit constants). Let `u` be a classical solution of `u_t + a u_x + a₀ u = f`
on `[x 0, x n] × [0, T]` with inflow value `u(x 0, t) = φ(t)`, continuous on the strip with
partial derivatives `ux`, `ut` and `ut` continuous on the strip, and regular in the sense that
`u(·, t) ∈ H^{r+1}(x 0, x n)` with `|u(·, t)|_{H^{r+1}} ≤ M` for every `t ∈ [0, T]`. Let
`u_h : [0, T] → W_h` solve the upwind discontinuous Galerkin semi-discretization on the broken
polynomials of degree `r ≥ 0` of a partition with panels of length between `h_min` and `h`
carrying a node system of degree `r`, with the discrete source `f_h(t)` the `L²` projection of
`f(·, t)`. Under the dissipativity `0 < μ₀ ≤ a₀ - a'/2`, with `0 ≤ a ≤ A`, `|a'| ≤ A'`, `|a₀| ≤ A₀`,
for every `t ∈ [0, T]`

`‖u(t) - u_h(t)‖² + ∫₀ᵗ (‖u(τ) - u_h(τ)‖² + ∑_{j=1}^{n-1} a(x_j) [u_h(τ)]_j²
    + a(x 0) (u_h⁺(x 0, τ) - φ(τ))²) dτ
  ≤ (16 + 4/μ₀) ‖u₀ - u_{0,h}‖² + dgConst · h^{2r+1}`,

the book's `O(‖u₀ - u_{0,h}‖ + h^{r+1/2})` squared (the jump `[u - u_h]_0` of the book is
`φ - u_h⁺(x 0)`, since `u` is continuous and `u(x 0) = φ`). The proof is the error equation
`IsSemidiscreteGalerkin.sub` with the `L²` projection `W(t) = P u(·, t)` of the exact solution,
which commutes with `∂ₜ` (`hasDerivWithinAt_proj`) and whose consistency error `dg_defect_le` is
absorbed by the dissipation of the upwind form (`le_dgUpwindForm`): the `L²` part is `O(h^{r+1})`
and the traces of the projection error at the nodes are `O(h^{r+1/2})` by the trace inequality
(`sum_mul_sq_sub_proj_le`), which is where the half power comes from. -/
theorem dG_error_sq_le (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A A' A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A')
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {u ux ut f : ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (huc2 : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y)
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc2 : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t)
    (hin : ∀ t ∈ Icc 0 T, u (x 0) t = φ t) {M : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsNodes x r node) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v, ⟪fh t, v⟫ = pairing (fun y => f y t) v)
    {u₀h : BrokenPolynomial x r} {uh : ℝ → BrokenPolynomial x r}
    (huh : IsSemidiscreteGalerkin (fun t => dgUpwindForm x r ha (ha₀ t))
      (fun t => innerSL ℝ (fh t) + (a (x 0) * φ t) • traceRightL x r ⟨0, hn⟩) u₀h T uh)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
      + ∫ τ in (0 : ℝ)..t, ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
          + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)
    ≤ (16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
      + dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1) := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hM : 0 ≤ M := (apply_nonneg _ _).trans hU₀M
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have hA'0 : 0 ≤ A' := (abs_nonneg _).trans (hA' (x 0) (left_mem_Icc.2 hab.le))
  have hA₀0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ 0 hT0 (x 0) (left_mem_Icc.2 hab.le))
  have hsub : [[(0 : ℝ), t]] ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))) := by
    intro t ht y hy
    have := huc2 (y, t) ⟨hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
  have hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))) := by
    intro t ht y hy
    have := hutc2 (y, t) ⟨hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
  -- the constants
  set ρ : ℝ := h / hmin with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hh h0.le
  set K : ℝ := 2 * r * (r + 1) / hmin with hK
  have hK0 : 0 ≤ K := by positivity
  set Ktr : ℝ := 2 * A * M ^ 2 * (ρ + (1 + 4 * r * (r + 1) * ρ) ^ 2) with hKtr
  have hKtr0 : 0 ≤ Ktr := by positivity
  set Φ₀ : ℝ := (A₀ + A' + A' * h * K) * M with hΦ₀
  have hΦ₀0 : 0 ≤ Φ₀ := by positivity
  set Φ : ℝ := (A₀ + A' + A' * h * K) * (h ^ (r + 1) * M) with hΦ
  have hΦ0 : 0 ≤ Φ := by positivity
  have hΦeq : Φ = h ^ (r + 1) * Φ₀ := by rw [hΦ, hΦ₀]; ring
  set gconst : ℝ := Φ ^ 2 / μ₀ + 2 * (h ^ (2 * r + 1) * Ktr) with hgconst
  have hgconst0 : 0 ≤ gconst := by positivity
  -- the projections
  set W : ℝ → BrokenPolynomial x r := fun t => proj x r fun y => u y t with hW
  set W' : ℝ → BrokenPolynomial x r := fun t => proj x r fun y => ut y t with hW'
  have hWd : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (W' t) (Icc 0 T) t := fun t ht =>
    hasDerivWithinAt_proj hn huc hut hutc2 ht
  have he := huh.sub hWd
  -- the approximation facts at each time
  have hproj : ∀ s ∈ Icc 0 T,
      √(∑ i, ∫ y in x i.castSucc..x i.succ, (u y s - (W s i).eval y) ^ 2) ≤ h ^ (r + 1) * M ∧
      ∀ y : Fin n → ℝ, (∀ i, y i ∈ Icc (x i.castSucc) (x i.succ)) →
        ∑ i, a (y i) * (u (y i) s - (W s i).eval (y i)) ^ 2 ≤ h ^ (2 * r + 1) * Ktr := by
    intro s hs
    obtain ⟨U, hU, hUM⟩ := hreg s hs
    have hS0 : 0 ≤ SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U := apply_nonneg _ _
    refine ⟨(sqrt_sum_integral_sq_sub_proj_le_seminorm hn hnode hmesh U (huc s hs) hU).trans
      (mul_le_mul_of_nonneg_left hUM (by positivity)), fun y hy => ?_⟩
    refine (sum_mul_sq_sub_proj_le hn hA0 hA hnode hmesh h0 hminle U (huc s hs) hU hy).trans ?_
    rw [hKtr, hρ]
    have := pow_le_pow_left₀ hS0 hUM 2
    have hc : 0 ≤ 2 * A * h ^ (2 * r + 1)
        * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
      positivity
    calc 2 * A * h ^ (2 * r + 1) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2
          * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)
        = 2 * A * h ^ (2 * r + 1) * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)
          * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 := by ring
      _ ≤ 2 * A * h ^ (2 * r + 1) * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) * M ^ 2 :=
          mul_le_mul_of_nonneg_left this hc
      _ = h ^ (2 * r + 1)
          * (2 * A * M ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)) := by
          ring
  -- the energy estimate for the discrete error
  set e : ℝ → BrokenPolynomial x r := fun t => uh t - W t with he_def
  set w : ℝ → ℝ := fun s => μ₀ * ‖e s‖ ^ 2
    + a (x (Fin.last n)) * traceLeft (e s) (Fin.last n) ^ 2 / 2
    + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e s) i ^ 2 / 2)
    + a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2 with hw_def
  have hec : ContinuousOn e (Icc 0 T) := he.continuousOn
  have hwc : ContinuousOn w (Icc 0 T) := by
    have h1 : ContinuousOn (fun s => μ₀ * ‖e s‖ ^ 2) (Icc 0 T) :=
      continuousOn_const.mul he.continuousOn_norm_sq
    have h2 : ContinuousOn
        (fun s => a (x (Fin.last n)) * traceLeft (e s) (Fin.last n) ^ 2 / 2) (Icc 0 T) :=
      (continuousOn_const.mul
        (((continuous_traceLeft (Fin.last n)).comp_continuousOn hec).pow 2)).div_const 2
    have h3 : ContinuousOn (fun s => ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e s) i ^ 2 / 2) (Icc 0 T) :=
      continuousOn_finsetSum _ fun i _ =>
        (continuousOn_const.mul (((continuous_jump i).comp_continuousOn hec).pow 2)).div_const 2
    have h4 : ContinuousOn (fun s => a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2) (Icc 0 T) :=
      continuousOn_const.mul (((continuous_jump ⟨0, hn⟩).comp_continuousOn hec).pow 2)
    exact ((h1.add h2).add h3).add h4
  have hbound : ∀ s ∈ Ico 0 T, 2 * (((innerSL ℝ (fh s) + (a (x 0) * φ s) • traceRightL x r ⟨0, hn⟩)
      - (innerSL ℝ (W' s) + dgUpwindForm x r ha (ha₀ s) (W s))) (e s)
      - dgUpwindForm x r ha (ha₀ s) (e s) (e s)) + w s ≤ gconst := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    obtain ⟨U, hU, hUM⟩ := hreg s hs'
    have hux_ae : (fun y => ux y s) =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))]
        SobolevInterval.deriv U 1 :=
      SobolevInterval.ae_eq_deriv_one_of_hasDerivAt hab U (huc s hs') hU fun y hy =>
        (hux y (Ioo_subset_Icc_self hy) s hs').hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have hdef := dg_defect_le hn ha (ha₀ s) hd hd' hapos hA'0 hA' hA₀0 (hA₀ s hs') hmesh h0 hminle
      (huc s hs') (fun y hy => (hux y (Ioo_subset_Icc_self hy) s hs').hasDerivAt
        (Icc_mem_nhds hy.1 hy.2)) (hutc s hs') (fun y hy => hpde y hy s hs') (hin s hs')
      (SobolevInterval.intervalIntegrable_deriv hab.le U 1) hux_ae (hproj s hs').1 (e s)
    have htr := (hproj s hs').2 (fun i => x i.succ) fun i => right_mem_Icc.2
      (hm (Fin.castSucc_lt_succ (i := i)).le)
    have hcoer := le_dgUpwindForm ha (ha₀ s) hd hd' (hμ₀ s hs') (e s)
    have hyoung := IsSemidiscreteGalerkin.two_mul_mul_norm_le hμ Φ (e s)
    have hsplit : ∑ i : Fin n, a (x i.castSucc) * jump (e s) i ^ 2 / 2
        = a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2 / 2
          + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e s) i ^ 2 / 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
      rfl
    have hsplit' : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e s) i ^ 2 / 4
        = (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e s) i ^ 2 / 2) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hF : ((innerSL ℝ (fh s) + (a (x 0) * φ s) • traceRightL x r ⟨0, hn⟩)
        - (innerSL ℝ (W' s) + dgUpwindForm x r ha (ha₀ s) (W s))) (e s)
        = (pairing (fun y => f y s) (e s) + a (x 0) * φ s * traceRight (e s) ⟨0, hn⟩)
          - (⟪W' s, e s⟫ + dgUpwindForm x r ha (ha₀ s) (W s) (e s)) := by
      simp only [_root_.sub_apply, _root_.add_apply, innerSL_apply_apply,
        _root_.smul_apply, traceRightL_apply, smul_eq_mul, hfh s hs' (e s)]
    rw [hF]
    simp only [hw_def]
    rw [hsplit] at hcoer
    have hΦ' : (A₀ + A' + A' * h * K) * (h ^ (r + 1) * M) * ‖e s‖ = Φ * ‖e s‖ := by rw [hΦ]
    rw [hΦ', hsplit'] at hdef
    have hjump0 : 0 ≤ a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2 :=
      mul_nonneg (hapos _ (left_mem_Icc.2 hab.le)) (sq_nonneg _)
    rw [hgconst]
    linarith
  have hstab := he.norm_sq_add_integral_le_integral (w := w) (g := fun _ => gconst) hwc
    continuousOn_const hbound ht
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hstab
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hP1 : (h ^ (r + 1) * M) ^ 2 = h ^ (2 * r + 1) * (h * M ^ 2) := by
    rw [mul_pow, ← pow_mul, show (r + 1) * 2 = 2 * r + 1 + 1 by ring, pow_succ]
    ring
  set P : ℝ := h ^ (2 * r + 1) * (h * M ^ 2) with hP
  set Q : ℝ := h ^ (2 * r + 1) * Ktr with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- the `L²` error at each time, squared
  have hsqL2 : ∀ τ ∈ Icc 0 T, ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2
      ≤ 2 * P + 2 * ‖e τ‖ ^ 2 := by
    intro τ hτ
    have hui : IntervalIntegrable (fun y => u y τ) volume (x 0) (x (Fin.last n)) :=
      ((huc τ hτ).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hui2 : IntervalIntegrable (fun y => u y τ ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc τ hτ).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have htri := sqrt_sum_integral_sub_sq_le hui hui2 (uh τ) (W τ)
    have hX0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hY0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hne : ‖W τ - uh τ‖ = ‖e τ‖ := by rw [he_def, norm_sub_rev]
    have hY := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hproj τ hτ).1 2
    rw [Real.sq_sqrt hY0, hP1] at hY
    calc ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2
        = √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2) ^ 2 :=
          (Real.sq_sqrt hX0).symm
      _ ≤ (√(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2)
          + ‖W τ - uh τ‖) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) htri 2
      _ ≤ 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2) ^ 2
          + 2 * ‖W τ - uh τ‖ ^ 2 := add_sq_le_two_mul
      _ ≤ 2 * P + 2 * ‖e τ‖ ^ 2 := by
          rw [Real.sq_sqrt hY0, hne]
          linarith only [hY]
  -- the integrand of the left side at each time
  have hL : ∀ τ ∈ Icc 0 T,
      (∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
        + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2
      ≤ 2 * P + 10 * Q + (2 / μ₀ + 6) * w τ := by
    intro τ hτ
    have hTrp := (hproj τ hτ).2 (fun i => x i.castSucc) fun i => left_mem_Icc.2 (hle i)
    have hTrm := (hproj τ hτ).2 (fun i => x i.succ) fun i => right_mem_Icc.2 (hle i)
    have huhW : uh τ = e τ + W τ := by rw [he_def]; simp
    have hapos' : ∀ i : Fin n, 0 ≤ a (x i.castSucc) := fun i =>
      hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))
    -- the jumps
    have hjump : ∀ i : Fin n, a (x i.castSucc) * jump (uh τ) i ^ 2
        ≤ 2 * (a (x i.castSucc) * jump (e τ) i ^ 2)
          + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
          + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2) := by
      intro i
      have e1 : jump (uh τ) i = jump (e τ) i + ((u (x i.castSucc) τ - traceLeft (W τ) i.castSucc)
          - (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc))) := by
        rw [huhW, jump_add, jump_apply (W τ), traceRight_apply]
        ring
      rw [e1]
      exact mul_sq_add_sub_le (hapos' i)
    have hsumjump : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2
        ≤ 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
          + 4 * Q + 4 * Q := by
      have hminus : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2 ≤ Q := by
        have hnode := node_sum_eq hn fun j => a (x j) * (u (x j) τ - traceLeft (W τ) j) ^ 2
        have hlast : 0 ≤ a (x (Fin.last n))
            * (u (x (Fin.last n)) τ - traceLeft (W τ) (Fin.last n)) ^ 2 :=
          mul_nonneg (hapos _ (right_mem_Icc.2 hab.le)) (sq_nonneg _)
        have hrw : ∑ i : Fin n, a (x i.succ) * (u (x i.succ) τ - traceLeft (W τ) i.succ) ^ 2
            = ∑ i : Fin n, a (x i.succ) * (u (x i.succ) τ - (W τ i).eval (x i.succ)) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [traceLeft_succ]
        linarith only [hnode, hlast, hrw, hTrm]
      have hplus : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2 ≤ Q :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => mul_nonneg (hapos' i) (sq_nonneg _)).trans hTrp
      calc ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2
          ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (2 * (a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
              + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2)) :=
            Finset.sum_le_sum fun i _ => hjump i
        _ = 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
                a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
              + 4 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
                a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
              Finset.mul_sum]
        _ ≤ 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * Q + 4 * Q := by gcongr
    -- the inflow term
    have hin' : a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2
        ≤ 2 * (a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2) + 2 * Q := by
      have hc : x (⟨0, hn⟩ : Fin n).castSucc = x 0 := rfl
      have e1 : traceRight (uh τ) ⟨0, hn⟩ - φ τ
          = jump (e τ) ⟨0, hn⟩ - (u (x 0) τ - (W τ ⟨0, hn⟩).eval (x 0)) := by
        rw [huhW, traceRight_add, ← jump_zero (e τ) hn, traceRight_apply, hc, hin τ hτ]
        ring
      have h0' := (Finset.single_le_sum (f := fun i : Fin n =>
          a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2)
          (fun i _ => mul_nonneg (hapos' i) (sq_nonneg _)) (Finset.mem_univ ⟨0, hn⟩)).trans hTrp
      simp only [hc] at h0'
      have ha0 := hapos _ (left_mem_Icc.2 hab.le)
      rw [e1]
      have := mul_sq_sub_le (c := a (x 0)) (j := jump (e τ) ⟨0, hn⟩)
        (p := u (x 0) τ - (W τ ⟨0, hn⟩).eval (x 0)) ha0
      linarith only [this, h0']
    -- the parts of `w`
    have hw1 : 0 ≤ a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2 := by
      have := hapos _ (right_mem_Icc.2 hab.le); positivity
    have hw2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e τ) i ^ 2 / 2 :=
      Finset.sum_nonneg fun i _ => by have := hapos' i; positivity
    have hw3 : 0 ≤ a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2 := by
      have := hapos _ (left_mem_Icc.2 hab.le); positivity
    have hw4 : 0 ≤ μ₀ * ‖e τ‖ ^ 2 := by positivity
    have hwτ : w τ = μ₀ * ‖e τ‖ ^ 2 + a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2 / 2)
        + a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2 := rfl
    have hsumhalf : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2
        = 2 * ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e τ) i ^ 2 / 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnorm : 2 * ‖e τ‖ ^ 2 = 2 / μ₀ * (μ₀ * ‖e τ‖ ^ 2) := by field_simp
    have hμ' : 0 ≤ 2 / μ₀ := by positivity
    have hkey : 2 * ‖e τ‖ ^ 2
        + 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
        + 2 * (a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2) ≤ (2 / μ₀ + 6) * w τ := by
      rw [hwτ, hnorm, hsumhalf]
      have := energy_parts_le hμ hw4 hw1 hw2 hw3
      linarith only [this]
    have hsq := hsqL2 τ hτ
    linarith only [hsq, hsumjump, hin', hkey]
  -- integrating the bound on the integrand
  have hwint : IntervalIntegrable w volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hwc.mono (Icc_subset_Icc le_rfl ht.2)
  have hLnn : ∀ τ ∈ Icc 0 T, 0 ≤ (∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
      + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
      + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 := by
    intro τ _
    have h1 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))) (sq_nonneg _)
    have h3 : 0 ≤ a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 :=
      mul_nonneg (hapos _ (left_mem_Icc.2 hab.le)) (sq_nonneg _)
    linarith only [h1, h2, h3]
  have hLint : ∫ τ in (0 : ℝ)..t,
      ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
        + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)
      ≤ t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * ∫ τ in (0 : ℝ)..t, w τ := by
    have hR : ∫ τ in (0 : ℝ)..t, (2 * P + 10 * Q + (2 / μ₀ + 6) * w τ)
        = t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * ∫ τ in (0 : ℝ)..t, w τ := by
      rw [integral_add intervalIntegrable_const (hwint.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
        sub_zero]
    rw [← hR, integral_of_le ht.1, integral_of_le ht.1]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ =>
        hLnn τ (Icc_subset_Icc le_rfl ht.2 (Ioc_subset_Icc_self hτ)))
    · exact ((continuousOn_const.add (continuousOn_const.mul (hwc.mono
        (Icc_subset_Icc le_rfl ht.2)))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ =>
        hL τ (Icc_subset_Icc le_rfl ht.2 (Ioc_subset_Icc_self hτ)))
  -- the initial error
  have he0 : ‖u₀h - W 0‖ ^ 2
      ≤ 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) + 2 * P := by
    have hui : IntervalIntegrable (fun y => u y 0) volume (x 0) (x (Fin.last n)) :=
      ((huc 0 hT0).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hui2 : IntervalIntegrable (fun y => u y 0 ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc 0 hT0).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have htri := norm_sub_le_sqrt_add_sqrt hui hui2 u₀h (W 0)
    have hY0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hX0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hY := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hproj 0 hT0).1 2
    rw [Real.sq_sqrt hY0, hP1] at hY
    calc ‖u₀h - W 0‖ ^ 2
        ≤ (√(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
          + √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) ^ 2
          + 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2) ^ 2 :=
          add_sq_le_two_mul
      _ ≤ 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) + 2 * P := by
          rw [Real.sq_sqrt hX0, Real.sq_sqrt hY0]
          linarith only [hY]
  -- the pieces of the energy estimate
  have hwnn : 0 ≤ ∫ τ in (0 : ℝ)..t, w τ := by
    refine integral_nonneg ht.1 fun τ hτ => ?_
    have h1 := hapos _ (right_mem_Icc.2 hab.le)
    have h2 := hapos _ (left_mem_Icc.2 hab.le)
    have h3 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e τ) i ^ 2 / 2 :=
      Finset.sum_nonneg fun i _ => by
        have := hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i))); positivity
    change 0 ≤ μ₀ * ‖e τ‖ ^ 2 + a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2
      + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2 / 2)
      + a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2
    positivity
  have hwle : ∫ τ in (0 : ℝ)..t, w τ ≤ ‖u₀h - W 0‖ ^ 2 + t * gconst := by
    linarith only [hstab, sq_nonneg ‖e t‖]
  have hY₀ : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2
      ≤ 2 * P + 2 * (‖u₀h - W 0‖ ^ 2 + t * gconst) := by
    have := hsqL2 t ht
    linarith only [this, hstab, hwnn]
  -- assembling
  have hfinal := dg_final (μ₀ := μ₀) hμ ht.2 hP0 hQ0 hgconst0 he0 hwle hY₀ hLint
  refine hfinal.trans (le_of_eq ?_)
  have hΦsq : Φ ^ 2 = h ^ (2 * r + 1) * (h * Φ₀ ^ 2) := by
    rw [hΦeq, mul_pow, ← pow_mul, show (r + 1) * 2 = 2 * r + 1 + 1 by ring, pow_succ]
    ring
  rw [hgconst, hΦsq, hQ, hP, hKtr, hΦ₀, hK, hρ, dgConst]
  ring

end DGTimeDependent

end Variational

end
