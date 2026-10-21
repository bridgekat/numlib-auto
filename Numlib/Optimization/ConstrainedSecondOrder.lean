import Numlib.Optimization.Constrained
import Mathlib.Analysis.Calculus.TangentCone.Seq
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Strict sufficiency on the tangent critical cone

Second-order sufficiency uses limits of normalized feasible directions. Requiring positivity
only on radial feasible directions can miss these limits, even for closed convex sets.
The positive tangent cone retains them. A first-order variational inequality and positivity
of the actual Hessian on its nonzero critical directions imply a strict local minimum.
-/

open Filter Topology Metric Set

namespace Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive tangent directions along which the first variation vanishes. -/
def tangentCriticalCone (S : Set E) (x : E) (g : E →L[ℝ] ℝ) : Set E :=
  {d | d ∈ tangentConeAt NNReal S x ∧ g d = 0}

/-- Membership records both actual tangency and the vanishing first variation. -/
@[simp] theorem mem_tangentCriticalCone {S : Set E} {x d : E} {g : E →L[ℝ] ℝ} :
    d ∈ tangentCriticalCone S x g ↔ d ∈ tangentConeAt NNReal S x ∧ g d = 0 := Iff.rfl

/-- Every feasible point has the zero critical direction. -/
theorem zero_mem_tangentCriticalCone {S : Set E} {x : E} (hx : x ∈ S)
    (g : E →L[ℝ] ℝ) : (0 : E) ∈ tangentCriticalCone S x g :=
  ⟨zero_mem_tangentConeAt (subset_closure hx), map_zero g⟩

/-- A first-order variational inequality and Hessian positivity on all nonzero tangent
critical directions imply a strict constrained local minimum. Only finite-dimensional
compactness and actual derivatives are used; the feasible set need not be convex or closed. -/
theorem isStrictLocalMinOn_of_posDef_tangentCriticalCone [FiniteDimensional ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {S : Set E} {x : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hH : HasFDerivAt f' H x)
    (hfirst : ∀ y ∈ S, 0 ≤ f' x (y - x))
    (hpos : ∀ d ∈ tangentCriticalCone S x (f' x), d ≠ 0 → 0 < H d d) :
    ∃ δ > 0, ∀ y ∈ S, dist y x < δ → y ≠ x → f x < f y := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ y, y ∈ S ∧ dist y x < 1 / ((n : ℝ) + 1) ∧ y ≠ x ∧
      f y ≤ f x := by
    intro n
    exact hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose y hyS hyd hyne hyf using hseq
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwne : ∀ n, y n - x ≠ 0 := fun n => sub_ne_zero.2 (hyne n)
  set u : ℕ → E := fun n => ‖y n - x‖⁻¹ • (y n - x) with hu
  have hunorm : ∀ n, ‖u n‖ = 1 := fun n => by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hwne n))]
  obtain ⟨z, hz, φ, hφ, hulim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun n => mem_sphere_zero_iff_norm.2 (hunorm n)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz
    exact zero_ne_one hz
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 x) := hylim.comp hφ.tendsto_atTop
  have htan : z ∈ tangentConeAt NNReal S x := by
    apply mem_tangentConeAt_of_seq atTop (fun n => Real.toNNReal ‖y (φ n) - x‖⁻¹)
      (fun n => y (φ n) - x)
    · simpa using hyφ.sub_const x
    · exact Eventually.of_forall fun n => by simpa using hyS (φ n)
    · refine hulim.congr fun n => ?_
      rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr (norm_nonneg _))]
      rfl
  have hlin : ∀ n, 0 ≤ f' x (u n) := by
    intro n
    rw [hu, map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hfirst _ (hyS n))
  have hcrit : f' x z = 0 := by
    have hrem := (hasFDerivAt_iff_tendsto.mp hf.self_of_nhds).comp hyφ
    have hpoint : ∀ n, f' x (u (φ n)) ≤ ‖y (φ n) - x‖⁻¹ *
        ‖f (y (φ n)) - f x - f' x (y (φ n) - x)‖ := by
      intro n
      rw [hu, map_smul, smul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
      rw [Real.norm_eq_abs]
      linarith [neg_abs_le (f (y (φ n)) - f x - f' x (y (φ n) - x)), hyf (φ n)]
    have hl := ((f' x).continuous.tendsto z).comp hulim
    exact le_antisymm (le_of_tendsto_of_tendsto' hl hrem hpoint)
      (ge_of_tendsto' hl fun n => hlin (φ n))
  have hr := ((isLittleO_taylor_two hf hH).tendsto_div_nhds_zero).comp hyφ
  have hkey : ∀ n, H (u (φ n)) (u (φ n)) / 2 ≤
      -((f (y (φ n)) - f x - f' x (y (φ n) - x) -
        H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2) := by
    intro n
    have hn : ‖y (φ n) - x‖ ≠ 0 := norm_ne_zero_iff.2 (hwne _)
    have hnpos : 0 < ‖y (φ n) - x‖ ^ 2 := pow_pos (norm_pos_iff.2 (hwne _)) 2
    have hHu : H (u (φ n)) (u (φ n)) =
        H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 := by
      simp only [hu, map_smul, smul_apply, smul_eq_mul]
      field_simp
    rw [hHu]
    have hd : (f (y (φ n)) - f x - f' x (y (φ n) - x)) / ‖y (φ n) - x‖ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [hyf (φ n), hfirst _ (hyS (φ n))])
        hnpos.le
    have hsplit : -((f (y (φ n)) - f x - f' x (y (φ n) - x) -
        H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2) =
        H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 / 2 -
        (f (y (φ n)) - f x - f' x (y (φ n) - x)) / ‖y (φ n) - x‖ ^ 2 := by ring
    rw [hsplit]
    linarith
  have hlimL : Tendsto (fun n => H (u (φ n)) (u (φ n)) / 2) atTop (𝓝 (H z z / 2)) := by
    have hcont : Continuous fun v : E => H v v :=
      H.continuous₂.comp (continuous_id.prodMk continuous_id)
    exact ((hcont.tendsto z).comp hulim).div_const 2
  have hlimR : Tendsto (fun n => -((f (y (φ n)) - f x - f' x (y (φ n) - x) -
      H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hr.neg
  have hle := le_of_tendsto_of_tendsto' hlimL hlimR hkey
  have := hpos z ⟨htan, hcrit⟩ hz0
  linarith

/-- Twice continuous differentiability on an open neighborhood gives the actual
first derivative and Hessian required by tangent-critical-cone sufficiency. -/
theorem isStrictLocalMinOn_of_contDiffOn_posDef_tangentCriticalCone [FiniteDimensional ℝ E]
    {f : E → ℝ} {S U : Set E} {x : E} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContDiffOn ℝ 2 f U) (hfirst : ∀ y ∈ S, 0 ≤ fderiv ℝ f x (y - x))
    (hpos : ∀ d ∈ tangentCriticalCone S x (fderiv ℝ f x), d ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x d d) :
    ∃ δ > 0, ∀ y ∈ S, dist y x < δ → y ≠ x → f x < f y := by
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hxU
  have hf' : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  apply isStrictLocalMinOn_of_posDef_tangentCriticalCone _
    (((hf'.differentiableOn (by norm_num) x hxU).differentiableAt hUn).hasFDerivAt) hfirst hpos
  filter_upwards [hUn] with y hy
  exact ((hf.differentiableOn (by norm_num) y hy).differentiableAt
    (hU.mem_nhds hy)).hasFDerivAt

/-- A twice continuously differentiable objective uses its actual derivative and Hessian. -/
theorem isStrictLocalMinOn_of_contDiff_posDef_tangentCriticalCone [FiniteDimensional ℝ E]
    {f : E → ℝ} {S : Set E} {x : E} (hf : ContDiff ℝ 2 f)
    (hfirst : ∀ y ∈ S, 0 ≤ fderiv ℝ f x (y - x))
    (hpos : ∀ d ∈ tangentCriticalCone S x (fderiv ℝ f x), d ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x d d) :
    ∃ δ > 0, ∀ y ∈ S, dist y x < δ → y ≠ x → f x < f y :=
  isStrictLocalMinOn_of_contDiffOn_posDef_tangentCriticalCone isOpen_univ (mem_univ x)
    hf.contDiffOn hfirst hpos

/-- At a stationary constrained local minimum, the actual Hessian is nonnegative on
all positive tangent directions. A tangent sequence suffices for the Peano expansion;
no second derivative of a feasible curve is required. -/
theorem nonneg_second_on_tangentCone_of_isLocalMinOn
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hH : HasFDerivAt f' H x)
    (hstat : f' x = 0) (hmin : IsLocalMinOn f S x) {z : E}
    (hz : z ∈ tangentConeAt NNReal S x) : 0 ≤ H z z := by
  obtain ⟨c, d, hd, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq.mp hz
  have hxd : Tendsto (fun n => x + d n) atTop (𝓝 x) := by simpa using hd.const_add x
  have hxdS : Tendsto (fun n => x + d n) atTop (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxd, hds⟩
  have hval : ∀ᶠ n in atTop, 0 ≤ f (x + d n) - f x :=
    (hxdS.eventually hmin).mono fun n hn => sub_nonneg.mpr hn
  let R : ℕ → ℝ := fun n => f (x + d n) - f x - H (d n) (d n) / 2
  have hrem : Tendsto (fun n => R n / ‖d n‖ ^ 2) atTop (𝓝 0) := by
    have hr := ((isLittleO_taylor_two hf hH).tendsto_div_nhds_zero).comp hxd
    simpa only [Function.comp_def, add_sub_cancel_left, hstat,
      zero_apply, sub_zero, R] using hr
  have hnorm : Tendsto (fun n => ‖c n • d n‖ ^ 2) atTop (𝓝 (‖z‖ ^ 2)) := hcd.norm.pow 2
  have hR : Tendsto (fun n => (c n : ℝ) ^ 2 * R n) atTop (𝓝 0) := by
    have hmul := hrem.mul hnorm
    rw [zero_mul] at hmul
    refine hmul.congr fun n => ?_
    by_cases hn : d n = 0
    · simp [hn, R]
    · rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (c n).coe_nonneg,
        mul_pow]
      have hdn : ‖d n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
      field_simp
  have hquad : Tendsto (fun n => H (c n • d n) (c n • d n) / 2) atTop
      (𝓝 (H z z / 2)) := by
    have hcont : Continuous fun v : E => H v v :=
      H.continuous₂.comp (continuous_id.prodMk continuous_id)
    exact ((hcont.tendsto z).comp hcd).div_const 2
  have hpoint : ∀ᶠ n in atTop, -(c n : ℝ) ^ 2 * R n ≤
      H (c n • d n) (c n • d n) / 2 := by
    filter_upwards [hval] with n hn
    simp only [NNReal.smul_def, map_smul, smul_apply, smul_eq_mul]
    dsimp [R]
    nlinarith [sq_nonneg (c n : ℝ), mul_nonneg (sq_nonneg (c n : ℝ)) hn]
  have hneg : Tendsto (fun n => -(c n : ℝ) ^ 2 * R n) atTop (𝓝 0) := by
    simpa [neg_mul] using hR.neg
  have := le_of_tendsto_of_tendsto hneg hquad hpoint
  linarith

/-- Equality LICQ makes every Jacobian-kernel direction positively tangent to the
feasible set. Stationary Lagrangian multipliers therefore have nonnegative actual Hessian
on that kernel at a feasible local minimum. The implicit-function curve needs only one
derivative; the second-order expansion is applied directly to the Lagrangian. -/
theorem nonneg_lagrangian_second_of_isRegularPoint [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hx : IsRegularPoint h h' x) (hmin : IsLocalMinOn f (feasibleEq h) x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hh : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (h' i y) y)
    (hhstrict : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hH : HasFDerivAt (fun y => f' y + ∑ i, l i • h' i y) H x)
    (hstat : f' x + ∑ i, l i • h' i x = 0) {z : E} (hz : ∀ i, h' i x z = 0) :
    0 ≤ H z z := by
  classical
  have hcs : HasStrictFDerivAt (fun y i => h i y)
      (ContinuousLinearMap.pi (fun i => h' i x)) x :=
    hasStrictFDerivAt_pi.mpr hhstrict
  obtain ⟨γ, hγ0, hγ, hγc⟩ := exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top
    hcs hx.2.range_pi_eq_top z
  have hγcont : Tendsto γ (𝓝 0) (𝓝 x) := by simpa [hγ0] using hγ.continuousAt.tendsto
  have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ feasibleEq h := by
    filter_upwards [hγc] with t ht
    intro i
    have hi := congrFun ht i
    simpa [ContinuousLinearMap.pi_apply, hx.1 i, hz i] using hi
  have htan : z ∈ tangentConeAt NNReal (feasibleEq h) x := by
    refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => Real.toNNReal t⁻¹)
      (fun t => γ t - x) ?_ ?_ ?_
    · simpa using (hγcont.mono_left nhdsWithin_le_nhds).sub_const x
    · exact (hfeas.filter_mono nhdsWithin_le_nhds).mono fun t ht => by simpa using ht
    · have hslope := hγ.tendsto_slope_zero_right
      simp only [zero_add, hγ0] at hslope
      refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)]
  have hLmin : IsLocalMinOn (fun y => lagrangian f h y l) (feasibleEq h) x := by
    filter_upwards [hmin, self_mem_nhdsWithin] with y hy hyS
    simpa only [lagrangian_eq_of_mem hx.1 l, lagrangian_eq_of_mem hyS l] using hy
  apply nonneg_second_on_tangentCone_of_isLocalMinOn _ hH hstat hLmin htan
  filter_upwards [hf, eventually_all.mpr hh] with y hfy hhy
  exact lagrangian_hasFDerivAt hfy hhy l

section EqualityContDiff
variable {ι : Type*} [Fintype ι]

/-- The finite Lagrangian inherits any common differentiability order on the same set. -/
theorem contDiffOn_lagrangian {f : E → ℝ} {h : ι → E → ℝ} {n : WithTop ℕ∞} {U : Set E}
    (hf : ContDiffOn ℝ n f U) (hh : ∀ i, ContDiffOn ℝ n (h i) U) (l : ι → ℝ) :
    ContDiffOn ℝ n (fun y => lagrangian f h y l) U := by
  exact hf.add (ContDiffOn.sum fun i _ => contDiffOn_const.mul (hh i))

/-- The actual derivative of the finite Lagrangian is the sum of the actual derivatives. -/
theorem fderiv_lagrangian {f : E → ℝ} {h : ι → E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hh : ∀ i, DifferentiableAt ℝ (h i) x) (l : ι → ℝ) :
    fderiv ℝ (fun y => lagrangian f h y l) x =
      fderiv ℝ f x + ∑ i, l i • fderiv ℝ (h i) x :=
  (lagrangian_hasFDerivAt hf.hasFDerivAt (fun i => (hh i).hasFDerivAt) l).fderiv

/-- Equality LICQ gives unique stationary multipliers, and the actual Lagrangian Hessian
is nonnegative on the constraint Jacobian kernel at a local minimum. Smoothness is needed
only on an open neighborhood of the point. -/
theorem existsUnique_stationary_lagrangian_second_of_isLocalMinOn [FiniteDimensional ℝ E]
    {f : E → ℝ} {h : ι → E → ℝ} {x : E} {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContDiffOn ℝ 2 f U) (hh : ∀ i, ContDiffOn ℝ 2 (h i) U)
    (hx : IsRegularPoint h (fun i => fderiv ℝ (h i)) x)
    (hmin : IsLocalMinOn f (feasibleEq h) x) :
    ∃! l : ι → ℝ, fderiv ℝ (fun y => lagrangian f h y l) x = 0 ∧
      ∀ z, (∀ i, fderiv ℝ (h i) x z = 0) →
        0 ≤ fderiv ℝ (fderiv ℝ (fun y => lagrangian f h y l)) x z z := by
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hxU
  have hfn : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hUn] with y hy
    exact ((hf.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hhn : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (fderiv ℝ (h i) y) y := by
    intro i
    filter_upwards [hUn] with y hy
    exact (((hh i).differentiableOn (by norm_num) y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt
  have hhstrict : ∀ i, HasStrictFDerivAt (h i) (fderiv ℝ (h i) x) x :=
    fun i => ((hh i).contDiffAt hUn).hasStrictFDerivAt (by norm_num)
  obtain ⟨l, hl, huniq⟩ := existsUnique_multipliers_of_isLocalMinOn hx hmin
    ((hf.contDiffAt hUn).hasStrictFDerivAt (by norm_num)) hhstrict
  have heq (a : ι → ℝ) : (fun y => fderiv ℝ f y + ∑ i, a i • fderiv ℝ (h i) y) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => lagrangian f h y a) := by
    filter_upwards [hfn, eventually_all.mpr hhn] with y hfy hhy
    exact (lagrangian_hasFDerivAt hfy hhy a).fderiv.symm
  refine ⟨l, ⟨?_, ?_⟩, ?_⟩
  · rw [← (heq l).self_of_nhds]
    exact hl
  · intro z hz
    have hL := contDiffOn_lagrangian hf hh l
    have hL' : ContDiffOn ℝ 1 (fderiv ℝ (fun y => lagrangian f h y l)) U :=
      hL.fderiv_of_isOpen hU (by norm_num)
    have hH := ((hL'.differentiableOn (by norm_num) x hxU).differentiableAt hUn).hasFDerivAt
    exact nonneg_lagrangian_second_of_isRegularPoint hx hmin hfn hhn hhstrict
      (hH.congr_of_eventuallyEq (heq l)) hl hz
  · intro a ha
    apply huniq a
    exact (heq a).self_of_nhds.trans ha.1

/-- The actual stationary Lagrangian Hessian gives strict equality-constrained sufficiency.
Smoothness is local, and no constraint qualification is required in this direction. -/
theorem isStrictLocalMinOn_of_contDiffOn_lagrangian_second_order [FiniteDimensional ℝ E]
    {f : E → ℝ} {h : ι → E → ℝ} {x : E} {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContDiffOn ℝ 2 f U) (hh : ∀ i, ContDiffOn ℝ 2 (h i) U)
    (hx : x ∈ feasibleEq h) (l : ι → ℝ)
    (hstat : fderiv ℝ (fun y => lagrangian f h y l) x = 0)
    (hpos : ∀ z, z ≠ 0 → (∀ i, fderiv ℝ (h i) x z = 0) →
      0 < fderiv ℝ (fderiv ℝ (fun y => lagrangian f h y l)) x z z) :
    ∃ δ > 0, ∀ y ∈ feasibleEq h, dist y x < δ → y ≠ x → f x < f y := by
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hxU
  have hfn : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hUn] with y hy
    exact ((hf.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hhn : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (fderiv ℝ (h i) y) y := by
    intro i
    filter_upwards [hUn] with y hy
    exact (((hh i).differentiableOn (by norm_num) y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt
  have heq : (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => lagrangian f h y l) := by
    filter_upwards [hfn, eventually_all.mpr hhn] with y hfy hhy
    exact (lagrangian_hasFDerivAt hfy hhy l).fderiv.symm
  have hL := contDiffOn_lagrangian hf hh l
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ (fun y => lagrangian f h y l)) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hH := ((hL'.differentiableOn (by norm_num) x hxU).differentiableAt hUn).hasFDerivAt
  have hs : fderiv ℝ f x + ∑ i, l i • fderiv ℝ (h i) x = 0 := by
    exact heq.self_of_nhds.trans hstat
  exact isLocalMin_of_lagrangian_second_order hx hfn hhn
    (hH.congr_of_eventuallyEq heq) hs hpos

end EqualityContDiff

end Constrained
