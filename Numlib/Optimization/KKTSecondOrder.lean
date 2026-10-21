import Numlib.Optimization.ConstrainedSecondOrderComparison
import Numlib.Analysis.Calculus.ContDiffNeighborhood

/-!
# Second-order KKT geometry

The canonical sign convention is `h = 0`, `g ≤ 0` and nonnegative inequality multipliers.
The critical face keeps every inequality with positive multiplier at equality. The actual
Lagrangian equals the objective on this face. Under LICQ, critical linearized directions
are genuinely tangent to that face, using the first-derivative implicit-function curve.
-/

noncomputable section
open Filter Topology Set

namespace Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The mixed equality/inequality Lagrangian, with `g ≤ 0` and nonnegative `μ`. -/
def mixedLagrangian (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) (x : E) : ℝ :=
  lagrangian f h x l + ∑ j, μ j * g j x

/-- The linearized critical cone of a KKT point. -/
def kktCriticalCone (h' : ι → E → E →L[ℝ] ℝ) (g : κ → E → ℝ)
    (g' : κ → E → E →L[ℝ] ℝ) (x : E) (μ : κ → ℝ) : Set E :=
  {d | (∀ i, h' i x d = 0) ∧ ∀ j ∈ activeSet g x,
    (0 < μ j → g' j x d = 0) ∧ (μ j = 0 → g' j x d ≤ 0)}

omit [Fintype ι] [Fintype κ] in
/-- Membership exposes the equality, positive-multiplier and zero-multiplier branches. -/
@[simp] theorem mem_kktCriticalCone {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {x d : E} {μ : κ → ℝ} :
    d ∈ kktCriticalCone h' g g' x μ ↔ (∀ i, h' i x d = 0) ∧
      ∀ j ∈ activeSet g x, (0 < μ j → g' j x d = 0) ∧ (μ j = 0 → g' j x d ≤ 0) := Iff.rfl

omit [Fintype ι] [Fintype κ] in
/-- Every critical direction is linearized feasible when the multipliers are nonnegative. -/
theorem kktCriticalCone.active_nonpos {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {x d : E} {μ : κ → ℝ}
    (hd : d ∈ kktCriticalCone h' g g' x μ) (hμ : ∀ j, 0 ≤ μ j)
    {j : κ} (hj : j ∈ activeSet g x) : g' j x d ≤ 0 := by
  rcases eq_or_lt_of_le (hμ j) with hzero | hpos
  · exact (hd.2 j hj).2 hzero.symm
  · exact ((hd.2 j hj).1 hpos).le

/-- The actual feasible face that keeps positive-multiplier inequalities at equality. -/
def criticalFace (h : ι → E → ℝ) (g : κ → E → ℝ) (μ : κ → ℝ) : Set E :=
  {y | y ∈ feasible h g ∧ ∀ j, 0 < μ j → g j y = 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ] in
/-- Critical-face membership consists of actual feasibility and the extra equalities. -/
@[simp] theorem mem_criticalFace {h : ι → E → ℝ} {g : κ → E → ℝ} {μ : κ → ℝ} {y : E} :
    y ∈ criticalFace h g μ ↔ y ∈ feasible h g ∧ ∀ j, 0 < μ j → g j y = 0 := Iff.rfl

/-- Complementarity puts a KKT point in its critical face. -/
theorem IsKKTPoint.mem_criticalFace {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ}
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ}
    {x : E} {l : ι → ℝ} {μ : κ → ℝ} (hx : IsKKTPoint f' h h' g g' x l μ) :
    x ∈ criticalFace h g μ := by
  refine ⟨hx.mem_feasible, fun j hj => ?_⟩
  exact (mul_eq_zero.mp (hx.complementary j)).resolve_left hj.ne'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The mixed Lagrangian equals the objective on the actual critical face. -/
theorem mixedLagrangian_eq_of_mem_criticalFace {f : E → ℝ} {h : ι → E → ℝ}
    {g : κ → E → ℝ} {μ : κ → ℝ} {y : E} (hy : y ∈ criticalFace h g μ)
    (hμ : ∀ j, 0 ≤ μ j) (l : ι → ℝ) : mixedLagrangian f h g l μ y = f y := by
  have hsum : ∀ j, μ j * g j y = 0 := by
    intro j
    rcases eq_or_lt_of_le (hμ j) with hzero | hpos
    · rw [← hzero, zero_mul]
    · rw [hy.2 j hpos, mul_zero]
  simp only [mixedLagrangian, lagrangian_eq_of_mem hy.1.1 l, hsum,
    Finset.sum_const_zero, add_zero]

/-- Under LICQ, a critical direction is genuinely tangent to the actual critical face.
The feasible curve needs only its first derivative. -/
theorem IsKKTPoint.mem_posTangentConeAt_criticalFace [FiniteDimensional ℝ E]
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint f' h h' g g' x l μ) (hreg : IsRegularPointIneq h h' g g' x)
    (hh : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasStrictFDerivAt (g j) (g' j x) x) {d : E}
    (hd : d ∈ kktCriticalCone h' g g' x μ) : d ∈ posTangentConeAt (criticalFace h g μ) x := by
  obtain ⟨γ, hγ0, hγ, hfeas, hactive⟩ := exists_feasible_curve_of_isRegularPointIneq
    hreg hh hg hd.1 (fun j hj => kktCriticalCone.active_nonpos hd hkkt.nonneg hj)
  have hγcont : Tendsto γ (𝓝 0) (𝓝 x) := by simpa [hγ0] using hγ.continuousAt.tendsto
  have hface : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ criticalFace h g μ := by
    filter_upwards [hfeas, hactive.filter_mono nhdsWithin_le_nhds] with t ht ha
    refine ⟨ht, fun j hj => ?_⟩
    have hjact : j ∈ activeSet g x :=
      mem_activeSet.mpr ((mul_eq_zero.mp (hkkt.complementary j)).resolve_left hj.ne')
    rw [ha j hjact, (hd.2 j hjact).1 hj, mul_zero]
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => Real.toNNReal t⁻¹)
    (fun t => γ t - x) ?_ ?_ ?_
  · simpa using (hγcont.mono_left nhdsWithin_le_nhds).sub_const x
  · exact hface.mono fun t ht => by simpa using ht
  · have hslope := hγ.tendsto_slope_zero_right
    simp only [zero_add, hγ0] at hslope
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)]

/-- Actual derivatives of the finite mixed Lagrangian are exactly the KKT stationary sum. -/
theorem mixedLagrangian_hasFDerivAt {f : E → ℝ} {f' : E →L[ℝ] ℝ}
    {h : ι → E → ℝ} {h' : ι → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x)
    (hh : ∀ i, HasFDerivAt (h i) (h' i) x) (hg : ∀ j, HasFDerivAt (g j) (g' j) x)
    (l : ι → ℝ) (μ : κ → ℝ) :
    HasFDerivAt (mixedLagrangian f h g l μ) (f' + ∑ i, l i • h' i + ∑ j, μ j • g' j) x :=
  (lagrangian_hasFDerivAt (f' := fun _ => f') (h' := fun i _ => h' i) hf hh l).add
    (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => (hg j).const_mul (μ j))

/-- The finite mixed Lagrangian inherits a common differentiability order on the same set. -/
theorem contDiffOn_mixedLagrangian {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ}
    {n : WithTop ℕ∞} {U : Set E} (hf : ContDiffOn ℝ n f U)
    (hh : ∀ i, ContDiffOn ℝ n (h i) U) (hg : ∀ j, ContDiffOn ℝ n (g j) U)
    (l : ι → ℝ) (μ : κ → ℝ) : ContDiffOn ℝ n (mixedLagrangian f h g l μ) U :=
  (contDiffOn_lagrangian hf hh l).add
    (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hg j))

/-- At an LICQ constrained local minimum, the actual stationary mixed Lagrangian Hessian
is nonnegative on every critical-cone direction. The proof uses actual local minimality on
the critical face and its genuine tangent cone. -/
theorem IsKKTPoint.nonneg_second_of_isLocalMinOn [FiniteDimensional ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} (hkkt : IsKKTPoint f' h h' g g' x l μ)
    (hreg : IsRegularPointIneq h h' g g' x) (hmin : IsLocalMinOn f (feasible h g) x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hh : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (h' i y) y)
    (hg : ∀ j, ∀ᶠ y in 𝓝 x, HasFDerivAt (g j) (g' j y) y)
    (hhstrict : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hgstrict : ∀ j, HasStrictFDerivAt (g j) (g' j x) x)
    (hH : HasFDerivAt (fun y => f' y + ∑ i, l i • h' i y + ∑ j, μ j • g' j y) H x)
    {d : E} (hd : d ∈ kktCriticalCone h' g g' x μ) : 0 ≤ H d d := by
  have hminface : IsLocalMinOn f (criticalFace h g μ) x :=
    hmin.filter_mono (nhdsWithin_mono _ fun _ hy => hy.1)
  have hLmin : IsLocalMinOn (mixedLagrangian f h g l μ) (criticalFace h g μ) x := by
    filter_upwards [hminface, self_mem_nhdsWithin] with y hy hyface
    simpa only [mixedLagrangian_eq_of_mem_criticalFace hkkt.mem_criticalFace hkkt.nonneg l,
      mixedLagrangian_eq_of_mem_criticalFace hyface hkkt.nonneg l] using hy
  apply nonneg_second_on_tangentCone_of_isLocalMinOn _ hH hkkt.stationary hLmin
    (hkkt.mem_posTangentConeAt_criticalFace hreg hhstrict hgstrict hd)
  filter_upwards [hf, eventually_all.mpr hh, eventually_all.mpr hg] with y hfy hhy hgy
  exact mixedLagrangian_hasFDerivAt hfy hhy hgy l μ

/-- A feasible tangent direction with nonpositive objective first variation is a KKT
critical direction. Actual constraint derivatives and stationarity suffice; no qualification
is needed in this direction. -/
theorem IsKKTPoint.mem_kktCriticalCone_of_tangent_of_nonpos
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint f' h h' g g' x l μ)
    (hh : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasFDerivAt (g j) (g' j x) x) {z : E}
    (hz : z ∈ posTangentConeAt (feasible h g) x) (hfz : f' x z ≤ 0) :
    z ∈ kktCriticalCone h' g g' x μ := by
  have hhz : ∀ i, h' i x z = 0 := by
    intro i
    have hmin : IsMinOn (h i) (feasible h g) x := by
      intro y hy
      change h i x ≤ h i y
      rw [hkkt.feasible_eq i, hy.1 i]
    have hmax : IsMaxOn (h i) (feasible h g) x := by
      intro y hy
      change h i y ≤ h i x
      rw [hkkt.feasible_eq i, hy.1 i]
    exact le_antisymm
      (hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hh i).hasFDerivWithinAt hz)
      (hmin.isLocalMinOn.hasFDerivWithinAt_nonneg (hh i).hasFDerivWithinAt hz)
  have hgz : ∀ j ∈ activeSet g x, g' j x z ≤ 0 := by
    intro j hj
    have hmax : IsMaxOn (g j) (feasible h g) x := by
      intro y hy
      rw [mem_activeSet.mp hj]
      exact hy.2 j
    exact hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos (hg j).hasFDerivWithinAt hz
  have hterms : ∀ j, μ j * g' j x z ≤ 0 := by
    intro j
    by_cases hj : j ∈ activeSet g x
    · exact mul_nonpos_of_nonneg_of_nonpos (hkkt.nonneg j) (hgz j hj)
    · rw [hkkt.eq_zero_of_notMem_activeSet hj, zero_mul]
  have hs := congrArg (fun w : E →L[ℝ] ℝ => w z) hkkt.stationary
  simp only [add_apply, sum_apply,
    smul_apply, smul_eq_mul, zero_apply, hhz, mul_zero,
    Finset.sum_const_zero, add_zero] at hs
  have hsum : ∑ j, μ j * g' j x z = 0 := by
    have hn := Finset.sum_nonpos (s := Finset.univ) fun j _ => hterms j
    linarith
  have hzero : ∀ j, μ j * g' j x z = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterms i)).mp hsum j (Finset.mem_univ j)
  refine ⟨hhz, fun j hj => ⟨?_, fun _ => hgz j hj⟩⟩
  intro hμ
  exact (mul_eq_zero.mp (hzero j)).resolve_left hμ.ne'

/-- Positive definiteness on the exact nonzero KKT critical cone gives strict constrained
sufficiency. The actual mixed Lagrangian is a stationary comparison minorant; no constraint
qualification or feasible-curve assumption is required. -/
theorem IsKKTPoint.isStrictLocalMinOn_of_posDef_second [FiniteDimensional ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} (hkkt : IsKKTPoint f' h h' g g' x l μ)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hh : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (h' i y) y)
    (hg : ∀ j, ∀ᶠ y in 𝓝 x, HasFDerivAt (g j) (g' j y) y)
    (hH : HasFDerivAt (fun y => f' y + ∑ i, l i • h' i y + ∑ j, μ j • g' j y) H x)
    (hpos : ∀ z ∈ kktCriticalCone h' g g' x μ, z ≠ 0 → 0 < H z z) :
    ∃ δ > 0, ∀ y ∈ feasible h g, dist y x < δ → y ≠ x → f x < f y := by
  have hL : ∀ᶠ y in 𝓝 x, HasFDerivAt (mixedLagrangian f h g l μ)
      (f' y + ∑ i, l i • h' i y + ∑ j, μ j • g' j y) y := by
    filter_upwards [hf, eventually_all.mpr hh, eventually_all.mpr hg] with y hfy hhy hgy
    exact mixedLagrangian_hasFDerivAt hfy hhy hgy l μ
  apply isStrictLocalMinOn_of_posDef_comparison hf.self_of_nhds hL hH hkkt.stationary
    (mixedLagrangian_eq_of_mem_criticalFace hkkt.mem_criticalFace hkkt.nonneg l) ?_ ?_
  · intro y hy
    rw [mixedLagrangian, lagrangian_eq_of_mem hy.1 l]
    exact add_le_of_nonpos_right (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hkkt.nonneg j) (hy.2 j))
  · intro z htan hfz hz
    exact hpos z (hkkt.mem_kktCriticalCone_of_tangent_of_nonpos
      (fun i => (hh i).self_of_nhds) (fun j => (hg j).self_of_nhds) htan hfz) hz

/-- Local C2 smoothness and LICQ at a constrained local minimum yield actual KKT
multipliers whose actual mixed Lagrangian Hessian is nonnegative on the critical cone. -/
theorem exists_kkt_second_of_isLocalMinOn [FiniteDimensional ℝ E]
    {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E} {U : Set E}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContDiffOn ℝ 2 f U)
    (hh : ∀ i, ContDiffOn ℝ 2 (h i) U) (hg : ∀ j, ContDiffOn ℝ 2 (g j) U)
    (hreg : IsRegularPointIneq h (fun i => fderiv ℝ (h i)) g (fun j => fderiv ℝ (g j)) x)
    (hmin : IsLocalMinOn f (feasible h g) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      IsKKTPoint (fderiv ℝ f) h (fun i => fderiv ℝ (h i)) g (fun j => fderiv ℝ (g j)) x l μ ∧
      ∀ d ∈ kktCriticalCone (fun i => fderiv ℝ (h i)) g (fun j => fderiv ℝ (g j)) x μ,
        0 ≤ fderiv ℝ (fderiv ℝ (mixedLagrangian f h g l μ)) x d d := by
  have hfn := hf.eventually_hasFDerivAt (by norm_num) hU hxU
  have hhn := fun i => (hh i).eventually_hasFDerivAt (by norm_num) hU hxU
  have hgn := fun j => (hg j).eventually_hasFDerivAt (by norm_num) hU hxU
  have hhstrict := fun i => ((hh i).contDiffAt (hU.mem_nhds hxU)).hasStrictFDerivAt (by norm_num)
  have hgstrict := fun j => ((hg j).contDiffAt (hU.mem_nhds hxU)).hasStrictFDerivAt (by norm_num)
  obtain ⟨l, μ, hkkt⟩ := exists_kkt_of_isLocalMinOn hreg hmin hfn.self_of_nhds hhstrict hgstrict
  refine ⟨l, μ, hkkt, fun d hd => ?_⟩
  have hL := contDiffOn_mixedLagrangian hf hh hg l μ
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ (mixedLagrangian f h g l μ)) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hH := ((hL'.differentiableOn (by norm_num) x hxU).differentiableAt
    (hU.mem_nhds hxU)).hasFDerivAt
  have heq : (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y +
      ∑ j, μ j • fderiv ℝ (g j) y) =ᶠ[𝓝 x] fderiv ℝ (mixedLagrangian f h g l μ) := by
    filter_upwards [hfn, eventually_all.mpr hhn, eventually_all.mpr hgn] with y hfy hhy hgy
    exact (mixedLagrangian_hasFDerivAt hfy hhy hgy l μ).fderiv.symm
  exact hkkt.nonneg_second_of_isLocalMinOn hreg hmin hfn hhn hgn hhstrict hgstrict
    (hH.congr_of_eventuallyEq heq) hd

/-- Local C2 mixed KKT strict sufficiency uses the actual mixed Lagrangian Hessian.
No constraint qualification is required. -/
theorem IsKKTPoint.isStrictLocalMinOn_of_contDiffOn_posDef_second [FiniteDimensional ℝ E]
    {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E} {U : Set E}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContDiffOn ℝ 2 f U)
    (hh : ∀ i, ContDiffOn ℝ 2 (h i) U) (hg : ∀ j, ContDiffOn ℝ 2 (g j) U)
    {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint (fderiv ℝ f) h (fun i => fderiv ℝ (h i)) g (fun j => fderiv ℝ (g j)) x l μ)
    (hpos : ∀ d ∈ kktCriticalCone (fun i => fderiv ℝ (h i)) g (fun j => fderiv ℝ (g j)) x μ,
      d ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (mixedLagrangian f h g l μ)) x d d) :
    ∃ δ > 0, ∀ y ∈ feasible h g, dist y x < δ → y ≠ x → f x < f y := by
  have hfn := hf.eventually_hasFDerivAt (by norm_num) hU hxU
  have hhn := fun i => (hh i).eventually_hasFDerivAt (by norm_num) hU hxU
  have hgn := fun j => (hg j).eventually_hasFDerivAt (by norm_num) hU hxU
  have hL := contDiffOn_mixedLagrangian hf hh hg l μ
  have hL' : ContDiffOn ℝ 1 (fderiv ℝ (mixedLagrangian f h g l μ)) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hH := ((hL'.differentiableOn (by norm_num) x hxU).differentiableAt
    (hU.mem_nhds hxU)).hasFDerivAt
  have heq : (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y +
      ∑ j, μ j • fderiv ℝ (g j) y) =ᶠ[𝓝 x] fderiv ℝ (mixedLagrangian f h g l μ) := by
    filter_upwards [hfn, eventually_all.mpr hhn, eventually_all.mpr hgn] with y hfy hhy hgy
    exact (mixedLagrangian_hasFDerivAt hfy hhy hgy l μ).fderiv.symm
  exact hkkt.isStrictLocalMinOn_of_posDef_second hfn hhn hgn (hH.congr_of_eventuallyEq heq) hpos

end Constrained
