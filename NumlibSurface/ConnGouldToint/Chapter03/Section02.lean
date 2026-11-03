import Numlib.Optimization.Optimality.Unconstrained
import Numlib.Optimization.Optimality.Clarke
import Numlib.Optimization.Descent
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.LinearInequalities
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Optimality conditions

Smooth and nonsmooth optimality conditions in Section 3.2 of [conn2000trust].
The Fréchet differential is zero exactly when the Euclidean gradient vanishes.
-/

open Set Filter Topology ConvexAnalysis
open scoped RealInnerProductSpace NNReal

namespace ConnGouldToint.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.2.1.** The differential vanishes at a differentiable unconstrained
local minimizer. -/
theorem theorem_3_2_1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 :=
  hx.hasFDerivAt_eq_zero (hf.differentiable (by norm_num) x).hasFDerivAt

/-- **AF.1.** The objective function is twice continuously differentiable. -/
abbrev AF1 (f : E → ℝ) : Prop := ContDiff ℝ 2 f

/-- **Theorem 3.2.2.** At a twice continuously differentiable unconstrained local minimizer,
the differential vanishes and the Hessian is positive semidefinite. -/
theorem theorem_3_2_2 {f : E → ℝ} (hf : AF1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 ∧ ∀ s : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => s) :=
  ⟨theorem_3_2_1 (hf.of_le (by norm_num)) hx,
    IsLocalMin.iteratedFDeriv_two_apply_self_nonneg hx hf.contDiffAt⟩

/-- **Theorem 3.2.3.** A stationary point with positive-definite Hessian is a strict
local minimizer and has a neighbourhood containing no other local minimizers. -/
theorem theorem_3_2_3 [FiniteDimensional ℝ E] {f : E → ℝ} (hf : AF1 f)
    {x : E} (hx : fderiv ℝ f x = 0)
    (hpos : ∀ s : E, s ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => s)) :
    Optimization.IsStrictLocalMin f x ∧ ∀ᶠ y in 𝓝 x, IsLocalMin f y → y = x := by
  refine ⟨Optimization.isStrictLocalMin_of_fderiv_eq_zero_of_posDef hf.contDiffAt hx hpos, ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun y _ => Subsingleton.elim y x
  let H := iteratedFDeriv ℝ 2 f
  let c := minCurvature (H x)
  obtain ⟨v, hv, hvc⟩ := exists_eq_minCurvature (H x)
  have hc : 0 < c := by
    rw [show c = H x (fun _ => v) from hvc.symm]
    exact hpos v (by rintro rfl; simp at hv)
  have hH : Continuous H := hf.continuous_iteratedFDeriv'
  have hclose : ∀ᶠ z in 𝓝 x, dist (H z) (H x) < c :=
    hH.continuousAt (Metric.ball_mem_nhds (H x) hc)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hclose
  have hcurv (z : E) (hz : dist z x < r) : 0 < minCurvature (H z) := by
    have h := abs_minCurvature_sub_le (A := H z) (B := H x)
    have h' := hball (y := z) hz
    rw [dist_eq_norm] at h'
    linarith [neg_abs_le (minCurvature (H z) - minCurvature (H x))]
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy hymin
  by_contra hyx
  let d := y - x
  let g : ℝ → ℝ := fun t => fderiv ℝ f (x + t • d) d
  have hd : ∀ t : ℝ, HasDerivAt g (fderiv ℝ (fderiv ℝ f) (x + t • d) d d) t := by
    intro t
    have hseg : HasDerivAt (fun u : ℝ => x + u • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have h := hF.differentiable (by norm_num) (x + t • d)
    simpa [g] using (h.hasFDerivAt.comp_hasDerivAt t hseg).clm_apply (hasDerivAt_const t d)
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope g (by norm_num : (0 : ℝ) < 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
  have hnear : dist (x + t • d) x < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
    have hy' : ‖d‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, d] using hy
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2.le).trans_lt hy'
  have hdpos : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hyx)) _
  have hdiag : 0 < H (x + t • d) (fun _ => d) :=
    (mul_pos (hcurv _ hnear) hdpos).trans_le (minCurvature_mul_norm_sq_le _ _)
  have hstat := theorem_3_2_1 (hf.of_le (by norm_num)) hymin
  have hy' : x + d = y := by dsimp [d]; abel
  rw [(hd t).deriv] at he
  simp only [g, one_smul, zero_smul, add_zero, hy', hstat, hx,
    zero_apply, sub_zero, zero_div] at he
  exact hdiag.ne' (by simpa [H, iteratedFDeriv_two_apply] using he)

section ConvexNonsmooth

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **AC.2.** The feasible set is nonempty, closed, and convex. -/
def AC2 (C : Set V) : Prop := C.Nonempty ∧ IsClosed C ∧ Convex ℝ C

/-- **Theorem 3.2.9.** If the first-order directional inequality holds on the
feasible tangent cone, the negative gradient is normal to the convex feasible set.
Once criticality is expressed on the feasible tangent cone, the constraint qualification
used to pass from algebraic stationarity to that inequality is no longer needed. -/
theorem theorem_3_2_9 [CompleteSpace V] {C : Set V} (hC : AC2 C) {f : V → ℝ} {x : V} (hx : x ∈ C)
    (hcrit : ∀ d ∈ posTangentConeAt C x, 0 ≤ fderiv ℝ f x d) :
    -gradient f x ∈ normalCone (innerₗ V) C x := by
  rw [mem_normalCone]
  intro z hz
  have htan := sub_mem_posTangentConeAt_of_segment_subset (hC.2.2.segment_subset hx hz)
  simpa [innerₗ_apply_apply] using hcrit (z - x) htan

/-- **AC.7.** The feasible set is the intersection of finitely many superlevel sets. -/
def AC7 {ι : Type*} [Fintype ι] (C : Set V) (c : ι → V → ℝ) : Prop :=
  C = {x | ∀ i, 0 ≤ c i x}

/-- A first-order constraint qualification for inequality constraints. The actual
feasible tangent cone agrees with the cone of active linearized inequalities. -/
def ActiveLinearizedConeMatches {ι : Type*} (C : Set V) (c : ι → V → ℝ) (x : V) : Prop :=
  ∀ d : V, d ∈ posTangentConeAt C x ↔ ∀ i, c i x = 0 → 0 ≤ fderiv ℝ (c i) x d

/-- **Theorem 3.2.10 (normal-cone formula).** Under the active linearization
qualification the normal cone is generated by the outward active gradients. -/
theorem theorem_3_2_10_normalCone [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    {x : V} (hx : ∀ i, 0 ≤ c i x) (hQ : ActiveLinearizedConeMatches C c x) (g : V) :
    g ∈ normalCone (innerₗ V) C x ↔
      ∃ a : {i // c i x = 0} → ℝ, (∀ i, 0 ≤ a i) ∧
        ∑ i, a i • (-gradient (c i) x) = g := by
  classical
  let b (i : {i // c i x = 0}) := -gradient (c i) x
  rw [← ConvexAnalysis.farkas (B := innerₗ V) b g]
  have hxC : x ∈ C := by rw [hset]; exact hx
  have hlin (d : V) :
      (∀ i, innerₗ V d (b i) ≤ 0) ↔ d ∈ posTangentConeAt C x := by
    rw [hQ d]
    simp [b, innerₗ_apply_apply]
  constructor
  · intro hn d hd
    have hmax : IsMaxOn (fun y : V => ⟪g, y⟫) C x := by
      intro y hy
      have h := hn y hy
      simp only [innerₗ_apply_apply, inner_sub_left, sub_nonpos] at h
      change ⟪g, y⟫ ≤ ⟪g, x⟫
      simpa only [real_inner_comm g] using h
    have hder : HasFDerivAt (fun y : V => ⟪g, y⟫) (innerSL ℝ g) x :=
      (innerSL ℝ g).hasFDerivAt
    have hg := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hder.hasFDerivWithinAt ((hlin d).1 hd)
    simpa [innerₗ_apply_apply, real_inner_comm] using hg
  · intro hp z hz
    have hz' := sub_mem_posTangentConeAt_of_segment_subset (hC.2.2.segment_subset hxC hz)
    exact hp (z - x) ((hlin _).2 hz')

/-- The normal-cone graph is closed, giving the outer-limit part of continuity
in Theorem 3.2.10. -/
theorem isClosed_normalCone_graph (C : Set V) :
    IsClosed {p : V × V | p.2 ∈ normalCone (innerₗ V) C p.1} := by
  have he : {p : V × V | p.2 ∈ normalCone (innerₗ V) C p.1} =
      ⋂ z : C, {p : V × V | ⟪(z : V) - p.1, p.2⟫ ≤ 0} := by
    ext p
    simp [mem_normalCone, innerₗ_apply_apply, inner_sub_left]
  rw [he]
  exact isClosed_iInter fun z =>
    isClosed_le ((continuous_const.sub continuous_fst).inner continuous_snd) continuous_const

/-- The inner-limit part of normal-cone continuity in Theorem 3.2.10. Within a
face of fixed active constraints, each normal vector can be continued by the same
coefficients in the active gradients. -/
theorem continuous_normal_selection_on_active_face [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    (hc : ∀ i, ContDiff ℝ 1 (c i)) {x : V} (hx : ∀ i, 0 ≤ c i x)
    (hQ : ActiveLinearizedConeMatches C c x) {g : V} (hg : g ∈ normalCone (innerₗ V) C x) :
    ∃ G : V → V, Continuous G ∧ G x = g ∧
      ∀ z, (∀ i, 0 ≤ c i z) → (∀ i, c i z = 0 ↔ c i x = 0) →
        ActiveLinearizedConeMatches C c z → G z ∈ normalCone (innerₗ V) C z := by
  classical
  obtain ⟨a, ha, hax⟩ := (theorem_3_2_10_normalCone hC hset hx hQ g).1 hg
  let G (z : V) := ∑ i : {i // c i x = 0}, a i • (-gradient (c i) z)
  have hcont (i : ι) : Continuous (gradient (c i)) :=
    (InnerProductSpace.toDual ℝ V).symm.continuous.comp ((hc i).continuous_fderiv one_ne_zero)
  refine ⟨G, continuous_finsetSum _ fun i _ => (hcont i).neg.const_smul (a i), hax, ?_⟩
  intro z hz hface hzQ
  apply (theorem_3_2_10_normalCone hC hset hz hzQ (G z)).2
  let e : {i // c i x = 0} ≃ {i // c i z = 0} :=
    Equiv.subtypeEquivRight fun i => (hface i).symm
  refine ⟨fun i => a (e.symm i), fun i => ha (e.symm i), ?_⟩
  rw [← Equiv.sum_comp e]
  simp [G, e]

/-- **Theorem 3.2.12.** At a locally Lipschitz local minimizer, zero is a Clarke
subgradient and every Clarke directional derivative is nonnegative. The derivative
is the support function of the Clarke subdifferential. -/
theorem theorem_3_2_12 [CompleteSpace V] {f : V → ℝ} {x : V} (hmin : IsLocalMin f x)
    {U : Set V} {L : ℝ≥0} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    0 ∈ Optimization.clarkeSubgradient f x ∧
      (∀ d, 0 ≤ Optimization.clarkeDerivative f x d) ∧ Optimization.HasClarkeSupport f x := by
  have hd (d : V) : 0 ≤ Optimization.clarkeDerivative f x d := by
    apply Optimization.le_clarkeDerivative_of_eventually_base_quotient_ge hU hL
    have ht : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := x)).add
        (ht₀.smul (tendsto_const_nhds (x := d)))
    filter_upwards [ht.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    exact div_nonneg (sub_nonneg.2 ht) htpos.le
  refine ⟨?_, hd, Optimization.hasClarkeSupport_of_lipschitzOnWith hU hL⟩
  intro d
  simpa using hd d

private theorem composite_linearized_clarke_nonneg
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hmin : IsLocalMin (fun z => f z + h (c z)) x)
    {U : Set W} {L : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hL : LipschitzOnWith L h U) (d : V) :
    0 ≤ fderiv ℝ f x d + Optimization.clarkeDerivative h (c x) (fderiv ℝ c x d) := by
  let g (t : ℝ) := x + t • d
  let v := fderiv ℝ c x d
  let F := fderiv ℝ f x d
  have hg : HasDerivAt g d 0 := by
    simpa [g] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have htg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa [g] using hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = x := by simp [g]
  have htf : Tendsto (fun t : ℝ => (f (g t) - f x) / t) (𝓝[>] 0) (𝓝 F) := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (g 0) := by simpa only [hg0] using hf.hasFDerivAt
    have hd := (hf'.comp_hasDerivAt (0 : ℝ) hg).tendsto_slope_zero_right
    simpa [Function.comp_def, g, F, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have htc : Tendsto (fun t : ℝ => t⁻¹ • (c (g t) - c x)) (𝓝[>] 0) (𝓝 v) := by
    have hc' : HasFDerivAt c (fderiv ℝ c x) (g 0) := by simpa only [hg0] using hc.hasFDerivAt
    have hd := (hc'.comp_hasDerivAt (0 : ℝ) hg).tendsto_slope_zero_right
    simpa [Function.comp_def, g, v] using hd
  have hte : Tendsto (fun t : ℝ => (L : ℝ) * ‖t⁻¹ • (c (g t) - c x) - v‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((htc.sub (tendsto_const_nhds (x := v))).norm.const_mul (L : ℝ))
  have htm : Tendsto (fun t : ℝ => c x + t • v) (𝓝[>] 0) (𝓝 (c x)) := by
    have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := c x)).add
      (ht₀.smul (tendsto_const_nhds (x := v)))
  change 0 ≤ F + Optimization.clarkeDerivative h (c x) v
  by_contra! hneg
  let ε := -(F + Optimization.clarkeDerivative h (c x) v) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlow : -F - ε ≤ Optimization.clarkeDerivative h (c x) v := by
    apply Optimization.le_clarkeDerivative_of_eventually_base_quotient_ge hU hL
    filter_upwards [htg.eventually hmin, htf.eventually_lt_const (by linarith : F < F + ε / 2),
      hte.eventually_lt_const (half_pos hε), (hc.continuousAt.tendsto.comp htg).eventually hU,
      htm.eventually hU, self_mem_nhdsWithin] with t hm hft het hct hmt ht
    change 0 < t at ht
    have hnorm : ‖t⁻¹ • (c (g t) - c x) - v‖ = ‖c (g t) - (c x + t • v)‖ / t := by
      have heq : t⁻¹ • (c (g t) - c x) - v = t⁻¹ • (c (g t) - (c x + t • v)) := by
        rw [show c (g t) - (c x + t • v) = (c (g t) - c x) - t • v by abel]
        simp only [smul_sub, inv_smul_smul₀ ht.ne']
      rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_eq_mul_inv, mul_comm]
    have hLip := hL.dist_le_mul _ hct _ hmt
    rw [Real.dist_eq, dist_eq_norm] at hLip
    have herr : (h (c (g t)) - h (c x + t • v)) / t ≤
        (L : ℝ) * ‖t⁻¹ • (c (g t) - c x) - v‖ := by
      rw [hnorm, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right ((le_abs_self _).trans hLip) ht.le
    have hq : 0 ≤ (f (g t) - f x) / t + (h (c (g t)) - h (c x)) / t := by
      change f x + h (c x) ≤ f (g t) + h (c (g t)) at hm
      rw [← add_div]
      exact div_nonneg (by linarith) ht.le
    have hs : (h (c (g t)) - h (c x)) / t =
        (h (c (g t)) - h (c x + t • v)) / t + (h (c x + t • v) - h (c x)) / t := by ring
    rw [hs] at hq
    linarith
  dsimp [ε] at hlow
  linarith

/-- **Corollary 3.2.13.** At a local minimum of the smooth composite, an outer Clarke
subgradient cancels the smooth gradient after pullback by the Jacobian.
The associated support inequality uses the linearized composite and does not identify
its support function with the Clarke derivative of the composite itself. -/
theorem corollary_3_2_13 [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hmin : IsLocalMin (fun z => f z + h (c z)) x)
    {U : Set W} {L : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hL : LipschitzOnWith L h U) :
    (∃ y ∈ Optimization.clarkeSubgradient h (c x),
      gradient f x + (fderiv ℝ c x).adjoint y = 0) ∧
      ∀ d, 0 ≤ fderiv ℝ f x d + Optimization.clarkeDerivative h (c x) (fderiv ℝ c x d) := by
  let K := Optimization.clarkeSubgradient h (c x)
  let J := (fderiv ℝ c x).adjoint
  let P := (fun y => gradient f x + J y) '' K
  have hK := Optimization.isCompact_clarkeSubgradient hU hL
  have hP : IsClosed P := (hK.image (continuous_const.add J.continuous)).isClosed
  have hcP : Convex ℝ P := by
    intro a ha b hb s t hs ht hst
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    refine ⟨s • u + t • v, Optimization.convex_clarkeSubgradient h (c x) hu hv hs ht hst, ?_⟩
    simp only [map_add, map_smul, smul_add]
    have he : gradient f x = s • gradient f x + t • gradient f x := by
      rw [← add_smul, hst, one_smul]
    conv_lhs => rw [he]
    abel
  have hsupp := Optimization.hasClarkeSupport_of_lipschitzOnWith hU hL
  have hzero : (0 : V) ∈ P := by
    rw [← hP.closure_eq, ← hcP.convexHull_eq]
    apply (mem_closure_convexHull_iff_le_supportFn (B := innerₗ V) P 0).2
    intro d
    let v := fderiv ℝ c x d
    have hcont : Continuous (fun z : W => ⟪z, v⟫) := continuous_id.inner continuous_const
    obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn hsupp.nonempty hcont.continuousOn
    have houter : Optimization.clarkeDerivative h (c x) v ≤ ⟪y, v⟫ := by
      have hle := (supportFn_le_coe_iff (B := innerₗ W) (s := K) (y := v)).2
        (fun z hz => hymax hz)
      rw [hsupp v] at hle
      exact EReal.coe_le_coe_iff.1 hle
    have hdir := composite_linearized_clarke_nonneg hf hc hmin hU hL d
    have hpair : 0 ≤ ⟪gradient f x + J y, d⟫ := by
      rw [inner_add_left, inner_gradient_left, ContinuousLinearMap.adjoint_inner_left]
      exact hdir.trans (add_le_add_right houter _)
    have hmem : gradient f x + J y ∈ P := ⟨y, hy, rfl⟩
    have hcoe : ((0 : ℝ) : EReal) ≤ ((⟪gradient f x + J y, d⟫ : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 hpair
    simpa only [innerₗ_apply_apply, inner_zero_left] using
      hcoe.trans (le_supportFn (B := innerₗ V) hmem d)
  exact ⟨hzero, composite_linearized_clarke_nonneg hf hc hmin hU hL⟩

/-- The ambient Clarke derivative can exceed the Clarke derivative of a restriction
to a line, even when the restriction is constant and the embedding is linear. -/
theorem clarke_composite_equality_counterexample :
    ∃ (h : EuclideanSpace ℝ (Fin 2) → ℝ) (d : EuclideanSpace ℝ (Fin 2)),
      LipschitzWith 4 h ∧
      Optimization.clarkeDerivative (fun t : ℝ => h (t • d)) 0 1 = 0 ∧
      2 ≤ Optimization.clarkeDerivative h 0 d := by
  let h (p : EuclideanSpace ℝ (Fin 2)) := |p 0 + p 1| - |p 0 - p 1|
  let d : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let e : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hL : LipschitzWith 4 h := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have hb (i : Fin 2) : |p i - q i| ≤ dist p q := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) i
    have hplus : |(p 0 + p 1) - (q 0 + q 1)| ≤ 2 * dist p q := by
      rw [show (p 0 + p 1) - (q 0 + q 1) = (p 0 - q 0) + (p 1 - q 1) by ring]
      linarith [abs_add_le (p 0 - q 0) (p 1 - q 1), hb 0, hb 1]
    have hminus : |(p 0 - p 1) - (q 0 - q 1)| ≤ 2 * dist p q := by
      rw [show (p 0 - p 1) - (q 0 - q 1) = (p 0 - q 0) - (p 1 - q 1) by ring]
      linarith [abs_sub (p 0 - q 0) (p 1 - q 1), hb 0, hb 1]
    rw [Real.dist_eq]
    change |h p - h q| ≤ 4 * dist p q
    rw [show h p - h q =
      (|p 0 + p 1| - |q 0 + q 1|) - (|p 0 - p 1| - |q 0 - q 1|) by dsimp [h]; ring]
    exact (abs_sub _ _).trans (by
      linarith [(abs_abs_sub_abs_le_abs_sub (p 0 + p 1) (q 0 + q 1)).trans hplus,
        (abs_abs_sub_abs_le_abs_sub (p 0 - p 1) (q 0 - q 1)).trans hminus])
  refine ⟨h, d, hL, ?_, ?_⟩
  · have hz : (fun t : ℝ => h (t • d)) = fun _ => 0 := by
      funext t
      simp [h, d, PiLp.smul_apply]
    rw [hz]
    exact Optimization.clarkeDerivative_const 0 0 1
  · have ht₀ : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have hy : Tendsto (fun t : ℝ => (2 * t) • e) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ht₀.const_mul 2).smul (tendsto_const_nhds (x := e))
    apply Optimization.le_clarkeDerivative_of_eventually_path_quotient_ge
      (U := Set.univ) univ_mem hL.lipschitzOnWith hy
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h1 : h ((2 * t) • e + t • d) = 2 * t := by
      simp [h, d, e, PiLp.smul_apply, PiLp.add_apply]
      rw [abs_of_nonneg (by linarith : 0 ≤ t + 2 * t),
        abs_of_nonpos (by linarith : t - 2 * t ≤ 0)]
      ring
    have h2 : h ((2 * t) • e) = 0 := by simp [h, e, PiLp.smul_apply]
    rw [h1, h2, sub_zero]
    exact (le_div_iff₀ ht).2 le_rfl

end ConvexNonsmooth

end ConnGouldToint.Chapter03
