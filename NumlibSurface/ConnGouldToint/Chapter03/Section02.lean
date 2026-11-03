import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Numlib.Analysis.Convex.LinearInequalities
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Optimization.Constrained.SecondOrder
import Numlib.Optimization.Descent
import Numlib.Optimization.Optimality.Clarke
import Numlib.Optimization.Optimality.ConvexSet
import Numlib.Optimization.Optimality.Unconstrained

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

private theorem upperHemicontinuous_inter_compact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} {K : Set Y} (hK : IsCompact K)
    (hF : IsClosed {p : X × Y | p.2 ∈ F p.1}) :
    UpperHemicontinuous (fun x ↦ F x ∩ K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply upperHemicontinuous_iff_forall_isOpen.mpr
  intro x U hU hx
  let D : Set (X × K) := {p | (p.2 : Y) ∈ F p.1 ∧ (p.2 : Y) ∈ Uᶜ}
  have hD : IsClosed D := (hF.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).inter
    (hU.isClosed_compl.preimage (continuous_subtype_val.comp continuous_snd))
  have hclosed := (isClosedMap_fst_of_compactSpace (X := X) (Y := K)) D hD
  have hx' : x ∈ (Prod.fst '' D)ᶜ := by
    rintro ⟨⟨y, v⟩, hv, rfl⟩
    exact hv.2 (hx ⟨hv.1, v.property⟩)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx'] with y hy
  intro v hv
  by_contra hvU
  exact hy ⟨(y, ⟨v, hv.2⟩), ⟨hv.1, hvU⟩, rfl⟩

private theorem lowerHemicontinuous_inter_closedBall_of_smul
    {X : Type*} [TopologicalSpace X] {F : X → Set V}
    (hF : LowerHemicontinuous F)
    (hsmul : ∀ x (a : ℝ), 0 ≤ a → ∀ d ∈ F x, a • d ∈ F x)
    {R : ℝ} (hR : 0 < R) :
    LowerHemicontinuous (fun x ↦ F x ∩ Metric.closedBall 0 R) := by
  apply lowerHemicontinuous_iff.mpr
  intro x
  apply lowerHemicontinuousAt_iff.mpr
  intro U hU hhit
  obtain ⟨d, ⟨hdF, hdB⟩, hdU⟩ := hhit
  have hlim : Tendsto (fun a : ℝ ↦ a • d) (𝓝[<] (1 : ℝ)) (𝓝 d) := by
    have ht : Tendsto (fun a : ℝ ↦ a) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using ht.smul (tendsto_const_nhds (x := d))
  obtain ⟨a, haU, ha⟩ := ((hlim.eventually (hU.mem_nhds hdU)).and
    (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))).exists
  have had : a • d ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.1.le]
    have hdR : ‖d‖ ≤ R := by simpa [Metric.mem_closedBall] using hdB
    exact (mul_le_mul_of_nonneg_left hdR ha.1.le).trans_lt
      (by simpa using mul_lt_mul_of_pos_right ha.2 hR)
  have hhit' : (F x ∩ (U ∩ Metric.ball 0 R)).Nonempty :=
    ⟨a • d, hsmul x a ha.1.le d hdF, haU, had⟩
  filter_upwards [(lowerHemicontinuousAt_iff.mp (lowerHemicontinuous_iff.mp hF x))
    (U ∩ Metric.ball 0 R) (hU.inter Metric.isOpen_ball) hhit'] with y hy
  obtain ⟨z, hz, hzU, hzR⟩ := hy
  exact ⟨z, ⟨hz, Metric.ball_subset_closedBall hzR⟩, hzU⟩

/-- Theorem 3.2.10, continuity on a fixed active face. Both the outward normal cone
and the feasible positive tangent cone have continuous bounded sections, expressed
by upper and lower hemicontinuity after intersection with any positive-radius closed
ball. The bounded sections give the usual local convergence of closed cones. -/
theorem theorem_3_2_10_face_continuity [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {C : Set V} {c : ι → V → ℝ} (hC : AC2 C) (hset : AC7 C c)
    (hc : ∀ i, ContDiff ℝ 1 (c i)) (x₀ : V) {R : ℝ} (hR : 0 < R) :
    let S := {z : V | (∀ i, 0 ≤ c i z) ∧ (∀ i, c i z = 0 ↔ c i x₀ = 0) ∧
      ActiveLinearizedConeMatches C c z}
    let N := fun z : S ↦ normalCone (innerₗ V) C (z : V) ∩ Metric.closedBall 0 R
    let T := fun z : S ↦ posTangentConeAt C (z : V) ∩ Metric.closedBall 0 R
    UpperHemicontinuous N ∧ LowerHemicontinuous N ∧ UpperHemicontinuous T ∧ LowerHemicontinuous T := by
  classical
  intro S N T
  let N₀ (z : S) := normalCone (innerₗ V) C (z : V)
  let T₀ (z : S) := posTangentConeAt C (z : V)
  have hmemC (z : S) : (z : V) ∈ C := by
    rw [hset]
    exact z.property.1
  have hnclosed : IsClosed {p : S × V | p.2 ∈ N₀ p.1} :=
    (isClosed_normalCone_graph C).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have htclosed : IsClosed {p : S × V | p.2 ∈ T₀ p.1} := by
    have heq : {p : S × V | p.2 ∈ T₀ p.1} =
        ⋂ i : {i // c i x₀ = 0}, {p : S × V | 0 ≤ fderiv ℝ (c i) (p.1 : V) p.2} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, T₀]
      rw [p.1.property.2.2 p.2]
      constructor
      · exact fun h i ↦ h i ((p.1.property.2.1 i).mpr i.property)
      · exact fun h i hi ↦ h ⟨i, (p.1.property.2.1 i).mp hi⟩
    rw [heq]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const
      ((((hc i).continuous_fderiv one_ne_zero).comp
        (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd)
  have hNlow : LowerHemicontinuous N₀ := by
    apply lowerHemicontinuous_iff.mpr
    intro x
    apply lowerHemicontinuousAt_iff.mpr
    intro U hU hmeet
    obtain ⟨g, hg, hgU⟩ := hmeet
    obtain ⟨G, hG, hGx, hGN⟩ :=
      continuous_normal_selection_on_active_face hC hset hc x.property.1 x.property.2.2 hg
    have hcont : Continuous (fun z : S ↦ G (z : V)) := hG.comp continuous_subtype_val
    have hGmem : ∀ z : S, G z ∈ N₀ z := fun z ↦
      hGN z z.property.1 (fun i ↦ (z.property.2.1 i).trans (x.property.2.1 i).symm)
        z.property.2.2
    have hu : (G (x : V)) ∈ U := hGx.symm ▸ hgU
    filter_upwards [(hcont.tendsto x).eventually (hU.mem_nhds hu)] with z hz
    exact ⟨G z, hGmem z, hz⟩
  have hTlow : LowerHemicontinuous T₀ := by
    apply lowerHemicontinuous_iff.mpr
    intro x
    apply lowerHemicontinuousAt_iff.mpr
    intro U hU hmeet
    obtain ⟨d, hd, hdU⟩ := hmeet
    obtain ⟨α, l, hl, a, w, hw₀, hwC, hlim⟩ := exists_fun_of_mem_tangentConeAt hd
    let : l.NeBot := hl
    obtain ⟨j, hjC, hjU⟩ := (hwC.and (hlim.eventually (hU.mem_nhds hdU))).exists
    let y : V := (x : V) + w j
    let G (z : S) : V := (a j : ℝ) • (y - (z : V))
    have hG : Continuous G := (continuous_const.sub continuous_subtype_val).const_smul _
    have hGx : G x ∈ U := by
      simpa [G, y, NNReal.smul_def] using hjU
    have hGmem (z : S) : G z ∈ T₀ z := by
      have htan := sub_mem_posTangentConeAt_of_segment_subset
        (hC.2.2.segment_subset (hmemC z) hjC)
      apply (z.property.2.2 _).mpr
      intro i hi
      rw [show G z = (a j : ℝ) • (y - (z : V)) from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg (a j).coe_nonneg ((z.property.2.2 _).mp htan i hi)
    filter_upwards [(hG.tendsto x).eventually (hU.mem_nhds hGx)] with z hz
    exact ⟨G z, hGmem z, hz⟩
  let : ProperSpace V := FiniteDimensional.proper_real V
  refine ⟨upperHemicontinuous_inter_compact (isCompact_closedBall _ _) hnclosed,
    lowerHemicontinuous_inter_closedBall_of_smul hNlow ?_ hR,
    upperHemicontinuous_inter_compact (isCompact_closedBall _ _) htclosed,
    lowerHemicontinuous_inter_closedBall_of_smul hTlow ?_ hR⟩
  · intro z a ha d hd y hy
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hd y hy)
  · intro z a ha d hd
    apply (z.property.2.2 _).mpr
    intro i hi
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg ha ((z.property.2.2 _).mp hd i hi)

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


/-- Theorem 3.2.4 under the tangent inclusion form of AO.1.
The inequality multipliers are nonnegative for constraints written `cᵢ ≥ 0`. -/
theorem theorem_3_2_4 [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : E → ℝ} {ce : ι → E → ℝ} {ci : κ → E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hx : x ∈ Constrained.feasible ce (fun i y ↦ -ci i y))
    (hQ : ∀ d : E, (∀ i, fderiv ℝ (ce i) x d = 0) →
      (∀ i, ci i x = 0 → 0 ≤ fderiv ℝ (ci i) x d) →
      d ∈ posTangentConeAt (Constrained.feasible ce (fun i y ↦ -ci i y)) x)
    (hmin : IsLocalMinOn f (Constrained.feasible ce (fun i y ↦ -ci i y)) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      fderiv ℝ f x = (∑ i, l i • fderiv ℝ (ce i) x) + ∑ i, μ i • fderiv ℝ (ci i) x ∧
      (∀ i, ce i x = 0) ∧ (∀ i, 0 ≤ ci i x ∧ 0 ≤ μ i ∧ ci i x * μ i = 0) := by
  obtain ⟨l, μ, h⟩ := Constrained.exists_kkt_of_linearized_feasible_directions
    (f' := fderiv ℝ f) (h' := fun i ↦ fderiv ℝ (ce i)) (g' := fun i y ↦ -fderiv ℝ (ci i) y)
    hx fun d hd₁ hd₂ ↦ hmin.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt
      (hQ d hd₁ fun i hi ↦ by simpa using hd₂ i (by simp [Constrained.activeSet, hi]))
  refine ⟨-l, μ, ?_, h.feasible_eq, fun i ↦ ⟨by simpa using h.feasible_ineq i, h.nonneg i, ?_⟩⟩
  · have hs := h.stationary
    simp only [smul_neg, Finset.sum_neg_distrib] at hs
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    apply sub_eq_zero.mp
    calc
      _ = fderiv ℝ f x + (∑ i, l i • fderiv ℝ (ce i) x) -
          ∑ i, μ i • fderiv ℝ (ci i) x := by abel
      _ = 0 := by simpa [sub_eq_add_neg] using hs
  · have hp := h.complementary i
    simpa [mul_comm] using hp

section SmoothSecondOrder

open Constrained

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [FiniteDimensional ℝ E]

/-- Theorem 3.2.5 under LICQ, which supplies both constraint qualifications.
The inequalities are written as `g ≤ 0`, so the inequality part of the
Lagrangian is added. Negating the textbook's constraints yields this convention. -/
theorem theorem_3_2_5 {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hreg : IsRegularPointIneq h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x)
    (hmin : IsLocalMinOn f (feasible h g) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      IsKKTPoint (fderiv ℝ f) h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x l μ ∧
      ∀ d ∈ criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ,
        0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d) :=
  secondOrder_necessary_ineq hreg hmin hf hh hg
    (fun i ↦ ((hh i).differentiableAt (by norm_num)).hasFDerivAt)
    (fun j ↦ ((hg j).differentiableAt (by norm_num)).hasFDerivAt)

/-- Theorem 3.2.6. KKT and positive Lagrangian curvature on the nonzero critical
directions suffice for a strict constrained local minimum. -/
theorem theorem_3_2_6 {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E}
    {l : ι → ℝ} {μ : κ → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hkkt : IsKKTPoint (fderiv ℝ f) h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x l μ)
    (hpos : ∀ d ∈ criticalCone (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x μ,
      d ≠ 0 → 0 < iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d)) :
    Optimization.IsStrictLocalMinOn f (feasible h g) x :=
  isStrictLocalMinOn_of_secondOrder_sufficient hkkt hf hh hg
    (hf.differentiableAt (by norm_num)).hasFDerivAt
    (fun i ↦ ((hh i).differentiableAt (by norm_num)).hasFDerivAt)
    (fun j ↦ ((hg j).differentiableAt (by norm_num)).hasFDerivAt) hpos

end SmoothSecondOrder

section ActiveKKTSensitivity

variable {V Y P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

open ContinuousLinearMap

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Y] in
/-- Linearization of the active KKT equations with the positive multiplier sign
in the Lagrangian. A multiplier sign change yields the textbook convention. -/
noncomputable def activeKKTLinearization (A : V →L[ℝ] Y) (H : V →L[ℝ] V) :
    (V × Y) →L[ℝ] (V × Y) :=
  (H.comp (fst ℝ V Y) + A.adjoint.comp (snd ℝ V Y)).prod (A.comp (fst ℝ V Y))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Y] in
/-- The active KKT block maps a primal-dual direction to its stationarity and feasibility terms. -/
@[simp] theorem activeKKTLinearization_apply (A : V →L[ℝ] Y) (H : V →L[ℝ] V)
    (z : V × Y) : activeKKTLinearization A H z = (H z.1 + A.adjoint z.2, A z.1) := rfl

/-- The active KKT block is invertible under the rank and reduced-Hessian
conditions of Theorem 3.2.7. -/
theorem theorem_3_2_7_activeKKT_invertible {A : V →L[ℝ] Y} {H : V →L[ℝ] V}
    (hA : Function.Surjective A) (hH : ∀ d : V, A d = 0 → d ≠ 0 → 0 < ⟪H d, d⟫) :
    (activeKKTLinearization A H).IsInvertible := by
  let B := activeKKTLinearization A H
  have hinj : Function.Injective B := (injective_iff_map_eq_zero B).mpr fun z hz ↦ by
    have h₁ : H z.1 + A.adjoint z.2 = 0 := congrArg Prod.fst hz
    have h₂ : A z.1 = 0 := congrArg Prod.snd hz
    have hv : z.1 = 0 := by
      by_contra hne
      have heq := congrArg (fun v : V ↦ ⟪v, z.1⟫) h₁
      simp only [inner_add_left, ContinuousLinearMap.adjoint_inner_left, h₂, inner_zero_right,
        add_zero, inner_zero_left] at heq
      exact (hH z.1 h₂ hne).ne' heq
    have hμ : A.adjoint z.2 = 0 := by simpa [hv] using h₁
    obtain ⟨v, hv'⟩ := hA z.2
    have hμ' : ⟪z.2, z.2⟫ = 0 := by
      calc
        _ = ⟪A.adjoint z.2, v⟫ := by rw [ContinuousLinearMap.adjoint_inner_left, hv']
        _ = 0 := by rw [hμ, inner_zero_left]
    exact Prod.ext hv (inner_self_eq_zero.mp hμ')
  have hsurj : Function.Surjective B := LinearMap.surjective_of_injective
    (f := B.toLinearMap) hinj
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective ..⟩

/-- The rank and reduced-Hessian conditions in Theorem 3.2.7 are open in the
active Jacobian and Hessian. Compactness of the unit sphere handles the varying
kernel of the active Jacobian. -/
theorem theorem_3_2_7_activeKKT_conditions_open :
    IsOpen {p : (V →L[ℝ] Y) × (V →L[ℝ] V) | Function.Surjective p.1 ∧
      ∀ d : V, p.1 d = 0 → d ≠ 0 → 0 < ⟪p.2 d, d⟫} := by
  let X := (V →L[ℝ] Y) × (V →L[ℝ] V)
  let K := Metric.sphere (0 : V) 1
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let D : Set (X × K) := {q | q.1.1 (q.2 : V) = 0 ∧ ⟪q.1.2 (q.2 : V), (q.2 : V)⟫ ≤ 0}
  have hval : Continuous (fun q : X × K ↦ (q.2 : V)) :=
    continuous_subtype_val.comp continuous_snd
  have hAz : Continuous (fun q : X × K ↦ q.1.1 (q.2 : V)) :=
    (continuous_fst.comp continuous_fst).clm_apply hval
  have hHz : Continuous (fun q : X × K ↦ ⟪q.1.2 (q.2 : V), (q.2 : V)⟫) :=
    ((continuous_snd.comp continuous_fst).clm_apply hval).inner hval
  have hD : IsClosed D := (isClosed_eq hAz (continuous_const (y := (0 : Y)))).inter
    (isClosed_le hHz (continuous_const (y := (0 : ℝ))))
  have hbad := (isClosedMap_fst_of_compactSpace (X := X) (Y := K)) D hD
  have hB : Continuous (fun p : X ↦ activeKKTLinearization p.1 p.2) := by
    let i : V →L[ℝ] V × Y := inl ℝ V Y
    let j : Y →L[ℝ] V × Y := inr ℝ V Y
    let u : V × Y →L[ℝ] V := fst ℝ V Y
    let v : V × Y →L[ℝ] Y := snd ℝ V Y
    have heq : (fun p : X ↦ activeKKTLinearization p.1 p.2) =
        fun p ↦ i.comp (p.2.comp u) + i.comp (p.1.adjoint.comp v) + j.comp (p.1.comp u) := by
      funext p
      ext w <;> simp [i, j, u, v]
    rw [heq]
    exact ((continuous_const.clm_comp (continuous_snd.clm_comp continuous_const)).add
      (continuous_const.clm_comp
        ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_comp continuous_const))).add
      (continuous_const.clm_comp (continuous_fst.clm_comp continuous_const))
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp' : p ∈ (Prod.fst '' D)ᶜ := by
    rintro ⟨⟨q, d⟩, hd, rfl⟩
    have hnorm : ‖(d : V)‖ = 1 := mem_sphere_zero_iff_norm.mp d.property
    have hdne : (d : V) ≠ 0 := by intro hz; simp [hz] at hnorm
    exact (not_le_of_gt (hp.2 d hd.1 hdne)) hd.2
  have hinv := theorem_3_2_7_activeKKT_invertible hp.1 hp.2
  filter_upwards [hbad.isOpen_compl.mem_nhds hp',
    (hB.tendsto p).eventually hinv.eventually_nhds] with q hq hqB
  refine ⟨?_, ?_⟩
  · intro b
    obtain ⟨e, he⟩ := hqB
    obtain ⟨z, hz⟩ := e.surjective (0, b)
    refine ⟨z.1, ?_⟩
    have hb := congrArg Prod.snd hz
    change ((e : (V × Y) →L[ℝ] V × Y) z).2 = b at hb
    rwa [he, activeKKTLinearization_apply] at hb
  · intro d hd hdne
    by_contra! hnon
    let a := ‖d‖⁻¹
    have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr hdne)
    let v : K := ⟨a • d, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdne))⟩
    apply hq
    refine ⟨(q, v), ⟨?_, ?_⟩, rfl⟩
    · change q.1 (a • d) = 0
      rw [map_smul, hd, smul_zero]
    · change ⟪q.2 (a • d), a • d⟫ ≤ 0
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos ha.le (mul_nonpos_of_nonneg_of_nonpos ha.le hnon)

/-- The local fixed-active-set continuation in Theorem 3.2.7. If the residual
of the active KKT equations is jointly `C¹` and its partial derivative in the
primal-dual variables is the regular KKT block, the nearby zeros form a unique
differentiable branch. The result concerns zeros of the fixed-active-set equations. -/
theorem theorem_3_2_7_implicit_branch {F : P × (V × Y) → V × Y}
    {p₀ : P} {z₀ : V × Y} {A : V →L[ℝ] Y} {H : V →L[ℝ] V}
    (hF : ContDiffAt ℝ 1 F (p₀, z₀)) (hzero : F (p₀, z₀) = 0)
    (hB : (fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × Y)) = activeKKTLinearization A H)
    (hA : Function.Surjective A) (hH : ∀ d : V, A d = 0 → d ≠ 0 → 0 < ⟪H d, d⟫) :
    ∃ z : P → V × Y, ContDiffAt ℝ 1 z p₀ ∧ z p₀ = z₀ ∧
      ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ContinuousOn z U ∧
        ∃ W : Set (V × Y), IsOpen W ∧ z₀ ∈ W ∧
          ∀ p ∈ U, z p ∈ W ∧ ∀ w ∈ W, F (p, w) = 0 ↔ w = z p := by
  have hi : ((fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × Y))).IsInvertible :=
    hB ▸ theorem_3_2_7_activeKKT_invertible hA hH
  let z := hF.implicitFunction one_ne_zero hi
  have hz : z p₀ = z₀ := hF.implicitFunction_apply_self one_ne_zero hi
  have hzd : ContDiffAt ℝ 1 z p₀ := hF.contDiffAt_implicitFunction one_ne_zero hi
  have hu : {v | F v = 0 ↔ z v.1 = v.2} ∈ 𝓝 p₀ ×ˢ 𝓝 z₀ := by
    rw [← nhds_prod_eq]
    change ∀ᶠ v in 𝓝 (p₀, z₀), F v = 0 ↔ z v.1 = v.2
    simpa [z, hzero] using hF.eventually_apply_eq_iff_implicitFunction one_ne_zero hi
  obtain ⟨U₀, hU₀, W₀, hW₀, hsub⟩ := Filter.mem_prod_iff.mp hu
  obtain ⟨U, hUU, hU, hp⟩ := mem_nhds_iff.mp hU₀
  obtain ⟨W, hWW, hW, hw⟩ := mem_nhds_iff.mp hW₀
  have hzW : z ⁻¹' W ∈ 𝓝 p₀ := hzd.continuousAt (hW.mem_nhds (hz.symm ▸ hw))
  obtain ⟨U', hU'W, hU', hp'⟩ := mem_nhds_iff.mp hzW
  have hreg : {p | ContDiffAt ℝ 1 z p} ∈ 𝓝 p₀ := hzd.eventually (by norm_num)
  obtain ⟨U'', hU''reg, hU'', hp''⟩ := mem_nhds_iff.mp hreg
  refine ⟨z, hzd, hz, U ∩ (U' ∩ U''), hU.inter (hU'.inter hU''),
    ⟨hp, hp', hp''⟩, ?_, W, hW, hw, ?_⟩
  · intro p hpU
    have hpreg : ContDiffAt ℝ 1 z p := hU''reg hpU.2.2
    exact hpreg.continuousAt.continuousWithinAt
  · intro p hpU
    refine ⟨hU'W hpU.2.1, fun w hwW ↦ ?_⟩
    have he := hsub (show (p, w) ∈ U₀ ×ˢ W₀ from ⟨hUU hpU.1, hWW hwW⟩)
    exact he.trans eq_comm

end ActiveKKTSensitivity

section MixedKKTSensitivity

open Constrained ContinuousLinearMap

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- Euclidean coordinates for equality and active-inequality multipliers. -/
abbrev ActiveDual (ι κ : Type*) [Fintype ι] [Fintype κ] :=
  EuclideanSpace ℝ (ι ⊕ κ)

omit [FiniteDimensional ℝ V] in
/-- Active-system stationarity in vector and scalar-coordinate form. -/
theorem active_kkt_stationary_iff {f : V → ℝ} {h : ι → V → ℝ}
    {g : κ ⊕ ν → V → ℝ} {x : V}
    {A : V →L[ℝ] ActiveDual ι κ} {mult : ActiveDual ι κ}
    (hA : ∀ d i, A d i = Sum.elim (fun i ↦ fderiv ℝ (h i) x d)
      (fun j ↦ fderiv ℝ (g (.inl j)) x d) i) :
    gradient f x + A.adjoint mult = 0 ↔
      fderiv ℝ f x + ∑ i, mult (.inl i) • fderiv ℝ (h i) x +
        ∑ j : κ ⊕ ν, (Sum.elim (fun k ↦ mult (.inr k)) (fun _ ↦ 0) j) • fderiv ℝ (g j) x = 0 := by
  let L := fderiv ℝ f x + ∑ i, mult (.inl i) • fderiv ℝ (h i) x +
    ∑ j : κ ⊕ ν, (Sum.elim (fun k ↦ mult (.inr k)) (fun _ ↦ 0) j) • fderiv ℝ (g j) x
  have he (d : V) : ⟪gradient f x + A.adjoint mult, d⟫ = L d := by
    simp only [L, inner_add_left, inner_gradient_left, adjoint_inner_left,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hA, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, add_apply, sum_apply, smul_apply, smul_eq_mul,
      zero_mul, Finset.sum_const_zero, add_zero]
    simp only [mul_comm, add_assoc]
  constructor
  · intro hs
    ext d
    rw [← he d, hs, inner_zero_left, zero_apply]
  · intro hs
    apply ext_inner_right ℝ
    intro d
    rw [he, show L = 0 from hs, zero_apply, inner_zero_left]

omit [FiniteDimensional ℝ V] in
/-- Recover stationary active multipliers continuously where the active Jacobian is onto. -/
theorem continuous_active_multiplier_recovery
    {Q : Type*} [TopologicalSpace Q] {q₀ : Q}
    {A : Q → V →L[ℝ] ActiveDual ι κ} {G : Q → V} {m₀ : ActiveDual ι κ}
    (hA : ContinuousAt A q₀) (hG : ContinuousAt G q₀) (honto : Function.Surjective (A q₀))
    (hbase : G q₀ + (A q₀).adjoint m₀ = 0) :
    ∃ m : Q → ActiveDual ι κ, ContinuousAt m q₀ ∧ m q₀ = m₀ ∧
      ∀ᶠ q in 𝓝 q₀, Function.Surjective (A q) ∧
        ∀ b : ActiveDual ι κ, G q + (A q).adjoint b = 0 → b = m q := by
  let B (q : Q) := (A q).comp (A q).adjoint
  have hB : ContinuousAt B q₀ :=
    hA.clm_comp (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hA)
  have hadj : Function.Injective (A q₀).adjoint := by
    intro a b hab
    apply ext_inner_right ℝ
    intro v
    obtain ⟨d, rfl⟩ := honto v
    rw [← adjoint_inner_left, hab, adjoint_inner_left]
  have hinj : Function.Injective (B q₀) :=
    (ContinuousLinearMap.self_comp_adjoint_injective_iff (A q₀)).mpr hadj
  have hsurj : Function.Surjective (B q₀) :=
    LinearMap.surjective_of_injective (f := (B q₀).toLinearMap) hinj
  let e := ContinuousLinearEquiv.ofBijective (B q₀) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have he : (e : ActiveDual ι κ →L[ℝ] ActiveDual ι κ) = B q₀ :=
    ContinuousLinearEquiv.coe_ofBijective ..
  have hi : (B q₀).IsInvertible := ⟨e, he⟩
  let m (q : Q) := (B q).inverse (-(A q (G q)))
  have hinv : ContinuousAt (ContinuousLinearMap.inverse (R := ℝ)) (B q₀) := by
    rw [← ringInverse_eq_inverse, ← he]
    exact NormedRing.inverse_continuousAt ((ContinuousLinearEquiv.unitsEquiv ℝ _).symm e)
  have hm : ContinuousAt m q₀ :=
    (hinv.comp hB).clm_apply ((hA.clm_apply hG).neg)
  have hrec (q : Q) (hq : (B q).IsInvertible) (b : ActiveDual ι κ)
      (hb : G q + (A q).adjoint b = 0) : b = m q := by
    have hb' : (A q).adjoint b = -G q := eq_neg_of_add_eq_zero_right hb
    have hlin : B q b = -(A q (G q)) := by simp [B, hb', map_neg]
    obtain ⟨E, hE⟩ := hq
    change b = (B q).inverse (-(A q (G q)))
    rw [← hlin, ← hE, inverse_equiv]
    exact (E.symm_apply_apply b).symm
  refine ⟨m, hm, (hrec q₀ hi m₀ hbase).symm, ?_⟩
  filter_upwards [hB.tendsto.eventually hi.eventually_nhds] with q hq
  refine ⟨?_, hrec q hq⟩
  intro b
  obtain ⟨E, hE⟩ := hq
  obtain ⟨v, hv⟩ := E.surjective b
  have heval := congrArg (fun T : ActiveDual ι κ →L[ℝ] ActiveDual ι κ ↦ T v) hE
  exact ⟨(A q).adjoint v, by simpa [B] using heval.symm.trans hv⟩

omit [CompleteSpace V] [FiniteDimensional ℝ V] [Fintype ν] in
/-- An onto full active Jacobian gives LICQ for any subset of its active rows. -/
theorem active_surjective_licq {h : ι → V → ℝ} {g : κ ⊕ ν → V → ℝ}
    {x : V} {A : V →L[ℝ] ActiveDual ι κ}
    (hA : ∀ d i, A d i = Sum.elim (fun i ↦ fderiv ℝ (h i) x d)
      (fun j ↦ fderiv ℝ (g (.inl j)) x d) i)
    (honto : Function.Surjective A) (hneg : ∀ j : ν, g (.inr j) x < 0)
    (hx : x ∈ feasible h g) :
    IsRegularPointIneq h (fun i ↦ fderiv ℝ (h i)) g (fun j ↦ fderiv ℝ (g j)) x := by
  classical
  let row : ι ⊕ κ → V →L[ℝ] ℝ :=
    Sum.elim (fun i ↦ fderiv ℝ (h i) x) (fun j ↦ fderiv ℝ (g (.inl j)) x)
  have hrow (d : V) (i : ι ⊕ κ) : row i d = A d i := by
    rw [hA]
    cases i <;> rfl
  have hli : LinearIndependent ℝ row := Fintype.linearIndependent_iff.mpr fun a ha i ↦ by
    obtain ⟨d, hd⟩ := honto (WithLp.toLp 2 (Pi.single i 1))
    have h := congrArg (fun L : V →L[ℝ] ℝ ↦ L d) ha
    simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply, hrow, hd, PiLp.toLp_apply] at h
    simpa [Pi.single_apply, Finset.sum_ite_eq', eq_comm] using h
  have hl (j : activeSet g x) : ∃ k : κ, (j : κ ⊕ ν) = .inl k := by
    rcases j with ⟨j, hj⟩
    cases j with
    | inl k => exact ⟨k, rfl⟩
    | inr k => exact ((hneg k).ne (mem_activeSet.mp hj)).elim
  let jmap (j : activeSet g x) := (hl j).choose
  have hjmap (j : activeSet g x) : (j : κ ⊕ ν) = .inl (jmap j) := (hl j).choose_spec
  have hjinj : Function.Injective jmap := by
    intro i j hij
    apply Subtype.ext
    rw [hjmap i, hjmap j, hij]
  let emb : ι ⊕ activeSet g x → ι ⊕ κ := Sum.map id jmap
  have hemb : Function.Injective emb := by
    rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (Sum.inl.inj hij)
    · cases hij
    · cases hij
    · exact congrArg Sum.inr (hjinj (Sum.inr.inj hij))
  refine ⟨hx.1, hx.2, ?_⟩
  convert hli.comp emb hemb using 1
  funext i
  cases i with
  | inl i => rfl
  | inr j =>
    change fderiv ℝ (g (j : κ ⊕ ν)) x = fderiv ℝ (g (.inl (jmap j))) x
    rw [hjmap]

/-- Strict-minimizer continuation in Theorem 3.2.7. The inequalities indexed by
κ are active at the base and those indexed by ν are inactive. The smooth active
residual and its block derivative are supplied explicitly. Rank, reduced-Hessian
positivity, strict complementarity, and the original active set persist on the branch.
The branch has unique multipliers and is the only feasible local minimizer in a
common open primal neighborhood for parameters close to the base. -/
theorem theorem_3_2_7_strict_minimizer_branch
    {f : P → V → ℝ} {h : ι → P → V → ℝ} {g : κ ⊕ ν → P → V → ℝ}
    {F : P × (V × ActiveDual ι κ) → V × ActiveDual ι κ}
    {A : P → V → V →L[ℝ] ActiveDual ι κ} {H : P → V × ActiveDual ι κ → V →L[ℝ] V}
    {p₀ : P} {z₀ : V × ActiveDual ι κ}
    (hF : ContDiffAt ℝ 1 F (p₀, z₀)) (hzero : F (p₀, z₀) = 0)
    (hB : (fderiv ℝ F (p₀, z₀)).comp (inr ℝ P (V × ActiveDual ι κ)) =
      activeKKTLinearization (A p₀ z₀.1) (H p₀ z₀))
    (hA₀ : Function.Surjective (A p₀ z₀.1))
    (hH₀ : ∀ d : V, A p₀ z₀.1 d = 0 → d ≠ 0 → 0 < ⟪H p₀ z₀ d, d⟫)
    (hAcont : ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦ A w.1 w.2.1) (p₀, z₀))
    (hHcont : ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦ H w.1 w.2) (p₀, z₀))
    (hgcont : ∀ j : ν, ContinuousAt (fun w : P × (V × ActiveDual ι κ) ↦
      g (.inr j) w.1 w.2.1) (p₀, z₀))
    (hstrict : ∀ j : κ, 0 < z₀.2 (.inr j)) (hinactive : ∀ j : ν, g (.inr j) p₀ z₀.1 < 0)
    (hf : ∀ p x, ContDiffAt ℝ 2 (f p) x)
    (hh : ∀ p x i, ContDiffAt ℝ 2 (h i p) x)
    (hg : ∀ p x j, ContDiffAt ℝ 2 (g j p) x)
    (hF₁ : ∀ p z, (F (p, z)).1 = gradient (f p) z.1 + (A p z.1).adjoint z.2)
    (hF₂ : ∀ p z i, (F (p, z)).2 i = Sum.elim (fun i ↦ h i p z.1)
      (fun j ↦ g (.inl j) p z.1) i)
    (hA : ∀ p x d i, A p x d i = Sum.elim (fun i ↦ fderiv ℝ (h i p) x d)
      (fun j ↦ fderiv ℝ (g (.inl j) p) x d) i)
    (hH : ∀ p z d, ⟪H p z d, d⟫ =
      iteratedFDeriv ℝ 2 (kktLagrangian (f p) (fun i ↦ h i p) (fun j ↦ g j p)
        (fun i ↦ z.2 (.inl i)) (Sum.elim (fun j ↦ z.2 (.inr j)) (fun _ ↦ 0))) z.1
        (fun _ ↦ d)) :
    ∃ z : P → V × ActiveDual ι κ, ContDiffAt ℝ 1 z p₀ ∧ z p₀ = z₀ ∧
      ∃ X : Set V, IsOpen X ∧ z₀.1 ∈ X ∧ ∀ᶠ p in 𝓝 p₀,
        (z p).1 ∈ X ∧
        (∀ j : κ ⊕ ν, g j p (z p).1 = 0 ↔ ∃ i : κ, j = .inl i) ∧
        (∀ j : κ, 0 < (z p).2 (.inr j)) ∧
        Function.Surjective (A p (z p).1) ∧
        (∀ d : V, A p (z p).1 d = 0 → d ≠ 0 → 0 < ⟪H p (z p) d, d⟫) ∧
        IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 (fun i ↦ (z p).2 (.inl i))
          (Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        Optimization.IsStrictLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) (z p).1 ∧
        (∀ l μ, IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
          (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 l μ →
          l = (fun i ↦ (z p).2 (.inl i)) ∧
          μ = Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)) ∧
        ∀ w ∈ X, w ∈ feasible (fun i ↦ h i p) (fun j ↦ g j p) →
          IsLocalMinOn (f p) (feasible (fun i ↦ h i p) (fun j ↦ g j p)) w → w = (z p).1 := by
  obtain ⟨z, hz, hz₀, U, hU, hpU, -, W, hW, hzW, hbranch⟩ :=
    theorem_3_2_7_implicit_branch hF hzero hB hA₀ hH₀
  have hpair : Tendsto (fun p ↦ (p, z p)) (𝓝 p₀) (𝓝 (p₀, z₀)) := by
    rw [← hz₀]
    exact tendsto_id.prodMk_nhds hz.continuousAt.tendsto
  have hreg : ∀ᶠ p in 𝓝 p₀, Function.Surjective (A p (z p).1) ∧
      ∀ d : V, A p (z p).1 d = 0 → d ≠ 0 → 0 < ⟪H p (z p) d, d⟫ :=
    ((hAcont.prodMk hHcont).tendsto.comp hpair).eventually
      (theorem_3_2_7_activeKKT_conditions_open.mem_nhds ⟨hA₀, hH₀⟩)
  have hpos : ∀ᶠ p in 𝓝 p₀, ∀ j : κ, 0 < (z p).2 (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    have hcont : Continuous (fun w : V × ActiveDual ι κ ↦ w.2 (.inr j)) :=
      proj.continuous.comp continuous_snd
    exact ((hcont.tendsto _).comp hz.continuousAt.tendsto).eventually
      (Ioi_mem_nhds (show 0 < (z p₀).2 (.inr j) by rw [hz₀]; exact hstrict j))
  have hneg : ∀ᶠ p in 𝓝 p₀, ∀ j : ν, g (.inr j) p (z p).1 < 0 :=
    eventually_all.mpr fun j ↦ ((hgcont j).tendsto.comp hpair).eventually (Iio_mem_nhds (hinactive j))
  let q₀ : P × V := (p₀, z₀.1)
  let lift (q : P × V) := (q.1, (q.2, z₀.2))
  have hlift : ContinuousAt lift q₀ :=
    continuous_fst.continuousAt.prodMk (continuous_snd.continuousAt.prodMk continuousAt_const)
  have hlift₀ : lift q₀ = (p₀, z₀) := rfl
  have hA' : ContinuousAt (fun q : P × V ↦ A q.1 q.2) q₀ := by
    exact (hlift₀.symm ▸ hAcont).comp hlift
  have hG' : ContinuousAt (fun q : P × V ↦ gradient (f q.1) q.2) q₀ := by
    have hf₁ : ContinuousAt (fun q : P × V ↦ (F (lift q)).1) q₀ :=
      continuous_fst.continuousAt.comp ((hlift₀.symm ▸ hF.continuousAt).comp hlift)
    have hadd : ContinuousAt (fun q : P × V ↦ (A q.1 q.2).adjoint z₀.2) q₀ :=
      (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hA').clm_apply continuousAt_const
    convert hf₁.sub hadd using 1
    funext q
    change gradient (f q.1) q.2 = (F (q.1, (q.2, z₀.2))).1 - (A q.1 q.2).adjoint z₀.2
    rw [hF₁, add_sub_cancel_right]
  have hbase : gradient (f p₀) z₀.1 + (A p₀ z₀.1).adjoint z₀.2 = 0 := by
    simpa [hF₁] using congrArg Prod.fst hzero
  obtain ⟨m, hm, hm₀, hmrec⟩ := continuous_active_multiplier_recovery hA' hG' hA₀ hbase
  have hnearW : ∀ᶠ q : P × V in 𝓝 q₀, (q.2, m q) ∈ W := by
    apply (continuous_snd.continuousAt.prodMk hm).tendsto.eventually
    apply hW.mem_nhds
    change (z₀.1, m q₀) ∈ W
    rwa [hm₀]
  have hnearpos : ∀ᶠ q : P × V in 𝓝 q₀, ∀ j : κ, 0 < m q (.inr j) := by
    apply eventually_all.mpr
    intro j
    let proj : ActiveDual ι κ →L[ℝ] ℝ := PiLp.proj _ _ (.inr j)
    apply (proj.continuous.continuousAt.comp hm).tendsto.eventually
    apply Ioi_mem_nhds
    change 0 < m q₀ (.inr j)
    rw [hm₀]
    exact hstrict j
  have hnearneg : ∀ᶠ q : P × V in 𝓝 q₀, ∀ j : ν, g (.inr j) q.1 q.2 < 0 := by
    apply eventually_all.mpr
    intro j
    exact ((hlift₀.symm ▸ hgcont j).comp hlift).tendsto.eventually (Iio_mem_nhds (hinactive j))
  have hnear := hnearW.and (hnearpos.and (hnearneg.and hmrec))
  change ∀ᶠ q in 𝓝 (p₀, z₀.1), _ at hnear
  rw [nhds_prod_eq] at hnear
  obtain ⟨U', hU', X₀, hX₀, hrectangle⟩ := Filter.mem_prod_iff.mp hnear
  obtain ⟨X, hXX₀, hX, hxX⟩ := mem_nhds_iff.mp hX₀
  have hx : ∀ᶠ p in 𝓝 p₀, (z p).1 ∈ X := by
    apply (continuous_fst.continuousAt.comp hz.continuousAt).tendsto.eventually
    change ∀ᶠ y in 𝓝 (z p₀).1, y ∈ X
    rw [hz₀]
    exact hX.mem_nhds hxX
  refine ⟨z, hz, hz₀, X, hX, hxX, ?_⟩
  filter_upwards [hU.mem_nhds hpU, hreg, hpos, hneg, hU', hx] with p hp hpreg hppos hpneg hp' hpx
  have hFz : F (p, z p) = 0 := ((hbranch p hp).2 _ (hbranch p hp).1).mpr rfl
  have he (i : ι) : h i p (z p).1 = 0 := by
    simpa [hF₂] using congrArg (fun w : V × ActiveDual ι κ ↦ w.2 (.inl i)) hFz
  have hi (j : κ) : g (.inl j) p (z p).1 = 0 := by
    simpa [hF₂] using congrArg (fun w : V × ActiveDual ι κ ↦ w.2 (.inr j)) hFz
  have hstat : gradient (f p) (z p).1 + (A p (z p).1).adjoint (z p).2 = 0 := by
    simpa [hF₁] using congrArg Prod.fst hFz
  let μ : κ ⊕ ν → ℝ := Sum.elim (fun j ↦ (z p).2 (.inr j)) (fun _ ↦ 0)
  have hkkt : IsKKTPoint (fderiv ℝ (f p)) (fun i ↦ h i p) (fun i ↦ fderiv ℝ (h i p))
      (fun j ↦ g j p) (fun j ↦ fderiv ℝ (g j p)) (z p).1 (fun i ↦ (z p).2 (.inl i)) μ := by
    refine ⟨he, ?_, (active_kkt_stationary_iff (hA p _)).mp hstat, ?_, ?_⟩
    · intro j
      cases j with
      | inl j => exact (hi j).le
      | inr j => exact (hpneg j).le
    · intro j
      cases j with
      | inl j => exact (hppos j).le
      | inr j => exact le_rfl
    · intro j
      cases j with
      | inl j => rw [hi, mul_zero]
      | inr j => exact zero_mul _
  refine ⟨hpx, ?_, hppos, hpreg.1, hpreg.2, hkkt, theorem_3_2_6 (hf p _) (hh p _) (hg p _) hkkt ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl j => simp [hi]
    | inr j => simp [(hpneg j).ne]
  · intro d hd hdne
    have hker : A p (z p).1 d = 0 := by
      ext i
      rw [hA]
      cases i with
      | inl i => exact hd.1 i
      | inr j => exact hd.2.1 (.inl j) (hi j) (hppos j)
    rw [← hH]
    exact hpreg.2 d hker hdne

  · intro l' μ' hkkt'
    have hin (j : ν) : μ' (.inr j) = 0 :=
      (mul_eq_zero.mp (hkkt'.complementary (.inr j))).resolve_right (hpneg j).ne
    let mult' : ActiveDual ι κ := WithLp.toLp 2 (Sum.elim l' (fun j ↦ μ' (.inl j)))
    have hμ' : Sum.elim (fun j ↦ mult' (.inr j)) (fun _ ↦ 0) = μ' := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact (hin j).symm
    have hstat' : gradient (f p) (z p).1 + (A p (z p).1).adjoint mult' = 0 := by
      apply (active_kkt_stationary_iff (f := f p) (h := fun i ↦ h i p)
        (g := fun j ↦ g j p) (hA p _)).mpr
      rw [hμ']
      exact hkkt'.stationary
    have heq : (A p (z p).1).adjoint mult' = (A p (z p).1).adjoint (z p).2 :=
      add_left_cancel (hstat'.trans hstat.symm)
    have hmult : mult' = (z p).2 := by
      apply ext_inner_right ℝ
      intro y
      obtain ⟨d, rfl⟩ := hpreg.1 y
      rw [← adjoint_inner_left, heq, adjoint_inner_left]
    constructor
    · exact funext fun i ↦ congrArg (fun mult : ActiveDual ι κ ↦ mult (.inl i)) hmult
    · rw [← hμ', hmult]

  · intro w hw hwfeas hwmin
    have hnearw := hrectangle (show (p, w) ∈ U' ×ˢ X₀ from ⟨hp', hXX₀ hw⟩)
    obtain ⟨hwW, hwpos, hwneg, hwonto, hwrec⟩ := hnearw
    have hlicq := active_surjective_licq (h := fun i ↦ h i p) (g := fun j ↦ g j p)
      (hA p w) hwonto hwneg hwfeas
    obtain ⟨l', μ', hkkt'⟩ := exists_kkt_of_isLocalMinOn hlicq hwmin
      ((hf p w).differentiableAt (by norm_num)).hasFDerivAt
      (fun i ↦ (hh p w i).hasStrictFDerivAt (by norm_num))
      (fun j ↦ (hg p w j).hasStrictFDerivAt (by norm_num))
    have hout (j : ν) : μ' (.inr j) = 0 :=
      (mul_eq_zero.mp (hkkt'.complementary (.inr j))).resolve_right (hwneg j).ne
    let mult' : ActiveDual ι κ := WithLp.toLp 2 (Sum.elim l' (fun j ↦ μ' (.inl j)))
    have hμ' : Sum.elim (fun j ↦ mult' (.inr j)) (fun _ ↦ 0) = μ' := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => exact (hout j).symm
    have hstationary : gradient (f p) w + (A p w).adjoint mult' = 0 := by
      apply (active_kkt_stationary_iff (f := f p) (h := fun i ↦ h i p)
        (g := fun j ↦ g j p) (hA p w)).mpr
      rw [hμ']
      exact hkkt'.stationary
    have hmult : mult' = m (p, w) := hwrec mult' hstationary
    have hactive (j : κ) : g (.inl j) p w = 0 := by
      have hμpos : 0 < μ' (.inl j) := by
        change 0 < mult' (.inr j)
        rw [hmult]
        exact hwpos j
      exact (mul_eq_zero.mp (hkkt'.complementary (.inl j))).resolve_left hμpos.ne'
    have hFzero : F (p, (w, m (p, w))) = 0 := by
      apply Prod.ext
      · rw [hF₁, ← hmult]
        exact hstationary
      · ext i
        rw [hF₂]
        cases i with
        | inl i => exact hkkt'.feasible_eq i
        | inr j => exact hactive j
    exact congrArg Prod.fst (((hbranch p hp).2 _ hwW).mp hFzero)

end MixedKKTSensitivity

section ParametricMinimum

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

private theorem eventually_feasible_prod_subset {C : P → Set X} {p : P}
    (hC : IsCompact (C p)) (hU : UpperHemicontinuousAt C p)
    {S : Set (X × P)} (hS : IsOpen S) (hmem : ∀ x ∈ C p, (x, p) ∈ S) :
    ∀ᶠ q in 𝓝 p, ∀ x ∈ C q, (x, q) ∈ S := by
  have hprod : S ∈ (𝓝ˢ (C p)) ×ˢ 𝓝 p := hC.mem_nhdsSet_prod_of_forall fun x hx ↦ by
    rw [← nhds_prod_eq]
    exact hS.mem_nhds (hmem x hx)
  obtain ⟨U, hUn, V, hV, hsub⟩ := Filter.mem_prod_iff.mp hprod
  obtain ⟨U', hU'o, hCU', hU'U⟩ := mem_nhdsSet_iff_exists.mp hUn
  filter_upwards [hU.forall_isOpen U' hU'o hCU', hV] with q hq hqV
  exact fun x hx ↦ hsub ⟨hU'U (hq hx), hqV⟩

/-- Theorem 3.2.8 with compact, nonempty feasible fibers. The minimum value is continuous,
and the minimizer correspondence is upper hemicontinuous. Lower hemicontinuity can
fail even for linear objectives on a fixed compact convex feasible set. -/
theorem theorem_3_2_8 {C : P → Set X} {f : X × P → ℝ}
    (hC : ∀ p, IsCompact (C p)) (hne : ∀ p, (C p).Nonempty)
    (hupper : UpperHemicontinuous C) (hlower : LowerHemicontinuous C) (hf : Continuous f) :
    let value := fun p ↦ sInf ((fun x ↦ f (x, p)) '' C p)
    let sol := fun p ↦ {x ∈ C p | f (x, p) = value p}
    Continuous value ∧ UpperHemicontinuous sol ∧ ∀ p, (sol p).Nonempty := by
  let value (p : P) := sInf ((fun x ↦ f (x, p)) '' C p)
  let sol (p : P) := {x ∈ C p | f (x, p) = value p}
  have hmin (p : P) : ∃ x ∈ C p, f (x, p) = value p ∧ ∀ y ∈ C p, f (x, p) ≤ f (y, p) := by
    obtain ⟨x, hx, hm⟩ := (hC p).exists_isMinOn (hne p)
      (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
    refine ⟨x, hx, ?_, fun y hy ↦ hm hy⟩
    exact (show IsLeast ((fun y ↦ f (y, p)) '' C p) (f (x, p)) from
      ⟨mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hm hy⟩).csInf_eq.symm
  have hle (p : P) (x : X) (hx : x ∈ C p) : value p ≤ f (x, p) := by
    obtain ⟨z, -, hz, h⟩ := hmin p
    rw [← hz]
    exact h x hx
  have hvalue : Continuous value := by
    rw [continuous_iff_continuousAt]
    intro p
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have h := eventually_feasible_prod_subset (hC p) (upperHemicontinuous_iff.mp hupper p)
        (S := {z | b < f z}) (isOpen_lt continuous_const hf)
        (fun x hx ↦ hb.trans_le (hle p x hx))
      filter_upwards [h] with q hq
      obtain ⟨x, hx, hv, -⟩ := hmin q
      exact hv ▸ hq x hx
    · intro b hb
      obtain ⟨x, hx, hv, -⟩ := hmin p
      have hp : (x, p) ∈ {z | f z < b} := by
        change f (x, p) < b
        rwa [hv]
      have hopen : IsOpen {z | f z < b} := isOpen_lt hf continuous_const
      have hprod : {z | f z < b} ∈ 𝓝 x ×ˢ 𝓝 p := by
        rw [← nhds_prod_eq]
        exact hopen.mem_nhds hp
      obtain ⟨U, hU, V, hV, hsub⟩ := Filter.mem_prod_iff.mp hprod
      obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
      have hhit : {q | (C q ∩ W).Nonempty} ∈ 𝓝 p :=
        ((lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hlower) W hW).mem_nhds
          ⟨x, hx, hxW⟩
      filter_upwards [hhit, hV] with q hq hqV
      obtain ⟨y, hy, hyW⟩ := hq
      exact (hle q y hy).trans_lt (hsub ⟨hWU hyW, hqV⟩)
  refine ⟨hvalue, upperHemicontinuous_iff_forall_isOpen.mpr ?_, ?_⟩
  · intro p U hU hp
    have hopen : IsOpen {z : X × P | z.1 ∈ U ∨ value z.2 < f z} :=
      (hU.preimage continuous_fst).union (isOpen_lt (hvalue.comp continuous_snd) hf)
    have hmem (x : X) (hx : x ∈ C p) : (x, p) ∈ {z : X × P | z.1 ∈ U ∨ value z.2 < f z} := by
      by_cases he : f (x, p) = value p
      · exact Or.inl (hp ⟨hx, he⟩)
      · exact Or.inr (lt_of_le_of_ne (hle p x hx) (Ne.symm he))
    filter_upwards [eventually_feasible_prod_subset (hC p)
      (upperHemicontinuous_iff.mp hupper p) hopen hmem] with q hq
    intro x hx
    exact (hq x hx.1).resolve_right (by rw [hx.2]; exact lt_irrefl _)
  · intro p
    obtain ⟨x, hx, hv, -⟩ := hmin p
    exact ⟨x, hx, hv⟩

end ParametricMinimum

/-- The optimizers of `p * x` on `[0,1]` fail lower hemicontinuity at `p = 0`,
although the feasible set is fixed and the objective is jointly continuous and affine
in the decision variable. -/
theorem theorem_3_2_8_counterexample :
    ¬ LowerHemicontinuous (fun p : ℝ ↦
      {x ∈ Icc (0 : ℝ) 1 | IsMinOn (fun y ↦ p * y) (Icc (0 : ℝ) 1) x}) := by
  intro h
  have hopen := lowerHemicontinuous_iff_isOpen_inter_nonempty.mp h (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hmem : (0 : ℝ) ∈ {p : ℝ | ({x ∈ Icc (0 : ℝ) 1 |
      IsMinOn (fun y ↦ p * y) (Icc (0 : ℝ) 1) x} ∩ Ioi (1 / 2 : ℝ)).Nonempty} := by
    refine ⟨1, ⟨⟨by norm_num, le_rfl⟩, ?_⟩, by norm_num⟩
    intro y _
    simp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  have hεball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨x, ⟨hx, hxmin⟩, hxopen⟩ := hsub hεball
  have hle : (ε / 2) * x ≤ (ε / 2) * 0 := hxmin (show 0 ∈ Icc (0 : ℝ) 1 by norm_num)
  have hpos : 0 < (ε / 2) * x := mul_pos (half_pos hε) (by linarith [show (1 / 2 : ℝ) < x from hxopen])
  linarith


private theorem strictLocalMinOn_of_minorant [FiniteDimensional ℝ E]
    {F L : E → ℝ} {S : Set E} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hstat : fderiv ℝ L x = 0) (hminor : ∀ y ∈ S, L y - L x ≤ F y - F x)
    (hpos : ∀ d ∈ posTangentConeAt {y ∈ S | F y ≤ F x} x, d ≠ 0 →
      0 < iteratedFDeriv ℝ 2 L x (fun _ ↦ d)) :
    Optimization.IsStrictLocalMinOn F S x := by
  have hm := Optimization.isStrictLocalMinOn_of_posTangentCone hL
    (C := {y ∈ S | F y ≤ F x})
    (Eventually.of_forall fun y ↦ by simp [hstat]) (fun d hd hn _ ↦ hpos d hd hn)
  rw [Optimization.isStrictLocalMinOn_iff_eventually] at hm ⊢
  filter_upwards [hm] with y hy hyS hyx
  by_contra! hbad
  exact (not_lt_of_ge (by linarith [hminor y hyS, hbad])) (hy ⟨hyS, hbad⟩ hyx)

/-- Theorem 3.2.14. A stationary supporting Lagrangian with positive Hessian on
the unit critical directions gives a strict local minimizer of the composite.
Because the chosen subgradient gives zero first variation, the zero support
condition in (3.2.24) is equivalent to all supporting first variations being
nonpositive. Subgradients are taken relative to the domain `C`. -/
theorem theorem_3_2_14 [FiniteDimensional ℝ E]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {f : E → ℝ} {c : E → W} {h : W → ℝ} {S : Set E} {C : Set W} {x : E}
    (hx : x ∈ S) (hcS : MapsTo c S C) (hf : ContDiffAt ℝ 2 f x) (hc : ContDiffAt ℝ 2 c x) :
    let K := {g : W | ∀ z ∈ C, h (c x) + ⟪z - c x, g⟫ ≤ h z}
    let L := fun (g : W) (y : E) ↦ f y + ⟪c y, g⟫
    ∀ gStar ∈ K, fderiv ℝ (L gStar) x = 0 →
      (∀ d : E, ‖d‖ = 1 → (∀ g ∈ K, fderiv ℝ (L g) x d ≤ 0) →
        0 < iteratedFDeriv ℝ 2 (L gStar) x (fun _ ↦ d)) →
      x ∈ S ∧ Optimization.IsStrictLocalMinOn (fun y ↦ f y + h (c y)) S x := by
  dsimp only
  intro gStar hgStar hstat hpos
  let F (y : E) := f y + h (c y)
  let L (g : W) (y : E) := f y + ⟪c y, g⟫
  let K := {g : W | ∀ z ∈ C, h (c x) + ⟪z - c x, g⟫ ≤ h z}
  have hL (g : W) : ContDiffAt ℝ 2 (L g) x := hf.add (hc.inner ℝ contDiffAt_const)
  have hminor (g : W) (hg : g ∈ K) (y : E) (hy : y ∈ S) : L g y - L g x ≤ F y - F x := by
    have hp := hg (c y) (hcS hy)
    rw [inner_sub_left] at hp
    dsimp [L, F]
    linarith
  refine ⟨hx, strictLocalMinOn_of_minorant (F := F) (L := L gStar) (hL gStar) hstat
    (hminor gStar hgStar) ?_⟩
  intro d hd hd₀
  have hdir (g : W) (hg : g ∈ K) : fderiv ℝ (L g) x d ≤ 0 := by
    have hm : IsMaxOn (L g) {y ∈ S | F y ≤ F x} x := by
      intro y hy
      change y ∈ S ∧ F y ≤ F x at hy
      change L g y ≤ L g x
      linarith [hminor g hg y hy.1, hy.2]
    exact hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
      ((hL g).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt hd
  let a : ℝ := ‖d‖⁻¹
  have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr hd₀)
  have hunit : ‖a • d‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd₀)
  have hp := hpos (a • d) hunit (fun g hg ↦ by
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le (hdir g hg))
  let H := iteratedFDeriv ℝ 2 (L gStar) x
  have hscale : H (fun _ ↦ a • d) = a ^ 2 * H (fun _ ↦ d) := by
    change H.toMultilinearMap (fun _ ↦ a • d) = _
    rw [H.toMultilinearMap.map_smul_univ (fun _ ↦ a) (fun _ ↦ d)]
    simp
  change 0 < H (fun _ ↦ a • d) at hp
  rw [hscale] at hp
  exact pos_of_mul_pos_right hp (sq_nonneg a)


section SmoothNormalMultipliers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

open Constrained
open scoped Pointwise

/-- Theorem 3.2.11. The constraint qualification requires linearized feasible
displacements to lie in the feasible tangent cone and the normal cone sum rule
to be exact for the base set and the linearized constraints. Inequalities are
written as `g ≤ 0`. -/
theorem theorem_3_2_11 {ι κ : Type*} [Fintype ι] [Fintype κ]
    {C : Set V} {f : V → ℝ} {h : ι → V → ℝ} {g : κ → V → ℝ} {x : V}
    (hxC : x ∈ C) (hx : x ∈ feasible h g) (hf : DifferentiableAt ℝ f x)
    (hmin : IsLocalMinOn f (C ∩ feasible h g) x) :
    let Q := {z : V | (∀ i, fderiv ℝ (h i) x (z - x) = 0) ∧
      ∀ j ∈ activeSet g x, fderiv ℝ (g j) x (z - x) ≤ 0}
    (∀ z ∈ C ∩ Q, z - x ∈ posTangentConeAt (C ∩ feasible h g) x) →
    IsExactSum (innerₗ V) (indicatorFn C) (indicatorFn Q) →
    ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, h i x = 0) ∧
      (∀ j, g j x ≤ 0 ∧ 0 ≤ μ j ∧ μ j * g j x = 0) ∧
      -gradient f x - (∑ i, l i • gradient (h i) x) - (∑ j, μ j • gradient (g j) x) ∈
        normalCone (innerₗ V) C x := by
  classical
  intro Q hQ hsum
  have hxQ : x ∈ Q := by simp [Q]
  have hn : -gradient f x ∈ normalCone (innerₗ V) (C ∩ Q) x := by
    intro z hz
    have hp := hmin.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt (hQ z hz)
    simpa [innerₗ_apply_apply] using hp
  rw [hsum.normalCone_inter hxC hxQ] at hn
  obtain ⟨n, hn, w, hw, hnw⟩ := hn
  let A : (ι ⊕ ι) ⊕ activeSet g x → V :=
    Sum.elim (Sum.elim (fun i ↦ gradient (h i) x) (fun i ↦ -gradient (h i) x))
      (fun j ↦ gradient (g j) x)
  have hlin : ∀ d : V, (∀ i, innerₗ V d (A i) ≤ 0) → innerₗ V d w ≤ 0 := by
    intro d hd
    have hh (i : ι) : fderiv ℝ (h i) x d = 0 := by
      refine le_antisymm ?_ ?_
      · simpa [A, innerₗ_apply_apply] using hd (.inl (.inl i))
      · simpa [A, innerₗ_apply_apply] using hd (.inl (.inr i))
    have hg (j : κ) (hj : j ∈ activeSet g x) : fderiv ℝ (g j) x d ≤ 0 := by
      simpa [A, innerₗ_apply_apply] using hd (.inr ⟨j, hj⟩)
    have hz : x + d ∈ Q := by simpa [Q] using And.intro hh hg
    simpa using hw (x + d) hz
  obtain ⟨a, ha, hwa⟩ := (ConvexAnalysis.farkas (B := innerₗ V) A w).mp hlin
  let l (i : ι) := a (.inl (.inl i)) - a (.inl (.inr i))
  let μ := Function.extend (Subtype.val : activeSet g x → κ) (fun j ↦ a (.inr j)) 0
  have hμactive (j : κ) (hj : j ∈ activeSet g x) : μ j = a (.inr ⟨j, hj⟩) :=
    Subtype.val_injective.extend_apply _ _ ⟨j, hj⟩
  have hμinactive (j : κ) (hj : j ∉ activeSet g x) : μ j = 0 :=
    Function.extend_apply' _ _ _ (by rintro ⟨⟨j', hj'⟩, rfl⟩; exact hj hj')
  have hw' : (∑ i, l i • gradient (h i) x) + (∑ j, μ j • gradient (g j) x) = w := by
    rw [show (∑ j, μ j • gradient (g j) x) = ∑ j : activeSet g x,
      a (.inr j) • gradient (g j) x from sum_extend_activeSet_smul _ _]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hwa
    simp only [l, sub_eq_add_neg, add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simpa [A, smul_neg, Finset.sum_neg_distrib] using hwa
  refine ⟨l, μ, hx.1, fun j ↦ ⟨hx.2 j, ?_, ?_⟩, ?_⟩
  · by_cases hj : j ∈ activeSet g x
    · rw [hμactive j hj]
      exact ha _
    · rw [hμinactive j hj]
  · by_cases hj : j ∈ activeSet g x
    · rw [mem_activeSet.mp hj, mul_zero]
    · rw [hμinactive j hj, zero_mul]
  · have heq : -gradient f x - (∑ i, l i • gradient (h i) x) -
        (∑ j, μ j • gradient (g j) x) = n := by
      rw [← sub_add_eq_sub_sub, hw', ← hnw]
      exact add_sub_cancel_right n w
    simpa only [heq] using hn

end SmoothNormalMultipliers

/-- On the fixed feasible set `ℝ`, the minimum value of `(p * x - 1)^2`
is discontinuous at `p = 0`. This gives a separate failure of Theorem 3.2.8
when feasible sets are unbounded. -/
theorem theorem_3_2_8_noncompact_value_counterexample :
    ¬ Continuous (fun p : ℝ ↦ sInf (Set.range (fun x : ℝ ↦ (p * x - 1) ^ 2))) := by
  let v (p : ℝ) := sInf (Set.range (fun x : ℝ ↦ (p * x - 1) ^ 2))
  have hv₀ : v 0 = 1 := by simp [v]
  have hv (p : ℝ) (hp : p ≠ 0) : v p = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨p⁻¹, by simp [hp]⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact sq_nonneg _
  intro hc
  have hnear := (hc.continuousAt (x := (0 : ℝ))).eventually
    (Metric.ball_mem_nhds (v 0) (show (0 : ℝ) < 1 / 2 by norm_num))
  change ∀ᶠ p in 𝓝 (0 : ℝ), v p ∈ Metric.ball (v 0) (1 / 2) at hnear
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hcontra := hsub hb
  norm_num [hv₀, hv (ε / 2) (half_pos hε).ne', Metric.mem_ball, Real.dist_eq] at hcontra


/-- Theorem 3.2.15 needs regularity of the outer objective at the composite point.
The convex function `-√z` on `z ≥ 0` has no subgradient at zero, yet composing
it with `x ↦ x⁴` and adding `2x²` gives `x²`. The constraint is strictly inactive
everywhere. -/
theorem theorem_3_2_15_boundary_counterexample :
    let h := fun z : ℝ ↦ -Real.sqrt z
    let c := fun x : ℝ ↦ x ^ 4
    let f := fun x : ℝ ↦ 2 * x ^ 2
    let t := fun _ : ℝ ↦ (-1 : ℝ)
    let r := fun _ : ℝ ↦ (0 : ℝ)
    ConvexOn ℝ (Ici 0) h ∧ ConvexOn ℝ univ t ∧ MapsTo c univ (Ici 0) ∧
    ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧ ContDiff ℝ 1 r ∧ t (r 0) < 0 ∧
    IsLocalMinOn (fun x ↦ f x + h (c x)) {x | t (r x) ≤ 0} 0 ∧
    ¬ ∃ a : ℝ, ∀ z ≥ 0, h (c 0) + (z - c 0) * a ≤ h z := by
  dsimp only
  refine ⟨Real.strictConcaveOn_sqrt.concaveOn.neg, convexOn_const _ convex_univ,
    fun x _ ↦ (by positivity : 0 ≤ x ^ 4), contDiff_const.mul (contDiff_id.pow 2),
    contDiff_id.pow 4, contDiff_const, by norm_num, ?_, ?_⟩
  · apply IsMinOn.isLocalMinOn
    intro x _
    have hsq : Real.sqrt (x ^ 4) = x ^ 2 := by
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg x)]
    change 2 * (0 : ℝ) ^ 2 + -Real.sqrt (0 ^ 4) ≤ 2 * x ^ 2 + -Real.sqrt (x ^ 4)
    rw [hsq]
    norm_num
    nlinarith [sq_nonneg x]
  · rintro ⟨a, ha⟩
    let ε : ℝ := (|a| + 2)⁻¹
    have hε : 0 < ε := inv_pos.mpr (by positivity)
    have heq : (|a| + 2) * ε = 1 := mul_inv_cancel₀ (by positivity)
    have h := ha (ε ^ 2) (sq_nonneg ε)
    simp only [zero_pow (by decide : (4 : ℕ) ≠ 0), Real.sqrt_zero, neg_zero, sub_zero, zero_add,
      Real.sqrt_sq hε.le] at h
    have h' : ε * a ≤ -1 := by
      apply (mul_le_mul_iff_right₀ hε).mp
      calc
        ε * (ε * a) = ε ^ 2 * a := by ring
        _ ≤ -ε := h
        _ = ε * -1 := by ring
    have hl := mul_le_mul_of_nonneg_right (neg_abs_le a) hε.le
    nlinarith [hl]


section CompositeKKT

variable {V W Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

open Optimization

omit [CompleteSpace V] [FiniteDimensional ℝ W] in
private theorem eventually_composite_ray_quotient_lt
    {f : V → ℝ} {c : V → W} {h : W → ℝ} {x d : V} {b : ℝ}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    {U : Set W} {K : ℝ≥0} (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hb : fderiv ℝ f x d + clarkeDerivative h (c x) (fderiv ℝ c x d) < b) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ((f (x + s • d) + h (c (x + s • d))) - (f x + h (c x))) / s < b := by
  let p (s : ℝ) := x + s • d
  let v := fderiv ℝ c x d
  let A := fderiv ℝ f x d
  let B := clarkeDerivative h (c x) v
  let ε := (b - (A + B)) / 3
  have hε : 0 < ε := by dsimp [ε, A, B, v]; linarith
  have hp : HasDerivAt p d 0 := by
    simpa [p] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hp₀ : p 0 = x := by simp [p]
  have hpn : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [← hp₀]
    exact hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfn : Tendsto (fun s : ℝ ↦ (f (p s) - f x) / s) (𝓝[>] 0) (𝓝 A) := by
    have h : HasFDerivAt f (fderiv ℝ f x) (p 0) := hp₀ ▸ hf.hasFDerivAt
    simpa [hp₀, Function.comp_def, A, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h.comp_hasDerivAt 0 hp).tendsto_slope_zero_right
  have hcn : Tendsto (fun s : ℝ ↦ s⁻¹ • (c (p s) - c x)) (𝓝[>] 0) (𝓝 v) := by
    have h : HasFDerivAt c (fderiv ℝ c x) (p 0) := hp₀ ▸ hc.hasFDerivAt
    simpa [hp₀, Function.comp_def, v] using (h.comp_hasDerivAt 0 hp).tendsto_slope_zero_right
  have he : Tendsto (fun s : ℝ ↦ (K : ℝ) * ‖s⁻¹ • (c (p s) - c x) - v‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hcn.sub (tendsto_const_nhds (x := v))).norm.const_mul (K : ℝ))
  have hlin : Tendsto (fun s : ℝ ↦ c x + s • v) (𝓝[>] (0 : ℝ)) (𝓝 (c x)) := by
    have ht : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := c x)).add (ht.smul (tendsto_const_nhds (x := v)))
  have hbase := eventually_base_quotient_lt_of_clarkeDerivative_lt hU hK
    (show B < B + ε by linarith)
  filter_upwards [hfn.eventually_lt_const (show A < A + ε by linarith),
    he.eventually_lt_const hε, hbase, (hc.continuousAt.tendsto.comp hpn).eventually hU,
    hlin.eventually hU, self_mem_nhdsWithin] with s hsF hsE hsH hsC hsL hs
  change 0 < s at hs
  have hnorm : ‖s⁻¹ • (c (p s) - c x) - v‖ = ‖c (p s) - (c x + s • v)‖ / s := by
    have heq : s⁻¹ • (c (p s) - c x) - v = s⁻¹ • (c (p s) - (c x + s • v)) := by
      rw [show c (p s) - (c x + s • v) = (c (p s) - c x) - s • v by abel]
      simp only [smul_sub, inv_smul_smul₀ hs.ne']
    rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), div_eq_mul_inv, mul_comm]
  have hLip := hK.dist_le_mul _ hsC _ hsL
  rw [Real.dist_eq, dist_eq_norm] at hLip
  have herror : (h (c (p s)) - h (c x + s • v)) / s ≤
      (K : ℝ) * ‖s⁻¹ • (c (p s) - c x) - v‖ := by
    rw [hnorm, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans hLip) hs.le
  change ((f (p s) + h (c (p s))) - (f x + h (c x))) / s < b
  have hsplit : ((f (p s) + h (c (p s))) - (f x + h (c x))) / s =
      (f (p s) - f x) / s + (h (c (p s)) - h (c x + s • v)) / s +
        (h (c x + s • v) - h (c x)) / s := by ring
  rw [hsplit]
  dsimp only [ε] at hsF hsE hsH
  linarith

omit [CompleteSpace V] in
private theorem isCompact_convexJoin_real {P Q : Set V} (hP : IsCompact P) (hQ : IsCompact Q) :
    IsCompact (convexJoin ℝ P Q) := by
  let T (z : ℝ × V × V) := z.1 • z.2.1 + (1 - z.1) • z.2.2
  have hT : Continuous T := (continuous_fst.smul (continuous_fst.comp continuous_snd)).add
    ((continuous_const.sub continuous_fst).smul (continuous_snd.comp continuous_snd))
  have heq : convexJoin ℝ P Q = T '' (Icc (0 : ℝ) 1 ×ˢ (P ×ˢ Q)) := by
    ext z
    rw [mem_convexJoin]
    constructor
    · rintro ⟨p, hp, q, hq, a, b, ha, hb, hab, rfl⟩
      exact ⟨(a, p, q), ⟨⟨ha, by linarith⟩, hp, hq⟩, by
        change a • p + (1 - a) • q = a • p + b • q
        rw [show 1 - a = b by linarith]⟩
    · rintro ⟨⟨a, p, q⟩, ⟨ha, hp, hq⟩, rfl⟩
      exact ⟨p, hp, q, hq, a, 1 - a, ha.1, sub_nonneg.mpr ha.2, by ring, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod (hP.prod hQ)).image hT

/-- Theorem 3.2.15 with locally Lipschitz outer functions and an explicit Clarke
constraint qualification. At an active constraint a direction must strictly
decrease its linearized Clarke derivative. The multipliers use Clarke
subgradients, so the statement also applies to locally Lipschitz nonconvex outer functions. -/
theorem theorem_3_2_15_clarke {f : V → ℝ} {c : V → W} {r : V → Z} {h : W → ℝ}
    {t : Z → ℝ} {x : V} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hr : DifferentiableAt ℝ r x) {U : Set W} {T : Set Z} {K M : ℝ≥0}
    (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hT : T ∈ 𝓝 (r x)) (hM : LipschitzOnWith M t T)
    (hfeas : t (r x) ≤ 0)
    (hQ : t (r x) = 0 → ∃ d, clarkeDerivative t (r x) (fderiv ℝ r x d) < 0)
    (hmin : IsLocalMinOn (fun z ↦ f z + h (c z)) {z | t (r z) ≤ 0} x) :
    ∃ y ∈ clarkeSubgradient h (c x), ∃ u ∈ clarkeSubgradient t (r x), ∃ μ : ℝ,
      0 ≤ μ ∧ t (r x) * μ = 0 ∧
      gradient f x + (fderiv ℝ c x).adjoint y + μ • (fderiv ℝ r x).adjoint u = 0 := by
  let H := clarkeSubgradient h (c x)
  let J := clarkeSubgradient t (r x)
  let A := (fderiv ℝ c x).adjoint
  let B := (fderiv ℝ r x).adjoint
  have hsH := hasClarkeSupport_of_lipschitzOnWith hU hK
  have hsJ := hasClarkeSupport_of_lipschitzOnWith hT hM
  rcases hfeas.lt_or_eq with hinact | hact
  · have hct : ContinuousAt (fun z ↦ t (r z)) x :=
      (hM.continuousOn.continuousAt hT).comp hr.continuousAt
    have hnear : ∀ᶠ z in 𝓝 x, z ∈ {z | t (r z) ≤ 0} :=
      (hct.tendsto.eventually (Iio_mem_nhds hinact)).mono fun _ hz ↦ le_of_lt hz
    have hm : IsLocalMin (fun z ↦ f z + h (c z)) x := by
      change ∀ᶠ z in 𝓝[{z | t (r z) ≤ 0}] x,
        f x + h (c x) ≤ f z + h (c z) at hmin
      rw [eventually_nhdsWithin_iff] at hmin
      filter_upwards [hmin, hnear] with z hz hz'
      exact hz hz'
    obtain ⟨y, hy, hzero⟩ := (corollary_3_2_13 hf hc hm hU hK).1
    obtain ⟨u, hu⟩ := hsJ.nonempty
    exact ⟨y, hy, u, hu, 0, le_rfl, by simp, by simpa using hzero⟩
  · let P := (fun y ↦ gradient f x + A y) '' H
    let Q := B '' J
    have hP : IsCompact P := (isCompact_clarkeSubgradient hU hK).image
      (continuous_const.add A.continuous)
    have hQ' : IsCompact Q := (isCompact_clarkeSubgradient hT hM).image B.continuous
    have hPc : Convex ℝ P := by
      intro p hp q hq a b ha hb hab
      obtain ⟨y, hy, rfl⟩ := hp
      obtain ⟨z, hz, rfl⟩ := hq
      refine ⟨a • y + b • z, convex_clarkeSubgradient h (c x) hy hz ha hb hab, ?_⟩
      simp only [map_add, map_smul, smul_add]
      have he : gradient f x = a • gradient f x + b • gradient f x := by
        rw [← add_smul, hab, one_smul]
      conv_lhs => rw [he]
      abel
    have hQc : Convex ℝ Q := (convex_clarkeSubgradient t (r x)).linear_image B.toLinearMap
    have hjoin : convexHull ℝ (P ∪ Q) = convexJoin ℝ P Q :=
      hPc.convexHull_union hQc (hsH.nonempty.image _) (hsJ.nonempty.image _)
    have hmem : (0 : V) ∈ convexJoin ℝ P Q := by
      rw [← (isCompact_convexJoin_real hP hQ').isClosed.closure_eq, ← hjoin]
      apply (mem_closure_convexHull_iff_le_supportFn (B := innerₗ V) (P ∪ Q) 0).mpr
      intro d
      simp only [innerₗ_apply_apply, inner_zero_left]
      by_contra! hneg
      have hdot (v : V) (hv : v ∈ P ∪ Q) : ⟪v, d⟫ < 0 := by
        have he : ((⟪v, d⟫ : ℝ) : EReal) < 0 :=
          (le_supportFn (B := innerₗ V) hv d).trans_lt hneg
        exact EReal.coe_lt_coe_iff.mp (by simpa using he)
      have hmax :
          fderiv ℝ f x d + clarkeDerivative h (c x) (fderiv ℝ c x d) < 0 := by
        obtain ⟨y, hy, hymax⟩ := (isCompact_clarkeSubgradient hU hK).exists_isMaxOn
          hsH.nonempty (continuous_id.inner continuous_const :
            Continuous (fun z : W ↦ ⟪z, fderiv ℝ c x d⟫)).continuousOn
        have hle := (supportFn_le_coe_iff (B := innerₗ W) (s := H)
          (y := fderiv ℝ c x d)).2 (fun z hz ↦ hymax hz)
        rw [hsH] at hle
        have hv := hdot (gradient f x + A y) (Or.inl ⟨y, hy, rfl⟩)
        rw [inner_add_left, inner_gradient_left, ContinuousLinearMap.adjoint_inner_left] at hv
        exact (add_le_add_right (EReal.coe_le_coe_iff.mp hle) _).trans_lt hv
      have hmaxT : clarkeDerivative t (r x) (fderiv ℝ r x d) < 0 := by
        obtain ⟨u, hu, humax⟩ := (isCompact_clarkeSubgradient hT hM).exists_isMaxOn
          hsJ.nonempty (continuous_id.inner continuous_const :
            Continuous (fun z : Z ↦ ⟪z, fderiv ℝ r x d⟫)).continuousOn
        have hle := (supportFn_le_coe_iff (B := innerₗ Z) (s := J)
          (y := fderiv ℝ r x d)).2 (fun z hz ↦ humax hz)
        rw [hsJ] at hle
        have hv := hdot (B u) (Or.inr ⟨u, hu, rfl⟩)
        rw [ContinuousLinearMap.adjoint_inner_left] at hv
        exact (EReal.coe_le_coe_iff.mp hle).trans_lt hv
      have hbad := eventually_composite_ray_quotient_lt hf hc hU hK hmax
      have hfeas' := eventually_composite_ray_quotient_lt
        (f := fun _ : V ↦ (0 : ℝ)) (d := d) (differentiableAt_const 0) hr hT hM
        (b := 0) (by simpa using hmaxT)
      have hray : Tendsto (fun s : ℝ ↦ x + s • d) (𝓝[>] (0 : ℝ))
          (𝓝[{z | t (r z) ≤ 0}] x) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have ht : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
            tendsto_id.mono_right nhdsWithin_le_nhds
          simpa using (tendsto_const_nhds (x := x)).add (ht.smul (tendsto_const_nhds (x := d)))
        · filter_upwards [hfeas', self_mem_nhdsWithin] with s hfs hs
          change 0 < s at hs
          simpa only [zero_add, hact, sub_zero, zero_mul] using
            ((div_lt_iff₀ hs).mp hfs).le
      obtain ⟨s, hsbad, hsm, hs⟩ :=
        (hbad.and ((hray.eventually hmin).and self_mem_nhdsWithin)).exists
      exact (not_lt_of_ge (sub_nonneg.mpr hsm)) ((div_lt_iff₀ hs).mp hsbad |>.trans_eq (zero_mul _))
    obtain ⟨p, ⟨y, hy, rfl⟩, q, ⟨u, hu, rfl⟩, a, b, ha, hb, hab, hzero⟩ :=
      mem_convexJoin.mp hmem
    have hap : 0 < a := by
      by_contra! han
      have ha0 : a = 0 := le_antisymm han ha
      have hb1 : b = 1 := by linarith
      have hq0 : B u = 0 := by simpa [ha0, hb1] using hzero
      obtain ⟨d, hd⟩ := hQ hact
      have hu' := hu (fderiv ℝ r x d)
      rw [← ContinuousLinearMap.adjoint_inner_left, hq0, inner_zero_left] at hu'
      linarith
    refine ⟨y, hy, u, hu, b / a, div_nonneg hb hap.le, by rw [hact, zero_mul], ?_⟩
    have hscaled := congrArg (fun z : V ↦ a⁻¹ • z) hzero
    simpa [smul_add, smul_smul, inv_mul_cancel₀ hap.ne', div_eq_mul_inv, mul_comm a⁻¹ b] using hscaled

/-- Theorem 3.2.15 for continuous convex outer functions on their full spaces,
locally Lipschitz at the image points. An active constraint must admit a strict
Clarke descent direction through the inner map. -/
theorem theorem_3_2_15 {f : V → ℝ} {c : V → W} {r : V → Z} {h : W → ℝ}
    {t : Z → ℝ} {x : V} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hr : DifferentiableAt ℝ r x) (hh : ConvexOn ℝ univ h) (ht : ConvexOn ℝ univ t)
    (hch : Continuous h) (hct : Continuous t) {U : Set W} {T : Set Z} {K M : ℝ≥0}
    (hU : U ∈ 𝓝 (c x)) (hK : LipschitzOnWith K h U)
    (hT : T ∈ 𝓝 (r x)) (hM : LipschitzOnWith M t T)
    (hfeas : t (r x) ≤ 0)
    (hQ : t (r x) = 0 → ∃ d, clarkeDerivative t (r x) (fderiv ℝ r x d) < 0)
    (hmin : IsLocalMinOn (fun z ↦ f z + h (c z)) {z | t (r z) ≤ 0} x) :
    ∃ y ∈ subdifferential (innerₗ W) (fun w ↦ (h w : EReal)) (c x),
      ∃ u ∈ subdifferential (innerₗ Z) (fun z ↦ (t z : EReal)) (r x), ∃ μ : ℝ,
        0 ≤ μ ∧ t (r x) * μ = 0 ∧
        gradient f x + (fderiv ℝ c x).adjoint y + μ • (fderiv ℝ r x).adjoint u = 0 := by
  obtain ⟨y, hy, u, hu, μ, hμ, hcomp, hstat⟩ :=
    theorem_3_2_15_clarke hf hc hr hU hK hT hM hfeas hQ hmin
  exact ⟨y, clarkeSubgradient_subset_subdifferential hh hch hU hK hy,
    u, clarkeSubgradient_subset_subdifferential ht hct hT hM hu, μ, hμ, hcomp, hstat⟩

end CompositeKKT

end ConnGouldToint.Chapter03
