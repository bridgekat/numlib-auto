import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Duality.InnerPairing
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-! # Clarke directional derivatives and subgradients -/

open Filter Metric ConvexAnalysis
open scoped Topology RealInnerProductSpace NNReal

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private abbrev clarkeFilter (x : E) : Filter (E × ℝ) := 𝓝 x ×ˢ 𝓝[>] (0 : ℝ)

private noncomputable def clarkeQuotient (f : E → ℝ) (d : E) (p : E × ℝ) : ℝ :=
  (f (p.1 + p.2 • d) - f p.1) / p.2

/-- The Clarke directional derivative, given by the joint upper limit of difference
quotients as the base tends to `x` and the step size tends to zero from above.
The real upper limit is finite for a locally Lipschitz objective. -/
noncomputable def clarkeDerivative (f : E → ℝ) (x d : E) : ℝ :=
  limsup (clarkeQuotient f d) (clarkeFilter x)

private theorem tendsto_clarkeShift (x d : E) :
    Tendsto (fun p : E × ℝ ↦ (p.1 + p.2 • d, p.2)) (clarkeFilter x) (clarkeFilter x) := by
  have ht : Tendsto Prod.snd (clarkeFilter x) (𝓝[>] (0 : ℝ)) := tendsto_snd
  have ht₀ : Tendsto Prod.snd (clarkeFilter x) (𝓝 (0 : ℝ)) := ht.mono_right nhdsWithin_le_nhds
  have hs : Tendsto (fun p : E × ℝ ↦ p.2 • d) (clarkeFilter x) (𝓝 (0 : E)) := by
    simpa only [zero_smul] using ht₀.smul (tendsto_const_nhds (x := d))
  have hy : Tendsto Prod.fst (clarkeFilter x) (𝓝 x) := tendsto_fst
  have hh : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) (clarkeFilter x) (𝓝 x) := by
    simpa only [add_zero] using hy.add hs
  exact hh.prodMk ht

private theorem eventually_abs_clarkeQuotient_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : E) :
    ∀ᶠ p in clarkeFilter x, |clarkeQuotient f d p| ≤ (L : ℝ) * ‖d‖ := by
  let F := clarkeFilter x
  have hy : Tendsto Prod.fst F (𝓝 x) := tendsto_fst
  have ht : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
  have hy' : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) F (𝓝 x) :=
    tendsto_fst.comp (tendsto_clarkeShift x d)
  filter_upwards [hy.eventually hU, hy'.eventually hU,
    ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp hp' htp
  change 0 < p.2 at htp
  have h := hL.dist_le_mul _ hp' _ hp
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos htp] at h
  change |(f (p.1 + p.2 • d) - f p.1) / p.2| ≤ (L : ℝ) * ‖d‖
  rw [abs_div, abs_of_pos htp]
  apply (div_le_iff₀ htp).2
  convert h using 1
  ring
/-- The local Lipschitz constant bounds every Clarke directional derivative. -/
theorem abs_clarkeDerivative_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : E) :
    |clarkeDerivative f x d| ≤ (L : ℝ) * ‖d‖ := by
  let F := clarkeFilter x
  let q := clarkeQuotient f d
  have habs := eventually_abs_clarkeQuotient_le hU hL d
  have hlow := habs.mono fun _ hp ↦ (abs_le.mp hp).1
  have hupp := habs.mono fun _ hp ↦ (abs_le.mp hp).2
  have hb : F.IsBoundedUnder (· ≤ ·) q := ⟨_, hupp⟩
  have ha : F.IsBoundedUnder (· ≥ ·) q := ⟨_, hlow⟩
  change |limsup q F| ≤ (L : ℝ) * ‖d‖
  refine abs_le.mpr ⟨le_limsup_of_le hb (fun a ha' ↦ ?_),
    limsup_le_of_le ha.isCoboundedUnder_le hupp⟩
  obtain ⟨p, hp, hp'⟩ := (hlow.and ha').exists
  exact hp.trans hp'

/-- A Clarke directional derivative of a locally Lipschitz function is subadditive. -/
theorem clarkeDerivative_add_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d e : E) :
    clarkeDerivative f x (d + e) ≤ clarkeDerivative f x d + clarkeDerivative f x e := by
  let F := clarkeFilter x
  let T (p : E × ℝ) := (p.1 + p.2 • d, p.2)
  let u := clarkeQuotient f d
  let v := clarkeQuotient f e
  have ht : Tendsto T F F := tendsto_clarkeShift x d
  have hu := eventually_abs_clarkeQuotient_le hU hL d
  have hv := eventually_abs_clarkeQuotient_le hU hL e
  have hv' := ht.eventually hv
  have hulo : F.IsBoundedUnder (· ≥ ·) u := ⟨_, hu.mono fun _ h ↦ (abs_le.mp h).1⟩
  have huhi : F.IsBoundedUnder (· ≤ ·) u := ⟨_, hu.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hvhi : F.IsBoundedUnder (· ≤ ·) v := ⟨_, hv.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hv'lo : F.IsBoundedUnder (· ≥ ·) (v ∘ T) := ⟨_, hv'.mono fun _ h ↦ (abs_le.mp h).1⟩
  have hv'hi : F.IsBoundedUnder (· ≤ ·) (v ∘ T) := ⟨_, hv'.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hsplit : clarkeQuotient f (d + e) = u + v ∘ T := by
    funext p
    simp only [u, v, T, clarkeQuotient, Pi.add_apply, Function.comp_apply, smul_add, add_assoc]
    ring
  unfold clarkeDerivative
  rw [hsplit]
  refine (limsup_add_le hulo huhi hv'lo.isCoboundedUnder_le hv'hi).trans (add_le_add_right ?_ _)
  apply ht.limsup_comp_le_limsup _ hvhi
  exact hv'lo.isCoboundedUnder_le

omit [InnerProductSpace ℝ E] in
private theorem tendsto_clarkeScale (x : E) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : E × ℝ ↦ (p.1, a * p.2)) (clarkeFilter x) (clarkeFilter x) := by
  have ht : Tendsto Prod.snd (clarkeFilter x) (𝓝[>] (0 : ℝ)) := tendsto_snd
  have hm : Tendsto (fun p : E × ℝ ↦ a * p.2) (clarkeFilter x) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (ht.mono_right nhdsWithin_le_nhds).const_mul a
  have hm' : Tendsto (fun p : E × ℝ ↦ a * p.2) (clarkeFilter x) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hm, ?_⟩
    filter_upwards [ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)]
      with p hp
    exact mul_pos ha hp
  exact tendsto_fst.prodMk hm'

/-- A Clarke directional derivative of a locally Lipschitz function is positively homogeneous. -/
theorem clarkeDerivative_pos_smul {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) {a : ℝ} (ha : 0 < a) (d : E) :
    clarkeDerivative f x (a • d) = a * clarkeDerivative f x d := by
  let F := clarkeFilter x
  let T (p : E × ℝ) := (p.1, a * p.2)
  let S (p : E × ℝ) := (p.1, a⁻¹ * p.2)
  let q := clarkeQuotient f d
  have hm : map T F = F := by
    apply le_antisymm (tendsto_clarkeScale x ha)
    have hTS : T ∘ S = id := by
      funext p
      simp [T, S, ha.ne']
    calc
      F = map T (map S F) := by rw [map_map, hTS, map_id]
      _ ≤ map T F := map_mono (tendsto_clarkeScale x (inv_pos.mpr ha))
  have heq : clarkeQuotient f (a • d) =ᶠ[F] fun p ↦ a * q (T p) := by
    have ht : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
    filter_upwards [ht.eventually (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)]
      with p hp
    change 0 < p.2 at hp
    simp only [q, T, clarkeQuotient, smul_smul, mul_comm p.2 a]
    field_simp [ha.ne', hp.ne']
  have habs := eventually_abs_clarkeQuotient_le hU hL d
  have hb : F.IsBoundedUnder (· ≤ ·) q := ⟨_, habs.mono fun _ h ↦ (abs_le.mp h).2⟩
  have hl : F.IsBoundedUnder (· ≥ ·) q := ⟨_, habs.mono fun _ h ↦ (abs_le.mp h).1⟩
  have hba : F.IsBoundedUnder (· ≤ ·) (fun p ↦ a * q p) := ⟨a * _, habs.mono
    fun _ h ↦ mul_le_mul_of_nonneg_left (abs_le.mp h).2 ha.le⟩
  have hla : F.IsBoundedUnder (· ≥ ·) (fun p ↦ a * q p) := ⟨a * _, habs.mono
    fun _ h ↦ mul_le_mul_of_nonneg_left (abs_le.mp h).1 ha.le⟩
  unfold clarkeDerivative
  rw [limsup_congr heq, show (fun p ↦ a * q (T p)) = (fun p ↦ a * q p) ∘ T by rfl,
    limsup_comp, hm]
  exact ((OrderIso.mulLeft₀ a ha).limsup_apply hb hl.isCoboundedUnder_le
    hba hla.isCoboundedUnder_le).symm

/-- In its direction argument the Clarke derivative inherits the local Lipschitz
constant of the objective. -/
theorem lipschitzWith_clarkeDerivative {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) : LipschitzWith L (clarkeDerivative f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  have h (v w : E) : clarkeDerivative f x v - clarkeDerivative f x w ≤ (L : ℝ) * ‖v - w‖ := by
    have hadd := clarkeDerivative_add_le hU hL (v - w) w
    rw [sub_add_cancel] at hadd
    have hb := (le_abs_self _).trans (abs_clarkeDerivative_le hU hL (v - w))
    linarith
  exact ⟨h d e, by rw [norm_sub_rev d e]; exact h e d⟩

/-- The Clarke subdifferential consists of the vectors dominated by the directional
derivative in every direction. -/
def clarkeSubgradient (f : E → ℝ) (x : E) : Set E :=
  {g | ∀ d : E, ⟪g, d⟫ ≤ clarkeDerivative f x d}

theorem clarkeSubgradient_eq_iInter (f : E → ℝ) (x : E) :
    clarkeSubgradient f x = ⋂ d : E, {g | ⟪g, d⟫ ≤ clarkeDerivative f x d} := by
  ext g
  simp [clarkeSubgradient]

theorem isClosed_clarkeSubgradient (f : E → ℝ) (x : E) : IsClosed (clarkeSubgradient f x) := by
  rw [clarkeSubgradient_eq_iInter]
  exact isClosed_iInter fun _ ↦ isClosed_le (continuous_id.inner continuous_const) continuous_const

theorem convex_clarkeSubgradient (f : E → ℝ) (x : E) : Convex ℝ (clarkeSubgradient f x) := by
  rw [clarkeSubgradient_eq_iInter]
  refine convex_iInter fun d ↦ ?_
  exact (convex_Iic (clarkeDerivative f x d)).linear_preimage ((innerₗ E).flip d)

/-- The Clarke subdifferential of a locally Lipschitz function in finite dimension
is compact. Its vectors have norm at most the local Lipschitz constant. -/
theorem isCompact_clarkeSubgradient [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x)
    (hL : LipschitzOnWith L f U) : IsCompact (clarkeSubgradient f x) := by
  have := FiniteDimensional.proper_real E
  refine (isCompact_closedBall (0 : E) (L : ℝ)).of_isClosed_subset
    (isClosed_clarkeSubgradient f x) fun g hg ↦ ?_
  apply mem_closedBall_zero_iff.mpr
  by_cases hzero : g = 0
  · simp [hzero]
  have h : ⟪g, g⟫ ≤ clarkeDerivative f x g := hg g
  rw [real_inner_self_eq_norm_sq, pow_two] at h
  exact le_of_mul_le_mul_right (h.trans ((le_abs_self _).trans
    (abs_clarkeDerivative_le hU hL g))) (norm_pos_iff.mpr hzero)

/-- The Clarke support representation (3.1.4). -/
def HasClarkeSupport (f : E → ℝ) (x : E) : Prop :=
  ∀ d, supportFn (innerₗ E) (clarkeSubgradient f x) d = (clarkeDerivative f x d : EReal)

/-- The Clarke support identity. The sublinear directional derivative is the support
function of its dominated vectors. The support representation for closed homogeneous
convex functions follows from separation. -/
theorem hasClarkeSupport_of_lipschitzOnWith [CompleteSpace E]
    {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x)
    (hL : LipschitzOnWith L f U) : HasClarkeSupport f x := by
  let g (d : E) : EReal := clarkeDerivative f x d
  have hph : PosHomogeneous g := by
    intro a ha d
    simp only [g, clarkeDerivative_pos_smul hU hL ha, EReal.coe_mul]
  have hconv : ConvexFn g := (convexFn_iff_le fun _ ↦ EReal.coe_ne_bot _).2 <| by
    intro d e a b ha hb _
    simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simpa only [clarkeDerivative_pos_smul hU hL ha, clarkeDerivative_pos_smul hU hL hb] using
      clarkeDerivative_add_le hU hL (a • d) (b • e)
  have hcont : Continuous g :=
    continuous_coe_real_ereal.comp (lipschitzWith_clarkeDerivative hU hL).continuous
  have hc : ClosedConvex g :=
    (closedConvex_iff_lowerSemicontinuous fun _ ↦ EReal.coe_ne_bot _).2
      hcont.lowerSemicontinuous
  have hset : supportSet (innerₗ E).flip g = clarkeSubgradient f x := by
    ext z
    simp only [clarkeSubgradient, Set.mem_ofPred_eq, mem_supportSet, g,
      LinearMap.flip_apply, innerₗ_apply_apply, EReal.coe_le_coe_iff]
  have hs := supportFn_supportSet (B := innerₗ E) hph hconv hc ⟨0, EReal.coe_ne_top _⟩
  rw [hset] at hs
  exact congrFun hs

theorem HasClarkeSupport.nonempty {f : E → ℝ} {x : E} (h : HasClarkeSupport f x) :
    (clarkeSubgradient f x).Nonempty := by
  by_contra hn
  have h₀ := h 0
  rw [Set.not_nonempty_iff_eq_empty.mp hn, supportFn_empty] at h₀
  exact EReal.bot_ne_coe _ h₀

end Optimization
