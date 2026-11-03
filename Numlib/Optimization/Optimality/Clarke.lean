import Numlib.Analysis.Convex.Duality.Support
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

/-- The Clarke directional derivative, given by the joint upper limit of difference
quotients as the base tends to `x` and the step size tends to zero from above.
The real upper limit is finite for a locally Lipschitz objective. -/
noncomputable def clarkeDerivative (f : E → ℝ) (x d : E) : ℝ :=
  limsup (fun p : E × ℝ ↦ (f (p.1 + p.2 • d) - f p.1) / p.2)
    (𝓝 x ×ˢ 𝓝[>] (0 : ℝ))

/-- The local Lipschitz constant bounds every Clarke directional derivative. -/
theorem abs_clarkeDerivative_le {f : E → ℝ} {x : E} {U : Set E} {L : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : E) :
    |clarkeDerivative f x d| ≤ (L : ℝ) * ‖d‖ := by
  let F := 𝓝 x ×ˢ 𝓝[>] (0 : ℝ)
  let q (p : E × ℝ) := (f (p.1 + p.2 • d) - f p.1) / p.2
  have hy : Tendsto Prod.fst F (𝓝 x) := tendsto_fst
  have ht : Tendsto Prod.snd F (𝓝[>] (0 : ℝ)) := tendsto_snd
  have ht₀ : Tendsto Prod.snd F (𝓝 (0 : ℝ)) := ht.mono_right nhdsWithin_le_nhds
  have hstep : Tendsto (fun p : E × ℝ ↦ p.2 • d) F (𝓝 (0 : E)) := by
    simpa only [zero_smul] using ht₀.smul (tendsto_const_nhds (x := d))
  have hy' : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • d) F (𝓝 x) := by
    simpa only [add_zero] using hy.add hstep
  have habs : ∀ᶠ p in F, |q p| ≤ (L : ℝ) * ‖d‖ := by
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
  have hlow := habs.mono fun _ hp ↦ (abs_le.mp hp).1
  have hupp := habs.mono fun _ hp ↦ (abs_le.mp hp).2
  have hb : F.IsBoundedUnder (· ≤ ·) q := ⟨_, hupp⟩
  have ha : F.IsBoundedUnder (· ≥ ·) q := ⟨_, hlow⟩
  change |limsup q F| ≤ (L : ℝ) * ‖d‖
  refine abs_le.mpr ⟨le_limsup_of_le hb (fun a ha' ↦ ?_),
    limsup_le_of_le ha.isCoboundedUnder_le hupp⟩
  obtain ⟨p, hp, hp'⟩ := (hlow.and ha').exists
  exact hp.trans hp'

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

/-- The support representation (3.1.4), here isolated as the prerequisite to
the minimum-norm characterization. -/
def HasClarkeSupport (f : E → ℝ) (x : E) : Prop :=
  ∀ d, supportFn (innerₗ E) (clarkeSubgradient f x) d = (clarkeDerivative f x d : EReal)

theorem HasClarkeSupport.nonempty {f : E → ℝ} {x : E} (h : HasClarkeSupport f x) :
    (clarkeSubgradient f x).Nonempty := by
  by_contra hn
  have h₀ := h 0
  rw [Set.not_nonempty_iff_eq_empty.mp hn, supportFn_empty] at h₀
  exact EReal.bot_ne_coe _ h₀

end Optimization
