import Numlib.Optimization.ModelBased.ProjectedPath
import Numlib.Optimization.Optimality.ConstrainedMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Largest feasible linear decrease -/

open Metric Filter ConvexAnalysis
open scoped RealInnerProductSpace Topology

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} {x y v w d : E} {r s t : ℝ}

/-- The greatest value of a linear decrement over the feasible ball at `x`. -/
noncomputable def linearDecrease (C : Set E) (x v : E) (r : ℝ) : ℝ :=
  decrementMeasure (fun d ↦ ⟪v, d⟫) r (feasibleSteps C x)

omit [InnerProductSpace ℝ E] in
private theorem admissible_nonempty (hx : x ∈ C) (hr : 0 ≤ r) :
    (closedBall (0 : E) r ∩ feasibleSteps C x).Nonempty :=
  ⟨0, mem_closedBall_self hr, zero_mem_feasibleSteps.mpr hx⟩

private theorem bddAbove_inner :
    BddAbove ((fun d ↦ ⟪v, d⟫) '' (closedBall 0 r ∩ feasibleSteps C x)) :=
  ⟨‖v‖ * r, by
    rintro _ ⟨d, hd, rfl⟩
    exact (real_inner_le_norm v d).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) (norm_nonneg v))⟩

theorem inner_le_linearDecrease (hd : x + d ∈ C) (hn : ‖d‖ ≤ r) :
    ⟪v, d⟫ ≤ linearDecrease C x v r :=
  le_decrementMeasure bddAbove_inner ⟨mem_closedBall_zero_iff.mpr hn, hd⟩

theorem linearDecrease_le (hx : x ∈ C) (hr : 0 ≤ r) {b : ℝ}
    (h : ∀ d, x + d ∈ C → ‖d‖ ≤ r → ⟪v, d⟫ ≤ b) :
    linearDecrease C x v r ≤ b :=
  decrementMeasure_le (admissible_nonempty hx hr) fun d hd ↦
    h d hd.2 (mem_closedBall_zero_iff.mp hd.1)

theorem linearDecrease_nonneg (hx : x ∈ C) (hr : 0 ≤ r) : 0 ≤ linearDecrease C x v r :=
  decrementMeasure_nonneg bddAbove_inner (zero_mem_feasibleSteps.mpr hx) hr (inner_zero_right _)

theorem linearDecrease_mono_radius (hx : x ∈ C) (hs : 0 ≤ s) (hst : s ≤ t) :
    linearDecrease C x v s ≤ linearDecrease C x v t :=
  decrementMeasure_mono_radius (admissible_nonempty hx hs) bddAbove_inner hst

private theorem scale_linearDecrease_le (hc : Convex ℝ C) (hx : x ∈ C)
    (hs : 0 ≤ s) (ht : 0 < t) (hst : s ≤ t) :
    (s / t) * linearDecrease C x v t ≤ linearDecrease C x v s := by
  rw [linearDecrease, ← decrementMeasure_const_mul (div_nonneg hs ht.le)]
  apply decrementMeasure_le (admissible_nonempty hx ht.le)
  intro d hd
  have hsc := div_nonneg hs ht.le
  have hfeas := smul_mem_feasibleSteps hc hx hd.2 hsc ((div_le_one ht).mpr hst)
  have hnorm : ‖(s / t) • d‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsc]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) hsc).trans_eq
      (div_mul_cancel₀ s ht.ne')
  simpa only [real_inner_smul_right] using inner_le_linearDecrease (v := v) hfeas hnorm

/-- The largest feasible decrease divided by the positive radius is nonincreasing. -/
theorem linearDecrease_antitoneOn_ratio (hc : Convex ℝ C) (hx : x ∈ C) :
    AntitoneOn (fun r ↦ linearDecrease C x v r / r) (Set.Ioi 0) := by
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  apply (div_le_div_iff₀ ht hs).2
  have hscale := scale_linearDecrease_le (v := v) hc hx hs.le ht hst
  have hscale' : linearDecrease C x v t * s / t ≤ linearDecrease C x v s := by
    convert hscale using 1
    ring
  exact (div_le_iff₀ ht).1 hscale'

private theorem linearDecrease_sub_le_radius (hc : Convex ℝ C) (hx : x ∈ C)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    linearDecrease C x v t - linearDecrease C x v s ≤ (t - s) * ‖v‖ := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have ht := hs.trans_lt hst
  have hscale := scale_linearDecrease_le (v := v) hc hx hs ht hst.le
  have hbound : linearDecrease C x v t ≤ t * ‖v‖ :=
    decrementMeasure_inner_le (admissible_nonempty hx ht.le)
  have hmul := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr ((div_le_one ht).2 hst.le))
  have heq : (1 - s / t) * (t * ‖v‖) = (t - s) * ‖v‖ := by
    field_simp
  rw [heq] at hmul
  linarith

/-- Variation of the trust-region radius changes the measure by at most the radius
change times the norm of the linear direction. -/
theorem linearDecrease_lipschitzOnWith_radius (hc : Convex ℝ C) (hx : x ∈ C) :
    LipschitzOnWith ‖v‖₊ (linearDecrease C x v) (Set.Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  simp only [Real.dist_eq, coe_nnnorm]
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (linearDecrease_mono_radius hx hs h)),
      abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact linearDecrease_sub_le_radius hc hx hs h
  · rw [abs_of_nonneg (sub_nonneg.mpr (linearDecrease_mono_radius hx ht h)),
      abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact linearDecrease_sub_le_radius hc hx ht h

/-- The radius-one measure vanishes precisely when the linear direction is normal. -/
theorem linearDecrease_eq_zero_iff (hc : Convex ℝ C) (hx : x ∈ C) :
    linearDecrease C x v 1 = 0 ↔ v ∈ normalDirections C x := by
  rw [mem_normalDirections]
  constructor
  · intro h y hy
    let d := y - x
    let a := (1 + ‖d‖)⁻¹
    have hpos : 0 < a := by dsimp [a]; positivity
    have ha : a ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_right (norm_nonneg _))
    have hf : a • d ∈ feasibleSteps C x :=
      smul_mem_feasibleSteps hc hx (by simpa [d] using hy) hpos.le ha
    have hn : ‖a • d‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact (inv_mul_le_one₀ (by positivity : 0 < 1 + ‖d‖)).2 (by linarith)
    have hle := inner_le_linearDecrease (v := v) hf hn
    rw [h, real_inner_smul_right] at hle
    exact nonpos_of_mul_nonpos_right hle hpos
  · intro h
    refine le_antisymm (linearDecrease_le hx zero_le_one fun d hd _ ↦ ?_)
      (linearDecrease_nonneg hx zero_le_one)
    simpa using h (x + d) hd

private theorem linearDecrease_le_of_basePoint (hc : Convex ℝ C) (hx : x ∈ C) (hy : y ∈ C) :
    linearDecrease C x v 1 ≤ linearDecrease C y v 1 + 2 * ‖v‖ * ‖x - y‖ := by
  let h := ‖x - y‖
  have hh : 0 ≤ h := norm_nonneg _
  have hrad : (1 : ℝ) ≤ 1 + h := by linarith
  have h₁ := linearDecrease_sub_le_radius (v := v) hc hy zero_le_one hrad
  apply linearDecrease_le hx zero_le_one
  intro d hd hnorm
  let e := x + d - y
  have he : y + e ∈ C := by
    rwa [show y + e = x + d by dsimp [e]; abel]
  have heq : e = d + (x - y) := by dsimp [e]; abel
  have hen : ‖e‖ ≤ 1 + h := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add_left hnorm _)
  have h₂ := inner_le_linearDecrease (v := v) he hen
  rw [heq, inner_add_right] at h₂
  have h₃ : -⟪v, x - y⟫ ≤ ‖v‖ * h :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  linarith

private theorem abs_linearDecrease_sub_le_basePoint (hc : Convex ℝ C)
    (hx : x ∈ C) (hy : y ∈ C) :
    |linearDecrease C x v 1 - linearDecrease C y v 1| ≤ 2 * ‖v‖ * ‖x - y‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [linearDecrease_le_of_basePoint (v := v) hc hx hy]
  · have h := linearDecrease_le_of_basePoint (v := v) hc hy hx
    rw [norm_sub_rev y x] at h
    linarith

private theorem abs_linearDecrease_sub_le_direction (hx : x ∈ C) :
    |linearDecrease C x v 1 - linearDecrease C x w 1| ≤ ‖v - w‖ := by
  apply abs_decrementMeasure_sub_le (admissible_nonempty hx zero_le_one)
    bddAbove_inner bddAbove_inner
  intro d hd
  rw [← inner_sub_left]
  calc
    |⟪v - w, d⟫| ≤ ‖v - w‖ * ‖d‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v - w‖ := by simpa using
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) (norm_nonneg (v - w))

/-- The radius-one linear decrease varies continuously with the feasible base point
and a continuous linear direction. -/
theorem continuousOn_linearDecrease_one (hc : Convex ℝ C) {g : E → E}
    (hg : ContinuousOn g C) : ContinuousOn (fun x ↦ linearDecrease C x (g x) 1) C := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hgx : Tendsto (fun y ↦ ‖g y - g x‖) (𝓝[C] x) (𝓝 0) := by
    simpa only [dist_eq_norm] using tendsto_iff_dist_tendsto_zero.mp (hg x hx)
  have hyx : Tendsto (fun y ↦ ‖y - x‖) (𝓝[C] x) (𝓝 0) := by
    have h : Tendsto (fun y : E ↦ y) (𝓝[C] x) (𝓝 x) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [dist_eq_norm] using tendsto_iff_dist_tendsto_zero.mp h
  have hub : Tendsto (fun y ↦ ‖g y - g x‖ + 2 * ‖g x‖ * ‖y - x‖) (𝓝[C] x) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hgx.add (hyx.const_mul (2 * ‖g x‖))
  refine squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_ hub
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.dist_eq]
  calc
    _ ≤ |linearDecrease C y (g y) 1 - linearDecrease C y (g x) 1| +
        |linearDecrease C y (g x) 1 - linearDecrease C x (g x) 1| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (abs_linearDecrease_sub_le_direction hy)
      (abs_linearDecrease_sub_le_basePoint hc hy hx)

section Tangent

variable [CompleteSpace E]

/-- The tangent projection controls the improvement in the linear objective relative to
any feasible comparison step, with a signed directional term. -/
theorem linearDecrease_le_tangent (hx : x ∈ C) (hr : 0 ≤ r) :
    linearDecrease C x v r ≤ ⟪v, d⟫ +
      (r + ‖d‖) * ‖bestApprox (tangentDirections C (x + d)) v‖ := by
  let K := tangentDirections C (x + d)
  let p := bestApprox K v
  have hz : (0 : E) ∈ K := zero_mem_polarCone _ _
  have hcl : IsClosed K := isClosed_polarCone
  have hconv : Convex ℝ K := convex_polarCone _ _
  have hp : p ∈ K := bestApprox_mem ⟨0, hz⟩ hcl hconv _
  apply linearDecrease_le hx hr
  intro w hw hnorm
  have he : w - d ∈ K := by
    apply mem_polarCone.mpr
    intro n hn
    have h := mem_normalDirections.mp hn (x + w) hw
    simpa only [innerₗ_apply_apply, add_sub_add_left_eq_sub] using h
  have hpe : p + (w - d) ∈ K := (polarPointedCone _ _).add_mem hp he
  have h := inner_sub_bestApprox_le_zero ⟨0, hz⟩ hcl hconv v _ hpe
  have hlin : ⟪v, w - d⟫ ≤ ⟪p, w - d⟫ := by
    change ⟪v - p, p + (w - d) - p⟫ ≤ 0 at h
    rwa [add_sub_cancel_left, inner_sub_left, sub_nonpos] at h
  have hlen : ‖w - d‖ ≤ r + ‖d‖ :=
    (norm_sub_le _ _).trans (add_le_add_left hnorm _)
  have hbound : ⟪v, w - d⟫ ≤ (r + ‖d‖) * ‖p‖ :=
    hlin.trans ((real_inner_le_norm p _).trans (by
      rw [mul_comm ‖p‖]
      exact mul_le_mul_of_nonneg_right hlen (norm_nonneg p)))
  rw [inner_sub_right] at hbound
  exact sub_le_iff_le_add'.mp hbound

end Tangent

end Optimization
