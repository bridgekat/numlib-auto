/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Uniform`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Uniform
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani

/-!
# The Milman–Pettis theorem

**Every uniformly convex Banach space is reflexive**
(`NormedSpace.isReflexive_of_uniformConvexSpace`, registered as the instance
`NormedSpace.instIsReflexiveOfUniformConvexSpace`). Uniform convexity is Mathlib's
`UniformConvexSpace E`, a property of real normed spaces, so the theorem is stated over `ℝ`;
reflexivity is `NormedSpace.IsReflexive ℝ E`.

The proof is the classical one. Given `ξ` of norm `1` in the bidual and `ε > 0`, let `δ` be the
modulus of convexity for `ε / 2` (`exists_forall_closed_ball_dist_add_le_two_sub`: `‖x + y‖ ≤ 2 - δ`
whenever `‖x‖, ‖y‖ ≤ 1` and `ε / 2 ≤ ‖x - y‖`) and pick `f` in the dual ball with
`ξ f > 1 - δ / 4`. The weak-∗ neighbourhood `V = {η | |η f - ξ f| < δ / 4}` of `ξ` meets `J(B_E)` in
some `J x` by Goldstine's lemma (`NormedSpace.goldstine`). If `‖ξ - J x‖ > ε / 2`, the complement
`W` of the norm ball `J x + (ε/2) B` is a weak-∗ neighbourhood of `ξ` too, so `V ∩ W` meets `J(B_E)`
in some `J y` with `‖x - y‖ > ε / 2`; but then `2 ξ f < f (x + y) + δ / 2 ≤ ‖x + y‖ + δ / 2`
forces `‖x + y‖ > 2 - δ`, contradicting uniform convexity. Hence `ξ` is within `ε` of `J(B_E)` for
every `ε`, and `J(B_E)` is norm closed because `E` is complete
(`NormedSpace.isClosed_image_inclusionInDoubleDual_closedBall`), so `ξ ∈ J(B_E)`. Scaling handles
a general `ξ`.

Uniformly convex spaces have the Radon–Riesz property (`Numlib.Analysis.Convex.Uniform`); the
`L^p` spaces for `1 < p < ∞` are uniformly convex by Clarkson's inequalities, and this theorem is
one route to their reflexivity.

## References

[brezis2011functional] Theorem 3.31 (Milman–Pettis).
-/

open Filter Topology Metric Set Function

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [UniformConvexSpace E]

/-- The unit-norm case of the Milman–Pettis theorem: an element of norm `1` of the bidual lies
in `J(B_E)`. -/
private theorem mem_image_inclusionInDoubleDual_closedBall_of_norm_eq_one
    {ξ : StrongDual ℝ (StrongDual ℝ E)} (hξ : ‖ξ‖ = 1) :
    ξ ∈ inclusionInDoubleDual ℝ E '' closedBall (0 : E) 1 := by
  set J : E → StrongDual ℝ (StrongDual ℝ E) := ⇑(inclusionInDoubleDual ℝ E) with hJ
  have hJnorm : ∀ x y : E, ‖J x - J y‖ = ‖x - y‖ := fun x y => by
    rw [hJ, ← map_sub]; exact (inclusionInDoubleDualLi ℝ).norm_map (x - y)
  rw [← (isClosed_image_inclusionInDoubleDual_closedBall (𝕜 := ℝ) (E := E) 1).closure_eq,
    Metric.mem_closure_iff]
  intro ε hε
  -- the modulus of uniform convexity for `ε / 2`
  obtain ⟨δ, hδ, hconv⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (half_pos hε)
  -- an almost norming functional `f` for `ξ`
  obtain ⟨f₀, hf₀, hξf₀⟩ := ξ.exists_lt_apply_of_lt_opNorm (r := 1 - δ / 4) (by linarith)
  obtain ⟨f, hf, hξf⟩ : ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ 1 - δ / 4 < ξ f := by
    rcases le_or_gt 0 (ξ f₀) with h | h
    · exact ⟨f₀, hf₀.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h] at hξf₀⟩
    · refine ⟨-f₀, by rw [norm_neg]; exact hf₀.le, ?_⟩
      rw [map_neg]
      rwa [Real.norm_eq_abs, abs_of_neg h] at hξf₀
  -- Goldstine: every weak-∗ neighbourhood of `ξ` meets `J(B_E)`
  have hgold : ∀ U ∈ 𝓝 (StrongDual.toWeakDual ξ),
      ∃ x : E, ‖x‖ ≤ 1 ∧ StrongDual.toWeakDual (J x) ∈ U := by
    intro U hU
    have hmem : StrongDual.toWeakDual ξ ∈
        closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual ℝ E) '' closedBall (0 : E) 1) := by
      rw [goldstine]
      simp [hξ]
    obtain ⟨_, hU', ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hmem U hU
    exact ⟨x, mem_closedBall_zero_iff.1 hx, hU'⟩
  -- the weak-∗ neighbourhood `V = {η | |η f - ξ f| < δ / 4}` of `ξ`
  have hV : {η : WeakDual ℝ (StrongDual ℝ E) | |η f - ξ f| < δ / 4} ∈
      𝓝 (StrongDual.toWeakDual ξ) := by
    refine IsOpen.mem_nhds ?_ (by simp [hδ])
    have : Continuous fun η : WeakDual ℝ (StrongDual ℝ E) => |η f - ξ f| :=
      ((WeakDual.eval_continuous f).sub continuous_const).abs
    exact isOpen_lt this continuous_const
  obtain ⟨x, hx, hxV⟩ := hgold _ hV
  refine ⟨J x, ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  by_contra hcon
  push Not at hcon
  -- the complement of the norm ball `J x + (ε/2) B` is a weak-∗ neighbourhood of `ξ` too
  have hW : {η : WeakDual ℝ (StrongDual ℝ E) | ε / 2 < ‖WeakDual.toStrongDual η - J x‖} ∈
      𝓝 (StrongDual.toWeakDual ξ) := by
    have hmemW : StrongDual.toWeakDual ξ ∈
        {η : WeakDual ℝ (StrongDual ℝ E) | ε / 2 < ‖WeakDual.toStrongDual η - J x‖} := by
      simp only [mem_ofPred_eq, StrongDual.toStrongDual_toWeakDual]
      linarith
    refine IsOpen.mem_nhds ?_ hmemW
    have : IsClosed
        {η : WeakDual ℝ (StrongDual ℝ E) | ‖WeakDual.toStrongDual η - J x‖ ≤ ε / 2} := by
      have := WeakDual.isClosed_closedBall (J x) (ε / 2)
      convert this using 1
      ext η
      simp [dist_eq_norm]
    have hc : {η : WeakDual ℝ (StrongDual ℝ E) | ε / 2 < ‖WeakDual.toStrongDual η - J x‖} =
        {η : WeakDual ℝ (StrongDual ℝ E) | ‖WeakDual.toStrongDual η - J x‖ ≤ ε / 2}ᶜ := by
      ext η; simp
    rw [hc]
    exact this.isOpen_compl
  obtain ⟨y, hy, hyV, hyW⟩ := hgold _ (inter_mem hV hW)
  simp only [mem_ofPred_eq, StrongDual.toWeakDual_apply,
    StrongDual.toStrongDual_toWeakDual] at hxV hyV hyW
  rw [hJnorm] at hyW
  -- `x` and `y` are far apart while `x + y` is long: this contradicts uniform convexity
  have h1 := hconv hx hy (norm_sub_rev x y ▸ hyW.le)
  have h2 : f (x + y) ≤ ‖x + y‖ := by
    calc f (x + y) ≤ |f (x + y)| := le_abs_self _
      _ = ‖f (x + y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖x + y‖ := f.le_opNorm _
      _ ≤ 1 * ‖x + y‖ := by gcongr
      _ = ‖x + y‖ := one_mul _
  rw [map_add] at h2
  have hxV' := (abs_lt.1 hxV).1
  have hyV' := (abs_lt.1 hyV).1
  simp only [hJ, dual_def] at hxV' hyV'
  linarith

/-- **The Milman–Pettis theorem: a uniformly convex Banach space is reflexive.** Every element
of the bidual of norm `1` lies in `J(B_E)` (the argument in the module doc), and the rest by
scaling. -/
theorem isReflexive_of_uniformConvexSpace : IsReflexive ℝ E := by
  refine ⟨fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, map_zero _⟩
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨x, -, hx⟩ := mem_image_inclusionInDoubleDual_closedBall_of_norm_eq_one
    (ξ := ‖ξ‖⁻¹ • ξ) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ0.ne'])
  refine ⟨‖ξ‖ • x, ?_⟩
  rw [map_smul, hx, smul_smul, mul_inv_cancel₀ hξ0.ne', one_smul]

/-- The Milman–Pettis theorem as an instance: uniformly convex Banach spaces are reflexive, so
that uniform convexity (Clarkson's inequalities for `L^p`, `1 < p < ∞`) yields reflexivity by
instance search. Low priority, since Hilbert spaces are already reflexive by
`instIsReflexiveOfInnerProductSpace`. -/
instance (priority := 100) instIsReflexiveOfUniformConvexSpace : IsReflexive ℝ E :=
  isReflexive_of_uniformConvexSpace

end NormedSpace
