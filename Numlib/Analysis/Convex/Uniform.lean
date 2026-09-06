/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Uniform`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The Radon–Riesz property

A normed space has the **Radon–Riesz property** (also called the Kadec–Klee property, or property
(H)) when weak convergence together with convergence of the norms implies convergence in norm. Every
uniformly convex space has it, and so does every inner product space, where the proof is the
expansion of `‖vₙ - u‖²` and needs neither completeness nor uniform convexity. Both statements are
[han2009theoretical] Exercises 2.7.3 and 2.7.4 (c).

## Main statements

* `tendsto_of_forall_dual_tendsto_of_tendsto_norm` — the uniformly convex case.
* `tendsto_of_forall_inner_tendsto_of_tendsto_norm` — the inner product case, as an `iff`.

## Implementation notes

Weak convergence is written in the sequential form `∀ ℓ, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))`
rather than through a weak topology, because that is the form in which the numerical-analysis
literature states it and the form the consumers of this module use.
-/

open Filter Topology RCLike
open scoped InnerProductSpace

section UniformConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

/-- **The Radon–Riesz property of a uniformly convex space.** If `vₙ ⇀ u` weakly and `‖vₙ‖ → ‖u‖`,
then `vₙ → u` in norm.

The proof normalizes both `vₙ` and `u` by `max ‖vₙ‖ ‖u‖`, so that the two vectors lie in the closed
unit ball, and tests the sum against a norming functional at `u`: `‖aₙ + bₙ‖ → 2` forces `‖aₙ - bₙ‖
→ 0` by uniform convexity. -/
theorem tendsto_of_forall_dual_tendsto_of_tendsto_norm {v : ℕ → E} {u : E}
    (hweak : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u)))
    (hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖)) :
    Tendsto v atTop (𝓝 u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using hnorm
  -- A norming functional at `u`.
  obtain ⟨ℓ, hℓ, hℓu⟩ := exists_dual_vector ℝ u (norm_ne_zero_iff.2 hu)
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  set t : ℕ → ℝ := fun n => max ‖v n‖ ‖u‖ with ht
  have htu : Tendsto t atTop (𝓝 ‖u‖) := by
    simpa [ht] using hnorm.max (tendsto_const_nhds (x := ‖u‖))
  have htpos : ∀ n, 0 < t n := fun n => lt_of_lt_of_le hu0 (le_max_right _ _)
  -- The normalized vectors lie in the closed unit ball.
  have hball : ∀ n, ‖(t n)⁻¹ • v n‖ ≤ 1 ∧ ‖(t n)⁻¹ • u‖ ≤ 1 := by
    refine fun n => ⟨?_, ?_⟩ <;>
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos n),
        inv_mul_le_iff₀ (htpos n), mul_one]
    exacts [le_max_left _ _, le_max_right _ _]
  have hℓu' : ℓ u = ‖u‖ := by simpa using hℓu
  -- Their sum has norm tending to `2`, because `ℓ` sees the full norm of `u`.
  have hsum : Tendsto (fun n => ‖(t n)⁻¹ • v n + (t n)⁻¹ • u‖) atTop (𝓝 2) := by
    have hlow : Tendsto (fun n => (t n)⁻¹ * (ℓ (v n) + ℓ u)) atTop (𝓝 2) := by
      have hval : (‖u‖)⁻¹ * (ℓ u + ℓ u) = 2 := by
        rw [hℓu']
        field_simp
        norm_num
      have := (htu.inv₀ hu0.ne').mul ((hweak ℓ).add (tendsto_const_nhds (x := ℓ u)))
      rwa [hval] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => ?_) (fun n => ?_)
    · have hb := ℓ.le_opNorm ((t n)⁻¹ • v n + (t n)⁻¹ • u)
      rw [hℓ, one_mul] at hb
      refine le_trans (le_trans (le_abs_self _) ?_) hb
      rw [← Real.norm_eq_abs, map_add, map_smul, map_smul]
      simp [smul_eq_mul, mul_add]
    · exact le_trans (norm_add_le _ _) (by linarith [(hball n).1, (hball n).2])
  -- Uniform convexity turns that into `‖vₙ - u‖ → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hconv⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub E (ε := ε / (‖u‖ + 1)) (by positivity)
  have hne : ∀ᶠ n in atTop, 2 - δ < ‖(t n)⁻¹ • v n + (t n)⁻¹ • u‖ :=
    hsum.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hne, htu.eventually (eventually_lt_nhds (show ‖u‖ < ‖u‖ + 1 by linarith))]
    with n hn hbd
  have hlt : ‖(t n)⁻¹ • v n - (t n)⁻¹ • u‖ < ε / (‖u‖ + 1) := by
    by_contra hcon
    push Not at hcon
    exact absurd (hconv (hball n).1 (hball n).2 hcon) (by linarith)
  rw [← smul_sub, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos n),
    inv_mul_lt_iff₀ (htpos n)] at hlt
  calc ‖‖v n - u‖‖ = ‖v n - u‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ < t n * (ε / (‖u‖ + 1)) := hlt
    _ ≤ (‖u‖ + 1) * (ε / (‖u‖ + 1)) := mul_le_mul_of_nonneg_right hbd.le (by positivity)
    _ = ε := by field_simp

end UniformConvex

section Inner

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Radon–Riesz property of an inner product space**, as a characterization of norm
convergence: `vₙ → u` in norm if and only if `⟪vₙ, w⟫ → ⟪u, w⟫` for every `w` and `‖vₙ‖ → ‖u‖`.

The forward direction is continuity of the inner product and of the norm; the converse is the
expansion `‖vₙ - u‖² = ‖vₙ‖² - 2 re ⟪vₙ, u⟫ + ‖u‖²`, so neither completeness nor uniform convexity
is used. -/
theorem tendsto_of_forall_inner_tendsto_of_tendsto_norm {v : ℕ → E} {u : E} :
    Tendsto v atTop (𝓝 u) ↔
      (∀ w : E, Tendsto (fun n => ⟪v n, w⟫_𝕜) atTop (𝓝 ⟪u, w⟫_𝕜)) ∧
        Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖) := by
  constructor
  · exact fun h => ⟨fun w => h.inner tendsto_const_nhds, h.norm⟩
  · rintro ⟨hinner, hnorm⟩
    have hsq : Tendsto (fun n => ‖v n - u‖ ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ⟪v n, u⟫_𝕜) atTop (𝓝 ⟪u, u⟫_𝕜) := hinner u
      have hre : Tendsto (fun n => re ⟪v n, u⟫_𝕜) atTop (𝓝 (‖u‖ ^ 2)) := by
        have := (RCLike.continuous_re (K := 𝕜)).continuousAt.tendsto.comp h1
        rwa [Function.comp_def, inner_self_eq_norm_sq (𝕜 := 𝕜)] at this
      have heq : ‖u‖ ^ 2 - 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 = 0 := by ring
      have h2 := ((hnorm.pow 2).sub (hre.const_mul 2)).add
        (tendsto_const_nhds (x := ‖u‖ ^ 2) (f := atTop (α := ℕ)))
      rw [heq] at h2
      simpa [norm_sub_sq (𝕜 := 𝕜)] using h2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.sqrt_sq, norm_nonneg] using hsq.sqrt

end Inner
