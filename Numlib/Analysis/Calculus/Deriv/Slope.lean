/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Deriv.Slope`, beside
`hasDerivAt_iff_tendsto_slope`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The sign of a function near a point where its derivative is positive

If `h 0 = 0` and `h' (0) > 0` then `h t > 0` and `h (−t) < 0` for all small `t > 0`
(`eventually_pos_and_neg_of_hasDerivAt_pos`): the slope `h t / t` is eventually positive
(`hasDerivAt_iff_tendsto_slope`), and its sign at `t` and at `−t` gives the two conclusions.

This is what puts a set on one side of a level surface: a function vanishing at a boundary point
with a positive normal derivative is positive just inside and negative just outside.
-/

open Filter Topology

/-- **The sign of a function near a point where its derivative is positive**: if `h 0 = 0` and
`h' (0) > 0`, then `h t > 0` and `h (−t) < 0` for all small `t > 0`. -/
theorem eventually_pos_and_neg_of_hasDerivAt_pos {h : ℝ → ℝ} {h' : ℝ} (hh : HasDerivAt h h' 0)
    (hh' : 0 < h') (h0 : h 0 = 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < h t ∧ h (-t) < 0 := by
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope h 0 t :=
    (hasDerivAt_iff_tendsto_slope.1 hh).eventually (lt_mem_nhds hh')
  rw [Metric.nhdsWithin_basis_ball.eventually_iff] at hev
  obtain ⟨ε, hε, hev⟩ := hev
  rw [Metric.nhdsWithin_basis_ball.eventually_iff]
  refine ⟨ε, hε, fun t ⟨ht, (ht0 : 0 < t)⟩ ↦ ?_⟩
  have h1 := hev ⟨ht, ht0.ne'⟩
  have h2 := hev (x := -t) ⟨by simpa using ht, by simpa using ht0.ne'⟩
  rw [slope_def_field, h0, sub_zero, sub_zero] at h1 h2
  refine ⟨(div_pos_iff_of_pos_right ht0).1 h1, ?_⟩
  rcases div_pos_iff.1 h2 with ⟨_, h3⟩ | ⟨h3, _⟩
  · linarith
  · exact h3
