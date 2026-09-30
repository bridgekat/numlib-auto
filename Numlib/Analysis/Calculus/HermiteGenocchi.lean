import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Thickening
import Numlib.Analysis.Calculus.HermiteInterpolation
import Numlib.Analysis.Calculus.SegmentAverage

/-!
# The Hermite–Genocchi bound for divided differences

For `f` smooth on a convex set of `𝕜 = ℝ` or `ℂ`, the divided difference of `f` at `r + 1` nodes of
the set, repeated or not, is bounded by `M / r!`, where `M` bounds `‖f⁽ʳ⁾‖` on the set
([golub2013matrix] (9.2.1)). Over `ℝ` this is also a consequence of the mean value form
`f[x₀, …, x_r] = f⁽ʳ⁾(ξ)/r!`; over `ℂ` there is no mean value theorem, and the bound comes from
the Hermite–Genocchi formula `f[x₀, …, x_r] = ∫_{Σ_r} f⁽ʳ⁾(∑ tᵢ xᵢ) dt` over the standard simplex,
whose volume is `1/r!`.

## Main results

* `Hermite.norm_divDiff_le_of_contDiffOn`: the bound for `f` smooth on an open convex set `U`,
  with `M` bounding `‖f⁽ʳ⁾‖` on a convex `Ω ⊆ U` holding the nodes.
* `Hermite.norm_divDiff_le`: the bound for `f` analytic on a neighbourhood of a convex set.

## Implementation notes

The simplex integral is never written down. The proof is by induction on the number of nodes:
removing a node divides by `z - a` (`Hermite.divDiff_cons_eq_of_eventuallyEq` of
`Numlib/Analysis/Calculus/HermiteInterpolation`), which gives `f[a, s] = g[s]` for the segment
average `g z = ∫₀¹ f'(a + t(z - a)) dt` of `Numlib/Analysis/Calculus/SegmentAverage`, and
`‖g⁽ʳ⁻¹⁾‖ ≤ M / r` on `Ω`; this is the Hermite–Genocchi formula unrolled one simplex coordinate
at a time. The segment average needs `U` convex; an analytic `f` is smooth on an open convex
neighbourhood of the (compact) convex hull of the nodes, a thickening of it.
-/

open Set Filter Topology
open scoped ContDiff

private theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

namespace Hermite

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **The Hermite–Genocchi bound**, for a function smooth on an open convex set `U`: at `r + 1`
nodes in a convex `Ω ⊆ U`, `‖f[s]‖ ≤ M / r!` when `‖f⁽ʳ⁾‖ ≤ M` on `Ω`. -/
theorem norm_divDiff_le_of_contDiffOn {U Ω : Set 𝕜} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hΩ : Convex ℝ Ω) (hΩU : Ω ⊆ U) {f : 𝕜 → 𝕜} (hf : ContDiffOn 𝕜 ∞ f U) {r : ℕ}
    {s : Multiset 𝕜} (hs : Multiset.card s = r + 1) (hsΩ : ∀ x ∈ s, x ∈ Ω) {M : ℝ}
    (hM : ∀ z ∈ Ω, ‖iteratedDeriv r f z‖ ≤ M) :
    ‖divDiff f s‖ ≤ M / r.factorial := by
  induction r generalizing f s M with
  | zero =>
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hs
    simpa using hM x (hsΩ x (Multiset.mem_singleton_self x))
  | succ r ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card s)
    obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.card_cons, Nat.add_right_cancel_iff] at hs
    have haU : a ∈ U := hΩU (hsΩ a ha)
    obtain ⟨g, hgdef⟩ : ∃ g : 𝕜 → 𝕜, g = fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a)) :=
      ⟨_, rfl⟩
    have hg : ContDiffOn 𝕜 ∞ g U := by
      rw [hgdef]
      exact contDiffOn_integral_deriv_comp_segment hU hUc (n := ⊤) (by simpa using hf) haU
    have hf1 : ContDiffOn 𝕜 (1 : ℕ) f U := hf.of_le (natCast_le_infty _)
    have hf' : ∀ w ∈ U, HasDerivAt f (deriv f w) w := fun w hw => by
      simpa using hf1.hasDerivAt_iteratedDeriv_of_isOpen hU (j := 0) one_pos hw
    have hf'c : ContinuousOn (deriv f) U := by
      simpa using hf1.continuousOn_iteratedDeriv_of_isOpen hU le_rfl
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    have hfg : divDiff f (a ::ₘ s) = divDiff g s :=
      divDiff_cons_eq_of_eventuallyEq hs0
        (fun x hx => (hg.contDiffAt (hU.mem_nhds (hΩU (hsΩ x hx)))).of_le
          (by exact_mod_cast le_top))
        (fun x hx => eventually_of_mem (hU.mem_nhds (hΩU (hsΩ x hx))) fun w hw => by
          rw [hgdef]
          exact eq_add_mul_integral_comp_segment hUc hf' hf'c haU hw)
    have hbound : ∀ z ∈ Ω, ‖iteratedDeriv r g z‖ ≤ M / (r + 1) := fun z hz => by
      rw [hgdef, iteratedDeriv_integral_deriv_comp_segment hU hUc hf haU (natCast_le_infty _)
        (hΩU hz)]
      exact norm_integral_pow_smul_comp_segment_le r fun t ht =>
        hM _ (hΩ.add_smul_sub_mem (hsΩ a ha) hz ht)
    rw [hfg]
    refine (ih hg hs (fun x hx => hsΩ x (Multiset.mem_cons_of_mem hx)) hbound).trans_eq ?_
    rw [Nat.factorial_succ, Nat.cast_mul, div_div]
    push_cast
    ring

/-- **The Hermite–Genocchi bound** ([golub2013matrix] (9.2.1)): if `f` is analytic on a
neighbourhood of a convex set `Ω` and `‖f⁽ʳ⁾‖ ≤ M` on `Ω`, then the divided difference of `f` at
`r + 1` nodes of `Ω`, repeated or not, satisfies `‖f[s]‖ ≤ M / r!`. -/
theorem norm_divDiff_le {Ω : Set 𝕜} (hΩ : Convex ℝ Ω) {f : 𝕜 → 𝕜} (hf : AnalyticOnNhd 𝕜 f Ω)
    {r : ℕ} {s : Multiset 𝕜} (hs : Multiset.card s = r + 1) (hsΩ : ∀ x ∈ s, x ∈ Ω) {M : ℝ}
    (hM : ∀ z ∈ Ω, ‖iteratedDeriv r f z‖ ≤ M) :
    ‖divDiff f s‖ ≤ M / r.factorial := by
  obtain ⟨K, hK, hKc, hKΩ, hsK⟩ :
      ∃ K : Set 𝕜, IsCompact K ∧ Convex ℝ K ∧ K ⊆ Ω ∧ ∀ x ∈ s, x ∈ K :=
    ⟨convexHull ℝ {x | x ∈ s}, (Multiset.finite_toSet s).isCompact_convexHull ℝ,
      convex_convexHull ℝ _, convexHull_min (fun x hx => hsΩ x hx) hΩ,
      fun x hx => subset_convexHull ℝ {x | x ∈ s} hx⟩
  have hfK : AnalyticOnNhd 𝕜 f K := fun z hz => hf z (hKΩ hz)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open (isOpen_analyticAt 𝕜 f) hfK
  have hUo : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
  have hUc : Convex ℝ (Metric.thickening δ K) := hKc.thickening δ
  have hKU : K ⊆ Metric.thickening δ K := Metric.self_subset_thickening hδ K
  have hfU : AnalyticOnNhd 𝕜 f (Metric.thickening δ K) := fun z hz => hδU hz
  have hfU' : ContDiffOn 𝕜 ∞ f (Metric.thickening δ K) := hfU.contDiffOn_of_completeSpace
  exact norm_divDiff_le_of_contDiffOn hUo hUc hKc hKU hfU' hs hsK fun z hz => hM z (hKΩ hz)

end Hermite
