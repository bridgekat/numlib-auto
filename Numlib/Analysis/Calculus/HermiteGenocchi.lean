/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Thickening
import Numlib.Analysis.Calculus.HermiteInterpolation
import Numlib.Analysis.Calculus.SegmentAverage

/-!
# The Hermite–Genocchi bound for divided differences

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $f$ be smooth on a convex set of
$\mathbb{K}$. The divided difference of $f$ at $r + 1$ nodes of the set, repeated or not, satisfies
$\|f[x_0, \dots, x_r]\| \le M / r!$, where $M$ bounds $\|f^{(r)}\|$ on the set. This is (9.2.1) of
[golub2013matrix]. Over $\mathbb{R}$ the bound also follows from the mean value form
$f[x_0, \dots, x_r] = f^{(r)}(\xi)/r!$. Over $\mathbb{C}$ there is no mean value theorem, and the
bound comes from the Hermite–Genocchi formula
$$f[x_0, \dots, x_r] = \int_{\Sigma_r} f^{(r)}\Big(\sum_i t_i x_i\Big) \, dt$$
over the standard simplex $\Sigma_r$, whose volume is $1/r!$.

## Main results

* `Hermite.norm_divDiff_le_of_contDiffOn`: the bound for $f$ smooth on an open convex set $U$, with
  $M$ a bound of $\|f^{(r)}\|$ on a convex set $\Omega \subseteq U$ that contains the nodes.
* `Hermite.norm_divDiff_le`: the bound for $f$ analytic on a neighbourhood of a convex set.

## Proof outline

The simplex integral is not used. The proof is by induction on the number of nodes. Removing a node
divides by $z - a$ (`Hermite.divDiff_cons_eq_of_eventuallyEq`), which gives $f[a, s] = g[s]$ for the
segment average $g(z) = \int_0^1 f'(a + t(z - a)) \, dt$, and $\|g^{(r-1)}\| \le M / r$ on $\Omega$.
This is the Hermite–Genocchi formula, unrolled one simplex coordinate at a time.

## Implementation notes

* The segment average is taken from `Numlib.Analysis.Calculus.SegmentAverage`, and the node removal
  from `Numlib.Analysis.Calculus.HermiteInterpolation`.
* The segment average needs $U$ convex. An analytic $f$ is smooth on an open convex neighbourhood of
  the compact convex hull of the nodes, namely a thickening of that hull.
-/

open Set Filter Topology
open scoped ContDiff

private theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

namespace Hermite

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- The **Hermite–Genocchi bound** for a smooth function. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $U \subseteq \mathbb{K}$ be open and convex, and let $\Omega \subseteq U$ be
convex. Let $f : \mathbb{K} \to \mathbb{K}$ be $C^\infty$ on $U$, and let $M \in \mathbb{R}$
satisfy $\|f^{(r)}(z)\| \le M$ for all $z \in \Omega$. Then for every multiset $s$ of $r + 1$
nodes in $\Omega$, repeated or not,
$$\|f[s]\| \le \frac{M}{r!}.$$

Convexity is convexity over $\mathbb{R}$. The divided difference is `Hermite.divDiff`, and
$f^{(r)}$ is `iteratedDeriv r f`. -/
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

/-- The **Hermite–Genocchi bound** for an analytic function, (9.2.1) of [golub2013matrix]. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $\Omega \subseteq \mathbb{K}$ be convex, and
let $f : \mathbb{K} \to \mathbb{K}$ be analytic on a neighbourhood of each point of $\Omega$. If
$M \in \mathbb{R}$ satisfies $\|f^{(r)}(z)\| \le M$ for all $z \in \Omega$, then for every
multiset $s$ of $r + 1$ nodes in $\Omega$, repeated or not,
$$\|f[s]\| \le \frac{M}{r!}.$$

Convexity is convexity over $\mathbb{R}$. The proof applies
`Hermite.norm_divDiff_le_of_contDiffOn` on an open convex thickening of the convex hull of the
nodes. -/
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
