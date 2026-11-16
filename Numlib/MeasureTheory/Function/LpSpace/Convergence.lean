/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum` (the dominated subsequence)
and `Mathlib.MeasureTheory.Function.LpSpace.Indicator` (the infinite dimension of `L^p`).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# A dominated subsequence of a sequence that converges in $L^p$

Let $1 \le p \le \infty$. A sequence that converges in $L^p$ has a subsequence that converges almost
everywhere and is dominated by a single function in $L^p$: there are $n_0 < n_1 < \cdots$ and
$h \in L^p$ with $f_{n_k} \to g$ almost everywhere and $\|f_{n_k}(x)\| \le h(x)$ for almost every
$x$ and every $k$. This is Theorem 4.9 of [brezis2011functional]. Mathlib has the first part:
convergence in $L^p$ gives convergence in measure
(`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`), and convergence in measure gives a
subsequence that converges almost everywhere
(`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`). The domination makes the dominated
convergence theorem available after the passage to a subsequence. The Sobolev theory uses it in this
role for chain rules, truncations and traces.

The file also proves that $L^p(U, \mu)$ is infinite-dimensional for a nonempty open set $U$ of a
nontrivial real normed space and a locally finite measure $\mu$ that is positive on nonempty open
sets. This is the hypothesis of infinite dimension in the spectral theorem for the Dirichlet
Laplacian. Finally, an element of $L^\infty$ is bounded almost everywhere by its norm.

## Main results

* `MeasureTheory.exists_subseq_tendsto_ae_ae_le_of_tendsto_eLpNorm`: the dominated subsequence, for
  functions in $L^p$.
* `MeasureTheory.Lp.exists_subseq_tendsto_ae_ae_le_of_tendsto`: the dominated subsequence, for
  elements of the space `MeasureTheory.Lp`.
* `MeasureTheory.Lp.not_finiteDimensional_of_isOpen`: $L^p(U, \mu)$ is infinite-dimensional.
* `MeasureTheory.Lp.ae_norm_le_norm_top`: $\|u(x)\| \le \|u\|_\infty$ for almost every $x$.

## Proof outline

The dominated subsequence comes from the telescoping series of the Riesz–Fischer theorem, with
Mathlib's `MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top` and
`MeasureTheory.Lp.hasSum_coeFn_tsum`. Choose a subsequence with $\|f_{n_k} - g\|_p \le 2^{-k}$. The
series $\sum_k \|f_{n_k} - g\|$ converges in $L^p$ and hence almost everywhere. So its sum dominates
every term, and the terms tend to zero almost everywhere. The case $p = \infty$ needs no separate
argument.

For the infinite dimension, the indicator functions of a sequence of disjoint annuli around a point
of $U$ are linearly independent in $L^p(U, \mu)$.

## Implementation notes

* The instance `MeasureTheory.fact_one_le_of_one_lt` derives `Fact (1 ≤ p)` from `Fact (1 < p)`. An
  instance stated under `[Fact (1 < p)] [Fact (p ≠ ∞)]`, such as uniform convexity or reflexivity of
  `MeasureTheory.Lp`, then finds the normed structure of `Lp E p μ`.
-/

noncomputable section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]

/-- The hypothesis $1 < p$ implies $1 \le p$. With this instance, a statement about `Lp E p μ` under
`[Fact (1 < p)] [Fact (p ≠ ∞)]`, the form of $1 < p < \infty$ for instances, finds the normed
structure of `Lp E p μ`, which needs `Fact (1 ≤ p)`. -/
instance (priority := 100) fact_one_le_of_one_lt [h : Fact (1 < p)] : Fact (1 ≤ p) := ⟨h.out.le⟩

/-- **The dominated subsequence**, for functions in $L^p$. Let $1 \le p \le \infty$, let $E$ be a
normed group, and let $f_n, g \colon \alpha \to E$ be functions in $L^p(\mu)$ with
$\|f_n - g\|_p \to 0$. Then there are a strictly increasing sequence $n_0 < n_1 < \cdots$ of
indices and a real function $h \in L^p(\mu)$ such that $f_{n_k}(x) \to g(x)$ for $\mu$-almost
every $x$, and, for every $k$,
$$\|f_{n_k}(x)\| \le h(x) \quad \text{for } \mu\text{-almost every } x.$$
This is Theorem 4.9 of [brezis2011functional].

The dominating function is $h = \|g\| + \sum_k \|f_{n_k} - g\|$, where the series converges in
$L^p$ and hence almost everywhere. -/
theorem exists_subseq_tendsto_ae_ae_le_of_tendsto_eLpNorm [Fact (1 ≤ p)] {f : ℕ → α → E}
    {g : α → E} (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ h : α → ℝ, MemLp h p μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x))) ∧
      ∀ k, ∀ᵐ x ∂μ, ‖f (ns k) x‖ ≤ h x := by
  -- a subsequence along which the `L^p` distances are summable
  obtain ⟨ns, hns, hle⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ k, eLpNorm (f (ns k) - g) p μ ≤ (2⁻¹ : ℝ≥0∞) ^ k :=
    extraction_forall_of_eventually fun k =>
      ENNReal.tendsto_nhds_zero.1 hfg _ (ENNReal.pow_pos (by simp) k)
  -- the norms of the differences, as elements of `Lp ℝ p μ`
  let d : ℕ → Lp ℝ p μ := fun k => ((hf (ns k)).sub hg).norm.toLp _
  have hd_coe : ∀ᵐ x ∂μ, ∀ k, d k x = ‖f (ns k) x - g x‖ :=
    ae_all_iff.2 fun k => MemLp.coeFn_toLp _
  have hd_enorm : ∀ k, ‖d k‖ₑ = eLpNorm (f (ns k) - g) p μ := fun k => by
    rw [Lp.enorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _),
      eLpNorm_norm _ ((hf (ns k)).sub hg).aestronglyMeasurable]
  have hd_sum : ∑' k, ‖d k‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.tsum_geometric_two ▸ ENNReal.ofNat_ne_top)
      (tsum_le_tsum fun k => ?_)
    rw [hd_enorm]
    exact hle k
  -- the series converges pointwise almost everywhere
  have hpt := Lp.hasSum_coeFn_tsum hd_sum
  refine ⟨ns, hns, fun x => ‖g x‖ + (∑' k, d k) x, hg.norm.add (Lp.memLp _), ?_, fun k => ?_⟩
  · filter_upwards [hpt, hd_coe] with x hx hxk
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have := hx.summable.tendsto_atTop_zero
    simpa only [hxk] using this
  · filter_upwards [hpt, hd_coe] with x hx hxk
    calc ‖f (ns k) x‖ ≤ ‖g x‖ + ‖f (ns k) x - g x‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖g x‖ + (∑' j, d j) x := by
        gcongr
        rw [← hxk k]
        exact le_hasSum hx k fun j _ => by rw [hxk]; positivity

/-- **The dominated subsequence**, for elements of the space `MeasureTheory.Lp`. Let
$1 \le p \le \infty$, let $E$ be a normed group, and let $f_n \to g$ in $L^p(\mu; E)$. Then
there are a strictly increasing sequence $n_0 < n_1 < \cdots$ of indices and
$h \in L^p(\mu; \mathbb{R})$ such that $f_{n_k}(x) \to g(x)$ for $\mu$-almost every $x$, and,
for every $k$, $\|f_{n_k}(x)\| \le h(x)$ for $\mu$-almost every $x$. This is Theorem 4.9 of
[brezis2011functional]. -/
theorem Lp.exists_subseq_tendsto_ae_ae_le_of_tendsto [Fact (1 ≤ p)] {f : ℕ → Lp E p μ}
    {g : Lp E p μ} (hfg : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ h : Lp ℝ p μ,
      (∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x))) ∧
      ∀ k, ∀ᵐ x ∂μ, ‖f (ns k) x‖ ≤ h x := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hfg
  obtain ⟨ns, hns, h, hh, hlim, hle⟩ :=
    exists_subseq_tendsto_ae_ae_le_of_tendsto_eLpNorm (fun n => Lp.memLp (f n)) (Lp.memLp g) hfg
  refine ⟨ns, hns, hh.toLp h, hlim, fun k => ?_⟩
  filter_upwards [hle k, hh.coeFn_toLp] with x hx hx' using hx' ▸ hx

section Infinite

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Nontrivial G] [MeasurableSpace G]
  [OpensMeasurableSpace G]

/-- **$L^p$ of a nonempty open set is infinite-dimensional.** Let $G$ be a nontrivial real normed
space in which open sets are measurable, and let $\mu$ be a locally finite measure on $G$ that
is positive on nonempty open sets, for example a Haar measure on a finite-dimensional space, in
particular the Lebesgue measure on $\mathbb{R}^n$. Let $U \subseteq G$ be a nonempty open set
and let $p \in [0, \infty]$. Then the real space $L^p(U, \mu)$ is not finite-dimensional.

The space $L^p(U, \mu)$ is `Lp ℝ p (μ.restrict U)`. The indicator functions of a sequence of
disjoint annuli around a point of $U$ are linearly independent. This is the hypothesis of
infinite dimension in the spectral theorem for the Dirichlet problem, Theorems 8.22 and 9.31 of
[brezis2011functional]. -/
theorem Lp.not_finiteDimensional_of_isOpen (μ : Measure G) [μ.IsOpenPosMeasure]
    [IsLocallyFiniteMeasure μ] (p : ℝ≥0∞) {U : Set G} (hU : IsOpen U) (hne : U.Nonempty) :
    ¬ FiniteDimensional ℝ (Lp ℝ p (μ.restrict U)) := by
  intro hfin
  obtain ⟨x₀, hx₀⟩ := hne
  -- a ball around `x₀` inside `U` of finite measure
  obtain ⟨r, hr, hrU, hrfin⟩ : ∃ r > 0, ball x₀ r ⊆ U ∧ μ (ball x₀ r) < ∞ := by
    obtain ⟨s, hs, hμs⟩ := μ.finiteAt_nhds x₀
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hx₀) hs)
    exact ⟨r, hr, hrs.trans inter_subset_left,
      (measure_mono (hrs.trans inter_subset_right)).trans_lt hμs⟩
  -- the annuli
  let A : ℕ → Set G := fun n => ball x₀ (r / (n + 1)) \ closedBall x₀ (r / (n + 2))
  have hAU : ∀ n, A n ⊆ U := fun n =>
    (sdiff_subset.trans (ball_subset_ball (div_le_self hr.le (by norm_cast; omega)))).trans hrU
  have hAopen : ∀ n, IsOpen (A n) := fun n => isOpen_ball.sdiff isClosed_closedBall
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n => (hAopen n).measurableSet
  have hAne : ∀ n, (A n).Nonempty := fun n => by
    have h1 : r / (n + 2) < r / (n + 1) := by gcongr; linarith
    obtain ⟨v, hv⟩ := exists_norm_eq G (show 0 ≤ (r / (n + 2) + r / (n + 1)) / 2 by positivity)
    refine ⟨x₀ + v, ?_, ?_⟩
    · rw [mem_ball, _root_.dist_eq_norm, add_sub_cancel_left, hv]; linarith
    · rw [mem_closedBall, _root_.dist_eq_norm, add_sub_cancel_left, hv, not_le]; linarith
  have hApos : ∀ n, 0 < μ.restrict U (A n) := fun n => by
    rw [Measure.restrict_eq_self _ (hAU n)]
    exact (hAopen n).measure_pos μ (hAne n)
  have hAfin : ∀ n, μ.restrict U (A n) ≠ ∞ := fun n => by
    rw [Measure.restrict_eq_self _ (hAU n)]
    exact ((measure_mono (sdiff_subset.trans (ball_subset_ball
      (div_le_self hr.le (by norm_cast; omega))))).trans_lt hrfin).ne
  have hAdisj : Pairwise fun m n => Disjoint (A m) (A n) := by
    -- for `m < n`, `A n` lies inside the inner closed ball of `A m`
    have key : ∀ m n, m < n → Disjoint (A m) (A n) := fun m n hmn => by
      refine Set.disjoint_left.2 fun x hxm hxn => hxm.2 ?_
      have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
      have : r / (n + 1) ≤ r / (m + 2) :=
        div_le_div_of_nonneg_left hr.le (by positivity) (by linarith)
      exact mem_closedBall.2 (hxn.1.le.trans this)
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm
  -- the indicators are linearly independent
  let e : ℕ → Lp ℝ p (μ.restrict U) := fun n => indicatorConstLp p (hAmeas n) (hAfin n) (1 : ℝ)
  have hli : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro s c hsum j hj
    -- the linear combination is a.e. zero and equals `c j` on `A j`
    have h0 : (fun x => ∑ i ∈ s, c i * (A i).indicator (fun _ => (1 : ℝ)) x)
        =ᵐ[μ.restrict U] 0 := by
      have h1 := Lp.coeFn_fun_finsetSum s fun i => c i • e i
      rw [hsum] at h1
      have h2 : ∀ᵐ x ∂μ.restrict U, ∀ i ∈ s,
          (c i • e i : Lp ℝ p (μ.restrict U)) x = c i * (A i).indicator (fun _ => (1 : ℝ)) x := by
        rw [eventually_all_finset]
        intro i _
        filter_upwards [Lp.coeFn_smul (c i) (e i), indicatorConstLp_coeFn (p := p) (hs := hAmeas i)
          (hμs := hAfin i) (c := (1 : ℝ))] with x hx hx'
        simp [e, hx, hx']
      filter_upwards [h1, h2, Lp.coeFn_zero ℝ p (μ.restrict U)] with x hx hx' hx0
      simp only [Pi.zero_apply]
      rw [Finset.sum_congr rfl fun i hi => (hx' i hi).symm, ← hx, hx0, Pi.zero_apply]
    have h3 : ∀ᵐ x ∂(μ.restrict U).restrict (A j), c j = 0 := by
      rw [ae_restrict_iff' (hAmeas j)]
      filter_upwards [h0] with x hx hxj
      have : ∑ i ∈ s, c i * (A i).indicator (fun _ => (1 : ℝ)) x = c j := by
        rw [Finset.sum_eq_single j]
        · simp [Set.indicator_of_mem hxj]
        · intro i _ hij
          simp [Set.indicator_of_notMem (Set.disjoint_left.1 (hAdisj hij.symm) hxj)]
        · intro h; exact absurd hj h
      rw [← this]
      exact hx
    have hne : (μ.restrict U).restrict (A j) ≠ 0 := by
      intro h
      have := congrArg (fun ν : Measure G => ν univ) h
      simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact (hApos j).ne' this
    have : (ae ((μ.restrict U).restrict (A j))).NeBot := ae_neBot.2 hne
    exact h3.exists.choose_spec
  exact Module.Finite.not_linearIndependent_of_infinite e hli

end Infinite

/-! ### Elements of $L^\infty$ are bounded by their norm -/

namespace Lp

/-- Let $E$ be a normed group. Every $u \in L^\infty(\mu; E)$ satisfies $\|u(x)\| \le \|u\|_\infty$
for $\mu$-almost every $x$. -/
theorem ae_norm_le_norm_top (u : Lp E ∞ μ) :
    ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖u‖ := by
  have hne : eLpNormEssSup (⇑u) μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
    exact Lp.eLpNorm_ne_top u
  filter_upwards [ae_le_eLpNormEssSup (f := ⇑u) (μ := μ)] with x hx
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hx

end Lp

end MeasureTheory
