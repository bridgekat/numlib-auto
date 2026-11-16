/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Dual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Basic

/-!
# A normed space with a separable dual is separable

Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$, with dual $E^*$. This module proves two
consequences of the Hahn–Banach theorem. First, a point outside a closed subspace $M$ is separated
from $M$ by a functional of norm $1$ that vanishes on $M$. Second, if $E^*$ is separable, then $E$
is separable. The converse fails: $\ell^1$ is separable, and its dual $\ell^\infty$ is not. In the
other direction, a separable space $E$ has a countable family of functionals of norm at most $1$
that determines the norm of $E$ up to the factor $3$. Finally, in a locally convex space, a point
outside a nonempty closed absolutely convex set $s$ is separated from $s$ by a functional $f$ with
$|f| \le 1$ on $s$.

## Main results

* `Submodule.exists_dual_eq_zero_of_notMem`: a point outside a closed subspace is separated from it
  by a functional of norm $1$ that vanishes on the subspace.
* `separableSpace_of_separableSpace_strongDual`: if $E^*$ is separable, then $E$ is separable.
* `exists_seq_strongDual_norming_of_separableSpace`: a separable normed space has a sequence $(f_n)$
  of functionals with $\|f_n\| \le 1$ such that every $x$ satisfies $\|x\| \le 3 |f_n(x)|$ for some
  $n$.
* `AbsConvex.exists_norm_apply_le_one_of_isClosed_of_notMem`: separation of a point from a nonempty
  closed absolutely convex set, in modulus.

## Proof outline

The separating functional is the Hahn–Banach theorem in the quotient $E / M$, which is a normed
space because $M$ is closed. For the separability of $E$, let $(f_n)$ be a dense sequence in $E^*$,
and pick $x_n$ in the closed unit ball with $\|f_n\| / 2 \le |f_n(x_n)|$. The closed span of the
$x_n$ is separable. If it were a proper subspace, the separation lemma would give a functional $g$
of norm $1$ that vanishes on it. A functional $f_n$ within $1/4$ of $g$ would then satisfy both
$|f_n(x_n)| \ge 3/8$ and $|f_n(x_n)| = |(f_n - g)(x_n)| \le 1/4$.
-/

open Function Metric TopologicalSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $M$ be a closed subspace of a normed space $E$ over $\mathbb{R}$ or $\mathbb{C}$, and let
$z \notin M$. Then there is $f \in E^*$ with $\|f\| = 1$, $f(y) = 0$ for every $y \in M$, and
$f(z) \ne 0$.

The quotient $E / M$ is a normed space because $M$ is closed, and the class of $z$ in it is
nonzero. The Hahn–Banach theorem (`exists_dual_vector`) gives a norming functional of this
class. Its composition with the quotient map, rescaled, is $f$. -/
theorem Submodule.exists_dual_eq_zero_of_notMem (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E))
    {z : E} (hz : z ∉ M) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧ (∀ y ∈ M, f y = 0) ∧ f z ≠ 0 := by
  have := hM
  have hmk : (Submodule.Quotient.mk z : E ⧸ M) ≠ 0 := fun h =>
    hz ((Submodule.Quotient.mk_eq_zero M).1 h)
  obtain ⟨g, -, hgz⟩ :=
    exists_dual_vector 𝕜 (Submodule.Quotient.mk z : E ⧸ M) (norm_ne_zero_iff.2 hmk)
  -- the quotient map is a norm-nonincreasing bounded linear map
  set q : E →L[𝕜] E ⧸ M :=
    M.mkQ.mkContinuous 1 fun x => by simpa using Submodule.Quotient.norm_mk_le M x with hq
  set f₀ : StrongDual 𝕜 E := g.comp q with hf₀
  have hzero : ∀ y ∈ M, f₀ y = 0 := fun y hy => by
    simp [hf₀, hq, (Submodule.Quotient.mk_eq_zero M).2 hy]
  have hfz : f₀ z ≠ 0 := by
    have : f₀ z = ((‖(Submodule.Quotient.mk z : E ⧸ M)‖ : ℝ) : 𝕜) := hgz
    rw [this]
    exact_mod_cast norm_ne_zero_iff.2 hmk
  have hf₀ : ‖f₀‖ ≠ 0 := fun h => hfz (by rw [norm_eq_zero.1 h]; simp)
  refine ⟨(‖f₀‖⁻¹ : 𝕜) • f₀, ?_, fun y hy => by simp [hzero y hy], ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hf₀]
  · simpa using ⟨by simpa using hf₀, hfz⟩

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. If the dual $E^*$ is separable,
then $E$ is separable. The converse fails: $\ell^1$ is separable, and it is the dual of the
separable space $c_0$, but its own dual $\ell^\infty$ is not separable. -/
theorem separableSpace_of_separableSpace_strongDual [SeparableSpace (StrongDual 𝕜 E)] :
    SeparableSpace E := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → StrongDual 𝕜 E, DenseRange f :=
    ⟨denseSeq _, denseRange_denseSeq _⟩
  -- almost-norming vectors in the closed unit ball
  have hex : ∀ n : ℕ, ∃ y : E, ‖y‖ ≤ 1 ∧ ‖f n‖ / 2 ≤ ‖f n y‖ := fun n => by
    rcases eq_or_lt_of_le (norm_nonneg (f n)) with h | h
    · exact ⟨0, by simp, by simp [← h]⟩
    · obtain ⟨y, hy1, hy2⟩ := (f n).exists_lt_apply_of_lt_opNorm (r := ‖f n‖ / 2) (by linarith)
      exact ⟨y, hy1.le, hy2.le⟩
  choose x hx1 hx2 using hex
  set M : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range x)).topologicalClosure with hM
  have hxM : ∀ n, x n ∈ M :=
    fun n => (Submodule.span 𝕜 (Set.range x)).le_topologicalClosure (Submodule.subset_span ⟨n, rfl⟩)
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨g, hg1, hg0, -⟩ :=
      M.exists_dual_eq_zero_of_notMem (Submodule.isClosed_topologicalClosure _) hz
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hf g (1 / 4) (by norm_num)
    rw [dist_eq_norm] at hn
    -- `f n` is close to `g`, so it is large, so it is large at `x n`
    have h1 : 3 / 4 < ‖f n‖ := by
      have hle := norm_le_norm_add_norm_sub' g (f n)
      rw [hg1] at hle
      linarith
    -- but `g` kills `x n`, so `f n (x n)` is small
    have h2 : ‖f n (x n)‖ ≤ 1 / 4 := by
      have hgx : g (x n) = 0 := hg0 _ (hxM n)
      have hrw : ‖f n (x n)‖ = ‖(g - f n) (x n)‖ := by simp [hgx]
      rw [hrw]
      calc ‖(g - f n) (x n)‖ ≤ ‖g - f n‖ * ‖x n‖ := (g - f n).le_opNorm _
        _ ≤ (1 / 4) * 1 := mul_le_mul hn.le (hx1 n) (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := by ring
    have := hx2 n
    linarith
  -- the closed span of a sequence is separable, and it is everything
  have hsep : IsSeparable ((Submodule.span 𝕜 (Set.range x) : Submodule 𝕜 E) : Set E) :=
    (Set.countable_range x).isSeparable.span
  rw [← isSeparable_univ_iff, ← Submodule.top_coe (R := 𝕜) (M := E), ← hMtop, hM,
    Submodule.topologicalClosure_coe]
  exact hsep.closure

/-- Let $E$ be a separable normed space over $\mathbb{R}$ or $\mathbb{C}$. Then there is a sequence
$(f_n)$ in the closed unit ball of $E^*$ such that every $x \in E$ satisfies
$\|x\| \le 3 |f_n(x)|$ for some $n$. In particular, the $f_n$ separate the points of $E$. This
is what makes a weakly compact subset of a separable space metrizable ([brezis2011functional],
Problem 10).

Take a dense sequence $(d_n)$ and functionals with $f_n(d_n) = \|d_n\|$ and $\|f_n\| \le 1$. For
$x$ and $n$ with $\|x - d_n\| < \|x\| / 3$, one has $|f_n(x)| \ge \|d_n\| - \|x - d_n\| \ge
\|x\| - 2 \|x - d_n\| > \|x\| / 3$. The constant $3$ is not sharp. -/
theorem exists_seq_strongDual_norming_of_separableSpace [SeparableSpace E] :
    ∃ f : ℕ → StrongDual 𝕜 E, (∀ n, ‖f n‖ ≤ 1) ∧ ∀ x : E, ∃ n, ‖x‖ ≤ 3 * ‖f n x‖ := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → E, DenseRange d := ⟨denseSeq E, denseRange_denseSeq E⟩
  choose f hf1 hf2 using fun n => exists_dual_vector'' 𝕜 (d n)
  refine ⟨f, hf1, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hd x (‖x‖ / 3) (by positivity)
  rw [dist_eq_norm] at hn
  refine ⟨n, ?_⟩
  have h1 : ‖f n (d n)‖ = ‖d n‖ := by rw [hf2, RCLike.norm_ofReal, abs_norm]
  have h2 : ‖f n (d n) - f n x‖ ≤ ‖x - d n‖ := by
    rw [← map_sub, ← norm_neg, ← map_neg, neg_sub]
    exact ((f n).le_of_opNorm_le (hf1 n) _).trans (by rw [one_mul])
  have h3 := norm_sub_norm_le (f n (d n)) (f n x)
  have h4 := norm_sub_norm_le x (d n)
  linarith

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

open scoped ComplexOrder in
/-- Separation from a closed absolutely convex set, in modulus. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $E$ be a topological vector space over $\mathbb{K}$ that is locally convex
as a real vector space. Let $s \subseteq E$ be nonempty, closed and absolutely convex, and let
$x \notin s$. Then there is a continuous linear functional $f$ on $E$ with $|f(a)| \le 1$ for
every $a \in s$ and $|f(x)| > 1$.

This is the polar form of the geometric Hahn–Banach theorem
`RCLike.geometric_hahn_banach_closed_point`. The bound $\operatorname{Re} g(a) < u$ on a
balanced set improves to $|g(a)| < u$, by rotating $a$ with a scalar of modulus $1$ that makes
$g(a)$ a nonnegative real number. The set must be nonempty: for $s = \emptyset$ and $x = 0$, no
functional has $|f(0)| > 1$. The order on $\mathbb{K}$ that `AbsConvex 𝕜 s` uses is the scoped
`ComplexOrder`, as in Mathlib's `LinearMap.polar_AbsConvex`. -/
theorem AbsConvex.exists_norm_apply_le_one_of_isClosed_of_notMem {s : Set E} (hs : AbsConvex 𝕜 s)
    (hne : s.Nonempty) (hc : IsClosed s) {x : E} (hx : x ∉ s) :
    ∃ f : StrongDual 𝕜 E, (∀ a ∈ s, ‖f a‖ ≤ 1) ∧ 1 < ‖f x‖ := by
  obtain ⟨g, u, hgs, hgx⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (convex_RCLike_iff_convex_real.1 hs.2) hc hx
  have h0 : (0 : E) ∈ s := hs.1.zero_mem hne
  have hu : 0 < u := by simpa using hgs 0 h0
  -- on a balanced set the real-part bound is a modulus bound
  have hnorm : ∀ a ∈ s, ‖g a‖ < u := by
    intro a ha
    rcases eq_or_ne (g a) 0 with h | h
    · rw [h, norm_zero]; exact hu
    set c : 𝕜 := (‖g a‖ : 𝕜) / g a with hc
    have hc1 : ‖c‖ = 1 := by
      rw [hc, norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 h)]
    have hca : c • a ∈ s := hs.1.smul_mem hc1.le ha
    have := hgs _ hca
    rwa [map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ h, RCLike.ofReal_re] at this
  refine ⟨((u⁻¹ : ℝ) : 𝕜) • g, fun a ha => ?_, ?_⟩
  · rw [smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hu),
      ← div_eq_inv_mul, div_le_one hu]
    exact (hnorm a ha).le
  · calc 1 = u⁻¹ * u := (inv_mul_cancel₀ hu.ne').symm
      _ < u⁻¹ * RCLike.re (g x) := by gcongr
      _ = RCLike.re ((((u⁻¹ : ℝ) : 𝕜) • g) x) := by
          rw [smul_apply, smul_eq_mul, RCLike.re_ofReal_mul]
      _ ≤ ‖(((u⁻¹ : ℝ) : 𝕜) • g) x‖ := RCLike.re_le_norm _

end LocallyConvex
