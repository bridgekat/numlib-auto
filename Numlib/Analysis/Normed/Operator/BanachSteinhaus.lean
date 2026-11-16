/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The convergence half of the Banach–Steinhaus theorem, and its corollaries

Mathlib's `banach_steinhaus` is the uniform boundedness principle: a pointwise bounded family of
bounded linear operators on a Banach space is bounded in norm. This file adds the convergence half
that the applications use: a uniformly bounded family that converges pointwise on a dense set to a
bounded operator $L$ converges pointwise everywhere to $L$. This half needs neither completeness nor
a Baire argument. Together with the uniform boundedness principle it gives, on a Banach space, the
criterion by which a family of quadrature rules, or of interpolation projections, is shown to
converge on all of $C[a, b]$ from its convergence on the polynomials.

The file also proves the corollaries of the uniform boundedness principle in [brezis2011functional],
§2.2, that Mathlib does not state: the lower semicontinuity of the operator norm under pointwise
convergence (Corollary 2.3(c)), and the two statements "weakly bounded implies bounded" (Corollary
2.4) and "weak-∗ bounded implies bounded" (Corollary 2.5).

## Main results

* `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`: a uniformly bounded family that
  converges pointwise on a dense set to a bounded operator converges pointwise everywhere, along an
  arbitrary filter on an arbitrary index type.
* `ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace`: on a Banach space, a sequence
  of operators converges pointwise everywhere if and only if it converges on a dense set and is
  uniformly bounded.
* `ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove`: if the operator norms are unbounded,
  some vector has images that do not converge to a given limit. With the Lebesgue constants of the
  Fourier projections, this gives a continuous function whose Fourier series diverges.
* `ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto`: under pointwise convergence of a
  uniformly bounded sequence, $\|L\| \le \liminf \|L_n\|$.
* `isBounded_of_forall_dual_image_isBounded`, `isBounded_iff_forall_dual_image_isBounded`: a set is
  bounded if and only if every bounded linear functional is bounded on it.
* `StrongDual.isBounded_of_forall_eval_isBounded`: a set of functionals on a Banach space that is
  bounded at every point is bounded in norm.
-/

open Filter Topology Bornology Metric

namespace ContinuousLinearMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The ε/3 argument.** Let $V$ and $W$ be normed spaces over a nontrivially normed field, let
$s \subseteq V$ be dense, let $L : V \to W$ be a bounded linear operator, and let
$(L_n)_{n \in \iota}$ be bounded linear operators with $\|L_n\| \le C$ for all $n$. Let $l$ be a
filter on $\iota$. If $L_n v \to L v$ along $l$ for every $v \in s$, then $L_n v \to L v$ along
$l$ for every $v \in V$.

Neither completeness of $V$ nor linearity of $s$ is used, and the index type and the filter are
arbitrary. Only the boundedness of the limit $L$ matters, which is why $L$ is a
`ContinuousLinearMap` and not a bare function. -/
theorem tendsto_of_tendsto_on_dense_of_bounded {ι : Type*} {l : Filter ι} {s : Set V}
    (hs : Dense s) {L : V →L[𝕜] W} {Ln : ι → V →L[𝕜] W} {C : ℝ} (hC : ∀ n, ‖Ln n‖ ≤ C)
    (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) l (𝓝 (L v))) (v : V) :
    Tendsto (fun n => Ln n v) l (𝓝 (L v)) := by
  -- a bound on operator norms may be negative only over an empty index type; replace it
  set M : ℝ := max C 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCM : ∀ n, ‖Ln n‖ ≤ M := fun n => (hC n).trans (le_max_left _ _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM : 0 < M + ‖L‖ + 1 := by positivity
  obtain ⟨u, hu, hdist⟩ := hs.exists_dist_lt v (ε := ε / (3 * (M + ‖L‖ + 1))) (by positivity)
  have hvu : ‖v - u‖ < ε / (3 * (M + ‖L‖ + 1)) := by rwa [← dist_eq_norm]
  have hsum : (M + ‖L‖) * ‖v - u‖ < ε / 3 := by
    have hle : (M + ‖L‖) * ‖v - u‖ ≤ (M + ‖L‖ + 1) * ‖v - u‖ := by
      nlinarith [norm_nonneg (v - u)]
    have hval : (M + ‖L‖ + 1) * (ε / (3 * (M + ‖L‖ + 1))) = ε / 3 := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hvu hM]
  filter_upwards [Metric.tendsto_nhds.mp (h u hu) (ε / 3) (by positivity)] with n hn
  have h1 : ‖Ln n v - Ln n u‖ ≤ M * ‖v - u‖ := by
    rw [← map_sub]
    exact ((Ln n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hCM n) (norm_nonneg _))
  have h2 : ‖L u - L v‖ ≤ ‖L‖ * ‖v - u‖ := by
    rw [← map_sub, ← norm_neg, ← map_neg, neg_sub]
    exact L.le_opNorm _
  have h3 : ‖Ln n u - L u‖ < ε / 3 := by rw [← dist_eq_norm]; exact hn
  have hsplit : ‖Ln n v - L v‖ ≤ ‖Ln n v - Ln n u‖ + ‖Ln n u - L u‖ + ‖L u - L v‖ := by
    have hrw : Ln n v - L v = Ln n v - Ln n u + (Ln n u - L u) + (L u - L v) := by abel
    rw [hrw]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  rw [dist_eq_norm]
  nlinarith

/-- A convergent sequence in a normed additive group has bounded norms: if $f_n \to a$, then there
is $C$ with $\|f_n\| \le C$ for all $n$. -/
theorem _root_.Filter.Tendsto.exists_norm_le {X : Type*} [NormedAddCommGroup X] {f : ℕ → X} {a : X}
    (h : Tendsto f atTop (𝓝 a)) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h)
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- **The Banach–Steinhaus theorem, convergence form.** Let $V$ be a Banach space and $W$ a normed
space over a nontrivially normed field, let $s \subseteq V$ be dense, and let
$L, L_0, L_1, \dots : V \to W$ be bounded linear operators. Then $L_n v \to L v$ for every
$v \in V$ if and only if $L_n v \to L v$ for every $v \in s$ and there is $C$ with
$\|L_n\| \le C$ for all $n$.

The forward direction is the uniform boundedness principle `banach_steinhaus`, and it is where
the completeness of $V$ is used. The backward direction is the ε/3 argument
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`. -/
theorem tendsto_iff_tendsto_on_dense_of_completeSpace [CompleteSpace V] {s : Set V} (hs : Dense s)
    (L : V →L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) :
    (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔
      (∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C := by
  refine ⟨fun h => ⟨fun v _ => h v, banach_steinhaus fun v => (h v).exists_norm_le⟩, ?_⟩
  rintro ⟨hdense, C, hC⟩
  exact tendsto_of_tendsto_on_dense_of_bounded hs hC hdense

/-- **The contrapositive of the uniform boundedness principle.** Let $V$ be a Banach space and $W$ a
normed space over a nontrivially normed field, and let $L_0, L_1, \dots : V \to W$ be bounded
linear operators whose norms $\|L_n\|$ are unbounded. Then for every bounded linear operator
$L : V \to W$ there is $v \in V$ such that $L_n v$ does not converge to $Lv$.

Apply this to a sequence of projections whose norms grow, such as the Fourier projections on the
continuous periodic functions, whose norms are the Lebesgue constants, with $L$ the identity.
The result is a function to which its own approximations do not converge. -/
theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] {Ln : ℕ → V →L[𝕜] W}
    (h : ¬ BddAbove (Set.range fun n => ‖Ln n‖)) (L : V →L[𝕜] W) :
    ∃ v : V, ¬ Tendsto (fun n => Ln n v) atTop (𝓝 (L v)) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨C, hC⟩ := banach_steinhaus fun v => (hcon v).exists_norm_le
  exact h ⟨C, by rintro x ⟨n, rfl⟩; exact hC n⟩

/-- **The operator norm is lower semicontinuous under pointwise convergence.** Let $V$ and $W$ be
normed spaces over a nontrivially normed field, and let $L, L_0, L_1, \dots : V \to W$ be
bounded linear operators. If $L_n v \to Lv$ for every $v \in V$ and the norms $\|L_n\|$ are
bounded, then $$\|L\| \le \liminf_{n \to \infty} \|L_n\|.$$ This is Corollary 2.3(c) of
[brezis2011functional].

For each $v \neq 0$, $\|Lv\| / \|v\|$ is the limit of $\|L_n v\| / \|v\| \le \|L_n\|$, and the
bound on the norms makes the comparison of the limits inferior valid. On a Banach space the
bound on the norms follows from the pointwise convergence by `banach_steinhaus`. -/
theorem opNorm_le_liminf_opNorm_of_tendsto {L : V →L[𝕜] W} {Ln : ℕ → V →L[𝕜] W}
    (h : ∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v)))
    (hb : BddAbove (Set.range fun n => ‖Ln n‖)) :
    ‖L‖ ≤ liminf (fun n => ‖Ln n‖) atTop := by
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ n, ‖Ln n‖ ≤ C := fun n => hC ⟨n, rfl⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖Ln n‖ :=
    isCoboundedUnder_ge_of_le atTop hC'
  have hM : 0 ≤ liminf (fun n => ‖Ln n‖) atTop :=
    le_liminf_of_le hcobdd (Eventually.of_forall fun n => norm_nonneg _)
  refine opNorm_le_bound' L hM fun v hv => ?_
  have hv' : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  rw [← div_le_iff₀ hv']
  have hlim : Tendsto (fun n => ‖Ln n v‖ / ‖v‖) atTop (𝓝 (‖L v‖ / ‖v‖)) :=
    (h v).norm.div_const _
  calc ‖L v‖ / ‖v‖ = liminf (fun n => ‖Ln n v‖ / ‖v‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖Ln n‖) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          (isBoundedUnder_of ⟨0, fun n => by positivity⟩) hcobdd
        rw [div_le_iff₀ hv']
        exact (Ln n).le_opNorm v

end ContinuousLinearMap

section Corollaries

open NormedSpace

variable {𝕜 G : Type*}

/-- **Weakly bounded implies bounded.** Let $G$ be a normed space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $B \subseteq G$. If $f(B)$ is bounded for every bounded linear functional
$f \in G^*$, then $B$ is bounded. This is Corollary 2.4 of [brezis2011functional].

Completeness of $G$ is not needed. The uniform boundedness principle in the dual $G^*$, which is
always complete, applies to the evaluations $f \mapsto f(b)$ for $b \in B$ and bounds their
norms uniformly. Evaluation at $b$ has norm $\|b\|$, because the canonical embedding of $G$ in
its bidual is an isometry. -/
theorem isBounded_of_forall_dual_image_isBounded [RCLike 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {B : Set G} (h : ∀ f : StrongDual 𝕜 G, IsBounded (f '' B)) :
    IsBounded B := by
  have hpt : ∀ f : StrongDual 𝕜 G, ∃ C, ∀ b : B, ‖inclusionInDoubleDual 𝕜 G b f‖ ≤ C := fun f => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (h f)
    exact ⟨C, fun b => hC _ ⟨b, b.2, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun b : B => inclusionInDoubleDual 𝕜 G b) hpt
  refine isBounded_iff_forall_norm_le.2 ⟨C, fun b hb => ?_⟩
  have := hC ⟨b, hb⟩
  rwa [show inclusionInDoubleDual 𝕜 G b = inclusionInDoubleDualLi 𝕜 b from rfl,
    (inclusionInDoubleDualLi 𝕜).norm_map] at this

/-- Let $G$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A set $B \subseteq G$
is bounded if and only if $f(B)$ is bounded for every bounded linear functional $f \in G^*$.
This is Corollary 2.4 of [brezis2011functional], as an equivalence. -/
theorem isBounded_iff_forall_dual_image_isBounded [RCLike 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {B : Set G} :
    IsBounded B ↔ ∀ f : StrongDual 𝕜 G, IsBounded (f '' B) :=
  ⟨fun hB f => f.lipschitzWith.isBounded_image hB, isBounded_of_forall_dual_image_isBounded⟩

/-- **Weak-∗ bounded implies bounded.** Let $G$ be a Banach space over a nontrivially normed field,
and let $B \subseteq G^*$ be a set of bounded linear functionals. If $\{f(x) : f \in B\}$ is
bounded for every $x \in G$, then $B$ is bounded in norm. This is Corollary 2.5 of
[brezis2011functional].

This is the uniform boundedness principle for the family of functionals indexed by $B$. -/
theorem StrongDual.isBounded_of_forall_eval_isBounded [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G] {B : Set (StrongDual 𝕜 G)}
    (h : ∀ x : G, IsBounded ((fun f : StrongDual 𝕜 G => f x) '' B)) : IsBounded B := by
  have hpt : ∀ x : G, ∃ C, ∀ f : B, ‖(f : StrongDual 𝕜 G) x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (h x)
    exact ⟨C, fun f => hC _ ⟨f, f.2, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun f : B => (f : StrongDual 𝕜 G)) hpt
  exact isBounded_iff_forall_norm_le.2 ⟨C, fun f hf => hC ⟨f, hf⟩⟩

end Corollaries
