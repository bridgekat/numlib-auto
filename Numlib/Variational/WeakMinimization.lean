/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Variational.Minimization

/-!
# Existence of minimizers by weak sequential compactness

This file proves the direct method of the calculus of variations in a real normed space $V$ in which
every bounded sequence has a weakly convergent subsequence. A functional that is lower
semicontinuous along weakly convergent sequences attains its infimum on a nonempty set that is
closed under weak sequential limits, if the set is bounded or the functional is coercive on it. In
infinite dimensions a norm-closed bounded set is almost never norm-compact, so the
finite-dimensional argument of `Numlib.Variational.Minimization` does not carry over; the extraction
of a weakly convergent subsequence from a bounded sequence replaces compactness. Mazur's lemma makes
convexity a substitute for the weak hypotheses: a closed convex set is weakly sequentially closed,
and a lower semicontinuous convex functional is weakly sequentially lower semicontinuous. The
presentation follows [han2009theoretical], §3.3, Theorems 3.3.8, 3.3.10, 3.3.11, 3.3.12 and 3.3.14.

A sequence $(u_n)$ in $V$ converges weakly to $w$, written $u_n \rightharpoonup w$, if
$\ell(u_n) \to \ell(w)$ for every bounded linear functional $\ell$ on $V$.

## Main definitions

* `WeakSeqTendsto`: weak sequential convergence $u_n \rightharpoonup w$.
* `WeaklySeqCompactSpace`: every norm-bounded sequence in $V$ has a weakly convergent subsequence.
* `IsWeakSeqClosed`: a set contains the weak limit of every weakly convergent sequence of its
  points.
* `WeakSeqLowerSemicontinuousOn`: a functional is lower semicontinuous along the weakly convergent
  sequences of a set, in the form of Mathlib's `LowerSemicontinuousWithinAt`.

## Main results

* `WeaklySeqCompactSpace.of_isReflexive`: every reflexive real normed space is weakly sequentially
  compact, so every theorem of this file applies to it; `WeaklySeqCompactSpace.isReflexive` is the
  converse (Eberlein–Šmulian).
* `exists_seq_convexCombination_tendsto`: **Mazur's lemma**; from a weakly convergent sequence one
  can form convex combinations of its tails that converge in norm.
* `Convex.isWeakSeqClosed`, `ConvexOn.weakSeqLowerSemicontinuousOn`: a closed convex set is weakly
  sequentially closed, and a lower semicontinuous convex functional is weakly sequentially lower
  semicontinuous.
* `exists_isMinOn_of_isWeakSeqClosed`: the direct method on a bounded set.
* `exists_isMinOn_of_isCoerciveFunctionalOn`: the direct method on an unbounded set for a coercive
  functional.
* `exists_isMinOn_of_convexOn`: the convex form, whose hypotheses are on the norm topology alone.
* `exists_isBestApprox_of_convex`: every point has a best approximation from a nonempty closed
  convex set.

## Implementation notes

* The classical hypothesis on the space is that it is a reflexive Banach space. The proofs use only
  the sequential consequence of reflexivity, that every norm-bounded sequence has a weakly
  convergent subsequence. For a Banach space the two are equivalent by the theorems of
  Eberlein–Šmulian and Kakutani, and Theorem 2.7.5 of [han2009theoretical] states reflexivity in
  this form before it is used. The hypothesis of the theorems is therefore the class
  `WeaklySeqCompactSpace`, and the theorems are the classical ones with reflexivity replaced by this
  characterization.
* The class is reflexivity itself. Reflexivity is `NormedSpace.IsReflexive` of
  `Numlib.Analysis.Normed.Module.Reflexive`. The instance `WeaklySeqCompactSpace.of_isReflexive`
  derives the class from it; this is the easy half of the equivalence,
  `NormedSpace.exists_subseq_forall_dual_tendsto` read through `WeakSeqTendsto`. The converse
  `WeaklySeqCompactSpace.isReflexive` is the Eberlein–Šmulian theorem of
  `Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian`.
* The direct method therefore applies to every reflexive real Banach space: to every Hilbert space
  by `NormedSpace.instIsReflexiveOfInnerProductSpace`, to $L^p$ for $1 < p < \infty$ by
  `MeasureTheory.Lp.instIsReflexive`, and to every uniformly convex Banach space by
  `NormedSpace.isReflexive_of_uniformConvexSpace` (Milman–Pettis).
* Weak sequential convergence is stated pointwise on the dual, not as convergence in Mathlib's
  `WeakSpace`; `weakSeqTendsto_iff_tendsto_toWeakSpace` shows that the two agree.
-/

open Bornology Filter Topology

section Defs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Weak sequential convergence**. A sequence $(u_n)$ in a real normed space $V$ converges weakly
to $w \in V$, written $u_n \rightharpoonup w$, if $\ell(u_n) \to \ell(w)$ for every bounded
linear functional $\ell$ on $V$.

Mathlib has the weak topology as `WeakSpace ℝ V`, and `weakSeqTendsto_iff_tendsto_toWeakSpace`
shows that the two notions of convergence agree. The hypotheses of the direct method are stated
and verified in the pointwise form. -/
def WeakSeqTendsto (u : ℕ → V) (w : V) : Prop :=
  ∀ ℓ : StrongDual ℝ V, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ w))

/-- A sequence converges weakly, $u_n \rightharpoonup w$, if and only if it converges to $w$ in the
weak topology of $V$, which is Mathlib's `WeakSpace ℝ V`. -/
theorem weakSeqTendsto_iff_tendsto_toWeakSpace {u : ℕ → V} {w : V} :
    WeakSeqTendsto u w ↔
      Tendsto (fun n => toWeakSpace ℝ V (u n)) atTop (𝓝 (toWeakSpace ℝ V w)) :=
  tendsto_toWeakSpace_iff.symm

/-- If $u_n \rightharpoonup w$ and $\sigma : \mathbb{N} \to \mathbb{N}$ is strictly increasing, then
$u_{\sigma(n)} \rightharpoonup w$. -/
theorem WeakSeqTendsto.comp {u : ℕ → V} {w : V} (h : WeakSeqTendsto u w) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) : WeakSeqTendsto (u ∘ σ) w :=
  fun ℓ => (h ℓ).comp hσ.tendsto_atTop

/-- If $u_n \to w$ in norm, then $u_n \rightharpoonup w$. -/
theorem WeakSeqTendsto.of_tendsto {u : ℕ → V} {w : V} (h : Tendsto u atTop (𝓝 w)) :
    WeakSeqTendsto u w :=
  fun ℓ => (ℓ.continuous.tendsto w).comp h

/-- Let $H$ be a real Hilbert space. Then $u_n \rightharpoonup w$ if and only if
$\langle u_n, y\rangle \to \langle w, y\rangle$ for every $y \in H$. The proof uses the Riesz
representation theorem `InnerProductSpace.toDual`: every bounded linear functional on $H$ is
$\langle \cdot, y\rangle$ for some $y \in H$. -/
theorem weakSeqTendsto_iff_forall_tendsto_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {u : ℕ → H} {w : H} :
    WeakSeqTendsto u w ↔
      ∀ y : H, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ w y)) := by
  refine ⟨fun h y => ?_, fun h ℓ => ?_⟩
  · simpa only [innerSL_apply_apply, real_inner_comm y] using h (innerSL ℝ y)
  · have := h ((InnerProductSpace.toDual ℝ H).symm ℓ)
    simp only [real_inner_comm ((InnerProductSpace.toDual ℝ H).symm ℓ),
      InnerProductSpace.toDual_symm_apply] at this
    exact this

/-- A real normed space $V$ is **weakly sequentially compact** if every norm-bounded sequence in $V$
has a weakly convergent subsequence: for every sequence $(u_n)$ with $\|u_n\| \le C$ for all
$n$, there are a strictly increasing $\sigma : \mathbb{N} \to \mathbb{N}$ and $w \in V$ with
$u_{\sigma(n)} \rightharpoonup w$. For a Banach space this property is equivalent to reflexivity
by the theorems of Eberlein–Šmulian and Kakutani, and Theorem 2.7.5 of [han2009theoretical]
states reflexivity in this form.

The class is the hypothesis of the theorems of `Numlib.Variational.WeakMinimization` instead of
reflexivity, because it is what their proofs use. Every reflexive space is an instance by
`WeaklySeqCompactSpace.of_isReflexive`, and every instance is reflexive by
`WeaklySeqCompactSpace.isReflexive`. -/
class WeaklySeqCompactSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop where
  /-- Every norm-bounded sequence has a weakly convergent subsequence. -/
  exists_subseq_weakSeqTendsto : ∀ (u : ℕ → V) (C : ℝ), (∀ n, ‖u n‖ ≤ C) →
    ∃ (σ : ℕ → ℕ) (w : V), StrictMono σ ∧ WeakSeqTendsto (u ∘ σ) w

/-- A set $K$ in a real normed space is **weakly sequentially closed** if it contains the weak limit
of every weakly convergent sequence of its points: if $u_n \in K$ for all $n$ and
$u_n \rightharpoonup w$, then $w \in K$.

It is the hypothesis on the constraint set in Theorem 3.3.8 of [han2009theoretical].
`Convex.isWeakSeqClosed` gives the main examples. -/
def IsWeakSeqClosed (K : Set V) : Prop :=
  ∀ (u : ℕ → V) (w : V), (∀ n, u n ∈ K) → WeakSeqTendsto u w → w ∈ K

/-- A functional $f : V \to \mathbb{R}$ is **weakly sequentially lower semicontinuous on** a set $K$
if, for every sequence $(u_n)$ in $K$ that converges weakly to a point $w \in K$ and every
$y < f(w)$, eventually $y < f(u_n)$. This is the form of Mathlib's
`LowerSemicontinuousWithinAt`; in the extended reals it says $f(w) \le \liminf_n f(u_n)$.

The definition avoids $\liminf$ because a real-valued $\liminf$ has a junk value when the
sequence $f(u_n)$ is unbounded below, and this is exactly the case that the existence proof must
rule out. -/
def WeakSeqLowerSemicontinuousOn (f : V → ℝ) (K : Set V) : Prop :=
  ∀ (u : ℕ → V) (w : V), (∀ n, u n ∈ K) → w ∈ K → WeakSeqTendsto u w →
    ∀ y < f w, ∀ᶠ n in atTop, y < f (u n)

/-- If $f$ is weakly sequentially lower semicontinuous on $K$ and $K' \subseteq K$, then $f$ is
weakly sequentially lower semicontinuous on $K'$. -/
theorem WeakSeqLowerSemicontinuousOn.mono {f : V → ℝ} {K K' : Set V}
    (h : WeakSeqLowerSemicontinuousOn f K) (hKK : K' ⊆ K) :
    WeakSeqLowerSemicontinuousOn f K' :=
  fun u w hu hw => h u w (fun n => hKK (hu n)) (hKK hw)

end Defs

/-! ### Reflexive spaces are weakly sequentially compact -/

/-- **Every reflexive real normed space is weakly sequentially compact**: if $V$ is reflexive, then
every norm-bounded sequence in $V$ has a weakly convergent subsequence. This is the easy half of
the classical equivalence; the converse is `WeaklySeqCompactSpace.isReflexive`.

The proof is `NormedSpace.exists_subseq_forall_dual_tendsto`, whose conclusion is
`WeakSeqTendsto` with the quantifier over the dual moved outside. Through
`NormedSpace.instIsReflexiveOfInnerProductSpace` the instance covers every Hilbert space, so it
subsumes the direct route through the Riesz representation and `exists_subseq_weak_tendsto`. It
is the only instance of the class, so it has the default priority. It is stated over
$\mathbb{R}$ because `WeakSeqTendsto` is, since the direct method concerns real-valued
functionals. -/
instance WeaklySeqCompactSpace.of_isReflexive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace.IsReflexive ℝ V] : WeaklySeqCompactSpace V where
  exists_subseq_weakSeqTendsto u C hC := by
    obtain ⟨w, σ, hσ, h⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hC
    exact ⟨σ, w, hσ, h⟩

/-- **A weakly sequentially compact real normed space is reflexive**: if every norm-bounded sequence
in $V$ has a weakly convergent subsequence, then $V$ is reflexive. This is the converse of
`WeaklySeqCompactSpace.of_isReflexive`.

The proof is the Eberlein–Šmulian theorem
`NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto`. Completeness of $V$ is
not assumed, because it is a consequence. -/
theorem WeaklySeqCompactSpace.isReflexive (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [WeaklySeqCompactSpace V] : NormedSpace.IsReflexive ℝ V :=
  NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto fun v C h ↦
    let ⟨σ, w, hσ, hw⟩ := WeaklySeqCompactSpace.exists_subseq_weakSeqTendsto v C h
    ⟨w, σ, hσ, hw⟩

/-! ### Mazur's lemma -/

section Mazur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Mazur's lemma** for one tail. Let $E$ be a real normed space and let $v_n \rightharpoonup u$
in $E$. For every $n$ and every $\varepsilon > 0$ there are $N \ge n$ and weights
$\lambda_i \ge 0$ with $\sum_{i=n}^N \lambda_i = 1$ and
$$\Bigl\| \sum_{i=n}^N \lambda_i v_i - u \Bigr\| < \varepsilon.$$

The tail $(v_i)_{i \ge n}$ still converges weakly to $u$, so $u$ lies in the closed convex hull
of the tail by `mem_of_weak_tendsto_of_convex`, and a point of a convex hull is a finite convex
combination of points of the set. -/
theorem exists_convexCombination_norm_sub_lt {v : ℕ → E} {u : E} (h : WeakSeqTendsto v u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (lam : ℕ → ℝ), n ≤ N ∧ (∀ i, 0 ≤ lam i) ∧
      ∑ i ∈ Finset.Icc n N, lam i = 1 ∧ ‖(∑ i ∈ Finset.Icc n N, lam i • v i) - u‖ < ε := by
  classical
  -- `u` lies in the closed convex hull of the tail `{vᵢ : i ≥ n}`.
  set S : Set E := convexHull ℝ (v '' Set.Ici n) with hS
  have hmemS : ∀ k : ℕ, v (k + n) ∈ S :=
    fun k => subset_convexHull ℝ _ ⟨k + n, Set.mem_Ici.2 (Nat.le_add_left n k), rfl⟩
  have hucl : u ∈ closure S :=
    mem_of_weak_tendsto_of_convex (convex_convexHull ℝ _).closure isClosed_closure
      (fun k => subset_closure (hmemS k))
      (fun ℓ => (h ℓ).comp (tendsto_add_atTop_nat n))
  obtain ⟨b, hbS, hbu⟩ := Metric.mem_closure_iff.1 hucl ε hε
  -- A point of the convex hull is a finite convex combination of points of the tail.
  rw [hS, convexHull_eq] at hbS
  obtain ⟨ι, t, wt, z, hwt0, hwt1, hz, hcm⟩ := hbS
  choose! j hjn hjv using hz
  set T : Finset ℕ := t.image j with hT
  have hmaps : ∀ i ∈ t, j i ∈ T := fun i hi => Finset.mem_image_of_mem j hi
  set lam : ℕ → ℝ := fun k => ∑ i ∈ t with j i = k, wt i with hlam
  have hlam0 : ∀ k, 0 ≤ lam k :=
    fun k => Finset.sum_nonneg fun i hi => hwt0 i (Finset.mem_filter.1 hi).1
  have hsum1 : ∑ k ∈ T, lam k = 1 := by
    rw [hlam, Finset.sum_fiberwise_of_maps_to hmaps, hwt1]
  have hcomb : ∑ k ∈ T, lam k • v k = b := by
    have hstep : ∀ k ∈ T, lam k • v k = ∑ i ∈ t with j i = k, wt i • z i := by
      intro k _
      rw [hlam, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨hit, hik⟩ := Finset.mem_filter.1 hi
      rw [← hik, hjv i hit]
    rw [Finset.sum_congr rfl hstep, Finset.sum_fiberwise_of_maps_to hmaps,
      ← Finset.centerMass_eq_of_sum_1 _ _ hwt1, hcm]
  -- Pad the combination out to the interval `Icc n N`.
  have hsub : T ⊆ Finset.Icc n (max n (T.sup id)) := by
    intro k hk
    obtain ⟨i, hit, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_Icc.2
      ⟨Set.mem_Ici.1 (hjn i hit), le_max_of_le_right (Finset.le_sup (f := id) hk)⟩
  refine ⟨max n (T.sup id), fun k => if k ∈ T then lam k else 0, le_max_left _ _,
    fun k => by dsimp only; split_ifs with hk; exacts [hlam0 k, le_rfl], ?_, ?_⟩
  · rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, hsum1]
  · have hpad : ∑ k ∈ Finset.Icc n (max n (T.sup id)), (if k ∈ T then lam k else 0) • v k
        = ∑ k ∈ T, lam k • v k := by
      rw [← Finset.sum_subset hsub (fun k _ hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [hpad, hcomb, ← norm_neg, neg_sub]
    simpa [dist_eq_norm] using hbu

/-- **Mazur's lemma**. Let $E$ be a real normed space and let $v_n \rightharpoonup u$ in $E$. Then
there are indices $N(n) \ge n$ and weights $\lambda^{(n)}_i \ge 0$ with
$\sum_{i=n}^{N(n)} \lambda^{(n)}_i = 1$ such that the convex combinations
$$u_n = \sum_{i=n}^{N(n)} \lambda^{(n)}_i v_i$$
of the tails of the sequence converge to $u$ in norm. This is Theorem 3.3.11 of
[han2009theoretical]. -/
theorem exists_seq_convexCombination_tendsto {v : ℕ → E} {u : E} (h : WeakSeqTendsto v u) :
    ∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • v i) atTop (𝓝 u) := by
  choose N lam hN hlam0 hlam1 hlt using fun n : ℕ =>
    exists_convexCombination_norm_sub_lt h n (Nat.one_div_pos_of_nat (n := n))
  refine ⟨N, lam, hN, hlam0, hlam1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hlt n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **A closed convex set is weakly sequentially closed**: if $K$ is a convex and norm-closed subset
of a real normed space, then $K$ contains the weak limit of every weakly convergent sequence of
points of $K$. This is the first corollary of Mazur's lemma after Theorem 3.3.11 of
[han2009theoretical]. -/
theorem Convex.isWeakSeqClosed {K : Set E} (hconv : Convex ℝ K) (hcl : IsClosed K) :
    IsWeakSeqClosed K :=
  fun _ _ hu hw => mem_of_weak_tendsto_of_convex hconv hcl hu hw

/-- **A lower semicontinuous convex functional is weakly sequentially lower semicontinuous**: if $K$
is a convex subset of a real normed space and $f$ is convex and lower semicontinuous on $K$,
then $f$ is weakly sequentially lower semicontinuous on $K$. This is the second corollary of
Mazur's lemma after Theorem 3.3.11 of [han2009theoretical].

The sublevel set $S = \{x \in K : f(x) \le y\}$ is convex, so its closure is a closed convex set
and contains the weak limit $w$. Lower semicontinuity of $f$ along $K$ at $w$ then excludes
$f(w) > y$, because every neighbourhood of $w$ meets $S$, where $f \le y$. The proof takes the
closure of the sublevel set, not of $K$, so $K$ need not be closed. -/
theorem ConvexOn.weakSeqLowerSemicontinuousOn {f : E → ℝ} {K : Set E}
    (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K) :
    WeakSeqLowerSemicontinuousOn f K := by
  intro u w hu hw hlim y hy
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨σ, hσ, hσy⟩ := extraction_of_frequently_atTop hcon
  set S : Set E := {x ∈ K | f x ≤ y} with hS
  have hmem : w ∈ closure S :=
    mem_of_weak_tendsto_of_convex (hf.convex_le y).closure isClosed_closure
      (fun k => subset_closure ⟨hu (σ k), not_lt.1 (hσy k)⟩) (hlim.comp hσ)
  have : (𝓝[S] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  have hev : ∀ᶠ x in 𝓝[S] w, y < f x :=
    (hlsc w hw y hy).filter_mono (nhdsWithin_mono w fun x (hx : x ∈ S) => hx.1)
  obtain ⟨x, hx1, hx2⟩ := (hev.and eventually_mem_nhdsWithin).exists
  exact absurd hx2.2 (not_le.2 hx1)

end Mazur

/-! ### The direct method -/

section DirectMethod

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [WeaklySeqCompactSpace V]

/-- The compactness step of the direct method. Let $V$ be a weakly sequentially compact real normed
space, and let $K \subseteq V$ be bounded and weakly sequentially closed. Then every sequence
$(u_n)$ in $K$ has a subsequence $(u_{\sigma(n)})$ that converges weakly to a point $w \in K$. -/
theorem IsWeakSeqClosed.exists_subseq_weakSeqTendsto {K : Set V} (hbd : IsBounded K)
    (hKc : IsWeakSeqClosed K) {u : ℕ → V} (hu : ∀ n, u n ∈ K) :
    ∃ (σ : ℕ → ℕ) (w : V), StrictMono σ ∧ w ∈ K ∧ WeakSeqTendsto (u ∘ σ) w := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨σ, w, hσ, hlim⟩ :=
    WeaklySeqCompactSpace.exists_subseq_weakSeqTendsto u C fun n => hC _ (hu n)
  exact ⟨σ, w, hσ, hKc _ w (fun k => hu (σ k)) hlim, hlim⟩

/-- **Existence of a minimizer on a bounded set**. Let $V$ be a weakly sequentially compact real
normed space, let $K \subseteq V$ be nonempty, bounded and weakly sequentially closed, and let
$f : V \to \mathbb{R}$ be weakly sequentially lower semicontinuous on $K$. Then $f$ attains its
minimum on $K$: there is $u \in K$ with $f(u) \le f(v)$ for all $v \in K$. This is Theorem 3.3.8
of [han2009theoretical].

A minimizing sequence has a weakly convergent subsequence. Its limit lies in $K$, and lower
semicontinuity forces the value there to be at most the infimum. The finiteness of the infimum
is part of the argument: a sequence on which $f$ tends to $-\infty$ would have a weak limit
point in $K$ at which lower semicontinuity fails. -/
theorem exists_isMinOn_of_isWeakSeqClosed {K : Set V} {f : V → ℝ} (hne : K.Nonempty)
    (hbd : IsBounded K) (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K) :
    ∃ u ∈ K, IsMinOn f K u := by
  classical
  -- `f` is bounded below on `K`
  have hbdd : BddBelow (f '' K) := by
    by_contra hcon
    rw [not_bddBelow_iff] at hcon
    have hcon' : ∀ m : ℝ, ∃ x ∈ K, f x < m := by
      intro m
      obtain ⟨y, hy, hym⟩ := hcon m
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, hym⟩
    choose d hdK hdf using hcon'
    set c : ℕ → V := fun n => d (-(n : ℝ)) with hc
    have hcK : ∀ n, c n ∈ K := fun n => hdK _
    have hcf : ∀ n : ℕ, f (c n) < -(n : ℝ) := fun n => hdf _
    obtain ⟨σ, w, hσ, hwK, hlim⟩ := hKc.exists_subseq_weakSeqTendsto hbd hcK
    have h1 := hf (c ∘ σ) w (fun k => hcK (σ k)) hwK hlim (f w - 1) (by linarith)
    have h2 : ∀ᶠ k in atTop, f ((c ∘ σ) k) < f w - 1 := by
      have hten : Tendsto (fun k : ℕ => -((σ k : ℕ) : ℝ)) atTop atBot := by
        refine tendsto_neg_atTop_atBot.comp ?_
        exact tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop
      filter_upwards [hten.eventually_lt_atBot (f w - 1)] with k hk
      exact lt_trans (hcf (σ k)) hk
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact absurd hk1 (not_lt.2 hk2.le)
  -- a minimizing sequence
  obtain ⟨v₀, hv₀⟩ := hne
  have hAne : (f '' K).Nonempty := ⟨f v₀, v₀, hv₀, rfl⟩
  set m : ℝ := sInf (f '' K) with hm
  have hchoice : ∀ n : ℕ, ∃ x ∈ K, f x < m + 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
    obtain ⟨y, hy, hylt⟩ := (csInf_lt_iff hbdd hAne).1 (show m < m + 1 / (n + 1) by linarith)
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, hylt⟩
  choose c hcK hcf using hchoice
  obtain ⟨σ, w, hσ, hwK, hlim⟩ := hKc.exists_subseq_weakSeqTendsto hbd hcK
  refine ⟨w, hwK, isMinOn_iff.2 fun x hx => le_trans ?_ (csInf_le hbdd ⟨x, hx, rfl⟩)⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨y, hmy, hyw⟩ := exists_between hcon
  have h1 := hf (c ∘ σ) w (fun k => hcK (σ k)) hwK hlim y hyw
  have h2 : ∀ᶠ k in atTop, f ((c ∘ σ) k) < y := by
    have hten : Tendsto (fun k : ℕ => m + 1 / ((σ k : ℕ) + 1 : ℝ)) atTop (𝓝 (m + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop)
    rw [add_zero] at hten
    filter_upwards [hten.eventually_lt_const hmy] with k hk
    exact lt_trans (hcf (σ k)) hk
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  exact absurd hk1 (not_lt.2 hk2.le)

/-- **Existence of a minimizer of a coercive functional**. Let $V$ be a weakly sequentially compact
real normed space, let $K \subseteq V$ be nonempty and weakly sequentially closed, and let
$f : V \to \mathbb{R}$ be weakly sequentially lower semicontinuous on $K$ and coercive on $K$:
for every $M$ there is $R$ with $f(x) \ge M$ for all $x \in K$ with $\|x\| \ge R$. Then $f$
attains its minimum on $K$. This is Theorem 3.3.10 of [han2009theoretical]; the set $K$ need not
be bounded.

Coercivity is `IsCoerciveFunctionalOn`. The sublevel set of $f$ in $K$ below the value at any
point of $K$ is bounded by coercivity and weakly sequentially closed by lower semicontinuity,
and a minimizer on it is a minimizer on $K$. -/
theorem exists_isMinOn_of_isCoerciveFunctionalOn {K : Set V} {f : V → ℝ} (hne : K.Nonempty)
    (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K)
    (hcoer : IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u := by
  obtain ⟨v₀, hv₀⟩ := hne
  set K₀ : Set V := {x ∈ K | f x ≤ f v₀} with hK₀
  have hsub : K₀ ⊆ K := fun _ hx => hx.1
  have hne₀ : K₀.Nonempty := ⟨v₀, hv₀, le_rfl⟩
  -- coercivity confines the search to `K₀`
  obtain ⟨R, hR⟩ := hcoer (f v₀ + 1)
  have hbd : IsBounded K₀ := by
    refine (Metric.isBounded_closedBall (x := (0 : V)) (r := R)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hxR
    exact absurd (hR x hx.1 (not_le.1 hxR).le) (by linarith [hx.2])
  -- and `K₀` is weakly sequentially closed
  have hKc₀ : IsWeakSeqClosed K₀ := by
    intro u w hu hlim
    refine ⟨hKc u w (fun n => (hu n).1) hlim, ?_⟩
    by_contra hcon
    obtain ⟨k, hk⟩ := (hf u w (fun n => (hu n).1) (hKc u w (fun n => (hu n).1) hlim) hlim (f v₀)
      (not_le.1 hcon)).exists
    exact absurd (hu k).2 (not_le.2 hk)
  obtain ⟨u, hu, hmin⟩ :=
    exists_isMinOn_of_isWeakSeqClosed hne₀ hbd hKc₀ (hf.mono hsub)
  refine ⟨u, hsub hu, isMinOn_iff.2 fun x hx => ?_⟩
  by_cases hfx : f x ≤ f v₀
  · exact isMinOn_iff.1 hmin x ⟨hx, hfx⟩
  · exact le_trans (isMinOn_iff.1 hmin v₀ ⟨hv₀, le_rfl⟩) (not_le.1 hfx).le

/-- **Existence of a minimizer of a convex functional**. Let $V$ be a weakly sequentially compact
real normed space, let $K \subseteq V$ be nonempty, closed and convex, and let
$f : V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. If $K$ is bounded or $f$ is
coercive on $K$, then $f$ attains its minimum on $K$. This is Theorem 3.3.12 of
[han2009theoretical].

Every hypothesis is for the norm topology. The two corollaries of Mazur's lemma,
`Convex.isWeakSeqClosed` and `ConvexOn.weakSeqLowerSemicontinuousOn`, turn them into the weak
hypotheses of Theorems 3.3.8 and 3.3.10, which are `exists_isMinOn_of_isWeakSeqClosed` and
`exists_isMinOn_of_isCoerciveFunctionalOn`. Uniqueness under strict convexity is
`IsMinOn.eq_of_strictConvexOn`. -/
theorem exists_isMinOn_of_convexOn {K : Set V} {f : V → ℝ} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  h.elim
    (fun hbd => exists_isMinOn_of_isWeakSeqClosed hne hbd (hconv.isWeakSeqClosed hcl)
      (hf.weakSeqLowerSemicontinuousOn hlsc))
    (fun hcoer => exists_isMinOn_of_isCoerciveFunctionalOn hne (hconv.isWeakSeqClosed hcl)
      (hf.weakSeqLowerSemicontinuousOn hlsc) hcoer)

/-- **Existence of a maximizer of a concave functional**, the mirror of
`exists_isMinOn_of_convexOn`. Let $V$ be a weakly sequentially compact real normed space, let
$K \subseteq V$ be nonempty, closed and convex, and let $f : V \to \mathbb{R}$ be concave and
upper semicontinuous on $K$. If $K$ is bounded or $-f$ is coercive on $K$, then $f$ attains its
maximum on $K$. -/
theorem exists_isMaxOn_of_concaveOn {K : Set V} {f : V → ℝ} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (hf : ConcaveOn ℝ K f) (husc : UpperSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn (-f) K) : ∃ u ∈ K, IsMaxOn f K u := by
  have hlsc : LowerSemicontinuousOn (-f) K :=
    continuous_neg.comp_upperSemicontinuousOn_antitone husc fun _ _ h => neg_le_neg h
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_convexOn hne hcl hconv hf.neg hlsc h
  exact ⟨u, hu, isMaxOn_iff.2 fun x hx => neg_le_neg_iff.1 (isMinOn_iff.1 hmin x hx)⟩

/-- **Existence of a best approximation from a closed convex set**. Let $V$ be a weakly sequentially
compact real normed space, and let $K \subseteq V$ be nonempty, closed and convex. Then every
$u \in V$ has a best approximation from $K$: there is $v \in K$ with $\|u - v\| \le \|u - w\|$
for all $w \in K$. This is Theorem 3.3.14 of [han2009theoretical].

A best approximation is `IsBestApprox`. The distance to $u$ is convex, continuous and coercive,
so this is the coercive case of `exists_isMinOn_of_convexOn`. No completeness or inner product
is needed beyond the weak sequential compactness of bounded sequences. In a Hilbert space this
is the projection theorem. -/
theorem exists_isBestApprox_of_convex {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (u : V) : ∃ v, IsBestApprox K u v := by
  set f : V → ℝ := fun v => ‖u - v‖ with hf
  have hconvf : ConvexOn ℝ K f := by
    refine ⟨hconv, fun x _ y _ a b ha hb hab => ?_⟩
    have hcomb : a • (u - x) + b • (u - y) = u - (a • x + b • y) := by
      rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    rw [hf]
    calc ‖u - (a • x + b • y)‖ = ‖a • (u - x) + b • (u - y)‖ := by rw [hcomb]
      _ ≤ ‖a • (u - x)‖ + ‖b • (u - y)‖ := norm_add_le _ _
      _ = a • ‖u - x‖ + b • ‖u - y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]
  have hcoer : IsCoerciveFunctionalOn f K := by
    intro M
    refine ⟨M + ‖u‖, fun x _ hx => ?_⟩
    have h1 : ‖x‖ - ‖u‖ ≤ ‖x - u‖ := norm_sub_norm_le x u
    have h2 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev x u
    change M ≤ ‖u - x‖
    linarith
  obtain ⟨v, hv, hmin⟩ := exists_isMinOn_of_convexOn hne hcl hconv hconvf
    ((continuous_const.sub continuous_id).norm.lowerSemicontinuous.lowerSemicontinuousOn K)
    (Or.inr hcoer)
  exact ⟨v, hv, fun w hw => isMinOn_iff.1 hmin w hw⟩

end DirectMethod
