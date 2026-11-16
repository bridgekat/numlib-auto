/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Dual` and
`Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Metrizable.Basic

/-!
# Weak sequential compactness in a Hilbert space

The convergence analysis of numerical methods for variational problems rests on two facts about weak
sequential convergence, which Mathlib does not state in these forms. First, every bounded sequence
$(u_n)$ in a Hilbert space $V$ has a weakly convergent subsequence: there are indices
$n_0 < n_1 < \dots$ and $w \in V$ with $\langle u_{n_k}, v \rangle \to \langle w, v \rangle$ for
every $v \in V$. This is Theorem 2.7.5 of [han2009theoretical] for a Hilbert space. Second, a closed
convex subset $K$ of a real normed space is weakly sequentially closed (Mazur's lemma): if
$u_n \in K$ for all $n$ and $\ell(u_n) \to \ell(w)$ for every continuous linear functional $\ell$,
then $w \in K$. This consequence of Theorem 3.3.11 (Mazur) of [han2009theoretical] makes the second
hypothesis of Theorem 11.4.1 of [han2009theoretical] automatic for internal approximations.

## Main results

* `exists_subseq_weak_tendsto`: every bounded sequence in a Hilbert space has a weakly convergent
  subsequence.
* `mem_of_weak_tendsto_of_convex`: a closed convex subset of a real normed space is weakly
  sequentially closed (Mazur's lemma).

## Proof outline

The first result is the sequential Banach–Alaoglu theorem. Mathlib has this theorem
(`WeakDual.isSeqCompact_closedBall`) only for the dual of a separable normed space. The proof
removes the separability hypothesis: it works in the closed span of the terms of the sequence, which
is a separable complete subspace, and passes to the dual of this subspace by the Riesz isometry
`InnerProductSpace.toDual`. The orthogonal projection onto the span then carries the weak limit back
to the whole space, because a vector orthogonal to the span does not change any of the inner
products.

## Implementation notes

* Weak convergence is written in the sequential forms $\langle u_n, v \rangle \to \langle w, v
  \rangle$ for all $v$, and $\ell(u_n) \to \ell(w)$ for all $\ell$, and not with a weak topology.
  The literature of numerical analysis states the hypotheses in these forms.
* The statements for Banach spaces are not in this file, so that it depends on Mathlib only; the
  applications need only Hilbert spaces. Two of the three Banach-space facts are in
  `Numlib.Analysis.Normed.Module.Reflexive`: reflexivity, as the class `NormedSpace.IsReflexive`,
  and the weak sequential compactness of the bounded sets of a reflexive space, as
  `NormedSpace.exists_subseq_forall_dual_tendsto`. The second implies `exists_subseq_weak_tendsto`,
  because a Hilbert space is reflexive. The converse, that a space whose bounded sets are weakly
  sequentially compact is reflexive, is not in the library. It is Theorem 2.7.5 of
  [han2009theoretical] read from right to left. Its proof needs Goldstine's theorem, for which
  Mathlib has no weak-$*$ bipolar theorem, and the sequential-to-topological half of the
  Eberlein–Šmulian theorem, of which Mathlib has nothing.
-/

open Filter Topology Metric
open scoped InnerProductSpace

section Hilbert

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- **Weak sequential compactness of bounded sets in a Hilbert space.** Let $V$ be a complete inner
product space and let $(u_n)$ be a sequence in $V$ with $\|u_n\| \le C$ for all $n$. Then there
are a strictly increasing $\sigma : \mathbb{N} \to \mathbb{N}$ and a vector $w \in V$ with
$$\langle u_{\sigma(k)}, v \rangle \to \langle w, v \rangle \quad (k \to \infty) \qquad
  \text{for every } v \in V.$$

Mathlib's sequential Banach–Alaoglu theorem needs a separable space. The closed span of the
terms of $(u_n)$ is separable and complete, and the orthogonal projection onto it carries the
weak limit found there back to $V$. -/
theorem exists_subseq_weak_tendsto {u : ℕ → V} {C : ℝ} (hC : ∀ n, ‖u n‖ ≤ C) :
    ∃ (σ : ℕ → ℕ) (w : V), StrictMono σ ∧
      ∀ v : V, Tendsto (fun k => ⟪u (σ k), v⟫_𝕜) atTop (𝓝 ⟪w, v⟫_𝕜) := by
  -- The closed span of the range of `u`: a separable, complete subspace containing every `u n`.
  set S : Submodule 𝕜 V := (Submodule.span 𝕜 (Set.range u)).topologicalClosure with hSdef
  have hSclosed : IsClosed (S : Set V) := Submodule.isClosed_topologicalClosure _
  have hScomplete : CompleteSpace S := hSclosed.completeSpace_coe
  have hSsep : TopologicalSpace.SeparableSpace S := by
    have h1 : TopologicalSpace.IsSeparable ((S : Set V)) := by
      rw [hSdef, Submodule.topologicalClosure_coe]
      exact ((Set.countable_range u).isSeparable.span).closure
    exact h1.separableSpace
  have huS : ∀ n, u n ∈ S :=
    fun n => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  -- Transport the sequence into the dual of `S` and apply sequential Banach–Alaoglu.
  set x : ℕ → WeakDual 𝕜 S :=
    fun n => WeakDual.toStrongDual.symm (InnerProductSpace.toDual 𝕜 S ⟨u n, huS n⟩) with hxdef
  have hxmem : ∀ n, x n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 S) C := by
    intro n
    simp only [hxdef, Set.mem_preimage, LinearEquiv.apply_symm_apply, mem_closedBall,
      dist_zero_right]
    simpa using hC n
  obtain ⟨a, -, σ, hσ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall 𝕜 S (0 : StrongDual 𝕜 S) C hxmem
  refine ⟨σ, ((InnerProductSpace.toDual 𝕜 S).symm (WeakDual.toStrongDual a) : V), hσ, fun v => ?_⟩
  -- The projection of `v` onto `S` carries all the information the inner products see.
  set p : V := S.starProjection v
  have hpS : p ∈ S := S.starProjection_apply_mem v
  have hvp : v - p ∈ Sᗮ := S.sub_starProjection_mem_orthogonal v
  have hinner : ∀ z : V, z ∈ S → ⟪z, v⟫_𝕜 = ⟪z, p⟫_𝕜 := by
    intro z hz
    have : ⟪z, v - p⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hz hvp
    rw [inner_sub_right] at this
    linear_combination (norm := module) this
  rw [hinner _ (Submodule.coe_mem _)]
  have hev : Tendsto (fun k => (x (σ k)) ⟨p, hpS⟩) atTop (𝓝 (a ⟨p, hpS⟩)) :=
    ((WeakDual.eval_continuous (⟨p, hpS⟩ : S)).tendsto a).comp hlim
  convert hev using 2 with k
  · rw [hinner _ (huS (σ k))]
    rfl
  · exact InnerProductSpace.toDual_symm_apply (x := (⟨p, hpS⟩ : S))
      (y := WeakDual.toStrongDual a)

end Hilbert

section Mazur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Mazur's lemma: a closed convex set is weakly sequentially closed.** Let $E$ be a real normed
space, let $K \subseteq E$ be closed and convex, and let $(u_n)$ be a sequence in $K$. If
$w \in E$ and $\ell(u_n) \to \ell(w)$ for every continuous linear functional $\ell$ on $E$, then
$w \in K$.

The proof separates $w$ from $K$ by the Hahn–Banach theorem, and the separating functional
contradicts the convergence. The result is stated over $\mathbb{R}$, where the variational
applications use it. It makes the hypothesis that weak limits stay in the constraint set
automatic for internal approximations, whose discrete constraint sets are contained in the
continuous one. -/
theorem mem_of_weak_tendsto_of_convex {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    {u : ℕ → E} {w : E} (hu : ∀ n, u n ∈ K)
    (hw : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ w))) :
    w ∈ K := by
  by_contra hwK
  obtain ⟨f, c, hfK, hcw⟩ := geometric_hahn_banach_closed_point hconv hclosed hwK
  have hle : f w ≤ c :=
    le_of_tendsto (hw f) (Eventually.of_forall fun n => (hfK (u n) (hu n)).le)
  exact absurd hcw (not_lt.2 hle)

end Mazur
