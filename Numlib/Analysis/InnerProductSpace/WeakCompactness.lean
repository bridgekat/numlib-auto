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

Two facts about weak sequential convergence that the convergence analysis of numerical methods for
variational problems rests on, and that Mathlib states in neither form. These are
[Atkinson–Han][han2009theoretical] Theorem 2.7.5 in the Hilbert case, and the consequence of
Theorem 3.3.11 (Mazur) that makes the second hypothesis of their Theorem 11.4.1 automatic for
internal approximations.

## Main statements

* `exists_subseq_weak_tendsto` — every norm-bounded sequence in a Hilbert space has a weakly
  convergent subsequence;
* `mem_of_weak_tendsto_of_convex` — a closed convex subset of a real normed space is sequentially
  weakly closed (Mazur's lemma).

## Implementation notes

The first is the sequential Banach–Alaoglu theorem, which Mathlib has
(`WeakDual.isSeqCompact_closedBall`) only for the dual of a **separable** normed space. The
separability hypothesis is removed here by working inside the closed span of the range of the
sequence — a separable, complete subspace — transporting to its dual by the Riesz isometry
`InnerProductSpace.toDual`, and pushing the resulting weak limit back to the whole space with the
orthogonal projection onto that span: a vector outside the span contributes nothing to any of the
inner products involved.

Weak convergence is written in the sequential forms `∀ v, ⟪uₙ, v⟫ → ⟪w, v⟫` and
`∀ ℓ, ℓ (uₙ) → ℓ w` rather than through a weak topology, because those are the forms in which the
numerical-analysis literature states the hypotheses.

The general Banach-space statements — reflexivity, Eberlein–Šmulian, weak sequential compactness of
bounded sets in a reflexive space — are deliberately out of scope: Mathlib has no reflexivity class
for Banach spaces, and everything the applications need happens in a Hilbert space.
-/

open Filter Topology Metric
open scoped InnerProductSpace

section Hilbert

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- **Weak sequential compactness of bounded sets in a Hilbert space.** Every norm-bounded sequence
`u` in a complete inner product space has a subsequence converging weakly: there are a strictly
monotone `σ` and a vector `w` with `⟪u (σ k), v⟫ → ⟪w, v⟫` for every `v`.

Mathlib's sequential Banach–Alaoglu theorem needs a separable space; the closed span of the range
of `u` is separable and complete, and the orthogonal projection onto it carries the weak limit
found there back to the whole space. -/
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

/-- **A closed convex set is sequentially weakly closed** (Mazur). If every `uₙ` lies in a closed
convex set `K` and `uₙ ⇀ w` weakly, then `w ∈ K`.

Hahn–Banach separation of `w` from `K` produces a functional that contradicts the convergence.
Stated over `ℝ`, which is where the variational applications use it; it is what makes the
"weak limits stay in the constraint set" hypothesis automatic for internal approximations, whose
discrete constraint sets are contained in the continuous one. -/
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
