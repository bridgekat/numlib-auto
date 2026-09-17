import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.WeakStarMetrizable
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis §3.6: separable spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.6, over a real Banach space `E`. The book's
Definition of separability is `IsSeparable E` (a countable dense subset), identified with
Mathlib's `TopologicalSpace.SeparableSpace` by `separable_iff`; Proposition 3.25 is Mathlib's
instance chain (a separable metric space is second countable, and so is every subset); Theorem
3.26 and the reflexive half of Corollary 3.27 are the backbone
`Numlib/Analysis/Normed/Module/{DualSeparable,Reflexive}`; Theorems 3.28–3.29 and Remark 20 are
the backbone `Numlib/Analysis/Normed/Module/WeakStarMetrizable` (which also holds the two
exercises the text cites, 3.24 for the converse of 3.29 and 3.8 for Remarks 3 and 20);
Corollary 3.30 is Mathlib's `WeakDual.isSeqCompact_closedBall`. Remark 4 of §3.2 (and its
Exercise 3.22) is here, its proof being Theorem 3.29 with Example 1 of §3.2, or Theorem 3.18
with the sequential form of Eberlein–Šmulian. "Metrizable" is `TopologicalSpace.MetrizableSpace`
of the subtype.

## Main results

* `IsSeparable`, `separable_iff`, `proposition_3_25` — the Definition and subsets.
* `theorem_3_26`, `corollary_3_27` — `E*` separable ⇒ `E` separable; reflexive and separable
  passes to the dual and back.
* `theorem_3_28`, `theorem_3_29` (with `_mp`, `_mpr`) — `B_{E*}` is weak-∗ metrizable iff `E`
  is separable; `B_E` is weakly metrizable iff `E*` is separable.
* `remark_3_20` — in infinite dimension neither topology is metrizable on the whole space.
* `corollary_3_30` — sequential Banach–Alaoglu.
* `remark_3_4` — if `E*` is separable or `E` is reflexive, some sequence of unit vectors
  converges weakly to `0`.

Remark 19 (`L¹` separable, `L^∞` not) is chapter 4's.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Separability -/

/-- **The Definition of §3.6.** A (metric) space `E` is separable if it has a countable dense
subset `D`. -/
def IsSeparable (E : Type*) [TopologicalSpace E] : Prop :=
  ∃ D : Set E, D.Countable ∧ Dense D

/-- The book's Definition is Mathlib's `TopologicalSpace.SeparableSpace`. -/
theorem separable_iff (E : Type*) [TopologicalSpace E] :
    IsSeparable E ↔ TopologicalSpace.SeparableSpace E :=
  (TopologicalSpace.separableSpace_iff E).symm

/-- **Proposition 3.25.** Every subset `F` of a separable metric space `E` is separable. -/
theorem proposition_3_25 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    (F : Set X) : TopologicalSpace.SeparableSpace F :=
  inferInstance

/-- **Theorem 3.26.** If `E*` is separable then `E` is separable. -/
theorem theorem_3_26 [CompleteSpace E] [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.SeparableSpace E :=
  separableSpace_of_separableSpace_strongDual (𝕜 := ℝ)

/-- **Corollary 3.27.** `E` is reflexive and separable iff `E*` is reflexive and separable. -/
theorem corollary_3_27 [CompleteSpace E] :
    (IsReflexive E ∧ TopologicalSpace.SeparableSpace E) ↔
      (IsReflexive (StrongDual ℝ E) ∧ TopologicalSpace.SeparableSpace (StrongDual ℝ E)) := by
  constructor
  · rintro ⟨hE, hsep⟩
    have := isReflexive_iff.1 hE
    exact ⟨corollary_3_21.1 hE, NormedSpace.separableSpace_strongDual_of_isReflexive⟩
  · rintro ⟨hE, hsep⟩
    exact ⟨corollary_3_21.2 hE, theorem_3_26⟩

/-! ### Metrizability of the weak topologies on bounded sets -/

/-- **Theorem 3.28, forward.** If `E` is separable then `B_{E*}` is metrizable in the weak-∗
topology `σ(E*, E)`. -/
theorem theorem_3_28_mp [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.MetrizableSpace
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  WeakDual.metrizableSpace_closedBall 1

/-- **Theorem 3.28, converse.** If `B_{E*}` is metrizable in `σ(E*, E)` then `E` is
separable. -/
theorem theorem_3_28_mpr [CompleteSpace E]
    (h : TopologicalSpace.MetrizableSpace
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1)) :
    TopologicalSpace.SeparableSpace E :=
  separableSpace_of_metrizableSpace_weakDual_closedBall h

/-- **Theorem 3.28.** `E` is separable iff `B_{E*}` is metrizable in the weak-∗ topology
`σ(E*, E)`. -/
theorem theorem_3_28 [CompleteSpace E] :
    TopologicalSpace.SeparableSpace E ↔
      TopologicalSpace.MetrizableSpace
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  ⟨fun _ => theorem_3_28_mp, theorem_3_28_mpr⟩

/-- **Theorem 3.29, forward.** If `E*` is separable then `B_E` is metrizable in the weak
topology `σ(E, E*)` (the "however" of Remark 3). -/
theorem theorem_3_29_mp [CompleteSpace E] [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] :
    TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  WeakSpace.metrizableSpace_image_closedBall 1

/-- **Theorem 3.29, converse.** If `B_E` is metrizable in `σ(E, E*)` then `E*` is separable
(Exercise 3.24). -/
theorem theorem_3_29_mpr [CompleteSpace E]
    (h : TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1)) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ E) :=
  separableSpace_strongDual_of_metrizableSpace_weakSpace_closedBall h

/-- **Theorem 3.29.** `E*` is separable iff `B_E` is metrizable in the weak topology
`σ(E, E*)`. -/
theorem theorem_3_29 [CompleteSpace E] :
    TopologicalSpace.SeparableSpace (StrongDual ℝ E) ↔
      TopologicalSpace.MetrizableSpace (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  ⟨fun _ => theorem_3_29_mp, theorem_3_29_mpr⟩

/-- **Remark 20.** In an infinite-dimensional Banach space neither the weak topology
`σ(E, E*)` on all of `E` nor the weak-∗ topology `σ(E*, E)` on all of `E*` is metrizable
(Exercise 3.8); in particular the norm of the proof of Theorem 3.28 does not induce the weak-∗
topology on all of `E*`. -/
theorem remark_3_20 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ TopologicalSpace.MetrizableSpace (WeakSpace ℝ E) ∧
      ¬ TopologicalSpace.MetrizableSpace (WeakDual ℝ E) :=
  ⟨remark_3_3 h, not_metrizableSpace_weakDual h⟩

/-- **Corollary 3.30.** Let `E` be a separable Banach space and `(fₙ)` a bounded sequence in
`E*`. Then there is a subsequence `(f_{n_k})` converging in the weak-∗ topology `σ(E*, E)`. -/
theorem corollary_3_30 [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {f : ℕ → StrongDual ℝ E} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (g : StrongDual ℝ E) (φ : ℕ → ℕ), StrictMono φ ∧ (f ∘ φ) ⇀* g := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ E 0 C
    (x := fun n => StrongDual.toWeakDual (f n)) fun n => by
      simpa [mem_closedBall_zero_iff] using hf n
  exact ⟨WeakDual.toStrongDual a, φ, hφ,
    by simpa [WeakStarTendsto, Function.comp_def] using hlim⟩

/-! ### Remark 4 of §3.2 -/

/-- **Remark 4 of §3.2.** In an infinite-dimensional Banach space `E`, if `E*` is separable or
`E` is reflexive there is a sequence `(xₙ)` with `‖xₙ‖ = 1` and `xₙ ⇀ 0` weakly
(Exercise 3.22): `0` lies in the weak closure of the unit sphere (Example 1 of §3.2), which is
sequential on `B_E` when `B_E` is weakly metrizable (Theorem 3.29) or by Eberlein–Šmulian when
`E` is reflexive (Theorem 3.18). -/
theorem remark_3_4 [CompleteSpace E] (hinf : ¬ FiniteDimensional ℝ E)
    (h : TopologicalSpace.SeparableSpace (StrongDual ℝ E) ∨ IsReflexive E) :
    ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧ x ⇀ 0 := by
  have h0 : toWeakSpace ℝ E 0 ∈ closure (toWeakSpace ℝ E '' sphere (0 : E) 1) := by
    rw [(example_3_1 hinf).1]
    exact ⟨0, by simp, rfl⟩
  rcases h with hsep | hrefl
  · -- `B_E` is weakly metrizable, so the weak closure of the sphere in it is sequential
    set B : Set (WeakSpace ℝ E) := toWeakSpace ℝ E '' closedBall (0 : E) 1 with hB
    have hmetr : TopologicalSpace.MetrizableSpace B := theorem_3_29_mp
    set S : Set B := Subtype.val ⁻¹' (toWeakSpace ℝ E '' sphere (0 : E) 1) with hS
    have h0B : toWeakSpace ℝ E 0 ∈ B := ⟨0, by simp, rfl⟩
    have h0S : (⟨toWeakSpace ℝ E 0, h0B⟩ : B) ∈ closure S := by
      rw [closure_subtype]
      have : Subtype.val '' S = toWeakSpace ℝ E '' sphere (0 : E) 1 := by
        rw [hS, Subtype.image_preimage_val]
        exact inter_eq_right.2 (image_mono sphere_subset_closedBall)
      rw [this]
      exact h0
    obtain ⟨y, hyS, hy⟩ := mem_closure_iff_seq_limit.1 h0S
    refine ⟨fun n => (toWeakSpace ℝ E).symm (y n : WeakSpace ℝ E), fun n => ?_, ?_⟩
    · obtain ⟨z, hz, hzy⟩ := hyS n
      change ‖(toWeakSpace ℝ E).symm (y n : WeakSpace ℝ E)‖ = 1
      rw [← hzy, LinearEquiv.symm_apply_apply]
      exact mem_sphere_zero_iff_norm.1 hz
    · have := (continuous_subtype_val.tendsto _).comp hy
      simpa [WeakTendsto, Function.comp_def] using this
  · -- Eberlein–Šmulian: the weak closure of a set whose sequences have weakly convergent
    -- subsequences is sequential
    obtain ⟨y, hy, hlim⟩ :=
      NormedSpace.exists_seq_tendsto_toWeakSpace_of_mem_closure_image_toWeakSpace
        (A := sphere (0 : E) 1) (fun x hx => theorem_3_18 hrefl (C := 1)
          fun n => (mem_sphere_zero_iff_norm.1 (hx n)).le) h0
    exact ⟨y, fun n => mem_sphere_zero_iff_norm.1 (hy n), hlim⟩

end Brezis.Chapter03
