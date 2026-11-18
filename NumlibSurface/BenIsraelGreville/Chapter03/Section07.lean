/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.LinearAlgebra.Matrix.SVD
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Metric projections and generalized inverses for essentially strictly convex norms

Section 3.7 of [benIsrael2003generalized] uses metric projections onto the
range and kernel of a linear map. The norms are the given norm structures
on two finite-dimensional spaces. The projections and the associated
inverse are functions because their minimizing points are unique.

## Deviations from the source

* In Exercise 49 the minimizing segment is `(t, 1 - t)`, a segment of the
  stated affine line.
* The dual-vector and norm identities below use the operator norm on the
  complex continuous dual, with the real part of its canonical pairing.

-/

noncomputable section

namespace BenIsraelGreville.Chapter03

open Set Filter
open scoped Topology Pointwise

section StrictConvexity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Equation (119)** of [benIsrael2003generalized], Chapter 3.
A norm is essentially strictly convex when a proper convex combination of
distinct vectors of equal norm has strictly smaller norm. -/
def essentiallyStrictlyConvex : Prop :=
  ∀ x y : E, x ≠ y → ‖x‖ = ‖y‖ → ∀ t : ℝ, 0 < t → t < 1 →
    ‖t • x + (1 - t) • y‖ < ‖x‖

/-- This is strict convexity of the unit ball in the real scalar structure. -/
theorem essentiallyStrictlyConvex_iff :
    essentiallyStrictlyConvex E ↔ StrictConvexSpace ℝ E := by
  constructor
  · intro h
    apply StrictConvexSpace.of_norm_combo_lt_one
    intro x y hx hy hne
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, ?_⟩
    have he := h x y hne (hx.trans hy.symm) (1 / 2) (by norm_num) (by norm_num)
    rw [hx, show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] at he
    exact he
  · intro h
    let : StrictConvexSpace ℝ E := h
    intro x y hxy he t ht ht'
    exact norm_combo_lt_of_ne le_rfl he.ge hxy ht (sub_pos.mpr ht') (by ring)

/-- **Equation (118)** of [benIsrael2003generalized], Chapter 3.
The norm inequality is strict whenever the two vectors are in different
nonnegative real rays. -/
theorem essentiallyStrictlyConvex_iff_strictAwayFromRays :
    essentiallyStrictlyConvex E ↔
      ∀ x y : E, ¬ SameRay ℝ x y → ∀ t : ℝ, 0 < t → t < 1 →
        ‖t • x + (1 - t) • y‖ < t * ‖x‖ + (1 - t) * ‖y‖ := by
  constructor
  · intro h x y hxy t ht₀ ht₁
    let : StrictConvexSpace ℝ E := (essentiallyStrictlyConvex_iff E).mp h
    have hb : 0 < 1 - t := sub_pos.mpr ht₁
    have hx : x ≠ 0 := fun he => hxy (he.symm ▸ SameRay.zero_left y)
    have hy : y ≠ 0 := fun he => hxy (he.symm ▸ SameRay.zero_right x)
    have hn : ¬ SameRay ℝ (t • x) ((1 - t) • y) := by
      intro he
      apply hxy
      have h₁ := (SameRay.sameRay_pos_smul_right x ht₀).trans he
        (fun hzero => (smul_ne_zero ht₀.ne' hx hzero).elim)
      exact h₁.trans (SameRay.sameRay_pos_smul_left y hb)
        (fun hzero => (smul_ne_zero hb.ne' hy hzero).elim)
    have he := norm_add_lt_of_not_sameRay hn
    rwa [norm_smul, norm_smul, Real.norm_of_nonneg ht₀.le, Real.norm_of_nonneg hb.le] at he
  · intro h x y hxy he t ht₀ ht₁
    have hn : ¬ SameRay ℝ x y := (not_sameRay_iff_of_norm_eq he).mpr hxy
    have hh := h x y hn t ht₀ ht₁
    rwa [← he, show t * ‖x‖ + (1 - t) * ‖x‖ = ‖x‖ by ring] at hh

end StrictConvexity

section Projector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 3.
The metric projector selects a closest point of the subspace. Under
essential strict convexity this solution is unique. -/
abbrev definition_1 (L : Submodule ℂ E) (x : E) : E := bestApprox (L : Set E) x

/-- On a finite-dimensional subspace the metric projector realizes the minimum. -/
theorem isBestApprox_definition_1 (L : Submodule ℂ E) [FiniteDimensional ℂ L] (x : E) :
    IsBestApprox (L : Set E) x (definition_1 L x) :=
  isBestApprox_bestApprox (exists_isBestApprox_of_finiteDimensional L x)

/-- Every value of the projector lies in the subspace. -/
theorem definition_1_mem (L : Submodule ℂ E) [FiniteDimensional ℂ L] (x : E) :
    definition_1 L x ∈ L :=
  (isBestApprox_definition_1 L x).1

/-- **Theorem 11(a)** of [benIsrael2003generalized], Chapter 3.
The fixed points of the projector are exactly the points of the subspace. -/
theorem definition_1_eq_self_iff (L : Submodule ℂ E) [FiniteDimensional ℂ L] (x : E) :
    definition_1 L x = x ↔ x ∈ L := by
  constructor
  · intro h
    rw [← h]
    exact definition_1_mem L x
  · intro hx
    have h := (isBestApprox_definition_1 L x).2 x hx
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [norm_sub_rev]
    exact le_antisymm (by simpa only [sub_self, norm_zero] using h) (norm_nonneg _)

/-- **Theorem 11(b)** of [benIsrael2003generalized], Chapter 3. -/
theorem definition_1_idempotent (L : Submodule ℂ E) [FiniteDimensional ℂ L] :
    (∀ x, definition_1 L (definition_1 L x) = definition_1 L x) :=
  fun x => (definition_1_eq_self_iff L _).mpr (definition_1_mem L x)

/-- **Theorem 11(f)** of [benIsrael2003generalized], Chapter 3.
The norm of the residual is a 1-Lipschitz function of the data. -/
theorem definition_1_residual_lipschitz (L : Submodule ℂ E) [FiniteDimensional ℂ L] :
    LipschitzWith 1 (fun x => ‖x - definition_1 L x‖) := by
  have h (x : E) : ‖x - definition_1 L x‖ = Metric.infDist x (L : Set E) :=
    (isBestApprox_definition_1 L x).norm_sub_eq_infDist
  simpa only [h] using Metric.lipschitz_infDist_pt (s := (L : Set E))

/-- **Theorem 11(g)** of [benIsrael2003generalized], Chapter 3. -/
theorem definition_1_residual_norm_le (L : Submodule ℂ E) [FiniteDimensional ℂ L] (x : E) :
    ‖x - definition_1 L x‖ ≤ ‖x‖ := by
  simpa only [sub_zero] using (isBestApprox_definition_1 L x).2 0 L.zero_mem

/-- **Theorem 11(h)** of [benIsrael2003generalized], Chapter 3. -/
theorem definition_1_norm_le (L : Submodule ℂ E) [FiniteDimensional ℂ L] (x : E) :
    ‖definition_1 L x‖ ≤ 2 * ‖x‖ := calc
  ‖definition_1 L x‖ = ‖x - (x - definition_1 L x)‖ := by rw [sub_sub_cancel]
  _ ≤ ‖x‖ + ‖x - definition_1 L x‖ := norm_sub_le _ _
  _ ≤ 2 * ‖x‖ := by linarith [definition_1_residual_norm_le L x]

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- **Lemma 3** of [benIsrael2003generalized], Chapter 3.
A point has exactly one closest point in each finite-dimensional subspace. -/
theorem lemma_3 (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (x : E) : ∃! y, IsBestApprox (L : Set E) x y := by
  let : StrictConvexSpace ℝ E := (essentiallyStrictlyConvex_iff E).mp h
  refine ⟨definition_1 L x, isBestApprox_definition_1 L x, fun y hy => ?_⟩
  exact hy.unique (L.restrictScalars ℝ).convex (isBestApprox_definition_1 L x)

/-- A candidate equals the metric projection precisely when it realizes the minimum. -/
theorem definition_1_eq_iff (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (x y : E) :
    definition_1 L x = y ↔ IsBestApprox (L : Set E) x y := by
  let : StrictConvexSpace ℝ E := (essentiallyStrictlyConvex_iff E).mp h
  refine ⟨fun he => he ▸ isBestApprox_definition_1 L x, fun hy => ?_⟩
  exact (isBestApprox_definition_1 L x).unique (L.restrictScalars ℝ).convex hy

/-- **Theorem 11(c)** of [benIsrael2003generalized], Chapter 3.
The metric projector is homogeneous for complex scalars. -/
theorem definition_1_smul (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (c : ℂ) (x : E) :
    definition_1 L (c • x) = c • definition_1 L x := by
  by_cases hc : c = 0
  · subst c
    simpa only [zero_smul] using (definition_1_eq_self_iff L 0).mpr L.zero_mem
  · apply (definition_1_eq_iff h L _ _).mpr
    refine ⟨L.smul_mem _ (definition_1_mem L x), fun y hy => ?_⟩
    have he : c • (c⁻¹ • y) = y := smul_inv_smul₀ hc y
    have hb := (isBestApprox_definition_1 L x).2 (c⁻¹ • y) (L.smul_mem _ hy)
    rw [← he, ← smul_sub, ← smul_sub, norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg c)

/-- **Theorem 11(d)** of [benIsrael2003generalized], Chapter 3.
The projector commutes with translations by a vector of the subspace. -/
theorem definition_1_add_mem (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (x : E) {y : E} (hy : y ∈ L) :
    definition_1 L (x + y) = definition_1 L x + y := by
  apply (definition_1_eq_iff h L _ _).mpr
  refine ⟨L.add_mem (definition_1_mem L x) hy, fun z hz => ?_⟩
  rw [add_sub_add_right_eq_sub]
  have he : x + y - z = x - (z - y) := by abel
  rw [he]
  exact (isBestApprox_definition_1 L x).2 _ (L.sub_mem hz hy)

/-- **Theorem 11(e)** of [benIsrael2003generalized], Chapter 3. -/
theorem definition_1_residual (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (x : E) : definition_1 L (x - definition_1 L x) = 0 := by
  rw [sub_eq_add_neg, definition_1_add_mem h L x (L.neg_mem (definition_1_mem L x)),
    add_neg_cancel]

/-- **Theorem 11(i)** of [benIsrael2003generalized], Chapter 3.
Continuity follows from boundedness of projected converging sequences
and uniqueness of every cluster point. -/
theorem continuous_definition_1 [FiniteDimensional ℂ E] (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) : Continuous (definition_1 L) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  by_contra hnot
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  let P := definition_1 L
  let K : Set E := (L : Set E) ∩ Metric.closedBall 0 (2 * (‖x‖ + 1)) ∩
    {z | ε ≤ dist z (P x)}
  have hK : IsCompact K := by
    exact ((isCompact_closedBall 0 _).inter_left L.closed_of_finiteDimensional).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have huB : ∀ᶠ i in atTop, ‖u i‖ < ‖x‖ + 1 :=
    hu.norm.eventually_lt_const (by linarith)
  have hP : ∃ᶠ i in atTop, P (u i) ∈ K := by
    apply (hfreq.and_eventually huB).mono
    intro i hi
    refine ⟨⟨definition_1_mem L (u i), ?_⟩, hi.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [definition_1_norm_le L (u i)]
  obtain ⟨z, hz, φ, hφ, ht⟩ := hK.tendsto_subseq' hP
  have huv := hu.comp hφ.tendsto_atTop
  have hzbest : IsBestApprox (L : Set E) x z := by
    refine ⟨hz.1.1, fun w hw => ?_⟩
    exact le_of_tendsto_of_tendsto' (huv.sub ht).norm
      (huv.sub tendsto_const_nhds).norm fun i => (isBestApprox_definition_1 L (u (φ i))).2 _ hw
  have he := (definition_1_eq_iff h L x z).mpr hzbest
  have hd : ε ≤ dist z (P x) := hz.2
  rw [show P x = z from he, dist_self] at hd
  exact (not_le_of_gt hε) hd

/-- **Theorem 11(a)–(i)** of [benIsrael2003generalized], Chapter 3.
The metric projection has the stated fixed-point, homogeneity, translation,
norm, and continuity properties. -/
theorem theorem_11 [FiniteDimensional ℂ E] (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) :
    (∀ x, definition_1 L x = x ↔ x ∈ L) ∧
    (∀ x, definition_1 L (definition_1 L x) = definition_1 L x) ∧
    (∀ c : ℂ, ∀ x, definition_1 L (c • x) = c • definition_1 L x) ∧
    (∀ x y, y ∈ L → definition_1 L (x + y) = definition_1 L x + y) ∧
    (∀ x, definition_1 L (x - definition_1 L x) = 0) ∧
    LipschitzWith 1 (fun x => ‖x - definition_1 L x‖) ∧
    (∀ x, ‖x - definition_1 L x‖ ≤ ‖x‖) ∧
    (∀ x, ‖definition_1 L x‖ ≤ 2 * ‖x‖) ∧ Continuous (definition_1 L) :=
  ⟨definition_1_eq_self_iff L, definition_1_idempotent L, definition_1_smul h L,
    fun x _ => definition_1_add_mem h L x, definition_1_residual h L,
    definition_1_residual_lipschitz L, definition_1_residual_norm_le L, definition_1_norm_le L,
    continuous_definition_1 h L⟩

/-- Translation along the subspace leaves the residual unchanged. -/
theorem definition_1_residual_add_mem (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] (x : E) {y : E} (hy : y ∈ L) :
    (x + y) - definition_1 L (x + y) = x - definition_1 L x := by
  rw [definition_1_add_mem h L x hy, add_sub_add_right_eq_sub]

/-- **Equations (121)–(122)** of [benIsrael2003generalized], Chapter 3.
The zero fiber consists of all the residual vectors, and other fibers
are its translates by their value in the subspace. -/
theorem metricProjector_fibers (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] :
    {x | definition_1 L x = 0} = Set.range (fun x => x - definition_1 L x) ∧
      ∀ y ∈ L, ∀ x, definition_1 L x = y ↔ definition_1 L (x - y) = 0 := by
  constructor
  · ext x
    constructor
    · intro hx
      change definition_1 L x = 0 at hx
      exact ⟨x, by change x - definition_1 L x = x; rw [hx, sub_zero]⟩
    · rintro ⟨y, rfl⟩
      exact definition_1_residual h L y
  · intro y hy x
    rw [sub_eq_add_neg, definition_1_add_mem h L x (L.neg_mem hy), ← sub_eq_add_neg,
      sub_eq_zero]

private theorem additive_of_zeroFiber_closed_add (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) [FiniteDimensional ℂ L]
    (hadd : ∀ x y, definition_1 L x = 0 → definition_1 L y = 0 →
      definition_1 L (x + y) = 0) :
    ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y := by
  intro x y
  let a := x - definition_1 L x
  let b := y - definition_1 L y
  have h₁ : definition_1 L (a + b) = 0 :=
    hadd a b (definition_1_residual h L x) (definition_1_residual h L y)
  have hp : definition_1 L x + definition_1 L y ∈ L :=
    L.add_mem (definition_1_mem L x) (definition_1_mem L y)
  have he : x + y = a + b + (definition_1 L x + definition_1 L y) := by
    dsimp [a, b]
    abel
  have hout := (definition_1_add_mem h L (a + b) hp)
  rw [h₁, zero_add, ← he] at hout
  exact hout

/-- **Corollary 5** of [benIsrael2003generalized], Chapter 3.
Additivity is equivalent to the zero fiber being a subspace, or to all
the fibers over the projection subspace being affine subspaces. -/
theorem corollary_5 (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    [FiniteDimensional ℂ L] :
    ((∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y) ↔
      ∃ N : Submodule ℂ E, ∀ x, x ∈ N ↔ definition_1 L x = 0) ∧
    ((∃ N : Submodule ℂ E, ∀ x, x ∈ N ↔ definition_1 L x = 0) ↔
      ∀ y ∈ L, ∃ N : Submodule ℂ E, ∀ x, definition_1 L x = y ↔ x - y ∈ N) := by
  constructor
  · constructor
    · intro hadd
      let N : Submodule ℂ E :=
        { carrier := {x | definition_1 L x = 0}
          zero_mem' := (definition_1_eq_self_iff L _).mpr L.zero_mem
          add_mem' := fun hx hy => by
            change definition_1 L _ = 0 at hx hy ⊢
            rw [hadd, hx, hy, add_zero]
          smul_mem' := fun c _ hx => by
            change definition_1 L _ = 0 at hx ⊢
            rw [definition_1_smul h L c, hx, smul_zero] }
      exact ⟨N, fun _ => Iff.rfl⟩
    · rintro ⟨N, hN⟩
      exact additive_of_zeroFiber_closed_add h L fun x y hx hy =>
        (hN _).mp (N.add_mem ((hN x).mpr hx) ((hN y).mpr hy))
  · constructor
    · rintro ⟨N, hN⟩ y hy
      exact ⟨N, fun x => ((metricProjector_fibers h L).2 y hy x).trans (hN _).symm⟩
    · intro he
      obtain ⟨N, hN⟩ := he 0 L.zero_mem
      exact ⟨N, fun x => by simpa only [sub_zero] using (hN x).symm⟩

/-- **Corollary 6** of [benIsrael2003generalized], Chapter 3.
The metric projection onto a subspace of codimension one is additive. -/
theorem corollary_6 [FiniteDimensional ℂ E] (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) (hL : Module.finrank ℂ L + 1 = Module.finrank ℂ E) :
    ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y := by
  obtain ⟨M, hM⟩ := L.exists_isCompl
  have hdim : Module.finrank ℂ M = 1 := by
    have he := Submodule.finrank_add_eq_of_isCompl hM
    omega
  obtain ⟨u, hu, hu₀⟩ : ∃ u ∈ M, u ≠ 0 := M.ne_bot_iff.mp
    (by intro he; rw [he, finrank_bot] at hdim; omega)
  have hspan : M = ℂ ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hdim hu hu₀
  let v := u - definition_1 L u
  apply (corollary_5 h L).1.mpr
  refine ⟨ℂ ∙ v, fun x => ?_⟩
  constructor
  · rintro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [definition_1_smul h L, show definition_1 L v = 0 from definition_1_residual h L u,
      smul_zero]
  · intro hx
    have hx' : x ∈ L ⊔ M := by rw [hM.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.mp hx'
    rw [hspan] at hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hz : c • definition_1 L u + l = 0 := by
      simpa only [add_comm l, definition_1_add_mem h L _ hl,
        definition_1_smul h L] using hx
    have he : l = -(c • definition_1 L u) := eq_neg_of_add_eq_zero_right hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    change c • (u - definition_1 L u) = l + c • u
    rw [smul_sub, he]
    abel

private theorem exists_submodule_with_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (r : ℕ)
    (hW : Module.finrank ℂ W ≤ r) (hr : r ≤ Module.finrank ℂ V) :
    ∃ N : Submodule ℂ V, W ≤ N ∧ Module.finrank ℂ N = r := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  have hle : r - Module.finrank ℂ W ≤ Module.finrank ℂ C := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hle
  let D := Submodule.span ℂ (Set.range (C.subtype ∘ v))
  have hv' := hv.map' C.subtype C.ker_subtype
  have hD : D ≤ C := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).2)
  have hd : Module.finrank ℂ D = r - Module.finrank ℂ W := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range (C.subtype ∘ v))) = _
    rw [finrank_span_eq_card hv', Fintype.card_fin]
  refine ⟨W ⊔ D, le_sup_left, ?_⟩
  have hdj := hC.disjoint.mono_right hD
  have he := Submodule.finrank_sup_add_finrank_inf_eq W D
  rw [hdj.eq_bot, finrank_bot, add_zero, hd] at he
  omega

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
private theorem exists_submodule_with_finrank_of_mem [FiniteDimensional ℂ E]
    (L : Submodule ℂ E) {y : E} (hy : y ∈ L) (r : ℕ) (h₁ : 1 ≤ r)
    (h₂ : r ≤ Module.finrank ℂ L) :
    ∃ M : Submodule ℂ E, M ≤ L ∧ y ∈ M ∧ Module.finrank ℂ M = r := by
  let x : L := ⟨y, hy⟩
  let W := ℂ ∙ x
  have hW : Module.finrank ℂ W ≤ r := (finrank_span_le_card ({x} : Set L)).trans (by simpa)
  obtain ⟨M, hWM, hM⟩ := exists_submodule_with_finrank W r hW h₂
  let N := M.map L.subtype
  have hN : N ≤ L := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hx : x ∈ M := hWM (Submodule.mem_span_singleton_self x)
  exact ⟨N, hN, ⟨x, hx, rfl⟩, (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective L.subtype L.injective_subtype M)).symm.trans hM⟩

/-- If the closest point for a larger subspace lies in a smaller subspace,
it is also the closest point for the smaller one. -/
theorem definition_1_eq_of_le [FiniteDimensional ℂ E] (h : essentiallyStrictlyConvex E)
    {M L : Submodule ℂ E} (hML : M ≤ L) {x : E} (hx : definition_1 L x ∈ M) :
    definition_1 M x = definition_1 L x :=
  (definition_1_eq_iff h M _ _).mpr ⟨hx, fun _ hw => (isBestApprox_definition_1 L x).2 _ (hML hw)⟩

/-- **Corollary 7** of [benIsrael2003generalized], Chapter 3.
Additivity of every projector in one positive dimension implies additivity
in all larger dimensions. -/
theorem corollary_7 [FiniteDimensional ℂ E] (h : essentiallyStrictlyConvex E)
    (r : ℕ) (hr : 1 ≤ r)
    (hadd : ∀ M : Submodule ℂ E, Module.finrank ℂ M = r →
      ∀ x y, definition_1 M (x + y) = definition_1 M x + definition_1 M y)
    (L : Submodule ℂ E) (hL : r ≤ Module.finrank ℂ L) :
    ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y := by
  apply additive_of_zeroFiber_closed_add h L
  intro x x' hx hx'
  let y := definition_1 L (x + x')
  obtain ⟨M, hML, hy, hM⟩ :=
    exists_submodule_with_finrank_of_mem L (definition_1_mem L (x+x')) r hr hL
  have hP : definition_1 M (x + x') = y := definition_1_eq_of_le h hML hy
  have hP₁ : definition_1 M x = 0 :=
    (definition_1_eq_of_le h hML (hx.symm ▸ M.zero_mem)).trans hx
  have hP₂ : definition_1 M x' = 0 :=
    (definition_1_eq_of_le h hML (hx'.symm ▸ M.zero_mem)).trans hx'
  rw [hadd M hM, hP₁, hP₂, add_zero] at hP
  exact hP.symm

end Projector

section TwoNormInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem exists_linearInnerInverse (A : E →ₗ[ℂ] F) :
    ∃ U : F →ₗ[ℂ] E, ∀ x, A (U (A x)) = A x := by
  obtain ⟨V, hV⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  obtain ⟨W, hW⟩ := A.range.subtype.exists_leftInverse_of_injective (by simp)
  refine ⟨V.comp W, fun x => ?_⟩
  have h₁ : W (A x) = A.rangeRestrict x := DFunLike.congr_fun hW (A.rangeRestrict x)
  have h₂ : A.rangeRestrict (V (A.rangeRestrict x)) = A.rangeRestrict x :=
    DFunLike.congr_fun hV (A.rangeRestrict x)
  change A (V (W (A x))) = A x
  rw [h₁]
  exact congrArg Subtype.val h₂

/-- **Definition 2, Equation (123)** of [benIsrael2003generalized], Chapter 3.
Project to the range in the output norm, choose a preimage by an inner
inverse, and subtract the kernel projection in the input norm. -/
def definition_2 (A : E →ₗ[ℂ] F) (y : F) : E :=
  let x := (exists_linearInnerInverse A).choose (definition_1 A.range y)
  x - definition_1 A.ker x

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- **Equation (124)** of [benIsrael2003generalized], Chapter 3.
The inverse can be evaluated using any linear inner inverse. -/
theorem definition_2_eq_of_innerInverse (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (U : F →ₗ[ℂ] E) (hU : ∀ x, A (U (A x)) = A x) (y : F) :
    let x := U (definition_1 A.range y)
    definition_2 A y = x - definition_1 A.ker x := by
  intro x
  let P := definition_1 A.range
  let T := (exists_linearInnerInverse A).choose
  let z := T (P y)
  obtain ⟨w, hw⟩ := definition_1_mem A.range y
  change A w = P y at hw
  have hx : A x = P y := by
    change A (U (P y)) = P y
    rw [← hw, hU]
  have hz : A z = P y := by
    change A (T (P y)) = P y
    rw [← hw, (exists_linearInnerInverse A).choose_spec]
  have he : z - x ∈ A.ker := by
    rw [LinearMap.mem_ker, map_sub, hz, hx, sub_self]
  have hr := definition_1_residual_add_mem hβ A.ker x he
  rw [show x + (z - x) = z by abel] at hr
  exact hr

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F] in
/-- **Theorem 12(e)** of [benIsrael2003generalized], Chapter 3.
Applying the original operator after the inverse gives the range projection. -/
theorem definition_2_apply_left (A : E →ₗ[ℂ] F) (y : F) :
    A (definition_2 A y) = definition_1 A.range y := by
  let P := definition_1 A.range
  let U := (exists_linearInnerInverse A).choose
  let z := U (P y)
  obtain ⟨w, hw⟩ := definition_1_mem A.range y
  change A w = P y at hw
  have hz : A z = P y := by
    change A (U (P y)) = P y
    rw [← hw, (exists_linearInnerInverse A).choose_spec]
  change A (z - definition_1 A.ker z) = P y
  rw [map_sub, hz, show A (definition_1 A.ker z) = 0 from definition_1_mem A.ker z, sub_zero]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- **Theorem 12(f)** of [benIsrael2003generalized], Chapter 3.
Applying the inverse after the operator gives the residual of the kernel projection. -/
theorem definition_2_apply_right (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (x : E) :
    definition_2 A (A x) = x - definition_1 A.ker x := by
  let T := (exists_linearInnerInverse A).choose
  let u := T (A x)
  have hp := (definition_1_eq_self_iff A.range (A x)).mpr (LinearMap.mem_range_self A x)
  have h : u - x ∈ A.ker := by
    rw [LinearMap.mem_ker, map_sub, show A u = A x from
      (exists_linearInnerInverse A).choose_spec x, sub_self]
  change T (definition_1 A.range (A x)) - definition_1 A.ker (T (definition_1 A.range (A x))) = _
  rw [hp]
  have hr := definition_1_residual_add_mem hβ A.ker x h
  rw [show x + (u - x) = u by abel] at hr
  exact hr

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
/-- Any generalized inverse value has zero kernel projection. -/
theorem definition_2_kernelProjection (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (y : F) : definition_1 A.ker (definition_2 A y) = 0 :=
  definition_1_residual hβ A.ker ((exists_linearInnerInverse A).choose (definition_1 A.range y))

/-- **Theorem 12(i)** of [benIsrael2003generalized], Chapter 3.
An approximate solution minimizes the residual in the output norm. -/
def IsAlphaApproximateSolution (A : E →ₗ[ℂ] F) (y : F) (x : E) : Prop :=
  ∀ z, ‖A x - y‖ ≤ ‖A z - y‖

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ F] in
/-- **Equation (125)** of [benIsrael2003generalized], Chapter 3.
The approximate solutions are precisely the lifts of the projected datum. -/
theorem isAlphaApproximateSolution_iff (hα : essentiallyStrictlyConvex F)
    (A : E →ₗ[ℂ] F) (y : F) (x : E) :
    IsAlphaApproximateSolution A y x ↔ A x = A (definition_2 A y) := by
  rw [definition_2_apply_left, eq_comm, definition_1_eq_iff hα]
  constructor
  · intro h
    refine ⟨LinearMap.mem_range_self A x, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [norm_sub_rev y (A x), norm_sub_rev y (A z)]
    exact h z
  · intro h z
    rw [norm_sub_rev (A x) y, norm_sub_rev (A z) y]
    exact h.2 _ (LinearMap.mem_range_self A z)

omit [FiniteDimensional ℂ F] in
/-- **Equations (126a)–(126b)** of [benIsrael2003generalized], Chapter 3.
The inverse gives an approximate solution with strictly smaller input
norm than every other approximate solution. -/
theorem definition_2_leastApproximateSolution (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) (A : E →ₗ[ℂ] F) (y : F) :
    IsAlphaApproximateSolution A y (definition_2 A y) ∧
      ∀ x, IsAlphaApproximateSolution A y x → x ≠ definition_2 A y →
        ‖definition_2 A y‖ < ‖x‖ := by
  let u := definition_2 A y
  refine ⟨(isAlphaApproximateSolution_iff hα A y u).mpr rfl, fun x hx hxne => ?_⟩
  let z := u - x
  have hz : z ∈ A.ker := by
    change A (u - x) = 0
    rw [map_sub, (isAlphaApproximateSolution_iff hα A y x).mp hx, sub_self]
  have hker : definition_1 A.ker u = 0 := definition_2_kernelProjection hβ A y
  have hnorm : ‖u - z‖ = ‖x‖ := by rw [show u - z = x from sub_sub_cancel u x]
  have hbest := isBestApprox_definition_1 A.ker u
  rw [hker] at hbest
  have hle := hbest.2 z hz
  rw [sub_zero, hnorm] at hle
  refine lt_of_le_of_ne hle fun he => ?_
  have hzbest : IsBestApprox (A.ker : Set E) u z := by
    refine ⟨hz, ?_⟩
    rw [hnorm, ← he]
    simpa only [sub_zero] using hbest.2
  have hzero := (definition_1_eq_iff hβ A.ker u z).mpr hzbest
  rw [hker, eq_comm, sub_eq_zero] at hzero
  exact hxne hzero.symm

omit [FiniteDimensional ℂ F] in
/-- **Theorem 12(a)–(j)** of [benIsrael2003generalized], Chapter 3.
The two-norm inverse is homogeneous, is additive when its projections
are additive, obeys the reflexive equations, and gives the unique
least-norm approximate solution. -/
theorem theorem_12 (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) :
    let X := definition_2 A
    (∀ c : ℂ, ∀ y, X (c • y) = c • X y) ∧
    ((∀ u v, definition_1 A.range (u + v) = definition_1 A.range u + definition_1 A.range v) →
      (∀ u v, definition_1 A.ker (u + v) = definition_1 A.ker u + definition_1 A.ker v) →
      ∀ u v, X (u + v) = X u + X v) ∧
    {y | X y = 0} = {y | definition_1 A.range y = 0} ∧
    Set.range X = {x | definition_1 A.ker x = 0} ∧
    (∀ y, A (X y) = definition_1 A.range y) ∧
    (∀ x, X (A x) = x - definition_1 A.ker x) ∧
    (∀ x, A (X (A x)) = A x) ∧
    (∀ y, X (A (X y)) = X y) ∧
    (∀ y x, IsAlphaApproximateSolution A y x ↔ A x = A (X y)) ∧
    ∀ y, IsAlphaApproximateSolution A y (X y) ∧
      ∀ x, IsAlphaApproximateSolution A y x → x ≠ X y → ‖X y‖ < ‖x‖ := by
  intro X
  let U := (exists_linearInnerInverse A).choose
  refine ⟨?_, ?_, ?_, ?_, definition_2_apply_left A, definition_2_apply_right hβ A,
    ?_, ?_, isAlphaApproximateSolution_iff hα A, definition_2_leastApproximateSolution hα hβ A⟩
  · intro c y
    change U (definition_1 A.range (c • y)) - _ = c • (U (definition_1 A.range y) - _)
    rw [definition_1_smul hα, map_smul, definition_1_smul hβ, smul_sub]
  · intro hR hK x y
    change U (definition_1 A.range (x + y)) - _ =
      (U (definition_1 A.range x) - _) + (U (definition_1 A.range y) - _)
    rw [hR, map_add, hK, add_sub_add_comm]
  · ext y
    change X y = 0 ↔ definition_1 A.range y = 0
    rw [← definition_2_apply_left A y]
    refine ⟨fun hy => _root_.map_zero A ▸ congrArg A hy, fun hy => ?_⟩
    have hk : X y ∈ A.ker := hy
    have hf := (definition_1_eq_self_iff A.ker (X y)).mpr hk
    rw [definition_2_kernelProjection hβ] at hf
    exact hf.symm
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact definition_2_kernelProjection hβ A y
    · intro hx
      change definition_1 A.ker x = 0 at hx
      refine ⟨A x, ?_⟩
      change definition_2 A (A x) = x
      rw [definition_2_apply_right hβ, hx, sub_zero]
  · intro x
    rw [definition_2_apply_left, (definition_1_eq_self_iff A.range _).mpr
      (LinearMap.mem_range_self A x)]
  · intro y
    change definition_2 A (A (X y)) = X y
    rw [definition_2_apply_right hβ, show definition_1 A.ker (X y) = 0 from
      definition_2_kernelProjection hβ A y, sub_zero]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- **Exercise 78** of [benIsrael2003generalized], Chapter 3.
If a linear candidate has the two prescribed projector products and the
same rank, then it agrees pointwise with the two-norm inverse. -/
theorem exercise_78 (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (B : F →ₗ[ℂ] E)
    (hAB : ∀ y, A (B y) = definition_1 A.range y)
    (hBA : ∀ x, B (A x) = x - definition_1 A.ker x)
    (hRank : Module.finrank ℂ B.range = Module.finrank ℂ A.range) :
    ∀ y, B y = definition_2 A y := by
  let C : B.range →ₗ[ℂ] A.range := A.rangeRestrict.comp B.range.subtype
  have hsurj : Function.Surjective C := by
    rintro ⟨a, ⟨x, rfl⟩⟩
    refine ⟨⟨B (A x), ⟨A x, rfl⟩⟩, Subtype.ext ?_⟩
    change A (B (A x)) = A x
    rw [hAB, (definition_1_eq_self_iff A.range _).mpr (LinearMap.mem_range_self A x)]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hRank).mpr hsurj
  intro y
  let u := definition_2 A y
  have hu : u ∈ B.range := ⟨A u, by
    rw [hBA, show definition_1 A.ker u = 0 from definition_2_kernelProjection hβ A y,
      sub_zero]⟩
  have he : C ⟨B y, ⟨y, rfl⟩⟩ = C ⟨u, hu⟩ := by
    apply Subtype.ext
    change A (B y) = A (definition_2 A y)
    rw [hAB, definition_2_apply_left]
  exact congrArg Subtype.val (hinj he)

end TwoNormInverse

section EuclideanSpecialization

open Matrix

/-- With Euclidean norms on both spaces, the two-norm inverse is exactly
the Moore–Penrose inverse. -/
theorem definition_2_euclidean {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (y : EuclideanSpace ℂ m) :
    definition_2 (toEuclideanLin A) y = toEuclideanLin A.pinv y := by
  let T := toEuclideanLin A
  let U := toEuclideanLin A.pinv
  let P := definition_1 T.range
  let x := (exists_linearInnerInverse T).choose (P y)
  have hp : P y = T (U y) := by
    change definition_1 T.range y = _
    rw [IsBestApprox.eq_starProjection T.range (isBestApprox_definition_1 T.range y)]
    change T.range.starProjection y = toEuclideanLin A (toEuclideanLin A.pinv y)
    rw [← toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
    rfl
  have hUT : U (T (U y)) = U y := by
    change toEuclideanLin A.pinv (toEuclideanLin A (toEuclideanLin A.pinv y)) = _
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]
  have hku : U y ∈ T.kerᗮ := by
    rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint]
    have hq : (LinearMap.range (toEuclideanLin Aᴴ)).starProjection (U y) = U y := by
      have he := DFunLike.congr_fun A.pinv_mul_eq_starProjection (U y)
      change toEuclideanLin (A.pinv * A) (U y) =
        (LinearMap.range (toEuclideanLin Aᴴ)).starProjection (U y) at he
      rw [toEuclideanLin_mul_apply] at he
      exact he.symm.trans hUT
    exact (LinearMap.range (toEuclideanLin Aᴴ)).starProjection_eq_self_iff.mp hq
  have hx : T x = T (U y) := by
    change T ((exists_linearInnerInverse T).choose (P y)) = _
    rw [hp, (exists_linearInnerInverse T).choose_spec]
  have hdiff : x - U y ∈ T.ker := by rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  change x - definition_1 T.ker x = U y
  rw [IsBestApprox.eq_starProjection T.ker (isBestApprox_definition_1 T.ker x)]
  have hzero := T.ker.starProjection_apply_eq_zero_iff.mpr hku
  have hfix := T.ker.starProjection_eq_self_iff.mpr hdiff
  have hproj : T.ker.starProjection x = x - U y := by
    simpa only [map_sub, hzero, sub_zero] using hfix
  rw [hproj, sub_sub_cancel]

end EuclideanSpecialization

section BasicExercises

/-- **Exercise 48** of [benIsrael2003generalized], Chapter 3.
A closest point exists in every nonempty closed subset of a
finite-dimensional normed space. -/
theorem exercise_48 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {S : Set V} (hS : IsClosed S) (hne : S.Nonempty) (x : V) :
    ∃ y, IsBestApprox S x y :=
  exists_isBestApprox_of_isClosed_of_finiteDimensional hS hne (⊤ : Submodule ℂ V) (by simp) x

/-- **Exercise 49** of [benIsrael2003generalized], Chapter 3.
The closest points to `(1,1)` in the ℓ¹ norm on the affine line
`x₁ + x₂ = 1` form the segment joining `(0,1)` and `(1,0)`. -/
theorem exercise_49 (x y : ℝ) (hxy : x + y = 1) :
    (∀ a b : ℝ, a + b = 1 → |1 - x| + |1 - y| ≤ |1 - a| + |1 - b|) ↔
      x ∈ Icc (0 : ℝ) 1 ∧ y = 1 - x := by
  have hlow (a b : ℝ) (h : a + b = 1) : 1 ≤ |1 - a| + |1 - b| := by
    linarith [le_abs_self (1 - a), le_abs_self (1 - b)]
  constructor
  · intro h
    have hval : |1 - x| + |1 - y| = 1 := by
      refine le_antisymm ?_ (hlow _ _ hxy)
      have h' := h 0 1 (by norm_num)
      norm_num at h'
      exact h'
    have hx : x ≤ 1 := by
      by_contra! hn
      rw [abs_of_neg (by linarith : 1 - x < 0)] at hval
      linarith [le_abs_self (1 - y)]
    have hy : y ≤ 1 := by
      by_contra! hn
      rw [abs_of_neg (by linarith : 1 - y < 0)] at hval
      linarith [le_abs_self (1 - x)]
    exact ⟨⟨by linarith, hx⟩, by linarith⟩
  · rintro ⟨hx, rfl⟩ a b hab
    rw [abs_of_nonneg (sub_nonneg.mpr hx.2), abs_of_nonneg (by linarith [hx.1])]
    linarith [hlow _ _ hab]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Exercise 50** of [benIsrael2003generalized], Chapter 3.
The closest point in a convex set is characterized by its variational
inequality using the real part of the inner product. -/
theorem exercise_50 {S : Set V} (hS : Convex ℝ S) {x y : V} (hy : y ∈ S) :
    IsBestApprox S x y ↔ ∀ z ∈ S, 0 ≤ Complex.re (inner ℂ (y - x) (z - y)) := by
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  rw [isBestApprox_iff_inner_le_zero hS hy]
  have he (z : V) : inner ℝ (x - y) (z - y) =
      -Complex.re (inner ℂ (y - x) (z - y)) := by
    change Complex.re (inner ℂ (x - y) (z - y)) = _
    rw [← neg_sub y x, inner_neg_left, Complex.neg_re]
  simp only [he, neg_nonpos]

/-- **Exercise 51** of [benIsrael2003generalized], Chapter 3.
A closed convex set and a point outside it admit a strictly separating
real affine hyperplane. -/
theorem exercise_51 [FiniteDimensional ℂ V] {S : Set V} (hS : Convex ℝ S)
    (hcl : IsClosed S) (hne : S.Nonempty) {x : V} (hx : x ∉ S) :
    ∃ (u : V) (a : ℝ), u ≠ 0 ∧ Complex.re (inner ℂ u x) < a ∧
      ∀ z ∈ S, a ≤ Complex.re (inner ℂ u z) := by
  obtain ⟨y, hy⟩ := exercise_48 hcl hne x
  let u := y - x
  have hu : u ≠ 0 := fun h => hx ((sub_eq_zero.mp h) ▸ hy.1)
  let a := Complex.re (inner ℂ u y)
  refine ⟨u, a, hu, ?_, ?_⟩
  · have he : a - Complex.re (inner ℂ u x) = ‖u‖ ^ 2 := by
      dsimp only [a]
      rw [← Complex.sub_re, ← inner_sub_right]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hu)]
  · intro z hz
    have he := (exercise_50 hS hy.1).mp hy z hz
    rw [inner_sub_right, Complex.sub_re] at he
    exact sub_nonneg.mp he

end BasicExercises

section Gauges

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Exercise 52**, (G1)–(G4), of [benIsrael2003generalized], Chapter 3.
A gauge is continuous, positive away from zero, positively homogeneous,
and subadditive. -/
structure IsPositiveGauge (φ : V → ℝ) : Prop where
  continuous : Continuous φ
  nonnegative : ∀ x, 0 ≤ φ x
  eq_zero : ∀ x, φ x = 0 → x = 0
  homogeneity : ∀ (r : ℝ) (x : V), 0 ≤ r → φ (r • x) = r * φ x
  subadditive : ∀ x y, φ (x + y) ≤ φ x + φ y

/-- A finite-dimensional convex body is convex, closed and bounded, with nonempty interior. -/
structure IsGaugeConvexBody (B : Set V) : Prop where
  convex : Convex ℝ B
  closed : IsClosed B
  bounded : Bornology.IsBounded B
  interior_nonempty : (interior B).Nonempty

/-- **Exercise 53(a)–(c)** of [benIsrael2003generalized], Chapter 3.
The Minkowski functional of a convex body containing the origin in its
interior is a gauge, and identifies the body and its interior by sublevel sets. -/
theorem exercise_53_gauge {B : Set V} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : V) ∈ interior B) :
    IsPositiveGauge (gauge B) ∧
    B = {x | gauge B x ≤ 1} ∧ interior B = {x | gauge B x < 1} := by
  have hN : B ∈ 𝓝 (0 : V) := mem_interior_iff_mem_nhds.mp h₀
  have hAbs : Absorbent ℝ B := absorbent_nhds_zero hN
  refine ⟨⟨continuous_gauge hB.convex hN, fun _ => gauge_nonneg _,
      fun x hx => ?_, fun r x hr => ?_, gauge_add_le hB.convex hAbs⟩, ?_, ?_⟩
  · exact (gauge_eq_zero hAbs (NormedSpace.isVonNBounded_of_isBounded ℝ hB.bounded)).mp hx
  · simpa only [smul_eq_mul] using gauge_smul_of_nonneg (s := B) (x := x) hr
  · ext x
    exact (show x ∈ B ↔ x ∈ closure B by rw [hB.closed.closure_eq]).trans
      (gauge_le_one_iff_mem_closure hB.convex hN).symm
  · exact (setOfPred_gauge_lt_one_eq_interior hB.convex hN).symm

/-- The unit sublevel set of a gauge recovers the gauge as its Minkowski functional. -/
theorem positiveGauge_gauge_eq (φ : V → ℝ) (hφ : IsPositiveGauge φ) :
    gauge {x | φ x ≤ 1} = φ := by
  have hzero : φ 0 = 0 := by
    have hz := hφ.homogeneity 0 (0 : V) le_rfl
    simpa only [zero_smul, zero_mul] using hz
  funext x
  by_cases hx : x = 0
  · rw [hx, gauge_zero, hzero]
  · have hp : 0 < φ x := lt_of_le_of_ne (hφ.nonnegative x)
      (Ne.symm (fun h => hx (hφ.eq_zero x h)))
    have hm : x ∈ φ x • {x | φ x ≤ 1} := by
      refine ⟨(φ x)⁻¹ • x, ?_, smul_inv_smul₀ hp.ne' x⟩
      change φ ((φ x)⁻¹ • x) ≤ 1
      rw [hφ.homogeneity _ _ (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
    refine le_antisymm (gauge_le_of_mem hp.le hm) ?_
    rw [gauge]
    refine le_csInf ⟨_, hp, hm⟩ fun r hr => ?_
    obtain ⟨z, hz, rfl⟩ := hr.2
    change φ z ≤ 1 at hz
    rw [hφ.homogeneity _ _ hr.1.le]
    exact mul_le_of_le_one_right hr.1.le hz

/-- **Exercise 53**, converse, of [benIsrael2003generalized], Chapter 3.
On a finite-dimensional real normed space the unit sublevel set of a
gauge is a convex body containing zero in its interior. -/
theorem exercise_53_converse [FiniteDimensional ℝ V] (φ : V → ℝ) (hφ : IsPositiveGauge φ) :
    let B := {x | φ x ≤ 1}
    IsGaugeConvexBody B ∧ (0 : V) ∈ interior B ∧ gauge B = φ := by
  intro B
  have hzero : φ 0 = 0 := by
    have hz := hφ.homogeneity 0 (0 : V) le_rfl
    simpa only [zero_smul, zero_mul] using hz
  have hN : (0 : V) ∈ interior B := by
    refine mem_interior_iff_mem_nhds.mpr ?_
    apply Filter.mem_of_superset (hφ.continuous.continuousAt.eventually_lt
      continuousAt_const (by simpa only [hzero] using (zero_lt_one : (0 : ℝ) < 1)))
    intro x hx
    change φ x < 1 at hx
    exact hx.le
  refine ⟨⟨?_, isClosed_le hφ.continuous continuous_const, ?_, ⟨0, hN⟩⟩,
    hN, positiveGauge_gauge_eq φ hφ⟩
  · intro x hx y hy a b ha hb hab
    change φ x ≤ 1 at hx
    change φ y ≤ 1 at hy
    change φ (a • x + b • y) ≤ 1
    calc
      _ ≤ φ (a • x) + φ (b • y) := hφ.subadditive _ _
      _ = a * φ x + b * φ y := by rw [hφ.homogeneity _ _ ha, hφ.homogeneity _ _ hb]
      _ ≤ a + b := by
        exact add_le_add (mul_le_of_le_one_right ha hx) (mul_le_of_le_one_right hb hy)
      _ = 1 := hab
  · let : ProperSpace V := FiniteDimensional.proper ℝ V
    by_cases hV : Nontrivial V
    · let : Nontrivial V := hV
      obtain ⟨w, hw⟩ := exists_ne (0 : V)
      have hw₀ : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hS : (Metric.sphere (0 : V) 1).Nonempty := by
        refine ⟨‖w‖⁻¹ • w, ?_⟩
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hw₀]
      obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
        hS hφ.continuous.continuousOn
      have hv₀ : v ≠ 0 := by
        intro he
        rw [he, Metric.mem_sphere, dist_self] at hv
        norm_num at hv
      have hpositive : 0 < φ v := lt_of_le_of_ne (hφ.nonnegative v)
        (Ne.symm fun he => hv₀ (hφ.eq_zero v he))
      apply (Metric.isBounded_closedBall (x := (0 : V)) (r := (φ v)⁻¹)).subset
      intro x hx
      change φ x ≤ 1 at hx
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases hx₀ : x = 0
      · simp [hx₀, hpositive.le]
      · have hn₀ := norm_pos_iff.mpr hx₀
        have hz : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hn₀.le), inv_mul_cancel₀ hn₀.ne']
        have hle := hmin hz
        change φ v ≤ φ (‖x‖⁻¹ • x) at hle
        rw [hφ.homogeneity _ _ (inv_nonneg.mpr hn₀.le)] at hle
        rw [← one_div, le_div_iff₀ hpositive]
        have hm := mul_le_mul_of_nonneg_right hle hn₀.le
        have heq : ‖x‖⁻¹ * φ x * ‖x‖ = φ x := by
          rw [mul_comm (‖x‖⁻¹) (φ x), mul_assoc, inv_mul_cancel₀ hn₀.ne', mul_one]
        rw [heq] at hm
        rw [mul_comm]
        exact hm.trans hx
    · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have he : (B : Set V) ⊆ Metric.closedBall 0 0 := fun x _ => by
        rw [Subsingleton.elim x 0]
        simp
      exact Metric.isBounded_closedBall.subset he

variable [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

/-- **Exercise 54** of [benIsrael2003generalized], Chapter 3.
An equilibrated convex body is exactly one whose gauge is homogeneous
with respect to the modulus of complex scalars. -/
theorem exercise_54 {B : Set V} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : V) ∈ interior B) :
    Balanced ℂ B ↔ ∀ (c : ℂ) (x : V), gauge B (c • x) = ‖c‖ * gauge B x := by
  constructor
  · intro h c x
    exact gauge_smul h c x
  · intro h c hc
    rintro _ ⟨x, hx, rfl⟩
    have hmem (y : V) : y ∈ B ↔ gauge B y ≤ 1 :=
      Set.ext_iff.mp (exercise_53_gauge hB h₀).2.1 y
    apply (hmem _).mpr
    rw [h]
    exact (mul_le_of_le_one_right (norm_nonneg c) ((hmem x).mp hx)).trans hc

end Gauges

section DualPairing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **Equation (132), Exercise 59** of [benIsrael2003generalized], Chapter 3.
The real dual pairing is bounded by the product of the two norms. -/
theorem dualPairing_le_norm_mul (f : StrongDual ℂ V) (x : V) :
    (f x).re ≤ ‖x‖ * ‖f‖ :=
  (Complex.re_le_norm _).trans ((f.le_opNorm x).trans_eq (mul_comm _ _))

/-- A nonzero vector admits a norm-one functional attaining the bound. -/
theorem exercise_59_norming {x : V} (hx : x ≠ 0) :
    ∃ f : StrongDual ℂ V, ‖f‖ = 1 ∧ (f x).re = ‖x‖ * ‖f‖ := by
  obtain ⟨f, hf, hx'⟩ := exists_dual_vector ℂ x (norm_ne_zero_iff.mpr hx)
  refine ⟨f, hf, ?_⟩
  rw [hx', hf, mul_one]
  exact Complex.ofReal_re _

/-- **Exercise 62** of [benIsrael2003generalized], Chapter 3.
A unit dual pair defines supporting hyperplanes for both unit balls. -/
theorem exercise_62 {x : V} {f : StrongDual ℂ V} (hx : ‖x‖ = 1) (hf : ‖f‖ = 1)
    (hpair : (f x).re = 1) :
    (∀ y : V, ‖y‖ ≤ 1 → (f y).re ≤ (f x).re) ∧
    ∀ g : StrongDual ℂ V, ‖g‖ ≤ 1 → (g x).re ≤ (f x).re := by
  constructor
  · intro y hy
    have h := dualPairing_le_norm_mul f y
    simpa only [hf, mul_one, hpair] using h.trans (by simpa only [hf, mul_one] using hy)
  · intro g hg
    have h := dualPairing_le_norm_mul g x
    simpa only [hx, one_mul, hpair] using h.trans (by simpa only [hx, one_mul] using hg)

end DualPairing

section FurtherProjectionResults

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
/-- **Exercise 64(a)** of [benIsrael2003generalized], Chapter 3.
Essential strict convexity is strict convexity of the closed unit ball. -/
theorem exercise_64a :
    essentiallyStrictlyConvex E ↔ StrictConvex ℝ (Metric.closedBall (0 : E) 1) := by
  rw [essentiallyStrictlyConvex_iff E]
  exact ⟨fun h => by
    let : StrictConvexSpace ℝ E := h
    exact strictConvex_closedBall ℝ (0 : E) 1,
    StrictConvexSpace.of_strictConvex_unitClosedBall ℝ⟩

/-- **Exercise 70** of [benIsrael2003generalized], Chapter 3.
If an additive metric projector is contractive, projecting onto its
zero subspace has the original subspace as its own zero fiber. -/
theorem exercise_70 (h : essentiallyStrictlyConvex E) (L N : Submodule ℂ E)
    (hadd : ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y)
    (hcontr : ∀ x, ‖definition_1 L x‖ ≤ ‖x‖)
    (hN : ∀ x, x ∈ N ↔ definition_1 L x = 0) (x : E) :
    x ∈ L ↔ definition_1 N x = 0 := by
  have hL (w : E) (hw : w ∈ L) : definition_1 N w = 0 := by
    apply (definition_1_eq_iff h N w 0).mpr
    refine ⟨N.zero_mem, fun z hz => ?_⟩
    have he : definition_1 L (w - z) = w := by
      rw [sub_eq_add_neg, hadd, (definition_1_eq_self_iff L _).mpr hw, (hN _).mp (N.neg_mem hz),
        add_zero]
    simpa only [sub_zero, he] using hcontr (w - z)
  refine ⟨hL x, ?_⟩
  intro hx
  let l := definition_1 L x
  let z := x - l
  have hz : z ∈ N := (hN _).mpr (definition_1_residual h L x)
  have hl : l ∈ L := definition_1_mem L x
  have he : l + z = x := by dsimp [l, z]; abel
  have hP := definition_1_add_mem h N l hz
  rw [hL l hl, zero_add, he, hx] at hP
  rwa [show x = l from (sub_eq_zero.mp hP.symm)]

/-- **Exercise 72** of [benIsrael2003generalized], Chapter 3.
The two metric projectors add to the identity exactly when each has
the other subspace for its zero fiber. -/
theorem exercise_72 (h : essentiallyStrictlyConvex E) (L N : Submodule ℂ E)
    (hN : ∀ x, x ∈ N ↔ definition_1 L x = 0) :
    (∀ x, x ∈ L ↔ definition_1 N x = 0) ↔
      ∀ x, definition_1 L x + definition_1 N x = x := by
  constructor
  · intro hL x
    let l := definition_1 L x
    let z := x - l
    have hz : z ∈ N := (hN _).mpr (definition_1_residual h L x)
    have hl : l ∈ L := definition_1_mem L x
    have hP := definition_1_add_mem h N l hz
    rw [(hL _).mp hl, zero_add, show l + z = x by dsimp [l, z]; abel] at hP
    change l + definition_1 N x = x
    rw [hP]
    dsimp [z]
    abel
  · intro he x
    rw [← definition_1_eq_self_iff L x]
    constructor
    · intro hx
      have h := he x
      rw [hx] at h
      exact add_left_cancel (h.trans (add_zero x).symm)
    · intro hx
      simpa only [hx, add_zero] using he x

/-- A norm is projective when all its metric projections are contractive. -/
def IsProjectiveNorm : Prop :=
  ∀ (L : Submodule ℂ E) (x : E), ‖definition_1 L x‖ ≤ ‖x‖

/-- **Exercise 71** of [benIsrael2003generalized], Chapter 3.
All metric projections for an essentially strictly convex projective norm
are additive. -/
theorem exercise_71 (h : essentiallyStrictlyConvex E) (hProj : IsProjectiveNorm (E := E))
    (L : Submodule ℂ E) : ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y := by
  have hl (M : Submodule ℂ E) (hM : Module.finrank ℂ M = 1) :
      ∀ x y, definition_1 M (x + y) = definition_1 M x + definition_1 M y := by
    obtain ⟨u, hu, hu₀⟩ := M.ne_bot_iff.mp (by intro he; rw [he, finrank_bot] at hM; omega)
    have hspan : M = ℂ ∙ u := eq_span_singleton_of_mem_of_finrank_eq_one hM hu hu₀
    obtain ⟨f, hf, hfu⟩ := exists_dual_vector ℂ u (norm_ne_zero_iff.mpr hu₀)
    let N := f.toLinearMap.ker
    have hfu' : f u = Complex.ofReal ‖u‖ := hfu
    have hnorm : ‖f u‖ = ‖u‖ := by
      rw [hfu', Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hfu₀ : f u ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact norm_ne_zero_iff.mpr hu₀)
    have hNu : definition_1 N u = 0 := by
      apply (definition_1_eq_iff h N u 0).mpr
      refine ⟨N.zero_mem, fun n hn => ?_⟩
      have hn₀ : f n = 0 := hn
      have h := f.le_opNorm (u - n)
      rw [ContinuousLinearMap.map_sub, hn₀, sub_zero, hnorm] at h
      simpa only [hf, one_mul, sub_zero] using h
    have hker (x : E) : x ∈ M ↔ definition_1 N x = 0 := by
      constructor
      · rw [hspan]
        rintro hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [definition_1_smul h N, hNu, smul_zero]
      · intro hx
        let c := f x / f u
        let n := x - c • u
        have hn : n ∈ N := by
          change f (x - c • u) = 0
          rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu₀, sub_self]
        have e : c • u + n = x := by dsimp [n]; abel
        have he := definition_1_add_mem h N (c • u) hn
        rw [definition_1_smul h N, hNu, smul_zero, zero_add, e, hx] at he
        have h' : x = c • u := (sub_eq_zero.mp (show n = 0 from he.symm))
        rw [h', hspan]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have hAddN := (corollary_5 h N).1.mpr ⟨M, hker⟩
    exact (corollary_5 h M).1.mpr ⟨N, exercise_70 h N M hAddN (hProj N) hker⟩
  by_cases hdim : Module.finrank ℂ L = 0
  · have he : L = ⊥ := Submodule.finrank_eq_zero.mp hdim
    have hz (x : E) : definition_1 L x = 0 := by
      have hx := definition_1_mem L x
      simpa only [he, Submodule.mem_bot] using hx
    intro x y
    rw [hz, hz, hz, add_zero]
  · exact corollary_7 h 1 le_rfl hl L (Nat.one_le_iff_ne_zero.mpr hdim)

end FurtherProjectionResults

end BenIsraelGreville.Chapter03
