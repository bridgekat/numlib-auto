/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Numlib.Analysis.Convex.Subdifferential.Uniqueness
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.Polar
import Mathlib.Analysis.LocallyConvex.Basic
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.NormEquivalence
import NumlibSurface.BenIsraelGreville.Chapter00.Section01
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
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

section DualityExercises

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The unit sphere is the set of vectors of norm one. A nonzero vector
normalizes to a member of it by a positive real rescaling. -/
theorem norm_inv_smul_mem_unitSphere {x : E} (hx : x ≠ 0) :
    ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Complex.norm_real, Real.norm_of_nonneg,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  positivity

/-- **Exercise 59** of [benIsrael2003generalized], Chapter 3. A nonzero
functional on a finite-dimensional normed space has a norm-one vector on
which its value equals its norm as a nonnegative real number. -/
theorem exercise_59_dual_attainment [FiniteDimensional ℂ E]
    {f : StrongDual ℂ E} (hf : f ≠ 0) :
    ∃ x : E, ‖x‖ = 1 ∧ f x = (‖f‖ : ℂ) := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    by_contra! hempty
    apply hf
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hmem := norm_inv_smul_mem_unitSphere hx
      rw [hempty] at hmem
      exact hmem.elim
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    f.continuous.norm.continuousOn
  have hu₁ : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
  have hn : ‖f u‖ = ‖f‖ := by
    refine le_antisymm (by simpa only [hu₁, mul_one] using f.le_opNorm u)
      (f.opNorm_le_bound (norm_nonneg _) fun x => ?_)
    by_cases hx : x = 0
    · simp [hx]
    have he := hmax (norm_inv_smul_mem_unitSphere hx)
    change ‖f (((‖x‖⁻¹ : ℝ) : ℂ) • x)‖ ≤ ‖f u‖ at he
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at he
    exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp (by simpa only [div_eq_mul_inv, mul_comm] using he)
  obtain ⟨c, hc, he⟩ := RCLike.exists_norm_eq_mul_self (f u)
  refine ⟨c • u, by simp [norm_smul, hc, hu₁], ?_⟩
  rw [map_smul, smul_eq_mul, ← he, hn]
  rfl

/-- Pullback on the continuous dual is the adjoint corresponding to
the dual pairing of the two normed spaces. -/
noncomputable def mixedNormDualAdjoint (A : E →L[ℂ] F) :
    StrongDual ℂ F →L[ℂ] StrongDual ℂ E :=
  (ContinuousLinearMap.compL ℂ E F ℂ).flip A

/-- The adjoint acts on a functional by precomposition with the original map. -/
@[simp]
theorem mixedNormDualAdjoint_apply (A : E →L[ℂ] F) (f : StrongDual ℂ F) :
    mixedNormDualAdjoint A f = f.comp A := rfl

/-- **Exercise 67, Equation (144)** of [benIsrael2003generalized], Chapter 3.
The operator norm of a linear transformation agrees with that of its
adjoint, with the domain and codomain carrying the exchanged dual norms. -/
theorem exercise_67 (A : E →L[ℂ] F) : ‖A‖ = ‖mixedNormDualAdjoint A‖ := by
  refine le_antisymm (A.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_)
    ((mixedNormDualAdjoint A).opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _) fun f => ?_)
  · obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' ℂ (A x)
    have he : ‖(mixedNormDualAdjoint A f) x‖ = ‖A x‖ := by
      change ‖f (A x)‖ = ‖A x‖
      rw [hfx]
      change ‖(‖A x‖ : ℂ)‖ = ‖A x‖
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖A x‖ = ‖(mixedNormDualAdjoint A f) x‖ := he.symm
      _ ≤ ‖mixedNormDualAdjoint A f‖ * ‖x‖ := (mixedNormDualAdjoint A f).le_opNorm x
      _ ≤ (‖mixedNormDualAdjoint A‖ * ‖f‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((mixedNormDualAdjoint A).le_opNorm f) (norm_nonneg _)
      _ ≤ ‖mixedNormDualAdjoint A‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _) hf) (norm_nonneg _)
  · rw [mixedNormDualAdjoint_apply, mul_comm]
    exact f.opNorm_comp_le A

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- **Exercise 75** of [benIsrael2003generalized], Chapter 3.
A nonzero vector lies in the zero fiber of the metric projection exactly
when a norm-one functional norms it and annihilates the subspace. -/
theorem exercise_75 (h : essentiallyStrictlyConvex E) (L : Submodule ℂ E)
    {x : E} (hx : x ≠ 0) :
    definition_1 L x = 0 ↔
      ∃ f : StrongDual ℂ E, ‖f‖ = 1 ∧ f x = (‖x‖ : ℂ) ∧ ∀ z ∈ L, f z = 0 := by
  constructor
  · intro hzero
    let : IsClosed (L : Set E) := L.closed_of_finiteDimensional
    have hbest : IsBestApprox (L : Set E) x 0 :=
      (definition_1_eq_iff h L x 0).mp hzero
    have hquot : ‖L.mkQL x‖ = ‖x‖ := by
      change ‖(QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup)‖ = _
      rw [QuotientAddGroup.norm_mk]
      change Metric.infDist x (L : Set E) = ‖x‖
      simpa only [sub_zero] using hbest.norm_sub_eq_infDist.symm
    obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℂ (L.mkQL x) (by
      rw [hquot]; exact norm_ne_zero_iff.mpr hx)
    let f : StrongDual ℂ E := g.comp L.mkQL
    have hfx : f x = (‖x‖ : ℂ) := by
      change g (L.mkQL x) = _
      rw [hgx, hquot]
      rfl
    have hfle : ‖f‖ ≤ 1 := by
      apply f.opNorm_le_bound zero_le_one
      intro z
      change ‖g (L.mkQL z)‖ ≤ 1 * ‖z‖
      rw [one_mul]
      exact (by simpa only [hg, one_mul] using g.le_opNorm (L.mkQL z) :
        ‖g (L.mkQL z)‖ ≤ ‖L.mkQL z‖).trans (Submodule.Quotient.norm_mk_le L z)
    have hfge : 1 ≤ ‖f‖ := by
      have he := f.le_opNorm x
      rw [hfx, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at he
      exact le_of_mul_le_mul_right (by simpa only [one_mul] using he) (norm_pos_iff.mpr hx)
    refine ⟨f, le_antisymm hfle hfge, hfx, fun z hz => ?_⟩
    change g (L.mkQL z) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero L).mpr hz, map_zero]
  · rintro ⟨f, hf, hfx, hL⟩
    apply (definition_1_eq_iff h L x 0).mpr
    refine ⟨L.zero_mem, fun z hz => ?_⟩
    have hval := f.le_opNorm (x - z)
    rw [map_sub, hL z hz, sub_zero, hfx, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), hf, one_mul] at hval
    simpa only [sub_zero] using hval

end DualityExercises

section MixedNormExercises

open Set
open scoped Pointwise

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Continuity and complex homogeneity of a transformation in Exercise 66. -/
structure IsContinuousHomogeneous (f : E → F) : Prop where
  continuous : Continuous f
  smul : ∀ (c : ℂ) (x : E), f (c • x) = c • f x

/-- **Equation (143)** of [benIsrael2003generalized], Chapter 3.
The mixed operator norm is the supremum of output norms on the input
unit sphere, with value zero for the zero space. -/
noncomputable def mixedOperatorNorm (f : E → F) : ℝ :=
  sSup ((fun x => ‖f x‖) '' Metric.sphere (0 : E) 1)

private theorem IsContinuousHomogeneous.map_zero {f : E → F}
    (hf : IsContinuousHomogeneous f) : f 0 = 0 := by
  simpa only [zero_smul] using hf.smul 0 (0 : E)

omit [NormedSpace ℂ F] in
private theorem mixedNorm_bddAbove [FiniteDimensional ℂ E] {f : E → F} (hf : Continuous f) :
    BddAbove ((fun x => ‖f x‖) '' Metric.sphere (0 : E) 1) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  exact (isCompact_sphere _ _).bddAbove_image hf.norm.continuousOn

/-- **Exercise 66, Equation (143)** of [benIsrael2003generalized].
The ratio of output to input norm has the same supremum as on the unit
sphere. In nonzero finite dimension the latter supremum is a maximum. -/
theorem exercise_66 [FiniteDimensional ℂ E] (f : E → F) (hf : IsContinuousHomogeneous f) :
    mixedOperatorNorm f = sSup ((fun x => ‖f x‖ / ‖x‖) '' {x : E | x ≠ 0}) ∧
      (Nontrivial E → ∃ x : E, ‖x‖ = 1 ∧ ‖f x‖ = mixedOperatorNorm f) := by
  constructor
  · unfold mixedOperatorNorm
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx₁ : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
      exact ⟨x, fun hz => by simp [hz] at hx₁, by simp [hx₁]⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, norm_inv_smul_mem_unitSphere hx, ?_⟩
      change ‖f (((‖x‖⁻¹ : ℝ) : ℂ) • x)‖ = ‖f x‖ / ‖x‖
      rw [hf.smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        div_eq_mul_inv, mul_comm]
  · intro hE
    let : Nontrivial E := hE
    let : ProperSpace E := FiniteDimensional.proper ℂ E
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨_, norm_inv_smul_mem_unitSphere hw⟩
    obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
      hf.continuous.norm.continuousOn
    refine ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx, ?_⟩
    have hg : IsGreatest ((fun x => ‖f x‖) '' Metric.sphere (0 : E) 1) ‖f x‖ :=
      ⟨⟨x, hx, rfl⟩, fun y ⟨u, hu, hy⟩ => hy ▸ hmax hu⟩
    exact hg.csSup_eq.symm

omit [NormedSpace ℂ F] in
/-- The mixed norm is nonnegative, including for a zero input space. -/
theorem mixedOperatorNorm_nonneg [FiniteDimensional ℂ E] {f : E → F} (hf : Continuous f) :
    0 ≤ mixedOperatorNorm f := by
  by_cases h : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨x, hx⟩ := h
    exact (norm_nonneg (f x)).trans (le_csSup (mixedNorm_bddAbove hf) ⟨x, hx, rfl⟩)
  · simp [mixedOperatorNorm, Set.not_nonempty_iff_eq_empty.mp h]

/-- The mixed norm is the least nonnegative constant in the pointwise norm bound. -/
theorem mixedOperatorNorm_le_iff [FiniteDimensional ℂ E] {f : E → F}
    (hf : IsContinuousHomogeneous f) {a : ℝ} (ha : 0 ≤ a) :
    mixedOperatorNorm f ≤ a ↔ ∀ x, ‖f x‖ ≤ a * ‖x‖ := by
  constructor
  · intro h x
    by_cases hx : x = 0
    · simp [hx, hf.map_zero]
    have he := (le_csSup (mixedNorm_bddAbove hf.continuous) (show
      ‖f (((‖x‖⁻¹ : ℝ) : ℂ) • x)‖ ∈
        (fun x => ‖f x‖) '' Metric.sphere (0 : E) 1 from
        ⟨_, norm_inv_smul_mem_unitSphere hx, rfl⟩)).trans h
    rw [hf.smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at he
    exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp
      (by simpa only [div_eq_mul_inv, mul_comm] using he)
  · intro h
    by_cases hs : (Metric.sphere (0 : E) 1).Nonempty
    · apply csSup_le (hs.image _)
      rintro _ ⟨x, hx, rfl⟩
      have hx₁ : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
      simpa only [hx₁, mul_one] using h x
    · simpa only [mixedOperatorNorm, Set.not_nonempty_iff_eq_empty.mp hs,
        Set.image_empty, Real.sSup_empty] using ha

/-- Every output norm is bounded by the mixed norm times the input norm. -/
theorem norm_homogeneous_apply_le [FiniteDimensional ℂ E] {f : E → F}
    (hf : IsContinuousHomogeneous f) (x : E) : ‖f x‖ ≤ mixedOperatorNorm f * ‖x‖ :=
  (mixedOperatorNorm_le_iff hf (mixedOperatorNorm_nonneg hf.continuous)).mp le_rfl x

/-- **Exercise 66(a)**. The mixed norm vanishes exactly for the zero map. -/
theorem mixedOperatorNorm_eq_zero_iff [FiniteDimensional ℂ E] {f : E → F}
    (hf : IsContinuousHomogeneous f) : mixedOperatorNorm f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext x
    exact norm_eq_zero.mp (le_antisymm (by simpa [h] using norm_homogeneous_apply_le hf x)
      (norm_nonneg _))
  · intro h
    refine le_antisymm ((mixedOperatorNorm_le_iff hf le_rfl).mpr fun x => ?_)
      (mixedOperatorNorm_nonneg hf.continuous)
    simp [h]

/-- **Exercise 66(b)**. Scaling a homogeneous map scales its mixed norm
by the modulus of the scalar. -/
theorem mixedOperatorNorm_smul [FiniteDimensional ℂ E] {f : E → F}
    (hf : IsContinuousHomogeneous f) (a : ℂ) :
    mixedOperatorNorm (fun x => a • f x) = ‖a‖ * mixedOperatorNorm f := by
  let g := fun x => a • f x
  have hg : IsContinuousHomogeneous g :=
    ⟨continuous_const.smul hf.continuous, fun c x => by
      change a • f (c • x) = c • a • f x
      rw [hf.smul, smul_comm a]⟩
  refine le_antisymm ((mixedOperatorNorm_le_iff hg (mul_nonneg (norm_nonneg _)
    (mixedOperatorNorm_nonneg hf.continuous))).mpr fun x => ?_) ?_
  · change ‖a • f x‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_homogeneous_apply_le hf x) (norm_nonneg _)
  · by_cases ha : a = 0
    · change ‖a‖ * mixedOperatorNorm f ≤ mixedOperatorNorm g
      rw [ha, norm_zero, zero_mul]
      exact mixedOperatorNorm_nonneg hg.continuous
    have ha₀ : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have h := (mixedOperatorNorm_le_iff hf (div_nonneg
      (mixedOperatorNorm_nonneg hg.continuous) ha₀.le)).mpr fun x => ?_
    · exact (le_div_iff₀' ha₀).mp h
    · have hx := norm_homogeneous_apply_le hg x
      change ‖a • f x‖ ≤ _ at hx
      rw [norm_smul] at hx
      rw [div_mul_eq_mul_div, le_div_iff₀' ha₀]
      exact hx

/-- **Exercise 66(c)**. The mixed norm satisfies the triangle inequality. -/
theorem mixedOperatorNorm_add_le [FiniteDimensional ℂ E] {f g : E → F}
    (hf : IsContinuousHomogeneous f) (hg : IsContinuousHomogeneous g) :
    mixedOperatorNorm (fun x => f x + g x) ≤ mixedOperatorNorm f + mixedOperatorNorm g := by
  have hfg : IsContinuousHomogeneous (fun x => f x + g x) :=
    ⟨hf.continuous.add hg.continuous, fun c x => by simp only [hf.smul, hg.smul, smul_add]⟩
  apply (mixedOperatorNorm_le_iff hfg (add_nonneg (mixedOperatorNorm_nonneg hf.continuous)
    (mixedOperatorNorm_nonneg hg.continuous))).mpr
  intro x
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_homogeneous_apply_le hf x)
    (norm_homogeneous_apply_le hg x))

/-- **Exercise 66(d)**. The mixed norm is the infimum of the positive
dilation factors that contain the image of the input unit ball. -/
theorem mixedOperatorNorm_eq_sInf_unitBall [FiniteDimensional ℂ E] {f : E → F}
    (hf : IsContinuousHomogeneous f) :
    mixedOperatorNorm f = sInf {a : ℝ | 0 < a ∧
      f '' Metric.closedBall (0 : E) 1 ⊆ (a : ℂ) • Metric.closedBall (0 : F) 1} := by
  let S := {a : ℝ | 0 < a ∧
    f '' Metric.closedBall (0 : E) 1 ⊆ (a : ℂ) • Metric.closedBall (0 : F) 1}
  have hN := mixedOperatorNorm_nonneg hf.continuous
  have hmem (a : ℝ) (ha : 0 < a) : a ∈ S ↔ mixedOperatorNorm f ≤ a := by
    constructor
    · intro h
      apply (mixedOperatorNorm_le_iff hf ha.le).mpr
      intro x
      by_cases hx : x = 0
      · simp [hx, hf.map_zero]
      let u := ((‖x‖⁻¹ : ℝ) : ℂ) • x
      have hu : u ∈ Metric.closedBall (0 : E) 1 :=
        Metric.sphere_subset_closedBall (norm_inv_smul_mem_unitSphere hx)
      obtain ⟨v, hv, hvf⟩ := h.2 ⟨u, hu, rfl⟩
      have hv₁ : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
      have he : ‖f u‖ ≤ a := by
        rw [← hvf, norm_smul, Complex.norm_real, Real.norm_of_nonneg ha.le]
        exact mul_le_of_le_one_right ha.le hv₁
      change ‖f (((‖x‖⁻¹ : ℝ) : ℂ) • x)‖ ≤ a at he
      rw [hf.smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at he
      exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp
        (by simpa only [div_eq_mul_inv, mul_comm] using he)
    · intro h
      refine ⟨ha, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hx₁ : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      have hab := ((mixedOperatorNorm_le_iff hf ha.le).mp h x).trans
        (mul_le_of_le_one_right ha.le hx₁)
      refine ⟨((a⁻¹ : ℝ) : ℂ) • f x, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
        rw [mul_comm, ← div_eq_mul_inv]
        exact (div_le_iff₀ ha).mpr (by simpa only [one_mul] using hab)
      · change (a : ℂ) • ((a⁻¹ : ℝ) : ℂ) • f x = f x
        rw [Complex.ofReal_inv, smul_inv_smul₀ ((Complex.ofReal_ne_zero).mpr ha.ne')]
  have hpos : 0 < mixedOperatorNorm f + 1 := by linarith
  have hne : S.Nonempty := ⟨_, (hmem _ hpos).mpr (by linarith)⟩
  refine le_antisymm (le_csInf hne fun a ha => (hmem a ha.1).mp ha) ?_
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε' : 0 < mixedOperatorNorm f + ε := by linarith
  exact csInf_le ⟨mixedOperatorNorm f, fun a ha => (hmem a ha.1).mp ha⟩
    ((hmem _ hε').mpr (by linarith))

/-- **Exercise 66(e)**. Composition is submultiplicative with the
appropriate input, intermediate, and output norms. -/
theorem mixedOperatorNorm_comp_le [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {f : E → F} {g : F → G} (hf : IsContinuousHomogeneous f) (hg : IsContinuousHomogeneous g) :
    mixedOperatorNorm (g ∘ f) ≤ mixedOperatorNorm f * mixedOperatorNorm g := by
  have hgf : IsContinuousHomogeneous (g ∘ f) :=
    ⟨hg.continuous.comp hf.continuous, fun c x => by
      simp only [Function.comp_apply, hf.smul, hg.smul]⟩
  apply (mixedOperatorNorm_le_iff hgf (mul_nonneg (mixedOperatorNorm_nonneg hf.continuous)
    (mixedOperatorNorm_nonneg hg.continuous))).mpr
  intro x
  calc
    ‖(g ∘ f) x‖ ≤ mixedOperatorNorm g * ‖f x‖ := norm_homogeneous_apply_le hg (f x)
    _ ≤ mixedOperatorNorm g * (mixedOperatorNorm f * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_homogeneous_apply_le hf x)
        (mixedOperatorNorm_nonneg hg.continuous)
    _ = _ := by ring

/-- **Exercise 66(f)**. For a linear map the mixed norm is the usual
induced operator norm for the given domain and codomain norms. -/
theorem mixedOperatorNorm_eq_opNorm [FiniteDimensional ℂ E] (f : E →L[ℂ] F) :
    mixedOperatorNorm f = ‖f‖ := by
  have hf : IsContinuousHomogeneous f := ⟨f.continuous, fun c x => map_smul f c x⟩
  exact le_antisymm ((mixedOperatorNorm_le_iff hf f.opNorm_nonneg).mpr f.le_opNorm)
    (f.opNorm_le_bound (mixedOperatorNorm_nonneg f.continuous) (norm_homogeneous_apply_le hf))

end MixedNormExercises

section LpDualExercises

open Set
open scoped ENNReal
open BenIsraelGreville.Chapter00 (lpNorm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The continuous dual norm is the supremum of the real-pairing ratios
over nonzero vectors. Phasing a vector replaces the real part of its
pairing by its modulus. -/
theorem dualNorm_eq_sSup_real_pairing (f : StrongDual ℂ E) :
    ‖f‖ = sSup ((fun x => (f x).re / ‖x‖) '' {x : E | x ≠ 0}) := by
  let S := (fun x => (f x).re / ‖x‖) '' {x : E | x ≠ 0}
  change ‖f‖ = sSup S
  by_cases hE : ∃ x : E, x ≠ 0
  · have hphase (x : E) (hx : x ≠ 0) : ‖f x‖ / ‖x‖ ∈ S := by
      obtain ⟨c, hc, he⟩ := RCLike.exists_norm_eq_mul_self (f x)
      have hc₀ : c ≠ 0 := by intro h; simp [h] at hc
      refine ⟨c • x, smul_ne_zero hc₀ hx, ?_⟩
      change (f (c • x)).re / ‖c • x‖ = _
      rw [map_smul, smul_eq_mul, ← he, norm_smul, hc, one_mul]
      rfl
    have hbound : ‖f‖ ∈ upperBounds S := by
      rintro _ ⟨x, hx, rfl⟩
      exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
        ((Complex.re_le_norm _).trans (f.le_opNorm x))
    have hbdd : BddAbove S := ⟨_, hbound⟩
    obtain ⟨u, hu⟩ := hE
    have hn : 0 ≤ sSup S :=
      (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans (le_csSup hbdd (hphase u hu))
    refine le_antisymm (f.opNorm_le_bound hn fun x => ?_) (csSup_le ⟨_, hphase u hu⟩ hbound)
    by_cases hx : x = 0
    · simp [hx]
    exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mp (le_csSup hbdd (hphase x hx))
  · have hz (x : E) : x = 0 := by by_contra hx; exact hE ⟨x, hx⟩
    have hf : f = 0 := ContinuousLinearMap.ext fun x => by simp [hz x]
    have hS : S = ∅ := by
      ext y
      constructor
      · rintro ⟨x, hx, _⟩
        exact (hx (hz x)).elim
      · simp
    rw [hf, norm_zero, hS, Real.sSup_empty]

/-- The finite-coordinate norm of Chapter 0 agrees with the sequence-space
norm on the same entries, including the maximum norm at exponent infinity. -/
theorem lpNorm_eq_norm_finite_lp {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [hp : Fact (1 ≤ p)]
    (x : lp (fun _ : ι => ℂ) p) : lpNorm p (fun i => x i) = ‖x‖ := by
  by_cases h : p = ∞
  · subst p
    rw [lpNorm, ite_eq_left rfl, lp.norm_eq_ciSup]
  · rw [lpNorm, ite_eq_right h, lp.norm_eq_tsum_rpow
      (ENNReal.toReal_pos (zero_lt_one.trans_le hp.out).ne' h), tsum_fintype]

/-- **Exercise 58** of [benIsrael2003generalized], Chapter 3.
With the complex Hermitian pairing, the dual of a finite-coordinate
$ell^p$ norm is the $ell^q$ norm for any conjugate exponents.
The same statement includes $p=1$, $q=infty$, and their reverse. -/
theorem exercise_58 {ι : Type*} [Fintype ι] (p q : ℝ≥0∞) [hpq : p.HolderConjugate q]
    (y : ι → ℂ) :
    lpNorm q y = sSup ((fun x : ι → ℂ => (∑ i, star (y i) * x i).re / lpNorm p x) ''
      {x : ι → ℂ | x ≠ 0}) := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let u : lp (fun _ : ι => ℂ) q := ⟨y, Memℓp.all y⟩
  let f := lp.toDualCLM ℂ ι p q (star u)
  have hf : ‖f‖ = lpNorm q y := by
    rw [show f = lp.toDualCLM ℂ ι p q (star u) from rfl, lp.norm_toDualCLM_apply, norm_star]
    exact (lpNorm_eq_norm_finite_lp q u).symm
  rw [← hf, dualNorm_eq_sSup_real_pairing]
  congr 1
  have hpair (x : lp (fun _ : ι => ℂ) p) :
      f x = ∑ i, star (y i) * x i := by
    rw [show f = lp.toDualCLM ℂ ι p q (star u) from rfl,
      lp.toDualCLM_apply, tsum_fintype]
    rfl
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun i => x i, ?_, ?_⟩
    · intro h
      apply hx
      ext i
      exact congrFun h i
    · change (∑ i, star (y i) * x i).re / lpNorm p (fun i => x i) =
        (f x).re / ‖x‖
      rw [hpair x, lpNorm_eq_norm_finite_lp p x]
  · rintro ⟨x, hx, rfl⟩
    let v : lp (fun _ : ι => ℂ) p := ⟨x, Memℓp.all x⟩
    refine ⟨v, ?_, ?_⟩
    · intro h
      apply hx
      funext i
      exact congrArg (fun w : lp (fun _ : ι => ℂ) p => w i) h
    · change (f v).re / ‖v‖ = (∑ i, star (y i) * x i).re / lpNorm p x
      rw [hpair v, ← lpNorm_eq_norm_finite_lp p v]

end LpDualExercises

section DualProjectionExercises

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- An additive metric projection in an essentially strictly convex norm
as a continuous complex-linear projection. -/
noncomputable def additiveMetricProjection (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E)
    (hadd : ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y) :
    E →L[ℂ] E where
  toLinearMap :=
    { toFun := definition_1 L
      map_add' := hadd
      map_smul' := definition_1_smul h L }
  cont := continuous_definition_1 h L

/-- The continuous linear projection still takes the unique closest point. -/
@[simp]
theorem additiveMetricProjection_apply (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) (hadd : ∀ x y, definition_1 L (x + y) =
      definition_1 L x + definition_1 L y) (x : E) :
    additiveMetricProjection h L hadd x = definition_1 L x := rfl

/-- **Exercise 76** of [benIsrael2003generalized], Chapter 3.
If the primal and dual norms are essentially strictly convex, the
adjoint of an additive metric projection is the metric projection onto
the annihilator of its zero subspace. Its own zero subspace is the
annihilator of the original range. -/
theorem exercise_76 (h : essentiallyStrictlyConvex E)
    (hD : essentiallyStrictlyConvex (StrongDual ℂ E)) (L : Submodule ℂ E)
    (hadd : ∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y) :
    let P := additiveMetricProjection h L hadd
    let N := P.ker
    (∀ f : StrongDual ℂ E, f ∈ L.strongDualAnnihilator ↔
      definition_1 N.strongDualAnnihilator f = 0) ∧
    ∀ f : StrongDual ℂ E, definition_1 N.strongDualAnnihilator f = mixedNormDualAdjoint P f := by
  intro P N
  let : FiniteDimensional ℂ (StrongDual ℂ E) :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E).finiteDimensional
  have hPme (x : E) : P x ∈ L := definition_1_mem L x
  have hPfix {x : E} (hx : x ∈ L) : P x = x :=
    (definition_1_eq_self_iff L x).mpr hx
  have hproj (f : StrongDual ℂ E) :
      definition_1 N.strongDualAnnihilator f = mixedNormDualAdjoint P f := by
    let g := mixedNormDualAdjoint P f
    let d := f - g
    have hg : g ∈ N.strongDualAnnihilator := by
      rw [Submodule.mem_strongDualAnnihilator]
      intro x hx
      change f (P x) = 0
      rw [show P x = 0 from hx, map_zero]
    apply (definition_1_eq_iff hD N.strongDualAnnihilator f g).mpr
    refine ⟨hg, fun z hz => ?_⟩
    change ‖d‖ ≤ ‖f - z‖
    by_cases hd : d = 0
    · simp [hd]
    obtain ⟨x, hn, hdx⟩ := exercise_59_dual_attainment hd
    have hx₀ : x ≠ 0 := by intro he; simp [he] at hn
    have hn₀ : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    let e : StrongDual ℂ E := ((‖d‖⁻¹ : ℝ) : ℂ) • d
    have he₁ : ‖e‖ = 1 := by
      change ‖((‖d‖⁻¹ : ℝ) : ℂ) • d‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn₀]
    have hex : e x = (‖x‖ : ℂ) := by
      change ((‖d‖⁻¹ : ℝ) : ℂ) * d x = (‖x‖ : ℂ)
      rw [hdx, ← Complex.ofReal_mul, inv_mul_cancel₀ hn₀, hn]
    have heL (y : E) (hy : y ∈ L) : e y = 0 := by
      change ((‖d‖⁻¹ : ℝ) : ℂ) * (f y - f (P y)) = 0
      rw [hPfix hy, sub_self, mul_zero]
    have hxN : x ∈ N := (exercise_75 h L hx₀).mpr ⟨e, he₁, hex, heL⟩
    have hzx : z x = 0 := (Submodule.mem_strongDualAnnihilator.mp hz) x hxN
    have hval : (f - z) x = d x := by
      change f x - z x = f x - f (P x)
      rw [hzx, show P x = 0 from hxN, map_zero]
    have hb := (f - z).le_opNorm x
    rw [hval, hdx, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), hn, mul_one] at hb
    exact hb
  refine ⟨fun f => ?_, hproj⟩
  rw [hproj f, Submodule.mem_strongDualAnnihilator]
  constructor
  · intro hf
    ext x
    exact hf _ (hPme x)
  · intro hf x hx
    have he := congrArg (fun g : StrongDual ℂ E => g x) hf
    change f (P x) = 0 at he
    rwa [hPfix hx] at he

end DualProjectionExercises

section NormBodiesExercises

open Set
open scoped Pointwise
open BenIsraelGreville.Chapter00 (IsVectorNorm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- The origin is interior to a balanced convex body. -/
theorem balancedGaugeConvexBody_zero_mem_interior {B : Set E}
    (hB : IsGaugeConvexBody B) (hbal : Balanced ℂ B) : (0 : E) ∈ interior B := by
  obtain ⟨x, hx⟩ := hB.interior_nonempty
  by_cases hx₀ : x = 0
  · rwa [hx₀] at hx
  have hneg : -x ∈ insert 0 (interior B) := by
    simpa only [neg_one_smul] using hbal.zero_insert_interior (-1 : ℂ)
      (show ‖(-1 : ℂ)‖ ≤ 1 by simp)
      (show (-1 : ℂ) • x ∈ (-1 : ℂ) • insert 0 (interior B) from
        ⟨x, Set.mem_insert_of_mem _ hx, rfl⟩)
  have hy : -x ∈ interior B :=
    (Set.mem_insert_iff.mp hneg).resolve_left (neg_ne_zero.mpr hx₀)
  have hmid := hB.convex.interior hx hy (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [smul_neg, add_neg_cancel] using hmid

variable [FiniteDimensional ℂ E] [IsScalarTower ℝ ℂ E]

/-- A vector norm in finite dimension is precisely an absolutely
homogeneous positive gauge. -/
theorem isVectorNorm_iff_positiveGauge_absoluteHomogeneity (φ : E → ℝ) :
    IsVectorNorm φ ↔ IsPositiveGauge φ ∧ ∀ (c : ℂ) (x : E), φ (c • x) = ‖c‖ * φ x := by
  constructor
  · intro h
    let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
    let p : Seminorm ℂ E := Seminorm.of φ h.triangle h.smul
    have hcont : Continuous φ := (p.restrictScalars ℝ).continuous_of_finiteDimensional
    refine ⟨⟨hcont, h.nonneg, fun x hx => (h.eq_zero_iff x).mp hx, ?_, h.triangle⟩, h.smul⟩
    intro r x hr
    rw [← IsScalarTower.algebraMap_smul ℂ r x]
    change φ ((r : ℂ) • x) = r * φ x
    rw [h.smul, Complex.norm_real, Real.norm_of_nonneg hr]
  · rintro ⟨h, hh⟩
    refine ⟨h.nonnegative, fun x => ⟨h.eq_zero x, ?_⟩, hh, h.subadditive⟩
    rintro rfl
    simpa only [zero_smul, norm_zero, zero_mul] using hh (0 : ℂ) (0 : E)

/-- **Exercise 55** of [benIsrael2003generalized], Chapter 3.
Vector norms correspond bijectively to balanced convex bodies, by the
unit sublevel set in one direction and the Minkowski gauge in the other. -/
noncomputable def exercise_55 :
    {φ : E → ℝ // IsVectorNorm φ} ≃
      {B : Set E // IsGaugeConvexBody B ∧ Balanced ℂ B} where
  toFun φ := by
    let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
    have h := (isVectorNorm_iff_positiveGauge_absoluteHomogeneity φ.val).mp φ.property
    refine ⟨{x | φ.val x ≤ 1}, (exercise_53_converse φ.val h.1).1, ?_⟩
    intro c hc
    rintro _ ⟨x, hx, rfl⟩
    change φ.val (c • x) ≤ 1
    rw [φ.property.smul]
    exact (mul_le_of_le_one_right (norm_nonneg c) hx).trans hc
  invFun B := by
    have h₀ := balancedGaugeConvexBody_zero_mem_interior B.property.1 B.property.2
    exact ⟨gauge B.val, (isVectorNorm_iff_positiveGauge_absoluteHomogeneity _).mpr
      ⟨(exercise_53_gauge B.property.1 h₀).1, (exercise_54 B.property.1 h₀).mp B.property.2⟩⟩
  left_inv φ := by
    apply Subtype.ext
    exact positiveGauge_gauge_eq _
      ((isVectorNorm_iff_positiveGauge_absoluteHomogeneity _).mp φ.property).1
  right_inv B := by
    apply Subtype.ext
    exact (exercise_53_gauge B.property.1
      (balancedGaugeConvexBody_zero_mem_interior B.property.1 B.property.2)).2.1.symm

end NormBodiesExercises

section PolarGaugeExercises

open Set ConvexAnalysis
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The polar defined by the real part of the complex Hermitian pairing, Equation (138). -/
def hermitianPolar (B : Set E) : Set E := {y | ∀ x ∈ B, (inner ℂ y x).re ≤ 1}

private theorem hermitianPolar_eq_polarSet (B : Set E) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    hermitianPolar B = polarSet (innerₗ E) B := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  ext y
  change (∀ x ∈ B, (inner ℝ y x) ≤ 1) ↔ ∀ x ∈ B, (innerₗ E) x y ≤ 1
  simp only [innerₗ_apply_apply]
  exact forall_congr' fun x => by rw [real_inner_comm y x]

/-- Equilibrated bodies have equilibrated polars. -/
theorem hermitianPolar_balanced {B : Set E} (hB : Balanced ℂ B) :
    Balanced ℂ (hermitianPolar B) := by
  intro c hc
  rintro _ ⟨y, hy, rfl⟩
  intro x hx
  have hcx := hB.smul_mem (by simpa only [norm_star] using hc : ‖star c‖ ≤ 1) hx
  have he := hy (star c • x) hcx
  change (inner ℂ (c • y) x).re ≤ 1
  simpa only [inner_smul_right, inner_smul_left, starRingEnd_apply] using he

/-- For every bounded set with zero in its interior, the polar is a convex
body containing the origin in its interior. -/
theorem hermitianPolar_isGaugeConvexBody {B : Set E} (hb : Bornology.IsBounded B)
    (h₀ : (0 : E) ∈ interior B) :
    IsGaugeConvexBody (hermitianPolar B) ∧ (0 : E) ∈ interior (hermitianPolar B) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h₀)
  obtain ⟨R, hR, hupper⟩ := hb.exists_pos_norm_le
  have hP₀ : (0 : E) ∈ interior (hermitianPolar B) := by
    refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨R⁻¹, inv_pos.mpr hR, ?_⟩)
    intro y hy x hx
    have hy' : ‖y‖ < R⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    calc
      _ ≤ ‖y‖ * ‖x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖y‖ * R := mul_le_mul_of_nonneg_left (hupper _ hx) (norm_nonneg _)
      _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_right hy'.le hR.le
      _ = 1 := inv_mul_cancel₀ hR.ne'
  refine ⟨⟨?_, ?_, ?_, ⟨0, hP₀⟩⟩, hP₀⟩
  · rw [hermitianPolar_eq_polarSet]
    exact convex_polarSet _ _
  · rw [hermitianPolar_eq_polarSet]
    exact isClosed_polarSet
  · refine isBounded_iff_forall_norm_le.mpr ⟨(r / 2)⁻¹, ?_⟩
    intro y hy
    by_cases hy₀ : y = 0
    · simpa [hy₀] using inv_nonneg.mpr (half_pos hr).le
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy₀
    let t : ℝ := (r / 2) / ‖y‖
    have ht : 0 < t := div_pos (half_pos hr) hny
    have hty : t * ‖y‖ = r / 2 := div_mul_cancel₀ _ hny.ne'
    have hmem : t • y ∈ B := by
      apply hrB
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hty]
      exact half_lt_self hr
    have hyb := hy (t • y) hmem
    change inner ℝ y (t • y) ≤ 1 at hyb
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, ← mul_assoc, hty] at hyb
    rw [← one_div]
    exact (le_div_iff₀ (half_pos hr)).mpr (by simpa only [mul_comm] using hyb)

/-- A closed convex set containing zero is its Hermitian bipolar. -/
theorem hermitianPolar_polar {B : Set E} [CompleteSpace E]
    (hc : Convex ℝ B) (hb : IsClosed B) (h₀ : (0 : E) ∈ B) :
    hermitianPolar (hermitianPolar B) = B := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  rw [hermitianPolar_eq_polarSet, hermitianPolar_eq_polarSet]
  simpa only [flip_eq_self] using polarSet_polarSet (B := innerₗ E) hc hb h₀

private theorem sSup_eq_zero_of_subset_singleton_zero {S : Set ℝ}
    (h : S ⊆ {0}) : sSup S = 0 := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hx₀ : x = 0 := h hx
    rw [Set.Subset.antisymm h (by simpa only [Set.singleton_subset_iff, ← hx₀] using hx),
      csSup_singleton]
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]

/-- The Hermitian conjugate of a gauge, Equation (130). -/
noncomputable def hermitianDualGauge (φ : E → ℝ) (y : E) : ℝ :=
  sSup ((fun x => (inner ℂ y x).re / φ x) '' {x | x ≠ 0})

/-- The dual gauge can be computed as the support value of the primal
unit sublevel set. Only positivity and positive homogeneity are needed
for this identity. -/
theorem hermitianDualGauge_eq_sSup_unitSublevel (φ : E → ℝ) (hzero : φ 0 = 0)
    (hpos : ∀ x ≠ 0, 0 < φ x)
    (hhom : ∀ (t : ℝ) (x : E), 0 ≤ t → φ (t • x) = t * φ x)
    (hb : Bornology.IsBounded {x | φ x ≤ 1}) (y : E) :
    hermitianDualGauge φ y = sSup ((fun x => (inner ℂ y x).re) '' {x | φ x ≤ 1}) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let S := (fun x => inner ℝ y x / φ x) '' {x | x ≠ 0}
  let T := (fun x => inner ℝ y x) '' {x | φ x ≤ 1}
  change sSup S = sSup T
  have hnorm (x : E) (hx : x ≠ 0) : (φ x)⁻¹ • x ∈ {z | φ z ≤ 1} := by
    change φ ((φ x)⁻¹ • x) ≤ 1
    rw [hhom _ _ (inv_nonneg.mpr (hpos x hx).le), inv_mul_cancel₀ (hpos x hx).ne']
  have hST : S ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨_, hnorm x hx, ?_⟩
    change inner ℝ y ((φ x)⁻¹ • x) = inner ℝ y x / φ x
    rw [real_inner_smul_right, div_eq_inv_mul]
  obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_le
  have hbT : BddAbove T := by
    refine ⟨‖y‖ * R, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (re_inner_le_norm (𝕜 := ℂ) y x).trans
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  have hbS := hbT.mono hST
  have hT : T.Nonempty := ⟨0, 0, by simp [hzero], inner_zero_right _⟩
  by_cases hy : y = 0
  · have he : sSup S = 0 := sSup_eq_zero_of_subset_singleton_zero (by
      rintro _ ⟨x, hx, rfl⟩
      simp [hy])
    have hf : sSup T = 0 := sSup_eq_zero_of_subset_singleton_zero (by
      rintro _ ⟨x, hx, rfl⟩
      simp [hy])
    rw [he, hf]
  have hS : S.Nonempty := ⟨_, y, hy, rfl⟩
  have hn : 0 ≤ sSup S := le_trans
    (div_nonneg (real_inner_self_nonneg) (hpos y hy).le)
    (le_csSup hbS (show inner ℝ y y / φ y ∈ S from ⟨y, hy, rfl⟩))
  refine le_antisymm (csSup_le_csSup hbT hS hST) (csSup_le hT ?_)
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : 0 ≤ inner ℝ y x
  · by_cases hx₀ : x = 0
    · simpa [hx₀] using hn
    exact (le_div_iff₀ (hpos x hx₀)).mpr
      (mul_le_of_le_one_right h hx) |>.trans (le_csSup hbS ⟨x, hx₀, rfl⟩)
  · exact (le_of_not_ge h).trans hn

/-- The conjugate of a gauge equals the Minkowski gauge of the polar
of its unit sublevel set. The sublevel set need not be convex. -/
theorem hermitianDualGauge_eq_gauge_polar (φ : E → ℝ) (hzero : φ 0 = 0)
    (hpos : ∀ x ≠ 0, 0 < φ x)
    (hhom : ∀ (t : ℝ) (x : E), 0 ≤ t → φ (t • x) = t * φ x)
    (hb : Bornology.IsBounded {x | φ x ≤ 1})
    (h₀ : (0 : E) ∈ interior {x | φ x ≤ 1}) :
    hermitianDualGauge φ = gauge (hermitianPolar {x | φ x ≤ 1}) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let B := {x : E | φ x ≤ 1}
  obtain ⟨hP, hP₀⟩ := hermitianPolar_isGaugeConvexBody hb h₀
  obtain ⟨hg, he, _⟩ := exercise_53_gauge hP hP₀
  obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_le
  funext y
  rw [hermitianDualGauge_eq_sSup_unitSublevel φ hzero hpos hhom hb]
  let S := (fun x => inner ℝ y x) '' B
  change sSup S = gauge (hermitianPolar B) y
  have hS : S.Nonempty := ⟨0, 0, by simp [B, hzero], inner_zero_right _⟩
  have hbS : BddAbove S := by
    refine ⟨‖y‖ * R, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (re_inner_le_norm (𝕜 := ℂ) y x).trans
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  by_cases hy : y = 0
  · rw [hy, gauge_zero]
    apply sSup_eq_zero_of_subset_singleton_zero
    rintro _ ⟨x, hx, rfl⟩
    simp [hy]
  let g := gauge (hermitianPolar B) y
  have hgpos : 0 < g := lt_of_le_of_ne (hg.nonnegative y)
    (Ne.symm fun h => hy (hg.eq_zero y h))
  have hbound : sSup S ≤ g := by
    apply csSup_le hS
    rintro _ ⟨x, hx, rfl⟩
    have hm : g⁻¹ • y ∈ hermitianPolar B := by
      rw [he]
      change gauge (hermitianPolar B) (g⁻¹ • y) ≤ 1
      rw [hg.homogeneity _ _ (inv_nonneg.mpr hgpos.le), inv_mul_cancel₀ hgpos.ne']
    have hh := hm x hx
    change inner ℝ (g⁻¹ • y) x ≤ 1 at hh
    simpa only [real_inner_smul_left, inv_mul_le_iff₀ hgpos, mul_one] using hh
  refine le_antisymm hbound ?_
  have hs : 0 < sSup S := by
    have hh := le_csSup hbS
      (show inner ℝ y ((φ y)⁻¹ • y) ∈ S from
        ⟨_, by
          change φ ((φ y)⁻¹ • y) ≤ 1
          rw [hhom _ _ (inv_nonneg.mpr (hpos y hy).le), inv_mul_cancel₀ (hpos y hy).ne'], rfl⟩)
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm] at hh
    exact (mul_pos (inv_pos.mpr (hpos y hy))
      (mul_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hy))).trans_le hh
  have hm : (sSup S)⁻¹ • y ∈ hermitianPolar B := by
    intro x hx
    change inner ℝ ((sSup S)⁻¹ • y) x ≤ 1
    rw [real_inner_smul_left, inv_mul_le_iff₀ hs, mul_one]
    exact le_csSup hbS ⟨x, hx, rfl⟩
  exact gauge_le_of_mem hs.le ⟨_, hm, smul_inv_smul₀ hs.ne' y⟩

/-- **Exercise 57(a)–(d)** of [benIsrael2003generalized], Chapter 3.
The Hermitian polar of an equilibrated convex body is equilibrated,
polarity is involutive, and the corresponding norms are dual to one another. -/
theorem exercise_57 [CompleteSpace E] {B : Set E} (hB : IsGaugeConvexBody B)
    (hbal : Balanced ℂ B) :
    IsGaugeConvexBody (hermitianPolar B) ∧ Balanced ℂ (hermitianPolar B) ∧
    hermitianPolar (hermitianPolar B) = B ∧
    hermitianDualGauge (gauge B) = gauge (hermitianPolar B) ∧
    hermitianDualGauge (hermitianDualGauge (gauge B)) = gauge B := by
  have h₀ := balancedGaugeConvexBody_zero_mem_interior hB hbal
  obtain ⟨hP, hP₀⟩ := hermitianPolar_isGaugeConvexBody hB.bounded h₀
  have hPP := hermitianPolar_polar hB.convex hB.closed (interior_subset h₀)
  have key {U : Set E} (hU : IsGaugeConvexBody U) (hu : (0 : E) ∈ interior U) :
      hermitianDualGauge (gauge U) = gauge (hermitianPolar U) := by
    obtain ⟨hg, he, _⟩ := exercise_53_gauge hU hu
    rw [hermitianDualGauge_eq_gauge_polar (gauge U) gauge_zero
      (fun x hx => lt_of_le_of_ne (hg.nonnegative x) (Ne.symm fun h => hx (hg.eq_zero x h)))
      hg.homogeneity (he ▸ hU.bounded) (he ▸ hu), ← he]
  exact ⟨hP, hermitianPolar_balanced hbal, hPP, key hB h₀, by
    rw [key hB h₀, key hP hP₀, hPP]⟩

end PolarGaugeExercises

section HyperplaneResidualExercises

section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- With residual convention $r=b-Ax$, the possible residuals for a
range hyperplane $\ker f$ are exactly the solutions of $f(r)=f(b)$. -/
theorem exists_residual_eq_iff_of_range_eq_ker (A : E →ₗ[ℂ] F) (f : StrongDual ℂ F)
    (hA : A.range = f.ker) (b r : F) :
    (∃ x : E, b - A x = r) ↔ f r = f b := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : A x ∈ f.ker := hA ▸ LinearMap.mem_range_self A x
    have hx₀ : f (A x) = 0 := LinearMap.mem_ker.mp hx
    rw [map_sub, hx₀, sub_zero]
  · intro hr
    have hm : b - r ∈ f.ker := by
      change f (b - r) = 0
      rw [map_sub, hr, sub_self]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (hA.symm ▸ hm)
    exact ⟨x, by rw [hx, sub_sub_cancel]⟩

/-- The lower bound for residuals constrained by a nonzero functional. -/
theorem norm_residual_lower_bound_of_eval_eq {f : StrongDual ℂ F} (hf : f ≠ 0)
    {r b : F} (hr : f r = f b) : ‖f b‖ / ‖f‖ ≤ ‖r‖ := by
  apply (div_le_iff₀ (norm_pos_iff.mpr hf)).mpr
  rw [← hr, mul_comm]
  exact f.le_opNorm r

variable [FiniteDimensional ℂ F]

/-- **Exercise 61** of [benIsrael2003generalized], Chapter 3.
For a codimension-one range specified by its nonzero dual normal $f$,
choose a unit vector $v$ with $f(v)=\|f\|$. The optimal residual is
$(f(b)/\|f\|)v$. Any inner inverse sends $b-r$ to a minimizing solution.
The error is the modulus of the prescribed pairing divided by the dual norm. -/
theorem exercise_61 (A : E →ₗ[ℂ] F) (G : F →ₗ[ℂ] E) (f : StrongDual ℂ F) (hf : f ≠ 0)
    (hA : A.range = f.ker) (hG : ∀ x, A (G (A x)) = A x) (b : F) :
    ∃ v : F, ‖v‖ = 1 ∧ f v = (‖f‖ : ℂ) ∧
      let r := (f b / (‖f‖ : ℂ)) • v
      b - A (G (b - r)) = r ∧ ‖r‖ = ‖f b‖ / ‖f‖ ∧
        ∀ x : E, ‖r‖ ≤ ‖b - A x‖ := by
  obtain ⟨v, hv, hfv⟩ := exercise_59_dual_attainment hf
  refine ⟨v, hv, hfv, ?_⟩
  dsimp only
  let r := (f b / (‖f‖ : ℂ)) • v
  change b - A (G (b - r)) = r ∧ ‖r‖ = ‖f b‖ / ‖f‖ ∧
    ∀ x : E, ‖r‖ ≤ ‖b - A x‖
  have hd : (‖f‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf)
  have hr : f r = f b := by
    rw [show r = (f b / (‖f‖ : ℂ)) • v from rfl, map_smul, hfv, smul_eq_mul,
      div_mul_cancel₀ _ hd]
  obtain ⟨x, hx⟩ := (exists_residual_eq_iff_of_range_eq_ker A f hA b r).mpr hr
  have hAx : A x = b - r := by rw [← hx, sub_sub_cancel]
  have he : ‖r‖ = ‖f b‖ / ‖f‖ := by
    rw [show r = (f b / (‖f‖ : ℂ)) • v from rfl, norm_smul, hv, mul_one, norm_div,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  refine ⟨?_, he, fun y => he.trans_le ?_⟩
  · rw [← hAx, hG, hx]
  · exact norm_residual_lower_bound_of_eval_eq hf
      ((exists_residual_eq_iff_of_range_eq_ker A f hA b _).mp ⟨y, rfl⟩)

end

end HyperplaneResidualExercises

section ConjugateGaugeExercises

open Set
open scoped Topology

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Conditions (G1)–(G3). Subadditivity is unnecessary for taking the conjugate. -/
structure IsPositiveHomogeneousGauge (φ : E → ℝ) : Prop where
  continuous : Continuous φ
  nonnegative : ∀ x, 0 ≤ φ x
  eq_zero : ∀ x, φ x = 0 → x = 0
  homogeneity : ∀ (r : ℝ) (x : E), 0 ≤ r → φ (r • x) = r * φ x

variable {φ : E → ℝ}

private theorem IsPositiveHomogeneousGauge.zero (hφ : IsPositiveHomogeneousGauge φ) :
    φ 0 = 0 := by simpa only [zero_smul, zero_mul] using hφ.homogeneity 0 (0 : E) le_rfl

private theorem IsPositiveHomogeneousGauge.pos (hφ : IsPositiveHomogeneousGauge φ)
    {x : E} (hx : x ≠ 0) : 0 < φ x :=
  lt_of_le_of_ne (hφ.nonnegative x) (Ne.symm fun he => hx (hφ.eq_zero x he))

private theorem IsPositiveHomogeneousGauge.normalize (hφ : IsPositiveHomogeneousGauge φ)
    {x : E} (hx : x ≠ 0) : φ ((φ x)⁻¹ • x) = 1 := by
  rw [hφ.homogeneity _ _ (inv_nonneg.mpr (hφ.nonnegative x)),
    inv_mul_cancel₀ (hφ.pos hx).ne']

private theorem positiveHomogeneousGauge_of_positiveGauge (hφ : IsPositiveGauge φ) :
    IsPositiveHomogeneousGauge φ :=
  ⟨hφ.continuous, hφ.nonnegative, hφ.eq_zero, hφ.homogeneity⟩

private theorem IsPositiveHomogeneousGauge.interior_unitSublevel
    (hφ : IsPositiveHomogeneousGauge φ) : (0 : E) ∈ interior {x | φ x ≤ 1} := by
  have hN : {x | φ x < 1} ∈ 𝓝 (0 : E) :=
    hφ.continuous.continuousAt.eventually_lt continuousAt_const
      (by simpa only [hφ.zero] using (zero_lt_one : (0 : ℝ) < 1))
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset hN fun x hx => (show φ x < 1 from hx).le)

variable [FiniteDimensional ℂ E]

private theorem IsPositiveHomogeneousGauge.isBounded_unitSublevel
    (hφ : IsPositiveHomogeneousGauge φ) : Bornology.IsBounded {x | φ x ≤ 1} := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  by_cases hE : Nontrivial E
  · let : Nontrivial E := hE
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    have hnorm (x : E) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      ⟨_, hnorm w hw⟩ hφ.continuous.continuousOn
    have hv₀ : v ≠ 0 := by intro he; simp [he] at hv
    have hp := hφ.pos hv₀
    refine isBounded_iff_forall_norm_le.mpr ⟨(φ v)⁻¹, fun x hx => ?_⟩
    by_cases hx₀ : x = 0
    · simpa [hx₀] using inv_nonneg.mpr hp.le
    have hn := norm_pos_iff.mpr hx₀
    have hle := hmin (hnorm x hx₀)
    change φ v ≤ φ (‖x‖⁻¹ • x) at hle
    rw [hφ.homogeneity _ _ (inv_nonneg.mpr hn.le), ← div_eq_inv_mul] at hle
    rw [← one_div, le_div_iff₀ hp, mul_comm]
    exact ((le_div_iff₀ hn).mp hle).trans hx
  · let : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    exact isBounded_iff_forall_norm_le.mpr ⟨0, fun x _ => by simp [Subsingleton.elim x 0]⟩

/-- **Exercise 52(a)** of [benIsrael2003generalized], Chapter 3.
The dual ratio attains its supremum on any positively homogeneous
normalization sphere, in particular the primal gauge sphere and the
coordinate $ell^1$ sphere. -/
theorem exercise_52_dual_attainment [Nontrivial E] (φ ψ : E → ℝ)
    (hφ : IsPositiveHomogeneousGauge φ) (hψ : IsPositiveHomogeneousGauge ψ) (y : E) :
    ∃ x : E, ψ x = 1 ∧
      (inner ℂ y x).re / φ x = hermitianDualGauge φ y ∧
      ∀ z, ψ z = 1 → (inner ℂ y z).re / φ z ≤ (inner ℂ y x).re / φ x := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let G := {x | ψ x = 1}
  let f := fun x : E => inner ℝ y x / φ x
  have hclosed : IsClosed G := isClosed_eq hψ.continuous continuous_const
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hcompact : IsCompact G :=
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hψ.isBounded_unitSublevel.subset
      (fun x hx => (show ψ x = 1 from hx).le)⟩)
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hne : G.Nonempty := ⟨_, hψ.normalize hu⟩
  have hz (x : E) (hx : x ∈ G) : x ≠ 0 := by
    intro he
    change ψ x = 1 at hx
    simp [he, hψ.zero] at hx
  have hcont : ContinuousOn f G :=
    (continuous_const.inner continuous_id).continuousOn.div hφ.continuous.continuousOn
      (fun x hx => (hφ.pos (hz x hx)).ne')
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  let S := f '' {z : E | z ≠ 0}
  change ∃ x : E, ψ x = 1 ∧ f x = sSup S ∧ ∀ z, ψ z = 1 → f z ≤ f x
  have hbound : ∀ r ∈ S, r ≤ f x := by
    rintro _ ⟨z, hz, rfl⟩
    have hm := hmax (show (ψ z)⁻¹ • z ∈ G from hψ.normalize hz)
    have he : f ((ψ z)⁻¹ • z) = f z := by
      have hp := inv_pos.mpr (hψ.pos hz)
      dsimp [f]
      rw [real_inner_smul_right, hφ.homogeneity _ _ hp.le,
        mul_div_mul_left _ _ hp.ne']
    exact he ▸ hm
  refine ⟨x, hx, le_antisymm ?_ (csSup_le ⟨_, x, hz x hx, rfl⟩ hbound), ?_⟩
  · exact le_csSup ⟨_, hbound⟩ ⟨x, hz x hx, rfl⟩
  · exact fun z hz => hmax hz

/-- **Exercise 52(b)** of [benIsrael2003generalized], Chapter 3.
The conjugate of a positive homogeneous gauge is a subadditive positive gauge. -/
theorem exercise_52_dual_gauge (φ : E → ℝ) (hφ : IsPositiveHomogeneousGauge φ) :
    IsPositiveGauge (hermitianDualGauge φ) := by
  have hP := hermitianPolar_isGaugeConvexBody
    hφ.isBounded_unitSublevel hφ.interior_unitSublevel
  rw [hermitianDualGauge_eq_gauge_polar φ hφ.zero (fun _ => hφ.pos)
    hφ.homogeneity hφ.isBounded_unitSublevel hφ.interior_unitSublevel]
  exact (exercise_53_gauge hP.1 hP.2).1

omit [FiniteDimensional ℂ E] in
/-- **Exercise 52(c)** of [benIsrael2003generalized], Chapter 3.
Every unitary symmetry of the primal gauge is a symmetry of its conjugate. -/
theorem exercise_52_dual_invariant (φ : E → ℝ) (U : E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x, φ (U x) = φ x) (y : E) :
    hermitianDualGauge φ (U y) = hermitianDualGauge φ y := by
  rw [hermitianDualGauge, hermitianDualGauge]
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.symm x, ?_, ?_⟩
    · exact fun he => hx (by simpa using congrArg U he)
    · change (inner ℂ y (U.symm x)).re / φ (U.symm x) = (inner ℂ (U y) x).re / φ x
      have he := hU (U.symm x)
      rw [U.apply_symm_apply] at he
      rw [← he, ← U.inner_map_map, U.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨U x, fun he => hx (U.injective (he.trans U.map_zero.symm)),
      by
        change (inner ℂ (U y) (U x)).re / φ (U x) = (inner ℂ y x).re / φ x
        rw [U.inner_map_map, hU]⟩

/-- **Exercise 52(d)** of [benIsrael2003generalized], Chapter 3.
An ordinary positive gauge agrees with its double conjugate. -/
theorem exercise_52_dual_dual (φ : E → ℝ) (hφ : IsPositiveGauge φ) :
    hermitianDualGauge (hermitianDualGauge φ) = φ := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  let B := {x | φ x ≤ 1}
  obtain ⟨hB, h₀, he⟩ := exercise_53_converse φ hφ
  have form (ψ : E → ℝ) (hψ : IsPositiveGauge ψ) :=
    hermitianDualGauge_eq_gauge_polar ψ (positiveHomogeneousGauge_of_positiveGauge hψ).zero
      (fun _ => (positiveHomogeneousGauge_of_positiveGauge hψ).pos)
      hψ.homogeneity (positiveHomogeneousGauge_of_positiveGauge hψ).isBounded_unitSublevel
      (positiveHomogeneousGauge_of_positiveGauge hψ).interior_unitSublevel
  obtain ⟨hP, hP₀⟩ := hermitianPolar_isGaugeConvexBody hB.bounded h₀
  have hPset := (exercise_53_gauge hP hP₀).2.1
  rw [form _ (exercise_52_dual_gauge φ (positiveHomogeneousGauge_of_positiveGauge hφ)),
    form _ hφ, ← hPset, hermitianPolar_polar hB.convex hB.closed (interior_subset h₀)]
  exact he

end

end ConjugateGaugeExercises

section CoordinateGaugeExercises

open Set Finset
open scoped Matrix
open BenIsraelGreville.Chapter00 (IsVectorNorm)

variable {ι : Type*} [Fintype ι]

/-- Condition (G5) of Exercise 52, invariance under coordinate permutations. -/
def IsPermutationInvariantGauge (φ : EuclideanSpace ℂ ι → ℝ) : Prop :=
  ∀ (σ : ι ≃ ι) (x : EuclideanSpace ℂ ι),
    φ (WithLp.toLp 2 fun i => x (σ i)) = φ x

/-- Condition (G6) of Exercise 52, invariance under coordinate phases. -/
def IsPhaseInvariantGauge (φ : EuclideanSpace ℂ ι → ℝ) : Prop :=
  ∀ (ζ : ι → ℂ), (∀ i, ‖ζ i‖ = 1) → ∀ (x : EuclideanSpace ℂ ι),
    φ (WithLp.toLp 2 fun i => ζ i * x i) = φ x

private noncomputable def scalarPhaseLinearIsometry (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ℂ ≃ₗᵢ[ℂ] ℂ where
  toFun x := ζ * x
  invFun x := ζ⁻¹ * x
  left_inv x := by
    change ζ⁻¹ * (ζ * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ (by intro h; simp [h] at hζ), one_mul]
  right_inv x := by
    change ζ * (ζ⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ (by intro h; simp [h] at hζ), one_mul]
  map_add' x y := mul_add _ _ _
  map_smul' c x := by simp only [smul_eq_mul, RingHom.id_apply]; ring
  norm_map' x := by
    change ‖ζ * x‖ = ‖x‖
    rw [norm_mul, hζ, one_mul]

/-- **Exercise 52(c)** of [benIsrael2003generalized], Chapter 3.
Coordinate permutation symmetry passes to the conjugate gauge. -/
theorem exercise_52_dual_permutation (φ : EuclideanSpace ℂ ι → ℝ)
    (hφ : IsPermutationInvariantGauge φ) :
    IsPermutationInvariantGauge (hermitianDualGauge φ) := by
  intro σ x
  exact exercise_52_dual_invariant φ
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm) (hφ σ) x

/-- **Exercise 52(c)** of [benIsrael2003generalized], Chapter 3.
Coordinate phase symmetry passes to the conjugate gauge. -/
theorem exercise_52_dual_phase (φ : EuclideanSpace ℂ ι → ℝ)
    (hφ : IsPhaseInvariantGauge φ) :
    IsPhaseInvariantGauge (hermitianDualGauge φ) := by
  intro ζ hζ x
  exact exercise_52_dual_invariant φ
    (LinearIsometryEquiv.piLpCongrRight 2 fun i => scalarPhaseLinearIsometry (ζ i) (hζ i))
    (hφ ζ hζ) x

/-- **Exercise 56** of [benIsrael2003generalized], Chapter 3.
Unitary invariance implies the two symmetries required of a symmetric gauge. -/
theorem exercise_56 (φ : EuclideanSpace ℂ ι → ℝ)
    (hφ : ∀ (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) x, φ (U x) = φ x) :
    IsPermutationInvariantGauge φ ∧ IsPhaseInvariantGauge φ := by
  exact ⟨fun σ => hφ (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm),
    fun ζ hζ => hφ (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
      scalarPhaseLinearIsometry (ζ i) (hζ i))⟩

/-- The sum of coordinate moduli, used for the sphere in Equation (131b). -/
noncomputable def coordinateL1Gauge (x : EuclideanSpace ℂ ι) : ℝ := ∑ i, ‖x i‖

/-- The coordinate $ell^1$ gauge is a vector norm. -/
theorem coordinateL1Gauge_isVectorNorm :
    IsVectorNorm (coordinateL1Gauge : EuclideanSpace ℂ ι → ℝ) := by
  refine ⟨fun x => sum_nonneg fun i _ => norm_nonneg (x i), ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      ext i
      exact norm_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun i _ => norm_nonneg (x i)).mp
        hx i (mem_univ _))
    · rintro rfl
      simp [coordinateL1Gauge]
  · intro c x
    simp only [coordinateL1Gauge, PiLp.smul_apply, norm_smul, Finset.mul_sum]
  · intro x y
    unfold coordinateL1Gauge
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => norm_add_le (x i) (y i)

/-- **Exercise 52(a)** of [benIsrael2003generalized], Chapter 3.
The conjugate ratio attains its supremum on the coordinate $ell^1$ sphere. -/
theorem exercise_52_dual_attainment_coordinateL1 [Nonempty ι]
    (φ : EuclideanSpace ℂ ι → ℝ) (hφ : IsPositiveHomogeneousGauge φ)
    (y : EuclideanSpace ℂ ι) :
    ∃ x : EuclideanSpace ℂ ι, coordinateL1Gauge x = 1 ∧
      (inner ℂ y x).re / φ x = hermitianDualGauge φ y ∧
      ∀ z, coordinateL1Gauge z = 1 → (inner ℂ y z).re / φ z ≤ (inner ℂ y x).re / φ x := by
  have h := ((isVectorNorm_iff_positiveGauge_absoluteHomogeneity _).mp
    (coordinateL1Gauge_isVectorNorm (ι := ι))).1
  exact exercise_52_dual_attainment φ coordinateL1Gauge hφ
    ⟨h.continuous, h.nonnegative, h.eq_zero, h.homogeneity⟩ y

/-- The coordinate $ell^1$ norm satisfies (G5) and (G6). -/
theorem coordinateL1Gauge_isSymmetric :
    IsPermutationInvariantGauge (coordinateL1Gauge : EuclideanSpace ℂ ι → ℝ) ∧
      IsPhaseInvariantGauge (coordinateL1Gauge : EuclideanSpace ℂ ι → ℝ) := by
  constructor
  · intro σ x
    exact Fintype.sum_equiv σ (fun i => ‖x (σ i)‖) (fun i => ‖x i‖) (fun _ => rfl)
  · intro ζ hζ x
    exact sum_congr rfl fun i _ => by
      change ‖ζ i * x i‖ = ‖x i‖
      rw [norm_mul, hζ i, one_mul]

/-- **Exercise 56** of [benIsrael2003generalized], Chapter 3.
The converse fails on two complex coordinates. The normalized Hadamard
matrix sends the first coordinate vector to one of strictly larger
$ell^1$ norm. -/
theorem exercise_56_converse_failure :
    ∃ (φ : EuclideanSpace ℂ (Fin 2) → ℝ)
      (U : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2))
      (x : EuclideanSpace ℂ (Fin 2)),
      IsVectorNorm φ ∧ IsPermutationInvariantGauge φ ∧ IsPhaseInvariantGauge φ ∧
      φ (U x) ≠ φ x := by
  let s := (Real.sqrt 2)⁻¹
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  have hsq : s * s = 1 / 2 := by
    dsimp only [s]
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  let a : ℂ := s
  have hsq' : a * a = 1 / 2 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg Complex.ofReal hsq
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![a, a; a, -a]
  have hH : H ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, Matrix.mul_apply, Fin.sum_univ_two, a] <;>
      linear_combination 2 * hsq'
  let x : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let U := Matrix.unitaryLinearIsometryEquiv hH
  refine ⟨coordinateL1Gauge, U, x, coordinateL1Gauge_isVectorNorm,
    coordinateL1Gauge_isSymmetric.1, coordinateL1Gauge_isSymmetric.2, ?_⟩
  have hval : coordinateL1Gauge (U x) = 2 * s := by
    rw [coordinateL1Gauge, Fin.sum_univ_two]
    rw [show U x = Matrix.toEuclideanLin H x from Matrix.unitaryLinearIsometryEquiv_apply hH x]
    simp [x, H, a, Real.norm_of_nonneg hs.le, two_mul]
  have hx : coordinateL1Gauge x = 1 := by simp [coordinateL1Gauge, x, Fin.sum_univ_two]
  rw [hval, hx]
  intro he
  nlinarith

end CoordinateGaugeExercises

section RotundSmoothExercises

open Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A normal of the supporting real affine hyperplane through $y$,
normalized so that the supporting level equals one. -/
def IsNormalizedSupportingNormal (B : Set E) (y u : E) : Prop :=
  (inner ℂ u y).re = 1 ∧ u ∈ hermitianPolar B

/-- Smoothness of a body with the origin in its interior, stated as
uniqueness of a normalized supporting hyperplane at every boundary point. -/
def IsSmoothGaugeBody (B : Set E) : Prop :=
  ∀ y ∈ frontier B, ∃! u : E, IsNormalizedSupportingNormal B y u

/-- Distinct normalized supporting normals through the same point
specify distinct hyperplanes. -/
theorem eq_of_normalized_supporting_hyperplanes_eq {y u v : E}
    (hu : (inner ℂ u y).re = 1) (hv : (inner ℂ v y).re = 1)
    (he : {x : E | (inner ℂ u x).re = 1} = {x : E | (inner ℂ v x).re = 1}) :
    u = v := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  change inner ℝ u y = 1 at hu
  change inner ℝ v y = 1 at hv
  have key (x : E) : inner ℝ u x = inner ℝ v x := by
    let z := y + x - (inner ℝ u x) • y
    have huz : z ∈ {x : E | (inner ℂ u x).re = 1} := by
      change inner ℝ u (y + x - (inner ℝ u x) • y) = 1
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, hu, mul_one]
      ring
    have hvz := he ▸ huz
    change inner ℝ v (y + x - (inner ℝ u x) • y) = 1 at hvz
    rw [inner_sub_right, inner_add_right, real_inner_smul_right, hv, mul_one] at hvz
    linarith
  have hz : inner ℝ (u - v) (u - v) = 0 := by
    rw [inner_sub_left, key, sub_self]
  have hz' : ‖u - v‖ ^ 2 = 0 := (real_inner_self_eq_norm_sq (u - v)).symm.trans hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith))

private theorem re_inner_lt_one_of_mem_interior {B : Set E} {y x : E}
    (hy : y ∈ hermitianPolar B) (hy₀ : y ≠ 0) (hx : x ∈ interior B) :
    (inner ℂ y x).re < 1 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let t := (r / 2) / ‖y‖
  have hn := norm_pos_iff.mpr hy₀
  have ht : 0 < t := div_pos (half_pos hr) hn
  have hm : x + t • y ∈ B := by
    apply hB
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, div_mul_cancel₀ _ hn.ne']
    exact half_lt_self hr
  have he := hy _ hm
  change inner ℝ y (x + t • y) ≤ 1 at he
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at he
  exact lt_of_lt_of_le (lt_add_of_pos_right _ (mul_pos ht (sq_pos_of_pos hn))) he

variable [FiniteDimensional ℂ E]

private theorem exists_polar_normal_of_frontier {B : Set E} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : E) ∈ interior B) {x : E} (hx : x ∈ frontier B) :
    ∃ y, IsNormalizedSupportingNormal B x y := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have ⟨hxB, hxint⟩ : x ∈ B ∧ x ∉ interior B := by
    simpa only [frontier, hB.closed.closure_eq, Set.mem_sdiff] using hx
  have hg := exercise_53_gauge hB h₀
  have hgx₁ : gauge B x ≤ 1 := (Set.ext_iff.mp hg.2.1 x).mp hxB
  have hgx₂ : ¬ gauge B x < 1 := by
    intro h
    exact hxint ((Set.ext_iff.mp hg.2.2 x).mpr h)
  have hgx : gauge B x = 1 := le_antisymm hgx₁ (le_of_not_gt hgx₂)
  obtain ⟨hP, hP₀⟩ := hermitianPolar_isGaugeConvexBody hB.bounded h₀
  have hPP := hermitianPolar_polar hB.convex hB.closed (interior_subset h₀)
  obtain ⟨hp, hpset, _⟩ := exercise_53_gauge hP hP₀
  have hpos (y : E) (hy : y ≠ 0) : 0 < gauge (hermitianPolar B) y :=
    lt_of_le_of_ne (hp.nonnegative y) (Ne.symm fun he => hy (hp.eq_zero y he))
  have hsup : sSup ((fun y => inner ℝ x y) '' hermitianPolar B) = 1 := by
    change sSup ((fun y => (inner ℂ x y).re) '' hermitianPolar B) = 1
    rw [hpset]
    rw [← hermitianDualGauge_eq_sSup_unitSublevel _ gauge_zero hpos hp.homogeneity
      (hpset ▸ hP.bounded)]
    rw [hermitianDualGauge_eq_gauge_polar _ gauge_zero hpos hp.homogeneity
      (hpset ▸ hP.bounded) (hpset ▸ hP₀), ← hpset, hPP, hgx]
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hc := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hP.closed, hP.bounded⟩
  have hcont : Continuous (fun y : E => inner ℝ x y) :=
    continuous_const.inner continuous_id
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn ⟨0, interior_subset hP₀⟩ hcont.continuousOn
  have hxy : inner ℝ x y = 1 := by
    rw [← hsup]
    have hbd : ∀ t ∈ (fun y => inner ℝ x y) '' hermitianPolar B, t ≤ inner ℝ x y := by
      rintro _ ⟨z, hz, rfl⟩
      exact hmax hz
    exact le_antisymm (le_csSup ⟨_, hbd⟩ ⟨y, hy, rfl⟩)
      (csSup_le ⟨_, y, hy, rfl⟩ hbd)
  exact ⟨y, (real_inner_comm x y).trans hxy, hy⟩

/-- **Exercise 63** of [benIsrael2003generalized], Chapter 3.
An equilibrated convex body is rotund exactly when its Hermitian
polar has a unique supporting hyperplane at every boundary point. -/
theorem exercise_63 {B : Set E} (hB : IsGaugeConvexBody B) (hbal : Balanced ℂ B) :
    StrictConvex ℝ B ↔ IsSmoothGaugeBody (hermitianPolar B) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have h₀ := balancedGaugeConvexBody_zero_mem_interior hB hbal
  obtain ⟨hP, hP₀⟩ := hermitianPolar_isGaugeConvexBody hB.bounded h₀
  have hPP := hermitianPolar_polar hB.convex hB.closed (interior_subset h₀)
  constructor
  · intro h y hy
    obtain ⟨u, hu⟩ := exists_polar_normal_of_frontier hP hP₀ hy
    refine ⟨u, hu, fun v hv => ?_⟩
    have huvB : u ∈ B := hPP ▸ hu.2
    have hvvB : v ∈ B := hPP ▸ hv.2
    by_contra he
    have hmid := h hvvB huvB he (by norm_num : (1 / 2 : ℝ) > 0)
      (by norm_num : (1 / 2 : ℝ) > 0) (by norm_num)
    have hyP : y ∈ hermitianPolar B := hP.closed.frontier_subset hy
    have hy₀ : y ≠ 0 := by
      intro he
      have hv₀ := hv.1
      simp [he] at hv₀
    have hlt := re_inner_lt_one_of_mem_interior hyP hy₀ hmid
    change inner ℝ y ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • u) < 1 at hlt
    have hu₁ : inner ℝ u y = 1 := hu.1
    have hv₁ : inner ℝ v y = 1 := hv.1
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm v y, real_inner_comm u y, hv₁, hu₁] at hlt
    norm_num at hlt
  · intro h u hu v hv huv a b ha hb hab
    let x := a • u + b • v
    by_contra hx
    have hxB : x ∈ B := hB.convex hu hv ha.le hb.le hab
    have hxf : x ∈ frontier B := by
      rw [frontier, hB.closed.closure_eq]
      exact ⟨hxB, hx⟩
    obtain ⟨y, hys, hyP⟩ := exists_polar_normal_of_frontier hB h₀ hxf
    have hyf : y ∈ frontier (hermitianPolar B) := by
      rw [frontier, hP.closed.closure_eq]
      refine ⟨hyP, fun hI => ?_⟩
      have hx₀ : x ≠ 0 := by intro he; simp [he] at hys
      have ht := re_inner_lt_one_of_mem_interior
        (show x ∈ hermitianPolar (hermitianPolar B) from hPP.symm ▸ hxB) hx₀ hI
      change inner ℝ x y < 1 at ht
      change inner ℝ y x = 1 at hys
      rw [real_inner_comm y x, hys] at ht
      exact (lt_irrefl _ ht)
    have hule : inner ℝ y u ≤ 1 := hyP u hu
    have hvle : inner ℝ y v ≤ 1 := hyP v hv
    change inner ℝ y (a • u + b • v) = 1 at hys
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at hys
    have hu₁ : inner ℝ y u = 1 := by
      have := mul_nonneg hb.le (sub_nonneg.mpr hvle)
      by_contra he
      have hlt := mul_lt_mul_of_pos_left (lt_of_le_of_ne hule he) ha
      linarith
    have hv₁ : inner ℝ y v = 1 := by
      rw [hu₁, mul_one] at hys
      exact (mul_right_inj' hb.ne').mp (by linarith)
    have huS : IsNormalizedSupportingNormal (hermitianPolar B) y u :=
      ⟨(real_inner_comm y u).trans hu₁, hPP.symm ▸ hu⟩
    have hvS : IsNormalizedSupportingNormal (hermitianPolar B) y v :=
      ⟨(real_inner_comm y v).trans hv₁, hPP.symm ▸ hv⟩
    exact huv ((h y hyf).unique huS hvS)

end

end RotundSmoothExercises

section FixedDimensionProjection

open Set Module
open scoped Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- Every metric projection value occurs for a subspace in each prescribed
positive proper dimension. A norming functional for the residual supplies
a hyperplane in which to extend the span of the projected point. -/
theorem exists_finrank_eq_metricProjection (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) (x : E) (k : ℕ)
    (hk₁ : 1 ≤ k) (hk₂ : k < Module.finrank ℂ E) :
    ∃ M : Submodule ℂ E, Module.finrank ℂ M = k ∧ definition_1 M x = definition_1 L x := by
  let y := definition_1 L x
  let z := x - y
  by_cases hz : z = 0
  · have hxy : x = y := sub_eq_zero.mp hz
    obtain ⟨M, _, hx, hdim⟩ := exists_submodule_with_finrank_of_mem
      (⊤ : Submodule ℂ E) (show x ∈ (⊤ : Submodule ℂ E) from trivial) k hk₁
      (by simpa only [finrank_top] using hk₂.le)
    exact ⟨M, hdim, ((definition_1_eq_self_iff M x).mpr hx).trans hxy⟩
  have hz₀ : definition_1 L z = 0 := definition_1_residual h L x
  obtain ⟨f, hf, hfz, hL⟩ := (exercise_75 h L hz).mp hz₀
  have hyF : y ∈ f.ker := hL y (definition_1_mem L x)
  have hdim : k ≤ Module.finrank ℂ f.ker := by
    have hr := f.toLinearMap.finrank_range_add_finrank_ker
    have hr₁ := f.toLinearMap.range.finrank_le
    rw [finrank_self] at hr₁
    omega
  obtain ⟨M, hM, hy, hdimM⟩ := exists_submodule_with_finrank_of_mem
    f.ker hyF k hk₁ hdim
  have hzM : definition_1 M z = 0 := (exercise_75 h M hz).mpr
    ⟨f, hf, hfz, fun w hw => hM hw⟩
  have hsum : z + y = x := sub_add_cancel x y
  have he := definition_1_add_mem h M z hy
  rw [hsum, hzM, zero_add] at he
  exact ⟨M, hdimM, he⟩

/-- Mutual zero fibers imply that the metric projectors are contractive. -/
theorem metricProjector_contractive_of_mutual_zeroFibers (h : essentiallyStrictlyConvex E)
    (L N : Submodule ℂ E)
    (hN : ∀ x, x ∈ N ↔ definition_1 L x = 0)
    (hL : ∀ x, x ∈ L ↔ definition_1 N x = 0) (x : E) :
    ‖definition_1 L x‖ ≤ ‖x‖ := by
  let y := definition_1 L x
  let z := x - y
  have hN₀ : definition_1 N y = 0 := (hL y).mp (definition_1_mem L x)
  have hz : z ∈ N := (hN z).mpr (definition_1_residual h L x)
  have hz' := (isBestApprox_definition_1 N y).2 (-z) (N.neg_mem hz)
  rw [hN₀, sub_zero, sub_neg_eq_add, add_comm, sub_add_cancel] at hz'
  exact hz'

/-- **Exercise 73** of [benIsrael2003generalized], Chapter 3.
An essentially strictly convex norm is projective if in one positive proper
dimension all metric projectors are additive and have reciprocal zero fibers. -/
theorem exercise_73 (h : essentiallyStrictlyConvex E) (k : ℕ)
    (hk₁ : 1 ≤ k) (hk₂ : k < Module.finrank ℂ E)
    (hL : ∀ L : Submodule ℂ E, Module.finrank ℂ L = k →
      (∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y) ∧
      ∀ N : Submodule ℂ E, (∀ x, x ∈ N ↔ definition_1 L x = 0) →
        ∀ x, x ∈ L ↔ definition_1 N x = 0) :
    IsProjectiveNorm (E := E) := by
  intro L x
  obtain ⟨M, hM, hx⟩ := exists_finrank_eq_metricProjection h L x k hk₁ hk₂
  obtain ⟨hadd, hrecip⟩ := hL M hM
  obtain ⟨N, hN⟩ := (corollary_5 h M).1.mp hadd
  rw [← hx]
  exact metricProjector_contractive_of_mutual_zeroFibers h M N hN (hrecip N hN) x

end

end FixedDimensionProjection

section ChebyshevResidual

open Finset

section

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℂ E]

/-- The continuous functional with a given complex coordinate normal. -/
noncomputable def chebyshevNormalFunctional (u : ι → ℂ) : StrongDual ℂ (ι → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, star (u i) * x i
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        change (∑ i, star (u i) * (c * x i)) = c * ∑ i, star (u i) * x i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }

/-- The coordinate sum evaluates the Hermitian normal functional. -/
@[simp]
theorem chebyshevNormalFunctional_apply (u x : ι → ℂ) :
    chebyshevNormalFunctional u x = ∑ i, star (u i) * x i := rfl

private theorem sum_norm_normal_pos {u : ι → ℂ} (hu : u ≠ 0) :
    0 < ∑ i, ‖u i‖ := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  exact (norm_pos_iff.mpr hi).trans_le
    (Finset.single_le_sum (f := fun i => ‖u i‖) (fun j _ => norm_nonneg _) (mem_univ i))

private theorem star_mul_unit_phase (z : ℂ) (hz : z ≠ 0) :
    star z * (z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  have h₀ : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [← mul_div_assoc]
  apply (div_eq_iff h₀).mpr
  rw [mul_comm (star z)]
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj', pow_two]

private theorem eq_real_of_re_eq_of_norm_le {z : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (he : z.re = r) (hn : ‖z‖ ≤ r) : z = (r : ℂ) := by
  have he' : |z.re| = ‖z‖ := by
    rw [he, abs_of_nonneg hr]
    exact le_antisymm (he ▸ Complex.re_le_norm z) hn
  have hi := Complex.abs_re_eq_norm.mp he'
  exact Complex.ext (by simpa only [Complex.ofReal_re] using he)
    (by simpa only [Complex.ofReal_im] using hi)

/-- Equality in the ℓ∞ residual bound for a positive real prescribed
pairing. The coordinates of zero normal may be arbitrary in the disk. -/
theorem chebyshevResidual_eq_iff (u : ι → ℂ) (hu : u ≠ 0) (s : ℝ) (hs : 0 < s)
    (r : ι → ℂ) :
    let ρ := s / (∑ i, ‖u i‖)
    (chebyshevNormalFunctional u r = (s : ℂ) ∧ ‖r‖ = ρ) ↔
      (∀ i, u i ≠ 0 → r i = (ρ : ℂ) * (u i / (‖u i‖ : ℂ))) ∧
        (∀ i, u i = 0 → ‖r i‖ ≤ ρ) := by
  intro ρ
  let D := ∑ i, ‖u i‖
  have hD : 0 < D := sum_norm_normal_pos hu
  have hρ : 0 < ρ := div_pos hs hD
  have hρD : ρ * D = s := div_mul_cancel₀ s hD.ne'
  have hstar (i : ι) (hi : u i ≠ 0) :
      star (u i) * ((ρ : ℂ) * (u i / (‖u i‖ : ℂ))) =
        ((ρ * ‖u i‖ : ℝ) : ℂ) := by
    rw [← mul_left_comm, star_mul_unit_phase _ hi, Complex.ofReal_mul, mul_comm]
  constructor
  · rintro ⟨hpair, hnorm⟩
    have hcoord (i : ι) : ‖r i‖ ≤ ρ := hnorm ▸ norm_le_pi_norm r i
    have hle (i : ι) : (star (u i) * r i).re ≤ ρ * ‖u i‖ :=
      (Complex.re_le_norm _).trans (by
        rw [norm_mul, norm_star, mul_comm]
        exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _))
    have hsum : ∑ i, (ρ * ‖u i‖ - (star (u i) * r i).re) = 0 := by
      have h := congrArg Complex.re hpair
      rw [chebyshevNormalFunctional_apply] at h
      change Complex.reCLM (∑ i, star (u i) * r i) = s at h
      rw [map_sum] at h
      change ∑ i, (star (u i) * r i).re = s at h
      rw [sum_sub_distrib, ← mul_sum, ← show D = ∑ i, ‖u i‖ from rfl, hρD, h, sub_self]
    have hz (i : ι) : (star (u i) * r i).re = ρ * ‖u i‖ := by
      have ht := ((sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hle i)).mp
        hsum i (mem_univ i))
      exact (sub_eq_zero.mp ht).symm
    refine ⟨fun i hi => ?_, fun i _ => hcoord i⟩
    apply mul_left_cancel₀ (star_ne_zero.mpr hi)
    rw [hstar i hi]
    apply eq_real_of_re_eq_of_norm_le (mul_nonneg hρ.le (norm_nonneg _)) (hz i)
    rw [norm_mul, norm_star, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)
  · rintro ⟨hactive, hzero⟩
    have hcoord (i : ι) (hi : u i ≠ 0) : ‖r i‖ = ρ := by
      rw [hactive i hi, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hρ.le, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hi), mul_one]
    have hterm (i : ι) : star (u i) * r i = ((ρ * ‖u i‖ : ℝ) : ℂ) := by
      by_cases hi : u i = 0
      · simp [hi]
      · rw [hactive i hi, hstar i hi]
    refine ⟨?_, le_antisymm ((pi_norm_le_iff_of_nonneg hρ.le).mpr fun i => ?_) ?_⟩
    · rw [chebyshevNormalFunctional_apply]
      simp_rw [hterm]
      rw [← Complex.ofReal_sum, ← mul_sum]
      change ((ρ * D : ℝ) : ℂ) = (s : ℂ)
      rw [hρD]
    · by_cases hi : u i = 0
      · exact hzero i hi
      · exact (hcoord i hi).le
    · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
        by_contra! h
        exact hu (funext h)
      exact (hcoord i hi).symm.trans_le (norm_le_pi_norm r i)

/-- **Exercise 60**, corrected, of [benIsrael2003generalized], Chapter 3.
For a codimension-one coordinate range with normal $u$, normalize it
so that the prescribed residual pairing $s$ is real and positive.
The minimum ℓ∞ residual norm is $s/\sum_i |u_i|$. Equation (141)
determines all coordinates with nonzero normal. The remaining components
may vary throughout the disk of the same radius. The lift is $G(b-r)$. -/
theorem exercise_60 (A : E →ₗ[ℂ] (ι → ℂ)) (G : (ι → ℂ) →ₗ[ℂ] E)
    (u : ι → ℂ) (hu : u ≠ 0) (b : ι → ℂ) (s : ℝ) (hs : 0 < s)
    (hA : A.range = (chebyshevNormalFunctional u).ker)
    (hG : ∀ x, A (G (A x)) = A x) (hb : chebyshevNormalFunctional u b = (s : ℂ)) :
    let ρ := s / (∑ i, ‖u i‖)
    (∀ x : E, ρ ≤ ‖b - A x‖) ∧
      (∀ r : ι → ℂ,
        ((∃ x : E, b - A x = r) ∧ ‖r‖ = ρ) ↔
          (∀ i, u i ≠ 0 → r i = (ρ : ℂ) * (u i / (‖u i‖ : ℂ))) ∧
            (∀ i, u i = 0 → ‖r i‖ ≤ ρ)) ∧
      ∃ r : ι → ℂ, b - A (G (b - r)) = r ∧ ‖r‖ = ρ := by
  classical
  intro ρ
  let D := ∑ i, ‖u i‖
  have hD : 0 < D := sum_norm_normal_pos hu
  have hρ : 0 < ρ := div_pos hs hD
  let f := chebyshevNormalFunctional u
  have character (r : ι → ℂ) :=
    exists_residual_eq_iff_of_range_eq_ker A f hA b r
  have hchar (r : ι → ℂ) :
      ((∃ x : E, b - A x = r) ∧ ‖r‖ = ρ) ↔
        (∀ i, u i ≠ 0 → r i = (ρ : ℂ) * (u i / (‖u i‖ : ℂ))) ∧
          (∀ i, u i = 0 → ‖r i‖ ≤ ρ) := by
    rw [character r]
    change (f r = f b ∧ _) ↔ _
    rw [show f b = (s : ℂ) from hb]
    exact chebyshevResidual_eq_iff u hu s hs r
  refine ⟨fun x => ?_, hchar, ?_⟩
  · let r := b - A x
    have hr := (character r).mp ⟨x, rfl⟩
    have he : f r = (s : ℂ) := hr.trans hb
    have hre := congrArg Complex.re he
    change (f r).re = s at hre
    apply (div_le_iff₀ hD).mpr
    rw [← hre]
    change (∑ i, star (u i) * r i).re ≤ ‖r‖ * D
    rw [show (∑ i, star (u i) * r i).re = ∑ i, (star (u i) * r i).re from
      map_sum Complex.reCLM _ _, show D = ∑ i, ‖u i‖ from rfl, mul_sum]
    exact sum_le_sum fun i _ => (Complex.re_le_norm _).trans (by
      rw [norm_mul, norm_star, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm r i) (norm_nonneg _))
  · let r := fun i => if u i = 0 then 0 else (ρ : ℂ) * (u i / (‖u i‖ : ℂ))
    obtain ⟨⟨x, hx⟩, hnorm⟩ := (hchar r).mpr
      ⟨fun i hi => ite_eq_right hi, fun i hi => by simp [r, hi, hρ.le]⟩
    have hAx : A x = b - r := by rw [← hx, sub_sub_cancel]
    exact ⟨r, by rw [← hAx, hG, hx], hnorm⟩


/-- For an injective system, the minimizing solution is unique exactly
when every coordinate of the normal is active. -/
theorem exercise_60_unique_iff (A : E →ₗ[ℂ] (ι → ℂ)) (G : (ι → ℂ) →ₗ[ℂ] E)
    (hAi : Function.Injective A) (u : ι → ℂ) (hu : u ≠ 0) (b : ι → ℂ) (s : ℝ) (hs : 0 < s)
    (hA : A.range = (chebyshevNormalFunctional u).ker)
    (hG : ∀ x, A (G (A x)) = A x) (hb : chebyshevNormalFunctional u b = (s : ℂ)) :
    (∃! x : E, ‖b - A x‖ = s / (∑ i, ‖u i‖)) ↔ ∀ i, u i ≠ 0 := by
  classical
  let ρ := s / (∑ i, ‖u i‖)
  have hρ : 0 < ρ := div_pos hs (sum_norm_normal_pos hu)
  obtain ⟨_, hchar, r, hr, hn⟩ := exercise_60 A G u hu b s hs hA hG hb
  change (∃! x : E, ‖b - A x‖ = ρ) ↔ ∀ i, u i ≠ 0
  have hopt (x : E) (hx : ‖b - A x‖ = ρ) :=
    (hchar (b - A x)).mp ⟨⟨x, rfl⟩, hx⟩
  constructor
  · intro h i hi
    let v := fun j : ι => if u j = 0 then 0 else (ρ : ℂ) * (u j / (‖u j‖ : ℂ))
    let w := Function.update v i (ρ : ℂ)
    have hva : ∀ j, u j ≠ 0 → v j = (ρ : ℂ) * (u j / (‖u j‖ : ℂ)) :=
      fun j hj => ite_eq_right hj
    have hvz : ∀ j, u j = 0 → ‖v j‖ ≤ ρ := fun j hj => by simp [v, hj, hρ.le]
    have hwa : ∀ j, u j ≠ 0 → w j = (ρ : ℂ) * (u j / (‖u j‖ : ℂ)) := by
      intro j hj
      have hji : j ≠ i := fun he => hj (he ▸ hi)
      change Function.update v i (ρ : ℂ) j = _
      rw [Function.update_of_ne hji]
      exact hva j hj
    have hwz : ∀ j, u j = 0 → ‖w j‖ ≤ ρ := by
      intro j hj
      by_cases hji : j = i
      · subst j
        change ‖Function.update v i (ρ : ℂ) i‖ ≤ ρ
        rw [Function.update_self, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      · change ‖Function.update v i (ρ : ℂ) j‖ ≤ ρ
        rw [Function.update_of_ne hji]
        exact hvz j hj
    obtain ⟨⟨x, hx⟩, hv⟩ := (hchar v).mpr ⟨hva, hvz⟩
    obtain ⟨⟨y, hy⟩, hw⟩ := (hchar w).mpr ⟨hwa, hwz⟩
    have he : x = y := h.unique (hx ▸ hv) (hy ▸ hw)
    have hew : v = w := hx.symm.trans (he ▸ hy)
    have hcoord := congrFun hew i
    change v i = Function.update v i (ρ : ℂ) i at hcoord
    rw [Function.update_self] at hcoord
    simp only [v, hi, ite_true] at hcoord
    exact (Complex.ofReal_ne_zero.mpr hρ.ne') hcoord.symm
  · intro hu_all
    let x := G (b - r)
    have hx : ‖b - A x‖ = ρ := hr ▸ hn
    refine ⟨x, hx, fun z hz => ?_⟩
    apply hAi
    apply (sub_right_inj (a := b)).mp
    funext i
    exact ((hopt z hz).1 i (hu_all i)).trans (((hopt x hx).1 i (hu_all i)).symm)

end

end ChebyshevResidual

section ProjectiveBound

open Set Module
open scoped Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- The projective bound of a norm, Equation (145), is the supremum
of the projection norms over positive-dimensional proper subspaces. -/
noncomputable def projectiveBound : ℝ :=
  sSup ((fun L : Submodule ℂ E => mixedOperatorNorm (definition_1 L)) ''
    {L | 1 ≤ Module.finrank ℂ L ∧ Module.finrank ℂ L < Module.finrank ℂ E})

private theorem metricProjection_isContinuousHomogeneous (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) : IsContinuousHomogeneous (definition_1 L) :=
  ⟨continuous_definition_1 h L, definition_1_smul h L⟩

omit [IsScalarTower ℝ ℂ E] in
private theorem norm_metricProjection_lt_two_of_norm_eq_one (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) {x : E} (hx : ‖x‖ = 1) : ‖definition_1 L x‖ < 2 := by
  let : StrictConvexSpace ℝ E := (essentiallyStrictlyConvex_iff E).mp h
  let y := definition_1 L x
  let z := y - x
  have hz : ‖z‖ ≤ 1 := by
    rw [show z = y - x from rfl, norm_sub_rev, ← hx]
    exact definition_1_residual_norm_le L x
  have he : x + z = y := by dsimp [z]; abel
  have hle := norm_add_le x z
  rw [he, hx] at hle
  change ‖y‖ < 2
  by_contra! h₂
  have hz₁ : ‖z‖ = 1 := by linarith
  have hy₂ : ‖y‖ = 2 := by linarith
  have hsum : ‖x + z‖ = ‖x‖ + ‖z‖ := by rw [he, hx, hz₁, hy₂]; norm_num
  have hzx : x = z := eq_of_norm_eq_of_norm_add_eq (hx.trans hz₁.symm) hsum
  have hy : y = (2 : ℂ) • x := by
    rw [two_smul]
    simpa only [← hzx] using he.symm
  have hxL : x ∈ L := by
    have hm := L.smul_mem ((2 : ℂ)⁻¹) (definition_1_mem L x)
    change (2 : ℂ)⁻¹ • y ∈ L at hm
    rw [hy, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)] at hm
    exact hm
  have hyx : y = x := (definition_1_eq_self_iff L x).mpr hxL
  rw [hyx, hx] at hy₂
  norm_num at hy₂

private def projectionPairSet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Set (E × E) :=
  {p | ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 2 ∧ ∀ c : ℂ, ‖p.1 - p.2‖ ≤ ‖p.1 - c • p.2‖}

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
private theorem isCompact_projectionPairSet : IsCompact (projectionPairSet E) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · change IsClosed ({p : E × E | ‖p.1‖ = 1} ∩ ({p | ‖p.2‖ ≤ 2} ∩
      {p | ∀ c : ℂ, ‖p.1 - p.2‖ ≤ ‖p.1 - c • p.2‖}))
    refine (isClosed_eq continuous_fst.norm continuous_const).inter
      ((isClosed_le continuous_snd.norm continuous_const).inter ?_)
    have he : {p : E × E | ∀ c : ℂ, ‖p.1 - p.2‖ ≤ ‖p.1 - c • p.2‖} =
        ⋂ c : ℂ, {p : E × E | ‖p.1 - p.2‖ ≤ ‖p.1 - c • p.2‖} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
    rw [he]
    exact isClosed_iInter fun c =>
      isClosed_le (continuous_fst.sub continuous_snd).norm
        (continuous_fst.sub (continuous_const.smul continuous_snd)).norm
  · apply (Metric.isBounded_closedBall (x := (0 : E × E)) (r := 2)).subset
    rintro p ⟨hp₁, hp₂, _⟩
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, hp₁]
    exact ⟨by norm_num, hp₂⟩

omit [FiniteDimensional ℂ E] in
private theorem definition_1_span_eq_of_mem_projectionPairSet (h : essentiallyStrictlyConvex E)
    {p : E × E} (hp : p ∈ projectionPairSet E) :
    definition_1 (ℂ ∙ p.2) p.1 = p.2 := by
  refine (definition_1_eq_iff h _ _ _).mpr ⟨Submodule.mem_span_singleton_self _, ?_⟩
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  exact hp.2.2 c

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
private theorem mem_projectionPairSet_of_definition_1 (L : Submodule ℂ E)
    {x : E} (hx : ‖x‖ = 1) : (x, definition_1 L x) ∈ projectionPairSet E := by
  refine ⟨hx, ?_, fun c => (isBestApprox_definition_1 L x).2 _
    (L.smul_mem c (definition_1_mem L x))⟩
  simpa only [hx, mul_one] using definition_1_norm_le L x

/-- **Exercise 68(a)** and the inequalities in **Exercise 68(b)** of
[benIsrael2003generalized], Chapter 3. The finite projective bound is
attained by a projector of each positive proper rank, and lies in $[1,2)$. -/
theorem exercise_68 (h : essentiallyStrictlyConvex E) (k : ℕ)
    (hk₁ : 1 ≤ k) (hk₂ : k < Module.finrank ℂ E) :
    (∃ L : Submodule ℂ E, Module.finrank ℂ L = k ∧
      mixedOperatorNorm (definition_1 L) = projectiveBound (E := E)) ∧
    1 ≤ projectiveBound (E := E) ∧ projectiveBound (E := E) < 2 := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  obtain ⟨u, hu₀⟩ := exists_ne (0 : E)
  let w := ((‖u‖⁻¹ : ℝ) : ℂ) • u
  have hw : ‖w‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_inv_smul_mem_unitSphere hu₀
  have htop : definition_1 (⊤ : Submodule ℂ E) w = w :=
    (definition_1_eq_self_iff ⊤ w).mpr trivial
  have hww : (w, w) ∈ projectionPairSet E := by
    simpa only [htop] using mem_projectionPairSet_of_definition_1 (⊤ : Submodule ℂ E) hw
  have hcont : Continuous (fun p : E × E => ‖p.2‖) := continuous_snd.norm
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_projectionPairSet (E := E)).exists_isMaxOn ⟨(w, w), hww⟩ hcont.continuousOn
  have hunit : ‖p.1‖ = 1 := hp.1
  have h1 : 1 ≤ ‖p.2‖ := hw ▸ hmax hww
  have hpval := definition_1_span_eq_of_mem_projectionPairSet h hp
  have h2 : ‖p.2‖ < 2 := hpval ▸ norm_metricProjection_lt_two_of_norm_eq_one h (ℂ ∙ p.2) hunit
  obtain ⟨L, hdimL, hL⟩ := exists_finrank_eq_metricProjection h (ℂ ∙ p.2) p.1 k hk₁ hk₂
  have hnorm (M : Submodule ℂ E) : mixedOperatorNorm (definition_1 M) ≤ ‖p.2‖ := by
    obtain ⟨v, hv, he⟩ :=
      (exercise_66 _ (metricProjection_isContinuousHomogeneous h M)).2 inferInstance
    exact he ▸ hmax (mem_projectionPairSet_of_definition_1 M hv)
  have heq : mixedOperatorNorm (definition_1 L) = ‖p.2‖ := by
    refine le_antisymm (hnorm L) ?_
    have he := norm_homogeneous_apply_le (metricProjection_isContinuousHomogeneous h L) p.1
    rwa [hL, hpval, hunit, mul_one] at he
  have hQ : projectiveBound (E := E) = ‖p.2‖ := by
    unfold projectiveBound
    apply IsGreatest.csSup_eq
    refine ⟨⟨L, ⟨by omega, by omega⟩, heq⟩, ?_⟩
    rintro _ ⟨M, _, rfl⟩
    exact hnorm M
  rw [hQ]
  exact ⟨⟨L, hdimL, heq⟩, h1, h2⟩

/-- **Exercise 69**, projective bound criterion, of [benIsrael2003generalized], Chapter 3.
In dimension at least two, the projective bound equals one exactly when
every metric projection is contractive. -/
theorem exercise_69_projectiveBound_iff (h : essentiallyStrictlyConvex E)
    (hd : 2 ≤ Module.finrank ℂ E) :
    projectiveBound (E := E) = 1 ↔ IsProjectiveNorm (E := E) := by
  obtain ⟨⟨L, hdim, hmax⟩, h₁, h₂⟩ :=
    exercise_68 h 1 le_rfl (by omega)
  constructor
  · intro he M x
    obtain ⟨N, hN, hx⟩ := exists_finrank_eq_metricProjection h M x 1 le_rfl (by omega)
    have hb : BddAbove ((fun S : Submodule ℂ E => mixedOperatorNorm (definition_1 S)) ''
        {S | 1 ≤ Module.finrank ℂ S ∧ Module.finrank ℂ S < Module.finrank ℂ E}) := by
      refine ⟨2, ?_⟩
      rintro _ ⟨S, _, rfl⟩
      exact (mixedOperatorNorm_le_iff (metricProjection_isContinuousHomogeneous h S)
        (by norm_num)).mpr (definition_1_norm_le S)
    have hn : mixedOperatorNorm (definition_1 N) ≤ 1 :=
      he ▸ le_csSup hb ⟨N, ⟨by omega, by omega⟩, rfl⟩
    have hx' := (mixedOperatorNorm_le_iff (metricProjection_isContinuousHomogeneous h N)
      zero_le_one).mp hn x
    simpa only [hx, one_mul] using hx'
  · intro hproj
    exact le_antisymm (hmax ▸ (mixedOperatorNorm_le_iff
      (metricProjection_isContinuousHomogeneous h L) zero_le_one).mpr
      (by simpa only [one_mul] using hproj L)) h₁

end

end ProjectiveBound

section DualProjectiveExercises

open Set Module
open scoped Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- For a unit vector in a projective space, its norming functional is unique. -/
theorem eq_of_norming_functional_projective (h : essentiallyStrictlyConvex E)
    (hP : IsProjectiveNorm (E := E)) {x : E} (hx : ‖x‖ = 1)
    {f g : StrongDual ℂ E} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (hfx : f x = 1) (hgx : g x = 1) :
    f = g := by
  have hx₀ : x ≠ 0 := by intro he; simp [he] at hx
  let L := ℂ ∙ x
  have hker (u : StrongDual ℂ E) (hu : ‖u‖ = 1) (hux : u x = 1) (z : E) :
      z ∈ u.ker ↔ definition_1 L z = 0 := by
    have hxP : definition_1 u.ker x = 0 := (exercise_75 h u.ker hx₀).mpr
      ⟨u, hu, by rw [hx, hux, Complex.ofReal_one], fun _ hw => hw⟩
    have hzero (w : E) : w ∈ L ↔ definition_1 u.ker w = 0 := by
      constructor
      · rintro hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [definition_1_smul h u.ker, hxP, smul_zero]
      · intro hw
        let v := w - u w • x
        have hv : v ∈ u.ker := by
          change u (w - u w • x) = 0
          rw [map_sub, map_smul, smul_eq_mul, hux, mul_one, sub_self]
        have he := definition_1_add_mem h u.ker (u w • x) hv
        have hsum : u w • x + v = w := by dsimp [v]; abel
        rw [hsum, hw, definition_1_smul h u.ker, hxP, smul_zero, zero_add] at he
        have hww : w = u w • x := eq_of_sub_eq_zero he.symm
        exact Submodule.mem_span_singleton.mpr ⟨u w, hww.symm⟩
    exact exercise_70 h u.ker L (exercise_71 h hP u.ker) (hP u.ker) hzero z
  apply ContinuousLinearMap.ext
  intro y
  have hm : y - f y • x ∈ f.ker := by
    change f (y - f y • x) = 0
    rw [map_sub, map_smul, smul_eq_mul, hfx, mul_one, sub_self]
  have he : g (y - f y • x) = 0 :=
    (hker g hg hgx _).mpr ((hker f hf hfx _).mp hm)
  rw [map_sub, map_smul, smul_eq_mul, hgx, mul_one] at he
  exact (sub_eq_zero.mp he).symm

private theorem eq_one_of_re_eq_one_of_norm_le_one {z : ℂ}
    (hr : z.re = 1) (hn : ‖z‖ ≤ 1) : z = 1 := by
  have hnorm : ‖z‖ = 1 := le_antisymm hn (hr ▸ Complex.re_le_norm z)
  have hi : z.im = 0 := Complex.abs_re_eq_norm.mp (by rw [hr, abs_one, hnorm])
  exact Complex.ext (hr.trans Complex.one_re.symm) (hi.trans Complex.one_im.symm)

/-- **Exercise 77(b)** of [benIsrael2003generalized], Chapter 3.
The dual norm of an essentially strictly convex projective norm is
essentially strictly convex. -/
theorem exercise_77_dual_strictConvex (h : essentiallyStrictlyConvex E)
    (hP : IsProjectiveNorm (E := E)) : essentiallyStrictlyConvex (StrongDual ℂ E) := by
  apply (essentiallyStrictlyConvex_iff _).mpr
  apply StrictConvexSpace.of_norm_combo_lt_one
  intro f g hf hg hne
  let a : ℝ := 1 / 2
  refine ⟨a, a, by norm_num [a], ?_⟩
  let k := a • f + a • g
  change ‖k‖ < 1
  have hk : ‖k‖ ≤ 1 := by
    dsimp only [k]
    calc
      _ ≤ ‖a • f‖ + ‖a • g‖ := norm_add_le _ _
      _ = 1 := by rw [norm_smul, norm_smul, hf, hg]; norm_num [a]
  refine lt_of_le_of_ne hk fun he => ?_
  have hk₀ : k ≠ 0 := by intro hz; simp [hz] at he
  obtain ⟨x, hx, hkx⟩ := exercise_59_dual_attainment hk₀
  rw [he, Complex.ofReal_one] at hkx
  have hpair : (a : ℂ) * f x + (a : ℂ) * g x = 1 := hkx
  have hpairR : a * (f x).re + a * (g x).re = 1 := by
    simpa only [Complex.add_re, Complex.re_ofReal_mul, Complex.one_re] using
      congrArg Complex.re hpair
  have hfn : ‖f x‖ ≤ 1 := by simpa only [hf, hx, one_mul] using f.le_opNorm x
  have hgn : ‖g x‖ ≤ 1 := by simpa only [hg, hx, one_mul] using g.le_opNorm x
  have hfr := (Complex.re_le_norm (f x)).trans hfn
  have hgr := (Complex.re_le_norm (g x)).trans hgn
  dsimp [a] at hpairR
  have hf₁ : f x = 1 := eq_one_of_re_eq_one_of_norm_le_one (by linarith) hfn
  have hg₁ : g x = 1 := eq_one_of_re_eq_one_of_norm_le_one (by linarith) hgn
  exact hne (eq_of_norming_functional_projective h hP hx hf hg hf₁ hg₁)

/-- **Exercise 77(c)** of [benIsrael2003generalized], Chapter 3.
Projectivity passes to the dual norm. -/
theorem exercise_77_dual_projective (h : essentiallyStrictlyConvex E)
    (hP : IsProjectiveNorm (E := E)) : IsProjectiveNorm (E := StrongDual ℂ E) := by
  let : FiniteDimensional ℂ (StrongDual ℂ E) :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E).finiteDimensional
  let hD := exercise_77_dual_strictConvex h hP
  intro M f
  let N := M.strongDualCoannihilator
  have hNM : N.strongDualAnnihilator = M := by
    rw [Submodule.strongDualAnnihilator_strongDualCoannihilator,
      M.closed_of_finiteDimensional.submodule_topologicalClosure_eq]
  obtain ⟨L, hL⟩ := (corollary_5 h N).1.mp (exercise_71 h hP N)
  have hNL := exercise_70 h N L (exercise_71 h hP N) (hP N) hL
  let T := additiveMetricProjection h L (exercise_71 h hP L)
  have hker : T.ker = N := by ext x; exact (hNL x).symm
  have hproj := (exercise_76 h hD L (exercise_71 h hP L)).2 f
  change definition_1 T.ker.strongDualAnnihilator f = mixedNormDualAdjoint T f at hproj
  rw [hker, hNM] at hproj
  rw [hproj]
  have hnorm : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one fun x => by
    change ‖definition_1 L x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using hP L x
  have he := (mixedNormDualAdjoint T).le_opNorm f
  rw [← exercise_67 T] at he
  exact he.trans ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _))

end

end DualProjectiveExercises

section LinearInverseExercises

open Set Module

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The two-norm inverse as a continuous linear map, when the range and
kernel projectors are additive. -/
noncomputable def linearTwoNormInverse (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) (A : E →ₗ[ℂ] F)
    (hR : ∀ y z, definition_1 A.range (y + z) =
      definition_1 A.range y + definition_1 A.range z)
    (hK : ∀ x z, definition_1 A.ker (x + z) =
      definition_1 A.ker x + definition_1 A.ker z) : F →L[ℂ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := definition_2 A
      map_add' := (theorem_12 hα hβ A).2.1 hR hK
      map_smul' := (theorem_12 hα hβ A).1 }

/-- The underlying function of the linear two-norm inverse. -/
@[simp]
theorem linearTwoNormInverse_apply (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) (A : E →ₗ[ℂ] F)
    (hR : ∀ y z, definition_1 A.range (y + z) =
      definition_1 A.range y + definition_1 A.range z)
    (hK : ∀ x z, definition_1 A.ker (x + z) =
      definition_1 A.ker x + definition_1 A.ker z) (y : F) :
    linearTwoNormInverse hα hβ A hR hK y = definition_2 A y := rfl

omit [FiniteDimensional ℂ F] in
/-- The linear inverse kernel is the zero fiber of the original range projection. -/
theorem linearTwoNormInverse_ker_iff (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) {A : E →ₗ[ℂ] F} {B : F →ₗ[ℂ] E}
    (hB : ∀ y, B y = definition_2 A y) (y : F) :
    y ∈ B.ker ↔ definition_1 A.range y = 0 := by
  rw [LinearMap.mem_ker, hB]
  exact Set.ext_iff.mp (theorem_12 hα hβ A).2.2.1 y

omit [FiniteDimensional ℂ F] in
/-- The linear inverse range is the zero fiber of the original kernel projection. -/
theorem linearTwoNormInverse_range_iff (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) {A : E →ₗ[ℂ] F} {B : F →ₗ[ℂ] E}
    (hB : ∀ y, B y = definition_2 A y) (x : E) :
    x ∈ B.range ↔ definition_1 A.ker x = 0 := by
  have hr : (B.range : Set E) = Set.range (definition_2 A) := by
    ext z
    change z ∈ B.range ↔ z ∈ Set.range (definition_2 A)
    simp only [LinearMap.mem_range, mem_range, hB]
  rw [show x ∈ B.range ↔ x ∈ Set.range (definition_2 A) from Set.ext_iff.mp hr x]
  exact Set.ext_iff.mp (theorem_12 hα hβ A).2.2.2.1 x

omit [FiniteDimensional ℂ F] in
/-- A linear two-norm inverse has the same rank as the original operator. -/
theorem linearTwoNormInverse_finrank_range (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) {A : E →ₗ[ℂ] F} {B : F →ₗ[ℂ] E}
    (hB : ∀ y, B y = definition_2 A y) :
    Module.finrank ℂ B.range = Module.finrank ℂ A.range := by
  let C : B.range →ₗ[ℂ] A.range := A.rangeRestrict.comp B.range.subtype
  have hs : Function.Surjective C := by
    rintro ⟨z, ⟨x, rfl⟩⟩
    refine ⟨⟨B (A x), LinearMap.mem_range_self B (A x)⟩, Subtype.ext ?_⟩
    change A (B (A x)) = A x
    rw [hB, definition_2_apply_left,
      (definition_1_eq_self_iff A.range (A x)).mpr (LinearMap.mem_range_self A x)]
  have hi : Function.Injective C := by
    intro x y he
    have hx : B (A (x : E)) = x.val := by
      rw [hB, definition_2_apply_right hβ,
        (linearTwoNormInverse_range_iff hα hβ hB _).mp x.property, sub_zero]
    have hy : B (A (y : E)) = y.val := by
      rw [hB, definition_2_apply_right hβ,
        (linearTwoNormInverse_range_iff hα hβ hB _).mp y.property, sub_zero]
    have he' : A x.val = A y.val := congrArg Subtype.val he
    exact Subtype.ext (hx.symm.trans ((congrArg B he').trans hy))
  exact (LinearEquiv.ofBijective C ⟨hi, hs⟩).finrank_eq

/-- **Exercise 79**, forward implication, of [benIsrael2003generalized], Chapter 3.
For projective norms the inverse is linear, and its inverse with the
two spaces exchanged recovers the original operator. -/
theorem exercise_79_of_projective (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) (hαP : IsProjectiveNorm (E := F))
    (hβP : IsProjectiveNorm (E := E)) (A : E →ₗ[ℂ] F) :
    ∃ B : F →ₗ[ℂ] E, (∀ y, B y = definition_2 A y) ∧
      ∀ x, definition_2 B x = A x := by
  let B := (linearTwoNormInverse hα hβ A
    (exercise_71 hα hαP A.range) (exercise_71 hβ hβP A.ker)).toLinearMap
  have hB (y : F) : B y = definition_2 A y := rfl
  have hR := linearTwoNormInverse_range_iff hα hβ hB
  have hK := linearTwoNormInverse_ker_iff hα hβ hB
  have hEK := exercise_70 hβ A.ker B.range (exercise_71 hβ hβP A.ker) (hβP A.ker) hR
  have hFR := exercise_70 hα A.range B.ker (exercise_71 hα hαP A.range) (hαP A.range) hK
  have hE := (exercise_72 hβ A.ker B.range hR).mp hEK
  have hF := (exercise_72 hα A.range B.ker hK).mp hFR
  refine ⟨B, hB, fun x => (exercise_78 hα B A ?_ ?_
    (linearTwoNormInverse_finrank_range hα hβ hB).symm x).symm⟩
  · intro z
    rw [hB, definition_2_apply_right hβ]
    symm
    rw [eq_sub_iff_add_eq]
    exact (add_comm _ _).trans (hE z)
  · intro y
    rw [hB, definition_2_apply_left, eq_sub_iff_add_eq]
    exact hF y

end

end LinearInverseExercises

section InvolutionConverseExercises

open Set Module
open scoped Pointwise

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem projective_of_finrank_le_one (hd : Module.finrank ℂ E ≤ 1) :
    IsProjectiveNorm (E := E) := by
  intro L x
  by_cases hL : L = ⊥
  · have h := definition_1_mem L x
    rw [hL, Submodule.mem_bot] at h
    rw [hL, h, norm_zero]
    exact norm_nonneg _
  · have hfin : Module.finrank ℂ L ≠ 0 := fun he => hL (Submodule.finrank_eq_zero.mp he)
    have htop : L = ⊤ := Submodule.eq_top_of_finrank_eq (by
      have := L.finrank_le
      omega)
    rw [(definition_1_eq_self_iff L x).mpr (htop ▸ trivial)]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem exists_linearMap_range_eq_of_finrank_one [Nontrivial E]
    (L : Submodule ℂ F) (hL : Module.finrank ℂ L = 1) :
    ∃ A : E →ₗ[ℂ] F, A.range = L := by
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  obtain ⟨u, hu, hu₀⟩ := L.ne_bot_iff.mp (by intro he; rw [he, finrank_bot] at hL; omega)
  obtain ⟨f, _, hfw⟩ := exists_dual_vector ℂ w (norm_ne_zero_iff.mpr hw)
  have hf : f w ≠ 0 := hfw.symm ▸ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hs : Function.Surjective f.toLinearMap := by
    intro c
    refine ⟨(c / f w) • w, ?_⟩
    change f ((c / f w) • w) = c
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf]
  let A := f.toLinearMap.smulRight u
  refine ⟨A, ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact L.smul_mem (f x) hu
  · rw [eq_span_singleton_of_mem_of_finrank_eq_one hL hu hu₀]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨y, hy⟩ := hs c
    exact ⟨y, by change f.toLinearMap y • u = c • u; rw [hy]⟩

omit [FiniteDimensional ℂ F] in
private theorem exists_linearMap_ker_eq_of_codim_one [Nontrivial F]
    (L : Submodule ℂ E) (hL : Module.finrank ℂ L + 1 = Module.finrank ℂ E) :
    ∃ A : E →ₗ[ℂ] F, A.ker = L := by
  obtain ⟨u, hu⟩ := exists_ne (0 : F)
  have hdim : Module.finrank ℂ (E ⧸ L) = Module.finrank ℂ ℂ := by
    rw [finrank_self]
    have := L.finrank_quotient_add_finrank
    omega
  let e := LinearEquiv.ofFinrankEq (E ⧸ L) ℂ hdim
  let f := e.toLinearMap.comp L.mkQ
  have hf : f.ker = L := by
    ext x
    change e (L.mkQ x) = 0 ↔ x ∈ L
    rw [← e.map_zero, e.injective.eq_iff]
    exact Submodule.Quotient.mk_eq_zero L
  refine ⟨f.smulRight u, ?_⟩
  ext x
  change f x • u = 0 ↔ x ∈ L
  simp only [smul_eq_zero, hu, or_false]
  exact (show f x = 0 ↔ x ∈ f.ker from Iff.rfl).trans (Set.ext_iff.mp (congrArg
    (fun L : Submodule ℂ E => (L : Set E)) hf) x)

/-- The two projections and their reciprocal zero fibers forced by a
linear inverse whose two-norm inverse recovers the original operator. -/
theorem projection_reciprocity_of_twoNormInverse_involution
    (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (B : F →ₗ[ℂ] E)
    (hB : ∀ y, B y = definition_2 A y) (hA : ∀ x, definition_2 B x = A x) :
    ((∀ y z, definition_1 A.range (y + z) =
        definition_1 A.range y + definition_1 A.range z) ∧
      ∀ N : Submodule ℂ F, (∀ y, y ∈ N ↔ definition_1 A.range y = 0) →
        ∀ y, y ∈ A.range ↔ definition_1 N y = 0) ∧
    ((∀ x z, definition_1 A.ker (x + z) =
        definition_1 A.ker x + definition_1 A.ker z) ∧
      ∀ N : Submodule ℂ E, (∀ x, x ∈ N ↔ definition_1 A.ker x = 0) →
        ∀ x, x ∈ A.ker ↔ definition_1 N x = 0) := by
  have hR := linearTwoNormInverse_range_iff hα hβ hB
  have hK := linearTwoNormInverse_ker_iff hα hβ hB
  have hAB (y : F) : A (B y) = definition_1 A.range y := by
    rw [hB, definition_2_apply_left]
  have hBA (x : E) : B (A x) = definition_1 B.range x := by
    rw [← hA, definition_2_apply_left]
  have hF (y : F) : definition_1 A.range y + definition_1 B.ker y = y := by
    rw [← hAB, ← hA, definition_2_apply_right hα, sub_add_cancel]
  have hE (x : E) : definition_1 A.ker x + definition_1 B.range x = x := by
    rw [← hBA, hB, definition_2_apply_right hβ, add_sub_cancel]
  refine ⟨⟨fun y z => ?_, fun N hN => ?_⟩, ⟨fun x z => ?_, fun N hN => ?_⟩⟩
  · rw [← hAB, ← hAB, ← hAB, map_add, map_add]
  · have he : N = B.ker := by ext y; exact (hN y).trans (hK y).symm
    exact he.symm ▸ (exercise_72 hα A.range B.ker hK).mpr hF
  · have he (w : E) : definition_1 A.ker w = w - B (A w) := by
      rw [hB, definition_2_apply_right hβ, sub_sub_cancel]
    rw [he, he, he, map_add, map_add, add_sub_add_comm]
  · have he : N = B.range := by ext x; exact (hN x).trans (hR x).symm
    exact he.symm ▸ (exercise_72 hβ A.ker B.range hR).mpr hE

/-- **Exercise 79** of [benIsrael2003generalized], Chapter 3.
For two nonzero spaces the two-norm inversion is linear and involutive
for every operator exactly when both norms are projective. -/
theorem exercise_79 [Nontrivial E] [Nontrivial F]
    (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E) :
    (∀ A : E →ₗ[ℂ] F, ∃ B : F →ₗ[ℂ] E, (∀ y, B y = definition_2 A y) ∧
      ∀ x, definition_2 B x = A x) ↔ IsProjectiveNorm (E := F) ∧ IsProjectiveNorm (E := E) := by
  constructor
  · intro hh
    constructor
    · by_cases hd : Module.finrank ℂ F ≤ 1
      · exact projective_of_finrank_le_one hd
      apply exercise_73 hα 1 le_rfl (Nat.lt_of_not_ge hd)
      intro L hL
      obtain ⟨A, hA⟩ := exists_linearMap_range_eq_of_finrank_one (E := E) L hL
      obtain ⟨B, hB, he⟩ := hh A
      exact hA ▸ (projection_reciprocity_of_twoNormInverse_involution hα hβ A B hB he).1
    · by_cases hd : Module.finrank ℂ E ≤ 1
      · exact projective_of_finrank_le_one hd
      apply exercise_73 hβ (Module.finrank ℂ E - 1) (by omega) (by omega)
      intro L hL
      obtain ⟨A, hA⟩ := exists_linearMap_ker_eq_of_codim_one (F := F) L (by omega)
      obtain ⟨B, hB, he⟩ := hh A
      exact hA ▸ (projection_reciprocity_of_twoNormInverse_involution hα hβ A B hB he).2
  · rintro ⟨hαP, hβP⟩ A
    exact exercise_79_of_projective hα hβ hαP hβP A

end

end InvolutionConverseExercises

section AdjointInverseExercises

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem range_mixedNormDualAdjoint_eq_map (A : E →L[ℂ] F) :
    (mixedNormDualAdjoint A).toLinearMap.range = A.toLinearMap.dualMap.range.map
      (LinearMap.toContinuousLinearMap : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g.toLinearMap, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨LinearMap.toContinuousLinearMap g, rfl⟩

/-- A continuous linear operator and its adjoint have the same finite rank. -/
theorem finrank_range_mixedNormDualAdjoint (A : E →L[ℂ] F) :
    Module.finrank ℂ (mixedNormDualAdjoint A).toLinearMap.range =
      Module.finrank ℂ A.toLinearMap.range := by
  let e : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E := LinearMap.toContinuousLinearMap
  rw [range_mixedNormDualAdjoint_eq_map A]
  exact (Submodule.equivMapOfInjective e.toLinearMap e.injective
    A.toLinearMap.dualMap.range).finrank_eq.symm.trans
      A.toLinearMap.finrank_range_dualMap_eq_finrank_range

private theorem range_mixedNormDualAdjoint (A : E →L[ℂ] F) :
    (mixedNormDualAdjoint A).toLinearMap.range = A.ker.strongDualAnnihilator := by
  rw [range_mixedNormDualAdjoint_eq_map A, LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Submodule.mem_strongDualAnnihilator.mpr ((A.ker.mem_dualAnnihilator g).mp hg)
  · intro hf
    exact ⟨f.toLinearMap, (A.ker.mem_dualAnnihilator f.toLinearMap).mpr
      (Submodule.mem_strongDualAnnihilator.mp hf), rfl⟩

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem ker_mixedNormDualAdjoint (A : E →L[ℂ] F) :
    (mixedNormDualAdjoint A).ker = A.toLinearMap.range.strongDualAnnihilator := by
  ext f
  change mixedNormDualAdjoint A f = 0 ↔ _
  rw [Submodule.mem_strongDualAnnihilator]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact congrArg (fun g : StrongDual ℂ E => g x) h
  · intro h
    exact ContinuousLinearMap.ext fun x => h (A x) (LinearMap.mem_range_self A.toLinearMap x)

/-- **Exercise 80**, with the projectivity hypotheses used in its proof,
of [benIsrael2003generalized], Chapter 3. The adjoint of the linear
two-norm inverse is the two-norm inverse of the adjoint in the dual norms. -/
theorem exercise_80 (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    (hαP : IsProjectiveNorm (E := F)) (hβP : IsProjectiveNorm (E := E))
    (A : E →L[ℂ] F) :
    let B := linearTwoNormInverse hα hβ A.toLinearMap
      (exercise_71 hα hαP A.toLinearMap.range) (exercise_71 hβ hβP A.ker)
    ∀ f, mixedNormDualAdjoint B f = definition_2 (mixedNormDualAdjoint A).toLinearMap f := by
  intro B
  let : FiniteDimensional ℂ (StrongDual ℂ E) :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E).finiteDimensional
  let : FiniteDimensional ℂ (StrongDual ℂ F) :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℂ F ≃ₗ[ℂ] StrongDual ℂ F).finiteDimensional
  have hαD := exercise_77_dual_strictConvex hα hαP
  have hβD := exercise_77_dual_strictConvex hβ hβP
  have hB (y : F) : B.toLinearMap y = definition_2 A.toLinearMap y := rfl
  have hR := linearTwoNormInverse_range_iff hα hβ hB
  have hK := linearTwoNormInverse_ker_iff hα hβ hB
  let L := B.toLinearMap.range
  let N := B.ker
  have hEK := exercise_70 hβ A.ker L (exercise_71 hβ hβP A.ker) (hβP A.ker) hR
  have hFR := exercise_70 hα A.toLinearMap.range N
    (exercise_71 hα hαP A.toLinearMap.range) (hαP A.toLinearMap.range) hK
  have hE := (exercise_72 hβ A.ker L hR).mp hEK
  have hF := (exercise_72 hα A.toLinearMap.range N hK).mp hFR
  let P := additiveMetricProjection hβ L (exercise_71 hβ hβP L)
  let S := additiveMetricProjection hα N (exercise_71 hα hαP N)
  have hPker : P.ker = A.ker := by ext x; exact (hEK x).symm
  have hSker : S.ker = A.toLinearMap.range := by ext y; exact (hFR y).symm
  have hP (x : E) : P x = B (A x) := by
    change definition_1 L x = B.toLinearMap (A.toLinearMap x)
    rw [hB, definition_2_apply_right hβ, eq_sub_iff_add_eq]
    exact (add_comm _ _).trans (hE x)
  have hS (y : F) : S y = y - A (B y) := by
    change definition_1 N y = y - A.toLinearMap (B.toLinearMap y)
    rw [hB, definition_2_apply_left, eq_sub_iff_add_eq]
    exact (add_comm _ _).trans (hF y)
  apply exercise_78 hαD (mixedNormDualAdjoint A).toLinearMap (mixedNormDualAdjoint B).toLinearMap
  · intro f
    have hproj := (exercise_76 hβ hβD L (exercise_71 hβ hβP L)).2 f
    change definition_1 P.ker.strongDualAnnihilator f = mixedNormDualAdjoint P f at hproj
    rw [hPker] at hproj
    rw [range_mixedNormDualAdjoint A, hproj]
    exact ContinuousLinearMap.ext fun x => congrArg f (hP x).symm
  · intro g
    have hproj := (exercise_76 hα hαD N (exercise_71 hα hαP N)).2 g
    change definition_1 S.ker.strongDualAnnihilator g = mixedNormDualAdjoint S g at hproj
    rw [hSker] at hproj
    rw [ker_mixedNormDualAdjoint A, hproj]
    apply ContinuousLinearMap.ext
    intro y
    change g (A (B y)) = g y - g (S y)
    rw [hS, map_sub, sub_sub_cancel]
  · rw [finrank_range_mixedNormDualAdjoint, finrank_range_mixedNormDualAdjoint]
    exact linearTwoNormInverse_finrank_range hα hβ hB

end

end AdjointInverseExercises

section DualProjectiveBoundExercises

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem isContinuousHomogeneous_metricProjection (h : essentiallyStrictlyConvex E)
    (L : Submodule ℂ E) : IsContinuousHomogeneous (definition_1 L) :=
  ⟨continuous_definition_1 h L, definition_1_smul h L⟩

/-- The projective bound controls each projector, including the
zero and identity projections. -/
theorem norm_projection_le_projectiveBound_mul (h : essentiallyStrictlyConvex E)
    (hd : 2 ≤ Module.finrank ℂ E) (L : Submodule ℂ E) (x : E) :
    ‖definition_1 L x‖ ≤ projectiveBound (E := E) * ‖x‖ := by
  obtain ⟨M, hM, hx⟩ := exists_finrank_eq_metricProjection h L x 1 le_rfl (by omega)
  have hb : BddAbove ((fun S : Submodule ℂ E => mixedOperatorNorm (definition_1 S)) ''
      {S | 1 ≤ Module.finrank ℂ S ∧ Module.finrank ℂ S < Module.finrank ℂ E}) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨S, _, rfl⟩
    exact (mixedOperatorNorm_le_iff (isContinuousHomogeneous_metricProjection h S)
      (by norm_num)).mpr (definition_1_norm_le S)
  have hm : mixedOperatorNorm (definition_1 M) ≤ projectiveBound (E := E) :=
    le_csSup hb ⟨M, ⟨by omega, by omega⟩, rfl⟩
  rw [← hx]
  exact (norm_homogeneous_apply_le (isContinuousHomogeneous_metricProjection h M)
    x).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _))

private theorem projectiveBound_le_dual (h : essentiallyStrictlyConvex E)
    (hD : essentiallyStrictlyConvex (StrongDual ℂ E)) (hd : 2 ≤ Module.finrank ℂ E) :
    projectiveBound (E := E) ≤ projectiveBound (E := StrongDual ℂ E) := by
  let e : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E := LinearMap.toContinuousLinearMap
  let : FiniteDimensional ℂ (StrongDual ℂ E) := e.finiteDimensional
  have hdD : 2 ≤ Module.finrank ℂ (StrongDual ℂ E) := by
    rw [← e.finrank_eq, Subspace.dual_finrank_eq]
    exact hd
  obtain ⟨⟨L, hdimL, hL⟩, _, _⟩ :=
    exercise_68 h (Module.finrank ℂ E - 1) (by omega) (by omega)
  obtain ⟨_, hD₁, _⟩ := exercise_68 hD 1 le_rfl (by omega)
  let ha := corollary_6 h L (by omega)
  let P := additiveMetricProjection h L ha
  let Q := mixedNormDualAdjoint P
  have hQ (f : StrongDual ℂ E) :
      definition_1 P.ker.strongDualAnnihilator f = Q f := (exercise_76 h hD L ha).2 f
  have he : ‖P‖ = projectiveBound (E := E) :=
    (mixedOperatorNorm_eq_opNorm P).symm.trans hL
  rw [← he, exercise_67 P]
  change ‖Q‖ ≤ projectiveBound (E := StrongDual ℂ E)
  apply Q.opNorm_le_bound (zero_le_one.trans hD₁)
  intro f
  rw [← hQ]
  exact norm_projection_le_projectiveBound_mul hD hdD P.ker.strongDualAnnihilator f

private theorem hyperplane_eq_annihilator_line
    [FiniteDimensional ℂ (StrongDual ℂ E)]
    (M : Submodule ℂ (StrongDual ℂ E))
    (hM : Module.finrank ℂ M + 1 = Module.finrank ℂ (StrongDual ℂ E)) :
    ∃ x : E, x ≠ 0 ∧ M = (ℂ ∙ x).strongDualAnnihilator := by
  let D := StrongDual ℂ E
  have hr : Module.finrank ℂ (D ⧸ M) = Module.finrank ℂ ℂ := by
    rw [Module.finrank_self]
    change Module.finrank ℂ ((StrongDual ℂ E) ⧸ M) = 1
    have := M.finrank_quotient_add_finrank
    omega
  let e := LinearEquiv.ofFinrankEq (D ⧸ M) ℂ hr
  let g : StrongDual ℂ D := LinearMap.toContinuousLinearMap (e.toLinearMap.comp M.mkQ)
  let j := NormedSpace.doubleDualIsometryEquiv ℂ E
  let x : E := j.symm g
  have hx (f : D) : f x = g f := congrArg (fun z : StrongDual ℂ D => z f) (j.apply_symm_apply g)
  have hg (f : D) : g f = 0 ↔ f ∈ M := by
    change e (M.mkQ f) = 0 ↔ f ∈ M
    rw [← e.map_zero, e.injective.eq_iff]
    exact Submodule.Quotient.mk_eq_zero M
  have hx₀ : x ≠ 0 := by
    intro he
    obtain ⟨f, hf⟩ := M.mkQ_surjective (e.symm 1)
    have hval : g f = 1 := by
      change e (M.mkQ f) = 1
      rw [hf, e.apply_symm_apply]
    rw [← hx, he, map_zero] at hval
    exact (zero_ne_one hval)
  refine ⟨x, hx₀, ?_⟩
  ext f
  rw [Submodule.mem_strongDualAnnihilator, ← hg, ← hx]
  constructor
  · intro hz y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [hz]
  · intro hz
    exact hz x (Submodule.mem_span_singleton_self _)

private theorem exists_metricProjection_ker_line (h : essentiallyStrictlyConvex E)
    {u : E} (hu : u ≠ 0) :
    ∃ L : Submodule ℂ E, ∃ ha : ∀ x y, definition_1 L (x + y) =
        definition_1 L x + definition_1 L y,
      (additiveMetricProjection h L ha).ker = ℂ ∙ u := by
  obtain ⟨f, hf, hfu⟩ := exists_dual_vector ℂ u (norm_ne_zero_iff.mpr hu)
  let L := f.ker
  have hf₀ : f u ≠ 0 := hfu.symm ▸ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have hp : definition_1 L u = 0 :=
    (exercise_75 h L hu).mpr ⟨f, hf, hfu, fun x hx => hx⟩
  have hker (x : E) : x ∈ ℂ ∙ u ↔ definition_1 L x = 0 := by
    constructor
    · rintro hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [definition_1_smul h L, hp, smul_zero]
    · intro hx
      let c := f x / f u
      let y := x - c • u
      have hy : y ∈ L := by
        change f (x - c • u) = 0
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hf₀, sub_self]
      have he := definition_1_add_mem h L (c • u) hy
      rw [show c • u + y = x by dsimp [y]; abel,
        definition_1_smul h L, hp, smul_zero, zero_add, hx] at he
      exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp he.symm).symm⟩
  have ha := (corollary_5 h L).1.mpr ⟨ℂ ∙ u, hker⟩
  exact ⟨L, ha, by ext x; exact (hker x).symm⟩

/-- **Exercise 77(a)** of [benIsrael2003generalized], Chapter 3.
If both the norm and its dual are essentially strictly convex, their
projective bounds are equal. -/
theorem exercise_77 (h : essentiallyStrictlyConvex E)
    (hD : essentiallyStrictlyConvex (StrongDual ℂ E)) (hd : 2 ≤ Module.finrank ℂ E) :
    projectiveBound (E := E) = projectiveBound (E := StrongDual ℂ E) := by
  let e : Module.Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E := LinearMap.toContinuousLinearMap
  let : FiniteDimensional ℂ (StrongDual ℂ E) := e.finiteDimensional
  let d := Module.finrank ℂ (StrongDual ℂ E)
  have hdD : 2 ≤ d := by
    dsimp only [d]
    rw [← e.finrank_eq, Subspace.dual_finrank_eq]
    exact hd
  obtain ⟨⟨M, hMd, hM⟩, _, _⟩ := exercise_68 hD (d - 1) (by omega) (by omega)
  have hcodim : Module.finrank ℂ M + 1 = Module.finrank ℂ (StrongDual ℂ E) := by omega
  obtain ⟨u, hu, huM⟩ := hyperplane_eq_annihilator_line M hcodim
  obtain ⟨L, ha, hker⟩ := exists_metricProjection_ker_line h hu
  let P := additiveMetricProjection h L ha
  let Q := mixedNormDualAdjoint P
  have hnorm (f : StrongDual ℂ E) : definition_1 M f = Q f := by
    have he := (exercise_76 h hD L ha).2 f
    change definition_1 P.ker.strongDualAnnihilator f = Q f at he
    rw [show P.ker = ℂ ∙ u from hker, ← huM] at he
    exact he
  have hQ : ‖Q‖ = projectiveBound (E := StrongDual ℂ E) := by
    rw [← hM, ← mixedOperatorNorm_eq_opNorm Q]
    exact congrArg mixedOperatorNorm (funext (fun f => (hnorm f).symm))
  refine le_antisymm (projectiveBound_le_dual h hD hd) ?_
  rw [← hQ, ← exercise_67 P]
  obtain ⟨_, h₁, _⟩ := exercise_68 h 1 le_rfl (by omega)
  apply P.opNorm_le_bound (zero_le_one.trans h₁)
  exact norm_projection_le_projectiveBound_mul h hd L

end

end DualProjectiveBoundExercises

section RankDistanceExercises

open Set Module

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The two-norm generalized inverse is continuous and complex homogeneous. -/
theorem definition_2_isContinuousHomogeneous (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) (A : E →ₗ[ℂ] F) :
    IsContinuousHomogeneous (definition_2 A) := by
  refine ⟨?_, (theorem_12 hα hβ A).1⟩
  unfold definition_2
  have hf : Continuous (fun y => (exists_linearInnerInverse A).choose (definition_1 A.range y)) :=
    (LinearMap.continuous_of_finiteDimensional _).comp (continuous_definition_1 hα A.range)
  exact hf.sub ((continuous_definition_1 hβ A.ker).comp hf)

private theorem norm_twoNormInverse_pos (hα : essentiallyStrictlyConvex F)
    (hβ : essentiallyStrictlyConvex E) {A : E →ₗ[ℂ] F} (hA : A ≠ 0) :
    0 < mixedOperatorNorm (definition_2 A) := by
  have h := definition_2_isContinuousHomogeneous hα hβ A
  refine lt_of_le_of_ne (mixedOperatorNorm_nonneg h.continuous) (Ne.symm fun he => hA ?_)
  have hz := (mixedOperatorNorm_eq_zero_iff h).mp he
  apply LinearMap.ext
  intro x
  have hval := definition_2_apply_left A (A x)
  rw [congrFun hz (A x),
    (definition_1_eq_self_iff A.range _).mpr (LinearMap.mem_range_self A x)] at hval
  change A 0 = A x at hval
  rw [map_zero] at hval
  exact hval.symm

/-- Distance in the mixed operator norm to the set of operators of smaller rank. -/
noncomputable def rankLossDistance (A : E →ₗ[ℂ] F) : ℝ :=
  sInf ((fun X : E →L[ℂ] F => ‖X‖) ''
    {X : E →L[ℂ] F | Module.finrank ℂ (A + X.toLinearMap).range <
      Module.finrank ℂ A.range})

/-- **Exercise 81**, upper bound in (153), of [benIsrael2003generalized],
Chapter 3. A rank-one perturbation lowers the rank and its norm is bounded
by the range projector norm divided by the norm of the two-norm inverse. -/
theorem exercise_81_upper (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    {A : E →ₗ[ℂ] F} (hA : A ≠ 0) :
    rankLossDistance A ≤ mixedOperatorNorm (definition_1 A.range) /
      mixedOperatorNorm (definition_2 A) := by
  have hM := norm_twoNormInverse_pos hα hβ hA
  have hnon : Nontrivial F := by
    by_contra! he
    let : Subsingleton F := he
    exact hA (Subsingleton.elim _ _)
  let : Nontrivial F := hnon
  obtain ⟨y, hy, hynorm⟩ := (exercise_66 _ (definition_2_isContinuousHomogeneous hα hβ A)).2 hnon
  let x := definition_2 A y
  have hx : x ≠ 0 := by
    have hxp : 0 < ‖x‖ := hynorm.symm ▸ hM
    exact norm_pos_iff.mp hxp
  have hxK : definition_1 A.ker x = 0 := definition_2_kernelProjection hβ A y
  obtain ⟨f, hf, hfx, hfk⟩ := (exercise_75 hβ A.ker hx).mp hxK
  let K : E →L[ℂ] F := LinearMap.toContinuousLinearMap
    (f.toLinearMap.smulRight ((-((‖x‖ : ℂ)⁻¹)) • A x))
  have hK (z : E) : K z = -(f z / (‖x‖ : ℂ)) • A x := by
    change f z • (-((‖x‖ : ℂ)⁻¹) • A x) = _
    rw [smul_smul, mul_neg, div_eq_mul_inv]
  have hxK₀ : (A + K.toLinearMap) x = 0 := by
    change A x + K x = 0
    rw [hK, hfx, div_self (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)),
      neg_one_smul, add_neg_cancel]
  have hl : A.ker ≤ (A + K.toLinearMap).ker := by
    intro z hz
    change A z + K z = 0
    rw [show A z = 0 from hz, hK, hfk z hz, zero_div, neg_zero, zero_smul, add_zero]
  have hlt : A.ker < (A + K.toLinearMap).ker := by
    refine lt_of_le_of_ne hl fun h => hx ?_
    have hm : x ∈ (A + K.toLinearMap).ker := hxK₀
    have hxfix := (definition_1_eq_self_iff A.ker x).mpr (h.symm ▸ hm)
    exact hxfix.symm.trans hxK
  have hrank : Module.finrank ℂ (A + K.toLinearMap).range < Module.finrank ℂ A.range := by
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt
    have ha := A.finrank_range_add_finrank_ker
    have hk := (A + K.toLinearMap).finrank_range_add_finrank_ker
    omega
  have hnorm : ‖K‖ ≤ ‖A x‖ / ‖x‖ := by
    apply K.opNorm_le_bound (div_nonneg (norm_nonneg _) (norm_nonneg _))
    intro z
    rw [hK, norm_smul, norm_neg, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _)]
    have hle : ‖f z‖ ≤ ‖z‖ := by simpa only [hf, one_mul] using f.le_opNorm z
    calc
      _ ≤ ‖z‖ / ‖x‖ * ‖A x‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hle (norm_nonneg _))
          (norm_nonneg _)
      _ = ‖A x‖ / ‖x‖ * ‖z‖ := by ring
  have hPx : ‖A x‖ ≤ mixedOperatorNorm (definition_1 A.range) := by
    change ‖A (definition_2 A y)‖ ≤ _
    rw [definition_2_apply_left]
    have he := norm_homogeneous_apply_le
      ⟨continuous_definition_1 hα A.range, definition_1_smul hα A.range⟩ y
    simpa only [hy, mul_one] using he
  have hset : BddBelow ((fun X : E →L[ℂ] F => ‖X‖) ''
      {X : E →L[ℂ] F | Module.finrank ℂ (A + X.toLinearMap).range <
        Module.finrank ℂ A.range}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨X, _, rfl⟩
    exact norm_nonneg _
  refine (csInf_le hset ⟨K, hrank, rfl⟩).trans (hnorm.trans ?_)
  change ‖A x‖ / ‖definition_2 A y‖ ≤ _
  rw [hynorm]
  exact div_le_div_of_nonneg_right hPx hM.le


/-- The lower bound in (153) applies whenever the original range
projection is linear and contractive. -/
theorem exercise_81_lower_of_contractive_rangeProjection
    (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    {A : E →ₗ[ℂ] F} (hA : A ≠ 0)
    (P : F →ₗ[ℂ] F) (hP : ∀ y, P y = definition_1 A.range y)
    (hPc : ∀ y, ‖P y‖ ≤ ‖y‖) :
    (mixedOperatorNorm (definition_2 A))⁻¹ ≤ rankLossDistance A := by
  have hM := norm_twoNormInverse_pos hα hβ hA
  let S := ((fun X : E →L[ℂ] F => ‖X‖) ''
    {X : E →L[ℂ] F | Module.finrank ℂ (A + X.toLinearMap).range <
      Module.finrank ℂ A.range})
  have hRn : A.range ≠ ⊥ := fun h => hA (LinearMap.range_eq_bot.mp h)
  have hRpos : 0 < Module.finrank ℂ A.range := by
    have hn : Module.finrank ℂ A.range ≠ 0 := fun h => hRn (Submodule.finrank_eq_zero.mp h)
    omega
  have hne : S.Nonempty := by
    let K : E →L[ℂ] F := LinearMap.toContinuousLinearMap (-A)
    refine ⟨‖K‖, K, ?_, rfl⟩
    change Module.finrank ℂ (A + -A).range < Module.finrank ℂ A.range
    rw [show A + -A = 0 from add_neg_cancel A, LinearMap.range_zero, finrank_bot]
    exact hRpos
  change _ ≤ sInf S
  refine le_csInf hne ?_
  rintro _ ⟨X, hrank, rfl⟩
  let B := A + X.toLinearMap
  let Q : B.range →ₗ[ℂ] A.range :=
    (P.comp B.range.subtype).codRestrict A.range fun z => by
      change P z.val ∈ A.range
      rw [hP]
      exact definition_1_mem _ _
  have hlt : Module.finrank ℂ Q.range < Module.finrank ℂ A.range :=
    Q.finrank_range_le.trans_lt hrank
  have htop : Q.range ≠ ⊤ := fun he => by
    rw [he, finrank_top] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨w, hw⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr htop)
  have hwQ : Q.range.mkQL w ≠ 0 := by
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply]
    exact fun he => hw.2 ((Submodule.Quotient.mk_eq_zero Q.range).mp he)
  let : IsClosed (Q.range : Set A.range) := Q.range.closed_of_finiteDimensional
  obtain ⟨g, hg, hgw⟩ := exists_dual_vector ℂ (Q.range.mkQL w) (norm_ne_zero_iff.mpr hwQ)
  let f : StrongDual ℂ A.range := g.comp Q.range.mkQL
  have hf0 : f ≠ 0 := by
    intro h
    have hwz : f w = 0 := by rw [h, zero_apply]
    change g (Q.range.mkQL w) = 0 at hwz
    rw [hgw] at hwz
    exact (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hwQ)) hwz
  obtain ⟨y, hy, hfy⟩ := exercise_59_dual_attainment hf0
  let x := definition_2 A y.val
  have hAx : A x = y.val := by
    rw [show x = definition_2 A y.val from rfl, definition_2_apply_left]
    exact (definition_1_eq_self_iff _ _).mpr y.property
  let q := Q (B.rangeRestrict x)
  have hfq : f q = 0 := by
    change g (Q.range.mkQL q) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero Q.range).mpr (LinearMap.mem_range_self Q _), map_zero]
  have hPX : P (X x) ∈ A.range := by rw [hP]; exact definition_1_mem _ _
  let z : A.range := ⟨P (X x), hPX⟩
  have heq : q = y + z := by
    apply Subtype.ext
    change P (A x + X x) = y.val + P (X x)
    rw [map_add, hAx, hP y.val, (definition_1_eq_self_iff _ _).mpr y.property]
  have hfz : f z = - (‖f‖ : ℂ) := by
    rw [heq, map_add, hfy] at hfq
    exact eq_neg_of_add_eq_zero_right hfq
  have hzl := f.le_opNorm z
  rw [hfz, norm_neg] at hzl
  have hznorm : ‖(‖f‖ : ℂ)‖ = ‖f‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (ContinuousLinearMap.opNorm_nonneg f)]
  rw [hznorm] at hzl
  have hfpos : 0 < ‖f‖ := by
    have hwf : f w ≠ 0 := by
      change g (Q.range.mkQL w) ≠ 0
      rw [hgw]
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hwQ)
    have hpos := (norm_pos_iff.mpr hwf).trans_le (f.le_opNorm w)
    by_contra! hn
    exact hpos.not_ge (mul_nonpos_of_nonpos_of_nonneg hn (norm_nonneg w))
  have hzineq : ‖f‖ * 1 ≤ ‖f‖ * ‖z‖ := by simpa only [mul_one] using hzl
  have hzn : 1 ≤ ‖z‖ := le_of_mul_le_mul_left hzineq hfpos
  have hzb : ‖z‖ ≤ ‖X‖ * ‖x‖ := (hPc (X x)).trans (X.le_opNorm x)
  have hxb : ‖x‖ ≤ mixedOperatorNorm (definition_2 A) := by
    have h := norm_homogeneous_apply_le (definition_2_isContinuousHomogeneous hα hβ A) y.val
    change ‖y.val‖ = 1 at hy
    simpa only [hy, mul_one] using h
  rw [← one_div, div_le_iff₀ hM]
  exact hzn.trans (hzb.trans (mul_le_mul_of_nonneg_left hxb (norm_nonneg _)))

/-- **Exercise 81**, full-row-rank and projective-output equality cases.
The range projection is contractive in either case and the two bounds
therefore coincide. -/
theorem exercise_81_exact (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    {A : E →ₗ[ℂ] F} (hA : A ≠ 0)
    (hR : A.range = ⊤ ∨ IsProjectiveNorm (E := F)) :
    rankLossDistance A = (mixedOperatorNorm (definition_2 A))⁻¹ := by
  have hP :
      ∃ P : F →ₗ[ℂ] F, (∀ y, P y = definition_1 A.range y) ∧ (∀ y, ‖P y‖ ≤ ‖y‖) := by
    rcases hR with hfull | hproj
    · refine ⟨LinearMap.id, fun y => ((definition_1_eq_self_iff _ _).mpr ?_).symm,
        fun _ => le_rfl⟩
      rw [hfull]
      trivial
    · exact ⟨(additiveMetricProjection hα A.range (exercise_71 hα hproj A.range)).toLinearMap,
        fun _ => rfl, hproj A.range⟩
  obtain ⟨P, hP, hPc⟩ := hP
  have hnorm : mixedOperatorNorm (definition_1 A.range) ≤ 1 := by
    apply (mixedOperatorNorm_le_iff
      ⟨continuous_definition_1 hα A.range, definition_1_smul hα A.range⟩ zero_le_one).mpr
    intro y
    rw [← hP, one_mul]
    exact hPc y
  refine le_antisymm ((exercise_81_upper hα hβ hA).trans ?_)
    (exercise_81_lower_of_contractive_rangeProjection hα hβ hA P hP hPc)
  rw [← one_div]
  exact div_le_div_of_nonneg_right hnorm (norm_twoNormInverse_pos hα hβ hA).le

end

end RankDistanceExercises

section LpProjectionExercises

open Set Finset
open scoped ENNReal

section

/-- Strict convexity of the $p$-th power of the norm of a complex
coordinate for $p>1$. -/
theorem strictConvexOn_complex_norm_rpow (p : ℝ) (hp : 1 < p) :
    StrictConvexOn ℝ (univ : Set ℂ) (fun z => ‖z‖ ^ p) := by
  let : StrictConvexSpace ℝ ℂ := StrictConvexSpace.of_strictConvexOn_norm_rpow
    one_le_two strictConvexOn_norm_rpow_two
  exact strictConvexOn_norm_rpow hp

variable {ι : Type*} [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
private theorem piLp_norm_rpow (hp : 0 < p.toReal) (x : PiLp p fun _ : ι => ℂ) :
    ‖x‖ ^ p.toReal = ∑ i, ‖x i‖ ^ p.toReal := by
  have hsum : 0 ≤ ∑ i, ‖x i‖ ^ p.toReal :=
    sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul hsum, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- Every finite complex $ell^p$ space with $1<p<\infty$ is essentially
strictly convex, as required for its single-valued metric projection. -/
theorem essentiallyStrictlyConvex_piLp (hp : 1 < p.toReal) :
    essentiallyStrictlyConvex (PiLp p fun _ : ι => ℂ) := by
  intro x y hxy he t ht ht'
  have hp₀ : 0 < p.toReal := zero_lt_one.trans hp
  let b := 1 - t
  have hb : 0 < b := sub_pos.mpr ht'
  have htb : t + b = 1 := by dsimp [b]; ring
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (by ext i; exact h i)
  apply (Real.rpow_lt_rpow_iff (norm_nonneg _) (norm_nonneg _) hp₀).mp
  rw [piLp_norm_rpow p hp₀, piLp_norm_rpow p hp₀]
  change (∑ i, ‖(t • x + b • y) i‖ ^ p.toReal) < ∑ i, ‖x i‖ ^ p.toReal
  have he₁ : (∑ i, ‖x i‖ ^ p.toReal) = ∑ i, ‖y i‖ ^ p.toReal := by
    rw [← piLp_norm_rpow p hp₀, ← piLp_norm_rpow p hp₀, he]
  calc
    _ < ∑ i, (t * ‖x i‖ ^ p.toReal + b * ‖y i‖ ^ p.toReal) := by
      refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, mem_univ _, ?_⟩
      · simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
          (strictConvexOn_complex_norm_rpow p.toReal hp).convexOn.2
            (mem_univ (x i)) (mem_univ (y i)) ht.le hb.le htb
      · simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
          (strictConvexOn_complex_norm_rpow p.toReal hp).2
            (mem_univ (x j)) (mem_univ (y j)) hj ht hb htb
    _ = ∑ i, ‖x i‖ ^ p.toReal := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← he₁,
      ← add_mul, htb, one_mul]

end

section SharpBound

open Filter
open scoped Topology Pointwise

private theorem pow_tangent_le_norm_pow {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 ≤ r)
    (z : ℂ) : r ^ n + (n : ℝ) * r ^ (n - 1) * (z.re - r) ≤ ‖z‖ ^ n := by
  let j := fun t : ℝ => t ^ n
  have hc : ConvexOn ℝ (Ici 0) j := (strictConvexOn_pow hn).convexOn
  have hd : HasDerivAt j ((n : ℝ) * r ^ (n - 1)) r := hasDerivAt_pow n r
  have hlin : r ^ n + (n : ℝ) * r ^ (n - 1) * (‖z‖ - r) ≤ ‖z‖ ^ n := by
    rcases lt_trichotomy r ‖z‖ with h | h | h
    · have h₁ := hc.le_slope_of_hasDerivAt hr (norm_nonneg z) h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h₁
      change (n : ℝ) * r ^ (n - 1) * (‖z‖ - r) ≤ ‖z‖ ^ n - r ^ n at h₁
      linarith
    · rw [h, sub_self, mul_zero, add_zero]
    · have h₁ := hc.slope_le_of_hasDerivAt (norm_nonneg z) hr h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at h₁
      change r ^ n - ‖z‖ ^ n ≤ (n : ℝ) * r ^ (n - 1) * (r - ‖z‖) at h₁
      linarith [show (n : ℝ) * r ^ (n - 1) * (‖z‖ - r) =
          -((n : ℝ) * r ^ (n - 1) * (r - ‖z‖)) by ring]
  have hmono : (n : ℝ) * r ^ (n - 1) * (z.re - r) ≤
      (n : ℝ) * r ^ (n - 1) * (‖z‖ - r) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right (Complex.re_le_norm z) r) (by positivity)
  linarith

private theorem piLp_norm_nat_pow {n : ℕ} (hn : 0 < n) (x : PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ) :
    ‖x‖ ^ n = ‖x 0‖ ^ n + ‖x 1‖ ^ n := by
  have he := piLp_norm_rpow (n : ℝ≥0∞)
    (by rw [ENNReal.toReal_natCast]; exact_mod_cast hn) x
  rw [ENNReal.toReal_natCast] at he
  simpa only [Real.rpow_natCast, Fin.sum_univ_two] using he

private theorem sharp_bound_pair {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    letI : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ n by omega)⟩
    ∃ (L : Submodule ℂ (PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ))
      (x : PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ),
      2 * a ≤ ‖definition_1 L x‖ ∧
        ‖x‖ ≤ (2 : ℝ) ^ (1 / (n : ℝ)) * (1 + 2 * a ^ n) := by
  let : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ n by omega)⟩
  let p : ℝ≥0∞ := n
  let E := PiLp p fun _ : Fin 2 => ℂ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hESC : essentiallyStrictlyConvex E := by
    apply essentiallyStrictlyConvex_piLp p
    rw [show p.toReal = (n : ℝ) from ENNReal.toReal_natCast n]
    exact_mod_cast (show 1 < n by omega)
  let r : E := WithLp.toLp p ![(a : ℂ), 1]
  let y : E := WithLp.toLp p ![((2 * a : ℝ) : ℂ), ((-2 * a ^ n : ℝ) : ℂ)]
  let x := y - r
  let L := ℂ ∙ y
  have hproj : definition_1 L x = y := by
    apply (definition_1_eq_iff hESC L x y).mpr
    refine ⟨Submodule.mem_span_singleton_self _, ?_⟩
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (show w ∈ L from hw)
    let z := r + (c - 1) • y
    have h₁ : x - y = -r := by dsimp [x]; abel
    have h₂ : x - c • y = -z := by
      dsimp [x, z]
      rw [sub_smul, one_smul]
      abel
    rw [h₁, h₂, norm_neg, norm_neg]
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by omega : n ≠ 0)).mp
    rw [piLp_norm_nat_pow (by omega : 0 < n), piLp_norm_nat_pow (by omega : 0 < n)]
    have hzi : (z 0).re = a + (c.re - 1) * (2 * a) := by
      change ((a : ℂ) + (c - 1) * ((2 * a : ℝ) : ℂ)).re = _
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hzj : (z 1).re = 1 + (c.re - 1) * (-2 * a ^ n) := by
      change ((1 : ℂ) + (c - 1) * ((-2 * a ^ n : ℝ) : ℂ)).re = _
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have htan₀ := pow_tangent_le_norm_pow hn ha.le (z 0)
    have htan₁ := pow_tangent_le_norm_pow hn zero_le_one (z 1)
    rw [hzi] at htan₀
    rw [hzj, one_pow, one_pow] at htan₁
    have hpow : a ^ (n - 1) * a = a ^ n := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    have hsum : a ^ n + 1 ≤ ‖z 0‖ ^ n + ‖z 1‖ ^ n := by
      have hcalc :
          (n : ℝ) * a ^ (n - 1) * (a + (c.re - 1) * (2 * a) - a) +
            (n : ℝ) * 1 * (1 + (c.re - 1) * (-2 * a ^ n) - 1) = 0 := by
        linear_combination 2 * (n : ℝ) * (c.re - 1) * hpow
      linarith
    have hr₀ : ‖r 0‖ = a := by
      change ‖(a : ℂ)‖ = a
      rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
    have hr₁ : ‖r 1‖ = 1 := norm_one
    rw [hr₀, hr₁, one_pow]
    exact hsum
  refine ⟨L, x, ?_, ?_⟩
  · rw [hproj]
    have he : ‖y 0‖ = 2 * a := by
      change ‖((2 * a : ℝ) : ℂ)‖ = 2 * a
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact he ▸ PiLp.norm_apply_le y 0
  · let m := 1 + 2 * a ^ n
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hx₀ : ‖x 0‖ = a := by
      change ‖((2 * a : ℝ) : ℂ) - (a : ℂ)‖ = a
      rw [← Complex.ofReal_sub, show 2 * a - a = a by ring, Complex.norm_real,
        Real.norm_of_nonneg ha.le]
    have hx₁ : ‖x 1‖ = m := by
      change ‖(((-2 * a ^ n : ℝ) : ℂ) - 1)‖ = m
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, show -2 * a ^ n - 1 = -m by
        dsimp [m]; ring, Complex.ofReal_neg, norm_neg, Complex.norm_real, Real.norm_of_nonneg hm]
    rw [PiLp.norm_eq_of_nat n rfl, Fin.sum_univ_two, hx₀, hx₁]
    have hm₁ : 1 ≤ m := by
      dsimp only [m]
      linarith [show 0 ≤ 2 * a ^ n by positivity]
    have ham : a ≤ m := ha₁.le.trans hm₁
    have hs : a ^ n + m ^ n ≤ 2 * m ^ n := by
      calc
        _ ≤ m ^ n + m ^ n := add_le_add (pow_le_pow_left₀ ha.le ham _) le_rfl
        _ = _ := by ring
    have he : (m ^ n) ^ (1 / (n : ℝ)) = m := by
      rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv hm hnR.ne']
    change _ ≤ (2 : ℝ) ^ (1 / (n : ℝ)) * m
    calc
      _ ≤ (2 * m ^ n) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (by positivity) hs (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hm n), he]

/-- **Exercise 68(b)** of [benIsrael2003generalized], Chapter 3.
The strict upper bound two is sharp. Complex two-coordinate $ell^p$
norms with finite exponents can have projective bound arbitrarily near two. -/
theorem exercise_68_upper_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ hn : 2 ≤ n,
      letI : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ n by omega)⟩
      essentiallyStrictlyConvex (PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ) ∧
        2 - ε < projectiveBound (E := PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ) := by
  obtain ⟨a, ha, ha₁⟩ := exists_between
    (show max (0 : ℝ) ((2 - ε) / 2) < 1 from max_lt (by norm_num) (by linarith))
  have ha₀ : 0 < a := (le_max_left _ _).trans_lt ha
  have haε : 2 - ε < 2 * a := by linarith [(le_max_right (0 : ℝ) ((2 - ε) / 2)).trans_lt ha]
  let M := fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ)) * (1 + 2 * a ^ n)
  have hpow : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha₀.le ha₁
  have hroot : Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => (2 : ℝ) ^ t) 0 :=
      (Real.continuous_const_rpow (show (2 : ℝ) ≠ 0 by norm_num)).continuousAt
    simpa only [Function.comp_def, Real.rpow_zero] using
      hc.tendsto.comp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hM : Tendsto M atTop (𝓝 1) := by
    simpa [M] using hroot.mul ((hpow.const_mul 2).const_add 1)
  have hratio : Tendsto (fun n => (2 * a) / M n) atTop (𝓝 (2 * a)) := by
    have ht : Tendsto ((fun _ : ℕ => 2 * a) / M) atTop (𝓝 (2 * a / 1)) :=
      tendsto_const_nhds.div hM one_ne_zero
    rw [div_one] at ht
    exact ht.congr (fun _ => rfl)
  obtain ⟨n, hn, hna⟩ := ((eventually_ge_atTop 2).and (hratio.eventually_const_lt haε)).exists
  refine ⟨n, hn, ?_⟩
  let : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ n by omega)⟩
  let E := PiLp (n : ℝ≥0∞) fun _ : Fin 2 => ℂ
  have hESC : essentiallyStrictlyConvex E := by
    apply essentiallyStrictlyConvex_piLp (n : ℝ≥0∞)
    rw [ENNReal.toReal_natCast]
    exact_mod_cast (show 1 < n by omega)
  have hdim : 2 ≤ Module.finrank ℂ E := by
    rw [(WithLp.linearEquiv (n : ℝ≥0∞) ℂ (Fin 2 → ℂ)).finrank_eq]
    simp
  obtain ⟨L, x, hL, hx⟩ := sharp_bound_pair hn ha₀ ha₁
  obtain ⟨_, hQ₁, _⟩ := exercise_68 (E := E) hESC 1 le_rfl (by omega)
  have hQ := norm_projection_le_projectiveBound_mul hESC hdim L x
  have hMn : 0 < M n := by
    dsimp [M]
    positivity
  refine ⟨hESC, hna.trans_le ((div_le_iff₀ hMn).mpr ?_)⟩
  exact hL.trans (hQ.trans (mul_le_mul_of_nonneg_left hx (zero_le_one.trans hQ₁)))

end SharpBound

end LpProjectionExercises

section EllipsoidalExercises

section

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Exercise 69**, the ellipsoidal case, of [benIsrael2003generalized],
Chapter 3. A finite-dimensional norm linearly isometric to a Hermitian
inner-product norm has contractive metric projectors. In coordinates an
ellipsoidal norm has such an isometry given by its positive-definite square root. -/
theorem exercise_69_of_ellipsoidal [FiniteDimensional ℂ E] (e : E ≃ₗᵢ[ℂ] H) :
    IsProjectiveNorm (E := E) := by
  intro L x
  let M := L.map e.toLinearEquiv.toLinearMap
  let : FiniteDimensional ℂ M :=
    (Submodule.equivMapOfInjective e.toLinearEquiv.toLinearMap e.injective L).finiteDimensional
  have hb := isBestApprox_definition_1 L x
  have hbest : IsBestApprox (M : Set H) (e x) (e (definition_1 L x)) := by
    refine ⟨⟨_, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖e x - e (definition_1 L x)‖ ≤ ‖e x - e z‖
    rw [← map_sub, ← map_sub, e.norm_map, e.norm_map]
    exact hb.2 z hz
  have he := hbest.eq_starProjection M
  rw [← e.norm_map (definition_1 L x), he, ← e.norm_map x]
  exact M.norm_starProjection_apply_le (e x)

end

end EllipsoidalExercises

section SmoothDerivativeExercises

open Set ConvexAnalysis Filter
open scoped Topology

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem gauge_pos_of_ne_zero {B : Set E} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : E) ∈ interior B) {x : E} (hx : x ≠ 0) : 0 < gauge B x := by
  have h := (exercise_53_gauge hB h₀).1
  exact lt_of_le_of_ne (h.nonnegative x) (Ne.symm fun he => hx (h.eq_zero x he))

private theorem frontier_gauge_iff {B : Set E} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : E) ∈ interior B) {x : E} : x ∈ frontier B ↔ gauge B x = 1 := by
  have h := (exercise_53_gauge hB h₀).2
  rw [frontier, hB.closed.closure_eq, Set.mem_sdiff]
  have hx := Set.ext_iff.mp h.1 x
  have hxi := Set.ext_iff.mp h.2 x
  change (x ∈ B ↔ gauge B x ≤ 1) at hx
  change (x ∈ interior B ↔ gauge B x < 1) at hxi
  rw [hx, hxi, not_lt, le_antisymm_iff]

private theorem gauge_normalize {B : Set E} (hB : IsGaugeConvexBody B)
    (h₀ : (0 : E) ∈ interior B) {x : E} (hx : x ≠ 0) :
    gauge B ((gauge B x)⁻¹ • x) = 1 := by
  have h := gauge_pos_of_ne_zero hB h₀ hx
  rw [(exercise_53_gauge hB h₀).1.homogeneity _ _ (inv_nonneg.mpr h.le),
    inv_mul_cancel₀ h.ne']

private theorem isNormalizedSupportingNormal_iff_real_bound {B : Set E}
    (hB : IsGaugeConvexBody B) (h₀ : (0 : E) ∈ interior B) {x u : E} (hx : x ≠ 0) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    IsNormalizedSupportingNormal B ((gauge B x)⁻¹ • x) u ↔
      inner ℝ x u = gauge B x ∧ ∀ z, inner ℝ z u ≤ gauge B z := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hp := gauge_pos_of_ne_zero hB h₀ hx
  have hmem (z : E) : z ∈ B ↔ gauge B z ≤ 1 :=
    Set.ext_iff.mp (exercise_53_gauge hB h₀).2.1 z
  have hre {z : E} : (inner ℂ u z).re = inner ℝ z u := real_inner_comm z u
  unfold IsNormalizedSupportingNormal
  have he : (inner ℂ u ((gauge B x)⁻¹ • x)).re = 1 ↔ inner ℝ x u = gauge B x := by
    rw [hre, real_inner_smul_left, ← div_eq_inv_mul, div_eq_iff hp.ne', one_mul]
  rw [he]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h z
    by_cases hz : z = 0
    · rw [hz, inner_zero_left, gauge_zero]
    have hz₀ := gauge_pos_of_ne_zero hB h₀ hz
    have hm := (hmem _).mpr (gauge_normalize hB h₀ hz).le
    have hle := h _ hm
    rw [hre, real_inner_smul_left, inv_mul_le_iff₀ hz₀, mul_one] at hle
    exact hle
  · intro h z hz
    rw [hre]
    exact (h z).trans ((hmem z).mp hz)

private theorem mem_subdifferential_gauge_iff {B : Set E}
    (hB : IsGaugeConvexBody B) (h₀ : (0 : E) ∈ interior B) {x u : E} :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    u ∈ subdifferential (innerₗ E) (fun z => ((gauge B z : ℝ) : EReal)) x ↔
      inner ℝ x u = gauge B x ∧ ∀ z, inner ℝ z u ≤ gauge B z := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  simp only [mem_subdifferential, innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
  constructor
  · intro h
    have hzero := h 0
    rw [zero_sub, inner_neg_left, gauge_zero] at hzero
    have htwo := h ((2 : ℝ) • x)
    rw [two_smul, add_sub_cancel_right,
      ← two_smul ℝ x, (exercise_53_gauge hB h₀).1.homogeneity _ _ (by norm_num)] at htwo
    have he : inner ℝ x u = gauge B x := by linarith
    refine ⟨he, fun z => ?_⟩
    have hz := h z
    rw [inner_sub_left, he] at hz
    linarith
  · rintro ⟨he, h⟩ z
    rw [inner_sub_left, he]
    linarith [h z]

variable [FiniteDimensional ℂ E]

/-- **Exercise 64(b)** of [benIsrael2003generalized], Chapter 3.
The gauge has a two-sided real directional derivative at every nonzero
point in every direction exactly when the body has a unique supporting
hyperplane at each boundary point. -/
theorem exercise_64b {B : Set E} (hB : IsGaugeConvexBody B) (h₀ : (0 : E) ∈ interior B) :
    (∀ x : E, x ≠ 0 → ∀ d : E,
      DifferentiableAt ℝ (fun t : ℝ => gauge B (x + t • d)) 0) ↔ IsSmoothGaugeBody B := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  let φ := gauge B
  let f := fun z : E => ((φ z : ℝ) : EReal)
  have hg := (exercise_53_gauge hB h₀).1
  have hc : ConvexFn f := by
    apply ConvexOn.convexFn_coe
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    exact (hg.subadditive _ _).trans_eq (by
      rw [hg.homogeneity _ _ ha, hg.homogeneity _ _ hb, smul_eq_mul, smul_eq_mul])
  have hp : ProperConvex f := properConvex_coe _
  have hsub (x : E) : (subdifferential (innerₗ E) f x).Nonempty :=
    subdifferential_nonempty_of_mem_relint_convexDom hc hp (by
      rw [convexDom_coe, intrinsicInterior_univ]
      trivial)
  have hpair (x : E) (hx : x ≠ 0) (u : E) :
      u ∈ subdifferential (innerₗ E) f x ↔
        IsNormalizedSupportingNormal B ((φ x)⁻¹ • x) u :=
    (mem_subdifferential_gauge_iff hB h₀).trans
      (isNormalizedSupportingNormal_iff_real_bound hB h₀ hx).symm
  constructor
  · intro h x hxF
    have hφx : φ x = 1 := (frontier_gauge_iff hB h₀).mp hxF
    have hx : x ≠ 0 := by intro he; simp [φ, he] at hφx
    have hnormal (u : E) :
        u ∈ subdifferential (innerₗ E) f x ↔ IsNormalizedSupportingNormal B x u := by
      simpa only [hφx, inv_one, one_smul] using hpair x hx u
    obtain ⟨u, hu⟩ := hsub x
    refine ⟨u, (hnormal u).mp hu, fun v hv => ?_⟩
    have hdir (w : E) (hw : w ∈ subdifferential (innerₗ E) f x) (d : E) :
        deriv (fun t : ℝ => gauge B (x + t • d)) 0 = inner ℝ d w := by
      obtain ⟨hxe, hbound⟩ := (mem_subdifferential_gauge_iff hB h₀).mp hw
      have hD := (h x hx d).hasDerivAt
      have hline : HasDerivAt (fun t : ℝ => inner ℝ (x + t • d) w) (inner ℝ d w) 0 := by
        simpa only [inner_add_left, real_inner_smul_left, id_eq, one_mul] using
          ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ d w)).const_add (inner ℝ x w)
      have hmin : IsLocalMin (fun t : ℝ => gauge B (x + t • d) - inner ℝ (x + t • d) w) 0 :=
        Filter.Eventually.of_forall fun t => by
          simp only [zero_smul, add_zero, hxe, sub_self]
          exact sub_nonneg.mpr (hbound _)
      exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hD.sub hline))
    have he (d : E) : inner ℝ d v = inner ℝ d u :=
      (hdir v ((hnormal v).mpr hv) d).symm.trans (hdir u hu d)
    have hz : inner ℝ (v - u) (v - u) = 0 := by
      rw [inner_sub_right, he, sub_self]
    exact sub_eq_zero.mp (norm_eq_zero.mp (by
      rw [real_inner_self_eq_norm_sq] at hz
      nlinarith))
  · intro h x hx d
    have hn := gauge_normalize hB h₀ hx
    have hfr := (frontier_gauge_iff hB h₀).mpr hn
    obtain ⟨u, hu, huni⟩ := h _ hfr
    have he : subdifferential (innerₗ E) f x = {u} := by
      ext v
      rw [mem_singleton_iff]
      exact ⟨fun hv => huni v ((hpair x hx v).mp hv),
        fun hv => (hpair x hx v).mpr (hv.symm ▸ hu)⟩
    have hgu := hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton hc hp he
    obtain ⟨g, heq, hd⟩ := hgu
    have heq' : φ =ᶠ[𝓝 x] g := heq.mono fun z hz => EReal.coe_injective hz
    have hφ : HasFDerivAt φ (evalCLM (innerₗ E) u) x := hd.congr_of_eventuallyEq heq'
    have hd₀ : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have hf₀ : DifferentiableAt ℝ φ ((fun t : ℝ => x + t • d) 0) := by
      simpa only [zero_smul, add_zero] using hφ.differentiableAt
    have hComp : DifferentiableAt ℝ (φ ∘ (fun t : ℝ => x + t • d)) 0 :=
      hf₀.comp 0 hd₀.differentiableAt
    exact hComp

end

end SmoothDerivativeExercises

section NonSmoothBodyExercises

open Set
open scoped Pointwise Topology

section

private abbrev Plane := EuclideanSpace ℂ (Fin 2)

private noncomputable def roundedCornerLevel (x : Plane) : ℝ := ‖x‖ ^ 2 + ‖x 0‖

/-- An equilibrated convex body with curved boundary and a corner. -/
def exercise_65_body : Set (EuclideanSpace ℂ (Fin 2)) := {x | roundedCornerLevel x ≤ 1}

private theorem roundedCornerLevel_strictConvex :
    StrictConvexOn ℝ (univ : Set Plane) roundedCornerLevel := by
  let : InnerProductSpace ℝ Plane := InnerProductSpace.rclikeToReal ℂ Plane
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hsq := (strictConvexOn_norm_sq (H := Plane)).2
    (mem_univ x) (mem_univ y) hxy ha hb hab
  have hn : ‖(a • x + b • y) 0‖ ≤ a * ‖x 0‖ + b * ‖y 0‖ := by
    change ‖a • (x 0) + b • (y 0)‖ ≤ _
    calc
      _ ≤ ‖a • (x 0)‖ + ‖b • (y 0)‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  change ‖a • x + b • y‖ ^ 2 < a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 at hsq
  dsimp only [roundedCornerLevel]
  rw [smul_eq_mul, smul_eq_mul]
  linarith

private theorem exercise_65_body_subset_unit :
    exercise_65_body ⊆ Metric.closedBall (0 : Plane) 1 := by
  intro x hx
  change ‖x‖ ^ 2 + ‖x 0‖ ≤ 1 at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x, norm_nonneg (x 0)]

private theorem exercise_65_body_isClosedConvex :
    IsGaugeConvexBody exercise_65_body ∧ Balanced ℂ exercise_65_body ∧
      (0 : Plane) ∈ interior exercise_65_body ∧ StrictConvex ℝ exercise_65_body := by
  have hc : Continuous roundedCornerLevel := by
    unfold roundedCornerLevel
    exact (continuous_norm.pow 2).add ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).norm)
  have hn : ∀ x ∈ exercise_65_body, roundedCornerLevel x ≤ 1 := fun _ hx => hx
  have h₀ : (0 : Plane) ∈ interior exercise_65_body := by
    have he : roundedCornerLevel (0 : Plane) < 1 := by simp [roundedCornerLevel]
    have hN : {x | roundedCornerLevel x < 1} ∈ 𝓝 (0 : Plane) :=
      hc.continuousAt.eventually_lt continuousAt_const he
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hN fun x hx => (show roundedCornerLevel x < 1 from hx).le)
  refine ⟨⟨?_, isClosed_le hc continuous_const,
    Metric.isBounded_closedBall.subset exercise_65_body_subset_unit, ⟨0, h₀⟩⟩, ?_, h₀, ?_⟩
  · intro x hx y hy a b ha hb hab
    have h := roundedCornerLevel_strictConvex.convexOn.2
      (mem_univ x) (mem_univ y) ha hb hab
    change roundedCornerLevel (a • x + b • y) ≤ 1
    rw [smul_eq_mul, smul_eq_mul] at h
    exact h.trans <| (add_le_add (mul_le_of_le_one_right ha (hn x hx))
      (mul_le_of_le_one_right hb (hn y hy))).trans_eq hab
  · intro c hc
    rintro _ ⟨x, hx, rfl⟩
    change roundedCornerLevel (c • x) ≤ 1
    apply le_trans _ (hn x hx)
    simp only [roundedCornerLevel, PiLp.smul_apply, norm_smul, mul_pow]
    exact add_le_add
      (mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg c) hc))
      (mul_le_of_le_one_left (norm_nonneg _) hc)
  · intro x hx y hy hxy a b ha hb hab
    have h := roundedCornerLevel_strictConvex.2
      (mem_univ x) (mem_univ y) hxy ha hb hab
    rw [smul_eq_mul, smul_eq_mul] at h
    have hbelow : roundedCornerLevel (a • x + b • y) < 1 :=
      h.trans_le ((add_le_add (mul_le_of_le_one_right ha.le (hn x hx))
        (mul_le_of_le_one_right hb.le (hn y hy))).trans_eq hab)
    apply interior_mono (show {x | roundedCornerLevel x < 1} ⊆ exercise_65_body from
      fun x hx => (show roundedCornerLevel x < 1 from hx).le)
    rw [(isOpen_lt hc continuous_const).interior_eq]
    exact hbelow

private theorem exercise_65_body_not_smooth : ¬ IsSmoothGaugeBody exercise_65_body := by
  let y : Plane := WithLp.toLp 2 ![0, 1]
  let u : Plane := WithLp.toLp 2 ![(1 / 2 : ℂ), 1]
  let v : Plane := WithLp.toLp 2 ![(-1 / 2 : ℂ), 1]
  have hy : y = PiLp.single 2 (1 : Fin 2) (1 : ℂ) := by
    ext i
    fin_cases i <;> simp [y]
  have hnorm_y : ‖y‖ = 1 := by rw [hy, PiLp.norm_single, norm_one]
  have hB := exercise_65_body_isClosedConvex.1
  have hyB : y ∈ exercise_65_body := by
    change roundedCornerLevel y ≤ 1
    simp [roundedCornerLevel, hnorm_y, y]
  have hyF : y ∈ frontier exercise_65_body := by
    rw [frontier, hB.closed.closure_eq]
    refine ⟨hyB, fun hy => ?_⟩
    have hy' := interior_mono exercise_65_body_subset_unit hy
    rw [interior_closedBall _ one_ne_zero, Metric.mem_ball, dist_zero_right, hnorm_y] at hy'
    exact lt_irrefl _ hy'
  have hpair (s : ℝ) (x : Plane) :
      (inner ℂ (WithLp.toLp 2 ![(s : ℂ), 1] : Plane) x).re =
        s * (x 0).re + (x 1).re := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    simp [mul_comm]
  have hsupport (s : ℝ) (hs : |s| ≤ 1 / 2) :
      IsNormalizedSupportingNormal exercise_65_body y (WithLp.toLp 2 ![(s : ℂ), 1]) := by
    constructor
    · rw [hpair]
      simp [y]
    · intro x hx
      rw [hpair]
      change ‖x‖ ^ 2 + ‖x 0‖ ≤ 1 at hx
      have h₀ : s * (x 0).re ≤ ‖x 0‖ / 2 := by
        have h := mul_le_mul hs (Complex.abs_re_le_norm (x 0)) (abs_nonneg _) (by norm_num)
        exact (le_abs_self _).trans (by rw [abs_mul]; linarith)
      have h₁ := (Complex.re_le_norm (x 1)).trans (PiLp.norm_apply_le x 1)
      nlinarith [sq_nonneg (‖x‖ - 1)]
  have hu : IsNormalizedSupportingNormal exercise_65_body y u := by
    convert hsupport (1 / 2) (by norm_num) using 1
    norm_num [u]
  have hv : IsNormalizedSupportingNormal exercise_65_body y v := by
    convert hsupport (-1 / 2) (by norm_num) using 1
    norm_num [v]
  intro h
  have he := congrArg (fun z : Plane => z 0) ((h y hyF).unique hu hv)
  change (1 / 2 : ℂ) = -1 / 2 at he
  norm_num at he

/-- **Exercise 65** of [benIsrael2003generalized], Chapter 3.
An explicit equilibrated body is strictly convex but its Hermitian polar
is not strictly convex. The two gauges therefore give the requested
pair of dual norms with different strict-convexity behavior. -/
theorem exercise_65 :
    IsGaugeConvexBody exercise_65_body ∧ Balanced ℂ exercise_65_body ∧
      StrictConvex ℝ exercise_65_body ∧ ¬ StrictConvex ℝ (hermitianPolar exercise_65_body) := by
  obtain ⟨hB, hbal, _, hstrict⟩ := exercise_65_body_isClosedConvex
  obtain ⟨hP, hPbal, hPP, _, _⟩ := exercise_57 hB hbal
  refine ⟨hB, hbal, hstrict, fun hp => exercise_65_body_not_smooth ?_⟩
  have h := (exercise_63 hP hPbal).mp hp
  rwa [hPP] at h

end

end NonSmoothBodyExercises

section LpNonlinearExercises

open Set Finset Filter
open scoped ENNReal Topology Pointwise

/-- The Euclidean metric projectors are linear. -/
theorem exercise_74_euclidean {ι : Type*} [Fintype ι] (L : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ P : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι,
      ∀ x, definition_1 L x = P x := by
  exact ⟨L.starProjection.toLinearMap,
    fun x => (isBestApprox_definition_1 L x).eq_starProjection L⟩

section

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Exercise 74**, converse, of [benIsrael2003generalized], Chapter 3.
For every $1<p<\infty$ other than two, projection onto the line spanned by
$(1,1,1)$ in three complex coordinates fails additivity. -/
theorem exercise_74_nonlinear (hp : 1 < p.toReal) (hne : p.toReal ≠ 2) :
    ∃ L : Submodule ℂ (PiLp p fun _ : Fin 3 => ℂ),
      ¬ (∀ x y, definition_1 L (x + y) = definition_1 L x + definition_1 L y) := by
  let X := PiLp p fun _ : Fin 3 => ℂ
  let q := p.toReal
  have hq : 0 < q := zero_lt_one.trans hp
  have hESC : essentiallyStrictlyConvex X := essentiallyStrictlyConvex_piLp p hp
  let w : X := WithLp.toLp p ![1, 1, 1]
  let u : X := WithLp.toLp p ![1, -1, 0]
  let v : X := WithLp.toLp p ![1, 0, -1]
  let L : Submodule ℂ X := ℂ ∙ w
  have hnorm (x : X) : ‖x‖ ^ q = ‖x 0‖ ^ q + ‖x 1‖ ^ q + ‖x 2‖ ^ q := by
    have hsum : 0 ≤ ∑ i : Fin 3, ‖x i‖ ^ q :=
      sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
    rw [PiLp.norm_eq_sum hq, ← Real.rpow_mul hsum, one_div, inv_mul_cancel₀ hq.ne',
      Real.rpow_one, Fin.sum_univ_three, add_assoc]
  have hconv (c : ℂ) : 2 ≤ ‖1 - c‖ ^ q + ‖-1 - c‖ ^ q := by
    have h := (strictConvexOn_complex_norm_rpow q hp).convexOn.2
      (mem_univ (1 - c : ℂ)) (mem_univ (1 + c))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have he : (1 / 2 : ℝ) • (1 - c) + (1 / 2 : ℝ) • (1 + c) = (1 : ℂ) := by
      rw [← smul_add, show (1 - c) + (1 + c) = (2 : ℂ) by ring,
        ← IsScalarTower.algebraMap_smul ℂ]
      norm_num
    rw [he] at h
    change ‖(1 : ℂ)‖ ^ q ≤ (1 / 2) * ‖1 - c‖ ^ q + (1 / 2) * ‖1 + c‖ ^ q at h
    rw [norm_one, Real.one_rpow] at h
    rw [show -1 - c = -(1 + c) by ring, norm_neg]
    linarith
  have hu : definition_1 L u = 0 := by
    apply (definition_1_eq_iff hESC L u 0).mpr
    refine ⟨L.zero_mem, fun z hz => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (show z ∈ L from hz)
    apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hq).mp
    rw [sub_zero, hnorm, hnorm]
    change ‖(1 : ℂ)‖ ^ q + ‖(-1 : ℂ)‖ ^ q + ‖(0 : ℂ)‖ ^ q ≤
      ‖1 - c * 1‖ ^ q + ‖-1 - c * 1‖ ^ q + ‖0 - c * 1‖ ^ q
    simp only [norm_one, norm_neg, norm_zero, Real.one_rpow, Real.zero_rpow hq.ne',
      add_zero, mul_one]
    linarith [hconv c, Real.rpow_nonneg (norm_nonneg (0 - c)) q]
  have hv : definition_1 L v = 0 := by
    apply (definition_1_eq_iff hESC L v 0).mpr
    refine ⟨L.zero_mem, fun z hz => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (show z ∈ L from hz)
    apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hq).mp
    rw [sub_zero, hnorm, hnorm]
    change ‖(1 : ℂ)‖ ^ q + ‖(0 : ℂ)‖ ^ q + ‖(-1 : ℂ)‖ ^ q ≤
      ‖1 - c * 1‖ ^ q + ‖0 - c * 1‖ ^ q + ‖-1 - c * 1‖ ^ q
    simp only [norm_one, norm_neg, norm_zero, Real.one_rpow, Real.zero_rpow hq.ne',
      add_zero, mul_one]
    linarith [hconv c, Real.rpow_nonneg (norm_nonneg (0 - c)) q]
  refine ⟨L, fun hadd => ?_⟩
  have huv : definition_1 L (u + v) = 0 := by rw [hadd, hu, hv, add_zero]
  let f : ℝ → ℝ := fun t => ‖u + v - (t : ℂ) • w‖ ^ q
  let g : ℝ → ℝ := fun t => (2 - t) ^ q + 2 * (1 + t) ^ q
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    obtain ⟨_, h⟩ := (definition_1_eq_iff hESC L (u + v) 0).mp huv
    have ht := h ((t : ℂ) • w) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have hle := Real.rpow_le_rpow (norm_nonneg _) ht hq.le
    simpa only [f, Complex.ofReal_zero, zero_smul, sub_zero] using hle
  have heq : f =ᶠ[𝓝 0] g := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    rw [show f t = ‖u + v - (t : ℂ) • w‖ ^ q from rfl, hnorm]
    change ‖(1 + 1 : ℂ) - (t : ℂ) * 1‖ ^ q + ‖-1 + 0 - (t : ℂ) * 1‖ ^ q +
      ‖0 + -1 - (t : ℂ) * 1‖ ^ q = g t
    have h₀ : ‖(1 + 1 : ℂ) - (t : ℂ) * 1‖ = 2 - t := by
      rw [mul_one, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.2])]
      norm_num
    have h₁ : ‖(-1 : ℂ) - (t : ℂ) * 1‖ = 1 + t := by
      rw [mul_one, show (-1 : ℂ) - (t : ℂ) = -(((1 + t : ℝ)) : ℂ) by
        push_cast
        ring,
        norm_neg, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.1])]
    rw [add_zero, zero_add, h₀, h₁]
    dsimp [g]
    ring
  have hD₀ : HasDerivAt (fun t : ℝ => (2 - t) ^ q) (-q * 2 ^ (q - 1)) 0 := by
    have hb : HasDerivAt (fun t : ℝ => 2 - t) (0 - 1) 0 :=
      (hasDerivAt_const 0 (2 : ℝ)).sub (hasDerivAt_id 0)
    convert hb.rpow_const (p := q) (Or.inr hp.le) using 1
    norm_num
  have hD₁ : HasDerivAt (fun t : ℝ => (1 + t) ^ q) q 0 := by
    have hb : HasDerivAt (fun t : ℝ => 1 + t) (0 + 1) 0 :=
      (hasDerivAt_const 0 (1 : ℝ)).add (hasDerivAt_id 0)
    convert hb.rpow_const (p := q) (Or.inr hp.le) using 1
    norm_num
  have hD : HasDerivAt g (-q * 2 ^ (q - 1) + 2 * q) 0 := hD₀.add (hD₁.const_mul 2)
  have hzero := hmin.hasDerivAt_eq_zero (hD.congr_of_eventuallyEq heq)
  have hpw : (2 : ℝ) ^ (q - 1) = 2 := by
    have hm : q * (2 ^ (q - 1) - 2) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hq.ne')
  have he : q - 1 = 1 := (Real.rpow_right_inj (by norm_num) (by norm_num)).mp
    (hpw.trans (Real.rpow_one 2).symm)
  exact hne (by linarith)

end

end LpNonlinearExercises

section PlanarProjectiveExercises

open Set Finset
open scoped Topology Pointwise NNReal

section

private abbrev RealPlane := ℝ × ℝ

/-- The two-coordinate real $ell^p$ norm for finite exponent $p$. -/
noncomputable def planarLp (p : ℝ) (x : ℝ × ℝ) : ℝ :=
  (|x.1| ^ p + |x.2| ^ p) ^ (1 / p)

/-- **Exercise 69**, the real planar example. The first and third
quadrants use exponent $p$, and the other quadrants use exponent $q$. -/
noncomputable def piecewisePlanarLp (p q : ℝ) (x : ℝ × ℝ) : ℝ :=
  if 0 ≤ x.1 * x.2 then planarLp p x else planarLp q x

/-- The usual bilinear pairing of two real coordinate pairs. -/
def planarDot (x y : RealPlane) : ℝ := x.1 * y.1 + x.2 * y.2

private def planarTurn (x : RealPlane) : RealPlane := (-x.2, x.1)

private theorem planarLp_nonneg (p : ℝ) (x : RealPlane) : 0 ≤ planarLp p x := by
  unfold planarLp
  positivity

private theorem planarLp_abs_le (p : ℝ) (hp : 0 < p) (x : RealPlane) :
    |x.1| ≤ planarLp p x ∧ |x.2| ≤ planarLp p x := by
  have hf (t u : ℝ) : |t| ≤ (|t| ^ p + |u| ^ p) ^ (1 / p) := by
    calc
      _ = (|t| ^ p) ^ (1 / p) := by
        rw [one_div, Real.rpow_rpow_inv (abs_nonneg _) hp.ne']
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (le_add_of_nonneg_right (by positivity)) (by positivity)
  exact ⟨hf _ _, by simpa only [planarLp, add_comm] using hf x.2 x.1⟩

private theorem planarLp_on_axis (p : ℝ) (hp : 0 < p) (x : RealPlane) (hx : x.1 * x.2 = 0) :
    planarLp p x = |x.1| + |x.2| := by
  rcases mul_eq_zero.mp hx with h | h
  · rw [planarLp, h, abs_zero, Real.zero_rpow hp.ne', zero_add, one_div,
      Real.rpow_rpow_inv (abs_nonneg _) hp.ne', zero_add]
  · rw [planarLp, h, abs_zero, Real.zero_rpow hp.ne', add_zero, one_div,
      Real.rpow_rpow_inv (abs_nonneg _) hp.ne', add_zero]

private theorem planarLp_le_one_iff (p : ℝ) (hp : 0 < p) (x : RealPlane) :
    planarLp p x ≤ 1 ↔ |x.1| ^ p + |x.2| ^ p ≤ 1 := by
  unfold planarLp
  conv_lhs => rhs; rw [← Real.one_rpow (1 / p)]
  exact Real.rpow_le_rpow_iff (by positivity) zero_le_one (by positivity)

private theorem piecewisePlanarLp_abs_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : RealPlane) :
    |x.1| ≤ piecewisePlanarLp p q x ∧ |x.2| ≤ piecewisePlanarLp p q x := by
  unfold piecewisePlanarLp
  split
  · exact planarLp_abs_le p hp x
  · exact planarLp_abs_le q hq x

private theorem planarLp_holder_abs {p q : ℝ} (hpq : p.HolderConjugate q)
    (x y : RealPlane) :
    |x.1| * |y.1| + |x.2| * |y.2| ≤ planarLp p x * planarLp q y := by
  let f : Fin 2 → ℝ := ![|x.1|, |x.2|]
  let g : Fin 2 → ℝ := ![|y.1|, |y.2|]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (univ : Finset (Fin 2)) hpq
    (f := f) (g := g) (fun i _ => by fin_cases i <;> exact abs_nonneg _)
    (fun i _ => by fin_cases i <;> exact abs_nonneg _)
  simpa [f, g, planarLp, Fin.sum_univ_two] using h

private theorem exists_planarLp_dual_attainment {p q : ℝ} (hpq : p.HolderConjugate q)
    (x : RealPlane) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ q + b ^ q ≤ 1 ∧
      |x.1| * a + |x.2| * b = planarLp p x := by
  let f : Fin 2 → ℝ≥0 := ![⟨|x.1|, abs_nonneg _⟩, ⟨|x.2|, abs_nonneg _⟩]
  obtain ⟨g, hg, hfg⟩ := (NNReal.isGreatest_Lp (univ : Finset (Fin 2)) f hpq).1
  refine ⟨g 0, g 1, (g 0).coe_nonneg, (g 1).coe_nonneg, ?_, ?_⟩
  · have hb : (g 0) ^ q + (g 1) ^ q ≤ 1 := by
      simpa only [Fin.sum_univ_two] using (show ∑ i, g i ^ q ≤ 1 from hg)
    exact_mod_cast hb
  · have he := congrArg (fun a : ℝ≥0 => (a : ℝ)) hfg
    push_cast at he
    simp only [f, Fin.sum_univ_two] at he
    change |x.1| * ↑(g 0) + |x.2| * ↑(g 1) =
      (|x.1| ^ p + |x.2| ^ p) ^ (1 / p) at he
    exact he

private theorem planarDot_le_piecewisePlanarLp {p q : ℝ} (hpq : p.HolderConjugate q)
    (x y : RealPlane) (hy : piecewisePlanarLp p q y ≤ 1) :
    planarDot x y ≤ piecewisePlanarLp q p x := by
  have hx := piecewisePlanarLp_abs_le hpq.symm.pos hpq.pos x
  have hy' := piecewisePlanarLp_abs_le hpq.pos hpq.symm.pos y
  have h₀ : |y.1| ≤ 1 := hy'.1.trans hy
  have h₁ : |y.2| ≤ 1 := hy'.2.trans hy
  have habs : planarDot x y ≤ |x.1| * |y.1| + |x.2| * |y.2| := by
    unfold planarDot
    exact add_le_add ((le_abs_self _).trans_eq (abs_mul _ _))
      ((le_abs_self _).trans_eq (abs_mul _ _))
  have hmismatch (h : (x.1 * y.1) * (x.2 * y.2) ≤ 0) :
      planarDot x y ≤ piecewisePlanarLp q p x := by
    by_cases he : x.1 * y.1 ≤ 0
    · have hb : x.2 * y.2 ≤ |x.2| := calc
        _ ≤ |x.2| * |y.2| := (le_abs_self _).trans_eq (abs_mul _ _)
        _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) h₁
      exact (add_le_of_nonpos_left he).trans (hb.trans hx.2)
    · have hnon : x.2 * y.2 ≤ 0 := nonpos_of_mul_nonpos_right h (lt_of_not_ge he)
      have hb : x.1 * y.1 ≤ |x.1| := calc
        _ ≤ |x.1| * |y.1| := (le_abs_self _).trans_eq (abs_mul _ _)
        _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) h₀
      exact (add_le_of_nonpos_right hnon).trans (hb.trans hx.1)
  by_cases hxprod : 0 ≤ x.1 * x.2 <;> by_cases hyprod : 0 ≤ y.1 * y.2
  · rw [piecewisePlanarLp, ite_eq_left hxprod]
    rw [piecewisePlanarLp, ite_eq_left hyprod] at hy
    exact habs.trans ((planarLp_holder_abs hpq.symm x y).trans
      (mul_le_of_le_one_right (planarLp_nonneg _ _) hy))
  · apply hmismatch
    rw [show (x.1 * y.1) * (x.2 * y.2) = (x.1 * x.2) * (y.1 * y.2) by ring]
    exact mul_nonpos_of_nonneg_of_nonpos hxprod (le_of_not_ge hyprod)
  · apply hmismatch
    rw [show (x.1 * y.1) * (x.2 * y.2) = (x.1 * x.2) * (y.1 * y.2) by ring]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hxprod) hyprod
  · rw [piecewisePlanarLp, ite_eq_right hxprod]
    rw [piecewisePlanarLp, ite_eq_right hyprod] at hy
    exact habs.trans ((planarLp_holder_abs hpq x y).trans
      (mul_le_of_le_one_right (planarLp_nonneg _ _) hy))

private theorem exists_planarDot_eq_piecewisePlanarLp {p q : ℝ} (hpq : p.HolderConjugate q)
    (x : RealPlane) : ∃ y : RealPlane, piecewisePlanarLp p q y ≤ 1 ∧
      planarDot x y = piecewisePlanarLp q p x := by
  by_cases h : 0 ≤ x.1 * x.2
  · obtain ⟨a, b, ha, hb, hab, he⟩ := exists_planarLp_dual_attainment hpq.symm x
    rw [piecewisePlanarLp, ite_eq_left h]
    have hsign : (0 ≤ x.1 ∧ 0 ≤ x.2) ∨ (x.1 ≤ 0 ∧ x.2 ≤ 0) := by
      rcases le_or_gt 0 x.1 with hx | hx <;>
        rcases le_or_gt 0 x.2 with hy | hy
      · exact Or.inl ⟨hx, hy⟩
      · refine Or.inr ⟨le_of_not_gt ?_, hy.le⟩
        exact fun hx => (not_lt_of_ge h) (mul_neg_of_pos_of_neg hx hy)
      · refine Or.inr ⟨hx.le, le_of_not_gt ?_⟩
        exact fun hy => (not_lt_of_ge h) (mul_neg_of_neg_of_pos hx hy)
      · exact Or.inr ⟨hx.le, hy.le⟩
    rcases hsign with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · refine ⟨(a, b), ?_, ?_⟩
      · rw [piecewisePlanarLp, ite_eq_left (mul_nonneg ha hb), planarLp_le_one_iff p hpq.pos]
        simpa only [abs_of_nonneg ha, abs_of_nonneg hb] using hab
      · simpa only [planarDot, abs_of_nonneg hx, abs_of_nonneg hy] using he
    · refine ⟨(-a, -b), ?_, ?_⟩
      · rw [piecewisePlanarLp, ite_eq_left (mul_nonneg_of_nonpos_of_nonpos
          (neg_nonpos.mpr ha) (neg_nonpos.mpr hb)), planarLp_le_one_iff p hpq.pos]
        simpa only [abs_neg, abs_of_nonneg ha, abs_of_nonneg hb] using hab
      · simpa only [planarDot, abs_of_nonpos hx, abs_of_nonpos hy, neg_mul, mul_neg] using he
  · obtain ⟨a, b, ha, hb, hab, he⟩ := exists_planarLp_dual_attainment hpq x
    rw [piecewisePlanarLp, ite_eq_right h]
    have hsign := mul_neg_iff.mp (lt_of_not_ge h)
    have hflip (y : RealPlane) (hy : y.1 * y.2 ≤ 0) (hL : planarLp q y ≤ 1) :
        piecewisePlanarLp p q y ≤ 1 := by
      unfold piecewisePlanarLp
      split
      · rename_i hs
        have hzero := le_antisymm hy hs
        rwa [planarLp_on_axis p hpq.pos y hzero, ← planarLp_on_axis q hpq.symm.pos y hzero]
      · exact hL
    rcases hsign with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · refine ⟨(a, -b), hflip _ (mul_nonpos_of_nonneg_of_nonpos ha (neg_nonpos.mpr hb)) ?_, ?_⟩
      · rw [planarLp_le_one_iff q hpq.symm.pos]
        simpa only [abs_neg, abs_of_nonneg ha, abs_of_nonneg hb] using hab
      · simpa only [planarDot, abs_of_nonneg hx.le, abs_of_nonpos hy.le, neg_mul, mul_neg] using he
    · refine ⟨(-a, b), hflip _ (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hb) ?_, ?_⟩
      · rw [planarLp_le_one_iff q hpq.symm.pos]
        simpa only [abs_neg, abs_of_nonneg ha, abs_of_nonneg hb] using hab
      · simpa only [planarDot, abs_of_nonpos hx.le, abs_of_nonneg hy.le, neg_mul, mul_neg] using he

/-- The exact real polar of the piecewise planar unit ball exchanges the exponents. -/
theorem piecewisePlanarLp_polar {p q : ℝ} (hpq : p.HolderConjugate q) (x : ℝ × ℝ) :
    (∀ y : ℝ × ℝ, piecewisePlanarLp p q y ≤ 1 → planarDot x y ≤ 1) ↔
      piecewisePlanarLp q p x ≤ 1 := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := exists_planarDot_eq_piecewisePlanarLp hpq x
    exact he ▸ h y hy
  · intro h y hy
    exact (planarDot_le_piecewisePlanarLp hpq x y hy).trans h


private theorem planarLp_smul (p : ℝ) (hp : 0 < p) (c : ℝ) (x : RealPlane) :
    planarLp p (c • x) = |c| * planarLp p x := by
  change (|c * x.1| ^ p + |c * x.2| ^ p) ^ (1 / p) = _
  rw [abs_mul, abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg x.1),
    Real.mul_rpow (abs_nonneg c) (abs_nonneg x.2), ← mul_add,
    Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.rpow_rpow_inv (abs_nonneg c) hp.ne']
  simp only [planarLp, one_div]

/-- The real planar piecewise norm is absolutely homogeneous. -/
theorem piecewisePlanarLp_smul {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (c : ℝ) (x : ℝ × ℝ) :
    piecewisePlanarLp p q (c • x) = |c| * piecewisePlanarLp p q x := by
  by_cases hc : c = 0
  · subst c
    simp [piecewisePlanarLp, planarLp, Real.zero_rpow hp.ne',
      Real.zero_rpow (inv_ne_zero hp.ne')]
  · have hprod : (c • x).1 * (c • x).2 = c ^ 2 * (x.1 * x.2) := by
      change c * x.1 * (c * x.2) = _
      ring
    have hpos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    by_cases h : 0 ≤ x.1 * x.2
    · have h' : 0 ≤ (c • x).1 * (c • x).2 := hprod ▸ mul_nonneg hpos.le h
      rw [piecewisePlanarLp, ite_eq_left h', piecewisePlanarLp, ite_eq_left h]
      exact planarLp_smul p hp c x
    · have h' : ¬0 ≤ (c • x).1 * (c • x).2 := by
        rw [hprod]
        exact not_le_of_gt (mul_neg_of_pos_of_neg hpos (lt_of_not_ge h))
      rw [piecewisePlanarLp, ite_eq_right h', piecewisePlanarLp, ite_eq_right h]
      exact planarLp_smul q hq c x

private theorem piecewisePlanarLp_zero {p q : ℝ} (hp : 0 < p) :
    piecewisePlanarLp p q (0 : RealPlane) = 0 := by
  simp [piecewisePlanarLp, planarLp, Real.zero_rpow hp.ne',
    Real.zero_rpow (inv_ne_zero hp.ne')]

private theorem piecewisePlanarLp_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {x : RealPlane} (hx : x ≠ 0) : 0 < piecewisePlanarLp p q x := by
  have h := piecewisePlanarLp_abs_le hp hq x
  by_contra! he
  apply hx
  apply Prod.ext (abs_eq_zero.mp (le_antisymm (h.1.trans he) (abs_nonneg _)))
  exact abs_eq_zero.mp (le_antisymm (h.2.trans he) (abs_nonneg _))

private theorem piecewisePlanarLp_turn {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (x : RealPlane) : piecewisePlanarLp q p (planarTurn x) = piecewisePlanarLp p q x := by
  have hprod : (planarTurn x).1 * (planarTurn x).2 = -(x.1 * x.2) := by
    change -x.2 * x.1 = _
    ring
  have hc (r : ℝ) : planarLp r (planarTurn x) = planarLp r x := by
    change (|-x.2| ^ r + |x.1| ^ r) ^ (1 / r) = (|x.1| ^ r + |x.2| ^ r) ^ (1 / r)
    rw [abs_neg, add_comm]
  rcases lt_trichotomy (x.1 * x.2) 0 with h | h | h
  · rw [piecewisePlanarLp, ite_eq_left (hprod ▸ (neg_nonneg.mpr h.le)),
      piecewisePlanarLp, ite_eq_right (not_le.mpr h), hc]
  · rw [piecewisePlanarLp, ite_eq_left (by rw [hprod, h, neg_zero]),
      piecewisePlanarLp, ite_eq_left h.ge, hc, planarLp_on_axis p hp x h,
      planarLp_on_axis q hq x h]
  · rw [piecewisePlanarLp, ite_eq_right (hprod ▸ not_le.mpr (neg_neg_of_pos h)),
      piecewisePlanarLp, ite_eq_left h.le, hc]

private theorem planarArea_le_piecewisePlanarLp {p q : ℝ} (hpq : p.HolderConjugate q)
    (v w : RealPlane) :
    |planarDot (planarTurn v) w| ≤ piecewisePlanarLp p q v * piecewisePlanarLp p q w := by
  by_cases hw : w = 0
  · simp [hw, planarDot, piecewisePlanarLp_zero hpq.pos]
  have hw' := piecewisePlanarLp_pos hpq.pos hpq.symm.pos hw
  let r := piecewisePlanarLp p q w
  have hc (u : RealPlane) (hu : piecewisePlanarLp p q u = r) :
      (r⁻¹ • u) ∈ {y | piecewisePlanarLp p q y ≤ 1} := by
    change piecewisePlanarLp p q (r⁻¹ • u) ≤ 1
    rw [piecewisePlanarLp_smul hpq.pos hpq.symm.pos, abs_of_pos (inv_pos.mpr hw'), hu,
      inv_mul_cancel₀ hw'.ne']
  have hcPlus := planarDot_le_piecewisePlanarLp hpq (planarTurn v) (r⁻¹ • w) (hc w rfl)
  have hn : piecewisePlanarLp p q (-w) = r := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      piecewisePlanarLp_smul hpq.pos hpq.symm.pos (-1) w
  have hcMinus := planarDot_le_piecewisePlanarLp hpq (planarTurn v) (r⁻¹ • -w) (hc (-w) hn)
  rw [piecewisePlanarLp_turn hpq.pos hpq.symm.pos] at hcPlus hcMinus
  have hdot (u : RealPlane) : planarDot (planarTurn v) (r⁻¹ • u) =
      r⁻¹ * planarDot (planarTurn v) u := by
    unfold planarDot
    change (planarTurn v).1 * (r⁻¹ * u.1) + (planarTurn v).2 * (r⁻¹ * u.2) = _
    ring
  rw [hdot, inv_mul_le_iff₀ hw', mul_comm] at hcPlus hcMinus
  have hneg : planarDot (planarTurn v) (-w) = -planarDot (planarTurn v) w := by
    unfold planarDot
    change (planarTurn v).1 * -w.1 + (planarTurn v).2 * -w.2 = _
    ring
  rw [hneg] at hcMinus
  exact abs_le.mpr ⟨neg_le.mp hcMinus, hcPlus⟩

private theorem exists_planarArea_eq_piecewisePlanarLp {p q : ℝ}
    (hpq : p.HolderConjugate q) {v : RealPlane} (hv : v ≠ 0) :
    ∃ w : RealPlane, piecewisePlanarLp p q w = 1 ∧
      planarDot (planarTurn v) w = piecewisePlanarLp p q v := by
  obtain ⟨w, hw, he⟩ := exists_planarDot_eq_piecewisePlanarLp hpq (planarTurn v)
  rw [piecewisePlanarLp_turn hpq.pos hpq.symm.pos] at he
  have h := planarArea_le_piecewisePlanarLp hpq v w
  have hpos := piecewisePlanarLp_pos hpq.pos hpq.symm.pos hv
  rw [he, abs_of_pos hpos] at h
  exact ⟨w, le_antisymm hw (le_of_mul_le_mul_left (by simpa only [mul_one] using h) hpos), he⟩

private theorem planarArea_zero_iff_mem_span {v : RealPlane} (hv : v ≠ 0) (z : RealPlane) :
    planarDot (planarTurn v) z = 0 ↔ z ∈ ℝ ∙ v := by
  constructor
  · intro hz
    change -v.2 * z.1 + v.1 * z.2 = 0 at hz
    by_cases h : v.1 = 0
    · have hn : v.2 ≠ 0 := fun he => hv (Prod.ext h he)
      rw [h, zero_mul, add_zero] at hz
      have hzero : z.1 = 0 := (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hn)
      refine Submodule.mem_span_singleton.mpr ⟨z.2 / v.2, Prod.ext ?_ ?_⟩
      · change z.2 / v.2 * v.1 = z.1
        rw [h, hzero, mul_zero]
      · exact div_mul_cancel₀ _ hn
    · refine Submodule.mem_span_singleton.mpr ⟨z.1 / v.1, Prod.ext (div_mul_cancel₀ _ h) ?_⟩
      change z.1 / v.1 * v.2 = z.2
      rw [div_mul_eq_mul_div, div_eq_iff h]
      linarith
  · intro hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change -v.2 * (c * v.1) + v.1 * (c * v.2) = 0
    ring

/-- **Exercise 69**, projectivity of the real piecewise planar example.
Every best approximation from a real subspace is contractive in its piecewise norm. -/
theorem exercise_69_planar_contractive {p q : ℝ} (hpq : p.HolderConjugate q)
    (L : Submodule ℝ (ℝ × ℝ)) {x y : ℝ × ℝ} (hy : y ∈ L)
    (hbest : ∀ z ∈ L, piecewisePlanarLp p q (x - y) ≤ piecewisePlanarLp p q (x - z)) :
    piecewisePlanarLp p q y ≤ piecewisePlanarLp p q x := by
  let φ := piecewisePlanarLp p q
  by_cases hL₀ : L = ⊥
  · have hy₀ : y = 0 := by simpa only [hL₀, Submodule.mem_bot] using hy
    rw [hy₀, piecewisePlanarLp_zero hpq.pos]
    exact (abs_nonneg _).trans (piecewisePlanarLp_abs_le hpq.pos hpq.symm.pos x).1
  by_cases hL₁ : L = ⊤
  · have h := hbest x (hL₁ ▸ trivial)
    rw [sub_self, piecewisePlanarLp_zero hpq.pos] at h
    by_cases he : x = y
    · exact le_of_eq (congrArg φ he).symm
    · exact False.elim ((piecewisePlanarLp_pos hpq.pos hpq.symm.pos (sub_ne_zero.mpr he)).not_ge h)
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hdimL₁ := Submodule.finrank_lt hL₁
  have hdimL₀ : Module.finrank ℝ L ≠ 0 := fun he => hL₀ (Submodule.finrank_eq_zero.mp he)
  have hdimL : Module.finrank ℝ L = 1 := by omega
  obtain ⟨v, hv, hv₀⟩ := L.ne_bot_iff.mp hL₀
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdimL hv hv₀
  have hpos := piecewisePlanarLp_pos hpq.pos hpq.symm.pos hv₀
  obtain ⟨w, hw, hdet⟩ := exists_planarArea_eq_piecewisePlanarLp hpq hv₀
  let D := fun a b : RealPlane => planarDot (planarTurn a) b
  let s := D v x / φ v
  let y₀ := x - s • w
  have hy₀ : y₀ ∈ L := by
    rw [hspan, ← planarArea_zero_iff_mem_span hv₀]
    change D v (x - s • w) = 0
    have he : D v (x - s • w) = D v x - s * D v w := by
      change -v.2 * (x.1 - s * w.1) + v.1 * (x.2 - s * w.2) = _
      dsimp [D, planarDot, planarTurn]
      ring
    rw [he, show D v w = φ v from hdet,
      show s * φ v = D v x from div_mul_cancel₀ _ hpos.ne', sub_self]
  have hupper : φ (x - y) ≤ |s| := by
    have h := hbest y₀ hy₀
    change piecewisePlanarLp p q (x - y) ≤
      piecewisePlanarLp p q (x - (x - s • w)) at h
    rw [sub_sub_cancel, piecewisePlanarLp_smul hpq.pos hpq.symm.pos, hw, mul_one] at h
    exact h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hy)
  let r := x - y
  have hVr : D v r = D v x := by
    change D v (x - y) = _
    rw [← hc]
    change -v.2 * (x.1 - c * v.1) + v.1 * (x.2 - c * v.2) = _
    dsimp [D, planarDot, planarTurn]
    ring
  have h₁ : |D v r| = φ v * φ r := by
    have h := planarArea_le_piecewisePlanarLp hpq v r
    have hsu : |s| = |D v r| / φ v := by
      rw [hVr, show s = D v x / φ v from rfl, abs_div, abs_of_pos hpos]
    rw [hsu] at hupper
    exact le_antisymm h ((mul_comm (φ v) (φ r)).trans_le ((le_div_iff₀ hpos).mp hupper))
  by_cases hr : r = 0
  · exact le_of_eq (congrArg φ (sub_eq_zero.mp hr)).symm
  have hrpos := piecewisePlanarLp_pos hpq.pos hpq.symm.pos hr
  have hY : D y r = c * D v r := by
    rw [← hc]
    change -(c * v.2) * r.1 + (c * v.1) * r.2 = _
    dsimp [D, planarDot, planarTurn]
    ring
  have hXY : D x r = D y r := by
    change -x.2 * (x.1 - y.1) + x.1 * (x.2 - y.2) =
      -y.2 * (x.1 - y.1) + y.1 * (x.2 - y.2)
    ring
  have he : |D x r| = φ y * φ r := by
    rw [hXY, hY, abs_mul, h₁, ← hc]
    change |c| * (φ v * φ r) = piecewisePlanarLp p q (c • v) * φ r
    rw [piecewisePlanarLp_smul hpq.pos hpq.symm.pos]
    ring
  have h := planarArea_le_piecewisePlanarLp hpq x r
  rw [he] at h
  exact le_of_mul_le_mul_right h hrpos


/-- The piecewise formula of Exercise 69 defines a continuous real norm. -/
theorem piecewisePlanarLp_isPositiveGauge {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsPositiveGauge (piecewisePlanarLp p q) := by
  let φ := piecewisePlanarLp p q
  have hnn (x : RealPlane) : 0 ≤ φ x :=
    (abs_nonneg _).trans (piecewisePlanarLp_abs_le hpq.pos hpq.symm.pos x).1
  have htri (v w : RealPlane) : φ (v + w) ≤ φ v + φ w := by
    obtain ⟨z, hz, he⟩ := exists_planarDot_eq_piecewisePlanarLp hpq.symm (v + w)
    have hv := planarDot_le_piecewisePlanarLp hpq.symm v z hz
    have hw := planarDot_le_piecewisePlanarLp hpq.symm w z hz
    have hadd : planarDot (v + w) z = planarDot v z + planarDot w z := by
      unfold planarDot
      change (v.1 + w.1) * z.1 + (v.2 + w.2) * z.2 = _
      ring
    change piecewisePlanarLp p q (v + w) ≤ _
    rw [← he, hadd]
    exact add_le_add hv hw
  have hbd (v : RealPlane) : φ v ≤ 2 * ‖v‖ := by
    obtain ⟨z, hz, he⟩ := exists_planarDot_eq_piecewisePlanarLp hpq.symm v
    have hcoord := piecewisePlanarLp_abs_le hpq.symm.pos hpq.pos z
    have h₀ : v.1 * z.1 ≤ ‖v‖ := calc
      _ ≤ |v.1| * |z.1| := (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ |v.1| := mul_le_of_le_one_right (abs_nonneg _) (hcoord.1.trans hz)
      _ ≤ _ := norm_fst_le v
    have h₁ : v.2 * z.2 ≤ ‖v‖ := calc
      _ ≤ |v.2| * |z.2| := (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ |v.2| := mul_le_of_le_one_right (abs_nonneg _) (hcoord.2.trans hz)
      _ ≤ _ := norm_snd_le v
    change piecewisePlanarLp p q v ≤ _
    rw [← he, planarDot]
    linarith
  have hlip : LipschitzWith 2 φ := LipschitzWith.of_dist_le_mul fun v w => by
    rw [Real.dist_eq, dist_eq_norm]
    change |φ v - φ w| ≤ 2 * ‖v - w‖
    have h₁ := htri (v - w) w
    have h₂ := htri (w - v) v
    rw [sub_add_cancel] at h₁ h₂
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hbd (w - v), norm_sub_rev w v]
    · linarith [hbd (v - w)]
  refine ⟨hlip.continuous, hnn, fun x hx => ?_, fun r x hr => ?_, htri⟩
  · by_contra h
    exact (piecewisePlanarLp_pos hpq.pos hpq.symm.pos h).ne' hx
  · rw [piecewisePlanarLp_smul hpq.pos hpq.symm.pos, abs_of_nonneg hr]

/-- **Exercise 69**, nonellipsoidality of the real two-dimensional
example for all conjugate finite exponents other than two.
The squared norm fails the parallelogram identity on the two axes. -/
theorem exercise_69_planar_not_ellipsoidal {p q : ℝ} (hpq : p.HolderConjugate q) (hp : p ≠ 2) :
    ∃ x y : ℝ × ℝ,
      piecewisePlanarLp p q (x + y) ^ 2 + piecewisePlanarLp p q (x - y) ^ 2 ≠
        2 * piecewisePlanarLp p q x ^ 2 + 2 * piecewisePlanarLp p q y ^ 2 := by
  let x : RealPlane := (1, 0)
  let y : RealPlane := (0, 1)
  have hx : piecewisePlanarLp p q x = 1 := by
    have he : x.1 * x.2 = 0 := by norm_num [x]
    rw [piecewisePlanarLp, ite_eq_left he.ge, planarLp_on_axis p hpq.pos x he]
    norm_num [x]
  have hy : piecewisePlanarLp p q y = 1 := by
    have he : y.1 * y.2 = 0 := by norm_num [y]
    rw [piecewisePlanarLp, ite_eq_left he.ge, planarLp_on_axis p hpq.pos y he]
    norm_num [y]
  have h₁ : piecewisePlanarLp p q (x + y) = 2 ^ (1 / p) := by
    rw [show x + y = (1, 1) by apply Prod.ext <;> norm_num [x, y]]
    rw [piecewisePlanarLp, ite_eq_left (by norm_num), planarLp]
    norm_num [Real.one_rpow]
  have h₂ : piecewisePlanarLp p q (x - y) = 2 ^ (1 / q) := by
    rw [show x - y = (1, -1) by apply Prod.ext <;> norm_num [x, y]]
    rw [piecewisePlanarLp, ite_eq_right (by norm_num), planarLp]
    norm_num [Real.one_rpow]
  refine ⟨x, y, ?_⟩
  rw [hx, hy, h₁, h₂]
  have hsq (r : ℝ) : ((2 : ℝ) ^ (1 / r)) ^ 2 = 2 ^ (2 / r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
    ring
  rw [hsq, hsq]
  let a : ℝ := 2 ^ (2 / p)
  let b : ℝ := 2 ^ (2 / q)
  have he : 2 / p + 2 / q = 2 := by
    simp only [div_eq_mul_inv]
    linarith [hpq.inv_add_inv_eq_one]
  have hab : a * b = 4 := by
    dsimp only [a, b]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he, Real.rpow_two]
    norm_num
  have ha : a ≠ 2 := by
    intro h
    have h' : (2 : ℝ) ^ (2 / p) = 2 ^ (1 : ℝ) := h.trans (Real.rpow_one _).symm
    have ht := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp h'
    have := (div_eq_iff hpq.ne_zero).mp ht
    apply hp
    linarith
  simp only [one_pow, mul_one]
  intro h
  change a + b = 2 + 2 at h
  have he' : a ^ 2 + a * b = (2 + 2) * a := by
    linarith [congrArg (a * ·) h]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ha)]

end

end PlanarProjectiveExercises

section BirkhoffJamesExercises

open scoped Pointwise

/-- Birkhoff–James orthogonality: zero is a best approximation
to the first vector from the span of the second vector. -/
def BirkhoffJamesOrthogonal {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x y : E) : Prop :=
  ∀ c : 𝕜, ‖x‖ ≤ ‖x - c • y‖

/-- Symmetry of Birkhoff–James orthogonality makes every best
approximation from a linear subspace contractive. -/
theorem norm_bestApprox_le_of_birkhoffJames_symmetric
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : ∀ x y : E, BirkhoffJamesOrthogonal (𝕜 := 𝕜) x y →
      BirkhoffJamesOrthogonal (𝕜 := 𝕜) y x)
    (L : Submodule 𝕜 E) {x y : E} (hy : IsBestApprox (L : Set E) x y) :
    ‖y‖ ≤ ‖x‖ := by
  have hxy : BirkhoffJamesOrthogonal (𝕜 := 𝕜) (x - y) y := by
    intro c
    have he := hy.2 (y + c • y) (L.add_mem hy.1 (L.smul_mem c hy.1))
    rw [sub_add_eq_sub_sub] at he
    exact he
  have he := h (x - y) y hxy (-1)
  rwa [neg_one_smul, sub_neg_eq_add, add_comm, sub_add_cancel] at he

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On an essentially strictly convex complex space, projectivity is
equivalent to symmetry of Birkhoff–James orthogonality. -/
theorem isProjectiveNorm_iff_birkhoffJames_symmetric (h : essentiallyStrictlyConvex E) :
    IsProjectiveNorm (E := E) ↔
      ∀ x y : E, BirkhoffJamesOrthogonal (𝕜 := ℂ) x y →
        BirkhoffJamesOrthogonal (𝕜 := ℂ) y x := by
  constructor
  · intro hP x y hxy
    let L : Submodule ℂ E := ℂ ∙ y
    have hx : definition_1 L x = 0 := by
      apply (definition_1_eq_iff h L x 0).mpr
      refine ⟨L.zero_mem, fun z hz => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      simpa only [sub_zero] using hxy c
    have ha := exercise_71 h hP L
    obtain ⟨N, hN⟩ := (corollary_5 h L).1.mp ha
    have hxN : x ∈ N := (hN x).mpr hx
    have hyL : y ∈ L := Submodule.mem_span_singleton_self _
    have hyN : definition_1 N y = 0 := (exercise_70 h L N ha (hP L) hN y).mp hyL
    intro c
    have he := (isBestApprox_definition_1 N y).2 (c • x) (N.smul_mem c hxN)
    simpa only [hyN, sub_zero] using he
  · intro hS L x
    exact norm_bestApprox_le_of_birkhoffJames_symmetric hS L (isBestApprox_definition_1 L x)

end

end BirkhoffJamesExercises

section RankLossKernelExercises

open Set Module

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- A nonzero vector of the perturbed kernel with zero original kernel
projection implies the perturbation lower estimate in (153). -/
theorem norm_rankLossPerturbation_lower_of_zeroFiber
    (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    (A : E →ₗ[ℂ] F) (X : E →L[ℂ] F) {x : E}
    (hx : x ≠ 0) (hker : (A + X.toLinearMap) x = 0) (hP : definition_1 A.ker x = 0) :
    (mixedOperatorNorm (definition_2 A))⁻¹ ≤ ‖X‖ := by
  let M := mixedOperatorNorm (definition_2 A)
  have hM : 0 ≤ M :=
    mixedOperatorNorm_nonneg (definition_2_isContinuousHomogeneous hα hβ A).continuous
  have hT : definition_2 A (A x) = x := by rw [definition_2_apply_right hβ, hP, sub_zero]
  have hTx := norm_homogeneous_apply_le (definition_2_isContinuousHomogeneous hα hβ A) (A x)
  rw [hT] at hTx
  have hAx : A x = -X x := eq_neg_of_add_eq_zero_left hker
  rw [hAx, norm_neg] at hTx
  have he : ‖x‖ ≤ (M * ‖X‖) * ‖x‖ := by
    rw [mul_assoc]
    exact hTx.trans (mul_le_mul_of_nonneg_left (X.le_opNorm x) hM)
  have hab : 1 ≤ M * ‖X‖ := by
    apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hx)
    simpa only [one_mul] using he
  have hpos : 0 < M := by
    refine lt_of_le_of_ne hM (Ne.symm fun h => ?_)
    rw [h, zero_mul] at hab
    exact (not_le_of_gt zero_lt_one) hab
  change M⁻¹ ≤ ‖X‖
  rw [← one_div, div_le_iff₀ hpos, mul_comm]
  exact hab

/-- **Exercise 81**, a second lower-bound case.
If the input kernel projector is additive, the rank-loss kernel has a
nonzero vector in its zero fiber by finite-dimensional rank-nullity. -/
theorem exercise_81_lower_of_additive_kernelProjection
    (hα : essentiallyStrictlyConvex F) (hβ : essentiallyStrictlyConvex E)
    {A : E →ₗ[ℂ] F} (hA : A ≠ 0)
    (hadd : ∀ x y, definition_1 A.ker (x + y) =
      definition_1 A.ker x + definition_1 A.ker y) :
    (mixedOperatorNorm (definition_2 A))⁻¹ ≤ rankLossDistance A := by
  let S := ((fun X : E →L[ℂ] F => ‖X‖) ''
    {X : E →L[ℂ] F | Module.finrank ℂ (A + X.toLinearMap).range <
      Module.finrank ℂ A.range})
  have hne : S.Nonempty := by
    let K : E →L[ℂ] F := LinearMap.toContinuousLinearMap (-A)
    refine ⟨‖K‖, K, ?_, rfl⟩
    change finrank ℂ (A + -A).range < finrank ℂ A.range
    rw [show A + -A = 0 from add_neg_cancel A, LinearMap.range_zero, finrank_bot]
    have hn : finrank ℂ A.range ≠ 0 := fun he => hA
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he))
    omega
  change _ ≤ sInf S
  refine le_csInf hne ?_
  rintro _ ⟨X, hX, rfl⟩
  let B := A + X.toLinearMap
  let P := (additiveMetricProjection hβ A.ker hadd).toLinearMap
  let C : B.ker →ₗ[ℂ] A.ker :=
    (P.comp B.ker.subtype).codRestrict A.ker fun z => definition_1_mem A.ker z.val
  have hlt : finrank ℂ A.ker < finrank ℂ B.ker := by
    have ha := A.finrank_range_add_finrank_ker
    have hb := B.finrank_range_add_finrank_ker
    change finrank ℂ B.range < finrank ℂ A.range at hX
    omega
  have hC : C.ker ≠ ⊥ := by
    intro h
    have he := C.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    exact (not_le_of_gt hlt) he
  obtain ⟨u, hu, hu₀⟩ := C.ker.ne_bot_iff.mp hC
  have hz : definition_1 A.ker (u : E) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
  have hu₀' : (u : E) ≠ 0 := fun h => hu₀ (Subtype.ext h)
  exact norm_rankLossPerturbation_lower_of_zeroFiber hα hβ A X hu₀' u.property hz

end

end RankLossKernelExercises

end BenIsraelGreville.Chapter03
