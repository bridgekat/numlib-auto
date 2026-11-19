/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

end BenIsraelGreville.Chapter03
