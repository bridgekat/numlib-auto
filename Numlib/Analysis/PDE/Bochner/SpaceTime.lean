import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.PDE.Bochner
import Numlib.Analysis.Sobolev.EmbeddingDomain

/-!
# The space–time reading of a curve of Sobolev functions

A curve `t ↦ u(t)` with values in `L²(Ω)` which is, on a set of times `s`, of class
`C^k(s; H^m(Ω))` in the sense of `Bochner.ContDiffOnThrough` — it factors through the inclusion
`H^m(Ω) → L²(Ω)` by a `C^k` curve of `H^m(Ω)` — is read as a function `U(x, t)` of space and time
through the continuous representatives of the Sobolev embedding theorems on a domain
(`Numlib/Analysis/Sobolev/EmbeddingDomain`, Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Corollaries 9.14–9.15). This is the sense in which
[brezis2011functional] Theorems 10.1 (5), 10.2 (c), 10.8 and Corollary 10.5 state the regularity
of the solutions of the heat and wave equations in space and time.

## Main results

* `Bochner.continuousOn_prod_of_forall_norm_sub_le`: the general joint-continuity lemma behind the
  bridge — if `rep w` is continuous on `K` for every `w`, and `‖rep w₁ x − rep w₂ x‖ ≤ C ‖w₁ − w₂‖`
  on `K`, then `(x, t) ↦ rep (v t) x` is continuous on `K ×ˢ s` for every `v` continuous on `s`.
* `Bochner.eqOn_closure_of_ae_eq`: two continuous functions almost everywhere equal on an open
  set agree on its closure (the uniqueness of continuous representatives).
* `Bochner.continuousOn_spaceTime_of_contDiffOnThrough`: **the `k = 0` bridge** — for an extension
  domain `Ω` (a `C¹` domain with bounded boundary, or the half space) and `m > N/2`, a curve
  `u ∈ C(s; H^m(Ω))` read in `L²(Ω)` has a space–time representative `U` continuous on
  `closure Ω ×ˢ s` with `U(·, t) = u(t)` almost everywhere on `Ω` for every `t ∈ s`. This is what
  [brezis2011functional] Corollary 10.5 (`u ∈ C(Q̄)`) needs.

The `C^∞` bridge, `Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough` (joint
smoothness of `U` from smoothness of `t ↦ u(t)` into every `H^m(Ω)`, [brezis2011functional]
Theorems 10.1 (5), 10.2 (c) and 10.8), is planned in this module and not yet proved: it rests on
the calculus fact that a function on `E × ℝ` whose partial derivatives of every order exist and are
jointly continuous is `C^∞`, which is not in Mathlib.

## References

[brezis2011functional], §10.1–10.3, and chapter 9, Corollaries 9.14–9.15 with footnote 16.
-/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace Bochner

/-! ### Joint continuity of `(x, t) ↦ rep (v t) x` -/

/-- **Joint continuity from a uniformly Lipschitz family of continuous functions**: let
`rep : V → X → F` be such that every `rep w` is continuous on `K` and
`‖rep w₁ x − rep w₂ x‖ ≤ C ‖w₁ − w₂‖` for `x ∈ K`. Then for every `v : ℝ → V` continuous on
`s`, the function `(x, t) ↦ rep (v t) x` is continuous on `K ×ˢ s`: the difference at `(x, t)` and
`(x₀, t₀)` is bounded by `C ‖v t − v t₀‖ + ‖rep (v t₀) x − rep (v t₀) x₀‖`. -/
theorem continuousOn_prod_of_forall_norm_sub_le {X V F : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedAddCommGroup F] {rep : V → X → F} {K : Set X} {C : ℝ}
    (hcont : ∀ w, ContinuousOn (rep w) K)
    (hsub : ∀ w₁ w₂, ∀ x ∈ K, ‖rep w₁ x - rep w₂ x‖ ≤ C * ‖w₁ - w₂‖)
    {v : ℝ → V} {s : Set ℝ} (hv : ContinuousOn v s) :
    ContinuousOn (fun q : X × ℝ ↦ rep (v q.2) q.1) (K ×ˢ s) := by
  intro q hq
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hC : 0 ≤ |C| + 1 := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 (hv q.2 hq.2) (ε / (2 * (|C| + 1)))
    (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 (hcont (v q.2) q.1 hq.1) (ε / 2)
    (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp hpq ↦ ?_⟩
  have hp1 : dist p.1 q.1 < δ₂ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (Prod.dist_eq (x := p) (y := q)).ge)
      (hpq.trans_le (min_le_right _ _))
  have hp2 : dist p.2 q.2 < δ₁ :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (Prod.dist_eq (x := p) (y := q)).ge)
      (hpq.trans_le (min_le_left _ _))
  have hA : dist (rep (v p.2) p.1) (rep (v q.2) p.1) ≤ ε / 2 := by
    rw [dist_eq_norm]
    refine (hsub _ _ p.1 hp.1).trans ?_
    have h3 := h₁ hp.2 hp2
    rw [dist_eq_norm] at h3
    calc C * ‖v p.2 - v q.2‖ ≤ |C| * ‖v p.2 - v q.2‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ |C| * (ε / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h3.le (abs_nonneg C)
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg C) hε.le]
  calc dist (rep (v p.2) p.1) (rep (v q.2) q.1)
      ≤ dist (rep (v p.2) p.1) (rep (v q.2) p.1) + dist (rep (v q.2) p.1) (rep (v q.2) q.1) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hA (h₂ hp.1 hp1)
    _ = ε := add_halves ε

/-! ### Uniqueness of continuous representatives up to the boundary -/

/-- **Two continuous functions almost everywhere equal on an open set agree on its closure**
(for a measure positive on open sets): the continuous representative of a Sobolev function is
unique on `Ω̄`. -/
theorem eqOn_closure_of_ae_eq {X F : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace F] [T2Space F] {μ : Measure X} [μ.IsOpenPosMeasure] {Ω : Set X}
    (hΩ : IsOpen Ω) {f g : X → F} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[μ.restrict Ω] g) : EqOn f g (closure Ω) :=
  (Measure.eqOn_open_of_ae_eq h hΩ hf.continuousOn hg.continuousOn).of_subset_closure
    hf.continuousOn hg.continuousOn subset_closure subset_rfl

/-! ### The `k = 0` bridge -/

variable {N m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Joint continuity from continuity into `H^m(Ω)`** (the `k = 0` space–time bridge). Let `Ω` be
an extension domain for every exponent (a `C¹` domain with bounded boundary, or the half space;
`IsSobolevExtensionDomainAll`), `m > N/2`, `s ⊆ ℝ`, and let `u : ℝ → L²(Ω)` be of class
`C(s; H^m(Ω))` — it factors on `s` through the inclusion `H^m(Ω) → L²(Ω)` by a curve `v`
continuous on `s`. Then there is `U : ℝ^N × ℝ → ℝ`, continuous on `closure Ω ×ˢ s`, with
`U(·, t) = u(t)` almost everywhere on `Ω` for every `t ∈ s`.

Proof: Corollary 9.15 at `k = 0`
(`SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`) gives every
`w ∈ H^m(Ω)` a continuous representative `w̃` on `ℝ^N` with `‖w̃‖_∞ ≤ C ‖w‖`. The
representative is unique on `closure Ω` (`eqOn_closure_of_ae_eq`), so `w ↦ w̃` is additive there
and `‖w̃₁ x − w̃₂ x‖ ≤ C ‖w₁ − w₂‖` for `x ∈ closure Ω`; `U(x, t) := (v t)~(x)` is then jointly
continuous by `continuousOn_prod_of_forall_norm_sub_le`. This is what [brezis2011functional]
Corollary 10.5 (`u ∈ C(Q̄)`) needs. -/
theorem continuousOn_spaceTime_of_contDiffOnThrough (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hm : (N : ℝ) / 2 < m) {s : Set ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      m 2 Ω volume) 0 u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      ContinuousOn U (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) ∧
      ∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t := by
  obtain ⟨v, hv, huv⟩ := hu
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_two⟩
  obtain ⟨C, θ, hC0, -, -, -, hrep⟩ :=
    SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension (p := 2)
      (m := m) hΩ (Or.inr one_lt_two) (by exact_mod_cast hm)
  choose rep hrepc hrepae hrepb hrepH using hrep
  clear hrepH
  -- the representatives are additive on `closure Ω`
  have hsub : ∀ w₁ w₂ : SobolevEuclidean N m ((2 : ℝ≥0) : ℝ≥0∞) Ω,
      ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ‖rep w₁ x - rep w₂ x‖ ≤ C * ‖w₁ - w₂‖ := by
    intro w₁ w₂ x hx
    -- `rep (w₁ − w₂) + rep w₂` and `rep w₁` are continuous representatives of `fn w₁`
    have h1 : SobolevMultiIndex.fn w₁ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (w₁ - w₂) + SobolevMultiIndex.fn w₂ := by
      have h2 := SobolevMultiIndex.fn_add (w₁ - w₂) w₂
      rwa [sub_add_cancel] at h2
    have heq : EqOn (rep w₁) (rep (w₁ - w₂) + rep w₂)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc w₁) ((hrepc _).add (hrepc w₂)) ?_
      filter_upwards [hrepae w₁, hrepae w₂, hrepae (w₁ - w₂), h1] with x hx₁ hx₂ hx₃ hx₄
      rw [← hx₁, hx₄, Pi.add_apply, Pi.add_apply, hx₂, hx₃]
    have h3 := heq hx
    rw [Pi.add_apply] at h3
    rw [h3, add_sub_cancel_right]
    exact hrepb _ x
  refine ⟨fun q ↦ rep (v q.2) q.1, ?_, fun t ht ↦ ?_⟩
  · exact continuousOn_prod_of_forall_norm_sub_le (fun w ↦ (hrepc w).continuousOn) hsub
      hv.continuousOn
  · rw [huv t ht, SobolevMultiIndex.fnL_apply]
    exact (hrepae (v t)).symm

end Bochner
