import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Calculus.ProdContDiff
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
* `Bochner.exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough`: **the `C^k` bridge** — for
  `k + N/2 < m` and `s` uniquely differentiable, a curve `u ∈ C^k(s; H^m(Ω))` has a space–time
  representative `U` of class `C^k` on `Ω ×ˢ s` whose derivatives within `Ω ×ˢ s` extend
  continuously to `closure Ω ×ˢ s` (`ContDiffOnExtendsTo`, from
  `Numlib.Analysis.Calculus.ProdContDiff`). The partial derivatives `∂ₜ^j D_x^i U (x, t)` are
  `D^i (rep (u^{(j)} t)) x`, the continuous extensions of the derivatives of the canonical
  `C^k(Ω̄)` representatives of Corollary 9.15: these are linear in `u` on `closure Ω` by the
  uniqueness of continuous representatives (`eqOn_closure_deriv_rep_add`,
  `eqOn_closure_deriv_rep_smul`), so that evaluation at a point commutes with `d/dt`
  (`hasDerivWithinAt_of_forall_add_smul_norm_le`), and the product-calculus theorem
  `contDiffOnExtendsTo_prod_of_partials` assembles the joint derivatives.
* `Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough` (with the variants `_Ioi`,
  `_Ici` and the within-form `contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough`):
  **the `C^∞` bridge** — a curve `u ∈ C^∞(s; H^m(Ω))` for every `m` has a space–time
  representative of class `C^∞(Ω̄ × s̄')`, in the sense of `ContDiffOnClosure`, on `Ω ×ˢ s'` for
  every open `s'` with `closure s' ⊆ s`: [brezis2011functional] Theorem 10.1 (5)
  (`u ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`), Theorem 10.2 (c) and Theorem 10.8
  (`u ∈ C^∞(Ω̄ × [0, ∞))`). The extension stops at `closure s' ⊆ s` because the curve need not be
  continuous into `H^m(Ω)` at the boundary of `s`.

## References

[brezis2011functional], §10.1–10.3, and chapter 9, Corollaries 9.14–9.15 with footnote 16.
-/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff ENNReal NNReal

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


/-! ### The canonical `C^k(Ω̄)` representatives are linear on the closure -/

section Linearity

variable {N m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0∞}
  {rep : SobolevEuclidean N m p Ω → EuclideanSpace ℝ (Fin N) → ℝ}

/-- The continuous representatives of a sum: `rep (w₁ + w₂) = rep w₁ + rep w₂` on `closure Ω`, by
the uniqueness of continuous representatives (`eqOn_closure_of_ae_eq`). -/
theorem eqOn_closure_rep_add (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (w₁ w₂ : SobolevEuclidean N m p Ω) :
    EqOn (rep (w₁ + w₂)) (rep w₁ + rep w₂) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc _) ((hrepc w₁).add (hrepc w₂)) ?_
  filter_upwards [hrepae w₁, hrepae w₂, hrepae (w₁ + w₂), SobolevMultiIndex.fn_add w₁ w₂]
    with x h₁ h₂ h₃ h₄
  rw [← h₃, h₄, Pi.add_apply, Pi.add_apply, h₁, h₂]

/-- The continuous representatives of a multiple: `rep (c • w) = c • rep w` on `closure Ω`. -/
theorem eqOn_closure_rep_smul (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (c : ℝ) (w : SobolevEuclidean N m p Ω) :
    EqOn (rep (c • w)) (c • rep w) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc _) ((hrepc w).const_smul c) ?_
  filter_upwards [hrepae w, hrepae (c • w), SobolevMultiIndex.fn_smul c w] with x h₁ h₂ h₃
  rw [← h₂, h₃, Pi.smul_apply, Pi.smul_apply, h₁]

variable {k : ℕ} {G : SobolevEuclidean N m p Ω → EuclideanSpace ℝ (Fin N) →
  (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ)}

/-- On the open set `Ω`, the `k`-th derivative of a function of class `C^k` on `Ω` that agrees
on `Ω` with `f₁ + f₂` is the sum of the derivatives. -/
theorem iteratedFDeriv_add_of_eqOn {f f₁ f₂ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h : EqOn f (f₁ + f₂) (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (h₁ : ContDiffOn ℝ k f₁ Ω) (h₂ : ContDiffOn ℝ k f₂ Ω) {x : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ Ω) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k f₁ x + iteratedFDeriv ℝ k f₂ x := by
  have heq : f =ᶠ[𝓝 x] f₁ + f₂ := eventually_of_mem (Ω.isOpen.mem_nhds hx) h
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    iteratedFDerivWithin_add_apply (h₁ x hx) (h₂ x hx) Ω.isOpen.uniqueDiffOn hx]

/-- On the open set `Ω`, the `k`-th derivative of a function of class `C^k` on `Ω` that agrees
on `Ω` with `c • f₁` is `c` times the derivative. -/
theorem iteratedFDeriv_smul_of_eqOn {f f₁ : EuclideanSpace ℝ (Fin N) → ℝ} {c : ℝ}
    (h : EqOn f (c • f₁) (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (h₁ : ContDiffOn ℝ k f₁ Ω) {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ k f x = c • iteratedFDeriv ℝ k f₁ x := by
  have heq : f =ᶠ[𝓝 x] c • f₁ := eventually_of_mem (Ω.isOpen.mem_nhds hx) h
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    iteratedFDerivWithin_const_smul_apply (h₁ x hx) Ω.isOpen.uniqueDiffOn hx]

/-- The continuous extensions `G w` of the derivatives `D^k (rep w)` of the canonical
representatives are additive on `closure Ω`. -/
theorem eqOn_closure_deriv_rep_add (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (hrepd : ∀ w, ContDiffOn ℝ k (rep w) Ω) (hGc : ∀ w, Continuous (G w))
    (hGe : ∀ w, EqOn (iteratedFDeriv ℝ k (rep w)) (G w) Ω) (w₁ w₂ : SobolevEuclidean N m p Ω) :
    EqOn (G (w₁ + w₂)) (G w₁ + G w₂) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine EqOn.of_subset_closure (fun x hx ↦ ?_) (hGc _).continuousOn
    ((hGc w₁).add (hGc w₂)).continuousOn subset_closure subset_rfl
  rw [Pi.add_apply, ← hGe _ hx, ← hGe _ hx, ← hGe _ hx]
  exact iteratedFDeriv_add_of_eqOn (eqOn_closure_rep_add hrepc hrepae w₁ w₂ |>.mono
    subset_closure) (hrepd w₁) (hrepd w₂) hx

/-- The continuous extensions `G w` of the derivatives `D^k (rep w)` of the canonical
representatives are homogeneous on `closure Ω`. -/
theorem eqOn_closure_deriv_rep_smul (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (hrepd : ∀ w, ContDiffOn ℝ k (rep w) Ω) (hGc : ∀ w, Continuous (G w))
    (hGe : ∀ w, EqOn (iteratedFDeriv ℝ k (rep w)) (G w) Ω) (c : ℝ)
    (w : SobolevEuclidean N m p Ω) :
    EqOn (G (c • w)) (c • G w) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine EqOn.of_subset_closure (fun x hx ↦ ?_) (hGc _).continuousOn
    ((hGc w).const_smul c).continuousOn subset_closure subset_rfl
  rw [Pi.smul_apply, ← hGe _ hx, ← hGe _ hx]
  exact iteratedFDeriv_smul_of_eqOn (eqOn_closure_rep_smul hrepc hrepae c w |>.mono
    subset_closure) (hrepd w) hx

end Linearity

/-! ### Evaluation of a bounded linear family commutes with `d/dt` -/

section Linear

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {Φ : V → W}

/-- An additive, homogeneous map bounded by `C ‖w‖` is Lipschitz with constant `C`. -/
theorem norm_sub_le_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖) (w₁ w₂ : V) :
    ‖Φ w₁ - Φ w₂‖ ≤ C * ‖w₁ - w₂‖ := by
  let L : V →ₗ[ℝ] W := ⟨⟨Φ, hadd⟩, hsmul⟩
  have : Φ w₁ - Φ w₂ = Φ (w₁ - w₂) := (map_sub L w₁ w₂).symm
  rw [this]
  exact hb _

/-- **A bounded linear map commutes with the derivative of a curve**: if `Φ` is additive,
homogeneous and bounded by `C ‖w‖`, then `Φ ∘ v` has derivative `Φ v'` within `s` wherever `v`
has derivative `v'`. This is how the evaluation at a point of the canonical `C^k(Ω̄)`
representative — a bounded linear functional of `w ∈ H^m(Ω)` — commutes with `d/dt`. -/
theorem hasDerivWithinAt_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖)
    {v : ℝ → V} {v' : V} {s : Set ℝ} {t : ℝ} (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun r ↦ Φ (v r)) (Φ v') s t := by
  let L : V →L[ℝ] W := LinearMap.mkContinuous ⟨⟨Φ, hadd⟩, hsmul⟩ C hb
  exact L.hasFDerivAt.comp_hasDerivWithinAt t hv

end Linear



/-! ### Lowering the Sobolev order of a curve -/

section LowerOrder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {b : Module.Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}
  {μ : Measure E}

/-- The inclusion `W^{k,p}(Ω) → L^p(Ω)` factors through `W^{k',p}(Ω)` for `k' ≤ k`. -/
theorem _root_.SobolevMultiIndex.fnL_comp_toLowerOrderL {k k' : ℕ} (hk : k' ≤ k) :
    (SobolevMultiIndex.fnL F b k' p Ω μ).comp (SobolevMultiIndex.toLowerOrderL F b p Ω μ hk) =
      SobolevMultiIndex.fnL F b k p Ω μ :=
  rfl

/-- **A curve of class `C^n(s; W^{k,p}(Ω))` is of class `C^n(s; W^{k',p}(Ω))` for `k' ≤ k`**: the
hypothesis `∀ m, u ∈ C^∞(s; H^m(Ω))` of the space–time bridge follows from
`u ∈ C^∞(s; H^{2ℓ}(Ω))` for every `ℓ`. -/
theorem ContDiffOnThrough.sobolev_of_le {k k' : ℕ} (hk : k' ≤ k) {n : WithTop ℕ∞}
    {u : ℝ → Lp F p (μ.restrict (Ω : Set E))} {s : Set ℝ}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL F b k p Ω μ) n u s) :
    ContDiffOnThrough (SobolevMultiIndex.fnL F b k' p Ω μ) n u s := by
  rw [← SobolevMultiIndex.fnL_comp_toLowerOrderL hk] at hu
  exact hu.of_comp

end LowerOrder

/-! ### The `C^k` bridge -/

section Bridge

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Joint `C^k` regularity from `C^k` regularity into `H^m(Ω)`, `k + N/2 < m`** (the
finite-order space–time bridge). Let `Ω` be an extension domain for every exponent
(`IsSobolevExtensionDomainAll`), `s ⊆ ℝ` uniquely differentiable, `k + N/2 < m`, and let
`u : ℝ → L²(Ω)` be of class `C^k(s; H^m(Ω))` — it factors on `s` through the inclusion
`H^m(Ω) → L²(Ω)` by a curve `v` of class `C^k` on `s`. Then there is `U : ℝ^N × ℝ → ℝ`, with
`U (·, t)` continuous and `= u t` almost everywhere on `Ω` for every `t ∈ s`, which is `C^k` on
`Ω ×ˢ s` with every derivative (within `Ω ×ˢ s`) extending continuously to `closure Ω ×ˢ s`.

Proof. Corollary 9.15 (`SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`)
gives every `w ∈ H^m(Ω)` a representative `rep w`, continuous on `ℝ^N` and `C^k` on `Ω`, whose
derivatives `D^i (rep w)`, `i ≤ k`, extend continuously to `ℝ^N` with `‖D^i (rep w)‖ ≤ C ‖w‖`.
The extensions are additive and homogeneous on `closure Ω` by the uniqueness of continuous
representatives (`eqOn_closure_deriv_rep_add`, `eqOn_closure_deriv_rep_smul`), so that the
evaluation `w ↦ D^i (rep w) x` at `x ∈ closure Ω` is a bounded linear functional of `w`. With
`v^{(j)} := iteratedDerivWithin j v s`, the family `g i j (x, t) := D^i (rep (v^{(j)} t)) x` is
jointly continuous on `closure Ω ×ˢ s` (`continuousOn_prod_of_forall_norm_sub_le`), the
`x`-derivative of `g i j` is `g (i + 1) j` (curried), and the `t`-derivative of `g i j` is
`g i (j + 1)` (the bounded linear evaluation commutes with `d/dt`,
`hasDerivWithinAt_of_forall_add_smul_norm_le`). The product-calculus theorem
`contDiffOnExtendsTo_prod_of_partials` then makes `U := g 0 0` of class `C^k` on `Ω ×ˢ s` with
derivatives extending to `closure Ω ×ˢ s`. This is [brezis2011functional], proof of
Theorem 10.1, the step "`u ∈ C^k((0, ∞); H^{2ℓ}(Ω))` for all `k, ℓ` ⇒ `u ∈ C^∞(Ω̄ × [ε, ∞))`"
made explicit at a fixed order. -/
theorem exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {k m : ℕ}
    (hm : (k : ℝ) + N / 2 < m)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      m 2 Ω volume) k u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, Continuous fun x ↦ U (x, t)) ∧
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ k U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
  obtain ⟨v, hv, huv⟩ := hu
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_two⟩
  obtain ⟨C, θ, hC0, -, -, -, hrep⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (p := 2) (m := m) k hΩ
      (Or.inr one_lt_two) (by exact_mod_cast hm)
  choose rep hrepc hrepd hrepae hG hGk using hrep
  clear hGk
  -- a total family of continuous extensions of the derivatives `D^j (rep w)`, `j ≤ k`
  have hG' : ∀ w : SobolevEuclidean N m ((2 : ℝ≥0) : ℝ≥0∞) Ω,
      ∃ G : (j : ℕ) → EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        ∀ j ≤ k, Continuous (G j) ∧ EqOn (iteratedFDeriv ℝ j (rep w)) (G j) Ω ∧
          ∀ x, ‖G j x‖ ≤ C * ‖w‖ := by
    intro w
    choose G hG using hG w
    exact ⟨fun j ↦ if h : j ≤ k then G j h else 0, fun j hj ↦ by
      simp only [dite_eq_left hj]
      exact hG j hj⟩
  choose G hG using hG'
  have hGc : ∀ j ≤ k, ∀ w, Continuous (G w j) := fun j hj w ↦ (hG w j hj).1
  have hGe : ∀ j ≤ k, ∀ w, EqOn (iteratedFDeriv ℝ j (rep w)) (G w j) Ω :=
    fun j hj w ↦ (hG w j hj).2.1
  have hGb : ∀ j ≤ k, ∀ w x, ‖G w j x‖ ≤ C * ‖w‖ := fun j hj w x ↦ (hG w j hj).2.2 x
  -- the extensions are linear on `closure Ω`
  have hGadd : ∀ j ≤ k, ∀ w₁ w₂, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
      G (w₁ + w₂) j x = G w₁ j x + G w₂ j x := fun j hj w₁ w₂ x hx ↦
    eqOn_closure_deriv_rep_add hrepc hrepae (fun w ↦ (hrepd w).of_le (by exact_mod_cast hj))
      (hGc j hj) (hGe j hj) w₁ w₂ hx
  have hGsmul : ∀ j ≤ k, ∀ (c : ℝ) w, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
      G (c • w) j x = c • G w j x := fun j hj c w x hx ↦
    eqOn_closure_deriv_rep_smul hrepc hrepae (fun w ↦ (hrepd w).of_le (by exact_mod_cast hj))
      (hGc j hj) (hGe j hj) c w hx
  -- the time derivatives of the lift
  have hv'c : ∀ j ≤ k, ContinuousOn (iteratedDerivWithin j v s) s := fun j hj ↦
    hv.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  have hv'd : ∀ j < k, ∀ t ∈ s,
      HasDerivWithinAt (iteratedDerivWithin j v s) (iteratedDerivWithin (j + 1) v s t) s t := by
    intro j hj t ht
    rw [iteratedDerivWithin_succ]
    exact (hv.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs t ht).hasDerivWithinAt
  -- the family of partial derivatives `g i j (x, t) = D^i (rep (v^{(j)} t)) x`
  have hgc : ∀ i j, i + j ≤ k → ContinuousOn
      (fun q : EuclideanSpace ℝ (Fin N) × ℝ ↦ G (iteratedDerivWithin j v s q.2) i q.1)
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
    intro i j hij
    refine continuousOn_prod_of_forall_norm_sub_le (rep := fun w x ↦ G w i x) (C := C)
      (fun w ↦ (hGc i (by omega) w).continuousOn) (fun w₁ w₂ x hx ↦ ?_) (hv'c j (by omega))
    exact norm_sub_le_of_forall_add_smul_norm_le (Φ := fun w ↦ G w i x)
      (fun w₁ w₂ ↦ hGadd i (by omega) w₁ w₂ x hx) (fun c w ↦ hGsmul i (by omega) c w x hx)
      (fun w ↦ hGb i (by omega) w x) w₁ w₂
  have hgx : ∀ i j, i + 1 + j ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasFDerivAt (fun y ↦ G (iteratedDerivWithin j v s t) i y)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin N)) ℝ
          (G (iteratedDerivWithin j v s t) (i + 1) x)) x := by
    intro i j hij x hx t ht
    have hd : DifferentiableOn ℝ (iteratedFDeriv ℝ i (rep (iteratedDerivWithin j v s t))) Ω := by
      have := (hrepd (iteratedDerivWithin j v s t)).differentiableOn_iteratedFDerivWithin (m := i)
        (by exact_mod_cast (by omega : i < k)) Ω.isOpen.uniqueDiffOn
      exact this.congr fun y hy ↦ (iteratedFDerivWithin_of_isOpen i Ω.isOpen hy).symm
    have h1 := (hd.differentiableAt (Ω.isOpen.mem_nhds hx)).hasFDerivAt
    have h2 : fderiv ℝ (iteratedFDeriv ℝ i (rep (iteratedDerivWithin j v s t))) x =
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin N)) ℝ
          (iteratedFDeriv ℝ (i + 1) (rep (iteratedDerivWithin j v s t)) x) := by
      ext y w
      rw [continuousMultilinearCurryLeftEquiv_apply, iteratedFDeriv_succ_apply_left,
        Fin.cons_zero, Fin.tail_cons]
    rw [h2, hGe (i + 1) (by omega) _ hx] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact (hGe i (by omega) _ hy).symm
  have hgt : ∀ i j, i + (j + 1) ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasDerivWithinAt (fun r ↦ G (iteratedDerivWithin j v s r) i x)
        (G (iteratedDerivWithin (j + 1) v s t) i x) s t := by
    intro i j hij x hx t ht
    exact hasDerivWithinAt_of_forall_add_smul_norm_le (Φ := fun w ↦ G w i x)
      (fun w₁ w₂ ↦ hGadd i (by omega) w₁ w₂ x (subset_closure hx))
      (fun c w ↦ hGsmul i (by omega) c w x (subset_closure hx)) (fun w ↦ hGb i (by omega) w x)
      (hv'd j (by omega) t ht)
  have hmain := contDiffOnExtendsTo_prod_of_partials Ω.isOpen hs
    (prod_mono_left subset_closure)
    (g := fun i j q ↦ G (iteratedDerivWithin j v s q.2) i q.1) hgc hgx hgt k 0 0 (by omega)
  have hv0 : iteratedDerivWithin 0 v s = v := iteratedDerivWithin_zero
  refine ⟨fun q ↦ continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
    (G (iteratedDerivWithin 0 v s q.2) 0 q.1), fun t ht ↦ ?_, fun t ht ↦ ?_, ?_⟩
  · exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ).continuous.comp
      (hGc 0 (by omega) (iteratedDerivWithin 0 v s t))
  · rw [huv t ht, SobolevMultiIndex.fnL_apply]
    refine EventuallyEq.trans ?_ (hrepae (v t)).symm
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    change continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
      (G (iteratedDerivWithin 0 v s t) 0 x) = rep (v t) x
    rw [← hGe 0 (by omega) _ hx, continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
    exact congrArg (fun w ↦ rep w x) (congrFun hv0 t)
  · exact hmain.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ).toContinuousLinearEquiv :
        (EuclideanSpace ℝ (Fin N) [×0]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (UniqueDiffOn.prod Ω.isOpen.uniqueDiffOn hs)


/-- **Joint smoothness from smoothness into every `H^m(Ω)`** (the space–time bridge, in the form
of derivatives within `Ω ×ˢ s`). Let `Ω` be an extension domain for every exponent, `s ⊆ ℝ`
uniquely differentiable, and let `u : ℝ → L²(Ω)` be of class `C^∞(s; H^m(Ω))` for every `m`.
Then there is `U : ℝ^N × ℝ → ℝ` with `U (·, t) = u t` almost everywhere on `Ω` for `t ∈ s`, which
is `C^∞` on `Ω ×ˢ s` with every derivative within `Ω ×ˢ s` extending continuously to
`closure Ω ×ˢ s`. Each order `k` is the finite-order bridge
`exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough` at `m = k + N + 1`; the `U` produced
at different orders agree on `closure Ω ×ˢ s` by the uniqueness of continuous representatives
(`eqOn_closure_of_ae_eq`), so the one of order `0` serves for all. -/
theorem contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
  have hpack : ∀ k : ℕ, ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, Continuous fun x ↦ U (x, t)) ∧
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ k U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := fun k ↦
    exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough hΩ hs (m := k + N + 1)
      (by push_cast; linarith [half_le_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      ((hu (k + N + 1)).of_le (by simp))
  choose U hUc hUae hU using hpack
  refine ⟨U 0, hUae 0, contDiffOnExtendsTo_infty_iff.2 fun k ↦ (hU k).congr fun q hq ↦ ?_⟩
  obtain ⟨x, t⟩ := q
  obtain ⟨hx, ht⟩ : x ∈ Ω ∧ t ∈ s := hq
  exact eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hUc 0 t ht) (hUc k t ht)
    ((hUae 0 t ht).trans (hUae k t ht).symm) (subset_closure hx)

/-- **Joint smoothness from smoothness into every `H^m(Ω)`** (the space–time bridge). Let `Ω` be
an extension domain for every exponent (a `C¹` domain with bounded boundary, or the half space;
`IsSobolevExtensionDomainAll`), `s ⊆ ℝ` uniquely differentiable, and let `u : ℝ → L²(Ω)` be of
class `C^∞(s; H^m(Ω))` for every `m` — it factors on `s` through the inclusion `H^m(Ω) → L²(Ω)`
by a `C^∞` curve. Then there is `U : ℝ^N × ℝ → ℝ` with `U (·, t) = u t` almost everywhere on `Ω`
for every `t ∈ s`, which is of class `C^∞(Ω̄ × s̄')` in the sense of `ContDiffOnClosure` on
`Ω ×ˢ s'` for every open `s'` whose closure lies in `s`: `C^∞` on `Ω × s'`, every derivative
extending continuously to `closure Ω × closure s'`. With `s = (0, ∞)` and `s' = (ε, ∞)` this is
[brezis2011functional] Theorem 10.1 (5), `u ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`; with
`s = [0, ∞)` and `s' = (0, ∞)` it is Theorem 10.2 (c) and Theorem 10.8, `u ∈ C^∞(Ω̄ × [0, ∞))`.
The extension is asked only up to `closure s' ⊆ s` because the curve `t ↦ u(t)` need not be
continuous into `H^m(Ω)` at the boundary of `s` (the heat equation with `L²` data is not smooth
at `t = 0`).

Proof: `contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough` and
`ContDiffOnExtendsTo.contDiffOnClosure`. -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ∀ s' : Set ℝ, IsOpen s' → closure s' ⊆ s →
        ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s') := by
  obtain ⟨U, hUae, hU⟩ := contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough hΩ hs hu
  refine ⟨U, hUae, fun s' hs' hs's ↦ hU.contDiffOnClosure (Ω.isOpen.prod hs')
    (prod_mono_right (subset_closure.trans hs's)) ?_⟩
  rw [closure_prod_eq]
  exact prod_mono_right hs's

/-- **The bridge on `(a, ∞)`**: a curve of class `C^∞((a, ∞); H^m(Ω))` for every `m` has a
space–time representative `U` of class `C^∞(Ω̄ × [ε, ∞))` for every `ε > a`
([brezis2011functional] Theorem 10.1 (5), `a = 0`). -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi
    (hΩ : IsSobolevExtensionDomainAll N Ω) {a : ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u (Ioi a)) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ Ioi a,
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ∀ ε > a, ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ Ioi ε) := by
  obtain ⟨U, hUae, hU⟩ :=
    contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough hΩ (uniqueDiffOn_Ioi a) hu
  exact ⟨U, hUae, fun ε hε ↦ hU (Ioi ε) isOpen_Ioi (by rw [closure_Ioi]; exact Ici_subset_Ioi.2 hε)⟩

/-- **The bridge on `[a, ∞)`**: a curve of class `C^∞([a, ∞); H^m(Ω))` for every `m` has a
space–time representative `U`, agreeing with `u t` for every `t ≥ a`, of class
`C^∞(Ω̄ × [a, ∞))` — `C^∞` on `Ω × (a, ∞)` with every derivative extending continuously to
`closure Ω × [a, ∞) = closure (Ω × (a, ∞))` ([brezis2011functional] Theorems 10.2 (c) and 10.8,
`a = 0`). -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (hΩ : IsSobolevExtensionDomainAll N Ω) {a : ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u (Ici a)) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ Ici a,
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ Ioi a) := by
  obtain ⟨U, hUae, hU⟩ :=
    contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough hΩ (uniqueDiffOn_Ici a) hu
  exact ⟨U, hUae, hU (Ioi a) isOpen_Ioi (by rw [closure_Ioi])⟩

end Bridge

end Bochner
