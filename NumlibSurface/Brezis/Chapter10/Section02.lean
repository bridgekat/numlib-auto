import Numlib.Analysis.PDE.Heat.MaximumPrinciple
import NumlibSurface.Brezis.Chapter10.Section01

/-!
# Brezis §10.2: The maximum principle

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §10.2: the maximum principle for the heat equation
(Theorem 10.3, by Stampacchia's truncation method in time), its Corollaries 10.4 (positivity, the
`L^∞` contraction) and 10.5 (continuity on `Q̄` for continuous data vanishing on `Γ`), and the
classical maximum principle Theorem 10.6 for a function `u(x, t)` of class `C¹` in `t` and `C²`
in `x` with `∂ₜu − Δu ≤ 0` on a bounded cylinder, whose maximum is attained on the parabolic
boundary `P = (Ω̄ × {0}) ∪ (Γ × [0, T])`. The backbone is
`Numlib/Analysis/PDE/Heat/MaximumPrinciple` (Theorems 10.3–10.4, on every open set) and
`Numlib/Analysis/PDE/Heat/Classical` (Theorem 10.6, the result that closes the Atkinson–Han
heat-equation examples of `notes/frontier.md`).

## Conventions

* Theorem 10.3 and Corollary 10.4 are stated for a solution `u` of (1), (2), (3) in the class
  (4) of §10.1 (`IsHeatSolution`); their proofs hold on every open set, without the chapter's
  standing regularity hypothesis. The book's "for all `(x, t) ∈ Q`" for an `L²`-valued solution
  is read almost everywhere in `x` for each `t ≥ 0` (`theorem_10_3`), and everywhere for the
  continuous representative of Theorem 10.1 (5) (`theorem_10_3_pointwise`). The book's `sup_Ω u₀`
  and `inf_Ω u₀` are essential bounds: `theorem_10_3` is stated for every admissible bound
  `K ≥ 0` (the book's `max {0, sup u₀}` is the least one, `+∞` when there is none), and
  `theorem_10_3_essSup` with `essSup`/`essInf` for an essentially bounded datum.
* Corollary 10.4 (ii)'s `‖u‖_{L^∞(Q)} ≤ ‖u₀‖_{L^∞(Ω)}` is stated as
  `‖u(t)‖_{L^∞(Ω)} ≤ ‖u₀‖_{L^∞(Ω)}` for every `t ≥ 0` (no jointly measurable representative of
  the curve is built; erratum recorded in `notes/book-errata.md`).
* Corollary 10.5's datum `u₀ ∈ C(Ω̄) ∩ L²(Ω)` with `u₀ = 0` on `Γ` is an `L²` datum agreeing
  a.e. with a function `f` continuous on `closure Ω` and vanishing on `frontier Ω`, which
  (footnote 6) tends to `0` at infinity along `Ω` — `Tendsto f (cocompact ⊓ 𝓟 Ω) (𝓝 0)`, void
  for bounded `Ω` (`corollary_10_5_of_isBounded`); `u ∈ C(Q̄)` is a representative `U` continuous
  on `closure Ω × [0, ∞)` with `U(·, t) = u(t)` a.e. for every `t ≥ 0` and `U(·, 0) = f` on
  `closure Ω`. The backbone (`Heat.IsSolution.continuousOn_spaceTime`) needs only a `C^{2ℓ}`
  domain with `N/2 < 2ℓ`; the surface keeps the chapter's `C^∞`.
* Theorem 10.6 is classical: `u : ℝ^N × ℝ → ℝ`, the Laplacian in `x` is Mathlib's `Δ`
  (`InnerProductSpace.laplacian`), the hypotheses (20), (21), (22) are `IsHeatSubsolution`, and
  the parabolic boundary is `parabolicBoundary`. The book's `max_{Ω̄ × [0,T]} u = max_P u` is
  stated as "the maximum over the closed cylinder is attained at a point of `P`" for a nonempty
  `Ω` (the book leaves `Ω ≠ ∅` implicit; for `Ω = ∅` there is no maximum), and as the bound
  `u ≤ max_P u` on the closed cylinder, which needs no such hypothesis (`theorem_10_6_le`).

## Main results

* `theorem_10_3`, `theorem_10_3_essSup`, `theorem_10_3_pointwise`.
* `corollary_10_4_i`, `corollary_10_4_ii`, `corollary_10_5`, `corollary_10_5_of_isBounded`.
* `parabolicBoundary`, `IsHeatSubsolution`, `IsHeatSubsolution.isClassicalSubsolution`,
  `theorem_10_6`, `theorem_10_6_le`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter10

open Brezis.Chapter07 Brezis.Chapter09 SobolevMultiIndex

section General

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-! ### Theorem 10.3 -/

/-- **Theorem 10.3 (the maximum principle).** Let `u₀ ∈ L²(Ω)` and let `u` be the solution of
(1), (2), (3). Then `min {0, inf_Ω u₀} ≤ u(x, t) ≤ max {0, sup_Ω u₀}` for all `(x, t) ∈ Q` — for
every `t ≥ 0`, almost everywhere on `Ω`: for every `K ≥ 0` with `u₀ ≤ K` a.e. on `Ω`, `u(t) ≤ K`
a.e. on `Ω`, and for every `K ≥ 0` with `−K ≤ u₀` a.e., `−K ≤ u(t)` a.e. (the book's bounds are
the least such `K`; the statement is empty when `sup u₀ = +∞`). Stampacchia's truncation method in
time: with `K = max {0, sup u₀}`, `H(s) = ∫₀ˢ G` and `φ(t) = ∫_Ω H(u(x, t) − K) dx`, one has
`φ ∈ C([0, ∞))`, `φ(0) = 0`, `φ ≥ 0`, `φ ∈ C¹((0, ∞))` and
`φ' = ∫_Ω G(u − K) ∂ₜu = ∫_Ω G(u − K) Δu = −∫_Ω G'(u − K) |∇u|² ≤ 0` since `G(u(t) − K) ∈ H¹₀(Ω)`,
so `φ ≡ 0`. The backbone's `Heat.IsSolution.le_of_le` and `ge_of_ge`, on every open set. -/
theorem theorem_10_3 (hu : IsHeatSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K) :
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u₀ x ≤ K) →
      ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u t x ≤ K) ∧
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u₀ x) →
      ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u t x) :=
  ⟨fun hu₀ _ ht ↦ hu.isSolution.le_of_le hK hu₀ ht, fun hu₀ _ ht ↦ hu.isSolution.ge_of_ge hK hu₀ ht⟩

/-- **Theorem 10.3 with the book's bounds**, for an essentially bounded datum: if `u₀` is
essentially bounded above and below on `Ω`, then for every `t ≥ 0`,
`min {0, essInf u₀} ≤ u(t) ≤ max {0, essSup u₀}` almost everywhere on `Ω`. -/
theorem theorem_10_3_essSup (hu : IsHeatSolution Ω u₀ u)
    (hb : IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ω : Set 𝔼))) u₀)
    (hb' : IsBoundedUnder (· ≥ ·) (ae (volume.restrict (Ω : Set 𝔼))) u₀) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      min 0 (essInf u₀ (volume.restrict (Ω : Set 𝔼))) ≤ u t x ∧
        u t x ≤ max 0 (essSup u₀ (volume.restrict (Ω : Set 𝔼))) := by
  have h1 := (theorem_10_3 hu (le_max_left 0 (essSup u₀ _))).1
    ((ae_le_essSup hb).mono fun x hx ↦ hx.trans (le_max_right _ _)) t ht
  have h2 := (theorem_10_3 hu (K := -min 0 (essInf u₀ (volume.restrict (Ω : Set 𝔼))))
    (by simp)).2
    ((ae_essInf_le hb').mono fun x hx ↦ by rw [neg_neg]; exact (min_le_right _ _).trans hx) t ht
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨by simpa using hx2, hx1⟩

/-- **Theorem 10.3 as printed, "for all `(x, t) ∈ Q`"**: for the continuous representative `U`
of the solution given by Theorem 10.1 (5) (`theorem_10_1_smooth`: `U(·, t) = u(t)` a.e. on `Ω`
for `t > 0`, `U ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`), the bounds of Theorem 10.3 hold at every
point: for every `K ≥ 0` with `u₀ ≤ K` a.e. on `Ω`, `U(x, t) ≤ K` for all `x ∈ Ω` and `t > 0`,
and likewise from below. An almost-everywhere bound on an open set for a continuous function
holds everywhere: `max (U(·, t)) K` is continuous on `Ω` and a.e. equal to the constant `K`
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). -/
theorem theorem_10_3_pointwise (hu : IsHeatSolution Ω u₀ u) {U : 𝔼 × ℝ → ℝ}
    (hU : ∀ t, 0 < t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t)
    (hUs : ∀ ε > 0, ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi ε)) {K : ℝ} (hK : 0 ≤ K) :
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u₀ x ≤ K) →
      ∀ t, 0 < t → ∀ x ∈ Ω, U (x, t) ≤ K) ∧
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u₀ x) →
      ∀ t, 0 < t → ∀ x ∈ Ω, -K ≤ U (x, t)) := by
  -- the slices `U(·, t)`, `t > 0`, are continuous on `Ω`
  have hc : ∀ t, 0 < t → ContinuousOn (fun x ↦ U (x, t)) Ω := fun t ht ↦
    ((hUs (t / 2) (by positivity)).contDiffOn.continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const) fun x hx ↦
        (⟨hx, by simp only [mem_Ioi]; linarith⟩ : (x, t) ∈ (Ω : Set 𝔼) ×ˢ Ioi (t / 2)))
  refine ⟨fun hu₀ t ht x hx ↦ ?_, fun hu₀ t ht x hx ↦ ?_⟩
  · have hae : (fun x ↦ max (U (x, t)) K) =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ K := by
      filter_upwards [(theorem_10_3 hu hK).1 hu₀ t ht.le, hU t ht] with x hx hx'
      simp only [hx', max_eq_right hx]
    have := Measure.eqOn_open_of_ae_eq hae Ω.isOpen (ContinuousOn.sup (hc t ht) continuousOn_const)
      continuousOn_const hx
    simpa only [max_eq_right_iff] using this
  · have hae : (fun x ↦ min (U (x, t)) (-K)) =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ -K := by
      filter_upwards [(theorem_10_3 hu hK).2 hu₀ t ht.le, hU t ht] with x hx hx'
      simp only [hx', min_eq_right hx]
    have := Measure.eqOn_open_of_ae_eq hae Ω.isOpen (ContinuousOn.inf (hc t ht) continuousOn_const)
      continuousOn_const hx
    simpa only [min_eq_right_iff] using this

/-! ### Corollary 10.4 -/

/-- **Corollary 10.4 (i).** Let `u₀ ∈ L²(Ω)` and `u` the solution of (1), (2), (3). If `u₀ ≥ 0`
a.e. on `Ω`, then `u ≥ 0` in `Q`: `u(t) ≥ 0` a.e. on `Ω` for every `t ≥ 0` (Theorem 10.3 with
`K = 0` for the lower bound; the backbone's `Heat.IsSolution.nonneg`). -/
theorem corollary_10_4_i (hu : IsHeatSolution Ω u₀ u)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ u₀ x) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ u t x :=
  hu.isSolution.nonneg hu₀ ht

/-- **Corollary 10.4 (ii).** Let `u₀ ∈ L²(Ω)` and `u` the solution of (1), (2), (3). If
`u₀ ∈ L^∞(Ω)`, then `u ∈ L^∞(Q)` and `‖u‖_{L^∞(Q)} ≤ ‖u₀‖_{L^∞(Ω)}`: `u(t) ∈ L^∞(Ω)` with
`‖u(t)‖_{L^∞(Ω)} ≤ ‖u₀‖_{L^∞(Ω)}` for every `t ≥ 0` (both bounds of Theorem 10.3 with
`K = ‖u₀‖_∞`; the backbone's `Heat.IsSolution.eLpNorm_top_le`). The joint `L^∞(Q)` reading is
this bound for every `t`. -/
theorem corollary_10_4_ii (hu : IsHeatSolution Ω u₀ u)
    (hu₀ : MemLp u₀ ∞ (volume.restrict (Ω : Set 𝔼))) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (u t) ∞ (volume.restrict (Ω : Set 𝔼)) ∧
      eLpNorm (u t) ∞ (volume.restrict (Ω : Set 𝔼)) ≤ eLpNorm u₀ ∞ (volume.restrict (Ω : Set 𝔼)) :=
  ⟨(hu.isSolution.eLpNorm_top_le ht).trans_lt hu₀, hu.isSolution.eLpNorm_top_le ht⟩

end General

/-! ### Corollary 10.5: continuity on `Q̄` for continuous data vanishing on `Γ` -/

section Regular

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **Corollary 10.5.** Let `Ω` be of class `C^∞` with `Γ` bounded, and let `u₀ ∈ C(Ω̄) ∩ L²(Ω)`
with `u₀ = 0` on `Γ` — and, footnote 6, `u₀(x) → 0` as `|x| → ∞` if `Ω` is unbounded: the `L²`
datum `u₀` agrees a.e. on `Ω` with a function `f` continuous on `Ω̄`, vanishing on `Γ` and tending
to `0` along `cocompact ⊓ 𝓟 Ω` (void for bounded `Ω`, `corollary_10_5_of_isBounded`). Then the
solution `u` of (1), (2), (3) belongs to `C(Q̄)`: there is `U : ℝ^N × ℝ → ℝ`, continuous on
`Ω̄ × [0, ∞)`, with `U(·, t) = u(t)` a.e. on `Ω` for every `t ≥ 0` and `U(·, 0) = u₀` on `Ω̄`. The
book's proof: `u_{0n} ∈ C_c^∞(Ω)` with `u_{0n} → u₀` in `L^∞(Ω)` (the "easily established"
approximation, `Heat.exists_testFunction_tendsto_of_continuousOn`), `uₙ ∈ C^∞(Q̄)` by
Theorem 10.2 (c), `‖uₙ − uₘ‖_{L^∞(Q)} ≤ ‖u_{0n} − u_{0m}‖_{L^∞(Ω)}` by (19), so `(uₙ)` converges
uniformly on `Q̄`; the limit is `u` by `|uₙ(t) − u(t)|_{L²} ≤ |u_{0n} − u₀|_{L²}` (Theorem 7.7),
which the backbone replaces by (19) once more (`uₙ(t) → u(t)` a.e.). The backbone's
`Heat.IsSolution.continuousOn_spaceTime`. -/
theorem corollary_10_5 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {f : 𝔼 → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set 𝔼))) (hf0 : ∀ x ∈ frontier (Ω : Set 𝔼), f x = 0)
    (hft : Tendsto f (cocompact 𝔼 ⊓ 𝓟 (Ω : Set 𝔼)) (𝓝 0))
    (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set 𝔼)] f) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, ContinuousOn U (closure (Ω : Set 𝔼) ×ˢ Ici 0) ∧
      (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set 𝔼)) :=
  hu.isSolution.continuousOn_spaceTime hΩ hΓ hf hf0 hft hu₀

/-- **Corollary 10.5 for bounded `Ω`**, as printed: `u₀ ∈ C(Ω̄) ∩ L²(Ω)` with `u₀ = 0` on `Γ`
gives `u ∈ C(Q̄)`. Footnote 6's condition at infinity is void, `cocompact ⊓ 𝓟 Ω` being the
trivial filter when `Ω̄` is compact (the backbone's
`Heat.IsSolution.continuousOn_spaceTime_of_isBounded`). -/
theorem corollary_10_5_of_isBounded (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼)) {f : 𝔼 → ℝ} (hf : ContinuousOn f (closure (Ω : Set 𝔼)))
    (hf0 : ∀ x ∈ frontier (Ω : Set 𝔼), f x = 0) (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set 𝔼)] f)
    (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, ContinuousOn U (closure (Ω : Set 𝔼) ×ˢ Ici 0) ∧
      (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set 𝔼)) :=
  hu.isSolution.continuousOn_spaceTime_of_isBounded hb hΩ hf hf0 hu₀

end Regular

/-! ### Theorem 10.6: the classical maximum principle -/

section Classical

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable (Ω : Opens (EuclideanSpace ℝ (Fin N))) (T : ℝ)

/-- **The parabolic boundary** `P = (Ω̄ × {0}) ∪ (Γ × [0, T])` of the cylinder `Ω × (0, T)`
(Theorem 10.6): the bottom and the lateral surface, without the top. The backbone's
`Heat.parabolicBoundary`, by definition. -/
def parabolicBoundary : Set (𝔼 × ℝ) :=
  closure (Ω : Set 𝔼) ×ˢ {0} ∪ frontier (Ω : Set 𝔼) ×ˢ Icc 0 T

/-- The parabolic boundary of the surface is the backbone's. -/
theorem parabolicBoundary_eq : parabolicBoundary Ω T = Heat.parabolicBoundary (Ω : Set 𝔼) T :=
  rfl

/-- **The hypotheses (20), (21), (22) of Theorem 10.6** on a function `u(x, t)`, for an open
`Ω` and `T > 0`: (20) `u ∈ C(Ω̄ × [0, T])`; (21) `u` is of class `C¹` in `t` and of class `C²` in
`x` in `Ω × (0, T)`; (22) `∂ₜu − Δu ≤ 0` in `Ω × (0, T)`, with Mathlib's Laplacian `Δ` in the
space variable. Footnote 7: no boundary condition and no initial datum are prescribed. -/
structure IsHeatSubsolution (u : 𝔼 × ℝ → ℝ) : Prop where
  /-- (20): `u ∈ C(Ω̄ × [0, T])`. -/
  continuousOn : ContinuousOn u (closure (Ω : Set 𝔼) ×ˢ Icc 0 T)
  /-- (21): `u` is of class `C¹` in `t` in `Ω × (0, T)`. -/
  contDiffAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 1 (fun s ↦ u (x, s)) t
  /-- (21): `u` is of class `C²` in `x` in `Ω × (0, T)`. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- (22): `∂ₜu − Δu ≤ 0` in `Ω × (0, T)`. -/
  deriv_sub_laplacian_nonpos : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t - Δ (fun y ↦ u (y, t)) x ≤ 0

variable {Ω T} {u : EuclideanSpace ℝ (Fin N) × ℝ → ℝ}

/-- A function satisfying (20), (21), (22) is a classical subsolution of `∂ₜu − Δu ≤ 0` in the
backbone's sense (`Heat.IsClassicalSubsolution` with diffusivity `1`, which asks only
differentiability in `t`). -/
theorem IsHeatSubsolution.isClassicalSubsolution (hu : IsHeatSubsolution Ω T u) :
    Heat.IsClassicalSubsolution 1 (Ω : Set 𝔼) T u :=
  ⟨hu.continuousOn, fun x hx t ht ↦ (hu.contDiffAt_snd x hx t ht).differentiableAt one_ne_zero,
    hu.contDiffAt_fst, fun x hx t ht ↦ by
      rw [one_mul]
      exact hu.deriv_sub_laplacian_nonpos x hx t ht⟩

/-- **Theorem 10.6.** Let `Ω` be bounded (and nonempty), `T > 0`, and let `u` satisfy (20), (21),
(22). Then `max_{Ω̄ × [0, T]} u = max_P u`: the maximum of `u` over the closed cylinder
`Ω̄ × [0, T]` is attained at a point of the parabolic boundary `P = (Ω̄ × {0}) ∪ (Γ × [0, T])`.
The book's proof — `v = u + ε |x|²` with `∂ₜv − Δv ≤ −2εN < 0`, an interior maximum
`(x₀, t₀) ∉ P` would have `Δv(x₀, t₀) ≤ 0` and `∂ₜv(x₀, t₀) ≥ 0` (footnote 8: `t₀ = T` gives only
the one-sided sign), a contradiction, then `ε → 0` — is the backbone's
`Heat.IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary` (with the perturbation `u − εt`,
which needs no computation of `Δ|x|²`), whose one non-Mathlib ingredient is the second-derivative
test at an interior maximum. -/
theorem theorem_10_6 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hT : 0 < T) (hu : IsHeatSubsolution Ω T u) :
    ∃ p ∈ parabolicBoundary Ω T, IsMaxOn u (closure (Ω : Set 𝔼) ×ˢ Icc 0 T) p :=
  hu.isClassicalSubsolution.exists_isMaxOn_parabolicBoundary Ω.isOpen hb hne one_pos hT

/-- **Theorem 10.6, the bound form**: for bounded `Ω`, `T > 0` and `u` satisfying (20), (21),
(22), a bound `u ≤ M` on the parabolic boundary `P` holds on the whole closed cylinder
`Ω̄ × [0, T]` — the inequality `max_{Ω̄ × [0, T]} u ≤ max_P u`, which needs no nonemptiness of
`Ω`. The backbone's `Heat.IsClassicalSubsolution.le_of_le_on_parabolicBoundary`. -/
theorem theorem_10_6_le (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hT : 0 < T)
    (hu : IsHeatSubsolution Ω T u) {M : ℝ} (hM : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M) :
    ∀ q ∈ closure (Ω : Set 𝔼) ×ˢ Icc 0 T, u q ≤ M :=
  hu.isClassicalSubsolution.le_of_le_on_parabolicBoundary Ω.isOpen hb one_pos hT hM

end Classical

end Brezis.Chapter10
