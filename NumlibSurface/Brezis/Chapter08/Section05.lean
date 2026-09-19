import Numlib.Variational.EllipticInterval.MaximumPrinciple
import NumlibSurface.Brezis.Chapter08.Section04

/-!
# Brezis §8.5: the maximum principle

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.5: Theorem 8.19 (the maximum principle for the
Dirichlet problem, by Stampacchia's truncation method), Remark 26 (the classical proof),
Corollary 8.20, Proposition 8.21 (the Neumann problem), Remarks 27–28. Everything is on
`I = (0, 1)` over `Numlib/Variational/EllipticInterval/MaximumPrinciple`.

## Correspondence

* "`u ∈ H²(I)` is the solution of the Dirichlet problem (32) with `u(0) = α`, `u(1) = β`" is
  `Φ : SobolevInterval 2 0 1` with `Φ'' = Φ − f` a.e. and `Φ(0) = α`, `Φ(1) = β` (Proposition
  8.16's object, §8.4); the weak equation (34) on `H_0^1`, which is what the backbone consumes,
  follows by Green's formula (`EllipticInterval.modelForm_inclusionCLM_eq_load_of_mem`).
* The book's `sup_I f` and `inf_I f` are the essential supremum and infimum (footnote 16),
  possibly infinite; the bounds (33) and (35) are stated through an arbitrary essential bound:
  "`f ≤ K` a.e." gives `u ≤ max (α, β, K)`, which is the book's statement when `sup f < ∞`
  (take `K = sup f`) and vacuous otherwise.
* "`u(x)`" is the continuous representative `SobolevInterval.rep u x`, `x ∈ [0, 1]`.

## Main results

* `theorem_8_19`, `theorem_8_19_le`, `theorem_8_19_ge` — the maximum principle (33).
* `remark_8_26` — the classical proof for `f ∈ C(Ī)`, `u ∈ C²(Ī)`.
* `corollary_8_20_i`, `corollary_8_20_ii`, `corollary_8_20_iii`, `corollary_8_20` — positivity,
  `‖u‖_∞ ≤ ‖f‖_∞`, `‖u‖_∞ ≤ ‖u‖_{L^∞(∂I)}`.
* `proposition_8_21`, `remark_8_27` — the Neumann problem, weak and classical.
* `remark_8_28` — the problem on `ℝ` of Example 8.
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval
open scoped ENNReal Topology

noncomputable section

namespace Brezis.Chapter08

/-- The coefficient `1` of the model problem, bounded below by `1` almost everywhere. -/
private theorem one_le_constLinf_ae' :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ constLinf 0 1 1 x :=
  (coeFn_constLinf 0 1 1).mono fun x hx ↦ by rw [hx]

/-! ### Theorem 8.19 -/

/-- **Theorem 8.19, the upper bound.** Let `f ∈ L²(I)`, `I = (0, 1)`, and let `u ∈ H²(I)` be
the solution of the Dirichlet problem (32): `−u'' + u = f` a.e., `u(0) = α`, `u(1) = β`. Then
for every `K` with `α ≤ K`, `β ≤ K` and `f ≤ K` a.e. — `K = max {α, β, sup f}` when
`sup f < ∞` — `u(x) ≤ K` for every `x ∈ Ī`. Stampacchia's truncation method, the backbone's
`EllipticInterval.rep_le_of_le_of_isWeakSolution` with `α = γ = 1`, the weak equation (34) on
`H_0^1` coming from Green's formula. -/
theorem theorem_8_19_le (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) {K : ℝ}
    (hα : α ≤ K) (hβ : β ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ K) :
    ∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ K :=
  rep_le_of_le_of_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae' (one_le_constLinf_ae'.mono fun _ hx ↦ zero_le_one.trans hx) f
    (fun v hv ↦ modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hv)
    (h0 ▸ hα) (h1 ▸ hβ) (by
      filter_upwards [hf, coeFn_constLinf 0 1 1] with x hx hx1
      rw [hx1, mul_one]; exact hx)

/-- **Theorem 8.19, the lower bound.** For every `K` with `K ≤ α`, `K ≤ β` and `K ≤ f` a.e.
(`K = min {α, β, inf f}` when `inf f > −∞`), `K ≤ u(x)` for every `x ∈ Ī`: the upper bound
applied to `−u`. -/
theorem theorem_8_19_ge (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) {K : ℝ}
    (hα : K ≤ α) (hβ : K ≤ β) (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), K ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, K ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  rep_ge_of_ge_of_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae' (one_le_constLinf_ae'.mono fun _ hx ↦ zero_le_one.trans hx) f
    (fun v hv ↦ modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hv)
    (h0 ▸ hα) (h1 ▸ hβ) (by
      filter_upwards [hf, coeFn_constLinf 0 1 1] with x hx hx1
      rw [hx1, mul_one]; exact hx)

/-- **Theorem 8.19** (the maximum principle). Let `f ∈ L²(I)` with `I = (0, 1)` and let
`u ∈ H²(I)` be the solution of the Dirichlet problem `−u'' + u = f` on `I`, `u(0) = α`,
`u(1) = β` (32). Then for every `x ∈ Ī`,
`min {α, β, inf_I f} ≤ u(x) ≤ max {α, β, sup_I f}` (33), the essential bounds of `f` being read
as: for every essential upper bound `M` of `f` (`f ≤ M` a.e.), `u ≤ max {α, β, M}`, and for
every essential lower bound `m`, `min {α, β, m} ≤ u`. -/
theorem theorem_8_19 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    (∀ M : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ M) → ∀ x ∈ Icc (0 : ℝ) 1,
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ max (max α β) M) ∧
    ∀ m : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), m ≤ f x) → ∀ x ∈ Icc (0 : ℝ) 1,
      min (min α β) m ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  ⟨fun M hM ↦ theorem_8_19_le f hΦ h0 h1 ((le_max_left α β).trans (le_max_left _ M))
    ((le_max_right α β).trans (le_max_left _ M)) (hM.mono fun _ hx ↦ hx.trans (le_max_right _ M)),
    fun m hm ↦ theorem_8_19_ge f hΦ h0 h1 ((min_le_left _ m).trans (min_le_left α β))
      ((min_le_left _ m).trans (min_le_right α β)) (hm.mono fun _ hx ↦ (min_le_right _ m).trans hx)⟩

/-- **Remark 26.** When `f ∈ C(Ī)`, `u ∈ C²(Ī)` and (33) can be established by the classical
approach to the maximum principle: let `x₀ ∈ Ī` be a point where `u` attains its maximum; if
`x₀ = 0` or `x₀ = 1` the conclusion is obvious, otherwise `u'(x₀) = 0`, `u''(x₀) ≤ 0` and
`u(x₀) = f(x₀) + u''(x₀) ≤ f(x₀) ≤ K`. For `v ∈ C²[0, 1]` with `−v'' + v = f` on `[0, 1]`,
`v(0) ≤ K`, `v(1) ≤ K` and `f ≤ K` on `[0, 1]`: `v ≤ K` on `[0, 1]`. The backbone's
`EllipticInterval.le_of_contDiffMapIcc_classical` over the second-derivative test
`IsLocalMax.deriv_deriv_nonpos`. -/
theorem remark_8_26 (v : ContDiffMapIcc (zero_lt_one' ℝ).le 2) {f : ℝ → ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -v.deriv 2 x + v x = f x) {K : ℝ}
    (hK0 : v ⟨0, left_mem_Icc.2 zero_le_one⟩ ≤ K) (hK1 : v ⟨1, right_mem_Icc.2 zero_le_one⟩ ≤ K)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ K) : ∀ x : Icc (0 : ℝ) 1, v x ≤ K :=
  le_of_contDiffMapIcc_classical (zero_lt_one' ℝ) v hode hK0 hK1 hf

/-! ### Corollary 8.20 -/

/-- **Corollary 8.20 (i).** Let `u` be a solution of (34) (the weak equation
`∫ u' v' + ∫ u v = ∫ f v` for all `v ∈ H_0^1(I)`, whatever its boundary values). If `u ≥ 0` on
`∂I` and `f ≥ 0` on `I`, then `u ≥ 0` on `I`. The backbone's
`EllipticInterval.rep_nonneg_of_isWeakSolution`. -/
theorem corollary_8_20_i (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : 0 ≤ SobolevInterval.rep u 0) (h1 : 0 ≤ SobolevInterval.rep u 1)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ SobolevInterval.rep u x :=
  rep_nonneg_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 hf

/-- **Corollary 8.20 (ii).** If `u = 0` on `∂I` and `f ∈ L^∞(I)`, then
`‖u‖_{L^∞(I)} ≤ ‖f‖_{L^∞(I)}`: `|u(x)| ≤ ‖f‖_∞` for every `x ∈ Ī`. The backbone's
`EllipticInterval.abs_rep_le_of_isWeakSolution` with the essential bound `M = ‖f‖_∞`. -/
theorem corollary_8_20_ii (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : SobolevInterval.rep u 0 = 0) (h1 : SobolevInterval.rep u 1 = 0)
    (hf : MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ (eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1))).toReal := by
  refine abs_rep_le_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 ?_
  have hne : eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) ≠ ⊤ := hf.eLpNorm_ne_top
  filter_upwards [ae_le_eLpNormEssSup (f := ⇑f) (μ := volume.restrict (Ioo (0 : ℝ) 1))] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at hne
  have := ENNReal.toReal_mono hne hx
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

/-- **Corollary 8.20 (ii), with an explicit essential bound.** If `u = 0` on `∂I` and
`|f| ≤ M` a.e. on `I`, then `|u| ≤ M` on `Ī`. -/
theorem corollary_8_20_ii' (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : SobolevInterval.rep u 0 = 0) (h1 : SobolevInterval.rep u 1 = 0) {M : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), |f x| ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) 1, |SobolevInterval.rep u x| ≤ M :=
  abs_rep_le_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 hf

/-- **Corollary 8.20 (iii).** If `f = 0` on `I`, then `‖u‖_{L^∞(I)} ≤ ‖u‖_{L^∞(∂I)}`:
`|u(x)| ≤ max (|u(0)|, |u(1)|)` for every `x ∈ Ī`. The backbone's
`EllipticInterval.abs_rep_le_max_of_isWeakSolution`. -/
theorem corollary_8_20_iii {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 0 v) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ max |SobolevInterval.rep u 0| |SobolevInterval.rep u 1| :=
  abs_rep_le_max_of_isWeakSolution (zero_lt_one' ℝ) hu

/-- **Corollary 8.20.** Let `u` be a solution of (34). (i) If `u ≥ 0` on `∂I` and `f ≥ 0` on
`I`, then `u ≥ 0` on `I`. (ii) If `u = 0` on `∂I` and `f ∈ L^∞(I)`, then
`‖u‖_{L^∞(I)} ≤ ‖f‖_{L^∞(I)}`. (iii) If `f = 0` on `I`, then `‖u‖_{L^∞(I)} ≤ ‖u‖_{L^∞(∂I)}`. -/
theorem corollary_8_20 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v) :
    (0 ≤ SobolevInterval.rep u 0 → 0 ≤ SobolevInterval.rep u 1 →
      (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ f x) →
      ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ SobolevInterval.rep u x) ∧
    (SobolevInterval.rep u 0 = 0 → SobolevInterval.rep u 1 = 0 →
      MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) → ∀ x ∈ Icc (0 : ℝ) 1,
        |SobolevInterval.rep u x| ≤ (eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1))).toReal) ∧
    (f = 0 → ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ max |SobolevInterval.rep u 0| |SobolevInterval.rep u 1|) :=
  ⟨fun h0 h1 hf ↦ corollary_8_20_i f hu h0 h1 hf, fun h0 h1 hf ↦ corollary_8_20_ii f hu h0 h1 hf,
    fun hf ↦ corollary_8_20_iii (hf ▸ hu)⟩

/-! ### Proposition 8.21: the Neumann problem -/

/-- **Proposition 8.21, the upper bound.** Let `f ∈ L²(I)`, `I = (0, 1)`, and let `u ∈ H²(I)`
be the solution of the Neumann problem `−u'' + u = f`, `u'(0) = u'(1) = 0` (Proposition 8.17).
Then `u(x) ≤ K` for every `x ∈ Ī` and every essential upper bound `K` of `f` (`K = sup_I f`
when finite). The truncation `G(u − K)` plugged into the weak formulation (36) on `H¹(I)`;
the backbone's `EllipticInterval.rep_le_of_le_of_isWeakSolution_neumann`. -/
theorem proposition_8_21_le (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ K) :
    ∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ K :=
  rep_le_of_le_of_isWeakSolution_neumann (zero_lt_one' ℝ) f
    (proposition_8_17_min f hΦ h0 h1).1 hf

/-- **Proposition 8.21, the lower bound.** `K ≤ u(x)` for every essential lower bound `K` of
`f`. -/
theorem proposition_8_21_ge (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), K ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, K ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  rep_ge_of_ge_of_isWeakSolution_neumann (zero_lt_one' ℝ) f
    (proposition_8_17_min f hΦ h0 h1).1 hf

/-- **Proposition 8.21.** Let `f ∈ L²(I)` with `I = (0, 1)` and let `u ∈ H²(I)` be the solution
of the Neumann problem `−u'' + u = f` on `I`, `u'(0) = u'(1) = 0`. Then for every `x ∈ Ī`,
`inf_I f ≤ u(x) ≤ sup_I f` (35): `m ≤ u(x) ≤ M` for every essential lower bound `m` and
essential upper bound `M` of `f`. -/
theorem proposition_8_21 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) :
    (∀ M : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ M) → ∀ x ∈ Icc (0 : ℝ) 1,
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ M) ∧
    ∀ m : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), m ≤ f x) → ∀ x ∈ Icc (0 : ℝ) 1,
      m ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  ⟨fun _ hM ↦ proposition_8_21_le f hΦ h0 h1 hM, fun _ hm ↦ proposition_8_21_ge f hΦ h0 h1 hm⟩

/-- **Remark 27.** If `f ∈ C(Ī)`, then `u ∈ C²(Ī)` and (35) can be established along the lines
of Remark 26; if `u` achieves its maximum on `∂I`, say at `0`, then `u''(0) ≤ 0` (extending `u`
by reflection to the left of `0` and using `u'(0) = 0`). For `v ∈ C²[0, 1]` with
`−v'' + v = f` on `[0, 1]`, `v'(0) = v'(1) = 0` and `f ≤ K` on `[0, 1]`: `v ≤ K` on `[0, 1]`.
The backbone's `EllipticInterval.le_of_contDiffMapIcc_classical_neumann` (the one-sided
second-derivative test at the endpoints). -/
theorem remark_8_27 (v : ContDiffMapIcc (zero_lt_one' ℝ).le 2) {f : ℝ → ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -v.deriv 2 x + v x = f x)
    (hv0 : v.deriv 1 ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0)
    (hv1 : v.deriv 1 ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0) {K : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ K) : ∀ x : Icc (0 : ℝ) 1, v x ≤ K :=
  le_of_contDiffMapIcc_classical_neumann (zero_lt_one' ℝ) v hode hv0 hv1 hf

/-! ### Remark 28: the problem on `ℝ` -/

/-- **Remark 28.** Let `f ∈ L²(ℝ)` and let `u ∈ H²(ℝ)` be the solution of `−u'' + u = f` on
`ℝ`, `u(x) → 0` as `|x| → ∞`, discussed in Example 8 (`EllipticInterval.Line.solution f`). Then
for all `x ∈ ℝ`, `inf_ℝ f ≤ u(x) ≤ sup_ℝ f`: `u(x) ≤ K` for every essential upper bound `K ≥ 0`
of `f`, and `k ≤ u(x)` for every essential lower bound `k ≤ 0`. (The sign conditions are no
restriction — a function of `L²(ℝ)` has `ess sup f ≥ 0 ≥ ess inf f` — but the truncation
`G(u − K)` lies in `H¹(ℝ)` only for `K ≥ 0`, which the book's sketch does not remark on.) The
backbone's `EllipticInterval.Line.rep_le_of_le` and `Line.le_rep_of_le`. -/
theorem remark_8_28 (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    (∀ K : ℝ, 0 ≤ K → (∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f x ≤ K) →
      ∀ x, (Line.solution f).rep x ≤ K) ∧
    ∀ k : ℝ, k ≤ 0 → (∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), k ≤ f x) →
      ∀ x, k ≤ (Line.solution f).rep x :=
  ⟨fun _ hK hf ↦ Line.rep_le_of_le f hK hf, fun _ hk hf ↦ Line.le_rep_of_le f hk hf⟩

end Brezis.Chapter08
