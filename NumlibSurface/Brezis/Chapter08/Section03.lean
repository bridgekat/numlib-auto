import Numlib.Analysis.Sobolev.Interval
import Numlib.Analysis.Sobolev.Interval.Dual
import NumlibSurface.Brezis.Chapter08.Section02

/-!
# Brezis §8.3: the space `W_0^{1,p}(I)` and its dual `W^{-1,p'}(I)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.3, with the paragraph on the dual space
`W^{-1,p'}(I)`. `I` is an open interval (`I : Opens ℝ` with `(hI : (I : Set ℝ).OrdConnected)`)
and `1 ≤ p < ∞` (`[Fact (1 ≤ p)]` with `(hp : p ≠ ∞)` where the book excludes `p = ∞`).
Everything delegates to `Numlib/Analysis/Sobolev/Interval/{Zero,Dual}` and to §8.2.

## Correspondence

* `W_0^{1,p}(I)` is `sobolevSpaceZero p I = SobolevIntervalLpZero 1 p I`, the closure of the
  test functions `C_c^∞(I)` in `W^{1,p}(I)` (`mem_sobolevSpaceZero_iff_mem_closure`; the book
  closes `C_c^1(I)`, which gives the same space by Remark 1); `H_0^1(I)` is `H10 I`. It is a
  closed subspace of `W^{1,p}(I)` (a `Submodule`), so it carries the norm of `W^{1,p}(I)` and, at
  `p = 2`, the scalar product of `H¹(I)`.
* "`u = 0` on `∂I`" is `∀ x ∈ frontier (I : Set ℝ), u.rep x = 0`, `u.rep` being the continuous
  representative of Theorem 8.2.
* `W^{-1,p'}(I)`, the dual of `W_0^{1,p}(I)`, is `sobolevSpaceDual p I = SobolevIntervalLpDual p I`,
  the strong dual `StrongDual ℝ (SobolevIntervalLpZero 1 p I)`; `H^{-1}(I)` is `Hneg1 I`.

## Main results

* `sobolevSpaceZero_banach` — `W_0^{1,p}` is a separable Banach space, reflexive for `p > 1`;
  `H_0^1` a separable Hilbert space.
* `remark_8_13`, `remark_8_14` — `W_0^{1,p}(ℝ) = W^{1,p}(ℝ)`; density of `C_c^∞(I)` and the
  compactly supported elements.
* `theorem_8_12`, `remark_8_16` — `u ∈ W_0^{1,p}(I)` iff `u = 0` on `∂I`, and the two other
  characterizations (zero extension, testing against `C_c^1(ℝ)`).
* `proposition_8_13`, `remark_8_17` — Poincaré's inequality, and `∫ u' v'` as a scalar product
  on `H_0^1`.
* `remark_8_18`, `remark_8_18_of_bounded`, `remark_8_18_ne` — `W_0^{m,p}(I)` by the vanishing
  of `u, Du, …, D^{m−1} u` on `∂I`, on every open interval and on `(a, b)`, and
  `W_0^{2,p} ≠ W^{2,p} ∩ W_0^{1,p}`.
* `inclusions_H10_L2_Hneg1`, `proposition_8_14`, `remark_8_19`, `remark_8_21` — the dual
  space: the inclusions `H_0^1 ⊆ L² ⊆ H^{-1}` and their `L^p` versions, the representation of
  `F ∈ W^{-1,p'}` by two functions `f₀, f₁ ∈ L^{p'}`, its non-uniqueness, and the same
  representation for functionals on `W^{1,p}`.

Remark 15 (discussion) and Remark 20 (the identification of `F` with the distribution
`f₀ − f₁'`) are not formalized (chapter plan).
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-! ### The definition -/

/-- **Definition (§8.3).** Given `1 ≤ p < ∞`, `W_0^{1,p}(I)` is the closure of `C_c^1(I)` — here
of the test functions `C_c^∞(I)`, equivalently by Remark 1 — in `W^{1,p}(I)`: the backbone's
`SobolevIntervalLpZero 1 p I`, a closed subspace of `W^{1,p}(I)` equipped with its norm. (The
book does not define `W_0^{1,p}` for `p = ∞`; the type exists, but Theorem 8.12 needs
`p < ∞`.) -/
abbrev sobolevSpaceZero (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) :
    Submodule ℝ (SobolevIntervalLp 1 p I) :=
  SobolevIntervalLpZero 1 p I

/-- **Notation (§8.3).** `H_0^1(I) = W_0^{1,2}(I)`, equipped with the scalar product of `H¹`. -/
abbrev H10 (I : Opens ℝ) : Submodule ℝ (SobolevIntervalLp 1 2 I) := sobolevSpaceZero 2 I

/-- The definition unfolded: `u ∈ W_0^{1,p}(I)` iff `u` lies in the closure, in `W^{1,p}(I)`, of
the set of elements carried by test functions. -/
theorem mem_sobolevSpaceZero_iff_mem_closure (u : SobolevIntervalLp 1 p I) :
    u ∈ sobolevSpaceZero p I ↔
      u ∈ closure {v : SobolevIntervalLp 1 p I | ∃ φ : 𝓓(I, ℝ), v.fn =ᵐ[volume.restrict I] φ} := by
  change u ∈ SobolevIntervalLpZero 1 p I ↔ _
  rw [SobolevIntervalLpZero, SobolevMultiIndexZero, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]
  rfl

/-! ### The unnumbered paragraph: Banach, reflexive, separable, Hilbert -/

/-- **§8.3, "The space `W_0^{1,p}` is a separable Banach space"**, first half: `W_0^{1,p}(I)` is
complete, being a closed subspace of `W^{1,p}(I)` (the instance
`SobolevMultiIndexZero.instCompleteSpace`). -/
theorem sobolevSpaceZero_banach : CompleteSpace (sobolevSpaceZero p I) := inferInstance

/-- **§8.3, "The space `W_0^{1,p}` is a separable Banach space"**, second half: for `1 ≤ p < ∞`,
`W_0^{1,p}(I)` is separable, as a subspace of the separable `W^{1,p}(I)` (Proposition 8.1, the
book's Proposition 3.25). -/
theorem sobolevSpaceZero_separable (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (sobolevSpaceZero p I) :=
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (SobolevIntervalLp 1 p I) :=
    SobolevMultiIndex.instSecondCountableTopology
  TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- **§8.3, "Moreover, it is reflexive for `p > 1`"**: a closed subspace of the reflexive
`W^{1,p}(I)` (Proposition 8.1, the book's Proposition 3.20; the backbone's
`SobolevMultiIndexZero.instIsReflexive` over chapter 4's `theorem_4_10`). -/
theorem sobolevSpaceZero_reflexive (hp1 : 1 < p) (hp : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (sobolevSpaceZero p I) :=
  have : NormedSpace.IsReflexive ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))) :=
    Brezis.Chapter04.theorem_4_10 hp1 hp
  inferInstance

/-- **§8.3, "The space `H_0^1` is a separable Hilbert space"**: `H_0^1(I)` carries the scalar
product of `H¹(I)` (`inner_H1`), and it is complete and separable. -/
theorem sobolevSpaceZero_hilbert :
    (∀ u v : H10 I, ⟪u, v⟫_ℝ = ⟪(u : SobolevIntervalLp 1 2 I), (v : SobolevIntervalLp 1 2 I)⟫_ℝ) ∧
      CompleteSpace (H10 I) ∧ TopologicalSpace.SeparableSpace (H10 I) :=
  ⟨fun u v ↦ Submodule.coe_inner _ u v, inferInstance,
    sobolevSpaceZero_separable ENNReal.ofNat_ne_top⟩

/-! ### Remarks 13 and 14 -/

/-- **Remark 13.** When `I = ℝ`, `C_c^1(ℝ)` is dense in `W^{1,p}(ℝ)` (Theorem 8.7), and therefore
`W_0^{1,p}(ℝ) = W^{1,p}(ℝ)`, `1 ≤ p < ∞`. The backbone's `sobolevIntervalLpZero_top`. -/
theorem remark_8_13 (hp : p ≠ ∞) : sobolevSpaceZero p ⊤ = ⊤ := sobolevIntervalLpZero_top hp

/-- **Remark 14 (i).** `C_c^∞(I)` is dense in `W_0^{1,p}(I)`: here by definition, the elements
carried by test functions being dense in their closure. -/
theorem remark_8_14_i :
    Dense {v : sobolevSpaceZero p I |
      ∃ φ : 𝓓(I, ℝ), (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] φ} := by
  change ∀ x, x ∈ closure _
  intro x
  rw [closure_subtype]
  have hx : (x : SobolevIntervalLp 1 p I) ∈ closure
      (SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume :
        Set (SobolevIntervalLp 1 p I)) := by
    have hx2 : (x : SobolevIntervalLp 1 p I) ∈ SobolevIntervalLpZero 1 p I := x.2
    rwa [← SetLike.mem_coe, SobolevIntervalLpZero, SobolevMultiIndexZero,
      Submodule.topologicalClosure_coe] at hx2
  refine closure_mono ?_ hx
  rintro v ⟨φ, hφ⟩
  exact ⟨⟨v, SobolevIntervalLpZero.mem_of_fn_ae_eq φ hφ⟩, ⟨φ, hφ⟩, rfl⟩

/-- **Remark 14 (ii).** If `u ∈ W^{1,p}(I) ∩ C_c(I)` — the continuous representative of `u`
vanishes off a compact subset of `I` — then `u ∈ W_0^{1,p}(I)`, `1 ≤ p < ∞`. The backbone's
`SobolevIntervalLpZero.mem_of_hasCompactSupport` (through Theorem 8.12, not the book's
mollification). -/
theorem remark_8_14_ii (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I)
    (h : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ I ∧ ∀ x ∈ closure (I : Set ℝ), x ∉ K → u.rep x = 0) :
    u ∈ sobolevSpaceZero p I :=
  SobolevIntervalLpZero.mem_of_hasCompactSupport hI hp u h

/-- **Remark 14.** (i) `C_c^∞(I)` is dense in `W_0^{1,p}(I)`;
(ii) `W^{1,p}(I) ∩ C_c(I) ⊆ W_0^{1,p}(I)`. -/
theorem remark_8_14 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) :
    Dense {v : sobolevSpaceZero p I |
      ∃ φ : 𝓓(I, ℝ), (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] φ} ∧
    ∀ u : SobolevIntervalLp 1 p I,
      (∃ K : Set ℝ, IsCompact K ∧ K ⊆ I ∧ ∀ x ∈ closure (I : Set ℝ), x ∉ K → u.rep x = 0) →
      u ∈ sobolevSpaceZero p I :=
  ⟨remark_8_14_i, fun u h ↦ remark_8_14_ii hI hp u h⟩

/-! ### Theorem 8.12 and Remark 16 -/

/-- **Theorem 8.12.** Let `u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`. Then `u ∈ W_0^{1,p}(I)` if and only if
`u = 0` on `∂I`. The backbone's `mem_sobolevIntervalLpZero_iff` (the converse by cut-off and
the bounded case, not by the book's truncation `G(nu)/n`); at `p = 2` on `(a, b)` this is
`mem_sobolevIntervalZero_iff` of `Numlib/Analysis/Sobolev/Interval.lean`. -/
theorem theorem_8_12 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I) :
    u ∈ sobolevSpaceZero p I ↔ ∀ x ∈ frontier (I : Set ℝ), u.rep x = 0 :=
  mem_sobolevIntervalLpZero_iff hI hp u

/-- Almost everywhere equality on `I` transfers to the zero extensions on `ℝ`. -/
private theorem indicator_ae_eq_of_ae_eq_restrict {f g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : f =ᵐ[volume.restrict s] g) : s.indicator f =ᵐ[volume] s.indicator g := by
  filter_upwards [(ae_restrict_iff' hs).1 h] with x hx
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, indicator_of_mem hxs, hx hxs]
  · rw [indicator_of_notMem hxs, indicator_of_notMem hxs]

/-- **Remark 16 (i).** Let `1 ≤ p < ∞` and `u ∈ L^p(I)`; let `ū` be the extension of `u` by `0`
outside `I`. Then `u` is (a.e. the function of an element of) `W_0^{1,p}(I)` if and only if
`ū ∈ W^{1,p}(ℝ)`. The backbone's `mem_sobolevIntervalLpZero_iff_indicator_mem`, with the
restriction `SobolevIntervalLp.restrict` of `ū` to `I` for the converse. -/
theorem remark_8_16_i (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) {u : ℝ → ℝ}
    (_hu : MemLp u p (volume.restrict I)) :
    (∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      MemSobolevSpace p ⊤ ((I : Set ℝ).indicator u) := by
  rw [memSobolevSpace_iff_memSobolevIntervalLp]
  constructor
  · rintro ⟨v, hv, hvu⟩
    refine ((mem_sobolevIntervalLpZero_iff_indicator_mem hI hp v).1 hv).congr_ae ?_
    exact SobolevIntervalLp.eventuallyEq_restrict_top_iff.2
      (indicator_ae_eq_of_ae_eq_restrict I.isOpen.measurableSet hvu)
  · intro h
    obtain ⟨w, hw⟩ := h.exists_sobolevIntervalLp
    have hw' : w.fn =ᵐ[volume] (I : Set ℝ).indicator u :=
      SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hw
    have hw'' : w.fn =ᵐ[volume.restrict I] (I : Set ℝ).indicator u := ae_restrict_of_ae hw'
    have hvu : (SobolevIntervalLp.restrict (J := I) (I := ⊤) (subset_univ _) w).fn
        =ᵐ[volume.restrict I] u :=
      (SobolevIntervalLp.fn_restrict_ae_eq _ w).trans
        (hw''.trans (indicator_ae_eq_restrict I.isOpen.measurableSet))
    refine ⟨_, (mem_sobolevIntervalLpZero_iff_indicator_mem hI hp _).2 (h.congr_ae ?_), hvu⟩
    exact SobolevIntervalLp.eventuallyEq_restrict_top_iff.2
      (indicator_ae_eq_of_ae_eq_restrict I.isOpen.measurableSet hvu).symm

/-- **Remark 16 (ii).** Let `1 < p < ∞`, `p'` the conjugate exponent and `u ∈ L^p(I)`. Then `u`
belongs to `W_0^{1,p}(I)` if and only if there is a constant `C` such that
`|∫_I u φ'| ≤ C ‖φ‖_{L^{p'}(I)}` for all `φ ∈ C_c^1(ℝ)` — test functions on the whole line. The
backbone's `mem_sobolevIntervalLpZero_iff_forall_abs_integral_le`. -/
theorem remark_8_16_ii {q : ℝ≥0∞} [p.HolderConjugate q] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) :
    (∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      ∃ C : ℝ, ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
        |∫ x in (I : Set ℝ), u x * deriv φ x| ≤ C * (eLpNorm φ q (volume.restrict I)).toReal :=
  mem_sobolevIntervalLpZero_iff_forall_abs_integral_le hp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne hI hu

/-- **Remark 16.** The two other characterizations of `W_0^{1,p}(I)`: by the zero extension
(`1 ≤ p < ∞`) and by the bound `|∫_I u φ'| ≤ C ‖φ‖_{L^{p'}(I)}` over `φ ∈ C_c^1(ℝ)`
(`1 < p < ∞`). -/
theorem remark_8_16 {q : ℝ≥0∞} [p.HolderConjugate q] (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞)
    {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) :
    ((∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      MemSobolevSpace p ⊤ ((I : Set ℝ).indicator u)) ∧
    (1 < p →
      ((∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
        ∃ C : ℝ, ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
          |∫ x in (I : Set ℝ), u x * deriv φ x|
            ≤ C * (eLpNorm φ q (volume.restrict I)).toReal)) :=
  ⟨remark_8_16_i hI hp hu, fun hp1 ↦ remark_8_16_ii hp1 hp hI hu⟩

/-! ### Proposition 8.13, Poincaré's inequality -/

/-- **Proposition 8.13 (Poincaré's inequality), with the backbone's constant.** For a bounded
interval `I = (a, b)`, `1 ≤ p ≤ ∞` and `u ∈ W_0^{1,p}(I)`,
`‖u‖_{W^{1,p}(I)} ≤ ((b − a)/p^{1/p} + 1) ‖u'‖_{L^p(I)}` in the book's norm — the book's own
proof gives `1 + (b − a)`; at `p = 2` the factor is `(b − a)/√2`
(`SobolevIntervalZero.norm_deriv_zero_le`). The backbone's
`SobolevIntervalLpZero.norm_deriv_zero_le`. -/
theorem proposition_8_13_const {a b : ℝ} (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ sobolevSpaceZero p (Opens.Ioo a b)) :
    sobolevNorm u ≤ ((b - a) / p.toReal ^ p.toReal⁻¹ + 1) * ‖u.deriv 1‖ := by
  have := SobolevIntervalLpZero.norm_deriv_zero_le hab hu
  unfold sobolevNorm
  linarith

/-- **Proposition 8.13 (Poincaré's inequality).** Suppose `I` is a bounded interval. Then there
is a constant `C` (depending on `|I| < ∞`) such that
`‖u‖_{W^{1,p}(I)} ≤ C ‖u'‖_{L^p(I)}` for all `u ∈ W_0^{1,p}(I)`. -/
theorem proposition_8_13 {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, ∀ u ∈ sobolevSpaceZero p (Opens.Ioo a b), sobolevNorm u ≤ C * ‖u.deriv 1‖ :=
  ⟨_, fun _ hu ↦ proposition_8_13_const hab hu⟩

/-- **Proposition 8.13, "in other words"**: on `W_0^{1,p}(I)`, `I` bounded, the quantity
`‖u'‖_{L^p(I)}` is a norm equivalent to the `W^{1,p}` norm: `‖u'‖_p ≤ ‖u‖ ≤ C ‖u'‖_p`, and
`‖u'‖_p = 0` only for `u = 0`. -/
theorem proposition_8_13_equiv {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, ∀ u ∈ sobolevSpaceZero p (Opens.Ioo a b),
      ‖u.deriv 1‖ ≤ ‖u‖ ∧ ‖u‖ ≤ C * ‖u.deriv 1‖ ∧ (‖u.deriv 1‖ = 0 ↔ u = 0) :=
  ⟨_, fun u hu ↦ ⟨SobolevIntervalLp.norm_deriv_le u 1,
    SobolevIntervalLpZero.norm_le_mul_norm_deriv hab hu,
    SobolevIntervalLpZero.norm_deriv_one_eq_zero_iff hab hu⟩⟩

/-- **Remark 17.** If `I = (a, b)` is bounded, `(u', v')_{L²} = ∫ u' v'` defines a scalar product
on `H_0^1(I)` — it is the `L²` scalar product of the derivatives, and it is definite on
`H_0^1` — and the associated norm `‖u'‖_{L²}` is equivalent to the `H¹` norm:
`‖u'‖_{L²} ≤ ‖u‖_{H¹} ≤ √(1 + (b − a)²/2) ‖u'‖_{L²}`. The backbone's
`SobolevIntervalZero.norm_le_seminorm` and `seminorm_eq_zero_iff`. -/
theorem remark_8_17 {a b : ℝ} (hab : a < b) :
    (∀ u v : SobolevIntervalLp 1 2 (Opens.Ioo a b),
      ⟪u.deriv 1, v.deriv 1⟫_ℝ = ∫ x in Ioo a b, u.deriv 1 x * v.deriv 1 x) ∧
    (∀ u ∈ sobolevSpaceZero 2 (Opens.Ioo a b), ⟪u.deriv 1, u.deriv 1⟫_ℝ = 0 → u = 0) ∧
    ∀ u ∈ sobolevSpaceZero 2 (Opens.Ioo a b),
      ‖u.deriv 1‖ ≤ ‖u‖ ∧ ‖u‖ ≤ √(1 + (b - a) ^ 2 / 2) * ‖u.deriv 1‖ := by
  refine ⟨fun u v ↦ ?_, fun u hu h ↦ ?_, fun u hu ↦ ⟨SobolevIntervalLp.norm_deriv_le u 1, ?_⟩⟩
  · rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp [RCLike.inner_apply, mul_comm]
  · rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff] at h
    exact (SobolevIntervalZero.seminorm_eq_zero_iff hab hu).1 h
  · exact SobolevIntervalZero.norm_le_seminorm hab hu

/-! ### Remark 18: `W_0^{m,p}` -/

/-- **Remark 18, on a bounded interval.** Given `m ≥ 2` and `1 ≤ p < ∞`, `W_0^{m,p}(I)` is the
closure of `C_c^m(I)` (here of the test functions) in `W^{m,p}(I)`; on `I = (a, b)`,
`W_0^{m,p}(I) = {u ∈ W^{m,p}(I) : u = Du = ⋯ = D^{m−1} u = 0 on ∂I}`, each `D^j u` read through
its continuous representative (the element `SobolevIntervalLp.derivOne u j` of `W^{1,p}`). The
backbone's `mem_sobolevIntervalLpZero_higher_iff_of_bounded` (by induction from Theorem 8.12,
not the book's Exercise 8.9); stated for `m + 1 ≥ 1`. -/
theorem remark_8_18_of_bounded {a b : ℝ} (hab : a < b) (hp : p ≠ ∞) {m : ℕ}
    (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b)) :
    u ∈ SobolevIntervalLpZero (m + 1) p (Opens.Ioo a b) ↔
      ∀ j : Fin (m + 1), ∀ x ∈ frontier (Ioo a b), (SobolevIntervalLp.derivOne u j).rep x = 0 :=
  mem_sobolevIntervalLpZero_higher_iff_of_bounded hab hp u

/-- **Remark 18.** Given `m ≥ 2` and `1 ≤ p < ∞`, `W_0^{m,p}(I)` is the closure of `C_c^m(I)`
(here of the test functions) in `W^{m,p}(I)`; on every open interval `I`,
`W_0^{m,p}(I) = {u ∈ W^{m,p}(I) : u = Du = ⋯ = D^{m−1} u = 0 on ∂I}`, each `D^j u` read through
its continuous representative (the element `SobolevIntervalLp.derivOne u j` of `W^{1,p}(I)`).
The backbone's `mem_sobolevIntervalLpZero_higher_iff`, which reduces the unbounded case to the
bounded one by the cut-offs `ζ_n u` at every order rather than by the book's Exercise 8.9;
stated for `m + 1 ≥ 1`. -/
theorem remark_8_18 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) {m : ℕ}
    (u : SobolevIntervalLp (m + 1) p I) :
    u ∈ SobolevIntervalLpZero (m + 1) p I ↔
      ∀ j : Fin (m + 1), ∀ x ∈ frontier (I : Set ℝ), (SobolevIntervalLp.derivOne u j).rep x = 0 :=
  mem_sobolevIntervalLpZero_higher_iff hI hp u

/-- **Remark 18, the distinction between `W_0^{2,p}(I)` and `W^{2,p}(I) ∩ W_0^{1,p}(I)`**: on
`I = (0, 1)` the function `x(1 − x)` lies in `W^{2,p}(I)` and (as an element of `W^{1,p}(I)`) in
`W_0^{1,p}(I)`, but not in `W_0^{2,p}(I)`, its derivative at `0` being `1`. -/
theorem remark_8_18_ne (hp : p ≠ ∞) :
    ∃ u : SobolevIntervalLp 2 p (Opens.Ioo 0 1),
      (u.fn =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦ x * (1 - x)) ∧
      SobolevIntervalLp.derivOne u 0 ∈ sobolevSpaceZero p (Opens.Ioo 0 1) ∧
      u ∉ SobolevIntervalLpZero 2 p (Opens.Ioo 0 1) := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo (0 : ℝ) 1
  have hcl := SobolevIntervalLp.closure_coe_Ioo (zero_lt_one' ℝ)
  have hfr : frontier ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ) = {0, 1} := by
    rw [Opens.coe_Ioo, frontier_Ioo zero_lt_one]
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x ↦ x * (1 - x) := ⟨_, rfl⟩
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := by rw [hg]; fun_prop
  have hderiv : ∀ x, deriv g x = 1 * (1 - x) + x * (0 - 1) := fun x ↦ by
    rw [hg]
    exact ((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).deriv
  have hmemj : ∀ j : ℕ,
      MemLp (iteratedDeriv j g) p (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)) :=
    fun j ↦ ((hgs.continuous_iteratedDeriv j
      (by simp)).continuousOn.memLp_top_restrict_Ioo).mono_exponent le_top
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → Lp ℝ p (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)),
      ∀ j, v j = (hmemj j).toLp _ := ⟨_, fun _ ↦ rfl⟩
  have hv0 : ⇑(v 0) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)] g := by
    rw [hv]
    exact (hmemj 0).coeFn_toLp.trans (Eventually.of_forall fun x ↦ by rw [iteratedDeriv_zero])
  have hvj : ∀ j : Fin 3, ⇑(v j) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
      iteratedDeriv j g := fun j ↦ by rw [hv]; exact (hmemj j).coeFn_toLp
  obtain ⟨u, hu⟩ : ∃ u : SobolevIntervalLp 2 p (Opens.Ioo 0 1), u = SobolevIntervalLp.mk v
      (fun j ↦ (hasWeakIteratedDerivOn_of_contDiffOn (I := Opens.Ioo 0 1) (k := j)
        hgs.contDiffOn (by simp)).congr_ae hv0.symm (hvj j).symm) := ⟨_, rfl⟩
  have hfn : u.fn =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)] g := by
    rw [hu]; exact hv0
  have hrep0 : ∀ x ∈ Icc (0 : ℝ) 1, (SobolevIntervalLp.derivOne u 0).rep x = g x := fun x hx ↦
    SobolevIntervalLp.rep_eq_of_continuousOn hI _ hgs.continuous.continuousOn hfn (hcl ▸ hx)
  have hrep1 : ∀ x ∈ Icc (0 : ℝ) 1, (SobolevIntervalLp.derivOne u 1).rep x = deriv g x := by
    intro x hx
    refine SobolevIntervalLp.rep_eq_of_continuousOn hI _
      (hgs.continuous_deriv (by simp)).continuousOn ?_ (hcl ▸ hx)
    have h1 : ⇑(v 1) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
        iteratedDeriv 1 g := hvj 1
    rw [iteratedDeriv_one] at h1
    rw [hu]
    exact h1
  refine ⟨u, ?_, ?_, fun hu0 ↦ ?_⟩
  · rw [← hg]; exact hfn
  · refine (theorem_8_12 hI hp _).2 fun x hx ↦ ?_
    rw [hfr] at hx
    rcases hx with rfl | rfl
    · rw [hrep0 0 (left_mem_Icc.2 zero_le_one), hg]; ring
    · rw [hrep0 1 (right_mem_Icc.2 zero_le_one), hg]; ring
  · have := (remark_8_18_of_bounded (zero_lt_one' ℝ) hp u).1 hu0 1 0
      (by rw [frontier_Ioo zero_lt_one]; simp)
    rw [hrep1 0 (left_mem_Icc.2 zero_le_one), hderiv] at this
    norm_num at this

/-! ### The dual space `W^{-1,p'}(I)` -/

/-- **Notation (§8.3, "The dual space of `W_0^{1,p}(I)`").** The dual space of `W_0^{1,p}(I)`
(`1 ≤ p < ∞`) is denoted by `W^{-1,p'}(I)`: the backbone's `SobolevIntervalLpDual p I`, the
strong dual of `SobolevIntervalLpZero 1 p I`. -/
abbrev sobolevSpaceDual (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) : Type := SobolevIntervalLpDual p I

/-- **Notation (§8.3).** The dual space of `H_0^1(I)` is denoted by `H^{-1}(I)`. -/
abbrev Hneg1 (I : Opens ℝ) : Type := sobolevSpaceDual 2 I

/-- **§8.3, the inclusions `H_0^1 ⊆ L² ⊆ H^{-1}`**, continuous and dense: `L²` identified with
its dual but `H_0^1` not (Remark 3 of chapter 5), the first injection is the inclusion of the
functions, `SobolevIntervalLpZero.toL2`, and the second is `f ↦ (u ↦ ∫_I f u)`,
`SobolevIntervalLpDual.ofL2`; both are injective with dense range. -/
theorem inclusions_H10_L2_Hneg1 (hI : (I : Set ℝ).OrdConnected) :
    Function.Injective (SobolevIntervalLpZero.toL2 2 I hI le_rfl) ∧
      DenseRange (SobolevIntervalLpZero.toL2 2 I hI le_rfl) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2 2 I hI le_rfl) ∧
      DenseRange (SobolevIntervalLpDual.ofL2 2 I hI le_rfl) :=
  have : Fact ((1 : ℝ≥0∞) < 2) := ⟨ENNReal.one_lt_two⟩
  ⟨SobolevIntervalLpZero.toL2_injective hI le_rfl, SobolevIntervalLpZero.denseRange_toL2 hI le_rfl,
    SobolevIntervalLpDual.ofL2_injective hI le_rfl, SobolevIntervalLpDual.denseRange_ofL2 hI le_rfl⟩

/-- **§8.3, the inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}` on a bounded interval**, for all
`1 ≤ p < ∞` with continuous injections (`SobolevIntervalLpZero.toL2OfBounded`,
`SobolevIntervalLpDual.ofL2OfBounded`, both injective), and dense injections when
`1 < p < ∞`. -/
theorem inclusions_W1p_L2_of_bounded {a b : ℝ} (hab : a < b) (_hp : p ≠ ∞) :
    Function.Injective (SobolevIntervalLpZero.toL2OfBounded p hab) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2OfBounded p hab) ∧
      (1 < p → DenseRange (SobolevIntervalLpZero.toL2OfBounded p hab) ∧
        DenseRange (SobolevIntervalLpDual.ofL2OfBounded p hab)) :=
  ⟨SobolevIntervalLpZero.toL2OfBounded_injective hab,
    SobolevIntervalLpDual.ofL2OfBounded_injective hab, fun hp1 ↦
      have : Fact (1 < p) := ⟨hp1⟩
      have : Fact (p ≠ ∞) := ⟨_hp⟩
      ⟨SobolevIntervalLpZero.denseRange_toL2OfBounded hab,
        SobolevIntervalLpDual.denseRange_ofL2OfBounded hab⟩⟩

/-- **§8.3, the inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}` on an unbounded interval**, only for
`1 ≤ p ≤ 2` (Remark 12), with continuous injections `SobolevIntervalLpZero.toL2` and
`SobolevIntervalLpDual.ofL2`. -/
theorem inclusions_W1p_L2_of_unbounded (hI : (I : Set ℝ).OrdConnected)
    (_hunb : ¬ Bornology.IsBounded (I : Set ℝ)) (hp : p ≤ 2) :
    Function.Injective (SobolevIntervalLpZero.toL2 p I hI hp) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2 p I hI hp) :=
  ⟨SobolevIntervalLpZero.toL2_injective hI hp, SobolevIntervalLpDual.ofL2_injective hI hp⟩

/-- **Proposition 8.14.** Let `F ∈ W^{-1,p'}(I)`, `1 ≤ p < ∞`. Then there are two functions
`f₀, f₁ ∈ L^{p'}(I)` — the two components `f 0`, `f 1` of a pair `f` — such that
`⟨F, u⟩ = ∫_I f₀ u + ∫_I f₁ u'` for all `u ∈ W_0^{1,p}(I)` and `‖F‖_{W^{-1,p'}} = ‖f‖`, the norm of
the pair in the `ℓ^{p'}` product `L^{p'}(I) × L^{p'}(I)`. The book's
`‖F‖ = max(‖f₀‖_{p'}, ‖f₁‖_{p'})` is this identity for its sum norm `‖u‖_p + ‖u'‖_p` on
`W^{1,p}`; the type carries the `ℓ^p` sum `(‖u‖_p^p + ‖u'‖_p^p)^{1/p}`, whose dual norm is the
`ℓ^{p'}` one (they agree at `p = 1`). The backbone's `SobolevIntervalLpDual.exists_repr`
(Hahn–Banach and the Riesz representation theorem, as in the book). -/
theorem proposition_8_14 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (F : sobolevSpaceDual p I) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u : sobolevSpaceZero p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * (u : SobolevIntervalLp 1 p I).fn x)
          + ∫ x in (I : Set ℝ), f 1 x * (u : SobolevIntervalLp 1 p I).deriv 1 x) ∧
      ‖F‖ = ‖f‖ :=
  SobolevIntervalLpDual.exists_repr hp F

/-- **Proposition 8.14, "when `I` is bounded we can take `f₀ = 0`"**: for `I = (a, b)` and
`F ∈ W^{-1,p'}(I)`, there is `f₁ ∈ L^{p'}(I)` with `⟨F, u⟩ = ∫_I f₁ u'` for all `u ∈ W_0^{1,p}(I)`
(Poincaré's inequality makes `u ↦ u'` an isomorphism onto its range). The backbone's
`SobolevIntervalLpDual.exists_repr_of_bounded`. -/
theorem proposition_8_14_bounded {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞) {a b : ℝ}
    (hab : a < b) (F : sobolevSpaceDual p (Opens.Ioo a b)) :
    ∃ f₁ : Lp ℝ q (volume.restrict (Ioo a b)), ∀ u : sobolevSpaceZero p (Opens.Ioo a b),
      F u = ∫ x in Ioo a b, f₁ x * (u : SobolevIntervalLp 1 p (Opens.Ioo a b)).deriv 1 x :=
  SobolevIntervalLpDual.exists_repr_of_bounded hp hab F

/-- **Remark 19.** The functions `f₀` and `f₁` are not uniquely determined by `F`: for every
test function `g` on `I`, the pair `(f₀ + g', f₁ + g)` represents the same functional as
`(f₀, f₁)`, since `∫_I g' u = −∫_I g u'` for `u ∈ W_0^{1,p}(I)`. The backbone's
`SobolevIntervalLpDual.repr_not_unique`. -/
theorem remark_8_19 {q : ℝ≥0∞} [p.HolderConjugate q] {f₀ f₁ : ℝ → ℝ}
    (hf₀ : MemLp f₀ q (volume.restrict I)) (hf₁ : MemLp f₁ q (volume.restrict I)) (g : 𝓓(I, ℝ))
    (u : sobolevSpaceZero p I) :
    (∫ x in (I : Set ℝ), (f₀ x + deriv g x) * (u : SobolevIntervalLp 1 p I).fn x)
        + ∫ x in (I : Set ℝ), (f₁ x + g x) * (u : SobolevIntervalLp 1 p I).deriv 1 x
      = (∫ x in (I : Set ℝ), f₀ x * (u : SobolevIntervalLp 1 p I).fn x)
        + ∫ x in (I : Set ℝ), f₁ x * (u : SobolevIntervalLp 1 p I).deriv 1 x :=
  SobolevIntervalLpDual.repr_not_unique hf₀ hf₁ g (u : SobolevIntervalLp 1 p I)

/-- **Remark 21.** The first assertion of Proposition 8.14 also holds for continuous linear
functionals on `W^{1,p}(I)`, `1 ≤ p < ∞`: every `F ∈ (W^{1,p}(I))^*` may be represented as
`⟨F, u⟩ = ∫_I f₀ u + ∫_I f₁ u'` for all `u ∈ W^{1,p}(I)`, for some `f₀, f₁ ∈ L^{p'}(I)`. The
backbone's `SobolevIntervalLp.exists_repr_strongDual`. -/
theorem remark_8_21 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (F : StrongDual ℝ (SobolevIntervalLp 1 p I)) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      ∀ u : SobolevIntervalLp 1 p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * u.fn x) + ∫ x in (I : Set ℝ), f 1 x * u.deriv 1 x :=
  let ⟨f, hf, _⟩ := SobolevIntervalLp.exists_repr_strongDual hp F
  ⟨f, hf⟩

end Brezis.Chapter08
