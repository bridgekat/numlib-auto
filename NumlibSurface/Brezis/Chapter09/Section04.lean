import Numlib.Analysis.PDE.Elliptic.Dirichlet
import NumlibSurface.Brezis.Chapter09.Section03

/-!
# Brezis §9.4: The space `W_0^{1,p}(Ω)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.4, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue
measure: the Definition of `W_0^{1,p}(Ω)` and `H_0^1(Ω)`, Remarks 17 and 18, Lemma 9.5,
Theorem 9.17 (`u ∈ W^{1,p}(Ω) ∩ C(Ω̄)`: `u = 0` on `Γ` iff `u ∈ W_0^{1,p}(Ω)`) with Remark 19,
Proposition 9.18 (three characterizations of `W_0^{1,p}(Ω)`, with the extension by zero),
Remark 20 (Corollary 9.14 and Theorem 9.16 on `W_0^{1,p}(Ω)` of an arbitrary open set),
Corollary 9.19 (Poincaré's inequality) with Remark 21, Remark 22 (`W_0^{m,p}(Ω)`), the dual
space `W^{−1,p'}(Ω)` with the inclusions `H_0^1(Ω) ⊂ L^2(Ω) ⊂ H^{−1}(Ω)`, and Proposition 9.20.

The backbone is `Numlib/Analysis/Sobolev/Zero` (the extension by zero, Theorem 9.17,
Proposition 9.18, Remarks 17, 18, 20, 21, Proposition 9.20, the Gelfand triple),
`Numlib/Analysis/Sobolev/Cutoff` (Lemma 9.5), `Numlib/Analysis/Sobolev/Poincare` (Corollary 9.19,
Remark 21's bounded-projection clause), `Numlib/Analysis/Sobolev/EmbeddingDomain` and
`Numlib/Analysis/Sobolev/Compactness` (Remark 20) and, for the scalar product of `H_0^1(Ω)`,
the Dirichlet form of `Numlib/Analysis/PDE/Elliptic/Dirichlet`.

## Conventions

* The book's `W_0^{1,p}(Ω)`, "the closure of `C_c^1(Ω)` in `W^{1,p}(Ω)`", is the submodule
  `sobolevZeroSpace N p Ω := SobolevEuclideanZero N 1 p Ω` of `sobolevSpace N p Ω`, the closure
  of the test functions `𝓓(Ω, ℝ)`; the two closures agree by Remark 18
  (`remark_9_18_closure`). `u ∈ W_0^{1,p}(Ω)` is `u ∈ sobolevZeroSpace N p Ω`; a function
  `u : ℝ^N → ℝ` "belongs to `W_0^{1,p}(Ω)`" when it is almost everywhere on `Ω` the function of an
  element of `sobolevZeroSpace N p Ω`.
* The results needing `Ω` of class `C^1` (Theorem 9.17 (ii) ⇒ (i), Proposition 9.18 (iii) ⇒ (i))
  are stated with `IsClassC1` of §9.2 on `ℝ^{d+1}`; the implications valid on every open set
  (Remark 19) are stated for every `N`.
* "`W_0^{1,p}(Ω) ⊂ L^q(Ω)` with continuous (compact) injection" is
  `IsContinuousInjectionLpZero` (`IsCompactInjectionLpZero`), the vocabulary of §9.3 for the
  subspace `W_0^{1,p}(Ω)` along the inclusion `SobolevMultiIndex.toLpₗOn`.
* `‖∇u‖_{L^p(Ω)}` is `eLpNorm (gradient u) p`, as in §9.1 and §9.3; the backbone's `ℓ^p`
  reading `SobolevMultiIndex.gradNorm u` is bridged by §9.3's `gradNorm_le_eLpNorm_gradient` and
  `toReal_eLpNorm_gradient_le_gradNorm`, and at `p = 2` the two agree
  (`gradNorm_eq_toReal_eLpNorm_gradient_two`).
* Hypotheses the book leaves implicit and the backbone needs: `N ≥ 2` or `p > 1` in the `L^q`
  clauses of Remark 20 (as in Corollary 9.13), `N ≥ 2` in the finite-measure clause of Remark 21
  (the statement is false for `N = 1`), `N ≥ 2` in Remark 16's example; Remark 21's
  bounded-projection clause is stated for the last coordinate axis.

## Main results

* `sobolevZeroSpace`, `hZeroSpace`, `sobolevZeroSpace_banach`, `remark_9_17`, `remark_9_18`,
  `remark_9_18_closure`, `lemma_9_5`.
* `theorem_9_17` (with `theorem_9_17_mp`, `theorem_9_17_mpr`), `remark_9_19`,
  `proposition_9_18` (with `_i_ii`, `_ii_iii`, `_i_iii`, `_iii_i`).
* `IsContinuousInjectionLpZero`, `IsCompactInjectionLpZero`, `remark_9_20` (with
  `remark_9_20_embedding`, `remark_9_20_compact`, `remark_9_20_sobolev` and their cases).
* `corollary_9_19` (with `corollary_9_19_gradNorm`, `corollary_9_19_norm`,
  `corollary_9_19_inner`), `remark_9_21` (with `remark_9_21_measure`, `remark_9_21_projection`).
* `sobolevZeroSpaceHigher`, `sobolevZeroSpaceHigher_eq_closure_contDiff`, `dualSpace`,
  `hMinusOne`, `dual_inclusions`, `proposition_9_20`, `proposition_9_20_bounded`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

/-! ### The Definition -/

section Definition

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **The space `W_0^{1,p}(Ω)`** of §9.4, `1 ≤ p < ∞`: "the closure of `C_c^1(Ω)` in
`W^{1,p}(Ω)`", as the backbone's `SobolevEuclideanZero N 1 p Ω`, the closure of the test
functions `𝓓(Ω, ℝ)` in `W^{1,p}(Ω)` — the same closure by Remark 18 (`remark_9_18_closure`). It
is a submodule of `sobolevSpace N p Ω`, so that `u ∈ W_0^{1,p}(Ω)` is literally membership. -/
noncomputable abbrev sobolevZeroSpace (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Submodule ℝ (sobolevSpace N p Ω) :=
  SobolevEuclideanZero N 1 p Ω

/-- **The space `H_0^1(Ω) = W_0^{1,2}(Ω)`**, footnote 19's `H_0^1`. -/
noncomputable abbrev hZeroSpace (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Submodule ℝ (hSpace N Ω) :=
  sobolevZeroSpace N 2 Ω

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The Definition, second sentence.** The space `W_0^{1,p}(Ω)`, `1 ≤ p < ∞`, equipped with
the `W^{1,p}` norm, is a separable Banach space; it is reflexive if `1 < p < ∞`. `H_0^1(Ω)`,
equipped with the `H^1` scalar product, is a Hilbert space — its inner product is the
restriction of the scalar product `(u, v)_{H^1} = ∫_Ω u v + ∑_i ∫_Ω ∂_i u ∂_i v` of `H^1(Ω)`
(`hInner`). All of it because `W_0^{1,p}(Ω)` is a closed subspace of `W^{1,p}(Ω)`
(Proposition 9.1). -/
theorem sobolevZeroSpace_banach (hp' : p ≠ ⊤) :
    CompleteSpace (sobolevZeroSpace N p Ω) ∧ Chapter03.IsSeparable (sobolevZeroSpace N p Ω) ∧
    (1 < p → Chapter03.IsReflexive (sobolevZeroSpace N p Ω)) ∧
    (CompleteSpace (hZeroSpace N Ω) ∧ ∀ u v : hZeroSpace N Ω,
      inner ℝ u v = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u : hSpace N Ω) x
        * SobolevMultiIndex.fn (v : hSpace N Ω) x)
        + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u : hSpace N Ω) i x
          * partialDeriv (v : hSpace N Ω) i x) := by
  refine ⟨inferInstance, ?_, fun hp ↦ ?_, inferInstance, fun u v ↦ ?_⟩
  · have := Fact.mk hp'
    exact (Chapter03.separable_iff _).2 inferInstance
  · have := Chapter04.theorem_4_10 (μ := volume.restrict (Ω : Set 𝔼)) hp hp'
    exact Chapter03.isReflexive_iff.2 inferInstance
  · rw [Submodule.coe_inner, hInner]

/-- **Remark 17.** Since `C_c^1(ℝ^N)` is dense in `W^{1,p}(ℝ^N)` (Theorem 9.2), we have
`W_0^{1,p}(ℝ^N) = W^{1,p}(ℝ^N)`, `1 ≤ p < ∞`. The backbone's `SobolevEuclideanZero.eq_top`. The
remark's "by contrast, in general `W_0^{1,p}(Ω) ≠ W^{1,p}(Ω)`" is the content of Theorem 9.17,
and its punctured space `H_0^1(ℝ^N ∖ {0}) = H^1(ℝ^N ∖ {0})`, `N ≥ 2`, is `remark_9_17_punctured`. -/
theorem remark_9_17 (hp' : p ≠ ⊤) : sobolevZeroSpace N p ⊤ = ⊤ :=
  SobolevEuclideanZero.eq_top hp'

/-- **Remark 18, and the book's Definition through `C_c^1(Ω)`.** Every `C^1` function `v` with
compact support in `Ω` lies in `W_0^{1,p}(Ω)`, `1 ≤ p < ∞` (as the function of an element of
`sobolevZeroSpace N p Ω`): the backbone's
`SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport`, from Lemma 9.5. -/
theorem remark_9_18 (hp' : p ≠ ⊤) {v : 𝔼 → ℝ} (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (hvΩ : tsupport v ⊆ Ω) :
    ∃ u ∈ sobolevZeroSpace N p Ω, SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v :=
  SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport hp' hv hvc hvΩ

/-- **Remark 18, "in other words".** `C_c^∞(Ω)` could equally well have been used instead of
`C_c^1(Ω)` in the definition of `W_0^{1,p}(Ω)`, `1 ≤ p < ∞`: the closure in `W^{1,p}(Ω)` of the
`C^1` functions with compact support in `Ω` is the closure of the test functions `𝓓(Ω, ℝ)`, which
is `sobolevZeroSpace N p Ω`. (`⊆`: `remark_9_18` places `C_c^1(Ω)` in the closed subspace
`W_0^{1,p}(Ω)`; `⊇`: a test function is a `C^1` function with compact support in `Ω`.) -/
theorem remark_9_18_closure (hp' : p ≠ ⊤) :
    closure {u : sobolevSpace N p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ 1 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v}
      = (sobolevZeroSpace N p Ω : Set (sobolevSpace N p Ω)) := by
  apply subset_antisymm
  · refine closure_minimal ?_ SobolevMultiIndexZero.isClosed
    rintro u ⟨v, hv, hvc, hvΩ, hu⟩
    exact SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu
  · rw [show (sobolevZeroSpace N p Ω : Set (sobolevSpace N p Ω))
        = closure (SobolevMultiIndex.testFunctions ℝ 𝔟 1 p Ω volume : Set (sobolevSpace N p Ω))
        from Submodule.topologicalClosure_coe _]
    refine closure_mono ?_
    rintro u ⟨φ, hφ⟩
    exact ⟨φ, φ.contDiff.of_le (by simp), φ.hasCompactSupport, φ.tsupport_subset, hφ⟩

/-- **Lemma 9.5.** Let `u ∈ W^{1,p}(Ω)` with `1 ≤ p < ∞` and assume that `supp u` is a compact
subset of `Ω`: `u = 0` almost everywhere on `Ω` outside a compact `K ⊆ Ω`. Then
`u ∈ W_0^{1,p}(Ω)`. The backbone's `SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`
(the book's proof: a cut-off `α ∈ C_c^1(ω)`, `α = 1` on `supp u`, and Theorem 9.2). -/
theorem lemma_9_5 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {K : Set 𝔼} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hu : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), x ∉ K → SobolevMultiIndex.fn u x = 0) :
    u ∈ sobolevZeroSpace N p Ω :=
  SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact hp' u hK hKΩ hu

/-! ### Theorem 9.17 -/

/-- **Theorem 9.17, (i) ⇒ (ii), on an arbitrary open set** (Remark 19: "in the proof of
(i) ⇒ (ii) we have not used the smoothness of `Ω`"). Let `u ∈ W^{1,p}(Ω) ∩ C(Ω̄)`, `1 ≤ p < ∞`
— `u` with a representative `ũ` continuous on `closure Ω`. If `ũ = 0` on `Γ = ∂Ω` then
`u ∈ W_0^{1,p}(Ω)`. The backbone's
`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`: the truncations
`u_n = G(nu)/n` of the book's proof (Proposition 9.5) have compact support in `Ω`, so lie in
`W_0^{1,p}(Ω)` by Lemma 9.5, and converge to `u` in `W^{1,p}(Ω)`. -/
theorem theorem_9_17_mp (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (h0 : EqOn ũ 0 (frontier (Ω : Set 𝔼))) :
    u ∈ sobolevZeroSpace N p Ω :=
  SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier hp' u hu hc h0

/-- **Remark 19, first sentence.** The implication (i) ⇒ (ii) of Theorem 9.17 holds for every
open set `Ω`, with no smoothness hypothesis: `theorem_9_17_mp`. (The second sentence, that the
converse fails on `Ω = ℝ^N ∖ {0}`, `N ≥ 2`, `p ≤ N`, is the punctured-space clause of Remark 17,
`remark_9_17_punctured`.) -/
theorem remark_9_19 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (h0 : EqOn ũ 0 (frontier (Ω : Set 𝔼))) :
    u ∈ sobolevZeroSpace N p Ω :=
  theorem_9_17_mp hp' u hu hc h0

end Definition

section ClassC1

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 9.17, (ii) ⇒ (i).** Suppose that `Ω` is of class `C^1` and let
`u ∈ W^{1,p}(Ω) ∩ C(Ω̄)`, `1 ≤ p < ∞`, with the representative `ũ` continuous on `closure Ω`.
If `u ∈ W_0^{1,p}(Ω)` then `ũ = 0` on `Γ`. The backbone's
`SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure`: by local charts, the problem on
`Q_+` — `u ∈ W_0^{1,p}(Q_+) ∩ C(Q̄_+)` vanishes on `Q_0` — through the strip inequality
`ε⁻¹ ∫_{|x'|<1} ∫_0^ε |u| ≤ ∫_{|x'|<1} ∫_0^ε |∂_N u|`. -/
theorem theorem_9_17_mpr (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    {u : sobolevSpace (d + 1) p Ω} (hu : u ∈ sobolevZeroSpace (d + 1) p Ω) {ũ : 𝔼 → ℝ}
    (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) : EqOn ũ 0 (frontier (Ω : Set 𝔼)) :=
  SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure hp' hΩ hu hũ hc

/-- **Theorem 9.17.** Suppose that `Ω` is of class `C^1`. Let `u ∈ W^{1,p}(Ω) ∩ C(Ω̄)` with
`1 ≤ p < ∞` — `u ∈ W^{1,p}(Ω)` with a representative `ũ` continuous on `closure Ω`. Then the
following properties are equivalent: (i) `ũ = 0` on `Γ`; (ii) `u ∈ W_0^{1,p}(Ω)`. Footnote 21:
for `p > N` the continuous representative exists automatically (Corollary 9.14). -/
theorem theorem_9_17 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) (u : sobolevSpace (d + 1) p Ω)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    EqOn ũ 0 (frontier (Ω : Set 𝔼)) ↔ u ∈ sobolevZeroSpace (d + 1) p Ω :=
  ⟨theorem_9_17_mp hp' u hũ hc, fun hu ↦ theorem_9_17_mpr hΩ hp' hu hũ hc⟩

end ClassC1

/-! ### Proposition 9.18 -/

section Prop18

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Proposition 9.18, (i) ⇒ (ii), on an arbitrary open set.** If `u ∈ L^p(Ω)` belongs to
`W_0^{1,p}(Ω)` (`p` and `p'` conjugate), there is a constant `C` such that
`|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{L^{p'}(Ω)}` for all `φ ∈ C_c^1(ℝ^N)` and all `i = 1, …, N`; one can take
`C = ‖∇u‖_{L^p(Ω)}` (the backbone's `ℓ^p` reading `SobolevMultiIndex.gradNorm`). The backbone's
`SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le`: for `u_n ∈ C_c^1(Ω)` with `u_n → u`,
`|∫_Ω u_n ∂_i φ| = |∫_Ω ∂_i u_n φ| ≤ ‖∂_i u_n‖_p ‖φ‖_{p'}`, and one passes to the limit. -/
theorem proposition_9_18_i_ii [p.HolderConjugate q] {u : 𝔼 → ℝ}
    (h : ∃ v ∈ sobolevZeroSpace N p Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal := by
  obtain ⟨v, hv, hvu⟩ := h
  refine ⟨SobolevMultiIndex.gradNorm v, fun φ hφ hφc i ↦ ?_⟩
  have h1 := SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le (q := q) ⟨v, hv⟩ hφ hφc i
  have e : ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼),
          SobolevMultiIndex.fn v x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    integral_congr_ae (hvu.symm.mono fun x hx ↦ by simp only [hx])
  rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right
    (SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm v i) ENNReal.toReal_nonneg)

/-- **Proposition 9.18, (ii) ⇒ (iii), on an arbitrary open set.** Let `u ∈ L^p(Ω)`,
`1 < p < ∞` (`p'` the conjugate exponent, `p' ≠ ∞`). If there is a constant `C` with
`|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{L^{p'}(Ω)}` for all `φ ∈ C_c^1(ℝ^N)` and all `i`, then the extension by
zero `ū` (`= u` on `Ω`, `= 0` on `ℝ^N ∖ Ω`) belongs to `W^{1,p}(ℝ^N)`. The backbone's
`SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le`: since
`∫_{ℝ^N} ū ∂_i φ = ∫_Ω u ∂_i φ` and `‖φ‖_{L^{p'}(Ω)} ≤ ‖φ‖_{L^{p'}(ℝ^N)}`, this is
Proposition 9.3 on `ℝ^N`. -/
theorem proposition_9_18_ii_iii [p.HolderConjugate q] (hq : q ≠ ⊤) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set 𝔼)))
    (h : ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal) :
    ∃ w : sobolevSpace N p ⊤, SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨w, hw⟩ := (exists_fn_ae_eq_iff (N := N) (p := p) (Ω := ⊤) (m := 1) _).2
    (SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le hq hu hC)
  exact ⟨w, by simpa [Measure.restrict_coe_top] using hw⟩

/-- **Proposition 9.18, (i) ⇒ (iii), on an arbitrary open set, with the derivatives**, for
every `1 ≤ p ≤ ∞`: for `u ∈ W_0^{1,p}(Ω)` the extension by zero `ū` belongs to `W^{1,p}(ℝ^N)`,
"and in this case `∂ū/∂x_i = \overline{∂u/∂x_i}`" — the zero extension of `∂u/∂x_i`. The
backbone's extension by zero `SobolevEuclideanZero.extendZeroL` (an isometry
`W_0^{1,p}(Ω) → W^{1,p}(ℝ^N)`), with `SobolevEuclideanZero.fn_extendZeroL` and
`SobolevEuclideanZero.weakDeriv_extendZeroL_single`; proved without the Riesz representation
theorem, by the closedness of the weak derivative under `L^p` limits applied to the zero
extensions of approximating test functions. -/
theorem proposition_9_18_i_iii {u : sobolevSpace N p Ω} (hu : u ∈ sobolevZeroSpace N p Ω) :
    ∃ w : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator (SobolevMultiIndex.fn u) ∧
      ∀ i, (partialDeriv w i : 𝔼 → ℝ) =ᵐ[volume] (Ω : Set 𝔼).indicator (partialDeriv u i) :=
  ⟨SobolevEuclideanZero.extendZeroL N p Ω ⟨u, hu⟩, SobolevEuclideanZero.fn_extendZeroL _,
    fun i ↦ SobolevEuclideanZero.weakDeriv_extendZeroL_single _ i⟩

end Prop18

section Prop18ClassC1

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Proposition 9.18, (iii) ⇒ (i).** Suppose `Ω` is of class `C^1` and `1 ≤ p < ∞`. If the
extension by zero `ū` of `u` belongs to `W^{1,p}(ℝ^N)`, then `u ∈ W_0^{1,p}(Ω)` (as the function
of an element of `sobolevZeroSpace`). The backbone's
`SobolevEuclideanZero.mem_of_indicator_memSobolev`: by local charts and a partition of unity
this is the problem on `Q_+`, solved with the one-sided mollifiers `ρ_n` supported in
`{1/(2n) < x_N < 1/n}`, for which `ρ_n ⋆ (α ū) ∈ C_c^1(Q_+)`. -/
theorem proposition_9_18_iii_i (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) {u : 𝔼 → ℝ}
    (h : ∃ w : sobolevSpace (d + 1) p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u) :
    ∃ v ∈ sobolevZeroSpace (d + 1) p Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  obtain ⟨w, hw⟩ := h
  refine SobolevEuclideanZero.mem_of_indicator_memSobolev hp' hΩ ?_
  exact (exists_fn_ae_eq_iff (Ω := ⊤) (m := 1) _).1
    ⟨w, by simpa [Measure.restrict_coe_top] using hw⟩

/-- **Proposition 9.18.** Suppose `Ω` is of class `C^1`. Let `u ∈ L^p(Ω)` with `1 < p < ∞`
(`p'` the conjugate exponent). The following properties are equivalent:
(i) `u ∈ W_0^{1,p}(Ω)`;
(ii) there is a constant `C` such that `|∫_Ω u ∂φ/∂x_i| ≤ C ‖φ‖_{L^{p'}(Ω)}` for all
`φ ∈ C_c^1(ℝ^N)` and all `i = 1, …, N`;
(iii) the function `ū` (`= u` on `Ω`, `= 0` on `ℝ^N ∖ Ω`) belongs to `W^{1,p}(ℝ^N)` — and in
this case `∂ū/∂x_i = \overline{∂u/∂x_i}` (`proposition_9_18_i_iii`).
Only (iii) ⇒ (i) uses the regularity of `Ω`. -/
theorem proposition_9_18 (hΩ : IsClassC1 (Ω : Set 𝔼)) [p.HolderConjugate q] (hp : 1 < p)
    (hp' : p ≠ ⊤) {u : 𝔼 → ℝ} (hu : MemLp u p (volume.restrict (Ω : Set 𝔼))) :
    [∃ v ∈ sobolevZeroSpace (d + 1) p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u,
      ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin (d + 1),
        |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
          ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal,
      ∃ w : sobolevSpace (d + 1) p ⊤,
        SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u].TFAE := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  tfae_have 1 → 2 := proposition_9_18_i_ii
  tfae_have 2 → 3 := proposition_9_18_ii_iii hq hu
  tfae_have 3 → 1 := proposition_9_18_iii_i hΩ hp'
  tfae_finish

end Prop18ClassC1

/-! ### Remark 20: the embeddings on `W_0^{1,p}(Ω)` of an arbitrary open set -/

/-- **"`W_0^{1,p}(Ω) ⊂ L^q(Ω)` with continuous injection"**, the conclusion of Remark 20: every
function of `W_0^{1,p}(Ω)` lies in `L^q(Ω)` and the inclusion `u ↦ fn u` of the subspace
(`SobolevMultiIndex.toLpₗOn`) is a continuous embedding — the vocabulary
`IsContinuousInjectionLp` of §9.3 for the subspace `W_0^{1,p}(Ω)`. -/
def IsContinuousInjectionLpZero (N : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevZeroSpace N p Ω, MemLp (SobolevMultiIndex.fn (u : sobolevSpace N p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsContinuousEmbedding (SobolevMultiIndex.toLpₗOn ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p Ω volume
      (sobolevZeroSpace N p Ω) h)

/-- **"`W_0^{1,p}(Ω) ⊂ L^q(Ω)` with compact injection"**, the conclusion of Remark 20's second
clause (Theorem 9.16 on `W_0^{1,p}(Ω)`): the inclusion `u ↦ fn u` of the subspace is a compact
embedding. -/
def IsCompactInjectionLpZero (N : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevZeroSpace N p Ω, MemLp (SobolevMultiIndex.fn (u : sobolevSpace N p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsCompactEmbedding (SobolevMultiIndex.toLpₗOn ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p Ω volume
      (sobolevZeroSpace N p Ω) h)

section Remark20

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- A compact injection is a continuous injection. -/
theorem IsCompactInjectionLpZero.isContinuousInjectionLpZero [Fact (1 ≤ (q : ℝ≥0∞))]
    (h : IsCompactInjectionLpZero N p q Ω) : IsContinuousInjectionLpZero N p q Ω :=
  let ⟨h, hc⟩ := h
  ⟨h, hc.toIsContinuousEmbedding⟩

/-- **Remark 20, the conclusion of Corollary 9.14 on `W_0^{1,p}(Ω)`, case `p < N`**: for an
arbitrary open set `Ω`, `1 ≤ p < N` and `1/p* = 1/p − 1/N`, `W_0^{1,p}(Ω) ⊂ L^{p*}(Ω)` with
continuous injection — stated for every `q ∈ [p, p*]`. The extension by zero
(`SobolevEuclideanZero.hasSobolevExtensionOn`) replaces the extension operator of Theorem 9.7:
the backbone's `SobolevEuclideanZero.isContinuousEmbedding_toLp_of_lt`. -/
theorem remark_9_20_embedding_lt [Fact (1 ≤ (q : ℝ≥0∞))] {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousInjectionLpZero N p q Ω :=
  ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_of_lt hpN hp' hpq hqp'⟩

/-- **Remark 20, the conclusion of Corollary 9.14 on `W_0^{1,p}(Ω)`, case `p = N`**: for an
arbitrary open set `Ω` and `N ≥ 2`, `W_0^{1,N}(Ω) ⊂ L^q(Ω)` with continuous injection for all
`q ∈ [N, +∞)`. The backbone's `SobolevEuclideanZero.isContinuousEmbedding_toLp_of_eq`. -/
theorem remark_9_20_embedding_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N) (hp : p = (N : ℝ≥0))
    (hq : p ≤ q) : IsContinuousInjectionLpZero N p q Ω := by
  subst hp
  have : Fact (1 ≤ (N : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_of_eq hN hq⟩

/-- **Remark 20, the conclusion of Corollary 9.14 on `W_0^{1,p}(Ω)`, case `p > N`, the
injection**: for an arbitrary open set `Ω` and `N < p < ∞`, `W_0^{1,p}(Ω) ⊂ L^∞(Ω)` with
continuous injection. The backbone's `SobolevEuclideanZero.isContinuousEmbedding_toLp_top_of_lt`. -/
theorem remark_9_20_embedding_gt (hp : (N : ℝ≥0) < p) : IsContinuousInjectionLpZero N p ⊤ Ω :=
  ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_top_of_lt hp⟩

/-- **Remark 20, the conclusion of Corollary 9.14 on `W_0^{1,p}(Ω)`, case `p > N`, the Hölder
estimate and `W_0^{1,p}(Ω) ⊂ C(Ω̄)`**: for an arbitrary open set `Ω` and `N < p < ∞`, with
`α = 1 − N/p`, there is `C = C(p, N)` such that every `u ∈ W_0^{1,p}(Ω)` has a representative `ũ`
continuous on `Ω̄` with `|ũ(x) − ũ(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α` for all `x, y ∈ Ω̄`, hence
`|u(x) − u(y)| ≤ C ‖u‖_{W^{1,p}} |x − y|^α` for a.e. `x, y ∈ Ω`. The backbone's
`SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq` (Morrey's representative of
the extension by zero, continuous on all of `ℝ^N`). -/
theorem remark_9_20_embedding_holder (hp : (N : ℝ≥0) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
            - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
          ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p) := by
  obtain ⟨C, hC⟩ := SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq
    (N := N) (p := p) (Ω := Ω) hp
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hα : ((1 - (N : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - (N : ℝ) / p := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hh, -⟩ := hC u
  have hbound : ∀ x y, |ũ x - ũ y|
      ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p) := by
    intro x y
    have h1 := hh.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    refine h1.trans ?_
    gcongr
    exact (bookNorm_equiv (u : sobolevSpace N p Ω)).1
  refine ⟨ũ, hc.continuousOn, hae, fun x _ y _ ↦ hbound x y, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Remark 20, first clause.** "The conclusion of Corollary 9.14 is true for `W_0^{1,p}(Ω)`
with an arbitrary open set `Ω`": for `1 ≤ p < ∞`, `W_0^{1,p}(Ω) ⊂ L^{p*}(Ω)` (indeed `L^q(Ω)`,
`q ∈ [p, p*]`) if `p < N`; `W_0^{1,p}(Ω) ⊂ L^q(Ω)` for all `q ∈ [N, +∞)` if `p = N` (and
`N ≥ 2`); `W_0^{1,p}(Ω) ⊂ L^∞(Ω)` and `W_0^{1,p}(Ω) ⊂ C(Ω̄)` with the Hölder estimate if `p > N`,
all with continuous injections. The extension by zero is valid on every open set (Proposition
9.18, (i) ⇒ (iii)), which is why no regularity of `Ω` is needed. -/
theorem remark_9_20_embedding :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → p ≤ q →
      q ≤ p' → IsContinuousInjectionLpZero N p q Ω) ∧
    (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLpZero N p q Ω) ∧
    ((N : ℝ≥0) < p → IsContinuousInjectionLpZero N p ⊤ Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
        ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
        SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
        (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
          |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
        ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
          |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
              - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
            ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) :=
  ⟨fun _ _ _ hpN hp' hpq hqp' ↦ remark_9_20_embedding_lt hpN hp' hpq hqp',
    fun hN hp _ _ hq ↦ remark_9_20_embedding_eq hN hp hq,
    fun hp ↦ ⟨remark_9_20_embedding_gt hp, remark_9_20_embedding_holder hp⟩⟩

/-! #### The compactness clause -/

/-- **Remark 20, the conclusion of Theorem 9.16 on `W_0^{1,p}(Ω)`, case `p < N`**: for an
arbitrary bounded open set `Ω`, `1 ≤ p < N` and `1/p* = 1/p − 1/N`, `W_0^{1,p}(Ω) ⊂ L^q(Ω)` with
compact injection for all `q ∈ [1, p*)`. The backbone's
`SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt` (which needs only `|Ω| < ∞`). -/
theorem remark_9_20_compact_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactInjectionLpZero N p q Ω :=
  ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt hb.measure_lt_top.ne hpN hp' hqp'⟩

/-- **Remark 20, the conclusion of Theorem 9.16 on `W_0^{1,p}(Ω)`, case `p = N`**: for an
arbitrary bounded open set `Ω` and `N ≥ 2`, `W_0^{1,N}(Ω) ⊂ L^q(Ω)` with compact injection for
all `q ∈ [N, +∞)`. The backbone's `SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq`. -/
theorem remark_9_20_compact_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hN : 2 ≤ N) (hp : p = (N : ℝ≥0)) (hq : p ≤ q) : IsCompactInjectionLpZero N p q Ω := by
  subst hp
  have : Fact (1 ≤ (N : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq hb.measure_lt_top.ne hN hq⟩

/-- **The injection `W_0^{1,p}(Ω) ⊂ C(Ω̄)`, `u ↦ ũ|_{Ω̄}`**, for a bounded open `Ω` and
`N < p < ∞`: the restriction to the compact set `Ω̄` of the continuous representative of
Remark 20 (`remark_9_20_embedding_holder`), as a bounded linear map into `C(Ω̄, ℝ)` — the
backbone's `HasSobolevExtensionOn.toContinuousMapOnL` for the extension by zero. -/
noncomputable def toContinuousMapClosureZero (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : (N : ℝ≥0) < p) : sobolevZeroSpace N p Ω →L[ℝ] C(closure (Ω : Set 𝔼), ℝ) :=
  haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  (SobolevEuclideanZero.hasSobolevExtensionOn (N := N) (p := p) (Ω := Ω)).toContinuousMapOnL hp
    (closure (Ω : Set 𝔼))

/-- The injection `W_0^{1,p}(Ω) ⊂ C(Ω̄)` is the continuous representative: for every `u`,
`toContinuousMapClosureZero u` is the restriction to `Ω̄` of a continuous `ũ` with `u = ũ` a.e.
on `Ω`. -/
theorem exists_continuous_ae_eq_toContinuousMapClosureZero (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : (N : ℝ≥0) < p) (u : sobolevZeroSpace N p Ω) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧
      SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x : closure (Ω : Set 𝔼), toContinuousMapClosureZero hb hp u x = ũ x := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact ⟨_, (SobolevEuclidean.contRep hp _).continuous,
    SobolevEuclideanZero.hasSobolevExtensionOn.fn_ae_eq_toContinuousMapOnL hp
      (closure (Ω : Set 𝔼)) u, fun x ↦ rfl⟩

/-- **Remark 20, the conclusion of Theorem 9.16 on `W_0^{1,p}(Ω)`, case `p > N`**: for an
arbitrary bounded open set `Ω` and `N < p < ∞`, the injection `W_0^{1,p}(Ω) ⊂ C(Ω̄)`,
`u ↦ ũ|_{Ω̄}` (`toContinuousMapClosureZero`), is compact. The backbone's
`SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL` (Ascoli–Arzelà). -/
theorem remark_9_20_compact_gt (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : (N : ℝ≥0) < p) :
    haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
    IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL hp subset_closure

/-- **Remark 20, the conclusion of Theorem 9.16 on `W_0^{1,p}(Ω)`, "in particular
`W_0^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection"**, for an arbitrary bounded open set `Ω` and
every `1 ≤ p < ∞` and every `N` (here the case `N = 1 = p` is included: at `q = p` the
Kolmogorov–Riesz argument needs no case distinction). The backbone's
`SobolevEuclideanZero.isCompactEmbedding_toLp`. -/
theorem remark_9_20_compact_self (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    IsCompactInjectionLpZero N p p Ω :=
  ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp hb.measure_lt_top.ne⟩

/-- **Remark 20, second clause.** "Similarly, the conclusion of Theorem 9.16 is true for
`W_0^{1,p}(Ω)` with an arbitrary bounded open set `Ω`": for `1 ≤ p < ∞`, the injections
`W_0^{1,p}(Ω) ⊂ L^q(Ω)` for `q ∈ [1, p*)` if `p < N`, `W_0^{1,p}(Ω) ⊂ L^q(Ω)` for `q ∈ [p, +∞)`
if `p = N` (and `N ≥ 2`), `W_0^{1,p}(Ω) ⊂ C(Ω̄)` if `p > N`, are compact; in particular
`W_0^{1,p}(Ω) ⊂ L^p(Ω)` with compact injection for all `p` and all `N`. -/
theorem remark_9_20_compact (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → q < p' →
      IsCompactInjectionLpZero N p q Ω) ∧
    (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsCompactInjectionLpZero N p q Ω) ∧
    (∀ hp : (N : ℝ≥0) < p,
      haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
        isCompact_iff_compactSpace.1 hb.isCompact_closure
      IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap) ∧
    IsCompactInjectionLpZero N p p Ω :=
  ⟨fun _ _ _ hpN hp' hqp' ↦ remark_9_20_compact_lt hb hpN hp' hqp',
    fun hN hp _ _ hq ↦ remark_9_20_compact_eq hb hN hp hq, remark_9_20_compact_gt hb,
    remark_9_20_compact_self hb⟩

/-! #### The Sobolev inequality on `W_0^{1,p}(Ω)` -/

/-- **Remark 20, last clause.** "It can also be deduced from Theorem 9.9 that if `Ω` is an
arbitrary open set and `1 ≤ p < N`, then `‖u‖_{L^{p*}(Ω)} ≤ C(p, N) ‖∇u‖_{L^p(Ω)}` for all
`u ∈ W_0^{1,p}(Ω)`": Theorem 9.9 applied to the extension by zero `ū ∈ W^{1,p}(ℝ^N)`, whose
gradient is the zero extension of `∇u`. The backbone's
`SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq`, with the constant `N · gnsConst N p` of
Theorem 9.9. -/
theorem remark_9_20_sobolev {p' : ℝ≥0} [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u ∈ sobolevZeroSpace N p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p' (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  refine ⟨SobolevEuclidean.gnsConst N p * N, fun u hu ↦ ?_⟩
  refine (SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq hpN hp' ⟨u, hu⟩).trans ?_
  have h := sum_ofReal_norm_partialDeriv_le u
  push_cast
  rw [mul_assoc]
  exact mul_le_mul' le_rfl h

/-- **Remark 20.** The proof of Corollary 9.14 uses the extension operator, and because of this
fact one must assume that `Ω` is smooth. If `W^{1,p}(Ω)` is replaced by `W_0^{1,p}(Ω)` one can use
the canonical extension by zero outside `Ω`, which is valid for arbitrary domains `Ω`
(Proposition 9.18, (i) ⇒ (iii), uses no smoothness hypothesis on `Ω`). It follows that
(a) the conclusion of Corollary 9.14 is true for `W_0^{1,p}(Ω)` with an arbitrary open set `Ω`
(`remark_9_20_embedding`); (b) the conclusion of Theorem 9.16 is true for `W_0^{1,p}(Ω)` with an
arbitrary bounded open set `Ω` (`remark_9_20_compact`); (c) for an arbitrary open set `Ω` and
`1 ≤ p < N`, `‖u‖_{L^{p*}(Ω)} ≤ C(p, N) ‖∇u‖_{L^p(Ω)}` for all `u ∈ W_0^{1,p}(Ω)`
(`remark_9_20_sobolev`). -/
theorem remark_9_20 :
    ((∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → p ≤ q →
        q ≤ p' → IsContinuousInjectionLpZero N p q Ω) ∧
      (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
        IsContinuousInjectionLpZero N p q Ω) ∧
      ((N : ℝ≥0) < p → IsContinuousInjectionLpZero N p ⊤ Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
          ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
          SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
          (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
            |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω)
              * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
          ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
            |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
                - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
              ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p))) ∧
    (∀ hb : Bornology.IsBounded (Ω : Set 𝔼),
      (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → q < p' →
        IsCompactInjectionLpZero N p q Ω) ∧
      (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
        IsCompactInjectionLpZero N p q Ω) ∧
      (∀ hp : (N : ℝ≥0) < p,
        haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
          isCompact_iff_compactSpace.1 hb.isCompact_closure
        IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap) ∧
      IsCompactInjectionLpZero N p p Ω) ∧
    (∀ (p' : ℝ≥0) [Fact (1 ≤ (p' : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ →
      ∃ C : ℝ≥0, ∀ u ∈ sobolevZeroSpace N p Ω,
        eLpNorm (SobolevMultiIndex.fn u) p' (volume.restrict (Ω : Set 𝔼))
          ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))) :=
  ⟨remark_9_20_embedding, remark_9_20_compact, fun _ _ hpN hp' ↦ remark_9_20_sobolev hpN hp'⟩

end Remark20

/-! ### The gradient norm at `p = 2` -/

section GradientTwo

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- `∫_Ω |∇u|² = ∑ᵢ ‖∂ᵢu‖_{L²(Ω)}²` for `u ∈ H^1(Ω)`: the square of the `L²` norm of the
gradient vector is the sum of the squares of the `L²` norms of the partial derivatives. -/
theorem eLpNorm_gradient_two_sq (u : hSpace N Ω) :
    eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼)) ^ 2
      = ∑ i, eLpNorm (partialDeriv u i) 2 (volume.restrict (Ω : Set 𝔼)) ^ 2 := by
  have hg := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero
    (aestronglyMeasurable_gradient u)
  have hi : ∀ i, eLpNorm (partialDeriv u i) 2 (volume.restrict (Ω : Set 𝔼)) ^ 2
      = ∫⁻ x, ‖partialDeriv u i x‖ₑ ^ 2 ∂(volume.restrict (Ω : Set 𝔼)) := fun i ↦ by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero
      (Lp.aestronglyMeasurable (partialDeriv u i))
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using h
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at hg
  rw [hg]
  simp_rw [hi]
  rw [← lintegral_finsetSum' _ fun i _ ↦
    (Lp.aestronglyMeasurable (partialDeriv u i)).enorm.pow_const 2]
  refine lintegral_congr fun x ↦ ?_
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow, EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt,
    ENNReal.ofNNReal_finsetSum, gradient_apply]

/-- **At `p = 2` the two readings of `‖∇u‖_{L²(Ω)}` agree**: the Euclidean reading
`(∫_Ω |∇u|²)^{1/2}` of §9.1 (`eLpNorm (gradient u) 2`) is the backbone's `ℓ²` reading
`(∑ᵢ ‖∂ᵢu‖₂²)^{1/2}` (`SobolevMultiIndex.gradNorm`). -/
theorem gradNorm_eq_toReal_eLpNorm_gradient_two (u : hSpace N Ω) :
    SobolevMultiIndex.gradNorm u
      = (eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼))).toReal := by
  rw [Elliptic.gradNorm_eq_sqrt]
  have h := congrArg ENNReal.toReal (eLpNorm_gradient_two_sq u)
  rw [ENNReal.toReal_pow, ENNReal.toReal_sum fun i _ ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)]
    at h
  simp only [ENNReal.toReal_pow, ← Lp.norm_def, partialDeriv] at h
  rw [← h, Real.sqrt_sq ENNReal.toReal_nonneg]

end GradientTwo

/-! ### Corollary 9.19: Poincaré's inequality -/

section Poincare

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Corollary 9.19 (Poincaré's inequality).** Suppose that `1 ≤ p < ∞` and `Ω` is a bounded
open set. Then there exists a constant `C` (depending on `Ω` and `p`) such that
`‖u‖_{L^p(Ω)} ≤ C ‖∇u‖_{L^p(Ω)}` for all `u ∈ W_0^{1,p}(Ω)`. The backbone's
`SobolevEuclideanZero.eLpNorm_fn_le_of_isBounded` (`C = 2R` for `Ω ⊆ B(0, R)`, indeed with
`‖∂_N u‖_p` in place of `‖∇u‖_p`, by the fundamental theorem of calculus and Fubini along the
last coordinate; the book gives no proof here). -/
theorem corollary_9_19 (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ ENNReal.ofReal C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  refine ⟨2 * max R 0, by positivity, fun u hu ↦ ?_⟩
  refine (SobolevEuclideanZero.eLpNorm_fn_le_of_isBounded hp' (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0))) ⟨u, hu⟩).trans ?_
  exact mul_le_mul' le_rfl (eLpNorm_partialDeriv_le u (Fin.last d))

/-- **Corollary 9.19, "in particular", in the backbone's reading.** For `Ω` bounded and
`1 ≤ p < ∞`, the `W^{1,p}` norm of `u ∈ W_0^{1,p}(Ω)` is bounded by a constant times its
`ℓ^p` gradient norm `SobolevMultiIndex.gradNorm u = (∑ᵢ ‖∂ᵢu‖_p^p)^{1/p}`, which is therefore a
norm on `W_0^{1,p}(Ω)` (its other axioms hold on all of `W^{1,p}(Ω)`,
`SobolevMultiIndex.gradNorm_add_le`, `gradNorm_smul`) equivalent to `‖u‖`
(`SobolevMultiIndex.gradNorm_le_norm` for the other bound). The backbone's
`SobolevEuclideanZero.norm_le_gradNorm`. -/
theorem corollary_9_19_gradNorm (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, ∀ u ∈ sobolevZeroSpace (d + 1) p Ω, ‖u‖ ≤ C * SobolevMultiIndex.gradNorm u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  exact ⟨_, fun u hu ↦ SobolevEuclideanZero.norm_le_gradNorm hp' (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0))) ⟨u, hu⟩⟩

/-- **Corollary 9.19, "in particular, the expression `‖∇u‖_{L^p(Ω)}` is a norm on `W_0^{1,p}(Ω)`,
and it is equivalent to the norm `‖u‖_{W^{1,p}}`."** For `Ω` bounded and `1 ≤ p < ∞` there are
constants `0 < C₁` and `C₂` with `C₁ ‖u‖_{W^{1,p}} ≤ ‖∇u‖_{L^p(Ω)} ≤ C₂ ‖u‖_{W^{1,p}}` for all
`u ∈ W_0^{1,p}(Ω)`, the book's norm `bookNorm` and the Euclidean reading `eLpNorm (gradient u) p`
of `‖∇u‖_p`; in particular `‖∇u‖_{L^p(Ω)} = 0` forces `u = 0` (`corollary_9_19_norm_eq_zero`).
From `corollary_9_19_gradNorm` through the comparison of the two gradient norms
(`gradNorm_le_eLpNorm_gradient`, `toReal_eLpNorm_gradient_le_gradNorm`) and of the two
`W^{1,p}` norms (`bookNorm_equiv`). -/
theorem corollary_9_19_norm (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      C₁ * bookNorm u ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal ≤ C₂ * bookNorm u := by
  obtain ⟨K, hK⟩ := corollary_9_19_gradNorm hp' hb
  set M : ℝ := ((d + 1 : ℕ) + 1) * max K 1 * (d + 1 : ℕ) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M⁻¹, ((d + 1 : ℕ) : ℝ), inv_pos.2 hM0, fun u hu ↦ ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ hM0, hM]
    have h1 := (bookNorm_equiv u).2
    have h2 := hK u hu
    have h3 := gradNorm_le_eLpNorm_gradient u
    have h4 := SobolevMultiIndex.gradNorm_nonneg u
    have h5 : 0 ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    have hK1 : K ≤ max K 1 := le_max_left _ _
    have hK0 : 0 ≤ max K 1 := le_max_of_le_right zero_le_one
    calc bookNorm u ≤ ((d + 1 : ℕ) + 1) * ‖u‖ := h1
      _ ≤ ((d + 1 : ℕ) + 1) * (max K 1 * SobolevMultiIndex.gradNorm u) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right hK1 h4)
      _ ≤ ((d + 1 : ℕ) + 1) * (max K 1 * ((d + 1 : ℕ)
            * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal)) := by
          gcongr
      _ = _ := by ring
  · calc (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        ≤ (d + 1 : ℕ) * SobolevMultiIndex.gradNorm u := toReal_eLpNorm_gradient_le_gradNorm u
      _ ≤ (d + 1 : ℕ) * bookNorm u := by
          gcongr
          exact (SobolevMultiIndex.gradNorm_le_norm u).trans (bookNorm_equiv u).1

/-- **`‖∇u‖_{L^p(Ω)}` is a norm on `W_0^{1,p}(Ω)`, the definiteness**: for `Ω` bounded and
`1 ≤ p < ∞`, `u ∈ W_0^{1,p}(Ω)` with `‖∇u‖_{L^p(Ω)} = 0` is `0`. -/
theorem corollary_9_19_norm_eq_zero (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {u : sobolevSpace (d + 1) p Ω} (hu : u ∈ sobolevZeroSpace (d + 1) p Ω)
    (h : eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) = 0) : u = 0 := by
  obtain ⟨C₁, C₂, hC₁, hC⟩ := corollary_9_19_norm hp' hb
  have h1 := (hC u hu).1
  rw [h, ENNReal.toReal_zero] at h1
  have h2 : bookNorm u ≤ 0 := by nlinarith [bookNorm_nonneg u]
  exact (bookNorm_eq_zero_iff u).1 (le_antisymm h2 (bookNorm_nonneg u))

/-- **Corollary 9.19, last clause: the scalar product of `H_0^1(Ω)`.** For `Ω` bounded, on
`H_0^1(Ω)` the expression `∑ᵢ ∫_Ω ∂ᵢu ∂ᵢv` — the Dirichlet form `Elliptic.dirichletForm Ω`, a
bounded bilinear form on `H^1(Ω)` — is a scalar product (symmetric, and positive definite on
`H_0^1(Ω)`) that induces the norm `‖∇u‖_{L²(Ω)}` (`√(∑ᵢ ∫ (∂ᵢu)²) = ‖∇u‖_{L²}`), and it is
equivalent to the norm `‖u‖_{H^1}`. The positivity and the equivalence are Poincaré's
inequality (`SobolevEuclideanZero.norm_le_gradNorm` at `p = 2`) and
`Elliptic.dirichletForm_self_eq_gradNorm_sq`. -/
theorem corollary_9_19_inner (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ u v : hSpace (d + 1) Ω, Elliptic.dirichletForm Ω u v
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv u i x * partialDeriv v i x) ∧
    (∀ u v : hSpace (d + 1) Ω, Elliptic.dirichletForm Ω u v = Elliptic.dirichletForm Ω v u) ∧
    (∀ u : hSpace (d + 1) Ω, √(Elliptic.dirichletForm Ω u u)
        = (eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼))).toReal) ∧
    (∀ u ∈ hZeroSpace (d + 1) Ω, u ≠ 0 → 0 < Elliptic.dirichletForm Ω u u) ∧
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ u ∈ hZeroSpace (d + 1) Ω,
      C₁ * ‖u‖ ≤ √(Elliptic.dirichletForm Ω u u) ∧
        √(Elliptic.dirichletForm Ω u u) ≤ C₂ * ‖u‖ := by
  have hsq : ∀ u : hSpace (d + 1) Ω,
      √(Elliptic.dirichletForm Ω u u) = SobolevMultiIndex.gradNorm u := fun u ↦ by
    rw [Elliptic.dirichletForm_self_eq_gradNorm_sq,
      Real.sqrt_sq (SobolevMultiIndex.gradNorm_nonneg u)]
  obtain ⟨K, hK⟩ := corollary_9_19_gradNorm (p := 2) (by simp) hb
  have hK0 : 0 < max K 1 := lt_max_of_lt_right zero_lt_one
  refine ⟨fun u v ↦ ?_, fun u v ↦ ?_, fun u ↦ ?_, fun u hu hu0 ↦ ?_,
    (max K 1)⁻¹, 1, inv_pos.2 hK0, fun u hu ↦ ⟨?_, ?_⟩⟩
  · rw [Elliptic.dirichletForm_apply_inner]
    exact Finset.sum_congr rfl fun i _ ↦ Elliptic.inner_eq_integral Ω _ _
  · have h := Elliptic.dirichletForm_isHermitian Ω u v
    simpa using h
  · rw [hsq, gradNorm_eq_toReal_eLpNorm_gradient_two]
  · rw [Elliptic.dirichletForm_self_eq_gradNorm_sq]
    have h1 := hK u hu
    have h2 : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have h3 : 0 < SobolevMultiIndex.gradNorm u := by
      by_contra h
      push Not at h
      have := le_antisymm h (SobolevMultiIndex.gradNorm_nonneg u)
      rw [this, mul_zero] at h1
      exact absurd (h1.trans_lt' h2) (lt_irrefl _)
    positivity
  · rw [hsq, inv_mul_le_iff₀ hK0]
    exact (hK u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (SobolevMultiIndex.gradNorm_nonneg u))
  · rw [hsq, one_mul]
    exact SobolevMultiIndex.gradNorm_le_norm u

/-- **Remark 21, second clause: Poincaré's inequality "if `Ω` has a bounded projection on some
axis"**, stated for the last coordinate axis: for `1 ≤ p < ∞` and `Ω ⊆ {a < x_N < b}`,
`‖u‖_{L^p(Ω)} ≤ (b − a) ‖∇u‖_{L^p(Ω)}` for all `u ∈ W_0^{1,p}(Ω)`. The backbone's
`SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab` (fundamental theorem of calculus and Fubini
along `x_N`; the other axes follow by relabelling the coordinates). -/
theorem remark_9_21_projection (hp' : p ≠ ⊤) {a b : ℝ}
    (hΩ : ∀ x ∈ (Ω : Set 𝔼), a < x (Fin.last d) ∧ x (Fin.last d) < b) :
    ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ ENNReal.ofReal (b - a) * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  intro u hu
  rcases (Ω : Set 𝔼).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp only [h, Measure.restrict_empty, eLpNorm_measure_zero, zero_le]
  · have hab : a ≤ b := ((hΩ x hx).1.trans (hΩ x hx).2).le
    refine (SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab hp' hab
      (fun y hy ↦ hΩ y hy) ⟨u, hu⟩).trans ?_
    exact mul_le_mul' le_rfl (eLpNorm_partialDeriv_le u (Fin.last d))

end Poincare

section Remark21

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Remark 21, first clause: "Poincaré's inequality remains true if `Ω` has finite
measure"**, for `N ≥ 2` and `1 ≤ p < ∞`: there is `C < ∞` with
`‖u‖_{L^p(Ω)} ≤ C ‖∇u‖_{L^p(Ω)}` for all `u ∈ W_0^{1,p}(Ω)`. The backbone's
`SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top`, through the Sobolev inequality
of Remark 20 (`W_0^{1,r}(Ω) ⊂ L^{r*}(Ω)` for an `r ≤ p` with `r < N`, `r* ≥ p`) and Hölder's
inequality on the finite measure; the statement is false for `N = 1` (an unbounded open set of
finite measure), which is why `N ≥ 2` is assumed. -/
theorem remark_9_21_measure (hp' : p ≠ ⊤) (hN : 2 ≤ N) (hΩ : volume (Ω : Set 𝔼) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u ∈ sobolevZeroSpace N p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨C, hC, h⟩ := SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top
    (Ω := Ω) hp' hN hΩ
  refine ⟨C * N, ENNReal.mul_ne_top hC (ENNReal.natCast_ne_top N), fun u hu ↦ ?_⟩
  refine (h ⟨u, hu⟩).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have h1 := gradNorm_le_eLpNorm_gradient u
  have hfin : eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) ≠ ⊤ :=
    (memLp_gradient u).eLpNorm_ne_top
  calc ENNReal.ofReal (SobolevMultiIndex.gradNorm u)
      ≤ ENNReal.ofReal (N * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal) :=
        ENNReal.ofReal_le_ofReal h1
    _ = N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_toReal hfin]

end Remark21

section Remark21Both

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Remark 21.** Poincaré's inequality remains true if `Ω` has finite measure (for `N ≥ 2`),
and also if `Ω` has a bounded projection on some axis (here the last one): in both cases there
is `C < ∞` with `‖u‖_{L^p(Ω)} ≤ C ‖∇u‖_{L^p(Ω)}` for all `u ∈ W_0^{1,p}(Ω)`, `1 ≤ p < ∞`. -/
theorem remark_9_21 (hp' : p ≠ ⊤)
    (h : (1 ≤ d ∧ volume (Ω : Set 𝔼) ≠ ⊤) ∨
      ∃ a b : ℝ, ∀ x ∈ (Ω : Set 𝔼), a < x (Fin.last d) ∧ x (Fin.last d) < b) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  rcases h with ⟨hd, hΩ⟩ | ⟨a, b, hΩ⟩
  · exact remark_9_21_measure hp' (by omega) hΩ
  · exact ⟨ENNReal.ofReal (b - a), ENNReal.ofReal_ne_top, remark_9_21_projection hp' hΩ⟩

end Remark21Both

/-! ### Remark 22: the spaces `W_0^{m,p}(Ω)` -/

section Higher

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Remark 22: the space `W_0^{m,p}(Ω)`**, `m ≥ 1`, `1 ≤ p < ∞`, "the closure of `C_c^m(Ω)` in
`W^{m,p}(Ω)`" — the backbone's `SobolevEuclideanZero N m p Ω`, the closure of the test
functions, the same closure by Lemma 9.5 at order `m`
(`sobolevZeroSpaceHigher_eq_closure_contDiff`). The remark's "roughly, `D^α u = 0` on `Γ` for
`|α| ≤ m − 1`" is heuristic, and its distinction between `W_0^{m,p}(Ω)` and
`W^{m,p}(Ω) ∩ W_0^{1,p}(Ω)` for `m ≥ 2` is not restated. -/
noncomputable abbrev sobolevZeroSpaceHigher (N m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Submodule ℝ (sobolevSpaceHigher N m p Ω) :=
  SobolevEuclideanZero N m p Ω

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- `W_0^{1,p}(Ω)` is the case `m = 1` of `W_0^{m,p}(Ω)`. -/
theorem sobolevZeroSpaceHigher_one :
    sobolevZeroSpaceHigher N 1 p Ω = sobolevZeroSpace N p Ω :=
  rfl

/-- **Remark 22, the Definition.** `W_0^{m,p}(Ω)` is the closure in `W^{m,p}(Ω)` of the `C^m`
functions with compact support in `Ω`, `1 ≤ p < ∞`: as in Remark 18, the closure of `C_c^m(Ω)`
is the closure of the test functions (`⊆` by Lemma 9.5 at order `m`,
`SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset`; `⊇` since a test function is a
`C^m` function with compact support in `Ω`). -/
theorem sobolevZeroSpaceHigher_eq_closure_contDiff (hp' : p ≠ ⊤) {m : ℕ} :
    closure {u : sobolevSpaceHigher N m p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ m v ∧ HasCompactSupport v ∧
        tsupport v ⊆ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v}
      = (sobolevZeroSpaceHigher N m p Ω : Set (sobolevSpaceHigher N m p Ω)) := by
  apply subset_antisymm
  · refine closure_minimal ?_ SobolevMultiIndexZero.isClosed
    rintro u ⟨v, hv, hvc, hvΩ, hu⟩
    exact SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu
  · rw [show (sobolevZeroSpaceHigher N m p Ω : Set (sobolevSpaceHigher N m p Ω))
        = closure (SobolevMultiIndex.testFunctions ℝ 𝔟 m p Ω volume :
          Set (sobolevSpaceHigher N m p Ω)) from Submodule.topologicalClosure_coe _]
    refine closure_mono ?_
    rintro u ⟨φ, hφ⟩
    exact ⟨φ, φ.contDiff.of_le (by simp), φ.hasCompactSupport, φ.tsupport_subset, hφ⟩

end Higher

/-! ### The dual space of `W_0^{1,p}(Ω)` -/

section Dual

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, as a `Basis`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Notation: the space `W^{−1,p'}(Ω)`**, the dual space of `W_0^{1,p}(Ω)`, `1 ≤ p < ∞`. -/
noncomputable abbrev dualSpace (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  StrongDual ℝ (sobolevZeroSpace N p Ω)

/-- **Notation: the space `H^{−1}(Ω)`**, the dual of `H_0^1(Ω)`. "The dual of `L^2(Ω)` is
identified with `L^2(Ω)`, but we do not identify `H_0^1(Ω)` with its dual." -/
noncomputable abbrev hMinusOne (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  dualSpace N 2 Ω

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The inclusions `H_0^1(Ω) ⊂ L^2(Ω) ⊂ H^{−1}(Ω)`, "where these injections are continuous
and dense"**: the bounded linear maps `H_0^1(Ω) → L^2(Ω)`, `u ↦ u` (the backbone's
`SobolevMultiIndexZero.fnL`), and `L^2(Ω) → H^{−1}(Ω)`, `f ↦ (v ↦ ∫_Ω f v)` (the backbone's
`SobolevEuclideanZero.toDualL2`), are injective with dense range. The backbone's
`SobolevEuclideanZero.gelfandTriple`. -/
theorem dual_inclusions :
    (∀ u : hZeroSpace N Ω, (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u : 𝔼 → ℝ)
        = SobolevMultiIndex.fn (u : hSpace N Ω)) ∧
      Function.Injective (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) ∧
      DenseRange (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) ∧
    (∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (v : hZeroSpace N Ω),
        (SobolevEuclideanZero.toDualL2 N Ω f : hMinusOne N Ω) v
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v : hSpace N Ω) x) ∧
      Function.Injective (SobolevEuclideanZero.toDualL2 N Ω) ∧
      DenseRange (SobolevEuclideanZero.toDualL2 N Ω) :=
  ⟨fun u ↦ SobolevMultiIndexZero.fnL_apply u, SobolevEuclideanZero.gelfandTriple.1,
    SobolevEuclideanZero.gelfandTriple.2.1, fun f v ↦ SobolevEuclideanZero.toDualL2_apply f v,
    SobolevEuclideanZero.gelfandTriple.2.2.1, SobolevEuclideanZero.gelfandTriple.2.2.2⟩

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Proposition 9.20.** Let `F ∈ W^{−1,p'}(Ω)`, `1 ≤ p < ∞` (`p'` the conjugate exponent).
Then there exist functions `f_0, f_1, …, f_N ∈ L^{p'}(Ω)` such that
`⟨F, v⟩ = ∫_Ω f_0 v + ∑ᵢ ∫_Ω f_i ∂v/∂x_i` for all `v ∈ W_0^{1,p}(Ω)`, and `‖f_i‖_{p'} ≤ ‖F‖` for
every `i` (the book's `‖F‖ = max_i ‖f_i‖_{p'}` refers to its norm `∑ ‖h_i‖_p` on `(L^p)^{N+1}`;
for the `ℓ^p`-sum norm of the type the identity reads differently and only the bound is stated).
The backbone's `SobolevEuclideanZero.exists_dual_repr` ("adapt the proof of Proposition 8.14":
Hahn–Banach on the `ℓ^p` product of `N + 1` copies of `L^p(Ω)` and the Riesz representation on
each factor), the sum over multi-indices split into the index `0` and the `N` unit indices. -/
theorem proposition_9_20 [p.HolderConjugate q] (hp' : p ≠ ⊤) (F : dualSpace N p Ω) :
    ∃ (f₀ : Lp ℝ q (volume.restrict (Ω : Set 𝔼)))
      (f : Fin N → Lp ℝ q (volume.restrict (Ω : Set 𝔼))),
      (∀ v : sobolevZeroSpace N p Ω,
        F v = (∫ x in (Ω : Set 𝔼), f₀ x * SobolevMultiIndex.fn (v : sobolevSpace N p Ω) x)
          + ∑ i, ∫ x in (Ω : Set 𝔼), f i x * partialDeriv (v : sobolevSpace N p Ω) i x) ∧
      ‖f₀‖ ≤ ‖F‖ ∧ ∀ i, ‖f i‖ ≤ ‖F‖ := by
  obtain ⟨f, hf, hfn⟩ := SobolevEuclideanZero.exists_dual_repr (q := q) hp' F
  refine ⟨f 0, fun i ↦ f (MultiIndexLE.single i), fun v ↦ ?_, hfn 0, fun i ↦ hfn _⟩
  rw [hf v, MultiIndexLE.sum_univ_one]
  rfl

end Dual

section DualBounded

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Proposition 9.20, last sentence: "if `Ω` is bounded we can take `f_0 = 0`"**, with a
bound `‖f_i‖_{p'} ≤ C ‖F‖` uniform in `F` (the constant of Poincaré's inequality, through
which the gradient `v ↦ ∇v` is bounded below on `W_0^{1,p}(Ω)`). The backbone's
`SobolevEuclideanZero.exists_dual_repr_of_isBounded`. -/
theorem proposition_9_20_bounded [p.HolderConjugate q] (hp' : p ≠ ⊤)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, ∀ F : dualSpace (d + 1) p Ω, ∃ f : Fin (d + 1) → Lp ℝ q (volume.restrict (Ω : Set 𝔼)),
      (∀ v : sobolevZeroSpace (d + 1) p Ω,
        F v = ∑ i, ∫ x in (Ω : Set 𝔼), f i x * partialDeriv (v : sobolevSpace (d + 1) p Ω) i x) ∧
      ∀ i, ‖f i‖ ≤ C * ‖F‖ := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  refine ⟨(1 + (2 * max R 0) ^ p.toReal) ^ (1 / p.toReal), fun F ↦ ?_⟩
  obtain ⟨f, hf, hfn⟩ := SobolevEuclideanZero.exists_dual_repr_of_isBounded (q := q) hp'
    (le_max_right R 0) (hR.trans (ball_subset_ball (le_max_left R 0))) F
  exact ⟨f, hf, hfn⟩

end DualBounded

end Brezis.Chapter09
