import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Distribution.TestFunction
import Numlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Uniform approximation by test functions

A function `f` continuous on the closure of an open set `Ω ⊆ E` (`E` finite-dimensional),
vanishing on `frontier Ω` and tending to `0` at infinity along `Ω` — the class `C(Ω̄)` with
`f = 0` on `Γ` of [brezis2011functional] Corollary 10.5 and its footnote 6 — is the uniform limit
on `Ω` of test functions `φ n ∈ 𝓓(Ω, ℝ)` (`exists_testFunction_tendsto_of_continuousOn`). The
steps: `f` is small off a compact `K ⊆ Ω` (`exists_isCompact_subset_abs_lt`); a smooth cut-off
`η` equal to `1` on `K` and supported in `Ω` makes `η f` (extended by `0`) continuous with
compact support in `Ω` (`continuous_indicator_mul_of_tsupport_subset`); and a mollification
approximates such a function uniformly (`exists_testFunction_abs_sub_le_of_hasCompactSupport`).

For a bounded `Ω` of a proper space the condition at infinity is void, the filter
`cocompact E ⊓ 𝓟 Ω` being trivial (`Bornology.IsBounded.cocompact_inf_principal_eq_bot`).

## References

[brezis2011functional], Corollary 10.5 (the "easily established" approximation `u_{0n} → u₀`).
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions Topology

noncomputable section

/-- **The filter "at infinity along a bounded set" is trivial** in a proper space:
`cocompact E ⊓ 𝓟 s = ⊥` for a bounded `s`, since `s` and the complement of the compact
`closure s` are disjoint. -/
theorem Bornology.IsBounded.cocompact_inf_principal_eq_bot {E : Type*} [PseudoMetricSpace E]
    [ProperSpace E] {s : Set E} (hs : Bornology.IsBounded s) : cocompact E ⊓ 𝓟 s = ⊥ :=
  Filter.inf_eq_bot_iff.2 ⟨(closure s)ᶜ, hs.isCompact_closure.compl_mem_cocompact, s,
    mem_principal_self _, Set.eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.1 (subset_closure hx.2)⟩

/-- On a bounded set of a proper space every function tends to `0` at infinity along the set:
the filter `cocompact E ⊓ 𝓟 s` is trivial. -/
theorem Bornology.IsBounded.tendsto_cocompact_inf_principal {E F : Type*} [PseudoMetricSpace E]
    [ProperSpace E] [TopologicalSpace F] {s : Set E} (hs : Bornology.IsBounded s) (f : E → F)
    (y : F) : Tendsto f (cocompact E ⊓ 𝓟 s) (𝓝 y) := by
  rw [hs.cocompact_inf_principal_eq_bot]
  exact tendsto_bot

section Approximation

variable {E : Type*} [NormedAddCommGroup E]

/-- **A continuous function on `closure Ω` vanishing on `frontier Ω` and at infinity is small off
a compact subset of `Ω`**: for every `ε > 0` there is a compact `K ⊆ Ω` with `|f| < ε` on
`Ω \ K`. The tail is the hypothesis at infinity; near the boundary, `{|f| < ε}` is relatively
open in `closure Ω` and contains `frontier Ω`, so its complement in a compact set is a compact
subset of `Ω`. -/
theorem exists_isCompact_subset_abs_lt {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ Ω \ K, |f x| < ε := by
  -- the tail
  have htail := (Metric.tendsto_nhds.1 hft) ε hε
  rw [eventually_inf_principal, hasBasis_cocompact.eventually_iff] at htail
  obtain ⟨C, hC, hCf⟩ := htail
  -- the relatively open set `{|f| < ε}`
  obtain ⟨V, hV, hVf⟩ := continuousOn_iff'.1 hf (ball 0 ε) isOpen_ball
  refine ⟨(C ∩ closure Ω) \ V, (hC.inter_right isClosed_closure).diff hV, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · -- `K ⊆ Ω`: a point of `closure Ω` outside `V` is not on the frontier
    obtain ⟨⟨-, hxc⟩, hxV⟩ := hx
    by_contra hxΩ
    have hxΓ : x ∈ frontier Ω := by
      rw [frontier, hΩ.interior_eq]
      exact ⟨hxc, hxΩ⟩
    have : x ∈ f ⁻¹' ball 0 ε ∩ closure Ω := by
      refine ⟨?_, hxc⟩
      simp [hf0 x hxΓ, hε]
    rw [hVf] at this
    exact hxV this.1
  · obtain ⟨hxΩ, hxK⟩ := hx
    by_cases hxC : x ∈ C
    · have hxV : x ∈ V := by
        by_contra hxV
        exact hxK ⟨⟨hxC, subset_closure hxΩ⟩, hxV⟩
      have : x ∈ V ∩ closure Ω := ⟨hxV, subset_closure hxΩ⟩
      rw [← hVf] at this
      simpa [dist_eq_norm] using this.1
    · simpa [dist_eq_norm] using hCf hxC hxΩ

/-- **The cut-off of `f` to a compact subset of `Ω` is continuous**: for `η` continuous with
`tsupport η ⊆ Ω` and `f` continuous on `Ω`, the function equal to `η f` on `Ω` and to `0`
outside is continuous on the whole space. -/
theorem continuous_indicator_mul_of_tsupport_subset {Ω : Set E} (hΩ : IsOpen Ω) {f η : E → ℝ}
    (hf : ContinuousOn f Ω) (hη : Continuous η) (hηΩ : tsupport η ⊆ Ω) :
    Continuous (Ω.indicator fun x ↦ η x * f x) := by
  refine continuous_of_cover_nhds (s := fun b : Bool ↦ if b then Ω else (tsupport η)ᶜ)
    (fun x ↦ ?_) (fun b ↦ ?_)
  · by_cases hx : x ∈ Ω
    · exact ⟨true, by simpa using hΩ.mem_nhds hx⟩
    · refine ⟨false, by simpa using (isClosed_tsupport η).isOpen_compl.mem_nhds fun h ↦ hx (hηΩ h)⟩
  · cases b with
    | true =>
      change ContinuousOn _ Ω
      exact (hη.continuousOn.mul hf).congr fun x hx ↦ by simp [indicator_of_mem hx]
    | false =>
      change ContinuousOn _ (tsupport η)ᶜ
      refine (continuousOn_const (c := (0 : ℝ))).congr fun x hx ↦ ?_
      by_cases hxΩ : x ∈ Ω
      · simp [indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport hx]
      · simp [indicator_of_notMem hxΩ]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Mollification approximates a continuous compactly supported function uniformly** by test
functions of `Ω`: for `g` continuous with `tsupport g ⊆ Ω` compact and `ε > 0` there is
`φ ∈ 𝓓(Ω, ℝ)` with `|φ − g| ≤ ε` everywhere. The mollification `ρ_δ ⋆ g` at a scale `δ` below
the distance from `tsupport g` to `Ωᶜ` and below the modulus of uniform continuity of `g` at
`ε` does it (`ContDiffBump.dist_normed_convolution_le`). -/
theorem exists_testFunction_abs_sub_le_of_hasCompactSupport {Ω : Opens E} {g : E → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) {ε : ℝ}
    (hε : 0 < ε) : ∃ φ : 𝓓(Ω, ℝ), ∀ x, |φ x - g x| ≤ ε := by
  obtain ⟨δ₁, hδ₁, hδ₁Ω⟩ := hgc.exists_cthickening_subset_open Ω.isOpen hgΩ
  obtain ⟨δ₂, hδ₂, hδ₂g⟩ :=
    Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hg) ε hε
  set δ : ℝ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let μ : Measure E := Measure.addHaar
  set ψ : E → ℝ := ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g with hψ
  have hψs : ContDiff ℝ ∞ ψ :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _ ρ.contDiff_normed
      hg.locallyIntegrable
  have hψc : HasCompactSupport ψ := ρ.hasCompactSupport_normed.convolution _ hgc
  have hψΩ : tsupport ψ ⊆ Ω := by
    refine (closure_mono (support_convolution_subset _)).trans ?_
    refine (closure_minimal ?_ isClosed_cthickening).trans hδ₁Ω
    rintro _ ⟨y, hy, z, hz, rfl⟩
    rw [ρ.support_normed_eq] at hy
    refine mem_cthickening_of_dist_le (y + z) z δ₁ _ (subset_closure hz) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (mem_ball_zero_iff.1 hy).le.trans (min_le_left _ _)
  refine ⟨⟨ψ, hψs, hψc, hψΩ⟩, fun x ↦ ?_⟩
  rw [← Real.dist_eq]
  refine ρ.dist_normed_convolution_le hg.aestronglyMeasurable fun y hy ↦ (hδ₂g ?_).le
  exact (mem_ball.1 hy).trans_le (min_le_right _ _)

/-- **Uniform approximation of continuous data vanishing on the boundary by test functions**
(the approximation [brezis2011functional] calls "easily established" in the proof of
Corollary 10.5): if `f` is continuous on `closure Ω`, vanishes on `frontier Ω` and tends to `0`
at infinity along `Ω` (automatic for bounded `Ω`), then for every `ε > 0` there is a test
function `φ ∈ 𝓓(Ω, ℝ)` with `|φ − f| ≤ ε` on `Ω`. Proof: `|f| ≤ ε/2` off a compact `K ⊆ Ω`
(`exists_isCompact_subset_abs_lt`); a smooth cut-off `η`, equal to `1` on `K` and supported in
`Ω`, makes `η f` (extended by `0`) continuous with compact support in `Ω` and `ε/2`-close to `f`
on `Ω`; a mollification of it is `ε/2`-close uniformly
(`exists_testFunction_abs_sub_le_of_hasCompactSupport`). -/
theorem exists_testFunction_abs_sub_le {Ω : Opens E} {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, ℝ), ∀ x ∈ Ω, |φ x - f x| ≤ ε := by
  obtain ⟨K, hK, hKΩ, hKf⟩ := exists_isCompact_subset_abs_lt Ω.isOpen hf hf0 hft (half_pos hε)
  obtain ⟨η, hη, hηc, hηΩ, hη1, hη01⟩ :=
    exists_contDiff_one_on_of_isCompact_of_isOpen hK Ω.isOpen hKΩ
  set g : E → ℝ := (Ω : Set E).indicator fun x ↦ η x * f x with hg
  have hsupp : Function.support g ⊆ Function.support η := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h
    apply hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · simp [hg, indicator_of_mem hxΩ, h]
    · simp [hg, indicator_of_notMem hxΩ]
  have hgc : Continuous g :=
    continuous_indicator_mul_of_tsupport_subset Ω.isOpen (hf.mono subset_closure) hη.continuous
      hηΩ
  have hgs : HasCompactSupport g := hηc.mono hsupp
  have hgΩ : tsupport g ⊆ Ω := (closure_mono hsupp).trans hηΩ
  obtain ⟨φ, hφ⟩ := exists_testFunction_abs_sub_le_of_hasCompactSupport hgc hgs hgΩ (half_pos hε)
  refine ⟨φ, fun x hx ↦ ?_⟩
  have hgf : |g x - f x| ≤ ε / 2 := by
    simp only [hg, indicator_of_mem hx]
    by_cases hxK : x ∈ K
    · simp [hη1 x hxK, (half_pos hε).le]
    · have h2 := hKf x ⟨hx, hxK⟩
      rw [show η x * f x - f x = (η x - 1) * f x by ring, abs_mul]
      have h1 : |η x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hη01 x).1, (hη01 x).2]
      calc |η x - 1| * |f x| ≤ 1 * (ε / 2) := mul_le_mul h1 h2.le (abs_nonneg _) zero_le_one
        _ = ε / 2 := one_mul _
  calc |φ x - f x| = |(φ x - g x) + (g x - f x)| := by ring_nf
    _ ≤ |φ x - g x| + |g x - f x| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hφ x) hgf
    _ = ε := add_halves ε

/-- **A sequence of test functions converging uniformly on `Ω` to continuous data vanishing on
the boundary** ([brezis2011functional], proof of Corollary 10.5, the approximants `u_{0n}`): if
`f` is continuous on `closure Ω`, vanishes on `frontier Ω` and tends to `0` at infinity along `Ω`
(footnote 6; automatic for bounded `Ω`), there are `φ n ∈ 𝓓(Ω, ℝ)` with `φ n → f` uniformly on
`Ω` (`exists_testFunction_abs_sub_le` at `ε = 1/(n+1)`). The book also asks `φ n → f` in
`L²(Ω)`; Corollary 10.5 does not need it, the semigroup being an `L^∞`-contraction
(`Heat.IsSolution.eLpNorm_top_le`). -/
theorem exists_testFunction_tendsto_of_continuousOn {Ω : Opens E} {f : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hf0 : ∀ x ∈ frontier Ω, f x = 0)
    (hft : Tendsto f (cocompact E ⊓ 𝓟 Ω) (𝓝 0)) :
    ∃ φ : ℕ → 𝓓(Ω, ℝ), TendstoUniformlyOn (fun n x ↦ φ n x) f atTop Ω := by
  have h : ∀ n : ℕ, ∃ φ : 𝓓(Ω, ℝ), ∀ x ∈ Ω, |φ x - f x| ≤ 1 / (n + 1) := fun n ↦
    exists_testFunction_abs_sub_le hf hf0 hft (by positivity)
  choose φ hφ using h
  refine ⟨φ, Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop n₀] with n hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  refine (hφ n x hx).trans_lt (lt_of_le_of_lt ?_ hn₀)
  gcongr

end Approximation
