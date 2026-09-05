import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Atkinson–Han §1.2: normed spaces

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §1.2: normed spaces, convergence, equivalence of norms, Banach
spaces, the completion of a normed space, and the two facts from measure theory (§1.2.3) that the
book records for later use.

The definitions of the section — norm, seminorm, ball, open and closed set, convergence, dense
subset, Schauder basis, Cauchy sequence, completeness — are Mathlib's `Norm`, `Seminorm`,
`Metric.ball`, `IsOpen`, `IsClosed`, `Filter.Tendsto`, `Dense`, `CauchySeq` and `CompleteSpace`,
and are not restated.

## Main results

* `proposition_1_2_10` — the norm is a continuous function, in the sequential form of the book.
* `theorem_1_2_14` — any two norms on a finite-dimensional space are equivalent.
* `proposition_1_2_23` — a Cauchy sequence with a convergent subsequence converges.
* `theorem_1_2_25`, `theorem_1_2_25_uniqueness` — the completion of a normed space, and its
  uniqueness up to a linear isometric isomorphism fixing the embedded copy of `V`.
* `theorem_1_2_26` — the Lebesgue dominated convergence theorem.
* `theorem_1_2_27` — Fubini's theorem.

## Conventions

Theorem 1.2.14 is stated in the only shape Lean allows. The book quantifies over two norms on one
linear space; a Lean type carries one norm, so the statement is about two normed types `V` and `W`
and a linear equivalence `e : V ≃ₗ[𝕜] W` between them, the two norms being `‖v‖` and `‖e v‖`.

Theorems 1.2.26 and 1.2.27 are stated over an arbitrary measure space rather than over an open set
of `ℝ^d`, which is how Mathlib has them and how the book uses them.

## Not formalized here

The examples of the section (1.2.2 the `ℓᵖ` and `Lᵖ` norms, 1.2.16–1.2.22 the classical Banach
spaces, 1.2.28 the Sobolev spaces) are illustrations; the Sobolev ones are out of scope for the
whole project.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open Filter Topology MeasureTheory

namespace AtkinsonHan.Ch01

section Normed

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Proposition 1.2.10.** The norm is a continuous function: if `uₙ → u` then `‖uₙ‖ → ‖u‖`. The
book's proof is the backward triangle inequality (1.2.5), `|‖u‖ - ‖v‖| ≤ ‖u - v‖`, which is
Mathlib's `abs_norm_sub_norm_le`. -/
theorem proposition_1_2_10 {u : ℕ → V} {v : V} (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖v‖) :=
  h.norm

/-- **Theorem 1.2.14.** On a finite-dimensional linear space any two norms are equivalent: for a
linear equivalence `e : V ≃ₗ[𝕜] W` between normed spaces with `V` finite-dimensional there are
`c₁, c₂ > 0` with `c₁ ‖v‖ ≤ ‖e v‖ ≤ c₂ ‖v‖`. Both bounds come from the continuity of a linear map
on a finite-dimensional space, applied to `e` and to `e.symm`. -/
theorem theorem_1_2_14 {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] (e : V ≃ₗ[𝕜] W) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ v : V, c₁ * ‖v‖ ≤ ‖e v‖ ∧ ‖e v‖ ≤ c₂ * ‖v‖ := by
  have _ : FiniteDimensional 𝕜 W := e.finiteDimensional
  set E : V ≃L[𝕜] W := e.toContinuousLinearEquiv with hE
  have hcoe : ∀ v : V, E v = e v := fun _ => rfl
  refine ⟨(‖(E.symm : W →L[𝕜] V)‖ + 1)⁻¹, by positivity, ‖(E : V →L[𝕜] W)‖ + 1, by positivity,
    fun v => ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ (by positivity), ← hcoe]
    calc ‖v‖ = ‖E.symm (E v)‖ := by simp
      _ ≤ ‖(E.symm : W →L[𝕜] V)‖ * ‖E v‖ := (E.symm : W →L[𝕜] V).le_opNorm _
      _ ≤ (‖(E.symm : W →L[𝕜] V)‖ + 1) * ‖E v‖ := by nlinarith [norm_nonneg (E v)]
  · rw [← hcoe]
    calc ‖E v‖ ≤ ‖(E : V →L[𝕜] W)‖ * ‖v‖ := (E : V →L[𝕜] W).le_opNorm _
      _ ≤ (‖(E : V →L[𝕜] W)‖ + 1) * ‖v‖ := by nlinarith [norm_nonneg v]

/-- **Proposition 1.2.23.** A Cauchy sequence with a convergent subsequence converges, to the same
limit. -/
theorem proposition_1_2_23 {u : ℕ → V} (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ) {v : V}
    (h : Tendsto (u ∘ φ) atTop (𝓝 v)) : Tendsto u atTop (𝓝 v) :=
  tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop h

/-- **Theorem 1.2.25** (existence of a completion). Every normed space `V` has a completion: the
Banach space `UniformSpace.Completion V` together with the linear isometry
`UniformSpace.Completion.toComplₗᵢ`, whose range is dense. -/
theorem theorem_1_2_25 :
    CompleteSpace (UniformSpace.Completion V) ∧
      DenseRange (UniformSpace.Completion.toComplₗᵢ : V →ₗᵢ[𝕜] UniformSpace.Completion V) :=
  ⟨inferInstance, UniformSpace.Completion.denseRange_coe⟩

/-- **Theorem 1.2.25** (uniqueness of the completion). Any Banach space `W` carrying a linear
isometry `I : V →ₗᵢ[𝕜] W` with dense range is a copy of `UniformSpace.Completion V`: there is a
surjective linear isometry from the completion onto `W` extending `I`. Two completions of `V` are
therefore isometrically isomorphic by an isomorphism fixing the embedded copy of `V`. -/
theorem theorem_1_2_25_uniqueness {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [CompleteSpace W] (I : V →ₗᵢ[𝕜] W) (hI : DenseRange I) :
    ∃ e : UniformSpace.Completion V ≃ₗᵢ[𝕜] W, ∀ v : V, e v = I v := by
  set f : UniformSpace.Completion V →L[𝕜] W := I.toContinuousLinearMap.fromCompletion with hf
  have hcoe : ∀ v : V, f v = I v := by simp [hf]
  have hnorm : ∀ x : UniformSpace.Completion V, ‖f x‖ = ‖x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
      fun v => ?_
    rw [hcoe, I.norm_map, UniformSpace.Completion.norm_coe]
  let g : UniformSpace.Completion V →ₗᵢ[𝕜] W := ⟨f.toLinearMap, hnorm⟩
  have hsub : Set.range I ⊆ Set.range g := by
    rintro w ⟨v, rfl⟩
    exact ⟨(v : UniformSpace.Completion V), hcoe v⟩
  have hsurj : Function.Surjective g :=
    Set.range_eq_univ.mp <| by
      rw [← g.isometry.isClosedEmbedding.isClosed_range.closure_eq, (hI.mono hsub).closure_eq]
  exact ⟨LinearIsometryEquiv.ofSurjective g hsurj, hcoe⟩

end Normed

section Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Theorem 1.2.26**, the Lebesgue dominated convergence theorem, in the book's statement: if
`fₙ → f` almost everywhere and `|fₙ| ≤ g` almost everywhere for an integrable `g`, then `f` is
integrable and `∫ fₙ → ∫ f`. -/
theorem theorem_1_2_26 {f : ℕ → α → ℝ} {g : α → ℝ} {bound : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hbound : Integrable bound μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgmeas : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  have hgle : ∀ᵐ x ∂μ, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_all_iff.2 hle, hlim] with x hx hxlim
    exact le_of_tendsto' hxlim.norm hx
  exact ⟨hbound.mono' hgmeas hgle,
    tendsto_integral_of_dominated_convergence bound hf hbound hle hlim⟩

/-- **Theorem 1.2.27**, Fubini's theorem: a function integrable on a product is integrable in each
variable for almost every value of the other, and its double integrals in the two orders agree. -/
theorem theorem_1_2_27 {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → ℝ} (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (f x) ν) ∧ (∀ᵐ y ∂ν, Integrable (fun x => f x y) μ) ∧
      ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  ⟨hf.prod_right_ae, hf.prod_left_ae, integral_integral_swap hf⟩

end Measure

end AtkinsonHan.Ch01
