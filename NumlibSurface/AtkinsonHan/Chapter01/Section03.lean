import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter01.Section02

/-!
# Atkinson–Han §1.3: inner product spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.3: inner product spaces, Hilbert spaces,
orthogonality, orthonormal bases and the Gram–Schmidt process.

The book's inner product is linear in its *first* slot and Mathlib's in its second, so the book's
`(u, v)` is `inner 𝕜 v u`; every statement below is written in Mathlib's convention with that
swap, as the rest of this surface does. Definitions 1.3.1, 1.3.5, 1.3.8, 1.3.9 and 1.3.10 — inner
product space, Hilbert space, orthogonality, orthogonal complement, orthonormal system — are
Mathlib's `InnerProductSpace`, `CompleteSpace`, `inner 𝕜 x y = 0`, `Submodule.orthogonal` and
`Orthonormal`, and each is restated here under the book's number.

## Main definitions

* `definition_1_3_8` — `u` and `v` are orthogonal.
* `definition_1_3_9` — the orthogonal complement of a subset.
* `definition_1_3_10`, `definition_1_3_10_basis` — an orthonormal system, and an orthonormal
  basis: an orthonormal system that is a basis in the sense of Definition 1.2.20.

## Main results

* `definition_1_3_1` — Mathlib's `InnerProductSpace` satisfies exactly the three axioms the book
  lists for an inner product.
* `definition_1_3_5` — a Hilbert space is an inner product space complete for the induced norm
  `‖v‖ = √(v, v)`, completeness being Definition 1.2.24.
* `definition_1_3_9_iff`, `definition_1_3_9_isClosed`, `definition_1_3_9_isSubspace`,
  `definition_1_3_10_iff` — the restated definitions read back as the Mathlib notions, and the
  orthogonal complement as a closed subspace.
* `example_1_3_6` — `ℂ^d`, `ℓ²` and `L²(μ)` are Hilbert spaces, with the book's inner products.
* `theorem_1_3_2` — the Cauchy–Schwarz inequality, with its equality case.
* `proposition_1_3_3` — the inner product is continuous in both arguments.
* `theorem_1_3_4` — Fréchet–von Neumann–Jordan: a norm comes from an inner product exactly when
  it satisfies the parallelogram law (1.3.3).
* `theorem_1_3_11` — Bessel's inequality, convergence of the expansion, and uniqueness of the
  coefficients.
* `theorem_1_3_12` — orthonormal basis, the generalized Parseval identity, and Parseval's
  equality are equivalent.
* `theorem_1_3_13` — the real trigonometric system is an orthonormal basis of `L²(-π, π)`.
* `example_1_3_14` — the half-range cosine system is an orthonormal basis of `L²(0, π)`.
* `theorem_1_3_16` — the Gram–Schmidt process, with the equality of initial spans (1.3.11).

## Conventions

Theorem 1.3.13 is stated on `L²(AddCircle (2π))` with its *probability* Haar measure, which is
`L²(-π, π)` for the `2π`-periodic functions the book means, up to the scaling of the measure by
`2π`. That scaling is what turns the book's `1/√(2π)`, `cos (j x)/√π`, `sin (j x)/√π` into the
system `1`, `√2 cos (j x)`, `√2 sin (j x)` of the backbone's `trigFun`: dividing by `√(2π)`
renormalises a function of unit `L²(-π, π)` norm to unit norm for the probability measure.

## Not formalized here

Example 1.3.7 and Example 1.2.28 (b) need Sobolev spaces and are out of scope for the project.
Example 1.3.17, the Gram–Schmidt process applied to `1, x, x²` in `L²(-1, 1)`, is a worked
arithmetic illustration of `theorem_1_3_16`: it would need the three monomials read as elements of
`L²(-1, 1)` and the `gramSchmidtNormed` recursion unfolded and integrated by hand, and no result
depends on the answer. The family itself is the backbone's `Polynomial.legendre`, which §3.5 of
this surface uses.
-/

open Filter InnerProductSpace MeasureTheory Submodule Topology

open scoped Real

namespace AtkinsonHan.Chapter01

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Definition 1.3.1.** An *inner product* on a linear space `V` over `𝕂 = ℝ` or `ℂ` is a map
`(·, ·) : V × V → 𝕂` with `(v, v) ≥ 0` and `(v, v) = 0` only for `v = 0`; `(u, v) = conj (v, u)`;
and `(α u + β v, w) = α (u, w) + β (v, w)`. The space together with the inner product is an
*inner product space*.

This is Mathlib's `Inner`, bundled as `InnerProductSpace 𝕜 E`, and the statement below is the
book's three axioms in the slot convention of this file: the book's `(u, v)` is `inner 𝕜 v u`, so
the book's linearity in the first argument is Mathlib's linearity in the second. -/
theorem definition_1_3_1 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    (∀ v : E, 0 ≤ RCLike.re (inner 𝕜 v v) ∧ (inner 𝕜 v v = (0 : 𝕜) ↔ v = 0)) ∧
      (∀ u v : E, inner 𝕜 v u = starRingEnd 𝕜 (inner 𝕜 u v)) ∧
      (∀ (u v w : E) (α β : 𝕜),
        inner 𝕜 w (α • u + β • v) = α * inner 𝕜 w u + β * inner 𝕜 w v) := by
  refine ⟨fun v => ⟨?_, inner_self_eq_zero⟩, fun u v => (inner_conj_symm v u).symm,
    fun u v w α β => ?_⟩
  · rw [inner_self_eq_norm_sq]
    positivity
  · rw [inner_add_right, inner_smul_right, inner_smul_right]

/-- **Theorem 1.3.2** (Cauchy–Schwarz). `|(u, v)| ≤ ‖u‖ ‖v‖`, with equality if and only if `u` and
`v` are linearly dependent. -/
theorem theorem_1_3_2 (u v : E) :
    ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ ∧
      (‖inner 𝕜 u v‖ = ‖u‖ * ‖v‖ ↔ ¬ LinearIndependent 𝕜 ![u, v]) := by
  refine ⟨norm_inner_le_norm (𝕜 := 𝕜) (E := E) u v, ?_⟩
  have hdep : ¬ LinearIndependent 𝕜 ![u, v] ↔ (v = 0 ∨ ∃ a : 𝕜, a • v = u) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      by_cases hv : v = 0
      · exact Or.inl hv
      · push Not at h
        exact Or.inr (h hv)
    · rintro (rfl | ⟨a, rfl⟩) h
      · exact h.1 rfl
      · exact h.2 a rfl
  rw [hdep]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [norm_inner_eq_norm_iff hu hv]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact Or.inr ⟨r⁻¹, by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]⟩
  · rintro (h | ⟨a, ha⟩)
    · exact absurd h hv
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact hu (by simpa using ha.symm)
      exact ⟨a⁻¹, inv_ne_zero ha0, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

/-- **Proposition 1.3.3.** The inner product is continuous in both of its arguments: if `uₙ → u`
and `vₙ → v` then `(uₙ, vₙ) → (u, v)`. -/
theorem proposition_1_3_3 {u v : ℕ → E} {x y : E} (hu : Tendsto u atTop (𝓝 x))
    (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => inner 𝕜 (u n) (v n)) atTop (𝓝 (inner 𝕜 x y)) :=
  hu.inner hv

end InnerProduct

/-- **Theorem 1.3.4** (Fréchet–von Neumann–Jordan). The norm of a normed space is induced by an
inner product if and only if it satisfies the parallelogram law (1.3.3),
`‖u + v‖² + ‖u - v‖² = 2 (‖u‖² + ‖v‖²)`. -/
theorem theorem_1_3_4 (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    Nonempty (InnerProductSpace 𝕜 E) ↔
      ∀ u v : E, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  constructor
  · rintro ⟨_⟩ u v
    exact parallelogram_law_with_norm (𝕜 := 𝕜) (E := E) u v
  · intro h
    have : InnerProductSpaceable E := ⟨fun u v => by
      simpa only [← pow_two] using h u v⟩
    exact nonempty_innerProductSpace 𝕜 E

section Hilbert0

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Definition 1.3.5.** A *Hilbert space* is a complete inner product space: an inner product
space that is a Banach space under the induced norm `‖v‖ = √(v, v)`.

Mathlib bundles no `HilbertSpace`; a Hilbert space is `CompleteSpace E` beside
`InnerProductSpace 𝕜 E`, and that hypothesis pair is what this surface carries. The two clauses
below are the induced norm and completeness in the sense of Definition 1.2.24. -/
theorem definition_1_3_5 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    (∀ v : E, ‖v‖ = √(RCLike.re (inner 𝕜 v v))) ∧
      (CompleteSpace E ↔ ∀ u : ℕ → E, definition_1_2_21 u → ∃ v : E, definition_1_2_8 u v) :=
  ⟨fun v => by rw [inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)], definition_1_2_24 E⟩

/-- **Example 1.3.6.** Hilbert spaces: `ℂ^d` with `(x, y) = ∑ xᵢ conj yᵢ`; the sequence space `ℓ²`
with `(x, y) = ∑ xᵢ conj yᵢ`; and `L²(μ)` with `(u, v) = ∫ u conj v dμ`, of which `L²(0, 1)`,
`L²(Ω)` and the weighted space `L²_w(Ω)` — the case `μ = ν.withDensity w` — are instances. -/
theorem example_1_3_6 (d : ℕ) {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    ((∀ x y : EuclideanSpace ℂ (Fin d), inner ℂ y x = ∑ i, x i * starRingEnd ℂ (y i)) ∧
        CompleteSpace (EuclideanSpace ℂ (Fin d))) ∧
      ((∀ x y : lp (fun _ : ℕ => ℂ) 2, inner ℂ y x = ∑' i, x i * starRingEnd ℂ (y i)) ∧
        CompleteSpace (lp (fun _ : ℕ => ℂ) 2)) ∧
      ((∀ u v : Lp ℂ 2 μ, inner ℂ v u = ∫ a, u a * starRingEnd ℂ (v a) ∂μ) ∧
        CompleteSpace (Lp ℂ 2 μ)) := by
  refine ⟨⟨fun x y => ?_, inferInstance⟩, ⟨fun x y => ?_, inferInstance⟩,
    ⟨fun u v => ?_, inferInstance⟩⟩
  · rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [RCLike.inner_apply, mul_comm]
  · rw [lp.inner_eq_tsum]
    exact tsum_congr fun i => by rw [RCLike.inner_apply, mul_comm]
  · rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp [RCLike.inner_apply]

/-- **Definition 1.3.8.** Two vectors `u` and `v` are *orthogonal* when `(u, v) = 0`; an element
`v` is orthogonal to a subset `U` when it is orthogonal to every `u ∈ U`, which is
`v ∈ definition_1_3_9 𝕜 U`.

This is `inner 𝕜 v u = 0` in Mathlib, the slots swapped as everywhere in this file. The identity
the book records beside the definition — `‖u₁ + ⋯ + uₙ‖² = ‖u₁‖² + ⋯ + ‖uₙ‖²` for mutually
orthogonal elements — is `definition_1_3_8_pythagoras` in the two-term case. -/
def definition_1_3_8 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (u v : E) : Prop :=
  inner 𝕜 v u = (0 : 𝕜)

/-- Pythagoras: orthogonal vectors satisfy `‖u + v‖² = ‖u‖² + ‖v‖²`. -/
theorem definition_1_3_8_pythagoras {u v : E} (h : definition_1_3_8 𝕜 u v) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h' : inner 𝕜 u v = (0 : 𝕜) := by rw [← inner_conj_symm u v, h, map_zero]
  simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) u v h'

/-- **Definition 1.3.9.** The *orthogonal complement* of a subset `U` of an inner product space is
`Uᗮ = {v | (v, u) = 0 for all u ∈ U}`; it is always a closed subspace.

This is Mathlib's `Submodule.orthogonal` when `U` is a submodule (`definition_1_3_9_iff`); it is
closed by `definition_1_3_9_isClosed` and a subspace by `definition_1_3_9_isSubspace`. -/
def definition_1_3_9 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (U : Set E) : Set E :=
  {v | ∀ u ∈ U, definition_1_3_8 𝕜 v u}

/-- For a submodule, Definition 1.3.9 is Mathlib's `Submodule.orthogonal`. -/
theorem definition_1_3_9_iff (U : Submodule 𝕜 E) :
    definition_1_3_9 𝕜 (U : Set E) = (Uᗮ : Set E) := by
  ext v
  simp [definition_1_3_9, definition_1_3_8, Submodule.mem_orthogonal]

/-- The orthogonal complement of any subset is closed. -/
theorem definition_1_3_9_isClosed (U : Set E) : IsClosed (definition_1_3_9 𝕜 U) := by
  have h : definition_1_3_9 𝕜 U = ⋂ u ∈ U, (fun v => inner 𝕜 u v) ⁻¹' {(0 : 𝕜)} := by
    ext v
    simp [definition_1_3_9, definition_1_3_8]
  rw [h]
  exact isClosed_biInter fun u _ => isClosed_singleton.preimage (innerSL 𝕜 u).continuous

/-- The orthogonal complement of any subset is a subspace in the sense of Definition 1.1.3. -/
theorem definition_1_3_9_isSubspace (U : Set E) :
    definition_1_1_3 𝕜 (definition_1_3_9 𝕜 U) := by
  refine ⟨fun v hv w hw u hu => ?_, fun α v hv u hu => ?_⟩
  · have h1 : inner 𝕜 u v = (0 : 𝕜) := hv u hu
    have h2 : inner 𝕜 u w = (0 : 𝕜) := hw u hu
    change inner 𝕜 u (v + w) = (0 : 𝕜)
    rw [inner_add_right, h1, h2, add_zero]
  · have h1 : inner 𝕜 u v = (0 : 𝕜) := hv u hu
    change inner 𝕜 u (α • v) = (0 : 𝕜)
    rw [inner_smul_right, h1, mul_zero]

/-- **Definition 1.3.10.** A family `{vᵢ}` in an inner product space is an *orthonormal system*
when `(vᵢ, vⱼ) = δᵢⱼ`; it is an *orthonormal basis* when it is in addition a basis in the sense of
Definition 1.2.20.

This is Mathlib's `Orthonormal` (`definition_1_3_10_iff`), with `HilbertBasis` for the basis
form. -/
def definition_1_3_10 (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : ℕ → E) : Prop :=
  ∀ i j, inner 𝕜 (v i) (v j) = if i = j then (1 : 𝕜) else 0

/-- Definition 1.3.10 is Mathlib's `Orthonormal`. -/
theorem definition_1_3_10_iff (v : ℕ → E) : definition_1_3_10 𝕜 v ↔ Orthonormal 𝕜 v :=
  orthonormal_iff_ite.symm

/-- An *orthonormal basis*: an orthonormal system that is also a countably-infinite basis in the
sense of Definition 1.2.20. -/
def definition_1_3_10_basis (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : ℕ → E) : Prop :=
  definition_1_3_10 𝕜 v ∧ definition_1_2_20 𝕜 v

end Hilbert0

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {ι : Type*} {v : ι → E}

/-- **Theorem 1.3.11.** For an orthonormal system `{vⱼ}` in a Hilbert space and any `u`:
(a) Bessel's inequality `∑ |(u, vⱼ)|² ≤ ‖u‖²`; (b) the series `∑ (u, vⱼ) vⱼ` converges; (c) if
`u = ∑ aⱼ vⱼ` then necessarily `aⱼ = (u, vⱼ)`. -/
theorem theorem_1_3_11 (hv : Orthonormal 𝕜 v) (u : E) :
    ∑' i, ‖inner 𝕜 (v i) u‖ ^ 2 ≤ ‖u‖ ^ 2 ∧
      Summable (fun i => inner 𝕜 (v i) u • v i) ∧
      ∀ a : ι → 𝕜, HasSum (fun i => a i • v i) u → ∀ j, a j = inner 𝕜 (v j) u := by
  classical
  refine ⟨hv.tsum_inner_products_le u, ?_, ?_⟩
  · have h := (hv.orthogonalFamily.summable_iff_norm_sq_summable
      (fun i => (inner 𝕜 (v i) u : 𝕜))).2 (by simpa using hv.inner_products_summable u)
    simpa [LinearIsometry.toSpanSingleton_apply] using h
  · intro a hsum j
    have h : HasSum (fun i => inner 𝕜 (v j) (a i • v i)) (inner 𝕜 (v j) u) :=
      hsum.mapL (innerSL 𝕜 (v j))
    have hterm : ∀ i, inner 𝕜 (v j) (a i • v i) = if i = j then a j else 0 := by
      intro i
      rw [inner_smul_right, orthonormal_iff_ite.mp hv j i]
      rcases eq_or_ne i j with rfl | hij
      · simp
      · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, mul_zero]
    simp only [hterm] at h
    exact (hasSum_ite_eq j (a j)).unique h

/-- **Theorem 1.3.12.** For an orthonormal system `{vⱼ}` in a Hilbert space the following are
equivalent: (a) it is an orthonormal basis, that is its span is dense; (b) the generalized
Parseval identity `(u, w) = ∑ (u, vⱼ) (vⱼ, w)` holds for all `u, w`; (c) Parseval's equality
`‖w‖² = ∑ |(w, vⱼ)|²` holds for all `w`. -/
theorem theorem_1_3_12 (hv : Orthonormal 𝕜 v) :
    List.TFAE
      [(span 𝕜 (Set.range v)).topologicalClosure = ⊤,
        ∀ u w : E, HasSum (fun i => inner 𝕜 u (v i) * inner 𝕜 (v i) w) (inner 𝕜 u w),
        ∀ w : E, HasSum (fun i => ‖inner 𝕜 (v i) w‖ ^ 2) (‖w‖ ^ 2)] := by
  tfae_have 1 → 2 := by
    intro h u w
    have hbot : (span 𝕜 (Set.range v))ᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.mp h
    have h2 := (HilbertBasis.mkOfOrthogonalEqBot hv hbot).hasSum_inner_mul_inner u w
    rwa [HilbertBasis.coe_mkOfOrthogonalEqBot] at h2
  tfae_have 2 → 3 := by
    intro h w
    have h2 := (h w w).map (RCLike.re (K := 𝕜)) RCLike.continuous_re
    have key : ∀ i, RCLike.re (inner 𝕜 w (v i) * inner 𝕜 (v i) w)
        = ‖inner 𝕜 (v i) w‖ ^ 2 := by
      intro i
      rw [← inner_conj_symm w (v i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    simp only [Function.comp_def, key, inner_self_eq_norm_sq] at h2
    exact h2
  tfae_have 3 → 1 := by
    intro h
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    have hzero : ∀ i, inner 𝕜 (v i) w = 0 := by
      intro i
      have hmem : v i ∈ span 𝕜 (Set.range v) := subset_span ⟨i, rfl⟩
      exact (Submodule.mem_orthogonal _ _).mp hw _ hmem
    have h0 : HasSum (fun i : ι => ‖inner 𝕜 (v i) w‖ ^ 2) 0 := by
      simp [hzero]
    have hnorm : ‖w‖ ^ 2 = 0 := (h w).unique h0
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm)
  tfae_finish

end Hilbert

section Trigonometric

local instance instTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- **Theorem 1.3.13.** The real trigonometric system is an orthonormal basis of `L²(-π, π)`: it
is orthonormal and its span is dense. Its members, listed as `trigFun (2π) n` for `n : ℤ`, are the
constant, the cosines `√2 cos (j x)` and the sines `√2 sin (j x)`; these are the book's
`1/√(2π)`, `cos (j x)/√π` and `sin (j x)/√π` renormalised for the probability Haar measure of the
circle, which is Lebesgue measure on `(-π, π)` divided by `2π`. -/
theorem theorem_1_3_13 :
    Orthonormal ℝ (trigBasis (2 * π)) ∧
      (span ℝ (Set.range ⇑(trigBasis (2 * π)))).topologicalClosure = ⊤ ∧
      (∀ x : AddCircle (2 * π), trigFun (2 * π) 0 x = 1) ∧
      (∀ j : ℤ, 0 < j → ∀ x : ℝ,
        trigFun (2 * π) j (x : AddCircle (2 * π)) = √2 * Real.cos (j * x)) ∧
      (∀ j : ℤ, 0 < j → ∀ x : ℝ,
        trigFun (2 * π) (-j) (x : AddCircle (2 * π)) = √2 * Real.sin (j * x)) := by
  have hπ : (2 * π) ≠ 0 := ne_of_gt Real.two_pi_pos
  refine ⟨(trigBasis (2 * π)).orthonormal, (trigBasis (2 * π)).dense_span, fun x => by simp,
    fun j hj x => ?_, fun j hj x => ?_⟩
  · rw [trigFun_coe_apply_of_pos hj x]
    congr 2
    field_simp
  · rw [trigFun_coe_apply_of_neg (by omega : (-j : ℤ) < 0) x]
    congr 2
    push_cast
    field_simp

/-- **Example 1.3.14.** The half-range cosine system `e₀ = 1/√π`, `eₖ = √(2/π) cos (k x)` for
`k ≥ 1` is an orthonormal basis of `L²(0, π)`: it is orthonormal, its span is dense, and its
members are the stated functions.

`L²(0, π)` is `Lp ℝ 2 halfRangeMeasure`, with `halfRangeMeasure` Lebesgue measure on `[0, π]` read
on the subtype. The proof in `Numlib.Analysis.Fourier.CosineBasis` is Stone–Weierstrass rather than
the even extension the book suggests: the span of the `cos (k x)` is a subalgebra of `C([0, π], ℝ)`
by the product-to-sum formula, and it separates points because `cos` is injective on `[0, π]`. -/
theorem example_1_3_14 :
    Orthonormal ℝ cosLp ∧
      (span ℝ (Set.range cosLp)).topologicalClosure = ⊤ ∧
      (∀ k : ℕ, cosLp k = ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosFun k)) ∧
      (∀ x : Set.Icc (0 : ℝ) π, cosFun 0 x = 1 / √π) ∧
      (∀ k : ℕ, k ≠ 0 → ∀ x : Set.Icc (0 : ℝ) π,
        cosFun k x = √(2 / π) * Real.cos (k * (x : ℝ))) :=
  ⟨orthonormal_cosLp, dense_span_cosLp, fun _ => rfl, cosFun_zero_apply,
    fun _ hk => cosFun_apply_of_ne_zero hk⟩

end Trigonometric

section GramSchmidt

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Theorem 1.3.16** (the Gram–Schmidt process). A linearly independent sequence `{fₙ}` in an
inner product space can be replaced by an orthonormal sequence `{wₙ}` with the same initial spans,
which is (1.3.11). -/
theorem theorem_1_3_16 {f : ℕ → E} (hf : LinearIndependent 𝕜 f) :
    ∃ w : ℕ → E, Orthonormal 𝕜 w ∧
      ∀ n : ℕ, span 𝕜 (w '' Set.Iic n) = span 𝕜 (f '' Set.Iic n) :=
  ⟨gramSchmidtNormed 𝕜 f, gramSchmidtNormed_orthonormal hf, fun n => by
    rw [span_gramSchmidtNormed f (Set.Iic n), span_gramSchmidt_Iic 𝕜 f n]⟩

end GramSchmidt

end AtkinsonHan.Chapter01
