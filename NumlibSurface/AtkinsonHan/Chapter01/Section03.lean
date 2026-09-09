import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.OrthogonalPolynomial
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
* `monomialLp` — the monomials `1, x, x², …` as elements of `L²(-1, 1)`, the input of
  Example 1.3.17.

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
* `example_1_3_17` — Gram–Schmidt applied to `1, x, x², x³` in `L²(-1, 1)`, with the four
  orthonormal polynomials the book displays and their identification with the Legendre family.

## Conventions

Theorem 1.3.13 is stated on `L²(AddCircle (2π))` with its *probability* Haar measure, which is
`L²(-π, π)` for the `2π`-periodic functions the book means, up to the scaling of the measure by
`2π`. That scaling is what turns the book's `1/√(2π)`, `cos (j x)/√π`, `sin (j x)/√π` into the
system `1`, `√2 cos (j x)`, `√2 sin (j x)` of the backbone's `trigFun`: dividing by `√(2π)`
renormalises a function of unit `L²(-π, π)` norm to unit norm for the probability measure.

Example 1.3.17 is computed rather than quoted: `L²(-1, 1)` is `Lp ℝ 2` of Lebesgue measure on
`(-1, 1)`, the `gramSchmidtNormed` recursion is unfolded four steps on the monomials, and each
inner product and norm is a polynomial integral over `(-1, 1)`. The answer is then matched against
`Polynomial.legendre`, the backbone's Legendre family, which §3.5 of this surface also uses: the
book's `vₙ` are `√((2n + 1)/2)` times those. Elements of `L²(-1, 1)` are equivalence classes, so
the displayed formulas are almost-everywhere equalities of functions.

## Not formalized here

Example 1.3.7 and Example 1.2.28 (b) need Sobolev spaces and are out of scope for the project.
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

section Legendre

open Polynomial OrthogonalPolynomial

/-- `L²(-1, 1)` is `Lp ℝ 2 (volume.restrict (Set.Ioo (-1) 1))`, and Lebesgue measure on `(-1, 1)`
is a weight in the sense of the backbone: all its moments are finite, and it is not carried by a
finite set. This is what makes every polynomial an element of `L²(-1, 1)`. -/
private theorem isWeightIoo : IsWeight (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  isWeight_legendreMeasure

/-- A real polynomial read as an element of `L²(-1, 1)`, linearly in the polynomial. -/
private noncomputable def polyL2 : ℝ[X] →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  isWeightIoo.toLpₗ

/-- `polyL2 p` is the function `x ↦ p(x)`. -/
private theorem coeFn_polyL2 (p : ℝ[X]) :
    ⇑(polyL2 p) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x => eval x p :=
  isWeightIoo.coeFn_toLpₗ p

/-- Scaling a polynomial by a constant scales its image in `L²(-1, 1)`. -/
private theorem polyL2_C_mul (c : ℝ) (p : ℝ[X]) : polyL2 (C c * p) = c • polyL2 p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]

/-- Distinct polynomials are distinct in `L²(-1, 1)`: a nonzero polynomial has positive
`L²(-1, 1)` norm. -/
private theorem injective_polyL2 : Function.Injective polyL2 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  by_contra hne
  have hpos := isWeightIoo.integral_eval_sq_pos hne
  have hzero : inner ℝ (polyL2 p) (polyL2 p) = (0 : ℝ) := by rw [hp]; simp
  rw [polyL2, isWeightIoo.inner_toLpₗ] at hzero
  simp only [← pow_two] at hzero
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- An integral against Lebesgue measure on `(-1, 1)` is an integral over the interval. -/
private theorem integral_Ioo (f : ℝ → ℝ) :
    ∫ x, f x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)) = ∫ x in (-1 : ℝ)..1, f x :=
  integral_legendreMeasure f

/-- The integral over `(-1, 1)` of a polynomial of degree at most six, from its coefficients: the
odd powers integrate to zero and `∫ x^{2k} = 2/(2k + 1)`. -/
private theorem integral_poly (a : Fin 7 → ℝ) :
    (∫ x in (-1 : ℝ)..1, ∑ i : Fin 7, a i * x ^ (i : ℕ))
      = 2 * a 0 + 2 / 3 * a 2 + 2 / 5 * a 4 + 2 / 7 * a 6 := by
  rw [intervalIntegral.integral_finsetSum fun (i : Fin 7) _ =>
    (intervalIntegral.intervalIntegrable_pow (n := (i : ℕ))).const_mul (a i)]
  simp [Fin.sum_univ_seven, intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- The `L²(-1, 1)` inner product of two polynomials whose product has degree at most six, read off
from the coefficients of that product. -/
private theorem inner_polyL2 (p q : ℝ[X]) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
    (h : ∀ x : ℝ, eval x p * eval x q
      = a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6) :
    inner ℝ (polyL2 p) (polyL2 q) = 2 * a₀ + 2 / 3 * a₂ + 2 / 5 * a₄ + 2 / 7 * a₆ := by
  rw [polyL2, isWeightIoo.inner_toLpₗ p q, integral_Ioo]
  simp only [h]
  have := integral_poly ![a₀, a₁, a₂, a₃, a₄, a₅, a₆]
  simpa [Fin.sum_univ_seven] using this

/-- `inner_polyL2` in the diagonal case: the squared `L²(-1, 1)` norm of a polynomial. -/
private theorem normSq_polyL2 (p : ℝ[X]) (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ℝ)
    (h : ∀ x : ℝ, eval x p * eval x p
      = a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6) :
    ‖polyL2 p‖ ^ 2 = 2 * a₀ + 2 / 3 * a₂ + 2 / 5 * a₄ + 2 / 7 * a₆ := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_polyL2 p p a₀ a₁ a₂ a₃ a₄ a₅ a₆ h

/-- The monomial `x ↦ xⁿ` is square integrable on `(-1, 1)`. -/
private theorem memLp_pow (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  MemLp.ae_eq (by simp) (isWeightIoo.memLp (X ^ n))

/-- The monomials `1, x, x², …` as elements of `L²(-1, 1)`: the sequence that Example 1.3.17 feeds
to the Gram–Schmidt process of Theorem 1.3.16. -/
noncomputable def monomialLp (n : ℕ) : Lp ℝ 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  MemLp.toLp _ (memLp_pow n)

/-- `monomialLp n` is the function `x ↦ xⁿ`. -/
theorem coeFn_monomialLp (n : ℕ) :
    ⇑(monomialLp n) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => x ^ n :=
  MemLp.coeFn_toLp _

/-- `monomialLp n` is the monomial `Xⁿ` read in `L²(-1, 1)`. -/
private theorem monomialLp_eq (n : ℕ) : monomialLp n = polyL2 (X ^ n) := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_monomialLp n, coeFn_polyL2 (X ^ n)] with x h1 h2
  rw [h1, h2, eval_pow, eval_X]

/-- The Gram–Schmidt recursion in the form Example 1.3.17 unfolds it: the `n`-th vector minus its
projections onto the previous ones, the sum taken over `Finset.range n`. -/
private theorem gramSchmidt_recurrence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℕ → E) (n : ℕ) :
    gramSchmidt ℝ f n = f n - ∑ i ∈ Finset.range n,
      (inner ℝ (gramSchmidt ℝ f i) (f n) / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  rw [eq_sub_iff_add_eq]
  simpa [Nat.Iio_eq_range] using (gramSchmidt_def'' ℝ f n).symm

/-- The first Gram–Schmidt vector is the constant `1`. -/
private theorem gramSchmidt_monomialLp_zero : gramSchmidt ℝ monomialLp 0 = polyL2 1 := by
  rw [gramSchmidt_recurrence]
  simp [monomialLp_eq]

/-- `∫_{-1}^{1} 1 = 2`. -/
private theorem normSq_polyL2_one : ‖polyL2 1‖ ^ 2 = 2 := by
  rw [normSq_polyL2 _ 1 0 0 0 0 0 0 fun x => by simp]; norm_num

/-- `∫_{-1}^{1} x² = 2/3`. -/
private theorem normSq_polyL2_X : ‖polyL2 X‖ ^ 2 = 2 / 3 := by
  rw [normSq_polyL2 _ 0 0 1 0 0 0 0 fun x => by simp; ring]; norm_num

/-- The second Gram–Schmidt vector is `x`: `1` and `x` are already orthogonal. -/
private theorem gramSchmidt_monomialLp_one : gramSchmidt ℝ monomialLp 1 = polyL2 X := by
  rw [gramSchmidt_recurrence, Finset.sum_range_one, gramSchmidt_monomialLp_zero]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 1) 0 1 0 0 0 0 0 fun x => by simp]
  simp

/-- The third Gram–Schmidt vector is `x² - 1/3`: subtracting `(1, x²)/‖1‖² = 1/3` from `x²`. -/
private theorem gramSchmidt_monomialLp_two :
    gramSchmidt ℝ monomialLp 2 = polyL2 (X ^ 2 - C (1 / 3)) := by
  rw [gramSchmidt_recurrence, Finset.sum_range_succ, Finset.sum_range_one,
    gramSchmidt_monomialLp_zero, gramSchmidt_monomialLp_one]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 2) 0 0 1 0 0 0 0 (fun x => by simp),
    inner_polyL2 X (X ^ 2) 0 0 0 1 0 0 0 (fun x => by simp; ring),
    normSq_polyL2_one, normSq_polyL2_X, map_sub, ← polyL2_C_mul, mul_one]
  norm_num

/-- `∫_{-1}^{1} (x² - 1/3)² = 8/45`. -/
private theorem normSq_polyL2_two : ‖polyL2 (X ^ 2 - C (1 / 3))‖ ^ 2 = 8 / 45 := by
  rw [normSq_polyL2 _ (1 / 9) 0 (-2 / 3) 0 1 0 0 fun x => by simp; ring]; norm_num

/-- The fourth Gram–Schmidt vector is `x³ - (3/5) x`: only the projection onto `x` survives. -/
private theorem gramSchmidt_monomialLp_three :
    gramSchmidt ℝ monomialLp 3 = polyL2 (X ^ 3 - C (3 / 5) * X) := by
  rw [gramSchmidt_recurrence, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    gramSchmidt_monomialLp_zero, gramSchmidt_monomialLp_one, gramSchmidt_monomialLp_two]
  simp only [monomialLp_eq]
  rw [inner_polyL2 1 (X ^ 3) 0 0 0 1 0 0 0 (fun x => by simp),
    inner_polyL2 X (X ^ 3) 0 0 0 0 1 0 0 (fun x => by simp; ring),
    inner_polyL2 (X ^ 2 - C (1 / 3)) (X ^ 3) 0 0 0 (-1 / 3) 0 1 0 (fun x => by simp; ring),
    normSq_polyL2_one, normSq_polyL2_X, normSq_polyL2_two]
  have hrhs : polyL2 (X ^ 3 - C (3 / 5) * X) = polyL2 (X ^ 3) - (3 / 5 : ℝ) • polyL2 X := by
    rw [map_sub, polyL2_C_mul]
  rw [hrhs]
  norm_num

/-- `∫_{-1}^{1} (x³ - (3/5) x)² = 8/175`. -/
private theorem normSq_polyL2_three : ‖polyL2 (X ^ 3 - C (3 / 5) * X)‖ ^ 2 = 8 / 175 := by
  rw [normSq_polyL2 _ 0 0 (9 / 25) 0 (-6 / 5) 0 1 fun x => by simp; ring]; norm_num

/-- The `L²(-1, 1)` norm of a polynomial, from its square. -/
private theorem norm_polyL2_of_sq (p : ℝ[X]) (c : ℝ) (h : ‖polyL2 p‖ ^ 2 = c) :
    ‖polyL2 p‖ = √c := by
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- The first normalized Gram–Schmidt vector, before the constant is simplified. -/
private theorem gramSchmidtNormed_monomialLp_zero :
    gramSchmidtNormed ℝ monomialLp 0 = (√2)⁻¹ • polyL2 1 := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_zero,
    norm_polyL2_of_sq _ 2 normSq_polyL2_one, RCLike.ofReal_real_eq_id, id_eq]

/-- The second normalized Gram–Schmidt vector, before the constant is simplified. -/
private theorem gramSchmidtNormed_monomialLp_one :
    gramSchmidtNormed ℝ monomialLp 1 = (√(2 / 3))⁻¹ • polyL2 X := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_one,
    norm_polyL2_of_sq _ _ normSq_polyL2_X, RCLike.ofReal_real_eq_id, id_eq]

/-- The third normalized Gram–Schmidt vector, before the constant is simplified. -/
private theorem gramSchmidtNormed_monomialLp_two :
    gramSchmidtNormed ℝ monomialLp 2 = (√(8 / 45))⁻¹ • polyL2 (X ^ 2 - C (1 / 3)) := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_two,
    norm_polyL2_of_sq _ _ normSq_polyL2_two, RCLike.ofReal_real_eq_id, id_eq]

/-- The fourth normalized Gram–Schmidt vector, before the constant is simplified. -/
private theorem gramSchmidtNormed_monomialLp_three :
    gramSchmidtNormed ℝ monomialLp 3 = (√(8 / 175))⁻¹ • polyL2 (X ^ 3 - C (3 / 5) * X) := by
  rw [gramSchmidtNormed, gramSchmidt_monomialLp_three,
    norm_polyL2_of_sq _ _ normSq_polyL2_three, RCLike.ofReal_real_eq_id, id_eq]

/-- A scalar multiple of a polynomial in `L²(-1, 1)` is the function `x ↦ c p(x)`. -/
private theorem coeFn_smul_polyL2 (c : ℝ) (p : ℝ[X]) :
    ⇑(c • polyL2 p) =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x => c * eval x p := by
  filter_upwards [Lp.coeFn_smul c (polyL2 p), coeFn_polyL2 p] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

/-- `(√2)⁻¹ = 1/√2`. -/
private theorem inv_sqrt_two : (√(2 : ℝ))⁻¹ = 1 / √2 := (one_div _).symm

/-- `(√(2/3))⁻¹ = √(3/2)`. -/
private theorem inv_sqrt_two_div_three : (√(2 / 3 : ℝ))⁻¹ = √(3 / 2) := by
  rw [← Real.sqrt_inv]; norm_num

/-- `(√(8/45))⁻¹ = (3/2) √(5/2)`. -/
private theorem inv_sqrt_eight_div_fortyFive : (√(8 / 45 : ℝ))⁻¹ = 3 / 2 * √(5 / 2) := by
  rw [← Real.sqrt_inv, show ((8 : ℝ) / 45)⁻¹ = (3 / 2) ^ 2 * (5 / 2) by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- `(√(8/175))⁻¹ = (5/2) √(7/2)`. -/
private theorem inv_sqrt_eight_div_oneSeventyFive : (√(8 / 175 : ℝ))⁻¹ = 5 / 2 * √(7 / 2) := by
  rw [← Real.sqrt_inv, show ((8 : ℝ) / 175)⁻¹ = (5 / 2) ^ 2 * (7 / 2) by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- `√(1/2) = 1/√2`. -/
private theorem sqrt_half : √(1 / 2 : ℝ) = 1 / √2 := by
  rw [one_div, Real.sqrt_inv, one_div]

/-- `2 P₂ = 3 X² - 1`, from the Legendre recursion. -/
private theorem two_mul_legendre_two : 2 * legendre 2 = 3 * X ^ 2 - 1 := by
  have h := legendre_recurrence 0
  rw [legendre_zero, legendre_one] at h
  push_cast at h
  linear_combination h

/-- `6 P₃ = 15 X³ - 9 X`, from the Legendre recursion. -/
private theorem six_mul_legendre_three : 6 * legendre 3 = 15 * X ^ 3 - 9 * X := by
  have h := legendre_recurrence 1
  rw [legendre_one] at h
  push_cast at h
  linear_combination 2 * h + 5 * X * two_mul_legendre_two

/-- `P₂(x) = (3x² - 1)/2`. -/
private theorem eval_legendre_two (x : ℝ) : eval x (legendre 2) = (3 * x ^ 2 - 1) / 2 := by
  have h := congrArg (eval x) two_mul_legendre_two
  simp only [eval_mul, eval_ofNat, eval_sub, eval_pow, eval_X, eval_one] at h
  linarith

/-- `P₃(x) = (5x³ - 3x)/2`. -/
private theorem eval_legendre_three (x : ℝ) : eval x (legendre 3) = (5 * x ^ 3 - 3 * x) / 2 := by
  have h := congrArg (eval x) six_mul_legendre_three
  simp only [eval_mul, eval_ofNat, eval_sub, eval_pow, eval_X] at h
  linarith

/-- The monomials are linearly independent in `L²(-1, 1)`, so Theorem 1.3.16 applies to them. -/
private theorem linearIndependent_monomialLp : LinearIndependent ℝ monomialLp := by
  have h : LinearIndependent ℝ fun n : ℕ => (X : ℝ[X]) ^ n := by
    have hb := (Polynomial.basisMonomials ℝ).linearIndependent
    rw [Polynomial.coe_basisMonomials] at hb
    simpa [Polynomial.X_pow_eq_monomial] using hb
  rw [show monomialLp = fun n : ℕ => polyL2 (X ^ n) from funext monomialLp_eq]
  exact h.map' polyL2 (LinearMap.ker_eq_bot.2 injective_polyL2)

/-- The first orthonormal member, `1/√2`. -/
private theorem coeFn_gramSchmidtNormed_zero :
    ⇑(gramSchmidtNormed ℝ monomialLp 0)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun _ : ℝ => 1 / √2 := by
  rw [gramSchmidtNormed_monomialLp_zero, inv_sqrt_two]
  filter_upwards [coeFn_smul_polyL2 (1 / √2) 1] with x hx
  rw [hx, eval_one, mul_one]

/-- The second orthonormal member, `√(3/2) x`. -/
private theorem coeFn_gramSchmidtNormed_one :
    ⇑(gramSchmidtNormed ℝ monomialLp 1)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => √(3 / 2) * x := by
  rw [gramSchmidtNormed_monomialLp_one, inv_sqrt_two_div_three]
  filter_upwards [coeFn_smul_polyL2 (√(3 / 2)) X] with x hx
  rw [hx, eval_X]

/-- The third orthonormal member, `(3/2) √(5/2) (x² - 1/3)`. -/
private theorem coeFn_gramSchmidtNormed_two :
    ⇑(gramSchmidtNormed ℝ monomialLp 2)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => 3 / 2 * √(5 / 2) * (x ^ 2 - 1 / 3) := by
  rw [gramSchmidtNormed_monomialLp_two, inv_sqrt_eight_div_fortyFive]
  filter_upwards [coeFn_smul_polyL2 (3 / 2 * √(5 / 2)) (X ^ 2 - C (1 / 3))] with x hx
  rw [hx]
  simp

/-- The fourth orthonormal member, `(1/2) √(7/2) (5x³ - 3x)`. -/
private theorem coeFn_gramSchmidtNormed_three :
    ⇑(gramSchmidtNormed ℝ monomialLp 3)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => 1 / 2 * √(7 / 2) * (5 * x ^ 3 - 3 * x) := by
  rw [gramSchmidtNormed_monomialLp_three, inv_sqrt_eight_div_oneSeventyFive]
  filter_upwards [coeFn_smul_polyL2 (5 / 2 * √(7 / 2)) (X ^ 3 - C (3 / 5) * X)] with x hx
  rw [hx]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- The first four orthonormal members are `√((2n + 1)/2) Pₙ`, the normalized Legendre
polynomials. -/
private theorem coeFn_gramSchmidtNormed_legendre (n : ℕ) (hn : n ≤ 3) :
    ⇑(gramSchmidtNormed ℝ monomialLp n)
      =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
        fun x : ℝ => √((2 * n + 1) / 2) * eval x (legendre n) := by
  interval_cases n
  · filter_upwards [coeFn_gramSchmidtNormed_zero] with x hx
    rw [hx, legendre_zero, eval_one, mul_one]
    norm_num [sqrt_half]
  · filter_upwards [coeFn_gramSchmidtNormed_one] with x hx
    rw [hx, legendre_one, eval_X]
    norm_num
  · filter_upwards [coeFn_gramSchmidtNormed_two] with x hx
    rw [hx, eval_legendre_two]
    norm_num
    ring
  · filter_upwards [coeFn_gramSchmidtNormed_three] with x hx
    rw [hx, eval_legendre_three]
    norm_num
    ring

/-- **Example 1.3.17.** The Gram–Schmidt process of Theorem 1.3.16, applied to the linearly
independent monomials `1, x, x², x³` of `L²(-1, 1)`, produces `1/√2`, `√(3/2) x`,
`(3/2) √(5/2) (x² - 1/3)` and `(1/2) √(7/2) (5x³ - 3x)`.

These are the first four orthonormal Legendre polynomials: the last clause records that the `n`-th
one is `√((2n + 1)/2) Pₙ` for `n ≤ 3`, with `Pₙ` the Legendre polynomial `Polynomial.legendre n`,
whose orthogonality relation `∫_{-1}^{1} Pₘ Pₙ = 2 δₘₙ/(2n + 1)` is exactly the normalization used
here. The equalities hold almost everywhere because an element of `L²(-1, 1)` is an equivalence
class of functions. -/
theorem example_1_3_17 :
    LinearIndependent ℝ monomialLp ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 0)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun _ : ℝ => 1 / √2) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 1)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] fun x : ℝ => √(3 / 2) * x) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 2)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => 3 / 2 * √(5 / 2) * (x ^ 2 - 1 / 3)) ∧
      (⇑(gramSchmidtNormed ℝ monomialLp 3)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => 1 / 2 * √(7 / 2) * (5 * x ^ 3 - 3 * x)) ∧
      (∀ n ≤ 3, ⇑(gramSchmidtNormed ℝ monomialLp n)
        =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)]
          fun x : ℝ => √((2 * n + 1) / 2) * eval x (legendre n)) :=
  ⟨linearIndependent_monomialLp, coeFn_gramSchmidtNormed_zero, coeFn_gramSchmidtNormed_one,
    coeFn_gramSchmidtNormed_two, coeFn_gramSchmidtNormed_three, coeFn_gramSchmidtNormed_legendre⟩

end Legendre

end AtkinsonHan.Chapter01
