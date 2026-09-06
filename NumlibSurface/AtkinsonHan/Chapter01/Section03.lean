import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Fourier.TrigonometricBasis

/-!
# Atkinson–Han §1.3: inner product spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.3: inner product spaces, Hilbert spaces,
orthogonality, orthonormal bases and the Gram–Schmidt process.

The book's inner product is linear in its *first* slot and Mathlib's in its second, so the book's
`(u, v)` is `inner 𝕜 v u`; every statement below is written in Mathlib's convention with that
swap, as the rest of this surface does. Definitions 1.3.1, 1.3.5, 1.3.8, 1.3.9 and 1.3.10 are
`InnerProductSpace`, `CompleteSpace`, `inner 𝕜 x y = 0`, `Submodule.orthogonal` and `Orthonormal`,
and are not restated.

## Main results

* `theorem_1_3_2` — the Cauchy–Schwarz inequality, with its equality case.
* `proposition_1_3_3` — the inner product is continuous in both arguments.
* `theorem_1_3_4` — Fréchet–von Neumann–Jordan: a norm comes from an inner product exactly when
  it satisfies the parallelogram law (1.3.3).
* `theorem_1_3_11` — Bessel's inequality, convergence of the expansion, and uniqueness of the
  coefficients.
* `theorem_1_3_12` — orthonormal basis, the generalized Parseval identity, and Parseval's
  equality are equivalent.
* `theorem_1_3_13` — the real trigonometric system is an orthonormal basis of `L²(-π, π)`.
* `theorem_1_3_16` — the Gram–Schmidt process, with the equality of initial spans (1.3.11).

## Conventions

Theorem 1.3.13 is stated on `L²(AddCircle (2π))` with its *probability* Haar measure, which is
`L²(-π, π)` for the `2π`-periodic functions the book means, up to the scaling of the measure by
`2π`. That scaling is what turns the book's `1/√(2π)`, `cos (j x)/√π`, `sin (j x)/√π` into the
system `1`, `√2 cos (j x)`, `√2 sin (j x)` of the backbone's `trigFun`: dividing by `√(2π)`
renormalises a function of unit `L²(-π, π)` norm to unit norm for the probability measure.
-/

open Filter InnerProductSpace MeasureTheory Submodule Topology

open scoped Real

namespace AtkinsonHan.Chapter01

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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
