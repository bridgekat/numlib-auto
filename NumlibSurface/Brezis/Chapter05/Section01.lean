import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section07

/-!
# Brezis §5.1: definitions and elementary properties; projection onto a closed convex set

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §5.1, over a real Hilbert space `H`
(`[NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`; the definitional nodes omit
the completeness). The book's scalar product `(u, v)` is Mathlib's `⟪u, v⟫_ℝ`, symmetric over
`ℝ`, so no slot convention is needed. The two "Definition." paragraphs are read back as theorems
about Mathlib's `InnerProductSpace ℝ H` and `CompleteSpace H`; Theorem 5.2 is Mathlib's
projection theorem in the backbone's `IsBestApprox` vocabulary
(`Numlib/Analysis/Normed/Module/BestApprox`), and the projection `P_K` is the backbone's
`bestApprox K` (`Numlib/Analysis/InnerProductSpace/ConvexProjection`). Uniform convexity and
reflexivity are stated with chapter 3's definitions (`Brezis.Chapter03.IsUniformlyConvex`,
`Brezis.Chapter03.IsReflexive`), so that Proposition 5.1 and Remark 2 read through Theorem 3.31
(Milman–Pettis) as the book does. Theorem 5.12 of the Comments is placed here because it is the
converse of the parallelogram law.

## Main results

* `scalarProduct`, `cauchySchwarz`, `cauchySchwarz_of_nonneg`, `hilbertSpace`,
  `parallelogram_law`, `basicExample_L2`, `basicExample_l2` — the definitions and the facts the
  section recalls.
* `proposition_5_1`, `proposition_5_1_reflexive` — a Hilbert space is uniformly convex, hence
  reflexive.
* `theorem_5_2`, `theorem_5_2_infDist`, `theorem_5_2_iff`, `theorem_5_2_bestApprox` — the
  projection onto a closed convex set: existence and uniqueness, the distance (2), the
  variational characterization (3), and the notation `P_K`.
* `remark_5_1`, `remark_5_2` — the one-dimensional prototype of (3), and the projection in a
  uniformly convex Banach space.
* `proposition_5_3`, `corollary_5_4`, `corollary_5_4_linear` — `P_K` does not increase
  distances; on a closed subspace it is the orthogonal projection, a linear operator.
* `theorem_5_12` — Fréchet–von Neumann–Jordan: a norm satisfying the parallelogram law is a
  Hilbert norm.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

open Brezis.Chapter03 (IsUniformlyConvex IsReflexive uniformlyConvex_iff isReflexive_iff
  theorem_3_31)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Definitions and elementary properties -/

/-- **Definition (scalar product), read back.** The scalar product `(u, v) = ⟪u, v⟫_ℝ` of a real
inner product space is a bilinear form (linear in both variables), symmetric, positive and
definite. The converse — a real vector space with a scalar product is an inner product space,
with the norm `|u| = (u, u)^{1/2}` — is Mathlib's `InnerProductSpace.ofCore`. -/
theorem scalarProduct :
    ((∀ u v w : H, ⟪u + v, w⟫_ℝ = ⟪u, w⟫_ℝ + ⟪v, w⟫_ℝ) ∧
        (∀ (a : ℝ) (u w : H), ⟪a • u, w⟫_ℝ = a * ⟪u, w⟫_ℝ) ∧
        (∀ u v w : H, ⟪u, v + w⟫_ℝ = ⟪u, v⟫_ℝ + ⟪u, w⟫_ℝ) ∧
        (∀ (a : ℝ) (u w : H), ⟪u, a • w⟫_ℝ = a * ⟪u, w⟫_ℝ)) ∧
      (∀ u v : H, ⟪u, v⟫_ℝ = ⟪v, u⟫_ℝ) ∧
      (∀ u : H, 0 ≤ ⟪u, u⟫_ℝ) ∧
      (∀ u : H, u ≠ 0 → ⟪u, u⟫_ℝ ≠ 0) :=
  ⟨⟨inner_add_left, fun a u w => real_inner_smul_left u w a, inner_add_right,
      fun a u w => real_inner_smul_right u w a⟩,
    fun u v => real_inner_comm v u, fun _ => real_inner_self_nonneg,
    fun _ hu => mt inner_self_eq_zero.1 hu⟩

/-- **The Cauchy–Schwarz inequality** the section recalls: `|(u, v)| ≤ (u, u)^{1/2} (v, v)^{1/2}`
for all `u, v ∈ H`. -/
theorem cauchySchwarz (u v : H) : |⟪u, v⟫_ℝ| ≤ √⟪u, u⟫_ℝ * √⟪v, v⟫_ℝ := by
  rw [← norm_eq_sqrt_real_inner, ← norm_eq_sqrt_real_inner]
  exact abs_real_inner_le_norm u v

/-- **The bracketed remark after Cauchy–Schwarz**: its proof does not require the definiteness
`(u, u) ≠ 0` for `u ≠ 0`. For a real vector space `V` and a bilinear form `b` that is symmetric
and positive, `b(u, v)² ≤ b(u, u) b(v, v)`. Proved by Mathlib's Cauchy–Schwarz inequality for a
`PreInnerProductSpace.Core`, the structure of a scalar product without the definiteness
field. -/
theorem cauchySchwarz_of_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, b u v = b v u) (hpos : ∀ v, 0 ≤ b v v) (u v : V) :
    b u v ^ 2 ≤ b u u * b v v := by
  let _ : PreInnerProductSpace.Core ℝ V :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by simp [hsymm x y]
      re_inner_nonneg := fun x => by simpa using hpos x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) (F := V) u v
  simp only [RCLike.re_to_real, Real.norm_eq_abs] at h
  change |b u v| * |b v u| ≤ b u u * b v v at h
  rw [hsymm v u, ← sq, sq_abs] at h
  exact h

/-- **Definition (Hilbert space), read back.** The norm arising from the scalar product is
`|u| = (u, u)^{1/2}`, it satisfies the triangle inequality `|u + v| ≤ |u| + |v|` the section
derives from Cauchy–Schwarz, and a Hilbert space is a space with a scalar product that is
complete for this norm: `CompleteSpace H` is exactly "every Cauchy sequence converges". Mathlib
bundles no `HilbertSpace`; the pair `[InnerProductSpace ℝ H] [CompleteSpace H]` is what this
surface carries. -/
theorem hilbertSpace :
    (∀ u : H, ‖u‖ = √⟪u, u⟫_ℝ) ∧ (∀ u v : H, ‖u + v‖ ≤ ‖u‖ + ‖v‖) ∧
      (CompleteSpace H ↔ ∀ u : ℕ → H, CauchySeq u → ∃ v, Tendsto u atTop (𝓝 v)) :=
  ⟨norm_eq_sqrt_real_inner, norm_add_le,
    ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu,
      fun h => Metric.complete_of_cauchySeq_tendsto h⟩⟩

/-- **The parallelogram law (1)**, in the book's halved form:
`|(a + b)/2|² + |(a - b)/2|² = (|a|² + |b|²)/2` for all `a, b ∈ H`. -/
theorem parallelogram_law (a b : H) :
    ‖(1 / 2 : ℝ) • (a + b)‖ ^ 2 + ‖(1 / 2 : ℝ) • (a - b)‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  have h := parallelogram_law_with_norm ℝ a b
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [h]

/-- **Basic example.** `L²(Ω)` with the scalar product `(u, v) = ∫_Ω u(x) v(x) dμ` is a Hilbert
space: for any measure space `(α, μ)`, Mathlib's `Lp ℝ 2 μ` carries this scalar product and is
complete. -/
theorem basicExample_L2 {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) :
    (∀ u v : MeasureTheory.Lp ℝ 2 μ, ⟪u, v⟫_ℝ = ∫ x, u x * v x ∂μ) ∧
      CompleteSpace (MeasureTheory.Lp ℝ 2 μ) :=
  ⟨fun u v => by
    rw [MeasureTheory.L2.inner_def]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by
      simp [RCLike.inner_apply, mul_comm]), inferInstance⟩

/-- **Basic example, "in particular `ℓ²` is a Hilbert space"**: `ℓ² = lp (fun _ : ℕ => ℝ) 2`
with the scalar product `(u, v) = ∑ₙ uₙ vₙ` is complete. -/
theorem basicExample_l2 :
    (∀ u v : lp (fun _ : ℕ => ℝ) 2, ⟪u, v⟫_ℝ = ∑' n, u n * v n) ∧
      CompleteSpace (lp (fun _ : ℕ => ℝ) 2) :=
  ⟨fun u v => by
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun n => by simp [RCLike.inner_apply, mul_comm], inferInstance⟩

/-- **Proposition 5.1, first clause.** `H` is uniformly convex (the Definition of §3.7,
`Brezis.Chapter03.IsUniformlyConvex`): Mathlib's instance
`InnerProductSpace.toUniformConvexSpace` is the book's proof, the parallelogram law with
`δ = 1 - (1 - ε²/4)^{1/2}`. -/
theorem proposition_5_1 : IsUniformlyConvex H :=
  uniformlyConvex_iff.2 inferInstance

/-- **Proposition 5.1, second clause**, "and thus it is reflexive": by the Milman–Pettis
theorem (Theorem 3.31) applied to `proposition_5_1`. -/
theorem proposition_5_1_reflexive [CompleteSpace H] : IsReflexive H :=
  theorem_3_31 proposition_5_1

/-! ### Projection onto a closed convex set -/

section Projection

variable [CompleteSpace H]

/-- **Theorem 5.2 (projection onto a closed convex set), existence and uniqueness.** Let
`K ⊆ H` be a nonempty closed convex set. Then for every `f ∈ H` there is a unique `u ∈ K` with
`|f - u| = min_{v ∈ K} |f - v|` — a unique best approximation of `f` from `K`
(`IsBestApprox K f u` is "`u ∈ K` and `‖f - u‖ ≤ ‖f - v‖` for all `v ∈ K`"). The backbone's
`existsUnique_isBestApprox` is the book's second, direct proof: a minimizing sequence is Cauchy
by the parallelogram law. -/
theorem theorem_5_2 {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
    (f : H) : ∃! u, IsBestApprox K f u :=
  existsUnique_isBestApprox hne hcl hK f

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- **Theorem 5.2, the display (2).** For `u ∈ K`, `u` is the best approximation of `f` from
`K` exactly when `|f - u| = dist (f, K)`: the minimum is the distance. -/
theorem theorem_5_2_infDist {K : Set H} {f u : H} (hu : u ∈ K) :
    IsBestApprox K f u ↔ ‖f - u‖ = Metric.infDist f K :=
  isBestApprox_iff_norm_sub_eq_infDist hu

omit [CompleteSpace H] in
/-- **Theorem 5.2, the characterization (3).** For `K` convex and `u ∈ K`, `u` is the
projection of `f` onto `K` iff `(f - u, v - u) ≤ 0` for all `v ∈ K`. Neither closedness nor
completeness is needed for this clause. -/
theorem theorem_5_2_iff {K : Set H} (hK : Convex ℝ K) {f u : H} (hu : u ∈ K) :
    IsBestApprox K f u ↔ ∀ v ∈ K, ⟪f - u, v - u⟫_ℝ ≤ 0 :=
  isBestApprox_iff_inner_le_zero hK hu

/-- **Notation.** The element `u` of Theorem 5.2 is called the projection of `f` onto `K` and
is denoted `u = P_K f`; in this surface `P_K f` is the backbone's `bestApprox K f`, which is the
element of Theorem 5.2: it is the best approximation of `f` from `K`, and `P_K f = w` exactly when
`w ∈ K` and `(f - w, v - w) ≤ 0` for all `v ∈ K`. -/
theorem theorem_5_2_bestApprox {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : H) :
    IsBestApprox K f (bestApprox K f) ∧
      ∀ w, bestApprox K f = w ↔ w ∈ K ∧ ∀ v ∈ K, ⟪f - w, v - w⟫_ℝ ≤ 0 :=
  ⟨isBestApprox_bestApprox_of_isClosed hne hcl hK f, fun _ => bestApprox_eq_iff hne hcl hK⟩

omit [CompleteSpace H] in
/-- **Remark 1.** A minimization problem is connected with a system of inequalities: if
`F : ℝ → ℝ` is differentiable and `u ∈ [0, 1]` is a point where `F` achieves its minimum on
`[0, 1]`, then either `u ∈ (0, 1)` and `F'(u) = 0`, or `u = 0` and `F'(u) ≥ 0`, or `u = 1` and
`F'(u) ≤ 0`; the three cases are summarized by `F'(u) (v - u) ≥ 0` for all `v ∈ [0, 1]`. (The
Markdown conversion of the book prints the signs `≤ 0`, `= 1`, `≤ 0` here; the printed book and
minimality give the signs stated.) -/
theorem remark_5_1 {F : ℝ → ℝ} (hF : Differentiable ℝ F) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hmin : IsMinOn F (Set.Icc 0 1) u) :
    ((u ∈ Set.Ioo 0 1 ∧ deriv F u = 0) ∨ (u = 0 ∧ 0 ≤ deriv F u) ∨ (u = 1 ∧ deriv F u ≤ 0)) ∧
      ∀ v ∈ Set.Icc 0 1, 0 ≤ deriv F u * (v - u) := by
  have key : ∀ v ∈ Set.Icc (0 : ℝ) 1, 0 ≤ deriv F u * (v - u) := fun v hv => by
    have hseg : segment ℝ u (u + (v - u)) ⊆ Set.Icc 0 1 := by
      rw [add_sub_cancel]
      exact (convex_Icc 0 1).segment_subset hu hv
    have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      (hF u).hasDerivAt.hasFDerivAt.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using h
  refine ⟨?_, key⟩
  obtain ⟨hu0, hu1⟩ := hu
  have ha := key 0 ⟨le_rfl, zero_le_one⟩
  have hb := key 1 ⟨zero_le_one, le_rfl⟩
  rcases hu0.lt_or_eq with h0 | h0
  · rcases hu1.lt_or_eq with h1 | h1
    · exact Or.inl ⟨⟨h0, h1⟩, by nlinarith⟩
    · subst h1
      exact Or.inr (Or.inr ⟨rfl, by linarith⟩)
  · subst h0
    exact Or.inr (Or.inl ⟨rfl, by linarith⟩)

/-- **Remark 2.** Let `K ⊆ E` be a nonempty closed convex set in a uniformly convex Banach space
`E`. Then for every `f ∈ E` there is a unique `u ∈ K` with `‖f - u‖ = min_{v ∈ K} ‖f - v‖`. The
book refers to Exercise 3.32 (a direct minimizing-sequence argument); here existence comes from
reflexivity (Theorem 3.31, Milman–Pettis) and the direct method of the calculus of variations
(`exists_isBestApprox_of_convex`), uniqueness from strict convexity. -/
theorem remark_5_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hE : IsUniformlyConvex E) {K : Set E} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : E) : ∃! u, IsBestApprox K f u := by
  have := uniformlyConvex_iff.1 hE
  have := isReflexive_iff.1 (theorem_3_31 hE)
  obtain ⟨u, hu⟩ := exists_isBestApprox_of_convex hne hcl hK f
  exact ⟨u, hu, fun w hw => hw.unique hK hu⟩

/-- **Proposition 5.3.** Let `K ⊆ H` be a nonempty closed convex set. Then `P_K` does not
increase distance: `|P_K f₁ - P_K f₂| ≤ |f₁ - f₂|` for all `f₁, f₂ ∈ H`. -/
theorem proposition_5_3 {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
    (f₁ f₂ : H) : ‖bestApprox K f₁ - bestApprox K f₂‖ ≤ ‖f₁ - f₂‖ :=
  norm_bestApprox_sub_bestApprox_le hne hcl hK f₁ f₂

/-- **Corollary 5.4, the characterization (8).** Let `M ⊆ H` be a closed linear subspace and
`f ∈ H`. Then `u = P_M f` is characterized by `u ∈ M` and `(f - u, v) = 0` for all `v ∈ M`. -/
theorem corollary_5_4 {M : Submodule ℝ H} (hM : IsClosed (M : Set H)) (f u : H) :
    bestApprox (M : Set H) f = u ↔ u ∈ M ∧ ∀ v ∈ M, ⟪f - u, v⟫_ℝ = 0 := by
  have := hM.completeSpace_coe
  rw [bestApprox_eq_starProjection]
  constructor
  · rintro rfl
    exact ⟨M.starProjection_apply_mem f, fun v hv => M.starProjection_inner_eq_zero f v hv⟩
  · rintro ⟨hu, h⟩
    exact M.eq_starProjection_of_mem_of_inner_eq_zero hu h

/-- **Corollary 5.4, "moreover `P_M` is a linear operator, called the orthogonal projection".**
On a closed subspace `M`, the projection `P_M` is the bounded linear operator
`Submodule.starProjection M : H →L[ℝ] H`, of norm at most `1`. -/
theorem corollary_5_4_linear {M : Submodule ℝ H} (hM : IsClosed (M : Set H)) :
    haveI := hM.completeSpace_coe
    bestApprox (M : Set H) = ⇑M.starProjection ∧ ‖M.starProjection‖ ≤ 1 := by
  have := hM.completeSpace_coe
  exact ⟨funext (bestApprox_eq_starProjection M), M.starProjection_norm_le⟩

end Projection

/-- **Theorem 5.12 (Fréchet–von Neumann–Jordan)**, from the Comments on Chapter 5. If the norm
of a real normed space `E` satisfies the parallelogram law (1), then it is a Hilbert norm: there
is a scalar product on `E` with `‖u‖ = (u, u)^{1/2}` for all `u` (the class
`InnerProductSpace ℝ E` includes that identity). Mathlib's `InnerProductSpace.ofNorm` is the
polarization construction of the book's Exercise 5.1. -/
theorem theorem_5_12 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ∀ x y : E, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    Nonempty (InnerProductSpace ℝ E) :=
  ⟨InnerProductSpace.ofNorm ℝ fun x y => by simpa only [← pow_two] using h x y⟩

end Brezis.Chapter05

end
