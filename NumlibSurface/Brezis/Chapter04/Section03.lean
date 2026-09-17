import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.MeasureTheory.Function.LpSpace.Clarkson
import Numlib.MeasureTheory.Function.LpSpace.Duality
import NumlibSurface.Brezis.Chapter04.Section02

/-!
# Brezis §4.3: reflexivity, separability, dual of `L^p`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §4.3, over a σ-finite measure space `(α, μ)` (the
chapter's standing assumption (iii)) and real scalars. The three cases of the section:
(A) `1 < p < ∞` — reflexivity (Theorem 4.10 with its three steps), Clarkson's second inequality
(Remark 3), the Riesz representation theorem (Theorem 4.11, Remark 4), density of `C_c`
(Theorem 4.12) and separability (Theorem 4.13); (B) `p = 1` — the dual `(L^1)^* = L^∞`
(Theorem 4.14, Remark 5) and non-reflexivity (Remark 6); (C) `p = ∞` — weak-∗ compactness of the
unit ball, weak-∗ sequential compactness on subsets of `ℝ^N`, non-reflexivity, a functional not
given by an `L^1` function, and non-separability (Lemma 4.2, Remark 8).

The backbone behind it is `Numlib/MeasureTheory/Function/LpSpace/{Clarkson, Duality}`:
`Lp.instUniformConvexSpace`, `Lp.toDual` (the isometry `T` of Theorem 4.10, Step 3),
`Lp.toDual_surjective` (Theorems 4.11 and 4.14 at once, proved by Radon–Nikodym), `Lp.dualEquiv`,
`Lp.instIsReflexive` (proved from the duality, not from Milman–Pettis) and
`Lp.not_surjective_toDual_top`. Theorem 4.13 is Mathlib's `Lp.SecondCountableTopology`. The
negative results are stated, as the book proves them, for a nonempty open `Ω ⊆ ℝ^N`, `N ≥ 1`
(for `N = 0` every `L^p` is one-dimensional and the statements are false), with Lebesgue
measure; Remark 6 is proved from `Lp.not_surjective_toDual_top` rather than by the book's
weak-compactness argument.

## Main results

* `theorem_4_10`, `theorem_4_10_clarkson`, `theorem_4_10_uniformConvex`, `theorem_4_10_isometry`,
  `remark_4_3` — reflexivity and uniform convexity of `L^p`, `1 < p < ∞`.
* `theorem_4_11`, `remark_4_4`, `theorem_4_14`, `remark_4_5` — `(L^p)^* = L^{p'}`, `1 ≤ p < ∞`.
* `theorem_4_12`, `separableMeasureSpace_of_secondCountable`, `theorem_4_13`,
  `theorem_4_13_subset` — density of `C_c` and separability.
* `remark_4_6`, `lInfty_not_isReflexive` — `L^1(Ω)` and `L^∞(Ω)` are not reflexive.
* `lInfty_weakStar_isCompact_closedBall`, `lInfty_exists_subseq_weakStar_tendsto` — the weak-∗
  compactness properties of `L^∞`.
* `exists_strongDual_top_apply_eq`, `exists_strongDual_lInfty_not_integral` — a functional on
  `L^∞` extending `f ↦ f 0` on `C_c`, which is not an integral against an `L^1` function.
* `lemma_4_2`, `remark_4_8` — `L^∞(Ω)` is not separable.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-! ### A. `1 < p < ∞`: reflexivity and uniform convexity -/

/-- **Theorem 4.10.** `L^p` is reflexive for `1 < p < ∞`. The backbone instance
`MeasureTheory.Lp.instIsReflexive`, proved from the Riesz representation theorem; the book's
route — Clarkson's inequality, uniform convexity, Milman–Pettis for `2 ≤ p`, and the isometry
into `(L^{p'})^*` with Corollary 3.21 for `p ≤ 2` — is recorded in the three step nodes
`theorem_4_10_clarkson`, `theorem_4_10_uniformConvex` and `theorem_4_10_isometry`. -/
theorem theorem_4_10 [SigmaFinite μ] [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (Lp ℝ p μ) := by
  have := Fact.mk hp
  have := Fact.mk hp'
  infer_instance

/-- **Theorem 4.10, Step 1 (Clarkson's first inequality).** For `2 ≤ p < ∞` and `f, g ∈ L^p`,
`‖(f + g) / 2‖_p ^ p + ‖(f - g) / 2‖_p ^ p ≤ (‖f‖_p ^ p + ‖g‖_p ^ p) / 2` (8), which reduces to
its pointwise form (9) `|(a + b) / 2| ^ p + |(a - b) / 2| ^ p ≤ (|a| ^ p + |b| ^ p) / 2`. -/
theorem theorem_4_10_clarkson (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    (∀ f g : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal + ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ p.toReal ≤
      (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) / 2) ∧
    ∀ a b : ℝ, |(a + b) / 2| ^ p.toReal + |(a - b) / 2| ^ p.toReal ≤
      (|a| ^ p.toReal + |b| ^ p.toReal) / 2 :=
  ⟨Lp.clarkson_of_two_le hp hp',
    Real.clarkson_pointwise_of_two_le (by simpa using ENNReal.toReal_mono hp' hp)⟩

/-- **Theorem 4.10, Step 2.** For `2 ≤ p < ∞`, `L^p` is uniformly convex: if `‖f‖_p ≤ 1`,
`‖g‖_p ≤ 1` and `‖f - g‖_p > ε`, then `‖(f + g) / 2‖_p < 1 - δ` with the book's modulus
`δ = 1 - [1 - (ε / 2) ^ p] ^ (1 / p)`, by Clarkson's first inequality. "And thus reflexive by
Theorem 3.31" is chapter 3's Milman–Pettis theorem applied to this instance. -/
theorem theorem_4_10_uniformConvex [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    UniformConvexSpace (Lp ℝ p μ) ∧
    ∀ ε > 0, ∀ f g : Lp ℝ p μ, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε < ‖f - g‖ →
      ‖(2 : ℝ)⁻¹ • (f + g)‖ < (1 - (ε / 2) ^ p.toReal) ^ (1 / p.toReal) := by
  have h1 : Fact (1 < p) := ⟨ENNReal.one_lt_two.trans_le hp⟩
  have h2 : Fact (p ≠ ∞) := ⟨hp'⟩
  refine ⟨inferInstance, fun ε hε f g hf hg hfg => ?_⟩
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp'
  have hc := Lp.clarkson_of_two_le hp hp' f g
  have hA : 0 ≤ ‖(2 : ℝ)⁻¹ • (f + g)‖ := norm_nonneg _
  have hB : ‖(2 : ℝ)⁻¹ • (f - g)‖ = ‖f - g‖ / 2 := by
    rw [norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
  have hε2 : ε / 2 < ‖(2 : ℝ)⁻¹ • (f - g)‖ := by rw [hB]; linarith
  have h1' : (ε / 2) ^ p.toReal < ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ p.toReal :=
    Real.rpow_lt_rpow (by positivity) hε2 hP
  have hfp : ‖f‖ ^ p.toReal ≤ 1 := Real.rpow_le_one (norm_nonneg _) hf hP.le
  have hgp : ‖g‖ ^ p.toReal ≤ 1 := Real.rpow_le_one (norm_nonneg _) hg hP.le
  have key : ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal < 1 - (ε / 2) ^ p.toReal := by linarith
  calc ‖(2 : ℝ)⁻¹ • (f + g)‖ = (‖(2 : ℝ)⁻¹ • (f + g)‖ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [one_div, Real.rpow_rpow_inv hA hP.ne']
    _ < (1 - (ε / 2) ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_lt_rpow (by positivity) key (by positivity)

/-- **Theorem 4.10, Step 3.** For conjugate exponents `p, p'`, the operator
`T : L^p → (L^{p'})^*`, `⟨T u, f⟩ = ∫ u f`, satisfies `‖T u‖ = ‖u‖_p` (11), so it is an isometry
onto a closed subspace of `(L^{p'})^*`. The backbone's `MeasureTheory.Lp.toDual ℝ p' p μ`; the
book's last sentence (`L^p` reflexive for `1 < p ≤ 2` by Corollary 3.21 and Proposition 3.20)
is not needed, `theorem_4_10` taking the backbone instance. -/
theorem theorem_4_10_isometry [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] :
    (∀ u : Lp ℝ p μ, ‖Lp.toDual ℝ q p μ u‖ = ‖u‖) ∧
    (∀ (u : Lp ℝ p μ) (f : Lp ℝ q μ), Lp.toDual ℝ q p μ u f = ∫ x, u x * f x ∂μ) ∧
    IsClosed (Set.range (Lp.toDual ℝ q p μ)) :=
  ⟨fun u => (Lp.toDual ℝ q p μ).norm_map u, fun u f => Lp.toDual_apply u f,
    (Lp.toDual ℝ q p μ).isometry.isUniformInducing.isComplete_range.isClosed⟩

/-- **Remark 3 (Clarkson's second inequality).** For `1 < p ≤ 2` with conjugate exponent `p'`
and `f, g ∈ L^p`,
`‖(f + g) / 2‖_p ^ p' + ‖(f - g) / 2‖_p ^ p' ≤ ((‖f‖_p ^ p + ‖g‖_p ^ p) / 2) ^ (1 / (p - 1))`
(Problem 20, inequality (6), divided by `2 ^ p'`), and consequently `L^p` is uniformly convex
for `1 < p ≤ 2` as well. -/
theorem remark_4_3 [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 1 < p) (hp2 : p ≤ 2) :
    (∀ f g : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • (f + g)‖ ^ q.toReal + ‖(2 : ℝ)⁻¹ • (f - g)‖ ^ q.toReal ≤
      ((‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) / 2) ^ (1 / (p.toReal - 1))) ∧
    UniformConvexSpace (Lp ℝ p μ) := by
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top (by simp) hp2
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
  refine ⟨fun f g => ?_, ?_⟩
  · have hc := Lp.clarkson_of_le_two (q := q) hp hp2 f g
    have hdiv : q.toReal / p.toReal = q.toReal - 1 := hPQ.symm.div_conj_eq_sub_one
    have hP1 : 1 < p.toReal := hPQ.lt
    have h1 : 1 / (p.toReal - 1) = q.toReal / p.toReal := by
      rw [hdiv, hPQ.conjugate_eq]
      have hP0 : p.toReal - 1 ≠ 0 := by linarith
      field_simp
      ring
    have hn2 : ∀ x : Lp ℝ p μ, ‖(2 : ℝ)⁻¹ • x‖ = ‖x‖ / 2 := fun x => by
      rw [norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
    rw [h1, hn2, hn2, Real.div_rpow (norm_nonneg _) (by norm_num),
      Real.div_rpow (norm_nonneg _) (by norm_num), ← add_div,
      Real.div_rpow (by positivity) (by norm_num)]
    have h2Q : (2 : ℝ) ^ q.toReal = 2 ^ (q.toReal / p.toReal) * 2 := by
      rw [← Real.rpow_add_one two_ne_zero]
      congr 1
      linarith
    rw [h2Q, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (‖f + g‖ ^ q.toReal + ‖f - g‖ ^ q.toReal) * 2 ^ (q.toReal / p.toReal)
        ≤ 2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
          2 ^ (q.toReal / p.toReal) := by gcongr
      _ = (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q.toReal / p.toReal) *
          (2 ^ (q.toReal / p.toReal) * 2) := by ring
  · have := Fact.mk hp
    have := Fact.mk hp'
    infer_instance

/-! ### A. `1 < p < ∞`: the dual, density, separability -/

/-- **Theorem 4.11 (Riesz representation theorem).** For `1 ≤ p < ∞` with conjugate exponent
`p'` and `φ ∈ (L^p)^*`, there is a unique `u ∈ L^{p'}` with `⟨φ, f⟩ = ∫ u f` for all `f ∈ L^p`,
and `‖u‖_{p'} = ‖φ‖`. The book states it for `1 < p < ∞` and proves it from reflexivity; the
backbone (`MeasureTheory.Lp.toDual_surjective`) proves it by Radon–Nikodym for `1 ≤ p < ∞`,
so that Theorem 4.14 is the case `p = 1`. -/
theorem theorem_4_11 [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp' : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃! u : Lp ℝ q μ, (∀ f : Lp ℝ p μ, φ f = ∫ x, u x * f x ∂μ) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := Lp.toDual_surjective (𝕜 := ℝ) (μ := μ) (p := p) (q := q) hp' φ
  refine ⟨u, ⟨fun f => by rw [← hu, Lp.toDual_apply], by rw [← hu, LinearIsometry.norm_map]⟩,
    fun v ⟨hv, _⟩ => (Lp.toDual ℝ p q μ).injective ?_⟩
  rw [hu]
  ext f
  rw [Lp.toDual_apply, hv f]

/-- **Remark 4.** The identification `(L^p)^* = L^{p'}`, `1 ≤ p < ∞`: `u ↦ (f ↦ ∫ u f)` is a
linear surjective isometry `L^{p'} → (L^p)^*` (`MeasureTheory.Lp.dualEquiv`). -/
theorem remark_4_4 [SigmaFinite μ] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp' : p ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ),
      ∀ (u : Lp ℝ q μ) (f : Lp ℝ p μ), e u f = ∫ x, u x * f x ∂μ :=
  ⟨Lp.dualEquiv ℝ p q μ hp', fun u f => Lp.dualEquiv_apply hp' u f⟩

/-- **Theorem 4.12.** `C_c(ℝ^N)` is dense in `L^p(ℝ^N)`, `1 ≤ p < ∞`: the classes of
continuous compactly supported functions form a dense subset. Mathlib's
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, which does not follow the book's proof by
truncation. -/
theorem theorem_4_12 {N : ℕ} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {g : Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin N))) |
      ∃ φ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧
        ⇑g =ᵐ[volume] φ} := by
  refine Metric.dense_iff.2 fun f ε hε => ?_
  obtain ⟨φ, hφs, hφε, hφc, hφp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.2 (by positivity)).ne'
  refine ⟨hφp.toLp φ, ?_, φ, hφc, hφs, hφp.coeFn_toLp⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def]
  calc (eLpNorm (⇑f - ⇑(hφp.toLp φ)) p volume).toReal
      = (eLpNorm (⇑f - φ) p volume).toReal := by
        congr 1
        exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub hφp.coeFn_toLp)
    _ ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hφε
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := half_lt_self hε

/-- **The definition of a separable measure space, and the example following it.** The book's
"separable measure space" (a countable family generating the σ-algebra) is Mathlib's
`MeasurableSpace.CountablyGenerated`; the example says that `ℝ^N`, and more generally any
separable metric space with its Borel σ-algebra, is a separable measure space. -/
theorem separableMeasureSpace_of_secondCountable (N : ℕ) (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    MeasurableSpace.CountablyGenerated (EuclideanSpace ℝ (Fin N)) ∧
      MeasurableSpace.CountablyGenerated X :=
  ⟨inferInstance, inferInstance⟩

/-- **Theorem 4.13.** If `Ω` is a separable measure space (and σ-finite), then `L^p(Ω)` is
separable for `1 ≤ p < ∞`. The book proves only the case `Ω = ℝ^N`; Mathlib's
`Lp.SecondCountableTopology` has the general case. -/
theorem theorem_4_13 [MeasurableSpace.CountablyGenerated α] [SigmaFinite μ] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : TopologicalSpace.SeparableSpace (Lp ℝ p μ) := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (Lp ℝ p μ) := Lp.SecondCountableTopology
  infer_instance

/-- **The remark after Theorem 4.13.** `L^p(Ω)` is separable for every subset `Ω ⊆ ℝ^N`,
`1 ≤ p < ∞` (the book asks `Ω` measurable and goes through the extension by zero; here
`L^p(Ω)` is `L^p` of the restricted measure, to which Theorem 4.13 applies directly). -/
theorem theorem_4_13_subset {N : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin N))) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : TopologicalSpace.SeparableSpace (Lp ℝ p (volume.restrict Ω)) :=
  theorem_4_13 hp

/-! ### B. `p = 1` -/

/-- **Theorem 4.14 (Riesz representation theorem, `p = 1`).** For `φ ∈ (L^1)^*` there is a
unique `u ∈ L^∞` with `⟨φ, f⟩ = ∫ u f` for all `f ∈ L^1`, and `‖u‖_∞ = ‖φ‖`. The case `p = 1`
of `theorem_4_11`. -/
theorem theorem_4_14 [SigmaFinite μ] (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃! u : Lp ℝ ∞ μ, (∀ f : Lp ℝ 1 μ, φ f = ∫ x, u x * f x ∂μ) ∧ ‖u‖ = ‖φ‖ :=
  theorem_4_11 ENNReal.one_ne_top φ

/-- **Remark 5.** The identification `(L^1)^* = L^∞`: `u ↦ (f ↦ ∫ u f)` is a linear surjective
isometry `L^∞ → (L^1)^*`. -/
theorem remark_4_5 [SigmaFinite μ] :
    ∃ e : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ),
      ∀ (u : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ), e u f = ∫ x, u x * f x ∂μ :=
  ⟨Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top, fun u f => Lp.dualEquiv_apply _ u f⟩

/-- **Remark 6.** `L^1(Ω)` is not reflexive, for a nonempty open `Ω ⊆ ℝ^N` (`N ≥ 1`), the case
the book proves in full. Proof (not the book's weak-compactness argument): if `L^1` were
reflexive then, through `(L^1)^* = L^∞`, every functional on `L^∞` would be the evaluation at
some `u ∈ L^1`, i.e. `f ↦ ∫ u f`; but `(L^∞)^*` is strictly larger than `L^1`
(`MeasureTheory.Lp.not_surjective_toDual_top`, the concrete functional of
`exists_strongDual_lInfty_not_integral`). The general "unless `Ω` consists of finitely many
atoms" is not formalized. -/
theorem remark_4_6 {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) : ¬ NormedSpace.IsReflexive ℝ (Lp ℝ 1 (volume.restrict Ω)) := by
  intro h
  refine Lp.not_surjective_toDual_top volume hΩ hne fun ψ => ?_
  set e := Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top with he
  obtain ⟨u, hu⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ)
    (V := Lp ℝ 1 (volume.restrict Ω)) (ψ.comp (e.symm.toContinuousLinearEquiv :
      StrongDual ℝ (Lp ℝ 1 (volume.restrict Ω)) →L[ℝ] Lp ℝ ∞ (volume.restrict Ω)))
  refine ⟨u, ?_⟩
  ext f
  have := DFunLike.congr_fun hu (e f)
  rw [NormedSpace.dual_def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply] at this
  rw [Lp.toDual_apply, ← this, he, Lp.dualEquiv_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ### C. `p = ∞` -/

/-- **§4.3 C (i).** The closed unit ball of `L^∞` is compact in the weak-∗ topology
`σ(L^∞, L^1)`: through the identification `L^∞ = (L^1)^*` of Remark 5, its image is the closed
unit ball of `(L^1)^*` in the weak-∗ topology, compact by Theorem 3.16 (Banach–Alaoglu,
`WeakDual.isCompact_closedBall`). -/
theorem lInfty_weakStar_isCompact_closedBall [SigmaFinite μ] :
    IsCompact ((fun u : Lp ℝ ∞ μ =>
      StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1) := by
  have h : (fun u : Lp ℝ ∞ μ =>
      StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1 =
        WeakDual.toStrongDual ⁻¹' closedBall 0 1 := by
    rw [show (fun u : Lp ℝ ∞ μ =>
        StrongDual.toWeakDual (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top u)) '' closedBall 0 1 =
        StrongDual.toWeakDual '' (Lp.dualEquiv ℝ 1 ∞ μ ENNReal.one_ne_top '' closedBall 0 1) from
        (Set.image_image _ _ _).symm, LinearIsometryEquiv.image_closedBall, map_zero]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual] using hy
    · intro hx
      exact ⟨WeakDual.toStrongDual x, hx, WeakDual.toWeakDual_toStrongDual x⟩
  rw [h]
  exact WeakDual.isCompact_closedBall 0 1

/-- **§4.3 C (ii).** For `Ω ⊆ ℝ^N` and a bounded sequence `fₙ` in `L^∞(Ω)`, there are a
subsequence `f_{nₖ}` and `f ∈ L^∞(Ω)` with `f_{nₖ} ⇀ f` in the weak-∗ topology `σ(L^∞, L^1)`,
i.e. `∫ f_{nₖ} g → ∫ f g` for every `g ∈ L^1(Ω)`: Corollary 3.30 (the sequential Banach–Alaoglu
theorem for the dual of the separable space `L^1(Ω)`, `WeakDual.isSeqCompact_closedBall`)
through the identification `L^∞ = (L^1)^*` of Remark 5. -/
theorem lInfty_exists_subseq_weakStar_tendsto {N : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (f : ℕ → Lp ℝ ∞ (volume.restrict Ω)) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℝ ∞ (volume.restrict Ω)), StrictMono φ ∧
      ∀ h : Lp ℝ 1 (volume.restrict Ω),
        Tendsto (fun k => ∫ x, f (φ k) x * h x ∂(volume.restrict Ω)) atTop
          (𝓝 (∫ x, g x * h x ∂(volume.restrict Ω))) := by
  have : TopologicalSpace.SeparableSpace (Lp ℝ 1 (volume.restrict Ω)) :=
    theorem_4_13_subset Ω ENNReal.one_ne_top
  set e := Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top with he
  have hmem : ∀ n, StrongDual.toWeakDual (e (f n)) ∈
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (Lp ℝ 1 (volume.restrict Ω))) C :=
    fun n => by
      rw [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual, mem_closedBall_zero_iff,
        e.norm_map]
      exact hf n
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ (Lp ℝ 1 (volume.restrict Ω))
    0 C hmem
  refine ⟨φ, e.symm (WeakDual.toStrongDual a), hφ, fun h => ?_⟩
  have key := tendsto_iff_forall_eval_tendsto_topDualPairing.1 hlim h
  simp only [Function.comp_apply] at key
  have h1 : ∀ k, (StrongDual.toWeakDual (e (f (φ k))) : WeakDual ℝ (Lp ℝ 1 (volume.restrict Ω))) h
      = ∫ x, f (φ k) x * h x ∂(volume.restrict Ω) := fun k => by
    rw [StrongDual.toWeakDual_apply, he, Lp.dualEquiv_apply]
  have h2 : a h = ∫ x, (e.symm (WeakDual.toStrongDual a)) x * h x ∂(volume.restrict Ω) := by
    have := Lp.dualEquiv_apply (𝕜 := ℝ) (μ := volume.restrict Ω) (p := 1) (q := ∞)
      ENNReal.one_ne_top (e.symm (WeakDual.toStrongDual a)) h
    rw [← he, e.apply_symm_apply] at this
    exact this
  have key' : Tendsto (fun k => ∫ x, f (φ k) x * h x ∂(volume.restrict Ω)) atTop (𝓝 (a h)) :=
    key.congr h1
  rw [h2] at key'
  exact key'

/-- **§4.3 C, non-reflexivity.** `L^∞(Ω)` is not reflexive, for a nonempty open `Ω ⊆ ℝ^N`
(`N ≥ 1`): `L^∞ = (L^1)^*` (Remark 5), so `L^1` would be reflexive by Corollary 3.21
(`NormedSpace.isReflexive_of_isReflexive_strongDual`), contradicting Remark 6. -/
theorem lInfty_not_isReflexive {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ NormedSpace.IsReflexive ℝ (Lp ℝ ∞ (volume.restrict Ω)) := by
  intro h
  have h1 : NormedSpace.IsReflexive ℝ (StrongDual ℝ (Lp ℝ 1 (volume.restrict Ω))) :=
    (NormedSpace.isReflexive_congr
      (Lp.dualEquiv ℝ 1 ∞ (volume.restrict Ω) ENNReal.one_ne_top).toContinuousLinearEquiv).1 h
  exact remark_4_6 hΩ hne NormedSpace.isReflexive_of_isReflexive_strongDual

/-- **The functional `φ` of §4.3 C, general form.** Local helper — it belongs in
`Numlib/MeasureTheory/Function/LpSpace/Duality.lean` as a refinement of
`MeasureTheory.Lp.not_surjective_toDual_top`, whose proof it repeats: for a measure `μ` on a
finite-dimensional real normed space, positive on open sets, without atoms and σ-finite, and a
point `x₀`, there is a functional `φ` on `L^∞(μ)` with `φ f = f x₀` for every continuous
compactly supported `f` (a Hahn–Banach extension of the point evaluation), and `φ` is not
`f ↦ ∫ u f` for any `u ∈ L^1(μ)`: such a `u` would vanish a.e. off `x₀`, hence a.e., while
`φ` is `1` on a bump at `x₀`. -/
theorem exists_strongDual_top_apply_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsOpenPosMeasure] [NullSingletonClass μ] [SigmaFinite μ] (x₀ : G) :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ μ),
      (∀ (f : G → ℝ) (hf : MemLp f ∞ μ), Continuous f → HasCompactSupport f →
        φ (hf.toLp f) = f x₀) ∧
      ∀ u : Lp ℝ 1 μ, Lp.toDual ℝ ∞ 1 μ u ≠ φ := by
  -- continuous compactly supported functions lie in `L^∞`
  have hmem : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → MemLp f ∞ μ := fun f hf hs => by
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
    exact memLp_top_of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  -- an a.e. property with an open exceptional set holds everywhere
  have hall : ∀ {P : G → Prop}, IsOpen {x | ¬ P x} → (∀ᵐ x ∂μ, P x) → ∀ x, P x := by
    intro P hP h x
    rw [ae_iff, hP.measure_eq_zero_iff μ] at h
    by_contra hx
    exact Set.eq_empty_iff_forall_notMem.1 h x hx
  -- the subspace of `L^∞` of classes of continuous compactly supported functions
  let M : Submodule ℝ (Lp ℝ ∞ μ) :=
    { carrier := {g | ∃ f : G → ℝ, Continuous f ∧ HasCompactSupport f ∧ ⇑g =ᵐ[μ] f}
      add_mem' := fun {g₁ g₂} ⟨f₁, hf₁, hs₁, h₁⟩ ⟨f₂, hf₂, hs₂, h₂⟩ =>
        ⟨f₁ + f₂, hf₁.add hf₂, hs₁.add hs₂, (Lp.coeFn_add g₁ g₂).trans (h₁.add h₂)⟩
      zero_mem' := ⟨0, continuous_zero, HasCompactSupport.zero, Lp.coeFn_zero ℝ ∞ μ⟩
      smul_mem' := fun c {g} ⟨f, hf, hs, h⟩ =>
        ⟨c • f, hf.const_smul c, hs.smul_left, (Lp.coeFn_smul c g).trans (h.const_smul c)⟩ }
  choose F hFc hFs hF using fun g : M => g.2
  have hFeq : ∀ (g : M) (f : G → ℝ), Continuous f → ⇑(g : Lp ℝ ∞ μ) =ᵐ[μ] f → F g x₀ = f x₀ :=
    fun g f hf hgf => by
      rw [(Continuous.ae_eq_iff_eq μ (hFc g) hf).1 ((hF g).symm.trans hgf)]
  -- point evaluation at `x₀` on `M`, bounded by the `L^∞` norm
  let δ : M →ₗ[ℝ] ℝ :=
    { toFun := fun g => F g x₀
      map_add' := fun g₁ g₂ => hFeq (g₁ + g₂) (F g₁ + F g₂) ((hFc g₁).add (hFc g₂)) (by
        rw [Submodule.coe_add]
        exact (Lp.coeFn_add _ _).trans ((hF g₁).add (hF g₂)))
      map_smul' := fun c g => hFeq (c • g) (c • F g) ((hFc g).const_smul c) (by
        rw [Submodule.coe_smul]
        exact (Lp.coeFn_smul c _).trans ((hF g).const_smul c)) }
  have hδ : ∀ g : M, ‖δ g‖ ≤ 1 * ‖g‖ := fun g => by
    rw [one_mul]
    refine hall (P := fun x => ‖F g x‖ ≤ ‖g‖)
      (by simp only [not_le]; exact isOpen_lt continuous_const (hFc g).norm) ?_ x₀
    filter_upwards [hF g, Lp.ae_norm_le_norm_top (g : Lp ℝ ∞ μ)] with x hx hx'
    rw [← hx]
    exact hx'
  obtain ⟨φ, hφM, -⟩ := exists_extension_norm_eq M (δ.mkContinuous 1 hδ)
  refine ⟨φ, fun f hf hfc hfs => ?_, fun u hu => ?_⟩
  · have hfM : hf.toLp f ∈ M := ⟨f, hfc, hfs, hf.coeFn_toLp⟩
    rw [hφM ⟨_, hfM⟩]
    exact hFeq ⟨_, hfM⟩ f hfc hf.coeFn_toLp
  -- a bump at `x₀`, on which `φ` is `1`
  let ψ : ContDiffBump x₀ := ⟨1, 2, one_pos, one_lt_two⟩
  have hψ : MemLp ψ ∞ μ := hmem ψ ψ.continuous ψ.hasCompactSupport
  let gψ : M := ⟨hψ.toLp ψ, ψ, ψ.continuous, ψ.hasCompactSupport, hψ.coeFn_toLp⟩
  have hφψ : φ gψ = 1 := by
    rw [hφM gψ]
    change F gψ x₀ = 1
    rw [hFeq gψ ψ ψ.continuous hψ.coeFn_toLp]
    exact ψ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  -- if `φ = ∫ u ·` then `u = 0` a.e. off `x₀`
  have hu0 : ∀ᵐ x ∂μ, x ∈ ({x₀}ᶜ : Set G) → u x = 0 := by
    have huint : Integrable u μ := memLp_one_iff_integrable.1 (Lp.memLp u)
    refine isClosed_singleton.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (huint.locallyIntegrable.locallyIntegrableOn _) fun g hg hgs hgΩ => ?_
    have hgL : MemLp g ∞ μ := hmem g hg.continuous hgs
    have hgM : hgL.toLp g ∈ M := ⟨g, hg.continuous, hgs, hgL.coeFn_toLp⟩
    have h1 : φ (hgL.toLp g) = 0 := by
      rw [hφM ⟨_, hgM⟩]
      change F ⟨_, hgM⟩ x₀ = 0
      rw [hFeq ⟨_, hgM⟩ g hg.continuous hgL.coeFn_toLp]
      exact image_eq_zero_of_notMem_tsupport fun h => (hgΩ h) rfl
    rw [← hu, Lp.toDual_apply] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [hgL.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  -- hence `u = 0` and `φ = 0`, contradicting `φ gψ = 1`
  have hu' : u = 0 := by
    have hx₀' : ∀ᵐ x ∂μ, x ≠ x₀ := by
      rw [ae_iff]
      simp
    have huμ : ∀ᵐ x ∂μ, u x = 0 := by
      filter_upwards [hu0, hx₀'] with x hx hx'
      exact hx hx'
    apply Lp.ext
    filter_upwards [huμ, Lp.coeFn_zero ℝ 1 μ] with x hx hx0
    rw [hx0, hx]
    rfl
  rw [hu', map_zero] at hu
  rw [← hu] at hφψ
  simp at hφψ

/-- **§4.3 C, the concrete functional (17)–(18).** On `L^∞(ℝ^N)`, `N ≥ 1`, there is a
continuous linear functional `φ` with `⟨φ, f⟩ = f 0` for every `f ∈ C_c(ℝ^N)` — a Hahn–Banach
extension of `f ↦ f 0` — and there is no `u ∈ L^1(ℝ^N)` with `⟨φ, f⟩ = ∫ u f` for all
`f ∈ L^∞(ℝ^N)`: `(L^∞)^*` is strictly larger than `L^1`. -/
theorem exists_strongDual_lInfty_not_integral {N : ℕ} [NeZero N] :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ (volume : Measure (EuclideanSpace ℝ (Fin N)))),
      (∀ (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : MemLp f ∞ volume), Continuous f →
        HasCompactSupport f → φ (hf.toLp f) = f 0) ∧
      ¬ ∃ u : Lp ℝ 1 (volume : Measure (EuclideanSpace ℝ (Fin N))),
        ∀ g : Lp ℝ ∞ (volume : Measure (EuclideanSpace ℝ (Fin N))), φ g = ∫ x, u x * g x := by
  obtain ⟨φ, h1, h2⟩ := exists_strongDual_top_apply_eq
    (volume : Measure (EuclideanSpace ℝ (Fin N))) 0
  refine ⟨φ, h1, fun ⟨u, hu⟩ => h2 u ?_⟩
  ext g
  rw [Lp.toDual_apply, hu g]

/-- **Lemma 4.2.** A topological space (the book: a Banach space) with an uncountable family of
pairwise disjoint nonempty open sets is not separable
(Mathlib's `Pairwise.countable_of_isOpen_disjoint`). -/
theorem lemma_4_2 {E : Type*} [TopologicalSpace E] {ι : Type*} [Uncountable ι] (O : ι → Set E)
    (hO : ∀ i, IsOpen (O i)) (hne : ∀ i, (O i).Nonempty)
    (hdisj : Pairwise (Function.onFun Disjoint O)) :
    ¬ TopologicalSpace.SeparableSpace E := fun _ =>
  not_countable (hdisj.countable_of_isOpen_disjoint hO hne)

/-- **Remark 8.** `L^∞(Ω)` is not separable, for a nonempty open `Ω ⊆ ℝ^N` (`N ≥ 1`), the case
the book proves in full: for a ball `B(x₀, r₀) ⊆ Ω`, the classes of the indicator functions of
`B(x₀, r)`, `0 < r < r₀`, are pairwise at distance `1` in `L^∞`, so the balls of radius `1/2`
around them are an uncountable family of pairwise disjoint nonempty open sets (Lemma 4.2). The
general "unless `Ω` consists of finitely many atoms" is not formalized. -/
theorem remark_4_8 {N : ℕ} [NeZero N] {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) : ¬ TopologicalSpace.SeparableSpace (Lp ℝ ∞ (volume.restrict Ω)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  have hfin : ∀ r : ℝ, (volume.restrict Ω) (ball x₀ r) ≠ ∞ := fun r =>
    ((Measure.le_iff'.1 Measure.restrict_le_self _).trans_lt measure_ball_lt_top).ne
  -- the indicator classes
  set χ : Set.Ioo (0 : ℝ) r₀ → Lp ℝ ∞ (volume.restrict Ω) := fun r =>
    indicatorConstLp ∞ measurableSet_ball (hfin r) (1 : ℝ) with hχ
  -- two of them are at distance at least `1`
  have hdist : ∀ r s : Set.Ioo (0 : ℝ) r₀, r ≠ s → 1 ≤ dist (χ r) (χ s) := by
    -- by symmetry it suffices to treat `r < s`
    have key : ∀ r s : Set.Ioo (0 : ℝ) r₀, (r : ℝ) < s → 1 ≤ dist (χ r) (χ s) := by
      intro r s hrs
      rw [dist_comm, Lp.dist_def, hχ]
      have hsub : ball x₀ r ⊆ ball x₀ s := ball_subset_ball hrs.le
      have heq : ⇑(indicatorConstLp ∞ measurableSet_ball (hfin s) (1 : ℝ)) -
          ⇑(indicatorConstLp ∞ measurableSet_ball (hfin r) (1 : ℝ)) =ᵐ[volume.restrict Ω]
          (ball x₀ s \ ball x₀ r).indicator fun _ => (1 : ℝ) := by
        filter_upwards [indicatorConstLp_coeFn (p := ∞)
          (hs := measurableSet_ball (x := x₀) (ε := s)) (hμs := hfin s) (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := ∞) (hs := measurableSet_ball (x := x₀) (ε := r))
          (hμs := hfin r) (c := (1 : ℝ))] with x hx hx'
        rw [Pi.sub_apply, hx, hx', Set.indicator_sdiff hsub]
        rfl
      rw [eLpNorm_congr_ae heq, eLpNorm_exponent_top (aestronglyMeasurable_const.indicator
        (measurableSet_ball.diff measurableSet_ball)), eLpNormEssSup_indicator_const_eq]
      · simp
      -- the annulus has positive measure
      rw [Measure.restrict_apply (measurableSet_ball.diff measurableSet_ball),
        Set.inter_eq_left.2 (Set.sdiff_subset.trans ((ball_subset_ball s.2.2.le).trans hball))]
      have hlt : volume (ball x₀ (r : ℝ)) < volume (ball x₀ (s : ℝ)) := by
        rw [Measure.addHaar_ball volume x₀ r.2.1.le, Measure.addHaar_ball volume x₀ s.2.1.le,
          mul_comm, mul_comm (ENNReal.ofReal _)]
        refine ENNReal.mul_lt_mul_right (measure_ball_pos (volume : Measure (EuclideanSpace ℝ
          (Fin N))) (0 : EuclideanSpace ℝ (Fin N)) one_pos).ne' measure_ball_lt_top.ne ?_
        refine ENNReal.ofReal_lt_ofReal_iff'.2 ⟨pow_lt_pow_left₀ hrs r.2.1.le ?_, pow_pos s.2.1 _⟩
        rw [finrank_euclideanSpace_fin]
        exact NeZero.ne N
      rw [measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne]
      exact (tsub_pos_iff_lt.2 hlt).ne'
    intro r s hrs
    rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.2 hrs) with h | h
    · exact key r s h
    · rw [dist_comm]
      exact key s r h
  have : Uncountable (Set.Ioo (0 : ℝ) r₀) := not_countable_iff.1 fun h => by
    rw [Set.countable_coe_iff, Cardinal.Real.Ioo_countable_iff] at h
    linarith
  refine lemma_4_2 (fun r : Set.Ioo (0 : ℝ) r₀ => ball (χ r) (1 / 2)) (fun _ => isOpen_ball)
    (fun _ => nonempty_ball.2 (by norm_num)) fun r s hrs => ?_
  exact ball_disjoint_ball (le_of_eq_of_le (add_halves _) (hdist r s hrs))

end Brezis.Chapter04
