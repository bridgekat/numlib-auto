/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact`, beside `IsCompactOperator`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous and compact embeddings of normed spaces

A normed space `V` is *continuously embedded* in a normed space `W` when the inclusion `V ⊆ W` is
injective, linear and bounded, `‖v‖_W ≤ c ‖v‖_V`; it is *compactly embedded* when, in addition,
every bounded sequence of `V` has a subsequence whose image converges in `W`. These are the
relations written `V ↪ W` and `V ↪↪ W` in Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.3.6, in which
they are the vocabulary of the Sobolev embedding theorems and of Rellich–Kondrachov.

The inclusion `V ⊆ W` is carried by an arbitrary injective linear map `ι : V →ₗ[𝕜] W` rather than
by a subset relation, because the two spaces carry different norms and the embeddings of interest —
`W^{k,p}(Ω) ↪ L^q(Ω)`, `H^k(Ω) ↪ C(closure Ω)` — are between different types.

## Main definitions

* `IsContinuousEmbedding ι`, the relation `V ↪ W` along `ι`;
* `IsCompactEmbedding ι`, the relation `V ↪↪ W` along `ι`, with the *sequential* compactness
  condition as its definition.

## Main statements

* `isContinuousEmbedding_iff_continuous`: a continuous embedding is exactly an injective continuous
  linear map, the bound `‖ι v‖ ≤ c ‖v‖` being the continuity of a linear map between normed spaces;
* `isCompactEmbedding_iff_isCompactOperator`: a compact embedding is exactly an injective
  `IsCompactOperator`, so the closure properties of compact operators and the Riesz theory apply to
  it. Note that the continuity clause of the definition is not an extra hypothesis on the
  right-hand side: `IsCompactOperator.continuous` makes it automatic.

## Implementation notes

The definition of `IsCompactEmbedding` is the sequential one because that is how the relation is
introduced in the source cited above and how its consumers use it — a bounded sequence in the
finer space is passed to a convergent subsequence in the coarser one. The identification with
`IsCompactOperator`, whose definition is the compactness of the closure of the image of a
neighbourhood of `0`, is the two halves of the Bolzano–Weierstrass theorem in a metrizable space:
`IsCompact.isSeqCompact` one way and `IsSeqCompact.isCompact` the other. Neither space is required
to be complete; the source states the definition for Banach spaces, but completeness enters none of
the arguments here.
-/

open Filter Metric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The continuous embedding `V ↪ W`** along an inclusion `ι : V → W`: the map is injective and
bounded, `‖ι v‖_W ≤ c ‖v‖_V` for some constant `c` and all `v ∈ V`.

This is the relation `V ↪ W` of Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.3.6, equation (7.3.1),
with the book's `V ⊆ W` read as an arbitrary injective linear map because the two spaces carry
different norms. `IsContinuousEmbedding.toContinuousLinearMap` bundles `ι` as a continuous linear
map, which is what the bound says. -/
structure IsContinuousEmbedding (ι : V →ₗ[𝕜] W) : Prop where
  /-- The inclusion is injective: `V` is a subspace of `W`. -/
  injective : Function.Injective ι
  /-- The inclusion is bounded: `‖v‖_W ≤ c ‖v‖_V`. -/
  exists_bound : ∃ c : ℝ, ∀ v : V, ‖ι v‖ ≤ c * ‖v‖

/-- **The compact embedding `V ↪↪ W`** along an inclusion `ι : V → W`: the space `V` is
continuously embedded in `W` and, in addition, every bounded sequence of `V` has a subsequence
whose image converges in `W`.

This is the relation `V ↪↪ W` of Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.3.6.
`isCompactEmbedding_iff_isCompactOperator` identifies it with an injective `IsCompactOperator`. -/
structure IsCompactEmbedding (ι : V →ₗ[𝕜] W) : Prop extends IsContinuousEmbedding ι where
  /-- Every bounded sequence of `V` has a subsequence whose image converges in `W`. -/
  exists_subseq_tendsto : ∀ u : ℕ → V, (∃ M : ℝ, ∀ n, ‖u n‖ ≤ M) →
    ∃ (φ : ℕ → ℕ) (w : W), StrictMono φ ∧ Tendsto (fun n ↦ ι (u (φ n))) atTop (𝓝 w)

namespace IsContinuousEmbedding

variable {ι : V →ₗ[𝕜] W}

/-- The inclusion of a continuous embedding, bundled as a continuous linear map. -/
noncomputable def toContinuousLinearMap (h : IsContinuousEmbedding ι) : V →L[𝕜] W :=
  ι.mkContinuousOfExistsBound h.exists_bound

@[simp]
theorem coe_toContinuousLinearMap (h : IsContinuousEmbedding ι) :
    ⇑h.toContinuousLinearMap = ⇑ι := rfl

/-- The inclusion of a continuous embedding is continuous. -/
theorem continuous (h : IsContinuousEmbedding ι) : Continuous ι :=
  h.toContinuousLinearMap.continuous

end IsContinuousEmbedding

/-- **An injective linear map is a continuous embedding exactly when it is continuous**: the bound
`‖ι v‖ ≤ c ‖v‖` is the continuity of a linear map between normed spaces. -/
theorem isContinuousEmbedding_iff_continuous {ι : V →ₗ[𝕜] W} :
    IsContinuousEmbedding ι ↔ Function.Injective ι ∧ Continuous ι :=
  ⟨fun h ↦ ⟨h.injective, h.continuous⟩,
    fun ⟨hi, hc⟩ ↦ ⟨hi, ‖(⟨ι, hc⟩ : V →L[𝕜] W)‖, (⟨ι, hc⟩ : V →L[𝕜] W).le_opNorm⟩⟩

/-- **A compact embedding is exactly an injective compact operator.** The sequential condition —
every bounded sequence of `V` has a subsequence whose image converges in `W` — is the sequential
form of the compactness of the closure of the image of a ball, which is `IsCompactOperator`; the
two agree because a normed space is metrizable, and there compactness and sequential compactness
coincide.

The continuity clause of `IsCompactEmbedding` is not an extra hypothesis on the right-hand side: a
compact operator is automatically continuous, by `IsCompactOperator.continuous`. -/
theorem isCompactEmbedding_iff_isCompactOperator {ι : V →ₗ[𝕜] W} :
    IsCompactEmbedding ι ↔ Function.Injective ι ∧ IsCompactOperator ι := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc.injective, ?_⟩
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall ι one_pos]
    refine IsSeqCompact.isCompact fun {y} hy ↦ ?_
    have hy' : ∀ n : ℕ, ∃ v : V, ‖v‖ ≤ 1 ∧ dist (y n) (ι v) < 1 / (n + 1) := by
      intro n
      obtain ⟨z, ⟨v, hv, rfl⟩, hz⟩ := Metric.mem_closure_iff.1 (hy n) (1 / (n + 1)) (by positivity)
      exact ⟨v, mem_closedBall_zero_iff.1 hv, hz⟩
    choose v hv hvy using hy'
    obtain ⟨φ, w, hφ, hw⟩ := hs v ⟨1, hv⟩
    refine ⟨w, isClosed_closure.mem_of_tendsto hw (.of_forall fun n ↦
      subset_closure (mem_image_of_mem _ (mem_closedBall_zero_iff.2 (hv _)))),
      φ, hφ, hw.congr_dist ?_⟩
    refine squeeze_zero (g := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]
    refine (hvy (φ n)).le.trans (one_div_le_one_div_of_le (by positivity) ?_)
    have : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.le_apply
    linarith
  · rintro ⟨hi, hK⟩
    refine ⟨⟨hi, ‖(⟨ι, hK.continuous⟩ : V →L[𝕜] W)‖, (⟨ι, hK.continuous⟩ : V →L[𝕜] W).le_opNorm⟩,
      fun u ⟨M, hM⟩ ↦ ?_⟩
    obtain ⟨w, -, φ, hφ, hwφ⟩ :=
      (hK.isCompact_closure_image_closedBall M).tendsto_subseq (x := fun n ↦ ι (u n))
        fun n ↦ subset_closure ⟨u n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
    exact ⟨φ, w, hφ, hwφ⟩

/-- The inclusion of a compact embedding is a compact operator. -/
theorem IsCompactEmbedding.isCompactOperator {ι : V →ₗ[𝕜] W} (h : IsCompactEmbedding ι) :
    IsCompactOperator ι :=
  (isCompactEmbedding_iff_isCompactOperator.1 h).2
