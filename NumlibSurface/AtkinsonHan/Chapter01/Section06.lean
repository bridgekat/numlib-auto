import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Lemmas
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# Atkinson–Han §1.6: compact sets

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.6: the Heine–Borel theorem and the
Arzelà–Ascoli theorem.

Definition 1.6.1 — compact, sequentially compact, precompact — is Mathlib's `IsCompact`,
`IsSeqCompact` and "the closure is compact"; the equivalence of the first two in a metric space is
`isCompact_iff_isSeqCompact`, and all three are restated here under the book's number.

These are the two compactness facts §2.8 uses: Heine–Borel is what makes a bounded finite-rank
operator compact (Proposition 2.8.4), and Arzelà–Ascoli is what makes an integral operator with a
continuous kernel compact (§2.8.1) and is the engine of Schauder's theorem.

## Main definitions

* `definition_1_6_1_precompact` — a set is precompact when its closure is compact.

## Main results

* `definition_1_6_1` — the two readings of compactness the book gives, the open-cover one of
  clause (a) and the sequential one of clause (b), agree in a normed space.
* `theorem_1_6_2`, `theorem_1_6_2_converse` — Heine–Borel, and Riesz's converse.
* `theorem_1_6_3` — Arzelà–Ascoli.

## Conventions

The book states the hypothesis of Theorem 1.6.3 as a common modulus of continuity,
`|f x - f y| ≤ c(ε)` for `‖x - y‖ ≤ ε` with `c(ε) → 0`, which is `UniformEquicontinuous`. The
statement below assumes only `Equicontinuous`, which is weaker and, on the compact domain the
theorem is about, equivalent; `UniformEquicontinuous.equicontinuous` converts.

## Not formalized here

The converse half of Theorem 1.6.3 — a precompact subset of `C(D)` is uniformly bounded and
equicontinuous — is true and elementary but has no Mathlib form to specialize; only the direction
the book uses is proved.
-/

open Bornology Metric Set

universe u

namespace AtkinsonHan.Chapter01

/-! ### Definition 1.6.1: compact and precompact sets -/

/-- **Definition 1.6.1** (a), (b). A subset `S` of a normed space is *compact* when every open
covering `S ⊆ ⋃ Uα` by open sets has a finite subcover; equivalently, when every sequence in `S`
has a subsequence converging to an element of `S`.

These are Mathlib's `IsCompact` and `IsSeqCompact`; clause (a) is the general topological
definition and clause (b) the usual metric-space one, and the statement below is that `IsCompact`
is both. -/
theorem definition_1_6_1 {V : Type u} [NormedAddCommGroup V] (S : Set V) :
    (IsCompact S ↔ ∀ (ι : Type u) (U : ι → Set V), (∀ i, IsOpen (U i)) → S ⊆ ⋃ i, U i →
        ∃ t : Finset ι, S ⊆ ⋃ i ∈ t, U i) ∧
      (IsCompact S ↔ IsSeqCompact S) := by
  refine ⟨⟨fun h ι U hU hcov => isCompact_iff_finite_subcover.mp h U hU hcov, fun h => ?_⟩,
    isCompact_iff_isSeqCompact⟩
  exact isCompact_iff_finite_subcover.mpr fun {ι} U hU hcov => h ι U hU hcov

/-- **Definition 1.6.1** (c). A set `S` is *precompact* when its closure `S̄` is compact. The book
states it for a subset of a normed space; nothing but the topology is used, so it is stated here
for a subset of a topological space, which is how §2.8 and Theorem 1.6.3 need it. -/
def definition_1_6_1_precompact {V : Type*} [TopologicalSpace V] (S : Set V) : Prop :=
  IsCompact (closure S)

/-! ### Theorem 1.6.2: the Heine–Borel theorem -/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Heine–Borel theorem** (Theorem 1.6.2). In a finite-dimensional normed space a set is compact
if and only if it is closed and bounded. -/
theorem theorem_1_6_2 [FiniteDimensional 𝕜 V] (S : Set V) :
    IsCompact S ↔ IsClosed S ∧ IsBounded S :=
  have : ProperSpace V := FiniteDimensional.proper_rclike 𝕜 V
  isCompact_iff_isClosed_bounded

/-- **Riesz's theorem** (the converse remark after Theorem 1.6.2). A normed space in which every
closed bounded set is compact is finite-dimensional. -/
theorem theorem_1_6_2_converse (h : ∀ S : Set V, IsClosed S → IsBounded S → IsCompact S) :
    FiniteDimensional 𝕜 V :=
  FiniteDimensional.of_isCompact_closedBall₀ 𝕜 one_pos
    (h _ isClosed_closedBall isBounded_closedBall)

/-! ### Theorem 1.6.3: the Arzelà–Ascoli theorem -/

/-- **Arzelà–Ascoli theorem** (Theorem 1.6.3). A uniformly bounded, equicontinuous set of
continuous functions on a compact `D ⊆ ℝ^d` is precompact in `C(D)` with the uniform norm.

This is the backbone's `ContinuousMap.isCompact_closure_of_forall_norm_le`, which says the same for
maps from any compact space into a proper normed space; Mathlib states Arzelà–Ascoli for the
bounded continuous functions `D →ᵇ ℝ`, and the transport to `C(D, ℝ)` is what the backbone adds. -/
theorem theorem_1_6_3 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D)
    {S : Set C(D, ℝ)} {M : ℝ} (hbdd : ∀ f ∈ S, ∀ x, |f x| ≤ M)
    (heqc : Equicontinuous ((↑) : S → D → ℝ)) : definition_1_6_1_precompact S :=
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  ContinuousMap.isCompact_closure_of_forall_norm_le hbdd heqc

end AtkinsonHan.Chapter01
