import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Atkinson–Han §1.6: compact sets

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.6: the Heine–Borel theorem and the
Arzelà–Ascoli theorem.

Definition 1.6.1 — compact, sequentially compact, precompact — is Mathlib's `IsCompact`,
`IsSeqCompact` and "the closure is compact"; the equivalence of the first two in a metric space is
`UniformSpace.isCompact_iff_isSeqCompact`, and none of the three is restated here.

These are the two compactness facts §2.8 uses: Heine–Borel is what makes a bounded finite-rank
operator compact (Proposition 2.8.4), and Arzelà–Ascoli is what makes an integral operator with a
continuous kernel compact (§2.8.1) and is the engine of Schauder's theorem.

## Main results

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
open scoped BoundedContinuousFunction

namespace AtkinsonHan.Chapter01

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
continuous functions on a compact `D ⊆ ℝ^d` is precompact in `C(D)` with the uniform norm. -/
theorem theorem_1_6_3 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D)
    {S : Set C(D, ℝ)} {M : ℝ} (hbdd : ∀ f ∈ S, ∀ x, |f x| ≤ M)
    (heqc : Equicontinuous ((↑) : S → D → ℝ)) : IsCompact (closure S) := by
  have _ : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let h : C(D, ℝ) ≃ₜ (D →ᵇ ℝ) :=
    (ContinuousMap.isometryEquivBoundedOfCompact (D : Type _) ℝ).toHomeomorph
  have hu : ∀ g : (h '' S : Set (D →ᵇ ℝ)), h.symm (g : D →ᵇ ℝ) ∈ S := by
    rintro ⟨g, f, hf, rfl⟩
    simpa using hf
  have key : IsCompact (closure (h '' S)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-M) M) isCompact_Icc _ ?_ ?_
    · rintro f x ⟨g, hg, rfl⟩
      exact abs_le.mp (hbdd g hg x)
    · exact heqc.comp (fun g : (h '' S : Set (D →ᵇ ℝ)) =>
        (⟨h.symm (g : D →ᵇ ℝ), hu g⟩ : S))
  have himg : h.symm '' closure (h '' S) = closure S := by
    rw [h.symm.image_closure, ← Set.image_comp]
    simp
  rw [← himg]
  exact key.image h.symm.continuous

end AtkinsonHan.Chapter01
