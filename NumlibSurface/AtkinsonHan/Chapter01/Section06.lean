/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Lemmas
import Numlib.Topology.ContinuousMap.ArzelaAscoli

/-!
# Atkinson and Han, Section 1.6: Compact sets

This module formalizes §1.6 of [han2009theoretical]: compact, sequentially compact and precompact
sets, the Heine–Borel theorem with Riesz's converse, and the Arzelà–Ascoli theorem. In a
finite-dimensional normed space a set is compact if and only if it is closed and bounded, and a
normed space with this property is finite dimensional. A uniformly bounded and equicontinuous set of
continuous functions on a compact set $D \subseteq \mathbb{R}^d$ is precompact in $C(D)$.

Definition 1.6.1 is Mathlib's `IsCompact`, `IsSeqCompact` and the condition that the closure is
compact; the equivalence of the first two in a metric space is `isCompact_iff_isSeqCompact`. These
are the two compactness facts that §2.8 uses: the Heine–Borel theorem makes a bounded operator of
finite rank compact (Proposition 2.8.4), and the Arzelà–Ascoli theorem makes an integral operator
with a continuous kernel compact (§2.8.1) and underlies Schauder's theorem. The proof of the
Arzelà–Ascoli theorem is in the backbone module `Numlib.Topology.ContinuousMap.ArzelaAscoli`.

## Main definitions

* Definition 1.6.1(c), `AtkinsonHan.Chapter01.definition_1_6_1_precompact`: a set is precompact if
  its closure is compact.

## Main results

* Definition 1.6.1(a), (b), `AtkinsonHan.Chapter01.definition_1_6_1`: compactness by open covers and
  sequential compactness both characterize `IsCompact` in a normed space.
* Theorem 1.6.2, `AtkinsonHan.Chapter01.theorem_1_6_2`: the Heine–Borel theorem.
* Theorem 1.6.2, `AtkinsonHan.Chapter01.theorem_1_6_2_converse`: Riesz's theorem, the converse that
  the book remarks after Theorem 1.6.2.
* Theorem 1.6.3, `AtkinsonHan.Chapter01.theorem_1_6_3`: the Arzelà–Ascoli theorem.

## Implementation notes

* The book states the hypothesis of Theorem 1.6.3 as a common modulus of continuity:
  $|f(x) - f(y)| \le c(\varepsilon)$ for $\|x - y\| \le \varepsilon$, with $c(\varepsilon) \to 0$ as
  $\varepsilon \to 0$. This is `UniformEquicontinuous`. The statement assumes only `Equicontinuous`,
  which is weaker and, on a compact domain, equivalent; `UniformEquicontinuous.equicontinuous`
  converts.

## Deviations from the source

* **Definition 1.6.1** (generalization). The compactness criteria apply to normed additive
  commutative groups. Precompactness by compact closure applies in any topological space.

## Not formalized

* **The converse half of Theorem 1.6.3**, that a precompact subset of $C(D)$ is uniformly bounded
  and equicontinuous. It is true and elementary, but Mathlib has no form of it to specialize; only
  the direction that the book uses is proved.
-/

open Bornology Metric Set

universe u

namespace AtkinsonHan.Chapter01

/-! ### Definition 1.6.1: compact and precompact sets -/

/-- **Definition 1.6.1(a), (b)** of [han2009theoretical]. Let $S$ be a subset of a normed space $V$.
Then $S$ is **compact** if every covering $S \subseteq \bigcup_\alpha U_\alpha$ by open sets
$U_\alpha$ has a finite subcover; equivalently, if every sequence in $S$ has a subsequence that
converges to an element of $S$. The theorem states that `IsCompact S` is equivalent to each of
the two conditions.

The second condition is `IsSeqCompact S`. Clause (a) is the general topological definition, and
clause (b) is the usual definition in a metric space. The covering test uses index types in the
same universe as $V$. This suffices since each member of a cover is an open subset of $V$.

**Generalization.** Both criteria apply in normed additive commutative groups. -/
theorem definition_1_6_1 {V : Type u} [NormedAddCommGroup V] (S : Set V) :
    (IsCompact S ↔ ∀ (ι : Type u) (U : ι → Set V), (∀ i, IsOpen (U i)) → S ⊆ ⋃ i, U i →
        ∃ t : Finset ι, S ⊆ ⋃ i ∈ t, U i) ∧
      (IsCompact S ↔ IsSeqCompact S) := by
  refine ⟨⟨fun h ι U hU hcov => isCompact_iff_finite_subcover.mp h U hU hcov, fun h => ?_⟩,
    isCompact_iff_isSeqCompact⟩
  exact isCompact_iff_finite_subcover.mpr fun {ι} U hU hcov => h ι U hU hcov

/-- **Definition 1.6.1(c)** of [han2009theoretical]. A set $S$ is **precompact** if its closure
$\bar S$ is compact.

The book states the definition for a subset of a normed space. The definition uses only the
topology, so it is stated for a subset of a topological space, which is how §2.8 and Theorem
1.6.3 use it.

**Reading.** Compact closure defines precompactness on any topological space.
-/
def definition_1_6_1_precompact {V : Type*} [TopologicalSpace V] (S : Set V) : Prop :=
  IsCompact (closure S)

/-! ### Theorem 1.6.2: the Heine–Borel theorem -/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Theorem 1.6.2** of [han2009theoretical] (Heine–Borel theorem). Let $V$ be a finite-dimensional
normed space over $\mathbb{K}$. A set $S \subseteq V$ is compact if and only if it is closed and
bounded. -/
theorem theorem_1_6_2 [FiniteDimensional 𝕜 V] (S : Set V) :
    IsCompact S ↔ IsClosed S ∧ IsBounded S :=
  have : ProperSpace V := FiniteDimensional.proper_rclike 𝕜 V
  isCompact_iff_isClosed_bounded

/-- **Theorem 1.6.2** of [han2009theoretical], the converse in the remark after the theorem (Riesz's
theorem). Let $V$ be a normed space over $\mathbb{K}$ in which every closed and bounded set is
compact. Then $V$ is finite dimensional. -/
theorem theorem_1_6_2_converse (h : ∀ S : Set V, IsClosed S → IsBounded S → IsCompact S) :
    FiniteDimensional 𝕜 V :=
  FiniteDimensional.of_isCompact_closedBall₀ 𝕜 one_pos
    (h _ isClosed_closedBall isBounded_closedBall)

/-! ### Theorem 1.6.3: the Arzelà–Ascoli theorem -/

/-- **Theorem 1.6.3** of [han2009theoretical] (Arzelà–Ascoli theorem). Let
$D \subseteq \mathbb{R}^d$ be compact, and let $S \subseteq C(D)$ be uniformly bounded,
$|f(x)| \le M$ for all $f \in S$ and $x \in D$, and equicontinuous. Then $S$ is precompact in
$C(D)$ with the uniform norm.

The book assumes a common modulus of continuity, which is `UniformEquicontinuous`; the statement
assumes the weaker `Equicontinuous`, which is equivalent on the compact set $D$. The proof
specializes the backbone's `ContinuousMap.isCompact_closure_of_forall_norm_le`, which states the
same for maps from any compact space into a proper normed space. Mathlib states the
Arzelà–Ascoli theorem for the bounded continuous functions `D →ᵇ ℝ`, and the backbone transfers
it to `C(D, ℝ)`. -/
theorem theorem_1_6_3 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D)
    {S : Set C(D, ℝ)} {M : ℝ} (hbdd : ∀ f ∈ S, ∀ x, |f x| ≤ M)
    (heqc : Equicontinuous ((↑) : S → D → ℝ)) : definition_1_6_1_precompact S :=
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  ContinuousMap.isCompact_closure_of_forall_norm_le hbdd heqc

end AtkinsonHan.Chapter01
