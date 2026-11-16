/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Rademacher
import Numlib.Analysis.Convex.Saddle.Subdifferential
import NumlibSurface.Rockafellar.Chapter07.Section33

/-!
# Rockafellar, Section 35: Continuity and differentiability of saddle-functions

This module formalizes Section 35 of [rockafellar1970convex] (pages 370–378). The section carries
the continuity and convergence theorems of Section 10 and the differential theory of Sections 23–25
over to a **concave-convex** function $K$ of a pair $(u, v) \in \mathbb{R}^m \times \mathbb{R}^n$:
$K(\cdot, v)$ is concave and $K(u, \cdot)$ is convex. A finite concave-convex function on a
relatively open product $C \times D$ is continuous, and Lipschitzian on closed bounded subsets; the
families and sequences of such functions behave as in Section 10. The subdifferential is $\partial
K(u, v) = \partial_1 K(u, v) \times \partial_2 K(u, v)$, where $\partial_1 K(u, v)$ is the set of
supergradients of the concave function $K(\cdot, v)$ at $u$ and $\partial_2 K(u, v)$ is the set of
subgradients of the convex function $K(u, \cdot)$ at $v$. The directional derivative
$K'(u, v; u', v')$ exists and is a positively homogeneous concave-convex function of $(u', v')$, the
subdifferential mapping is upper semicontinuous, $K$ is differentiable exactly where $\partial K$ is
a single point, and $K$ is differentiable almost everywhere with a continuous gradient.

All twelve numbered results of Section 35 are formalized: Theorems 35.1–35.10 and Corollaries 35.7.1
and 35.8.1. The proofs specialize the backbone modules `Numlib.Analysis.Convex.Saddle.Continuity`,
`Numlib.Analysis.Convex.Saddle.Differential`, `Numlib.Analysis.Convex.Saddle.Subdifferential` and
`Numlib.Analysis.Convex.Saddle.Rademacher`.

## Main definitions

* Section 35, `Rockafellar.subdiff₁`: $\partial_1 K(u, v)$, the supergradients of $K(\cdot, v)$ at
  $u$.
* Section 35, `Rockafellar.subdiff₂`: $\partial_2 K(u, v)$, the subgradients of $K(u, \cdot)$ at
  $v$.
* Section 35, `Rockafellar.subdiff`: $\partial K(u, v) = \partial_1 K(u, v) \times \partial_2 K(u,
  v)$.

## Main results

* Theorem 35.1, `Rockafellar.theorem_35_1_continuousOn`, `Rockafellar.theorem_35_1_lipschitzian`: a
  finite concave-convex function on a relatively open convex product $C \times D$ is continuous
  there, and Lipschitzian on each closed bounded subset.
* Theorem 35.2, `Rockafellar.theorem_35_2`: a family of finite concave-convex functions that is
  pointwise bounded on a dense subset is uniformly bounded and equi-Lipschitzian on each closed
  bounded subset.
* Theorem 35.3, `Rockafellar.theorem_35_3`, `Rockafellar.theorem_35_3_dense`: a function
  $F(u, v, t)$ that is concave-convex in $(u, v)$ and continuous in $t$ is jointly continuous.
* Theorem 35.4, `Rockafellar.theorem_35_4`: convergence of finite concave-convex functions on a
  dense subset implies convergence on $C \times D$ to a finite concave-convex function, uniform on
  closed bounded subsets.
* Theorem 35.5, `Rockafellar.theorem_35_5`: a sequence of finite concave-convex functions that is
  bounded on a dense subset has a subsequence of this kind.
* Theorem 35.6, `Rockafellar.theorem_35_6`, `Rockafellar.theorem_35_6_tendsto`,
  `Rockafellar.theorem_35_6_concaveConvex`, `Rockafellar.theorem_35_6_posHom`: the directional
  derivative $K'(u, v; u', v')$ exists, equals $K'(u, v; u', 0) + K'(u, v; 0, v')$, and is a finite
  positively homogeneous concave-convex function of $(u', v')$.
* Theorem 35.7, `Rockafellar.theorem_35_7_fst`, `Rockafellar.theorem_35_7_snd`,
  `Rockafellar.theorem_35_7_subdiff`: semicontinuity of the partial directional derivatives and of
  the subdifferentials along a convergent sequence of functions and points.
* Corollary 35.7.1, `Rockafellar.corollary_35_7_1_fst`, `Rockafellar.corollary_35_7_1_snd`,
  `Rockafellar.corollary_35_7_1_subdiff`: the same for one function.
* Theorem 35.8, `Rockafellar.theorem_35_8`, `Rockafellar.theorem_35_8_gradient`: $K$ is
  differentiable at $(u, v)$ if and only if $\partial K(u, v)$ is a single point, and then
  $\partial K(u, v) = \{\nabla K(u, v)\}$.
* Corollary 35.8.1, `Rockafellar.corollary_35_8_1`: $K$ is differentiable at $(u, v)$ if and only if
  $K'(u, v; \cdot, \cdot)$ is linear.
* Theorem 35.9, `Rockafellar.theorem_35_9_measure`, `Rockafellar.theorem_35_9_dense`,
  `Rockafellar.theorem_35_9_continuousOn`: $K$ is differentiable almost everywhere on $C \times D$,
  on a dense set, and its gradient is continuous on the set where it exists.
* Theorem 35.10, `Rockafellar.theorem_35_10`, `Rockafellar.theorem_35_10_uniform`: pointwise
  convergence of differentiable concave-convex functions implies convergence of their gradients,
  uniformly on closed bounded subsets.

## Implementation notes

* The two inequalities that define $\partial_1 K$ and $\partial_2 K$ point in opposite directions.
  So $\partial K$ is not the subdifferential of $K$ as a function on $\mathbb{R}^{m+n}$, and it is
  not a monotone relation. `Rockafellar.mem_subdiff₁_iff_neg_mem_subdifferential_neg` translates a
  supergradient $u^*$ into the subgradient $-u^*$ of $-K(\cdot, v)$. Corollary 37.5.2 uses this
  change of sign to get a monotone relation.
* $K'(u, v; u', v')$ is `ConvexAnalysis.dirDerivReal K (u, v) (u', v')`, the limit of the difference
  quotient as the step decreases to $0$, with the value $0$ where the limit does not exist. The
  `EReal`-valued `ConvexAnalysis.dirDeriv` of Section 23 is an infimum of difference quotients. The
  infimum equals the limit along a line for a convex function, but not for a concave-convex function
  in a joint direction. Theorem 35.6 is about this difference.
* Theorems 35.6–35.10 use the subdifferential relative to the product,
  `ConvexAnalysis.saddleSubdifferentialOn C D K`: the inequalities are tested against the points of
  $C$ and of $D$ only. `Rockafellar.superdifferentialFstOn_univ_eq`,
  `Rockafellar.subdifferentialSndOn_univ_eq` and `Rockafellar.saddleSubdifferentialOn_univ_eq`
  identify it with the subdifferential of the book when
  $C \times D = \mathbb{R}^m \times \mathbb{R}^n$.
* Mathlib gives $\mathbb{R}^m \times \mathbb{R}^n$ the supremum norm
  $\|(u, v)\| = \max\{\|u\|, \|v\|\}$. This norm is used for the Lipschitz constants, for distances,
  and for the ball $B$.
* The gradient $\nabla K(u, v) = (u^*, v^*)$ is stated with `ConvexAnalysis.HasSaddleGradientAt`:
  $K$ has the Fréchet derivative $(u', v') \mapsto \langle u', u^* \rangle + \langle v', v^*
  \rangle$ at $(u, v)$. Mathlib's `gradient` does not apply, because the product with the supremum
  norm is not an inner product space.

## Deviations from the source

* **Theorems 35.6–35.10** (reading). The book takes $K$ concave-convex on
  $\mathbb{R}^m \times \mathbb{R}^n$ with values in $[-\infty, +\infty]$ and finite on the open set
  $C \times D$. Here $K$ is real-valued and concave-convex on $C \times D$, and $\partial K$ is
  tested against $C$ and $D$. The two readings agree after the simple extension of $K$ off
  $C \times D$. See `Rockafellar.saddleSubdifferentialOn_univ_eq`.
* **Theorem 35.7 and Corollary 35.7.1** (reading). The ball $B$ is the unit ball of the supremum
  norm, not the Euclidean unit ball. The two norms differ by a factor of at most $\sqrt 2$, and
  every statement holds for all $\varepsilon > 0$, so the statements are equivalent. The same
  applies to the balls $\varepsilon B$ of Theorems 35.9 and 35.10, which are stated here as
  continuity and convergence in the topology of the product. See `Rockafellar.theorem_35_7_subdiff`
  and `Rockafellar.corollary_35_7_1_subdiff`.
* **Theorem 35.10** (generalization). The book assumes that the functions are differentiable on all
  of $C \times D$. `Rockafellar.theorem_35_10` needs differentiability only at the point in
  question.

## Not formalized

* **Theorem 35.2**, the hypothesis in the form $\operatorname{conv}(\operatorname{cl}(C' \times D'))
  \supseteq C \times D$ of the book. `Rockafellar.theorem_35_2` assumes the stronger conditions
  $\operatorname{cl} C' \supseteq C$ and $\operatorname{cl} D' \supseteq D$, as
  `Rockafellar.theorem_10_6_ab` does in Section 10.
* **Corollary 35.8.1**, the last clause: finiteness of the $m + n$ two-sided partial derivatives
  implies differentiability.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal Pointwise

namespace Rockafellar

open ConvexAnalysis

/-! ### Two bookkeeping steps -/

section Bookkeeping

variable {m n : ℕ}

private theorem exists_lipschitz_of_lipschitzOnWith {E : Type*} [NormedAddCommGroup E]
    {f : E → ℝ} {S : Set E} {k : ℝ≥0} (h : LipschitzOnWith k f S) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ y ∈ S, ∀ x ∈ S, |f y - f x| ≤ α * ‖y - x‖ := by
  refine ⟨k, k.coe_nonneg, fun y hy x hx => ?_⟩
  have hd := h.dist_le_mul y hy x hx
  rwa [Real.dist_eq, dist_eq_norm] at hd

private theorem isCompact_prod_projections {C : Set (Rn m)} {D : Set (Rn n)}
    {E : Set (Rn m × Rn n)} (hE : IsCompact E) (hEsub : E ⊆ C ×ˢ D) :
    IsCompact (Prod.fst '' E) ∧ IsCompact (Prod.snd '' E) ∧ Prod.fst '' E ⊆ C ∧
      Prod.snd '' E ⊆ D ∧ E ⊆ (Prod.fst '' E) ×ˢ (Prod.snd '' E) := by
  refine ⟨hE.image continuous_fst, hE.image continuous_snd, ?_, ?_,
    fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).1
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).2

end Bookkeeping

/-! ### Theorem 35.1 -/

section Thm351

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Theorem 35.1** of [rockafellar1970convex], continuity. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be relatively open convex sets, and let $K : \mathbb{R}^m \times
\mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$. Then $K$ is continuous relative
to $C \times D$.

"Relatively open" is `ri C = C`. Concave-convex on $C \times D$ is
`ConvexAnalysis.ConcaveConvexOn C D K`: $K(\cdot, v)$ is concave on $C$ for each $v \in D$, and
$K(u, \cdot)$ is convex on $D$ for each $u \in C$. -/
theorem theorem_35_1_continuousOn (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) : ContinuousOn K (C ×ˢ D) := by
  have h := hK.continuousOn hC hD
  rwa [hCro, hDro] at h

/-- **Theorem 35.1** of [rockafellar1970convex], Lipschitz continuity. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be relatively open convex sets, and
let $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$. For
every closed bounded set $E \subseteq C \times D$ there is an $\alpha \ge 0$ with
$$|K(q) - K(p)| \le \alpha \|q - p\| \qquad \text{for all } p, q \in E.$$

The norm on $\mathbb{R}^m \times \mathbb{R}^n$ is the supremum norm of Mathlib. The proof uses
that $E$ is compact and lies in the product of its two projections. -/
theorem theorem_35_1_lipschitzian (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) {E : Set (Rn m × Rn n)} (hEcl : IsClosed E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ q ∈ E, ∀ p ∈ E, |K q - K p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  obtain ⟨k, hk⟩ := hK.exists_lipschitzOnWith_of_isCompact hC hD hS hSC' hT hTD'
  exact exists_lipschitz_of_lipschitzOnWith (hk.mono hrect)

end Thm351

/-! ### Theorem 35.2 -/

section Thm352

variable {m n : ℕ} {ι : Type*} {C C' : Set (Rn m)} {D D' : Set (Rn n)}

/-- **Theorem 35.2** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be relatively open convex sets, and let $C' \subseteq C$ and
$D' \subseteq D$ with $C \subseteq \operatorname{cl} C'$ and $D \subseteq \operatorname{cl} D'$.
Let $(K_i)_{i \in I}$ be a family of real functions that are concave-convex on $C \times D$,
such that $\{K_i(u, v) \mid i \in I\}$ is bounded for each $u \in C'$ and $v \in D'$. Then for
every closed bounded set $E \subseteq C \times D$ there are real numbers $\alpha_1, \alpha_2$
and $\alpha \ge 0$ with $\alpha_1 \le K_i(p) \le \alpha_2$ and
$$|K_i(q) - K_i(p)| \le \alpha \|q - p\|$$
for all $i \in I$ and all $p, q \in E$. That is, the family is uniformly bounded and
equi-Lipschitzian on $E$.

The book asks only for $\operatorname{conv}(\operatorname{cl}(C' \times D')) \supseteq C \times
D$. That weaker hypothesis is not formalized; the statement here drops the convex hull, as
`Rockafellar.theorem_10_6_ab` does for Theorem 10.6.

The index type $I$ is arbitrary, so the family can be empty. The norm on
$\mathbb{R}^m \times \mathbb{R}^n$ is the supremum norm. -/
theorem theorem_35_2 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    {K : ι → Rn m × Rn n → ℝ} (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v)))
    {E : Set (Rn m × Rn n)} (hEcl : IsClosed E) (hEb : Bornology.IsBounded E)
    (hEsub : E ⊆ C ×ˢ D) :
    (∃ α₁ α₂ : ℝ, ∀ p ∈ E, ∀ i, α₁ ≤ K i p ∧ K i p ≤ α₂) ∧
      ∃ α : ℝ, 0 ≤ α ∧ ∀ i, ∀ q ∈ E, ∀ p ∈ E, |K i q - K i p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨⟨M, hM0, hM⟩, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod hC hD hK
    hC'ri hCd hD'ri hDd hbdd hS hSC' hT hTD'
  refine ⟨⟨-M, M, fun p hp i => abs_le.1 (hM i p (hrect hp))⟩, k, k.coe_nonneg,
    fun i q hq p hp => ?_⟩
  have hd := ((hk i).mono hrect).dist_le_mul q hq p hp
  rwa [Real.dist_eq, dist_eq_norm] at hd

end Thm352

/-! ### Theorem 35.3 -/

section Thm353

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {T : Type*} [TopologicalSpace T]
  [LocallyCompactSpace T] {F : (Rn m × Rn n) × T → ℝ}

/-- **Theorem 35.3** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be relatively open convex sets, and let $T$ be a locally compact
topological space. Let $F : (\mathbb{R}^m \times \mathbb{R}^n) \times T \to \mathbb{R}$ be such
that $F(\cdot, \cdot, t)$ is concave-convex on $C \times D$ for each $t \in T$, and
$t \mapsto F(u, v, t)$ is continuous on $T$ for each $u \in C$ and $v \in D$. Then $F$ is
continuous relative to $C \times D \times T$.

The two convex variables are grouped as a pair $(u, v)$, because the concave-convex hypothesis
is about the pair. -/
theorem theorem_35_3 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hcont : ∀ u ∈ C, ∀ v ∈ D, Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hc : ∀ u ∈ ri C, ∀ v ∈ ri D, Continuous fun t => F ((u, v), t) := by
    rw [hCro, hDro]; exact hcont
  have h := continuousOn_prod_of_concaveConvexOn' hC hD hF hc
  rwa [hCro, hDro] at h

/-- **Theorem 35.3** of [rockafellar1970convex], with continuity in $t$ only on dense subsets. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be relatively open convex sets, let
$C' \subseteq C$ and $D' \subseteq D$ with $C \subseteq \operatorname{cl} C'$ and
$D \subseteq \operatorname{cl} D'$, and let $T$ be a locally compact topological space. Let $F :
(\mathbb{R}^m \times \mathbb{R}^n) \times T \to \mathbb{R}$ be such that $F(\cdot, \cdot, t)$ is
concave-convex on $C \times D$ for each $t \in T$, and $t \mapsto F(u, v, t)$ is continuous for
each $u \in C'$ and $v \in D'$. Then $F$ is continuous relative to $C \times D \times T$. -/
theorem theorem_35_3_dense (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcont : ∀ u ∈ C', ∀ v ∈ D', Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  have h := continuousOn_prod_of_concaveConvexOn hC hD hF hC'ri hCd hD'ri hDd hcont
  rwa [hCro, hDro] at h

end Thm353

/-! ### Theorems 35.4 and 35.5 -/

section Convergence

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {K : ℕ → Rn m × Rn n → ℝ}

/-- **Theorem 35.4** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be relatively open convex sets, and let $C' \subseteq C$ and
$D' \subseteq D$ with $C \subseteq \operatorname{cl} C'$ and $D \subseteq \operatorname{cl} D'$.
Let $K_0, K_1, \dots$ be real functions that are concave-convex on $C \times D$, such that the
limit of $K_i(u, v)$ exists and is finite for each $u \in C'$ and $v \in D'$. Then there is a
function $L$, concave-convex on $C \times D$, such that $K_i(p) \to L(p)$ for every
$p \in C \times D$, and the convergence is uniform on every closed bounded subset of
$C \times D$.

The sequence is indexed by $\mathbb{N}$, starting at $0$. -/
theorem theorem_35_4 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcv : ∀ u ∈ C', ∀ v ∈ D', ∃ L : ℝ, Tendsto (fun i => K i (u, v)) atTop (𝓝 L)) :
    ∃ L : Rn m × Rn n → ℝ, ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K i p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn K L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨L, hLcc, hLt, huc⟩ :=
    exists_tendstoUniformlyOn_prod_of_dense' hC hD hK hC'ri hCd hD'ri hDd hcv
  rw [hCro, hDro] at hLcc hLt
  refine ⟨L, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

/-- **Theorem 35.5** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be relatively open convex sets, and let $C' \subseteq C$ and
$D' \subseteq D$ with $C \subseteq \operatorname{cl} C'$ and $D \subseteq \operatorname{cl} D'$.
Let $K_0, K_1, \dots$ be real functions that are concave-convex on $C \times D$, such that
$\{K_i(u, v) \mid i \in \mathbb{N}\}$ is bounded for each $u \in C'$ and $v \in D'$. Then there
are a strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$ and a function $L$,
concave-convex on $C \times D$, such that $K_{\varphi(i)}(p) \to L(p)$ for every
$p \in C \times D$, and the convergence is uniform on every closed bounded subset of
$C \times D$.

This is the Arzelà–Ascoli theorem for saddle-functions. The proof takes a countable dense subset
of $C' \times D'$, which exists by separability, and extracts a diagonal subsequence. -/
theorem theorem_35_5 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v))) :
    ∃ (φ : ℕ → ℕ) (L : Rn m × Rn n → ℝ), StrictMono φ ∧ ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K (φ i) p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn (fun i => K (φ i)) L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨φ, L, hφ, hLcc, hLt, huc⟩ :=
    exists_subseq_tendstoUniformlyOn_prod hC hD hK hC'ri hCd hD'ri hDd hbdd
  rw [hCro, hDro] at hLcc hLt
  refine ⟨φ, L, hφ, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

end Convergence

/-!
### The subdifferential of a saddle-function

The definition of [rockafellar1970convex] for an arbitrary function $K$ with values in
$[-\infty, +\infty]$.
-/

section Subdifferential

variable {m n : ℕ}

/-- **Section 35** of [rockafellar1970convex], definition of $\partial_1 K$. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ and $(u, v) \in \mathbb{R}^m \times \mathbb{R}^n$.
Then $\partial_1 K(u, v) = \partial_u K(u, v)$ is the set of $u^* \in \mathbb{R}^m$ with
$$K(u', v) \le K(u, v) + \langle u' - u, u^* \rangle \qquad \text{for all } u' \in
  \mathbb{R}^m,$$
that is, the set of **supergradients** of the function $K(\cdot, v)$ at $u$.

The definition is `ConvexAnalysis.superdifferential` for the Euclidean pairing
`Rockafellar.pairing`. -/
noncomputable abbrev subdiff₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m) :=
  superdifferential (pairing m) (fun u => K (u, p.2)) p.1

/-- **Section 35** of [rockafellar1970convex], definition of $\partial_2 K$. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ and $(u, v) \in \mathbb{R}^m \times \mathbb{R}^n$.
Then $\partial_2 K(u, v) = \partial_v K(u, v)$ is the set of $v^* \in \mathbb{R}^n$ with
$$K(u, v) + \langle v' - v, v^* \rangle \le K(u, v') \qquad \text{for all } v' \in
  \mathbb{R}^n,$$
that is, the set of **subgradients** of the function $K(u, \cdot)$ at $v$.

The inequality points the other way from the one of `Rockafellar.subdiff₁`; this is the sign
convention of the book. The definition is `ConvexAnalysis.subdifferential` for the Euclidean
pairing `Rockafellar.pairing`. -/
noncomputable abbrev subdiff₂ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn n) :=
  subdifferential (pairing n) (fun v => K (p.1, v)) p.2

/-- **Section 35** of [rockafellar1970convex], definition of $\partial K$. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$. The **subdifferential** of $K$ at $(u, v)$ is the
product
$$\partial K(u, v) = \partial_1 K(u, v) \times \partial_2 K(u, v).$$

It is a product of two sets, not a set of pairs that satisfy one joint inequality. Its two
factors satisfy opposite inequalities, so it is not the subdifferential of $K$ as a function on
$\mathbb{R}^{m+n}$. The definition is `ConvexAnalysis.saddleSubdifferential` for the Euclidean
pairings. -/
noncomputable abbrev subdiff (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m × Rn n) :=
  saddleSubdifferential (pairing m) (pairing n) K p

variable {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and
$p \in \mathbb{R}^m \times \mathbb{R}^n$, $\partial K(p) = \partial_1 K(p) \times \partial_2
K(p)$. This holds by definition. -/
theorem subdiff_eq_prod : subdiff K p = subdiff₁ K p ×ˢ subdiff₂ K p := rfl

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, $u^* \in \partial_1 K(u, v)$
if and only if $K(u', v) \le K(u, v) + \langle u' - u, u^* \rangle$ for all
$u' \in \mathbb{R}^m$. -/
theorem mem_subdiff₁_iff {y : Rn m} :
    y ∈ subdiff₁ K p ↔ ∀ u' : Rn m, K (u', p.2) ≤ K p + ((pairing m (u' - p.1) y : ℝ) : EReal) :=
  Iff.rfl

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, $v^* \in \partial_2 K(u, v)$
if and only if $K(u, v) + \langle v' - v, v^* \rangle \le K(u, v')$ for all
$v' \in \mathbb{R}^n$. -/
theorem mem_subdiff₂_iff {y : Rn n} :
    y ∈ subdiff₂ K p ↔ ∀ v' : Rn n, K p + ((pairing n (v' - p.2) y : ℝ) : EReal) ≤ K (p.1, v') :=
  Iff.rfl

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, $u^* \in \partial_1 K(u, v)$
if and only if $-u^*$ is a subgradient of $-K(\cdot, v)$ at $u$.

This change of sign is the one that Corollary 37.5.2 uses to get a monotone relation, and that
Corollary 37.5.1 uses to get the map $(u - u^*, v^* + v)$. -/
theorem mem_subdiff₁_iff_neg_mem_subdifferential_neg {y : Rn m} :
    y ∈ subdiff₁ K p ↔ -y ∈ subdifferential (pairing m) (fun u => -K (u, p.2)) p.1 :=
  mem_superdifferential_iff_neg_mem_subdifferential_neg

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and every $p$, the set
$\partial K(p)$ is a convex subset of $\mathbb{R}^m \times \mathbb{R}^n$. No hypothesis on $K$
is needed. -/
theorem convex_subdiff : Convex ℝ (subdiff K p) := convex_saddleSubdifferential

end Subdifferential

/-! ### The subdifferential relative to a product and the subdifferential of the book -/

section Bridge

variable {m n : ℕ} (K : Rn m × Rn n → ℝ) (p : Rn m × Rn n)

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$, the set of supergradients of
$K(\cdot, v)$ at $u$ tested against all of $\mathbb{R}^m$
(`ConvexAnalysis.superdifferentialFstOn` with $C = \mathbb{R}^m$) is $\partial_1 K(u, v)$, with
$K$ read as a function with values in $[-\infty, +\infty]$. -/
theorem superdifferentialFstOn_univ_eq :
    superdifferentialFstOn (Set.univ : Set (Rn m)) K p
        = subdiff₁ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_superdifferentialFstOn, Set.mem_univ, forall_const, mem_superdifferential,
    pairing_apply]
  refine forall_congr' fun u' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$, the set of subgradients of
$K(u, \cdot)$ at $v$ tested against all of $\mathbb{R}^n$ (`ConvexAnalysis.subdifferentialSndOn`
with $D = \mathbb{R}^n$) is $\partial_2 K(u, v)$, with $K$ read as a function with values in
$[-\infty, +\infty]$. -/
theorem subdifferentialSndOn_univ_eq :
    subdifferentialSndOn (Set.univ : Set (Rn n)) K p
        = subdiff₂ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_subdifferentialSndOn, Set.mem_univ, forall_const, mem_subdifferential,
      pairing_apply]
  refine forall_congr' fun v' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$, the subdifferential relative to
$C \times D$ (`ConvexAnalysis.saddleSubdifferentialOn`) with $C = \mathbb{R}^m$ and
$D = \mathbb{R}^n$ is $\partial K(u, v)$, with $K$ read as a function with values in
$[-\infty, +\infty]$. -/
theorem saddleSubdifferentialOn_univ_eq :
    saddleSubdifferentialOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K p
      = subdiff (fun z => ((K z : ℝ) : EReal)) p := by
  rw [subdiff_eq_prod, ← superdifferentialFstOn_univ_eq, ← subdifferentialSndOn_univ_eq]
  rfl

end Bridge

/-! ### Theorem 35.6, the splitting identity -/

section Thm356

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}

/-- **Theorem 35.6** of [rockafellar1970convex], the displayed equation. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then for every $(u', v') \in \mathbb{R}^m \times \mathbb{R}^n$,
$$K'(u, v; u', v') = K'(u, v; u', 0) + K'(u, v; 0, v').$$

The proof does not use the convexity of $C$ and $D$; it uses only that $C$ and $D$ are open.

$K'(u, v; q)$ is `ConvexAnalysis.dirDerivReal K (u, v) q`, the limit of the difference quotient
as the step decreases to $0$. `Rockafellar.theorem_35_6_tendsto` shows that the limit exists. -/
theorem theorem_35_6 (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D) (_hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) q
      = dirDerivReal K (u, v) (q.1, 0) + dirDerivReal K (u, v) (0, q.2) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q, dirDerivReal_prod_fst hCo hDo hK hu hv q.1,
    dirDerivReal_prod_snd hCo hDo hK hu hv q.2]

/-- **Theorem 35.6** of [rockafellar1970convex], existence of the directional derivative. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then for every $q \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\frac{K((u, v) + t q) - K(u, v)}{t} \to K'(u, v; q) \qquad \text{as } t \downarrow 0.$$
The book calls this part of the theorem "problematical". -/
theorem theorem_35_6_tendsto (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (q : Rn m × Rn n) :
    Tendsto (fun t : ℝ => (K ((u, v) + t • q) - K (u, v)) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (dirDerivReal K (u, v) q)) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q]
  exact tendsto_slope_dirDerivReal_prod hCo hDo hK hu hv q

/-- **Theorem 35.6** of [rockafellar1970convex], concave-convexity of the directional derivative.
Let $C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then $K'(u, v; \cdot, \cdot)$ is a finite concave-convex function on
all of $\mathbb{R}^m \times \mathbb{R}^n$. -/
theorem theorem_35_6_concaveConvex (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n))
      (dirDerivReal K (u, v)) :=
  concaveConvexOn_dirDerivReal hCo hDo hK hu hv

/-- **Theorem 35.6** of [rockafellar1970convex], positive homogeneity of the directional derivative.
Let $C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then $K'(u, v; c q) = c K'(u, v; q)$ for every $c > 0$ and every
$q \in \mathbb{R}^m \times \mathbb{R}^n$. -/
theorem theorem_35_6_posHom (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {c : ℝ}
    (hc : 0 < c) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) (c • q) = c * dirDerivReal K (u, v) q :=
  dirDerivReal_prod_smul hCo hDo hK hu hv hc q

end Thm356

/-! ### Theorem 35.7 and Corollary 35.7.1 -/

section Thm357

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {Ks : ℕ → Rn m × Rn n → ℝ}
  {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n} {us : ℕ → Rn m} {vs : ℕ → Rn n}

/-- **Theorem 35.7** of [rockafellar1970convex], the first inequality. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let
$K_0, K_1, \dots$ and $K$ be real functions that are concave-convex on $C \times D$, with
$K_i(p) \to K(p)$ for every $p \in C \times D$. Let $u \in C$ and $v \in D$, and let $u_i \to u$
and $v_i \to v$. Then for every $u' \in \mathbb{R}^m$,
$$\liminf_{i \to \infty} K_i'(u_i, v_i; u', 0) \ge K'(u, v; u', 0).$$

The inequality is stated without extended values: for every real $\mu < K'(u, v; u', 0)$,
eventually $\mu < K_i'(u_i, v_i; u', 0)$.

The proof needs a step that the book does not write out: finite concave-convex functions
converge continuously, that is, $K_i(u_i, v_i) \to K(u, v)$. -/
theorem theorem_35_7_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (u' : Rn m) {μ : ℝ}
    (hμ : μ < dirDerivReal K (u, v) (u', 0)) :
    ∀ᶠ i in atTop, μ < dirDerivReal (Ks i) (us i, vs i) (u', 0) := by
  rw [dirDerivReal_prod_fst hCo hDo hK hu hv u'] at hμ
  filter_upwards [eventually_lt_dirDerivReal_fst hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_fst hCo hDo (hKs i) hui hvi u']

/-- **Theorem 35.7** of [rockafellar1970convex], the second inequality. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let
$K_0, K_1, \dots$ and $K$ be real functions that are concave-convex on $C \times D$, with
$K_i(p) \to K(p)$ for every $p \in C \times D$. Let $u \in C$ and $v \in D$, and let $u_i \to u$
and $v_i \to v$. Then for every $v' \in \mathbb{R}^n$,
$$\limsup_{i \to \infty} K_i'(u_i, v_i; 0, v') \le K'(u, v; 0, v').$$

The inequality is stated without extended values: for every real $\mu > K'(u, v; 0, v')$,
eventually $K_i'(u_i, v_i; 0, v') < \mu$. -/
theorem theorem_35_7_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (v' : Rn n) {μ : ℝ}
    (hμ : dirDerivReal K (u, v) (0, v') < μ) :
    ∀ᶠ i in atTop, dirDerivReal (Ks i) (us i, vs i) (0, v') < μ := by
  rw [dirDerivReal_prod_snd hCo hDo hK hu hv v'] at hμ
  filter_upwards [eventually_dirDerivReal_snd_lt hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_snd hCo hDo (hKs i) hui hvi v']

/-- **Theorem 35.7** of [rockafellar1970convex], the subdifferentials. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let
$K_0, K_1, \dots$ and $K$ be real functions that are concave-convex on $C \times D$, with
$K_i(p) \to K(p)$ for every $p \in C \times D$. Let $u \in C$ and $v \in D$, and let $u_i \to u$
and $v_i \to v$. Then for every $\varepsilon > 0$ there is an $i_0$ with
$$\partial K_i(u_i, v_i) \subseteq \partial K(u, v) + \varepsilon B \qquad \text{for all } i \ge
  i_0.$$

**Reading.** The book takes $B$ to be the Euclidean unit ball. Here $B$ is the closed unit ball
of the supremum norm on $\mathbb{R}^m \times \mathbb{R}^n$. The two balls differ by a factor of
at most $\sqrt 2$, and the statement holds for all $\varepsilon > 0$, so the two statements are
equivalent.

The subdifferentials are relative to $C \times D$ (`ConvexAnalysis.saddleSubdifferentialOn`). -/
theorem theorem_35_7_subdiff (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, saddleSubdifferentialOn C D (Ks i) (us i, vs i)
      ⊆ saddleSubdifferentialOn C D K (u, v) + Metric.closedBall (0 : Rn m × Rn n) ε :=
  eventually_saddleSubdifferentialOn_subset hCo hC hDo hD hKs hK hconv hu hv hus hvs hε

/-- **Corollary 35.7.1** of [rockafellar1970convex], the first assertion. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then for every $u' \in \mathbb{R}^m$ the function
$(x, y) \mapsto K'(x, y; u', 0)$ is lower semicontinuous at $(u, v)$.

Here $K'(x, y; u', 0)$ is written as the directional derivative of $K(\cdot, y)$ at $x$ in the
direction $u'$. The proof applies Theorem 35.7 to the constant sequence $K_i = K$. -/
theorem corollary_35_7_1_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (u' : Rn m) :
    LowerSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun w => K (w, p.2)) p.1 u')
      (u, v) :=
  lowerSemicontinuousAt_dirDerivReal_fst hCo hC hDo hD hK hu hv u'

/-- **Corollary 35.7.1** of [rockafellar1970convex], the second assertion. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then for every $v' \in \mathbb{R}^n$ the function
$(x, y) \mapsto K'(x, y; 0, v')$ is upper semicontinuous at $(u, v)$.

Here $K'(x, y; 0, v')$ is written as the directional derivative of $K(x, \cdot)$ at $y$ in the
direction $v'$. -/
theorem corollary_35_7_1_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (v' : Rn n) :
    UpperSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun x => K (p.1, x)) p.2 v')
      (u, v) :=
  upperSemicontinuousAt_dirDerivReal_snd hCo hC hDo hD hK hu hv v'

/-- **Corollary 35.7.1** of [rockafellar1970convex], the subdifferential. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$, and let
$u \in C$ and $v \in D$. Then for every $\varepsilon > 0$ there is a $\delta > 0$ such that
$$\partial K(x, y) \subseteq \partial K(u, v) + \varepsilon B$$
for every $(x, y)$ with $\|(x, y) - (u, v)\| < \delta$.

**Reading.** As in `Rockafellar.theorem_35_7_subdiff`, $B$ is the closed unit ball of the
supremum norm instead of the Euclidean unit ball. The statements are equivalent.

The subdifferentials are relative to $C \times D$, and the distance is the one of the supremum
norm. -/
theorem corollary_35_7_1_subdiff (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : Rn m × Rn n, dist p (u, v) < δ →
      saddleSubdifferentialOn C D K p ⊆ saddleSubdifferentialOn C D K (u, v)
        + Metric.closedBall (0 : Rn m × Rn n) ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_saddleSubdifferentialOn_subset hCo hC hDo hD hK hu hv hε)
  exact ⟨δ, hδ, fun p hp => h hp⟩

end Thm357

/-! ### Theorem 35.8 and Corollary 35.8.1 -/

section Thm358

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}
  {q : Rn m × Rn n}

/-- **Theorem 35.8** of [rockafellar1970convex], the gradient. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be open convex sets, let $K : \mathbb{R}^m \times \mathbb{R}^n \to
\mathbb{R}$ be concave-convex on $C \times D$, and let $u \in C$ and $v \in D$. If $K$ is
differentiable at $(u, v)$ with gradient $\nabla K(u, v) = q$, then $\partial K(u, v) = \{q\}$.

The gradient is a pair $q = (u^*, v^*)$, and `ConvexAnalysis.HasSaddleGradientAt K q (u, v)`
says that $K$ has the Fréchet derivative $(u', v') \mapsto \langle u', u^* \rangle + \langle v',
v^* \rangle$ at $(u, v)$. The subdifferential is relative to $C \times D$. -/
theorem theorem_35_8_gradient (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (hd : HasSaddleGradientAt K q (u, v)) : saddleSubdifferentialOn C D K (u, v) = {q} :=
  saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hK hu hv hd

/-- **Theorem 35.8** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be open convex sets, let $K : \mathbb{R}^m \times \mathbb{R}^n \to
\mathbb{R}$ be concave-convex on $C \times D$, and let $u \in C$ and $v \in D$. Then $K$ is
differentiable at $(u, v)$ if and only if $\partial K(u, v)$ consists of a single point.

The subdifferential is relative to $C \times D$. The converse direction is proved from Corollary
35.7.1, which gives the estimate of Fréchet differentiability directly. -/
theorem theorem_35_8 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ ∃ q, saddleSubdifferentialOn C D K (u, v) = {q} :=
  differentiableAt_iff_exists_saddleSubdifferentialOn_eq_singleton hCo hC hDo hD hK hu hv

/-- **Corollary 35.8.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be open convex sets, let $K : \mathbb{R}^m \times \mathbb{R}^n \to
\mathbb{R}$ be concave-convex on $C \times D$, and let $u \in C$ and $v \in D$. Then $K$ is
differentiable at $(u, v)$ if and only if $K'(u, v; \cdot, \cdot)$ is a linear function on
$\mathbb{R}^m \times \mathbb{R}^n$.

The last clause of the corollary, that finiteness of the $m + n$ two-sided partial derivatives
at $(u, v)$ implies differentiability, is not formalized. -/
theorem corollary_35_8_1 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ IsLinearMap ℝ (dirDerivReal K (u, v)) :=
  differentiableAt_iff_isLinearMap_dirDerivReal hCo hC hDo hD hK hu hv

end Thm358

/-! ### Theorems 35.9 and 35.10 -/

section Rademacher

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Theorem 35.9** of [rockafellar1970convex], the measure of the exceptional set. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$. Then the set
of points of $C \times D$ at which $K$ is not differentiable has Lebesgue measure $0$.

The measure is the product of the Lebesgue measures of $\mathbb{R}^m$ and $\mathbb{R}^n$. The
proof combines Theorem 35.1 with Rademacher's theorem, as in Section 25. -/
theorem theorem_35_9_measure (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) :
    volume ((C ×ˢ D) \ {p : Rn m × Rn n | DifferentiableAt ℝ K p}) = 0 := by
  have : (volume : Measure (Rn m × Rn n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  exact measure_diff_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Theorem 35.9** of [rockafellar1970convex], density. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be open convex sets, and let $K : \mathbb{R}^m \times \mathbb{R}^n
\to \mathbb{R}$ be concave-convex on $C \times D$. Then $C \times D$ is contained in the closure
of the set of points at which $K$ is differentiable. -/
theorem theorem_35_9_dense (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) : C ×ˢ D ⊆ closure {p : Rn m × Rn n | DifferentiableAt ℝ K p} :=
  subset_closure_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Theorem 35.9** of [rockafellar1970convex], continuity of the gradient. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on $C \times D$. Let
$S \subseteq C \times D$, and let $G : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}^m \times
\mathbb{R}^n$ satisfy $G(p) = \nabla K(p)$ for every $p \in S$. Then $G$ is continuous relative
to $S$.

There is no canonical function $\nabla K$ without a choice of values off $S$, so the statement
takes any $G$ that represents the gradient on $S$. The gradient is unique where it exists, so
$G$ is determined on $S$. The case where $S$ is the set of points of differentiability in
$C \times D$ is the statement of the book. -/
theorem theorem_35_9_continuousOn (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) {S : Set (Rn m × Rn n)} (hS : S ⊆ C ×ˢ D)
    {G : Rn m × Rn n → Rn m × Rn n} (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) :
    ContinuousOn G S :=
  continuousOn_saddleGradient hCo hC hDo hD hK hS hG

/-- **Theorem 35.10** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be open convex sets, and let $K_0, K_1, \dots$ and $K$ be real
functions that are concave-convex on $C \times D$, with $K_i(p) \to K(p)$ for every
$p \in C \times D$. Let $p \in C \times D$, and assume that each $K_i$ and $K$ are
differentiable at $p$. Then $\nabla K_i(p) \to \nabla K(p)$.

**Generalization.** The book assumes that the functions $K_i$ and $K$ are differentiable on all
of $C \times D$. The statement here needs differentiability only at $p$.

The gradients are given as `ConvexAnalysis.HasSaddleGradientAt (Ks i) (G i) p` and
`ConvexAnalysis.HasSaddleGradientAt K G' p`. -/
theorem theorem_35_10 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) {p : Rn m × Rn n}
    (hp : p ∈ C ×ˢ D) {G : ℕ → Rn m × Rn n} {G' : Rn m × Rn n}
    (hG : ∀ i, HasSaddleGradientAt (Ks i) (G i) p) (hG' : HasSaddleGradientAt K G' p) :
    Tendsto G atTop (𝓝 G') :=
  tendsto_of_hasSaddleGradientAt hCo hC hDo hD hKs hK hconv hp hG hG'

/-- **Theorem 35.10** of [rockafellar1970convex], uniform convergence. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be open convex sets, and let
$K_0, K_1, \dots$ and $K$ be real functions that are concave-convex on $C \times D$, with
$K_i(p) \to K(p)$ for every $p \in C \times D$. Assume that each $K_i$ and $K$ are
differentiable at every point of $C \times D$, with gradient mappings $G_i$ and $G$ on
$C \times D$. Then $G_i \to G$ uniformly on every closed bounded subset of $C \times D$. -/
theorem theorem_35_10_uniform (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p)))
    {Gs : ℕ → Rn m × Rn n → Rn m × Rn n} {G : Rn m × Rn n → Rn m × Rn n}
    (hGs : ∀ i, ∀ p ∈ C ×ˢ D, HasSaddleGradientAt (Ks i) (Gs i p) p)
    (hG : ∀ p ∈ C ×ˢ D, HasSaddleGradientAt K (G p) p) {E : Set (Rn m × Rn n)}
    (hEcl : IsClosed E) (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    TendstoUniformlyOn Gs G atTop E :=
  tendstoUniformlyOn_saddleGradient hCo hC hDo hD hKs hK hconv hGs hG
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub

end Rademacher

end Rockafellar
