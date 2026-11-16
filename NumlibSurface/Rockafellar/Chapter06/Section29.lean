/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Adjoint
import Numlib.Analysis.Convex.Extremum.Perturbation
import Numlib.Analysis.Convex.Process.Linear
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Chapter05.Section25

/-!
# Rockafellar, Section 29: Bifunctions and generalized convex programs

This module formalizes Section 29 (pp. 291–306) of [rockafellar1970convex]. A bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ assigns to each $u \in \mathbb{R}^m$ a function $Fu$ on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and it is convex if its graph function
$(u, x) \mapsto (Fu)(x)$ is convex. The generalized convex program $(P)$ associated with $F$ is the
minimization of the objective function $F0$, and the functions $Fu$ are its perturbations. The
perturbation function is $(\inf F)(u) = \inf_x (Fu)(x)$, and the optimal value in $(P)$ is
$(\inf F)(0)$. A Kuhn–Tucker vector for $(P)$ is a vector $u^* \in \mathbb{R}^m$ such that
$(\inf F)(0)$ is finite and $\inf_u \{\langle u, u^* \rangle + (\inf F)(u)\} = (\inf F)(0)$. This
generalizes the ordinary convex programs of Section 28.

The section shows that the Kuhn–Tucker vectors are the vectors $u^*$ with
$-u^* \in \partial (\inf F)(0)$, and derives from this their existence under strong consistency,
strict consistency or polyhedral convexity. It shows that a Kuhn–Tucker vector $\bar u^*$ together
with an optimal solution $\bar x$ is exactly a saddle-point of the Lagrangian $L(u^*, x) = \inf_u
\{\langle u, u^* \rangle + (Fu)(x)\}$, and it studies the closure $\operatorname{cl} F$ of a
bifunction. The duality theory of Section 30 is stated in these terms. All 12 numbered results of
Section 29 are formalized: Theorems 29.1–29.4 and Corollaries 29.1.1–29.1.6, 29.3.1 and 29.4.1. The
book prints Corollary 29.4.1 with no proof. The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Extremum.Perturbation`, `Numlib.Analysis.Convex.Extremum.Adjoint` and
`Numlib.Analysis.Convex.Saddle.Minimax`.

## Main definitions

* `Rockafellar.graphDomain`: the effective domain of the graph function of a bifunction.
* `Rockafellar.IsOptimalSolution`: the optimal solutions to $(P)$, the points $x$ at which $(F0)(x)$
  is finite and equal to the optimal value.
* `Rockafellar.linearIndicatorBifun`: the indicator bifunction $(Fu)(x) = \delta(x \mid Au)$ of a
  linear transformation $A$.
* `Rockafellar.originBifun`, `Rockafellar.corollary_29_4_1_perturbation`: the counterexample to the
  perturbation clause of Corollary 29.4.1, and that clause as printed.

## Main results

* Theorem 29.1, `Rockafellar.theorem_29_1`, `Rockafellar.theorem_29_1_convexFn`,
  `Rockafellar.theorem_29_1_dom`, `Rockafellar.theorem_29_1_set`: $\inf F$ is convex with
  $\operatorname{dom}(\inf F) = \operatorname{dom} F$, and at a finite optimal value the Kuhn–Tucker
  vectors are the vectors $u^*$ with $-u^* \in \partial (\inf F)(0)$.
* Corollary 29.1.1, `Rockafellar.corollary_29_1_1_monotone`, `Rockafellar.corollary_29_1_1_iInf`,
  `Rockafellar.corollary_29_1_1_posHomogeneous`, `Rockafellar.corollary_29_1_1_convexFn`,
  `Rockafellar.corollary_29_1_1_convex`, `Rockafellar.corollary_29_1_1_isClosed`,
  `Rockafellar.corollary_29_1_1_supportFn`: the directional derivative $(\inf F)'(0; \cdot)$ as an
  infimum of difference quotients, its positive homogeneity and convexity, and the Kuhn–Tucker set
  as a closed convex set whose support function is given by $(\inf F)'(0; \cdot)$.
* Corollary 29.1.2, `Rockafellar.corollary_29_1_2`: no Kuhn–Tucker vector exists if and only if
  $(\inf F)'(0; u) = -\infty$ and $(\inf F)'(0; -u) = +\infty$ for some $u$.
* Corollary 29.1.3, `Rockafellar.corollary_29_1_3`, `Rockafellar.corollary_29_1_3_eq`,
  `Rockafellar.corollary_29_1_3_partial`: there is exactly one Kuhn–Tucker vector if and only if
  $\inf F$ is differentiable at $0$, and it is then $-\nabla (\inf F)(0)$.
* Corollary 29.1.4, `Rockafellar.corollary_29_1_4_nonempty`,
  `Rockafellar.corollary_29_1_4_dirDeriv`: under strong consistency a Kuhn–Tucker vector exists, and
  $(\inf F)'(0; u) = -\inf \{\langle u, u^* \rangle \mid u^* \text{ a Kuhn–Tucker vector}\}$.
* Corollary 29.1.5, `Rockafellar.corollary_29_1_5_nbhd`, `Rockafellar.corollary_29_1_5_nonempty`,
  `Rockafellar.corollary_29_1_5_isClosed`, `Rockafellar.corollary_29_1_5_isBounded`,
  `Rockafellar.corollary_29_1_5_convex`, `Rockafellar.corollary_29_1_5_isCompact`: under strict
  consistency $\inf F$ is finite and continuous near $0$, and the Kuhn–Tucker set is nonempty,
  closed, bounded, convex and compact.
* Corollary 29.1.6, `Rockafellar.corollary_29_1_6_bot`, `Rockafellar.corollary_29_1_6_top`: if
  $(\inf F)(u) = -\infty$ for some $u$, then $(\inf F)(u) = -\infty$ for every
  $u \in \operatorname{ri}(\operatorname{dom} F)$; and $(\inf F)(u) = +\infty$ for
  $u \notin \operatorname{dom} F$.
* Theorem 29.2, `Rockafellar.theorem_29_2_objective`, `Rockafellar.theorem_29_2_infBifun`,
  `Rockafellar.theorem_29_2_argmin_nonempty`, `Rockafellar.theorem_29_2_kuhnTucker_nonempty`,
  `Rockafellar.theorem_29_2_polyhedral_argmin`, `Rockafellar.theorem_29_2_polyhedral_kuhnTucker`:
  for a polyhedral convex bifunction, $F0$ and $\inf F$ are polyhedral, and at a finite optimal
  value an optimal solution and a Kuhn–Tucker vector exist and both sets are polyhedral.
* Theorem 29.3, `Rockafellar.theorem_29_3`, `Rockafellar.theorem_29_3_isSaddlePoint`: for a closed
  proper convex bifunction, $\bar u^*$ is a Kuhn–Tucker vector and $\bar x$ is an optimal solution
  if and only if $(\bar u^*, \bar x)$ is a saddle-point of $L$.
* Corollary 29.3.1, `Rockafellar.corollary_29_3_1_stronglyConsistent`,
  `Rockafellar.corollary_29_3_1_strictlyConsistent`, `Rockafellar.corollary_29_3_1_polyhedral`:
  under strong consistency, strict consistency, or polyhedral convexity and consistency, $\bar x$ is
  optimal if and only if some $\bar u^*$ makes $(\bar u^*, \bar x)$ a saddle-point of $L$.
* Theorem 29.4, `Rockafellar.theorem_29_4_apply`, `Rockafellar.theorem_29_4_inf`,
  `Rockafellar.theorem_29_4_dom_subset`, `Rockafellar.theorem_29_4_dom_subset_closure`:
  $(\operatorname{cl} F)u = \operatorname{cl}(Fu)$ and $\inf (\operatorname{cl} F)u = \inf Fu$ for
  $u \in \operatorname{ri}(\operatorname{dom} F)$, and $\operatorname{dom} F \subseteq
  \operatorname{dom}(\operatorname{cl} F) \subseteq \operatorname{cl}(\operatorname{dom} F)$ for
  proper $F$.
* Corollary 29.4.1, `Rockafellar.corollary_29_4_1_relint`,
  `Rockafellar.corollary_29_4_1_stronglyConsistent`, `Rockafellar.corollary_29_4_1_objective`,
  `Rockafellar.corollary_29_4_1_optimalValue`, `Rockafellar.corollary_29_4_1_argmin`,
  `Rockafellar.corollary_29_4_1_optimalSolution`, `Rockafellar.corollary_29_4_1_eventually`,
  `Rockafellar.corollary_29_4_1_kuhnTucker`, `Rockafellar.corollary_29_4_1_perturbation_false`:
  under strong consistency, $(\operatorname{cl} P)$ is strongly consistent and has the objective
  function $\operatorname{cl}(F0)$, the same optimal value, at least the same optimal solutions, and
  the same Kuhn–Tucker vectors; its perturbation function agrees with that of $(P)$ near $0$ when
  $F$ is proper, and not in general.

## Conventions

* A bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ is `ConvexAnalysis.Bifun (Rn m) (Rn n)`, a
  function `Rn m → Rn n → EReal`, and $(Fu)(x)$ is `F u x`. The objective function $F0$ is `F 0`.
* The book's notions are backbone declarations: the graph function is `ConvexAnalysis.graphFn F`,
  convexity of $F$ is `ConvexAnalysis.ConvexBifun F`, closedness is
  `ConvexAnalysis.ClosedConvexBifun F`, properness is `ConvexAnalysis.ProperConvex
  (ConvexAnalysis.graphFn F)`, and polyhedral convexity is `ConvexAnalysis.PolyhedralBifun F`.
* The set $\operatorname{dom} F = \{u \mid (Fu)(x) < +\infty \text{ for some } x\}$ is
  `ConvexAnalysis.convexDomBifun F`, the perturbation function $\inf F$ is
  `ConvexAnalysis.infBifun F`, and the optimal value in $(P)$ is `ConvexAnalysis.infBifun F 0`.
* $(P)$ is consistent if $0 \in \operatorname{dom} F$ (`ConvexAnalysis.Consistent`), strongly
  consistent if $0 \in \operatorname{ri}(\operatorname{dom} F)$
  (`ConvexAnalysis.StronglyConsistent`), and strictly consistent if
  $0 \in \operatorname{int}(\operatorname{dom} F)$ (`ConvexAnalysis.StrictlyConsistent`).
* The set of Kuhn–Tucker vectors is `ConvexAnalysis.KuhnTucker (Rockafellar.pairing m) F`, and the
  Lagrangian $L$ is `ConvexAnalysis.lagrangian (Rockafellar.pairing m) F`, both with the Euclidean
  inner product on $\mathbb{R}^m$. As a function on $\mathbb{R}^m \times \mathbb{R}^n$, $L$ is
  `ConvexAnalysis.saddleLagrangian (Rockafellar.pairing m) F`.
* The closure $\operatorname{cl} F$ is `ConvexAnalysis.convexClBifun F`, the bifunction whose graph
  function is the closure of the graph function of $F$.

## Implementation notes

* An optimal solution is `Rockafellar.IsOptimalSolution`, not a minimizer of $F0$. The book requires
  $(F0)(x)$ to be finite and equal to the optimal value. So an inconsistent program has no optimal
  solutions, although every point minimizes the constant function $F0 = +\infty$. The two notions
  agree when $F0$ never takes the value $-\infty$ and $(P)$ is consistent
  (`Rockafellar.isOptimalSolution_iff_mem_argmin`).
* The closure of a convex function follows the book: it is the lower semicontinuous hull, except
  that it is the constant $-\infty$ if the hull takes the value $-\infty$ somewhere
  (`ConvexAnalysis.convexCl`). Theorem 29.4 and the counterexample to Corollary 29.4.1 depend on
  this convention.
* Some clauses hold with fewer hypotheses than the book states, and the declarations carry only the
  hypotheses that they need. For example, the Kuhn–Tucker set is convex and closed whenever the
  optimal value is finite, with no convexity of $F$.

## Deviations from the source

* **Theorem 29.1** (generalization). The book states the theorem for a convex bifunction. The
  equation $\operatorname{dom}(\inf F) = \operatorname{dom} F$ and the description of the
  Kuhn–Tucker vectors by $\partial(\inf F)(0)$ hold for every bifunction. See
  `Rockafellar.theorem_29_1` and `Rockafellar.theorem_29_1_dom`.
* **Corollary 29.1.6**, the parenthesis (generalization). The equation $(\inf F)(u) = +\infty$ for
  $u \notin \operatorname{dom} F$ holds for every bifunction, without the hypotheses of the
  corollary. See `Rockafellar.corollary_29_1_6_top`.
* **Theorem 29.2**, existence of an optimal solution (generalization). The book assumes that the
  optimal value is finite. The statement assumes only that it is not $-\infty$, and concludes that
  $F0$ attains its infimum. See `Rockafellar.theorem_29_2_argmin_nonempty`.
* **Corollary 29.4.1**, perturbation clause (correction). The book states that the perturbation
  functions of $(P)$ and $(\operatorname{cl} P)$ agree on a neighbourhood of $0$ for every convex
  bifunction $F$ with $(P)$ strongly consistent. This is false: the convex bifunction
  `Rockafellar.originBifun` on $\mathbb{R}^1$, which is not proper, is a counterexample; see
  `Rockafellar.corollary_29_4_1_perturbation_false`. The statement adds the hypothesis that $F$ is
  proper. See `Rockafellar.corollary_29_4_1_eventually`.
-/

open Filter Topology
open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis

/-! ### The section's vocabulary -/

section Vocabulary

variable {m n : ℕ}

/-- The **graph domain** of a bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$: the effective
domain $\{(u, x) \mid (Fu)(x) < +\infty\} \subseteq \mathbb{R}^m \times \mathbb{R}^n$ of its
graph function. It is convex when $F$ is convex (`Rockafellar.convex_graphDomain`). -/
def graphDomain (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n) := convexDom (graphFn F)

/-- The graph domain of $F$ is the effective domain of the graph function of $F$. -/
theorem graphDomain_eq (F : Bifun (Rn m) (Rn n)) : graphDomain F = convexDom (graphFn F) := rfl

/-- A pair $(u, x)$ lies in the graph domain of $F$ if and only if $(Fu)(x) < +\infty$. -/
@[simp] theorem mem_graphDomain {F : Bifun (Rn m) (Rn n)} {u : Rn m} {x : Rn n} :
    (u, x) ∈ graphDomain F ↔ F u x < ⊤ := Iff.rfl

/-- The set $\operatorname{dom} F$ is the projection of the graph domain of $F$ on $\mathbb{R}^m$.
Every step of Theorem 29.4 that concerns relative interiors uses this identification. -/
theorem convexDomBifun_eq_image_graphDomain (F : Bifun (Rn m) (Rn n)) :
    convexDomBifun F = LinearMap.fst ℝ (Rn m) (Rn n) '' graphDomain F :=
  convexDomBifun_eq_image_convexDom_graphFn F

/-- The graph domain of a convex bifunction is convex. -/
theorem convex_graphDomain {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F) :
    Convex ℝ (graphDomain F) :=
  ConvexFn.convex_convexDom hF

/-- **Section 29** of [rockafellar1970convex], definition of optimal solutions. Let $F$ be a
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. A vector $x \in \mathbb{R}^n$ is an **optimal
solution** to the program $(P)$ associated with $F$ if $(F0)(x)$ is finite and equal to the
optimal value $(\inf F)(0)$ in $(P)$.

This is not the set of minimizers of $F0$. The book states that "we do not speak of optimal
solutions to $(P)$ when $(P)$ is inconsistent", and the finiteness condition also excludes the
optimal value $-\infty$. -/
def IsOptimalSolution (F : Bifun (Rn m) (Rn n)) (x : Rn n) : Prop :=
  F 0 x ≠ ⊤ ∧ F 0 x ≠ ⊥ ∧ F 0 x = infBifun F 0

/-- Let $F$ be a bifunction such that $F0$ never takes the value $-\infty$ and $(P)$ is consistent,
that is, $(\inf F)(0) < +\infty$. Then $x$ is an optimal solution to $(P)$ if and only if $x$
minimizes $F0$ over $\mathbb{R}^n$. This connects `Rockafellar.IsOptimalSolution` with
`ConvexAnalysis.argmin`. -/
theorem isOptimalSolution_iff_mem_argmin {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (hb : ∀ y, F 0 y ≠ ⊥) (ht : infBifun F 0 ≠ ⊤) :
    IsOptimalSolution F x ↔ x ∈ argmin (F 0) := by
  constructor
  · rintro ⟨-, -, hx⟩
    intro z
    rw [hx, infBifun_apply]
    exact iInf_le _ z
  · intro hx
    have hval : F 0 x = infBifun F 0 := by
      rw [infBifun_apply]
      exact le_antisymm (le_iInf hx) (iInf_le _ x)
    exact ⟨by rw [hval]; exact ht, hb x, hval⟩

/-- If the optimal value $(\inf F)(0)$ is $-\infty$, then $(P)$ has no optimal solution, because an
optimal solution requires a finite optimal value. -/
theorem not_isOptimalSolution_of_infBifun_eq_bot {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (h : infBifun F 0 = ⊥) : ¬ IsOptimalSolution F x := by
  rintro ⟨-, hne, hval⟩
  exact hne (by rw [hval, h])

/-- The saddle-point condition of Theorem 29.3 as the book writes it: $(\bar u^*, \bar x)$ is a
saddle-point of the Lagrangian $L$ of $F$ if and only if
$$L(u^*, \bar x) \le L(\bar u^*, \bar x) \le L(\bar u^*, x) \qquad \text{for all } u^* \in
  \mathbb{R}^m, \ x \in \mathbb{R}^n.$$
-/
theorem isSaddlePoint_lagrangian_iff_forall (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔
      (∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y :=
  Iff.rfl

end Vocabulary

/-! ### The indicator bifunction of a linear transformation -/

section LinearIndicator

variable {m n : ℕ}

/-- The **indicator bifunction of a linear transformation** $A : \mathbb{R}^m \to \mathbb{R}^n$:
$(Fu)(x) = \delta(x \mid Au)$, which is $0$ if $x = Au$ and $+\infty$ otherwise.

It is the backbone's indicator bifunction `ConvexAnalysis.ConvexProcess.indicatorBifun` of the
convex process `ConvexAnalysis.ConvexProcess.ofLinearMap A`. -/
noncomputable def linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) : Bifun (Rn m) (Rn n) :=
  (ConvexProcess.ofLinearMap A).indicatorBifun

/-- The indicator bifunction of $A$ is $(Fu)(x) = \delta(x \mid \{Au\})$. -/
theorem linearIndicatorBifun_apply (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) (x : Rn n) :
    linearIndicatorBifun A u x = indicatorFn {A u} x := by
  rw [linearIndicatorBifun, ConvexProcess.indicatorBifun_apply, ConvexProcess.eval_ofLinearMap]

/-- The graph function of the indicator bifunction of $A$ is the indicator function of the graph
$\{(u, x) \mid x = Au\}$ of $A$, a linear subspace of $\mathbb{R}^m \times \mathbb{R}^n$. -/
theorem graphFn_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    graphFn (linearIndicatorBifun A) = indicatorFn {p : Rn m × Rn n | p.2 = A p.1} :=
  ConvexProcess.graphFn_indicatorBifun _

/-- The indicator bifunction of a linear transformation is convex. -/
theorem convexBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ConvexBifun (linearIndicatorBifun A) :=
  ConvexProcess.convexBifun_indicatorBifun _

/-- The indicator bifunction of a linear transformation is closed. -/
theorem closedConvexBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ClosedConvexBifun (linearIndicatorBifun A) := by
  rw [ClosedConvexBifun, graphFn_linearIndicatorBifun]
  refine closedConvex_indicatorFn ?_
  have hker : {p : Rn m × Rn n | p.2 = A p.1}
      = LinearMap.ker ((LinearMap.snd ℝ (Rn m) (Rn n)) - A ∘ₗ LinearMap.fst ℝ (Rn m) (Rn n)) := by
    ext p
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hker]
  exact (LinearMap.ker _).closed_of_finiteDimensional

/-- The indicator bifunction of a linear transformation is proper: its graph function is proper. -/
theorem properConvex_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ProperConvex (graphFn (linearIndicatorBifun A)) := by
  rw [graphFn_linearIndicatorBifun]
  exact ⟨⟨(0, A 0), by simp⟩, indicatorFn_ne_bot _⟩

/-- The indicator bifunction of a linear transformation has $\operatorname{dom} F = \mathbb{R}^m$.
-/
@[simp] theorem convexDomBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    convexDomBifun (linearIndicatorBifun A) = Set.univ := by
  rw [linearIndicatorBifun, ConvexProcess.convexDomBifun_indicatorBifun,
    ConvexProcess.dom_ofLinearMap]

end LinearIndicator

/-! ### Theorem 29.1 -/

section Theorem291

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m}

/-- **Theorem 29.1** of [rockafellar1970convex], convexity. If $F$ is a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, then its perturbation function $(\inf F)(u) = \inf_x (Fu)(x)$
is a convex function on $\mathbb{R}^m$.

The function $\inf F$ is the image of the graph function of $F$ under the projection
$(u, x) \mapsto u$, so this is Theorem 5.7. -/
theorem theorem_29_1_convexFn (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_infBifun hF

/-- **Theorem 29.1** of [rockafellar1970convex], effective domain. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, $\operatorname{dom}(\inf F) = \operatorname{dom} F$.

**Generalization.** The book assumes that $F$ is convex. No hypothesis is needed:
$(\inf F)(u) = +\infty$ only if $Fu$ is the constant $+\infty$. -/
theorem theorem_29_1_dom (F : Bifun (Rn m) (Rn n)) : convexDom (infBifun F) = convexDomBifun F :=
  convexDom_infBifun F

/-- A vector $u^*$ is a Kuhn–Tucker vector for $(P)$ if and only if the optimal value $(\inf F)(0)$
is finite and
$$(\inf F)(0) \le \langle u, u^* \rangle + (\inf F)(u) \qquad \text{for every } u \in
  \mathbb{R}^m.$$
The book records this reformulation of the definition immediately after the definition. -/
theorem theorem_29_1_forall_le :
    v ∈ KuhnTucker (pairing m) F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u : Rn m, infBifun F 0 ≤ ((pairing m u v : ℝ) : EReal) + infBifun F u :=
  mem_kuhnTucker_iff_forall_le

/-- **Theorem 29.1** of [rockafellar1970convex], Kuhn–Tucker vectors. Let $F$ be a bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ whose optimal value $(\inf F)(0)$ is finite. Then
$u^* \in \mathbb{R}^m$ is a Kuhn–Tucker vector for $(P)$ if and only if
$-u^* \in \partial (\inf F)(0)$.

**Generalization.** The book states the whole theorem for a convex bifunction. This assertion
uses no convexity: it is a rearrangement of the definition.

The set of Kuhn–Tucker vectors is `ConvexAnalysis.KuhnTucker (Rockafellar.pairing m) F`. -/
theorem theorem_29_1 (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker (pairing m) F ↔ -v ∈ subdifferential (pairing m) (infBifun F) 0 :=
  mem_kuhnTucker_iff_neg_mem_subdifferential ht hb

/-- **Theorem 29.1** of [rockafellar1970convex], Kuhn–Tucker vectors as a set. If the optimal value
$(\inf F)(0)$ is finite, then the set of Kuhn–Tucker vectors for $(P)$ is
$-\partial (\inf F)(0)$. Corollaries 29.1.1–29.1.5 transfer properties of subdifferentials
through this equation. -/
theorem theorem_29_1_set (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = -(subdifferential (pairing m) (infBifun F) 0) :=
  kuhnTucker_eq_neg_subdifferential ht hb

end Theorem291

/-! ### Corollary 29.1.1 -/

section Corollary2911

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.1** of [rockafellar1970convex], monotonicity of the difference quotient. Let
$F$ be a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ whose optimal value
$(\inf F)(0)$ is a real number, and let $u \in \mathbb{R}^m$. Then the difference quotient
$$\lambda \mapsto \frac{(\inf F)(\lambda u) - (\inf F)(0)}{\lambda}$$
is nondecreasing on $\lambda > 0$.

The Lean statement writes $\lambda u$ as `0 + a • u`, the form of `ConvexAnalysis.dirDeriv` at
the point $0$. -/
theorem corollary_29_1_1_monotone {r : ℝ} (hF : ConvexBifun F) (hr : infBifun F 0 = (r : EReal))
    (u : Rn m) :
    MonotoneOn (fun a : ℝ => (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal))
      (Set.Ioi 0) :=
  monotoneOn_sub_div (convexFn_infBifun hF) hr u

/-- **Corollary 29.1.1** of [rockafellar1970convex], the directional derivative. For every
bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ and every $u \in \mathbb{R}^m$,
$$(\inf F)'(0; u) = \inf_{\lambda > 0} \frac{(\inf F)(\lambda u) - (\inf F)(0)}{\lambda}.$$

This is the definition of `ConvexAnalysis.dirDeriv`, so no hypothesis is needed. -/
theorem corollary_29_1_1_iInf (F : Bifun (Rn m) (Rn n)) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = ⨅ a ∈ Set.Ioi (0 : ℝ), (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal) :=
  dirDeriv_apply _ 0 u

/-- **Corollary 29.1.1** of [rockafellar1970convex], positive homogeneity. For every bifunction $F$,
the directional derivative $(\inf F)'(0; \cdot)$ is positively homogeneous: $(\inf F)'(0;
\lambda u) = \lambda (\inf F)'(0; u)$ for every $\lambda > 0$ and every $u$.

The proof is a change of variable in the infimum, and needs no hypothesis. -/
theorem corollary_29_1_1_posHomogeneous (F : Bifun (Rn m) (Rn n)) :
    PosHomogeneous (dirDeriv (infBifun F) 0) :=
  posHomogeneous_dirDeriv_infBifun F

/-- **Corollary 29.1.1** of [rockafellar1970convex], convexity of the directional derivative. If $F$
is a convex bifunction and the optimal value $(\inf F)(0)$ is finite, then $(\inf F)'(0; \cdot)$
is a convex function on $\mathbb{R}^m$. -/
theorem corollary_29_1_1_convexFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : ConvexFn (dirDeriv (infBifun F) 0) :=
  convexFn_dirDeriv_infBifun hF ht hb

/-- **Corollary 29.1.1** of [rockafellar1970convex], convexity of the Kuhn–Tucker set. If the
optimal value $(\inf F)(0)$ is finite, then the set of Kuhn–Tucker vectors for $(P)$ is convex. -/
theorem corollary_29_1_1_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  convex_kuhnTucker ht hb

/-- **Corollary 29.1.1** of [rockafellar1970convex], closedness of the Kuhn–Tucker set. If the
optimal value $(\inf F)(0)$ is finite, then the set of Kuhn–Tucker vectors for $(P)$ is closed. -/
theorem corollary_29_1_1_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  isClosed_kuhnTucker ht hb

/-- **Corollary 29.1.1** of [rockafellar1970convex], the support function of the Kuhn–Tucker set.
Let $F$ be a convex bifunction whose optimal value $(\inf F)(0)$ is finite, and let $K$ be the
set of Kuhn–Tucker vectors for $(P)$. Then for every $u \in \mathbb{R}^m$,
$$\sup \{\langle u^*, u \rangle \mid u^* \in K\} = \operatorname{cl}\big((\inf F)'(0;
  \cdot)\big)(-u).$$

Replacing $u$ by $-u$ gives the form of the book, $\operatorname{cl}\big((\inf F)'(0;
\cdot)\big)(u) = -\inf \{\langle u^*, u \rangle \mid u^* \in K\}$. The left side is
`ConvexAnalysis.supportFn` of $K$, and the closure is `ConvexAnalysis.convexCl`. -/
theorem corollary_29_1_1_supportFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    supportFn (pairing m) (KuhnTucker (pairing m) F) u
      = convexCl (dirDeriv (infBifun F) 0) (-u) := by
  have h := supportFn_kuhnTucker (B := pairing m) hF ht hb u
  rwa [flip_pairing] at h

end Corollary2911

/-! ### Corollary 29.1.2 -/

section Corollary2912

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.2** of [rockafellar1970convex]. Let $F$ be a convex bifunction whose optimal
value $(\inf F)(0)$ is finite. Then $(P)$ has no Kuhn–Tucker vector if and only if there is a
vector $u \in \mathbb{R}^m$ with
$$(\inf F)'(0; u) = -\infty \quad \text{and} \quad (\inf F)'(0; -u) = +\infty.$$

So the condition is on the two-sided directional derivative of the optimal value. In the
interpretation of Kuhn–Tucker vectors as equilibrium prices, $(P)$ has one unless perturbation
in some direction is "infinitely advantageous". -/
theorem corollary_29_1_2 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = ∅ ↔
      ∃ u : Rn m, dirDeriv (infBifun F) 0 u = ⊥ ∧ dirDeriv (infBifun F) 0 (-u) = ⊤ :=
  kuhnTucker_eq_empty_iff hF ht hb

end Corollary2912

/-! ### Corollary 29.1.3 -/

section Corollary2913

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {b : Rn m}

/-- **Corollary 29.1.3** of [rockafellar1970convex]. Let $F$ be a convex bifunction whose optimal
value $(\inf F)(0)$ is finite. Then $(P)$ has exactly one Kuhn–Tucker vector if and only if the
perturbation function $\inf F$ is differentiable at $0$.

Differentiability is `ConvexAnalysis.DifferentiableAtFn`: near $0$, $\inf F$ agrees with a
real-valued function that is Fréchet differentiable at $0$. The proof of the book cites Theorem
25.1, which needs properness, and a finite optimal value does not give properness. The
hypotheses of the book suffice anyway: each side of the equivalence implies that $\inf F$ is
proper, by `ConvexAnalysis.properConvex_of_mem_subdifferential` and
`ConvexAnalysis.HasGradientAtFn.proper`. -/
theorem corollary_29_1_3 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (∃ v : Rn m, KuhnTucker (pairing m) F = {v}) ↔ DifferentiableAtFn (infBifun F) 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hsub : subdifferential (pairing m) (infBifun F) 0 = {-v} := by
      have h := theorem_29_1_set (F := F) ht hb
      rw [hv] at h
      have h2 : subdifferential (pairing m) (infBifun F) 0 = -({v} : Set (Rn m)) := by
        rw [h, neg_neg]
      rw [h2, Set.neg_singleton]
    have hmem : -v ∈ subdifferential (pairing m) (infBifun F) 0 := by rw [hsub]; rfl
    have hp : ProperConvex (infBifun F) := properConvex_of_mem_subdifferential ht hb hmem
    exact (theorem_25_1_differentiableAtFn (convexFn_infBifun hF) hp).2 ⟨-v, hsub⟩
  · intro hd
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
    have hp : ProperConvex (infBifun F) := corollary_25_1_1_proper (convexFn_infBifun hF) hc
    refine ⟨-c, ?_⟩
    rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) hc,
      Set.neg_singleton]

/-- **Corollary 29.1.3** of [rockafellar1970convex], the formula. Let $F$ be a convex bifunction
whose optimal value $(\inf F)(0)$ is finite. If $\inf F$ is differentiable at $0$ with gradient
$\nabla (\inf F)(0) = b$, then the unique Kuhn–Tucker vector for $(P)$ is $-b$. -/
theorem corollary_29_1_3_eq (hF : ConvexBifun F) (h : HasGradientVecAt (infBifun F) b 0)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = {-b} := by
  rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) h, Set.neg_singleton]

/-- **Corollary 29.1.3** of [rockafellar1970convex], the coordinates. Let $F$ be a convex
bifunction, let $u^* = (v_1^*, \dots, v_m^*)$ be a Kuhn–Tucker vector for $(P)$, and let
$\inf F$ be differentiable at $0$. Then for $i = 1, \dots, m$, the directional derivative of
$\inf F$ at $0$ in the direction of the $i$-th unit vector $e_i$ is $-v_i^*$. So
$u^* = -\nabla (\inf F)(0)$, coordinate by coordinate. -/
theorem corollary_29_1_3_partial (hF : ConvexBifun F) {v : Rn m}
    (hv : v ∈ KuhnTucker (pairing m) F) (hd : DifferentiableAtFn (infBifun F) 0) (i : Fin m) :
    dirDeriv (infBifun F) 0 (EuclideanSpace.single i (1 : ℝ)) = ((-(v i) : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
  have hset : KuhnTucker (pairing m) F = {-c} :=
    corollary_29_1_3_eq hF hc hv.1 hv.2.1
  have hvc : v = -c := by rw [hset] at hv; exact hv
  rw [theorem_25_2_dirDeriv (convexFn_infBifun hF) hc, hvc]
  congr 1
  rw [pairing_apply, EuclideanSpace.inner_single_left]
  simp

end Corollary2913

/-! ### Strong and strict consistency -/

section Consistency

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- Let $F$ be a convex bifunction. Then $(P)$ is strictly consistent if and only if for every
$u \in \mathbb{R}^m$ there is a $\lambda > 0$ with $\lambda u \in \operatorname{dom} F$. That
is, every direction of perturbation has a positive multiple at which the perturbed program is
consistent. -/
theorem strictlyConsistent_iff (hF : ConvexBifun F) :
    StrictlyConsistent F ↔ ∀ u : Rn m, ∃ a : ℝ, 0 < a ∧ a • u ∈ convexDomBifun F := by
  rw [StrictlyConsistent, Convex.mem_interior_iff_absorbs (convex_convexDomBifun hF)]
  exact forall_congr' fun u => exists_congr fun a => by rw [zero_add]

end Consistency

/-! ### Corollary 29.1.4 -/

section Corollary2914

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

private theorem iSup_coe_neg_eq (S : Set (Rn m)) (g : Rn m → ℝ) :
    (⨆ v ∈ S, ((-(g v) : ℝ) : EReal)) = -(⨅ v ∈ S, ((g v : ℝ) : EReal)) := by
  rw [EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [EReal.neg_iInf]
  exact iSup_congr fun _ => (EReal.coe_neg (g v)).symm

/-- **Corollary 29.1.4** of [rockafellar1970convex], existence. If $F$ is a convex bifunction, $(P)$
is strongly consistent, and the optimal value $(\inf F)(0)$ is finite, then $(P)$ has a
Kuhn–Tucker vector.

The proof applies Theorem 23.4 to $\inf F$, which is proper by Theorem 7.2. -/
theorem corollary_29_1_4_nonempty (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_stronglyConsistent hF
    (properConvex_infBifun_of_stronglyConsistent hF hs hb) hs ht

/-- **Corollary 29.1.4** of [rockafellar1970convex], the formula. Let $F$ be a convex bifunction
such that $(P)$ is strongly consistent and the optimal value $(\inf F)(0)$ is not $-\infty$.
Then for every $u \in \mathbb{R}^m$,
$$(\inf F)'(0; u) = -\inf \{\langle u, u^* \rangle \mid u^* \text{ a Kuhn–Tucker vector for }
  (P)\}.$$

Strong consistency gives $0 \in \operatorname{dom} F$, so the optimal value is then finite. -/
theorem corollary_29_1_4_dirDeriv (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = -(⨅ v ∈ KuhnTucker (pairing m) F, ((pairing m u v : ℝ) : EReal)) := by
  have hp : ProperConvex (infBifun F) := properConvex_infBifun_of_stronglyConsistent hF hs hb
  rw [dirDeriv_infBifun_eq (B := pairing m) hF hp hs u, flip_pairing, supportFn_apply,
    ← iSup_coe_neg_eq]
  refine iSup_congr fun v => iSup_congr fun _ => ?_
  rw [map_neg, pairing_comm v u]

end Corollary2914

/-! ### Corollary 29.1.5 -/

section Corollary2915

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.5** of [rockafellar1970convex], continuity. Let $F$ be a convex bifunction such
that $(P)$ is strictly consistent and the optimal value $(\inf F)(0)$ is not $-\infty$. Then
there is an open convex set $V \subseteq \mathbb{R}^m$ with $0 \in V$ such that $\inf F$ is
finite at every point of $V$ and continuous on $V$.

In the book, this neighbourhood is $\operatorname{int}(\operatorname{dom} F)$. -/
theorem corollary_29_1_5_nbhd (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) :
    ∃ V : Set (Rn m), IsOpen V ∧ Convex ℝ V ∧ (0 : Rn m) ∈ V ∧
      (∀ u ∈ V, infBifun F u ≠ ⊤ ∧ infBifun F u ≠ ⊥) ∧ ContinuousOn (infBifun F) V := by
  have hp : ProperConvex (infBifun F) :=
    properConvex_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb
  refine ⟨interior (convexDomBifun F), isOpen_interior, (convex_convexDomBifun hF).interior, hs,
    fun u hu => ⟨infBifun_ne_top_of_mem_convexDomBifun (interior_subset hu), hp.ne_bot u⟩,
    continuousOn_infBifun_interior hF hp⟩

/-- **Corollary 29.1.5** of [rockafellar1970convex], existence. If $F$ is a convex bifunction, $(P)$
is strictly consistent, and the optimal value $(\inf F)(0)$ is finite, then the set of
Kuhn–Tucker vectors for $(P)$ is nonempty. -/
theorem corollary_29_1_5_nonempty (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_strictlyConsistent hF
    (properConvex_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

/-- **Corollary 29.1.5** of [rockafellar1970convex], closedness. If the optimal value $(\inf F)(0)$
is finite, then the set of Kuhn–Tucker vectors for $(P)$ is closed. -/
theorem corollary_29_1_5_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  corollary_29_1_1_isClosed ht hb

/-- **Corollary 29.1.5** of [rockafellar1970convex], boundedness. If $F$ is a convex bifunction,
$(P)$ is strictly consistent, and the optimal value $(\inf F)(0)$ is not $-\infty$, then the set
of Kuhn–Tucker vectors for $(P)$ is bounded.

Boundedness distinguishes Corollary 29.1.5 from Corollary 29.1.4. Under strong consistency alone
the Kuhn–Tucker set need not be bounded, because Theorem 23.4 bounds $\partial f(x)$ only at
interior points $x$ of $\operatorname{dom} f$. -/
theorem corollary_29_1_5_isBounded (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) : Bornology.IsBounded (KuhnTucker (pairing m) F) :=
  isBounded_kuhnTucker_of_strictlyConsistent hF
    (properConvex_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs

/-- **Corollary 29.1.5** of [rockafellar1970convex], convexity. If the optimal value $(\inf F)(0)$
is finite, then the set of Kuhn–Tucker vectors for $(P)$ is convex. -/
theorem corollary_29_1_5_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  corollary_29_1_1_convex ht hb

/-- **Corollary 29.1.5** of [rockafellar1970convex], compactness. If $F$ is a convex bifunction,
$(P)$ is strictly consistent, and the optimal value $(\inf F)(0)$ is finite, then the set of
Kuhn–Tucker vectors for $(P)$ is compact.

Together with `Rockafellar.corollary_29_1_5_nonempty` and `Rockafellar.corollary_29_1_5_convex`,
this gives the last clause of the corollary: the set is nonempty, convex and compact. -/
theorem corollary_29_1_5_isCompact (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsCompact (KuhnTucker (pairing m) F) :=
  isCompact_kuhnTucker_of_strictlyConsistent hF
    (properConvex_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

end Corollary2915

/-! ### Corollary 29.1.6 -/

section Corollary2916

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.6** of [rockafellar1970convex]. Let $F$ be a convex bifunction. If
$(\inf F)(u) = -\infty$ for some $u \in \mathbb{R}^m$, then $(\inf F)(u) = -\infty$ for every
$u \in \operatorname{ri}(\operatorname{dom} F)$. -/
theorem corollary_29_1_6_bot (hF : ConvexBifun F) (h : ∃ u : Rn m, infBifun F u = ⊥) {u : Rn m}
    (hu : u ∈ ri (convexDomBifun F)) : infBifun F u = ⊥ :=
  infBifun_eq_bot_of_mem_relint hF h hu

/-- **Corollary 29.1.6** of [rockafellar1970convex], the parenthesis. For every bifunction $F$ and
every $u \notin \operatorname{dom} F$, $(\inf F)(u) = +\infty$.

**Generalization.** The corollary assumes that $F$ is convex and that $\inf F$ takes the value
$-\infty$ somewhere. This clause needs neither: it is the equation $\operatorname{dom}(\inf F) =
\operatorname{dom} F$ of Theorem 29.1. -/
theorem corollary_29_1_6_top {u : Rn m} (hu : u ∉ convexDomBifun F) : infBifun F u = ⊤ :=
  infBifun_eq_top_of_notMem_convexDomBifun hu

end Corollary2916

/-! ### Theorem 29.2 -/

section Theorem292

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Theorem 29.2** of [rockafellar1970convex], the objective function. If $F$ is a polyhedral
convex bifunction, then every function $Fu$, and in particular the objective function $F0$, is a
polyhedral convex function.

A polyhedral convex bifunction is one whose graph function is polyhedral convex
(`ConvexAnalysis.PolyhedralBifun`). -/
theorem theorem_29_2_objective (hF : PolyhedralBifun F) (u : Rn m) : PolyhedralFn (F u) :=
  hF.polyhedralFn_apply u

/-- **Theorem 29.2** of [rockafellar1970convex], the perturbation function. If $F$ is a polyhedral
convex bifunction, then its perturbation function $\inf F$ is a polyhedral convex function.

This is Corollary 19.3.1 for the projection $(u, x) \mapsto u$. -/
theorem theorem_29_2_infBifun (hF : PolyhedralBifun F) : PolyhedralFn (infBifun F) :=
  hF.polyhedralFn_infBifun

/-- **Theorem 29.2** of [rockafellar1970convex], existence of an optimal solution. If $F$ is a
polyhedral convex bifunction and the optimal value $(\inf F)(0)$ is not $-\infty$, then $F0$
attains its infimum: the set of minimizers of $F0$ is nonempty.

**Generalization.** The book assumes that the optimal value is finite. The bound
$(\inf F)(0) > -\infty$ alone bounds $F0$ below, and Corollary 27.3.2 then gives a minimizer. If
the optimal value is finite, the minimizers of $F0$ are the optimal solutions
(`Rockafellar.isOptimalSolution_iff_mem_argmin`). Finiteness is needed for the polyhedral
clauses below. -/
theorem theorem_29_2_argmin_nonempty (hF : PolyhedralBifun F) (hb : infBifun F 0 ≠ ⊥) :
    (argmin (F 0)).Nonempty :=
  argmin_nonempty_of_polyhedralBifun hF hb

/-- **Theorem 29.2** of [rockafellar1970convex], existence of a Kuhn–Tucker vector. If $F$ is a
polyhedral convex bifunction and the optimal value $(\inf F)(0)$ is finite, then $(P)$ has at
least one Kuhn–Tucker vector.

The proof applies Theorem 23.10 to $\inf F$ at $0$. -/
theorem theorem_29_2_kuhnTucker_nonempty (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_polyhedralBifun hF ht hb

/-- **Theorem 29.2** of [rockafellar1970convex], the optimal solutions. If $F$ is a polyhedral
convex bifunction and the optimal value $(\inf F)(0)$ is finite, then the set of minimizers of
$F0$ is a polyhedral convex set.

The set is a level set of the polyhedral convex function $F0$ at the optimal value. -/
theorem theorem_29_2_polyhedral_argmin (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (argmin (F 0)) :=
  polyhedral_argmin_of_polyhedralBifun hF ht hb

/-- **Theorem 29.2** of [rockafellar1970convex], the Kuhn–Tucker vectors. If $F$ is a polyhedral
convex bifunction and the optimal value $(\inf F)(0)$ is finite, then the set of Kuhn–Tucker
vectors for $(P)$ is a polyhedral convex set. -/
theorem theorem_29_2_polyhedral_kuhnTucker (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (KuhnTucker (pairing m) F) :=
  polyhedral_kuhnTucker_of_polyhedralBifun hF ht hb

end Theorem292

/-! ### Theorem 29.3 -/

section Theorem293

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m} {x : Rn n}

/-- **Theorem 29.3** of [rockafellar1970convex]. Let $F$ be a closed proper convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, with Lagrangian $L(u^*, x) = \inf_u \{\langle u, u^* \rangle +
(Fu)(x)\}$. Then $\bar u^*$ is a Kuhn–Tucker vector for $(P)$ and $\bar x$ is an optimal
solution to $(P)$ if and only if
$$L(u^*, \bar x) \le L(\bar u^*, \bar x) \le L(\bar u^*, x) \qquad \text{for all } u^* \in
  \mathbb{R}^m, \ x \in \mathbb{R}^n,$$
that is, if and only if $(\bar u^*, \bar x)$ is a saddle-point of $L$.

"Closed proper convex" means that the graph function of $F$ is closed, proper and convex. The
Lagrangian is `ConvexAnalysis.lagrangian (Rockafellar.pairing m) F`. -/
theorem theorem_29_3 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) :
    ((∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [← isSaddlePoint_lagrangian_iff_forall, isSaddlePoint_lagrangian_iff hF hcl hpr]
  refine and_congr_right fun hv => ?_
  exact (isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) hv.1).symm

/-- **Theorem 29.3** of [rockafellar1970convex], saddle-point form. Let $F$ be a closed proper
convex bifunction. Then $(\bar u^*, \bar x)$ is a saddle-point of the Lagrangian of $F$, in the
sense of `ConvexAnalysis.IsSaddlePoint`, if and only if $\bar u^*$ is a Kuhn–Tucker vector for
$(P)$ and $\bar x$ is an optimal solution to $(P)$. -/
theorem theorem_29_3_isSaddlePoint (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [isSaddlePoint_lagrangian_iff_forall]
  exact theorem_29_3 hF hcl hpr

end Theorem293

/-! ### Corollary 29.3.1 -/

section Corollary2931

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- The common part of the three cases of Corollary 29.3.1: for a closed proper convex consistent
program in which a finite optimal value implies a Kuhn–Tucker vector, $\bar x$ is optimal if and
only if some $\bar u^*$ makes $(\bar u^*, \bar x)$ a saddle-point of the Lagrangian. -/
private theorem corollary_29_3_1_aux (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hc : Consistent F)
    (hkt : infBifun F 0 ≠ ⊥ → (KuhnTucker (pairing m) F).Nonempty) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) := by
  by_cases hb : infBifun F 0 = ⊥
  · refine ⟨fun h => absurd h (not_isOptimalSolution_of_infBifun_eq_bot hb), ?_⟩
    rintro ⟨v, hv⟩
    exact absurd ((theorem_29_3_isSaddlePoint hF hcl hpr).1 hv).1.2.1 (not_not.2 hb)
  · have ht : infBifun F 0 ≠ ⊤ := infBifun_ne_top_of_mem_convexDomBifun hc
    rw [isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) ht]
    exact mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr (hkt hb)

/-- **Corollary 29.3.1** of [rockafellar1970convex], the strongly consistent case. Let $F$ be a
closed proper convex bifunction such that $(P)$ is strongly consistent. Then $\bar x$ is an
optimal solution to $(P)$ if and only if there is a vector $\bar u^*$ such that
$(\bar u^*, \bar x)$ is a saddle-point of the Lagrangian of $F$. -/
theorem corollary_29_3_1_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF hcl hpr hs.consistent fun hb =>
    corollary_29_1_4_nonempty hF hs (infBifun_ne_top_of_mem_convexDomBifun hs.consistent) hb

/-- **Corollary 29.3.1** of [rockafellar1970convex], the strictly consistent case. Let $F$ be a
closed proper convex bifunction such that $(P)$ is strictly consistent. Then $\bar x$ is an
optimal solution to $(P)$ if and only if there is a vector $\bar u^*$ such that
$(\bar u^*, \bar x)$ is a saddle-point of the Lagrangian of $F$.

A strictly consistent program is strongly consistent, so this follows from
`Rockafellar.corollary_29_3_1_stronglyConsistent`. -/
theorem corollary_29_3_1_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Corollary 29.3.1** of [rockafellar1970convex], the polyhedral case. Let $F$ be a polyhedral
convex bifunction that is closed and proper, such that $(P)$ is consistent. Then $\bar x$ is an
optimal solution to $(P)$ if and only if there is a vector $\bar u^*$ such that
$(\bar u^*, \bar x)$ is a saddle-point of the Lagrangian of $F$.

Consistency suffices here because Theorem 29.2 gives a Kuhn–Tucker vector with no condition on
the relative interior. -/
theorem corollary_29_3_1_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF.convexBifun hcl hpr hc fun hb =>
    theorem_29_2_kuhnTucker_nonempty hF (infBifun_ne_top_of_mem_convexDomBifun hc) hb

end Corollary2931

/-!
### Theorem 29.4

The closure $\operatorname{cl} F$ of a bifunction $F$ is the bifunction whose graph function is the
closure of the graph function of $F$. Closing a program regularizes it before Theorem 29.3 or the
duality theory of Section 30 is applied.
-/

section Theorem294

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- If $F$ is a convex bifunction, then $\operatorname{cl} F$ is convex. -/
theorem convexClBifun_convex (hF : ConvexBifun F) : ConvexBifun (convexClBifun F) :=
  ConvexBifun.convexClBifun hF

/-- For every bifunction $F$, the bifunction $\operatorname{cl} F$ is closed. -/
theorem convexClBifun_closed (F : Bifun (Rn m) (Rn n)) : ClosedConvexBifun (convexClBifun F) :=
  closedConvexBifun_convexClBifun F

/-- If $F$ is a proper convex bifunction, then $\operatorname{cl} F$ is proper. -/
theorem convexClBifun_properConvex (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    ProperConvex (graphFn (convexClBifun F)) :=
  ConvexFn.properConvex_convexCl hF hp

/-- **Theorem 29.4** of [rockafellar1970convex], the functions. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(\operatorname{cl} F)u = \operatorname{cl}(Fu)$ for
every $u \in \operatorname{ri}(\operatorname{dom} F)$.

The closure of a convex function that takes the value $-\infty$ somewhere is the constant
$-\infty$, not the lower semicontinuous hull. The statement and its proof depend on this
convention of the book (`ConvexAnalysis.convexCl`). -/
theorem theorem_29_4_apply (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (convexDomBifun F)) :
    convexClBifun F u = convexCl (F u) :=
  convexClBifun_apply_eq_convexCl hF hu

/-- **Theorem 29.4** of [rockafellar1970convex], the infima. Let $F$ be a convex bifunction. Then
$\inf (\operatorname{cl} F)u = \inf Fu$ for every
$u \in \operatorname{ri}(\operatorname{dom} F)$.

A convex function and its closure have the same infimum, so this follows from the first
assertion. -/
theorem theorem_29_4_inf (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (convexDomBifun F)) :
    infBifun (convexClBifun F) u = infBifun F u :=
  infBifun_convexClBifun_eq hF hu

/-- **Theorem 29.4** of [rockafellar1970convex], the domains, first inclusion. If $F$ is a proper
convex bifunction, then $\operatorname{dom} F \subseteq \operatorname{dom}(\operatorname{cl}
F)$. -/
theorem theorem_29_4_dom_subset (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    convexDomBifun F ⊆ convexDomBifun (convexClBifun F) :=
  convexDomBifun_subset_convexDomBifun_convexClBifun hF hp

/-- **Theorem 29.4** of [rockafellar1970convex], the domains, second inclusion. If $F$ is a proper
convex bifunction, then $\operatorname{dom}(\operatorname{cl} F) \subseteq
\operatorname{cl}(\operatorname{dom} F)$.

Properness is needed: `Rockafellar.originBifun` has $\operatorname{dom} F = \{0\}$ and
$\operatorname{dom}(\operatorname{cl} F) = \mathbb{R}^1$. -/
theorem theorem_29_4_dom_subset_closure (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    convexDomBifun (convexClBifun F) ⊆ closure (convexDomBifun F) :=
  convexDomBifun_convexClBifun_subset_closure hF hp

end Theorem294

/-! ### Corollary 29.4.1 -/

section Corollary2941

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- **Corollary 29.4.1** of [rockafellar1970convex], the relative interior of the domain. If $F$ is
a proper convex bifunction, then $\operatorname{ri}(\operatorname{dom}(\operatorname{cl} F)) =
\operatorname{ri}(\operatorname{dom} F)$.

Theorem 29.4 puts $\operatorname{dom}(\operatorname{cl} F)$ between $\operatorname{dom} F$ and
$\operatorname{cl}(\operatorname{dom} F)$, and by Corollary 6.3.1 such a set has the same
relative interior as $\operatorname{dom} F$. -/
theorem corollary_29_4_1_relint (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    ri (convexDomBifun (convexClBifun F)) = ri (convexDomBifun F) :=
  relint_convexDomBifun_convexClBifun hF hp

/-- **Corollary 29.4.1** of [rockafellar1970convex], consistency. If $F$ is a convex bifunction and
$(P)$ is strongly consistent, then $(\operatorname{cl} P)$, the program associated with
$\operatorname{cl} F$, is strongly consistent.

This clause holds without properness. If $F$ is not proper and its graph function takes the
value $-\infty$ somewhere, then $\operatorname{dom}(\operatorname{cl} F) = \mathbb{R}^m$; if its
graph domain is empty, then $(P)$ is not consistent. -/
theorem corollary_29_4_1_stronglyConsistent (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    StronglyConsistent (convexClBifun F) := by
  by_cases hp : ProperConvex (graphFn F)
  · exact stronglyConsistent_convexClBifun hF hp hs
  · have hne : (convexDom (graphFn F)).Nonempty := by
      have h0 : (0 : Rn m) ∈ convexDomBifun F := intrinsicInterior_subset hs
      obtain ⟨x, hx⟩ := h0
      exact ⟨(0, x), mem_convexDom.2 (lt_of_le_of_ne le_top hx)⟩
    have hbot : ∃ p, graphFn F p = ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hp ⟨hne, hcon⟩
    obtain ⟨p, hpbot⟩ := hbot
    have hlsc : lscHull (graphFn F) p = ⊥ :=
      le_bot_iff.1 (le_trans (lscHull_le (graphFn F) p) (le_of_eq hpbot))
    have hcl : convexCl (graphFn F) = fun _ => ⊥ := convexCl_of_exists_eq_bot ⟨p, hlsc⟩
    have hdom : convexDomBifun (convexClBifun F) = Set.univ := by
      ext u
      simp only [mem_convexDomBifun, Set.mem_univ, iff_true]
      exact ⟨0, by rw [convexClBifun_apply, hcl]; simp⟩
    change (0 : Rn m) ∈ ri (convexDomBifun (convexClBifun F))
    rw [hdom]
    exact interior_subset_intrinsicInterior (by simp)

/-- **Corollary 29.4.1** of [rockafellar1970convex], the objective function. If $F$ is a convex
bifunction and $(P)$ is strongly consistent, then the objective function of
$(\operatorname{cl} P)$ is the closure of the objective function of $(P)$:
$(\operatorname{cl} F)0 = \operatorname{cl}(F0)$.

This is Theorem 29.4 at $u = 0$. -/
theorem corollary_29_4_1_objective (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    convexClBifun F 0 = convexCl (F 0) :=
  convexClBifun_zero_eq_convexCl hF hs

/-- **Corollary 29.4.1** of [rockafellar1970convex], the optimal value. If $F$ is a convex
bifunction and $(P)$ is strongly consistent, then $(P)$ and $(\operatorname{cl} P)$ have the
same optimal value: $\inf (\operatorname{cl} F)0 = \inf F0$. -/
theorem corollary_29_4_1_optimalValue (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (convexClBifun F) 0 = infBifun F 0 :=
  infBifun_convexClBifun_zero_eq hF hs

/-- **Corollary 29.4.1** of [rockafellar1970convex], the minimizers. If $F$ is a convex bifunction
and $(P)$ is strongly consistent, then every minimizer of $F0$ is a minimizer of
$(\operatorname{cl} F)0$.

The inclusion can be strict, because the closure can create new minimizers. -/
theorem corollary_29_4_1_argmin (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (convexClBifun F 0) :=
  argmin_subset_argmin_convexClBifun hF hs

/-- **Corollary 29.4.1** of [rockafellar1970convex], the optimal solutions. If $F$ is a convex
bifunction and $(P)$ is strongly consistent, then every optimal solution to $(P)$ is an optimal
solution to $(\operatorname{cl} P)$. -/
theorem corollary_29_4_1_optimalSolution (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (h : IsOptimalSolution F x) : IsOptimalSolution (convexClBifun F) x := by
  have hval : infBifun (convexClBifun F) 0 = infBifun F 0 := infBifun_convexClBifun_zero_eq hF hs
  have hge : infBifun (convexClBifun F) 0 ≤ convexClBifun F 0 x := by
    rw [infBifun_apply]
    exact iInf_le _ x
  have hle : convexClBifun F 0 x ≤ infBifun (convexClBifun F) 0 := by
    rw [hval, ← h.2.2]
    exact convexClBifun_le F 0 x
  have heq : convexClBifun F 0 x = infBifun (convexClBifun F) 0 := le_antisymm hle hge
  refine ⟨?_, ?_, heq⟩
  · rw [heq, hval, ← h.2.2]; exact h.1
  · rw [heq, hval, ← h.2.2]; exact h.2.1

/-- **Corollary 29.4.1** of [rockafellar1970convex], the perturbation functions. Let $F$ be a proper
convex bifunction such that $(P)$ is strongly consistent. Then the perturbation functions of
$(P)$ and $(\operatorname{cl} P)$ agree on a neighbourhood of $0$:
$\inf (\operatorname{cl} F)u = \inf Fu$ for all $u$ near $0$.

**Correction.** The book states this clause without the hypothesis that $F$ is proper. It is
then false: see `Rockafellar.corollary_29_4_1_perturbation_false`.

Theorem 29.4 gives agreement only on $\operatorname{ri}(\operatorname{dom} F)$. For proper $F$,
$\operatorname{dom}(\operatorname{cl} F) \subseteq \operatorname{cl}(\operatorname{dom} F)
\subseteq \operatorname{aff}(\operatorname{dom} F)$, so a small ball around $0$ meets only
points of $\operatorname{ri}(\operatorname{dom} F)$ and points off
$\operatorname{aff}(\operatorname{dom} F)$, where both perturbation functions are $+\infty$.
Properness enters through this inclusion. -/
theorem corollary_29_4_1_eventually (hF : ConvexBifun F) (hp : ProperConvex (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (convexClBifun F) u = infBifun F u :=
  eventually_infBifun_convexClBifun_eq hF hp hs

/-- **Corollary 29.4.1** of [rockafellar1970convex], the Kuhn–Tucker vectors. If $F$ is a convex
bifunction and $(P)$ is strongly consistent, then $(P)$ and $(\operatorname{cl} P)$ have the
same Kuhn–Tucker vectors.

The book deduces this clause from the perturbation clause, which needs properness. The proof
here does not need properness, because the adjoint bifunction of $\operatorname{cl} F$ is the
adjoint of $F$ (`ConvexAnalysis.convexAdjointBifun_convexClBifun`). -/
theorem corollary_29_4_1_kuhnTucker (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    KuhnTucker (pairing m) (convexClBifun F) = KuhnTucker (pairing m) F :=
  kuhnTucker_convexClBifun_eq (Bu := pairing m) (pairing n) hF hs

end Corollary2941

/-!
### Corollary 29.4.1 as printed is false

`Rockafellar.corollary_29_4_1_perturbation` states the perturbation clause of the corollary with the
hypotheses that the book prints, and `Rockafellar.corollary_29_4_1_perturbation_false` refutes it on
$\mathbb{R}^1$.
-/

section Counterexample

/-- The counterexample to the perturbation clause of Corollary 29.4.1 of [rockafellar1970convex] as
printed. It is the bifunction on $\mathbb{R}^1$ with $(Fu)(x) = -\infty$ if $u = 0$ and
$(Fu)(x) = +\infty$ if $u \neq 0$.

The example must make $\operatorname{dom} F$ a proper affine subset of $\mathbb{R}^1$ with the
origin in its relative interior, and $\{0\}$ is the simplest such set. -/
noncomputable def originBifun : Bifun (Rn 1) (Rn 1) := fun u _ => ⨆ _ : u ≠ 0, (⊤ : EReal)

/-- The counterexample has $(F0)(x) = -\infty$ for every $x$. -/
@[simp] theorem originBifun_zero (x : Rn 1) : originBifun 0 x = ⊥ := by
  rw [originBifun, iSup_neg (by simp)]

/-- The counterexample has $(Fu)(x) = +\infty$ for every $u \neq 0$ and every $x$. -/
@[simp] theorem originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) (x : Rn 1) :
    originBifun u x = ⊤ := by
  rw [originBifun, iSup_pos hu]

/-- The counterexample is a convex bifunction: the epigraph of its graph function is the preimage of
$\{0\}$ under a linear map, so it is a linear subspace of $(\mathbb{R}^1 \times \mathbb{R}^1)
\times \mathbb{R}$. -/
theorem convexBifun_originBifun : ConvexBifun originBifun := by
  refine ⟨?_⟩
  have hepi : epi (graphFn originBifun)
      = ((LinearMap.fst ℝ (Rn 1) (Rn 1)) ∘ₗ
          (LinearMap.fst ℝ (Rn 1 × Rn 1) ℝ)) ⁻¹' ({0} : Set (Rn 1)) := by
    ext q
    obtain ⟨⟨u, y⟩, a⟩ := q
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · simp [hu]
  rw [hepi]
  exact (convex_singleton (0 : Rn 1)).linear_preimage _

/-- The counterexample has $\operatorname{dom} F = \{0\}$. -/
@[simp] theorem convexDomBifun_originBifun : convexDomBifun originBifun = ({0} : Set (Rn 1)) := by
  ext u
  simp only [mem_convexDomBifun, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy⟩
    by_contra hu
    exact hy (originBifun_of_ne_zero hu y)
  · rintro rfl
    exact ⟨0, by simp⟩

/-- The program of the counterexample is strongly consistent, because
$\operatorname{ri} \{0\} = \{0\}$ contains the origin. -/
theorem stronglyConsistent_originBifun : StronglyConsistent originBifun := by
  change (0 : Rn 1) ∈ ri (convexDomBifun originBifun)
  rw [convexDomBifun_originBifun, intrinsicInterior_singleton]
  exact rfl

/-- The closure of the counterexample is the constant $-\infty$:
$(\operatorname{cl} F)(u, x) = -\infty$ for all $u$ and $x$. The graph function takes the value
$-\infty$, and by the closure convention of the book the closure of such a function is the
constant $-\infty$. -/
theorem convexClBifun_originBifun (u x : Rn 1) : convexClBifun originBifun u x = ⊥ := by
  have hlsc : lscHull (graphFn originBifun) ((0 : Rn 1), (0 : Rn 1)) = ⊥ := by
    refine le_bot_iff.1 (le_trans (lscHull_le (graphFn originBifun) _) (le_of_eq ?_))
    rw [graphFn_apply, originBifun_zero]
  rw [convexClBifun_apply, convexCl_of_exists_eq_bot ⟨_, hlsc⟩]

/-- The perturbation function of the closure of the counterexample is the constant $-\infty$. -/
theorem infBifun_convexClBifun_originBifun (u : Rn 1) : infBifun (convexClBifun originBifun) u
    = ⊥ := by
  rw [infBifun_apply]
  exact le_bot_iff.1 (le_trans (iInf_le _ 0) (le_of_eq (convexClBifun_originBifun u 0)))

/-- The perturbation function of the counterexample is $+\infty$ at every $u \neq 0$. -/
theorem infBifun_originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) : infBifun originBifun u = ⊤ := by
  rw [infBifun_apply]
  simp [originBifun_of_ne_zero hu]

/-- **Corollary 29.4.1** of [rockafellar1970convex], the perturbation clause as printed. This is the
proposition that for all $m$ and $n$ and every convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ for which $(P)$ is strongly consistent, the perturbation functions $\inf F$ and
$\inf (\operatorname{cl} F)$ agree on a neighbourhood of $0$. The book states: "Let $F$ be a
convex bifunction from $R^m$ to $R^n$. … Assume that $(P)$ is strongly consistent. … The
perturbation functions for $(P)$ and $(\operatorname{cl} P)$ agree on a neighborhood of $0$." No
properness is assumed.

**Correction.** The proposition is false (`Rockafellar.corollary_29_4_1_perturbation_false`).
With the added hypothesis that $F$ is proper, the clause is
`Rockafellar.corollary_29_4_1_eventually`. -/
def corollary_29_4_1_perturbation : Prop :=
  ∀ (m n : ℕ) (F : Bifun (Rn m) (Rn n)), ConvexBifun F → StronglyConsistent F →
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (convexClBifun F) u = infBifun F u

/-- **Corollary 29.4.1** of [rockafellar1970convex], the perturbation clause: the clause as printed
is false.

Take $F$ = `Rockafellar.originBifun` on $\mathbb{R}^1$: $(Fu)(x) = -\infty$ for $u = 0$ and
$+\infty$ for $u \neq 0$. It is convex, and $\operatorname{dom} F = \{0\}$ has $0$ in its
relative interior, so $(P)$ is strongly consistent. But its graph function takes the value
$-\infty$, so the closure of the graph function is the constant $-\infty$ and
$\inf (\operatorname{cl} F) \equiv -\infty$, while $\inf F = +\infty$ at every $u \neq 0$. The
two perturbation functions agree only at the point $0$.

Every other clause of the corollary is Theorem 29.4 at the origin, where
$0 \in \operatorname{ri}(\operatorname{dom} F)$ holds. This clause needs agreement outside
$\operatorname{ri}(\operatorname{dom} F)$, which only the inclusion
$\operatorname{dom}(\operatorname{cl} F) \subseteq \operatorname{cl}(\operatorname{dom} F)$
gives, and that inclusion is stated for proper $F$. For proper $F$ the clause is
`Rockafellar.corollary_29_4_1_eventually`. -/
theorem corollary_29_4_1_perturbation_false : ¬ corollary_29_4_1_perturbation := by
  intro hcor
  have hev := hcor 1 1 originBifun convexBifun_originBifun stronglyConsistent_originBifun
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : Rn 1),
      infBifun (convexClBifun originBifun) u = infBifun originBifun u :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨u, hu, hune⟩ := (h1.and (eventually_mem_nhdsWithin (a := (0 : Rn 1)))).exists
  have hune' : u ≠ 0 := hune
  rw [infBifun_convexClBifun_originBifun u, infBifun_originBifun_of_ne_zero hune'] at hu
  exact absurd hu (by simp)

end Counterexample

end Rockafellar
