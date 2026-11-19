/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Process.Linear
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 39: Convex processes

This module formalizes Section 39 (pp. 413–424) of [rockafellar1970convex]. A **convex process** $A$
from $\mathbb{R}^m$ to $\mathbb{R}^n$ assigns to each $u \in \mathbb{R}^m$ a set
$Au \subseteq \mathbb{R}^n$ such that the graph $\{(u, x) \mid x \in Au\}$ is a convex cone in
$\mathbb{R}^m \times \mathbb{R}^n$ that contains the origin. Convex processes lie between linear
transformations and convex bifunctions, and they inherit a duality theory from Sections 30–38. An
**oriented** convex process carries one of the words *supremum* or *infimum*. For a
supremum-oriented process the inner product is $\langle Au, x^* \rangle = \sup \{\langle x, x^*
\rangle \mid x \in Au\}$, and the adjoint is the infimum-oriented process
$$A^* x^* = \{u^* \mid \langle u, u^* \rangle \ge \langle x, x^* \rangle \text{ for every } u \text{
  and every } x \in Au\}.$$
For an infimum-oriented process the supremum becomes an infimum, the inequality is reversed, and the
adjoint is supremum oriented.

The section proves that a convex process that is everywhere defined with $A0 = \{0\}$ is linear,
that $A^*$ is closed with $A^{**} = \operatorname{cl} A$, the duality between
$\langle Au, x^* \rangle$ and $\langle u, A^* x^* \rangle$, the one-to-one correspondence between
closed convex processes and certain saddle-functions, and the adjoint formulas
$(A_1 + A_2)^* = A_1^* + A_2^*$, $(\lambda A)^* = \lambda A^*$, $(Af)^* = A^{*-1} f^*$ and
$(BA)^* = A^* B^*$. All nine numbered results are formalized: Theorems 39.1–39.8 and Corollary
39.7.1. Three of them are formalized under a hypothesis that is stronger than the one of the book
(see Not formalized). The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Process.Basic`, `Numlib.Analysis.Convex.Process.Duality` and
`Numlib.Analysis.Convex.Process.Linear`.

## Main definitions

* `Rockafellar.PolyhedralConvexProcess`: a convex process whose graph is a polyhedral convex cone.
* `Rockafellar.imageFn`: the image $(Af)(x) = \inf \{f(u) \mid x \in Au\}$ of a function $f$ under a
  convex process $A$.
* `Rockafellar.convexProcessEquivGraph`, `Rockafellar.convexProcessCompleteLattice`: a convex
  process is the same as its graph, and the convex processes from $\mathbb{R}^m$ to $\mathbb{R}^n$
  form a complete lattice under inclusion of graphs.
* `Rockafellar.Orientation`, `Rockafellar.Orientation.flip`: the two orientations *supremum* and
  *infimum*, and the exchange of the two.
* `Rockafellar.Orientation.bracketSet`: the inner product $\langle C, x^* \rangle$ of an oriented
  convex set $C$ with a vector $x^*$.
* `Rockafellar.OrientedProcess`: a convex process together with an orientation.
* `Rockafellar.Orientation.adjointProcess`, `Rockafellar.OrientedProcess.adjoint`: the adjoint $A^*$
  of an oriented convex process, with the opposite orientation.
* `Rockafellar.OrientedProcess.inv`, `Rockafellar.OrientedProcess.comp`: the inverse $A^{-1}$ and
  the product $BA$ of oriented convex processes. The sum $A_1 + A_2$ and the scalar multiple
  $\lambda A$ are instances.
* `Rockafellar.OrientedProcess.bracket`: the inner product $\langle Au, x^* \rangle$ of an oriented
  convex process.

## Main results

* The elementary algebra of convex processes, `Rockafellar.eval_convex`, `Rockafellar.dom_convex`,
  `Rockafellar.range_convex`, `Rockafellar.dom_inv`, `Rockafellar.range_inv`,
  `Rockafellar.add_eval_zero_subset`, `Rockafellar.comp_assoc`, `Rockafellar.id_comp`,
  `Rockafellar.comp_id`, `Rockafellar.inv_comp`, `Rockafellar.inv_comp_ne_id`,
  `Rockafellar.comp_add_le`, `Rockafellar.add_comp_le`: the values, the domain and the range are
  convex, $(BA)^{-1} = A^{-1} B^{-1}$, the product is associative with the identity as unit,
  $A^{-1} A$ need not be the identity, and the two distributive laws hold only as inclusions.
* Theorem 39.1, `Rockafellar.theorem_39_1`, `Rockafellar.theorem_39_1_isBounded`: a convex process
  $A$ with $\operatorname{dom} A = \mathbb{R}^m$ and $A0 = \{0\}$ (equivalently, $A0$ bounded) is a
  linear transformation.
* Theorem 39.2, `Rockafellar.theorem_39_2_orientation`, `Rockafellar.theorem_39_2_isClosed`,
  `Rockafellar.theorem_39_2`, `Rockafellar.theorem_39_2_eq_self_iff`,
  `Rockafellar.theorem_39_2_indicatorBifun`: $A^*$ is a closed convex process with the opposite
  orientation, $A^{**} = \operatorname{cl} A$, and the adjoint of the indicator bifunction
  $\delta(x \mid Au)$ of $A$ is $-\delta(u^* \mid A^* x^*)$.
* Theorem 39.3, `Rockafellar.theorem_39_3_posHomogeneous`, `Rockafellar.theorem_39_3_convexFn`,
  `Rockafellar.theorem_39_3_closedFn`, `Rockafellar.theorem_39_3_concaveFn`,
  `Rockafellar.theorem_39_3_closedConcaveFn`, `Rockafellar.theorem_39_3_posHomogeneous_arg`,
  `Rockafellar.theorem_39_3_concaveFn_arg`, `Rockafellar.theorem_39_3_convexFn_arg`,
  `Rockafellar.theorem_39_3_cl`, `Rockafellar.theorem_39_3_cl_inf`,
  `Rockafellar.theorem_39_3_cl_adjoint`, `Rockafellar.theorem_39_3_relint_dom`,
  `Rockafellar.theorem_39_3_relint_dom_adjoint`: $\langle Au, x^* \rangle$ is positively homogeneous
  in each variable, concave in $u$ and closed convex in $x^*$ (the reverse for the infimum
  orientation), $\langle u, A^* x^* \rangle$ is its closure in $u$, and the two agree on
  $\operatorname{ri}(\operatorname{dom} A)$.
* Theorem 39.4, `Rockafellar.theorem_39_4`, `Rockafellar.theorem_39_4_eval`:
  $K(u, x^*) = \langle Au, x^* \rangle$ is a one-to-one correspondence between the closed convex
  processes and the lower closed, positively homogeneous concave-convex functions $K$ with
  $K(0, 0) = 0$.
* Theorem 39.5, `Rockafellar.theorem_39_5`, `Rockafellar.theorem_39_5_isClosed`,
  `Rockafellar.theorem_39_5_closure`: $(A_1 + A_2)^* = A_1^* + A_2^*$ for processes with the same
  orientation, and $(A_1 + A_2)^* = \operatorname{cl}(A_1^* + A_2^*)$ with $A_1 + A_2$ closed for
  closed $A_1$, $A_2$.
* Theorem 39.6, `Rockafellar.theorem_39_6`: $(\lambda A)^* = \lambda A^*$ for $\lambda > 0$.
* Theorem 39.7, `Rockafellar.theorem_39_7`, `Rockafellar.theorem_39_7_attained`,
  `Rockafellar.theorem_39_7_closedFn`, `Rockafellar.theorem_39_7_attained_image`,
  `Rockafellar.theorem_39_7_closure`: $(Af)^* = A^{*-1} f^*$ with the infimum attained, and for
  closed $A$ and $f$ the function $Af$ is closed, attains its infimum, and
  $(Af)^* = \operatorname{cl}(A^{*-1} f^*)$.
* Corollary 39.7.1, `Rockafellar.corollary_39_7_1`, `Rockafellar.corollary_39_7_1_isBounded`: the
  image $AC$ of a nonempty closed convex set $C$ under a closed convex process $A$ is closed if no
  nonzero vector of $A^{-1}0$ is in the recession cone of $C$, in particular if $C$ is bounded.
* Theorem 39.8, `Rockafellar.theorem_39_8`, `Rockafellar.theorem_39_8_isClosed`,
  `Rockafellar.theorem_39_8_closure`: $(BA)^* = A^* B^*$ for processes with the same orientation,
  and $(BA)^* = \operatorname{cl}(A^* B^*)$ with $BA$ closed for closed $A$, $B$.

## Conventions

* A convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ is a term of
  `ConvexAnalysis.ConvexProcess`, applied to `Rockafellar.Rn m` and `Rockafellar.Rn n`. It is given
  by its graph, a `PointedCone`. The set $Au$ is `A.eval u`. The domain $\operatorname{dom} A$, the
  set of all $u$ with $Au$ nonempty, is `A.dom`. The range is `A.range`, the inverse $A^{-1}$ is
  `A.inv`, the image $AC$ of a set $C$ is `A.image C`, and the product $BA$ is `B.comp A`. The
  process $A$ is closed if its graph is closed.
* A statement about a plain `ConvexAnalysis.ConvexProcess` treats it as supremum oriented. Its
  adjoint is then `ConvexAnalysis.ConvexProcess.adjointProcess (Rockafellar.pairing m)
  (Rockafellar.pairing n) A`, and its inner product is the one of `Rockafellar.OrientedProcess.mk A
  Rockafellar.Orientation.sup`.
* In the Lean statements, the variables `y : Rn n` and `v : Rn m` stand for the vectors $x^*$ and
  $u^*$ of the book.

## Implementation notes

* The orientation is data and not a global convention. The book defines an oriented convex set as "a
  pair consisting of a convex set and one of the words *supremum* or *infimum*". Theorems 39.5 and
  39.8 require two processes with the same orientation, and Theorem 39.2 exchanges the orientation.
  So both orientations must be expressible at the same time, and a global convention of the kind
  that Section 36 uses for saddle-functions cannot state Theorem 39.5.
* The relative-interior conditions of Theorems 39.5, 39.7 and 39.8 are replaced by hypotheses
  `ConvexAnalysis.IsExactSum`, one for each value of the dual variable. An exact sum requires both
  summands to be proper. The summands here are functions such as
  $u \mapsto -\langle A_i u, x^* \rangle$, which take the value $-\infty$ wherever $A_i u$ is
  unbounded in the direction $x^*$. For all $x^*$ together this forces
  $\operatorname{dom} A_i^* = \mathbb{R}^n$. So the hypothesis is strictly stronger than the one of
  the book. It excludes the example $Au = \{x \mid x \le Bu\}$ for $u \ge 0$ of the section itself,
  and `ConvexAnalysis.IsExactSum.of_relint` does not derive it from the relative-interior condition.
* Theorem 39.1 is stated with the hypothesis $A0 = \{0\}$, which does not use a norm. The book
  assumes that $A0$ is bounded, and the first line of its proof derives $A0 = \{0\}$. The two
  hypotheses are equivalent, because $A0$ is a convex cone that contains $0$, and
  `Rockafellar.theorem_39_1_isBounded` gives the form of the book.
* Most clauses about a supremum-oriented process come from Section 33 applied to the indicator
  bifunction $(Fu)(x) = \delta(x \mid Au)$ of $A$ (`Rockafellar.OrientedProcess.bracket_sup`). The
  closedness clause of Theorem 39.5 is not proved from Corollary 38.2.1, and Theorem 39.8 is not
  proved from Theorem 38.5. Corollary 39.7.1 is proved from Theorem 9.1 and not from Theorem 39.7.

## Deviations from the source

* **Image of a function** (reading). The indicator-sum definition agrees with the
  book's fiber infimum for functions that never take $-\infty$. An infeasible input
  with value $-\infty$ can contribute to the Lean infimum. See `Rockafellar.imageFn`.
* **Oriented sums and products** (generalization). The book considers operands of
  like orientation. The Lean operations are total and use the orientation of the
  first summand or of the process applied first.
* **Theorem 39.3**, last assertion (generalization). The book assumes that $A$ is closed for both
  halves. The half $\langle Au, x^* \rangle = \langle u, A^* x^* \rangle$ for
  $u \in \operatorname{ri}(\operatorname{dom} A)$ holds without closedness. See
  `Rockafellar.theorem_39_3_relint_dom`.
* **Theorem 39.7** (generalization). The book assumes that $f$ is proper convex. The statements of
  the first assertion assume only that $f$ is proper. See `Rockafellar.theorem_39_7` and
  `Rockafellar.theorem_39_7_attained`.
* **Theorem 39.7**, attainment (correction). The book states primal attainment for
  every target. The zero linear map with $f=0$ gives an empty fiber at any nonzero
  target, even though the relative-interior condition holds. Lean restricts primal
  attainment to targets with image value below $+\infty$. Its dual attainment clause
  gives equality in the indicator-sum formula, which allows an infeasible witness
  when the value is $+\infty$. See `Rockafellar.theorem_39_7_attained_image`.
* **Theorems 39.5, 39.7, and 39.8** (reading). The formalized statements assume
  pointwise exact-sum hypotheses in place of relative-interior overlap. The closure
  and adjoint-closure clauses in 39.5 and 39.8 treat the supremum orientation.

## Not formalized

* **Theorem 39.2, last assertion, for an infimum-oriented process.**
* **Theorem 39.3, the reverse closure identity and relative-interior equalities**, for
  an infimum-oriented process.
* **Theorems 39.5 and 39.8, the closure and adjoint-closure clauses**, for
  infimum-oriented processes.
-/

namespace Rockafellar

open Pointwise Set ConvexAnalysis

variable {m n p : ℕ}

/-! ### Convex processes: the elementary properties -/

/-- For a convex process $A$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $u \in \mathbb{R}^m$, the set
$Au$ is convex. -/
theorem eval_convex (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) : Convex ℝ (A.eval u) :=
  A.convex_eval u

/-- For a convex process $A$ and every $u$, $Au + A0 \subseteq Au$. -/
theorem add_eval_zero_subset (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    A.eval u + A.eval 0 ⊆ A.eval u :=
  A.add_eval_zero_subset u

/-- The domain $\operatorname{dom} A = \{u \mid Au \neq \emptyset\}$ of a convex process $A$ is
convex. -/
theorem dom_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.dom := A.convex_dom

/-- The range $\bigcup \{Au \mid u \in \mathbb{R}^m\}$ of a convex process $A$ is convex. -/
theorem range_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.range := A.convex_range

/-- For a convex process $A$, $\operatorname{dom} A^{-1} = \operatorname{range} A$. -/
theorem dom_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.dom = A.range := A.dom_inv

/-- For a convex process $A$, $\operatorname{range} A^{-1} = \operatorname{dom} A$. -/
theorem range_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.range = A.dom := A.range_inv

/-! ### Theorem 39.1 -/

/-- **Theorem 39.1** of [rockafellar1970convex]. Let $A$ be a convex process from $\mathbb{R}^m$ to
$\mathbb{R}^n$ with $\operatorname{dom} A = \mathbb{R}^m$ and $A0 = \{0\}$. Then there is a
linear transformation $T : \mathbb{R}^m \to \mathbb{R}^n$ with $Au = \{Tu\}$ for every $u$.

The book assumes that $A0$ is bounded, and the first line of its proof derives $A0 = \{0\}$. The
two hypotheses are equivalent, because $A0$ is a convex cone that contains $0$. The form of the
book is `Rockafellar.theorem_39_1_isBounded`. The hypothesis $A0 = \{0\}$ does not use a norm. -/
theorem theorem_39_1 (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hzero : A.eval 0 = {0}) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  A.exists_linearMap_of_isBounded hdom (by rw [hzero]; exact Bornology.isBounded_singleton)

/-- **Theorem 39.1** of [rockafellar1970convex], in the form of the book. Let $A$ be a convex
process from $\mathbb{R}^m$ to $\mathbb{R}^n$ with $\operatorname{dom} A = \mathbb{R}^m$ and
$A0$ bounded. Then there is a linear transformation $T$ with $Au = \{Tu\}$ for every $u$. -/
theorem theorem_39_1_isBounded (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  theorem_39_1 A hdom (A.eval_zero_eq_zero_of_isBounded hb)

/-! ### Polyhedral convex processes -/

/-- **Section 39** of [rockafellar1970convex], polyhedral convex processes. A convex process from
$\mathbb{R}^m$ to $\mathbb{R}^n$ is **polyhedral** if its graph is a polyhedral convex cone in
$\mathbb{R}^m \times \mathbb{R}^n$.

No numbered result of Section 39 uses this definition. The graph is then a polyhedral convex set
in the sense of `ConvexAnalysis.Polyhedral` (`Rockafellar.polyhedral_graph_of_polyhedral`). -/
def PolyhedralConvexProcess (A : ConvexProcess (Rn m) (Rn n)) : Prop :=
  PolyhedralCone (A.graph : Set (Rn m × Rn n))

/-- The graph of a polyhedral convex process is a polyhedral convex set. -/
theorem polyhedral_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : Polyhedral (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.polyhedral hA

/-- A polyhedral convex process is closed, because a polyhedral convex cone is closed. -/
theorem isClosed_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : IsClosed (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.isClosed hA

/-! ### The algebra of convex processes -/

/-- For convex processes $A_1$ and $A_2$, $\operatorname{dom}(A_1 + A_2) = \operatorname{dom} A_1
\cap \operatorname{dom} A_2$. -/
theorem dom_add (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    (A₁ + A₂).dom = A₁.dom ∩ A₂.dom :=
  ConvexProcess.dom_add A₁ A₂

/-- The image $AC = \bigcup \{Au \mid u \in C\}$ of a convex set $C$ under a convex process $A$ is
convex. -/
theorem image_convex (A : ConvexProcess (Rn m) (Rn n)) {C : Set (Rn m)} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) :=
  A.convex_image hC

/-- **Section 39** of [rockafellar1970convex], the image of a function under a convex process. Let
$A$ be a convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let
$f : \mathbb{R}^m \to [-\infty, +\infty]$. The **image** of $f$ under $A$ is
$$(Af)(x) = \inf_u \{f(u) + \delta(x \mid Au)\}.$$

This is `ConvexAnalysis.imageBifun` for the indicator bifunction of $A$. If $f$ never takes the
value $-\infty$, it is the formula $(Af)(x) = \inf \{f(u) \mid x \in Au\}$ of the book
(`Rockafellar.imageFn_apply`).

**Reading.** If $f \equiv -\infty$ and $A$ is the zero linear map, the indicator sum
gives $-\infty$ at a nonzero target, where the book's fiber is empty and its infimum
is $+\infty$. -/
noncomputable def imageFn (A : ConvexProcess (Rn m) (Rn n)) (f : Rn m → EReal) : Rn n → EReal :=
  imageBifun A.indicatorBifun f

/-- Let $A$ be a convex process and let $f$ be a function that never takes the value $-\infty$. Then
$$(Af)(x) = \inf \{f(u) \mid u \in A^{-1} x\}.$$

**Reading.** The hypothesis on $f$ makes the term $f(u) + \delta(x \mid Au)$ equal to $+\infty$ for
$u \notin A^{-1} x$. It holds for the proper function $f$ of Theorem 39.7. -/
theorem imageFn_apply (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal}
    (hf : ∀ u, f u ≠ ⊥) (x : Rn n) :
    imageFn A f x = ⨅ u ∈ A.inv.eval x, f u := by
  have hunfold : imageFn A f x = ⨅ u, f u + A.indicatorBifun u x := rfl
  rw [hunfold]
  refine iInf_congr fun u => ?_
  by_cases hu : u ∈ A.inv.eval x
  · rw [ConvexProcess.indicatorBifun_apply, indicatorFn_of_mem (show x ∈ A.eval u from hu),
      add_zero, iInf_pos hu]
  · rw [ConvexProcess.indicatorBifun_apply,
      indicatorFn_of_notMem (show x ∉ A.eval u from hu), iInf_neg hu]
    exact EReal.add_top_of_ne_bot (hf u)

/-- For convex processes $A$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $B$ from $\mathbb{R}^n$ to
$\mathbb{R}^p$, $(BA)^{-1} = A^{-1} B^{-1}$. -/
theorem inv_comp (B : ConvexProcess (Rn n) (Rn p)) (A : ConvexProcess (Rn m) (Rn n)) :
    (B.comp A).inv = A.inv.comp B.inv :=
  ConvexProcess.inv_comp B A

/-- The product of convex processes is associative: $(CB)A = C(BA)$. So the convex processes from
$\mathbb{R}^n$ to itself form a semigroup under multiplication. -/
theorem comp_assoc {q : ℕ} (C : ConvexProcess (Rn p) (Rn q)) (B : ConvexProcess (Rn n) (Rn p))
    (A : ConvexProcess (Rn m) (Rn n)) : (C.comp B).comp A = C.comp (B.comp A) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  constructor
  · rintro ⟨x, hx, z, hz, hw⟩
    exact ⟨z, ⟨x, hx, hz⟩, hw⟩
  · rintro ⟨z, ⟨x, hx, hz⟩, hw⟩
    exact ⟨x, hx, z, hz, hw⟩

/-- The identity transformation $I$ is a left unit for the product of convex processes: $IA = A$. -/
theorem id_comp (A : ConvexProcess (Rn m) (Rn n)) :
    (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn n))).comp A = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hz' : x = w := hz
    rwa [hz']
  · intro hr
    exact ⟨x, hr, rfl⟩

/-- The identity transformation $I$ is a right unit for the product of convex processes: $AI = A$.
-/
theorem comp_id (A : ConvexProcess (Rn m) (Rn n)) :
    A.comp (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn m))) = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hw' : w = u := hw
    rwa [hw'] at hz
  · intro hr
    exact ⟨u, rfl, hr⟩

/-- There is a convex process $A$ from $\mathbb{R}^1$ to $\mathbb{R}^1$ such that $A^{-1} A$ is not
the identity transformation.

The example is the zero transformation $A$. Then $A^{-1} 0 = \mathbb{R}^1$ and
$(A^{-1} A) u = \mathbb{R}^1$, while $Iu = \{u\}$. So the convex processes from $\mathbb{R}^n$
to itself form a semigroup and not a group. -/
theorem inv_comp_ne_id :
    ∃ A : ConvexProcess (Rn 1) (Rn 1),
      A.inv.comp A ≠ ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn 1)) := by
  refine ⟨ConvexProcess.ofLinearMap 0, fun hc => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Rn 1)
  have hmem : ((0 : Rn 1), v) ∈
      ((ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1)).inv.comp
        (ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1))).graph := ⟨0, rfl, rfl⟩
  rw [hc] at hmem
  exact hv hmem

/-- The first distributive inequality: for convex processes $A$, $A_1$ and $A_2$, the graph of
$AA_1 + AA_2$ is contained in the graph of $A(A_1 + A_2)$. -/
theorem comp_add_le (A : ConvexProcess (Rn n) (Rn p)) (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    ((A.comp A₁) + (A.comp A₂)).graph ≤ (A.comp (A₁ + A₂)).graph := by
  rintro ⟨u, z⟩ ⟨z₁, ⟨x₁, hx₁, hz₁⟩, z₂, ⟨x₂, hx₂, hz₂⟩, hz⟩
  refine ⟨x₁ + x₂, ⟨x₁, hx₁, x₂, hx₂, rfl⟩, ?_⟩
  have hz' : z = z₁ + z₂ := hz
  rw [hz']
  exact A.add_mem_graph hz₁ hz₂

/-- The second distributive inequality: for convex processes $A$, $A_1$ and $A_2$, the graph of
$(A_1 + A_2) A$ is contained in the graph of $A_1 A + A_2 A$. -/
theorem add_comp_le (A : ConvexProcess (Rn m) (Rn n)) (A₁ A₂ : ConvexProcess (Rn n) (Rn p)) :
    ((A₁ + A₂).comp A).graph ≤ ((A₁.comp A) + (A₂.comp A)).graph := by
  rintro ⟨u, z⟩ ⟨x, hx, z₁, hz₁, z₂, hz₂, hz⟩
  exact ⟨z₁, ⟨x, hx, hz₁⟩, z₂, ⟨x, hx, hz₂⟩, hz⟩

/-! ### The complete lattice of convex processes

The lattice of pointed cones is Mathlib's `Submodule` lattice, and the structure is transported
along the graph bijection rather than rebuilt. -/

/-- **Section 39** of [rockafellar1970convex], convex processes as graphs. The map that sends a
convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ to its graph is a bijection onto the convex
cones in $\mathbb{R}^m \times \mathbb{R}^n$ that contain the origin.

The cones are Mathlib's `PointedCone ℝ (Rn m × Rn n)`. The lattice structure of
`Rockafellar.convexProcessCompleteLattice` is transported along this bijection. -/
def convexProcessEquivGraph (m n : ℕ) :
    ConvexProcess (Rn m) (Rn n) ≃ PointedCone ℝ (Rn m × Rn n) where
  toFun A := A.graph
  invFun K := ⟨K⟩
  left_inv A := by cases A; rfl
  right_inv _ := rfl

/-- **Section 39** of [rockafellar1970convex], the lattice of convex processes. The convex processes
from $\mathbb{R}^m$ to $\mathbb{R}^n$ form a **complete lattice** under inclusion of graphs,
"inasmuch as the collection of all convex cones containing the origin in $\mathbb{R}^{m+n}$ is a
complete lattice under inclusion".

The structure is the lattice of `PointedCone`, transported along
`Rockafellar.convexProcessEquivGraph`. The order is described by
`Rockafellar.convexProcess_le_iff`. -/
noncomputable instance convexProcessCompleteLattice :
    CompleteLattice (ConvexProcess (Rn m) (Rn n)) :=
  (convexProcessEquivGraph m n).completeLattice

/-- For convex processes $A$ and $B$, $A \le B$ in the lattice if and only if the graph of $A$ is
contained in the graph of $B$. The book writes this inclusion as $B \supseteq A$. -/
theorem convexProcess_le_iff {A B : ConvexProcess (Rn m) (Rn n)} :
    A ≤ B ↔ (A.graph : Set (Rn m × Rn n)) ⊆ B.graph :=
  Iff.rfl

/-! ### Orientation -/

/-- **Section 39** of [rockafellar1970convex], orientation. An orientation is one of the two words
*supremum* or *infimum*. The book defines: "an oriented convex set is a pair consisting of a
convex set and one of the words *supremum* or *infimum*". -/
inductive Orientation where
  /-- The supremum orientation, under which a convex set $C$ is identified with its indicator
  function $\delta(\cdot \mid C)$. -/
  | sup : Orientation
  /-- The infimum orientation, under which a convex set $C$ is identified with
  $-\delta(\cdot \mid C)$. -/
  | inf : Orientation
  deriving DecidableEq

/-- **Section 39** of [rockafellar1970convex], the opposite orientation. The opposite of *supremum*
is *infimum*, and the opposite of *infimum* is *supremum*.

The inverse of an oriented convex process and its adjoint (Theorem 39.2) have the opposite
orientation. -/
def Orientation.flip : Orientation → Orientation
  | Orientation.sup => Orientation.inf
  | Orientation.inf => Orientation.sup

/-- The opposite of the supremum orientation is the infimum orientation. -/
@[simp] theorem Orientation.flip_sup : Orientation.sup.flip = Orientation.inf := rfl

/-- The opposite of the infimum orientation is the supremum orientation. -/
@[simp] theorem Orientation.flip_inf : Orientation.inf.flip = Orientation.sup := rfl

/-- The opposite of the opposite of an orientation is the orientation itself. -/
@[simp] theorem Orientation.flip_flip (o : Orientation) : o.flip.flip = o := by cases o <;> rfl

/-- **Section 39** of [rockafellar1970convex], the inner product of an oriented convex set. Let
$C \subseteq \mathbb{R}^n$ and $x^* \in \mathbb{R}^n$. The inner product
$\langle C, x^* \rangle$ is
$$\sup \{\langle x, x^* \rangle \mid x \in C\}$$
when $C$ is supremum oriented, and the infimum of the same set of numbers when $C$ is infimum
oriented.

The value is in `EReal`. The supremum over the empty set is $-\infty$, and the infimum over the
empty set is $+\infty$. -/
noncomputable def Orientation.bracketSet (o : Orientation) (C : Set (Rn n)) (y : Rn n) : EReal :=
  match o with
  | Orientation.sup => ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal)
  | Orientation.inf => ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal)

/-- For the supremum orientation, $\langle C, x^* \rangle = \sup \{\langle x, x^* \rangle \mid x \in
C\}$. -/
@[simp] theorem Orientation.bracketSet_sup (C : Set (Rn n)) (y : Rn n) :
    Orientation.sup.bracketSet C y = ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

/-- For the infimum orientation, $\langle C, x^* \rangle = \inf \{\langle x, x^* \rangle \mid x \in
C\}$. -/
@[simp] theorem Orientation.bracketSet_inf (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

/-- For a supremum-oriented set $C$, the function $\langle C, \cdot \rangle$ is the support function
$\delta^*(\cdot \mid C)$, the convex conjugate of $\delta(\cdot \mid C)$. -/
theorem bracketSet_sup_eq_supportFn (C : Set (Rn n)) :
    Orientation.sup.bracketSet C = supportFn (pairing n) C :=
  funext fun y => (supportFn_apply (pairing n) C y).symm

/-- For an infimum-oriented set $C$, $\langle C, x^* \rangle = -\delta^*(-x^* \mid C)$. That is,
$\langle C, \cdot \rangle$ is the concave conjugate of $-\delta(\cdot \mid C)$. -/
theorem bracketSet_inf_eq_neg_supportFn (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = -(supportFn (pairing n) C (-y)) := by
  rw [Orientation.bracketSet_inf, supportFn_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [← EReal.coe_neg, map_neg (pairing n x) y, _root_.neg_neg]

/-- **Section 39** of [rockafellar1970convex], oriented convex processes. An **oriented convex
process** from $\mathbb{R}^m$ to $\mathbb{R}^n$ consists of a convex process $A$ and an
orientation, and every set $Au$ carries this orientation.

It must be a pair. Theorems 39.5 and 39.8 require two processes with the same orientation and
Theorem 39.2 exchanges the orientation, so no global convention can state them. -/
@[ext] structure OrientedProcess (m n : ℕ) where
  /-- The underlying convex process. -/
  process : ConvexProcess (Rn m) (Rn n)
  /-- The orientation, *supremum* or *infimum*. -/
  orientation : Orientation

/-- **Section 39** of [rockafellar1970convex], the adjoint of a convex process in a given
orientation. Let $A$ be a convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$. For the supremum
orientation, the adjoint is the convex process from $\mathbb{R}^n$ to $\mathbb{R}^m$
$$A^* x^* = \{u^* \mid \langle u, u^* \rangle \ge \langle x, x^* \rangle \text{ for all } u
  \text{ and all } x \in Au\}.$$
For the infimum orientation, it is the same set with the inequality reversed.

The two cases are `ConvexAnalysis.ConvexProcess.adjointProcess` and
`ConvexAnalysis.ConvexProcess.coadjointProcess` for the pairings `Rockafellar.pairing m` and
`Rockafellar.pairing n`. -/
noncomputable def Orientation.adjointProcess (o : Orientation)
    (A : ConvexProcess (Rn m) (Rn n)) : ConvexProcess (Rn n) (Rn m) :=
  match o with
  | Orientation.sup => ConvexProcess.adjointProcess (pairing m) (pairing n) A
  | Orientation.inf => ConvexProcess.coadjointProcess (pairing m) (pairing n) A

/-- The adjoint in the supremum orientation is `ConvexAnalysis.ConvexProcess.adjointProcess`. -/
@[simp] theorem Orientation.adjointProcess_sup (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.sup.adjointProcess A
      = ConvexProcess.adjointProcess (pairing m) (pairing n) A := rfl

/-- The adjoint in the infimum orientation is `ConvexAnalysis.ConvexProcess.coadjointProcess`. -/
@[simp] theorem Orientation.adjointProcess_inf (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.inf.adjointProcess A
      = ConvexProcess.coadjointProcess (pairing m) (pairing n) A := rfl

namespace OrientedProcess

/-- **Section 39** of [rockafellar1970convex], the inverse of an oriented convex process. The
inverse of an oriented convex process $A$ is the convex process $A^{-1}$, whose graph is
$\{(x, u) \mid x \in Au\}$, with the opposite orientation. -/
def inv (A : OrientedProcess m n) : OrientedProcess n m := ⟨A.process.inv, A.orientation.flip⟩

/-- The underlying process of the inverse of $A$ is the inverse of the underlying process of $A$. -/
@[simp] theorem inv_process (A : OrientedProcess m n) : A.inv.process = A.process.inv := rfl

/-- The inverse of $A$ has the opposite orientation to $A$. -/
@[simp] theorem inv_orientation (A : OrientedProcess m n) :
    A.inv.orientation = A.orientation.flip := rfl

/-- **Section 39** of [rockafellar1970convex], the adjoint of an oriented convex process. The
adjoint $A^*$ of an oriented convex process $A$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ is the
oriented convex process from $\mathbb{R}^n$ to $\mathbb{R}^m$ whose process is
`Rockafellar.Orientation.adjointProcess` for the orientation of $A$, and whose orientation is
the opposite one. -/
noncomputable def adjoint (A : OrientedProcess m n) : OrientedProcess n m :=
  ⟨A.orientation.adjointProcess A.process, A.orientation.flip⟩

/-- The underlying process of $A^*$ is the adjoint of the underlying process of $A$ in the
orientation of $A$. -/
@[simp] theorem adjoint_process (A : OrientedProcess m n) :
    A.adjoint.process = A.orientation.adjointProcess A.process := rfl

/-- The adjoint $A^*$ has the opposite orientation to $A$. -/
@[simp] theorem adjoint_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := rfl

/-- The sum $A_1 + A_2$ of two oriented convex processes, $(A_1 + A_2) u = A_1 u + A_2 u$, with the
orientation of $A_1$.

The book considers only sums of processes with the same orientation. So every theorem about a
sum below has the hypothesis that the two orientations are equal.

**Reading.** The total instance also sums mixed orientations and takes the first tag.
-/
instance : Add (OrientedProcess m n) where
  add A₁ A₂ := ⟨A₁.process + A₂.process, A₁.orientation⟩

/-- The underlying process of $A_1 + A_2$ is the sum of the underlying processes. -/
@[simp] theorem add_process (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).process = A₁.process + A₂.process := rfl

/-- The orientation of $A_1 + A_2$ is the orientation of $A_1$.

**Reading.** When orientations differ the Lean sum uses the first tag.
-/
@[simp] theorem add_orientation (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).orientation = A₁.orientation := rfl

/-- The scalar multiple $\lambda A$ of an oriented convex process, $(\lambda A) u = \lambda (Au)$,
with the orientation of $A$. -/
instance : SMul ℝ (OrientedProcess m n) where
  smul a A := ⟨a • A.process, A.orientation⟩

/-- The underlying process of $\lambda A$ is $\lambda$ times the underlying process of $A$. -/
@[simp] theorem smul_process (a : ℝ) (A : OrientedProcess m n) :
    (a • A).process = a • A.process := rfl

/-- The orientation of $\lambda A$ is the orientation of $A$. -/
@[simp] theorem smul_orientation (a : ℝ) (A : OrientedProcess m n) :
    (a • A).orientation = A.orientation := rfl

/-- **Section 39** of [rockafellar1970convex], the product of oriented convex processes. For $A$
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $B$ from $\mathbb{R}^n$ to $\mathbb{R}^p$, the product
$BA$ is the convex process $(BA) u = \bigcup \{Bx \mid x \in Au\}$, with the orientation of $A$.

The book considers only products of processes with the same orientation. Theorem 39.8 has the
hypothesis that the orientations of $A$ and $B$ are equal.

**Reading.** The total operation also composes mixed orientations and keeps the tag of the process
applied first.
-/
def comp (B : OrientedProcess n p) (A : OrientedProcess m n) : OrientedProcess m p :=
  ⟨B.process.comp A.process, A.orientation⟩

/-- The underlying process of $BA$ is the product of the underlying processes. -/
@[simp] theorem comp_process (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).process = B.process.comp A.process := rfl

/-- The orientation of $BA$ is the orientation of $A$.

**Reading.** For mixed orientations the tag is that of the process applied first.
-/
@[simp] theorem comp_orientation (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).orientation = A.orientation := rfl

/-- **Section 39** of [rockafellar1970convex], the inner product $\langle Au, x^* \rangle$ of an
oriented convex process. For $u \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$, it is the inner
product $\langle Au, x^* \rangle$ of the set $Au$, with the orientation of $A$, and the vector
$x^*$ (`Rockafellar.Orientation.bracketSet`).

So $\langle Au, x^* \rangle$ is $\sup \{\langle x, x^* \rangle \mid x \in Au\}$ in the supremum
orientation, and the infimum in the infimum orientation. -/
noncomputable def bracket (A : OrientedProcess m n) (u : Rn m) (y : Rn n) : EReal :=
  A.orientation.bracketSet (A.process.eval u) y

/-- For a supremum-oriented convex process $A$, the inner product $\langle Au, x^* \rangle$ is the
bracket $(Fu)^*(x^*)$ of Section 33 for the indicator bifunction $(Fu)(x) = \delta(x \mid Au)$
of $A$.

The clauses of Theorem 39.3 about a supremum-oriented process come from this identity. -/
theorem bracket_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  (ConvexProcess.bracket_indicatorBifun_apply (pairing n) A u y).symm

/-- For an infimum-oriented convex process $A$, the inner product $\langle Au, x^* \rangle$ is
`ConvexAnalysis.ConvexProcess.coBracket`, the infimum of $\langle x, x^* \rangle$ over
$x \in Au$. -/
theorem bracket_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).bracket u y
      = ConvexProcess.coBracket (pairing n) A u y := rfl

/-- `Rockafellar.OrientedProcess.bracket_sup` as an equation between functions of $x^*$, for fixed
$u$. -/
theorem bracket_sup_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.sup).bracket u
      = ConvexAnalysis.bracket (pairing n) A.indicatorBifun u :=
  funext fun y => bracket_sup A u y

/-- `Rockafellar.OrientedProcess.bracket_inf` as an equation between functions of $x^*$, for fixed
$u$. -/
theorem bracket_inf_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.inf).bracket u
      = ConvexProcess.coBracket (pairing n) A u := rfl

/-- `Rockafellar.OrientedProcess.bracket_sup` as an equation between functions of $u$, for fixed
$x^*$. -/
theorem bracket_sup_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).bracket u y)
      = fun u => ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  funext fun u => bracket_sup A u y

/-- `Rockafellar.OrientedProcess.bracket_sup` as an equation between functions of $(u, x^*)$ on
$\mathbb{R}^m \times \mathbb{R}^n$. Theorems 39.3 and 39.4 state their closure identities in
this form. -/
theorem bracket_sup_prod (A : ConvexProcess (Rn m) (Rn n)) :
    (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
      = fun q : Rn m × Rn n =>
          ConvexAnalysis.bracket (pairing n) A.indicatorBifun q.1 q.2 :=
  funext fun q => bracket_sup A q.1 q.2

end OrientedProcess

/-- Let $T$ be a linear transformation from $\mathbb{R}^m$ to $\mathbb{R}^n$, read as a convex
process. In either orientation, the adjoint of $T$ as a convex process is the adjoint linear
transformation $T^*$. -/
theorem adjoint_ofLinearMap (T : Rn m →ₗ[ℝ] Rn n) (o : Orientation) :
    (OrientedProcess.mk (ConvexProcess.ofLinearMap T) o).adjoint.process
      = ConvexProcess.ofLinearMap (LinearMap.adjoint T) := by
  cases o
  · exact ConvexProcess.adjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)
  · exact ConvexProcess.coadjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)

/-! ### Theorem 39.2 -/

/-- **Theorem 39.2** of [rockafellar1970convex], orientation of the adjoint. For an oriented convex
process $A$, the adjoint $A^*$ has the opposite orientation to $A$.

This holds by definition. It is the clause that forces the orientation to be data. -/
theorem theorem_39_2_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := A.adjoint_orientation

/-- **Theorem 39.2** of [rockafellar1970convex], closedness of the adjoint. For an oriented convex
process $A$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, in either orientation, $A^*$ is a closed
convex process from $\mathbb{R}^n$ to $\mathbb{R}^m$.

The graph of $A^*$ is an intersection of closed half-spaces through the origin. -/
theorem theorem_39_2_isClosed (A : OrientedProcess m n) :
    IsClosed (A.adjoint.process.graph : Set (Rn n × Rn m)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact ConvexProcess.isClosed_graph_adjointProcess (pairing m) (pairing n) A
  · exact ConvexProcess.isClosed_graph_coadjointProcess (pairing m) (pairing n) A

/-- The graph of the second adjoint of a supremum-oriented process $A$ is the closure of the graph
of $A$. -/
private theorem graph_biadjoint_sup (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.coadjointProcess (pairing n) (pairing m)
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- The graph of the second adjoint of an infimum-oriented process $A$ is the closure of the graph
of $A$. -/
private theorem graph_biadjoint_inf (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.adjointProcess (pairing n) (pairing m)
        (ConvexProcess.coadjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_adjointProcess_coadjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- **Theorem 39.2** of [rockafellar1970convex], second adjoint. For an oriented convex process $A$
from $\mathbb{R}^m$ to $\mathbb{R}^n$, the graph of $A^{**}$ is the closure of the graph of $A$,
that is, $A^{**} = \operatorname{cl} A$.

For the graphs, this is the bipolar theorem $K^{\circ\circ} = \operatorname{cl} K$ of
Section 14. The two changes of sign cancel, because the second adjoint is taken in the opposite
orientation. -/
theorem theorem_39_2 (A : OrientedProcess m n) :
    (A.adjoint.adjoint.process.graph : Set (Rn m × Rn n))
      = closure (A.process.graph : Set (Rn m × Rn n)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact graph_biadjoint_sup A
  · exact graph_biadjoint_inf A

/-- **Theorem 39.2** of [rockafellar1970convex], closed processes. An oriented convex process $A$
satisfies $A^{**} = A$ if and only if $A$ is closed.

The equation $A^{**} = A$ is an equation of oriented processes. The orientation of $A^{**}$ is
always the orientation of $A$. -/
theorem theorem_39_2_eq_self_iff (A : OrientedProcess m n) :
    A.adjoint.adjoint = A ↔ IsClosed (A.process.graph : Set (Rn m × Rn n)) := by
  rw [← closure_eq_iff_isClosed, ← theorem_39_2 A]
  constructor
  · intro h
    rw [h]
  · intro h
    refine OrientedProcess.ext ?_ (by simp)
    exact ConvexProcess.ext (SetLike.ext' h)

/-- **Theorem 39.2** of [rockafellar1970convex], last assertion. Let $A$ be a supremum-oriented
convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ with the indicator bifunction
$(Fu)(x) = \delta(x \mid Au)$. Then the adjoint bifunction $F^*$ of Section 30 is
$$(F^* x^*)(u^*) = -\delta(u^* \mid A^* x^*).$$

The indicator has a minus sign because $A^*$ has the infimum orientation, and an
infimum-oriented set $C$ is identified with $-\delta(\cdot \mid C)$. The adjoint bifunction is
`ConvexAnalysis.convexAdjointBifun`. The same assertion for an infimum-oriented process is not
formalized.

**Reading.** The indicator-bifunction identity treats supremum orientation only.
-/
theorem theorem_39_2_indicatorBifun (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    convexAdjointBifun (pairing m) (pairing n) A.indicatorBifun y v
      = -((OrientedProcess.mk A Orientation.sup).adjoint.process.indicatorBifun y v) :=
  ConvexProcess.convexAdjointBifun_indicatorBifun (pairing m) (pairing n) A y v

/-! ### Theorem 39.3 -/

/-- For a supremum-oriented $A$, $\langle u, A^* x^* \rangle = \inf \{\langle u, u^* \rangle \mid
u^* \in A^* x^*\}$ is the concave bracket of the adjoint bifunction $F^*$ of the indicator
bifunction of $A$. -/
private theorem bracket_adjoint_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u
      = concaveBracket (pairing m)
          (convexAdjointBifun (pairing m) (pairing n) A.indicatorBifun) u y := by
  rw [ConvexProcess.concaveBracket_convexAdjointBifun_indicatorBifun]
  change (⨅ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iInf_congr fun v => iInf_congr fun _ => by rw [pairing_comm]

/-- For an infimum-oriented $A$, $\langle u, A^* x^* \rangle = \sup \{\langle u, u^* \rangle \mid
u^* \in A^* x^*\}$. -/
private theorem bracket_adjoint_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u
      = ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) := by
  change (⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iSup_congr fun v => iSup_congr fun _ => by rw [pairing_comm]

/-- **Theorem 39.3** of [rockafellar1970convex], homogeneity in $x^*$. For an oriented convex
process $A$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $u \in \mathbb{R}^m$, in either
orientation, the function $x^* \mapsto \langle Au, x^* \rangle$ is positively homogeneous:
$\langle Au, \lambda x^* \rangle = \lambda \langle Au, x^* \rangle$ for $\lambda > 0$. -/
theorem theorem_39_3_posHomogeneous (A : OrientedProcess m n) (u : Rn m) :
    PosHomogeneous (A.bracket u) := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_fn]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun (pairing n) A u
  · rw [OrientedProcess.bracket_inf_fn]
    exact ConvexProcess.posHomogeneous_coBracket (pairing n) A u

/-- **Theorem 39.3** of [rockafellar1970convex], convexity in $x^*$. For a supremum-oriented convex
process $A$ and $u \in \mathbb{R}^m$, the function $x^* \mapsto \langle Au, x^* \rangle$ is
convex.

It is the support function of $Au$. -/
theorem theorem_39_3_convexFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConvexFn ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.convexFn_bracket_indicatorBifun (pairing n) A u

/-- **Theorem 39.3** of [rockafellar1970convex], closedness in $x^*$. For a supremum-oriented convex
process $A$ and $u \in \mathbb{R}^m$, the function $x^* \mapsto \langle Au, x^* \rangle$ is
closed: it equals its closure `ConvexAnalysis.convexCl`. -/
theorem theorem_39_3_closedFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedConvex ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.closedConvex_bracket_indicatorBifun (Bx := pairing n) A u

/-- **Theorem 39.3** of [rockafellar1970convex], concavity in $x^*$ for the infimum orientation. The
book states that the theorem holds "likewise when $A$ is infimum oriented, except that then
convexity and concavity are reversed". For an infimum-oriented convex process $A$ and
$u \in \mathbb{R}^m$, the function $x^* \mapsto \langle Au, x^* \rangle$ is concave. -/
theorem theorem_39_3_concaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConcaveFn ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.concaveFn_coBracket (pairing n) A u

/-- **Theorem 39.3** of [rockafellar1970convex], closedness in $x^*$ for the infimum orientation.
For an infimum-oriented convex process $A$ and $u \in \mathbb{R}^m$, the function
$x^* \mapsto \langle Au, x^* \rangle$ is closed in the concave sense: it equals its concave
closure `ConvexAnalysis.concaveCl`. -/
theorem theorem_39_3_closedConcaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedConcave ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.closedConcave_coBracket (Bx := pairing n) A u

/-- **Theorem 39.3** of [rockafellar1970convex], homogeneity in $u$. For an oriented convex process
$A$ and $x^* \in \mathbb{R}^n$, in either orientation, the function
$u \mapsto \langle Au, x^* \rangle$ is positively homogeneous.

This clause uses the definition of a convex process and not Section 33: it is the axiom
$A(\lambda u) = \lambda (Au)$ for $\lambda > 0$. -/
theorem theorem_39_3_posHomogeneous_arg (A : OrientedProcess m n) (y : Rn n) :
    PosHomogeneous fun u => A.bracket u y := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_arg]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun_arg (pairing n) A y
  · exact ConvexProcess.posHomogeneous_coBracket_arg (pairing n) A y

/-- **Theorem 39.3** of [rockafellar1970convex], concavity in $u$. For a supremum-oriented convex
process $A$ and $x^* \in \mathbb{R}^n$, the function $u \mapsto \langle Au, x^* \rangle$ is
concave. -/
theorem theorem_39_3_concaveFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConcaveFn fun u => (OrientedProcess.mk A Orientation.sup).bracket u y := by
  rw [OrientedProcess.bracket_sup_arg]
  exact ConvexProcess.concaveFn_bracket_indicatorBifun (pairing n) A y

/-- **Theorem 39.3** of [rockafellar1970convex], convexity in $u$ for the infimum orientation. For
an infimum-oriented convex process $A$ and $x^* \in \mathbb{R}^n$, the function
$u \mapsto \langle Au, x^* \rangle$ is convex. A change of orientation exchanges convexity and
concavity in both variables. -/
theorem theorem_39_3_convexFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConvexFn fun u => (OrientedProcess.mk A Orientation.inf).bracket u y :=
  ConvexProcess.convexFn_coBracket_arg (pairing n) A y

/-- **Theorem 39.3** of [rockafellar1970convex], the closure in $u$. Let $A$ be a supremum-oriented
convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$. Then for
every $u$,
$$\langle u, A^* x^* \rangle = \operatorname{cl}_u \langle Au, x^* \rangle,$$
where $\operatorname{cl}_u$ is the concave closure in the variable $u$.

The closure is the concave one because $u \mapsto \langle Au, x^* \rangle$ is concave.
Closedness of $A$ is not needed. The closure in $u$ is `ConvexAnalysis.partialCl₁` of the
function $(u, x^*) \mapsto \langle Au, x^* \rangle$. -/
theorem theorem_39_3_cl (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => partialCl₁
          (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
          (u, y) := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => concaveBracket (pairing m)
          (convexAdjointBifun (pairing m) (pairing n) A.indicatorBifun) u y :=
    funext fun u => bracket_adjoint_sup A u y
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁
    (Bu := pairing m) (Bx := pairing n) A y

/-- **Theorem 39.3** of [rockafellar1970convex], the closure in $u$ for the infimum orientation. Let
$A$ be an infimum-oriented convex process and let $x^* \in \mathbb{R}^n$. Then the function
$u \mapsto \langle u, A^* x^* \rangle$ is the convex closure `ConvexAnalysis.convexCl` of
$u \mapsto \langle Au, x^* \rangle$.

The closure is the convex one because $u \mapsto \langle Au, x^* \rangle$ is convex for the
infimum orientation. -/
theorem theorem_39_3_cl_inf (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => convexCl (fun u' => (OrientedProcess.mk A Orientation.inf).bracket u' y) u := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) :=
    funext fun u => bracket_adjoint_inf A u y
  rw [hL]
  exact ConvexProcess.iSup_coadjointProcess_eq_convexCl (Bu := pairing m) (Bx := pairing n) A y

/-- **Theorem 39.3** of [rockafellar1970convex], the closure in $x^*$. Let $A$ be a closed
supremum-oriented convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then for all $u$ and
$x^*$,
$$\langle Au, x^* \rangle = \operatorname{cl}_{x^*} \langle u, A^* x^* \rangle,$$
where $\operatorname{cl}_{x^*}$ is the convex closure in the variable $x^*$.

Closedness of $A$ is needed here: this is the second equation of Theorem 33.2. The closure in
$x^*$ is `ConvexAnalysis.partialCl₂` of the function
$(u, x^*) \mapsto \langle u, A^* x^* \rangle$.

**Reading.** Dual-variable reverse closure is stated for the supremum orientation only.
-/
theorem theorem_39_3_cl_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) :
    partialCl₂ (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2 := by
  have hL : (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => concaveBracket (pairing m)
          (convexAdjointBifun (pairing m) (pairing n) A.indicatorBifun) q.1 q.2 :=
    funext fun q => bracket_adjoint_sup A q.1 q.2
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.partialCl₂_concaveBracket_convexAdjointBifun_indicatorBifun
    (Bu := pairing m) (Bx := pairing n) A hA

/-- **Theorem 39.3** of [rockafellar1970convex], last assertion. Let $A$ be a supremum-oriented
convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let
$u \in \operatorname{ri}(\operatorname{dom} A)$. Then for every $x^* \in \mathbb{R}^n$,
$$\langle Au, x^* \rangle = \langle u, A^* x^* \rangle.$$

**Generalization.** The book assumes that $A$ is closed for this assertion and for its dual half
`Rockafellar.theorem_39_3_relint_dom_adjoint`. This half holds without closedness. It is
Corollary 33.2.1, whose only input is that a concave function agrees with its closure on the
relative interior of its domain. -/
theorem theorem_39_3_relint_dom (A : ConvexProcess (Rn m) (Rn n)) {u : Rn m}
    (hu : u ∈ ri A.dom) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom
    (Bu := pairing m) (Bx := pairing n) A hu y

/-- **Theorem 39.3** of [rockafellar1970convex], last assertion, dual half. Let $A$ be a closed
supremum-oriented convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $x^* \in
\operatorname{ri}(\operatorname{dom} A^*)$. Then $\langle Au, x^* \rangle = \langle u, A^* x^*
\rangle$ for every $u \in \mathbb{R}^m$.

**Reading.** The dual-relative-interior identity is stated for the supremum orientation only.
-/
theorem theorem_39_3_relint_dom_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (OrientedProcess.mk A Orientation.sup).adjoint.process.dom) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint
    (Bu := pairing m) (Bx := pairing n) A hA u hy

/-! ### Theorem 39.4 -/

/-- **Theorem 39.4** of [rockafellar1970convex]. Let $K$ be a function on
$\mathbb{R}^m \times \mathbb{R}^n$ with values in $[-\infty, +\infty]$ that is concave-convex
and lower closed, with $K(0, 0) = 0$, and that is positively homogeneous in $u$ for each $x^*$
and in $x^*$ for each $u$. Then there is exactly one closed convex process $A$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ such that, with the supremum orientation,
$$K(u, x^*) = \langle Au, x^* \rangle \qquad \text{for all } u, x^*.$$

The book states a one-to-one correspondence between these functions $K$ and the closed convex
processes, given by this relation and by $Au = \{x \mid \langle x, x^* \rangle \le K(u, x^*)
\text{ for all } x^*\}$. The second relation is `Rockafellar.theorem_39_4_eval`. Closedness is
inside the unique existence, because the process is unique among closed processes.
Concave-convex is `ConvexAnalysis.ConcaveConvexFn`, and lower closed is
`ConvexAnalysis.LowerClosedFn`. -/
theorem theorem_39_4 {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K)
    (hK₀ : K (0, 0) = 0)
    (hhu : ∀ y : Rn n, PosHomogeneous fun u : Rn m => K (u, y))
    (hhy : ∀ u : Rn m, PosHomogeneous fun y : Rn n => K (u, y)) :
    ∃! A : ConvexProcess (Rn m) (Rn n), IsClosed (A.graph : Set (Rn m × Rn n)) ∧
      (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2) = K := by
  simp only [OrientedProcess.bracket_sup_prod]
  exact exists_unique_convexProcess_bracket_indicatorBifun_eq (pairing m) (pairing n)
    hK hlc hK₀ hhu hhy

/-- **Theorem 39.4** of [rockafellar1970convex], second relation. A closed convex process $A$ is
recovered from its inner product: for every $u$,
$$Au = \{x \mid \langle x, x^* \rangle \le \langle Au, x^* \rangle \text{ for every } x^*\},$$
with the supremum orientation. -/
theorem theorem_39_4_eval (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) :
    A.eval u = {x : Rn n | ∀ y : Rn n,
      ((pairing n x y : ℝ) : EReal) ≤ (OrientedProcess.mk A Orientation.sup).bracket u y} := by
  have h := ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun (Bx := pairing n) A hA u
  rw [flip_pairing] at h
  rw [h]
  ext x
  simp only [mem_supportSet, mem_ofPred_eq, OrientedProcess.bracket_sup]
  exact forall_congr' fun y => by rw [pairing_comm]

/-! ### Theorem 39.5 -/

/-- **Theorem 39.5** of [rockafellar1970convex], first statement. Let $A_1$ and $A_2$ be oriented
convex processes from $\mathbb{R}^m$ to $\mathbb{R}^n$ with the same orientation. Suppose that
for every $x^* \in \mathbb{R}^n$ the two functions $u \mapsto -\delta^*(x^* \mid A_1 u)$ and
$u \mapsto -\delta^*(x^* \mid A_2 u)$ have an exact sum. Then
$$(A_1 + A_2)^* = A_1^* + A_2^*.$$

The book assumes $\operatorname{ri}(\operatorname{dom} A_1) \cap
\operatorname{ri}(\operatorname{dom} A_2) \neq \emptyset$. The exact-sum hypothesis
(`ConvexAnalysis.IsExactSum`) is strictly stronger, and this form of the theorem is not
formalized; see the module doc comment. The equal orientations are essential, and they are the
reason that the orientation is data. The equation is an equation of oriented processes.

**Reading.** Slice-wise exactness replaces relative-interior overlap in the adjoint-of-sum formula.
-/
theorem theorem_39_5 (A₁ A₂ : OrientedProcess m n) (hor : A₁.orientation = A₂.orientation)
    (hex : ∀ y : Rn n, IsExactSum (pairing m)
      (fun u => -(supportFn (pairing n) (A₁.process.eval u) y))
      (fun u => -(supportFn (pairing n) (A₂.process.eval u) y))) :
    (A₁ + A₂).adjoint = A₁.adjoint + A₂.adjoint := by
  obtain ⟨A₁, o₁⟩ := A₁
  obtain ⟨A₂, o₂⟩ := A₂
  have hor' : o₁ = o₂ := hor
  subst hor'
  cases o₁
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl

/-- **Theorem 39.5** of [rockafellar1970convex], second statement, closedness. Let $A_1$ and $A_2$
be closed convex processes from $\mathbb{R}^m$ to $\mathbb{R}^n$, supremum oriented. Suppose
that for every $u \in \mathbb{R}^m$ the two functions $x^* \mapsto -\delta^*(u \mid A_1^* x^*)$
and $x^* \mapsto -\delta^*(u \mid A_2^* x^*)$ have an exact sum. Then $A_1 + A_2$ is closed.

The book assumes that $\operatorname{ri}(\operatorname{dom} A_1^*)$ and
$\operatorname{ri}(\operatorname{dom} A_2^*)$ meet. The exact-sum hypothesis is strictly
stronger. The proof does not use Corollary 38.2.1: $A_1 + A_2$ is the infimum-oriented adjoint
of $A_1^* + A_2^*$.

**Reading.** Sum closure uses exactness and treats the supremum orientation.
-/
theorem theorem_39_5_isClosed {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    IsClosed (((A₁ + A₂).graph : Set (Rn m × Rn n))) := by
  refine ConvexProcess.isClosed_graph_add (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-- **Theorem 39.5** of [rockafellar1970convex], second statement, the adjoint of the sum. Under the
hypotheses of `Rockafellar.theorem_39_5_isClosed`, the graph of $(A_1 + A_2)^*$ is the closure
of the graph of $A_1^* + A_2^*$:
$$(A_1 + A_2)^* = \operatorname{cl}(A_1^* + A_2^*).$$

**Reading.** Adjoint closure uses exactness and treats the supremum orientation.
-/
theorem theorem_39_5_closure {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing n) (A₁ + A₂)).graph : Set (Rn n × Rn m))
      = closure (((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁
          + ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).graph
            : Set (Rn n × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_add_eq_closure (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-! ### Theorem 39.6 -/

/-- **Theorem 39.6** of [rockafellar1970convex]. For an oriented convex process $A$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and a real number $\lambda > 0$,
$$(\lambda A)^* = \lambda A^*.$$
-/
theorem theorem_39_6 (A : OrientedProcess m n) {a : ℝ} (ha : 0 < a) :
    (a • A).adjoint = a • A.adjoint := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact OrientedProcess.ext (ConvexProcess.adjointProcess_smul (pairing m) (pairing n) ha A) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_smul (pairing m) (pairing n) ha A) rfl

/-! ### Theorem 39.7 -/

/-- **Theorem 39.7** of [rockafellar1970convex], first assertion. Let $A$ be a supremum-oriented
convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a proper function on
$\mathbb{R}^m$, and let $x^* \in \mathbb{R}^n$. Suppose that $f$ and
$u \mapsto -\langle Au, x^* \rangle$ have an exact sum. Then
$$(Af)^*(x^*) = (A^{*-1} f^*)(x^*),$$
where $(A^{*-1} f^*)(x^*) = \inf \{f^*(u^*) \mid u^* \in A^* x^*\}$ is the image of $f^*$ under
the inverse of $A^*$.

**Generalization.** The book assumes that $f$ is proper convex. The statement assumes only that
$f$ is proper: finite somewhere and never $-\infty$.

The book assumes $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} A) \neq \emptyset$. The exact-sum hypothesis
(`ConvexAnalysis.IsExactSum`) is strictly stronger, and this form of the theorem is not
formalized; see the module doc comment. The images are `Rockafellar.imageFn`. -/
theorem theorem_39_7 (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal} (hf : ProperConvex f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    convexConj (pairing n) (imageFn A f) y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (convexConj (pairing m) f) y := by
  refine ConvexProcess.convexConj_imageBifun_indicatorBifun (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Theorem 39.7** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.theorem_39_7`, the infimum that defines $(A^{*-1} f^*)(x^*)$ is attained: there is
$u^* \in \mathbb{R}^m$ with
$$f^*(u^*) + \delta(x^* \mid A^{*-1} u^*) = (A^{*-1} f^*)(x^*).$$

**Generalization.** As in `Rockafellar.theorem_39_7`, $f$ need only be proper, not convex. -/
theorem theorem_39_7_attained (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal}
    (hf : ProperConvex f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    ∃ v : Rn m, convexConj (pairing m) f v
        + (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv.indicatorBifun v y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (convexConj (pairing m) f) y := by
  refine ConvexProcess.exists_imageBifun_indicatorBifun_adjointProcess_eq
    (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Theorem 39.7** of [rockafellar1970convex], closedness of $Af$. Let $A$ be a closed convex
process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $f$ be a closed proper convex function on
$\mathbb{R}^m$. Suppose that for every $x \in \mathbb{R}^n$ the functions $f^*$ and
$u^* \mapsto -\langle A^{*-1} u^*, x \rangle$ have an exact sum, where $A^{*-1}$ is supremum
oriented. Then $Af$ is closed.

The book assumes that $\operatorname{ri}(\operatorname{dom} f^*)$ meets
$\operatorname{ri}(\operatorname{dom} A^{*-1})$. The exact-sum hypothesis is strictly stronger.

**Reading.** Closedness of the image uses slice-wise exactness in place of relative-interior
overlap.
-/
theorem theorem_39_7_closedFn {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (convexConj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    ClosedConvex (imageFn A f) := by
  refine ConvexProcess.closedConvex_imageBifun_indicatorBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Theorem 39.7** of [rockafellar1970convex], attainment in $Af$. Let $A$ be a closed convex
process from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a closed proper convex function on
$\mathbb{R}^m$, and let $x \in \mathbb{R}^n$ with $(Af)(x) < +\infty$. Suppose that $f^*$ and
$u^* \mapsto -\langle A^{*-1} u^*, x \rangle$ have an exact sum. Then there is $u$ with
$x \in Au$ and $f(u) = (Af)(x)$.

**Correction.** The book states attainment for every $x$. For the zero linear map and
$f=0$, the source relative-interior condition holds since both dual domains are $\{0\}$,
and a nonzero $x$ has an empty fiber. The Lean hypothesis $(Af)(x)\ne+\infty$ excludes
that case. -/
theorem theorem_39_7_attained_image {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f) {x : Rn n}
    (hex : IsExactSum (pairing m) (convexConj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x)))
    (hne : imageFn A f x ≠ ⊤) :
    ∃ u : Rn m, x ∈ A.eval u ∧ f u = imageFn A f x := by
  refine ConvexProcess.exists_mem_eval_and_eq_imageBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_ hne
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Theorem 39.7** of [rockafellar1970convex], the conjugate of $Af$. Under the hypotheses of
`Rockafellar.theorem_39_7_closedFn`,
$$(Af)^* = \operatorname{cl}(A^{*-1} f^*),$$
where $\operatorname{cl}$ is the closure `ConvexAnalysis.convexCl`.

**Reading.** The conjugate closure formula uses a family of exact sums.
-/
theorem theorem_39_7_closure {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (convexConj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    convexConj (pairing n) (imageFn A f)
      = convexCl (imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (convexConj (pairing m) f)) := by
  refine ConvexProcess.convexConj_imageBifun_indicatorBifun_eq_convexCl (Bu := pairing m)
      (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-! ### Corollary 39.7.1 -/

/-- **Corollary 39.7.1** of [rockafellar1970convex]. Let $A$ be a closed convex process from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and let $C \subseteq \mathbb{R}^m$ be a nonempty closed convex
set. If no nonzero vector of $A^{-1} 0$ is in the recession cone $0^+ C$, then $AC$ is closed.

The proof applies Theorem 9.1 to the projection $(u, x) \mapsto x$, and does not specialize
Theorem 39.7: $AC$ is the image of $\operatorname{graph} A \cap (C \times \mathbb{R}^n)$, whose
recession cone is $\operatorname{graph} A \cap (0^+ C \times \mathbb{R}^n)$. -/
theorem corollary_39_7_1 {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty)
    (h : ∀ v ∈ A.inv.eval 0, v ≠ 0 → v ∉ recessionCone C) :
    IsClosed (A.image C) := by
  refine ConvexProcess.isClosed_image hA hC hCcl hCne fun v hv hrec => ?_
  by_contra hv0
  exact h v hv hv0 hrec

/-- **Corollary 39.7.1** of [rockafellar1970convex], the case "which is true in particular if $C$ is
bounded". Let $A$ be a closed convex process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let
$C \subseteq \mathbb{R}^m$ be a nonempty, closed, bounded convex set. Then $AC$ is closed. -/
theorem corollary_39_7_1_isBounded {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) :=
  ConvexProcess.isClosed_image_of_isBounded hA hC hCcl hCne hb

/-! ### Theorem 39.8 -/

/-- **Theorem 39.8** of [rockafellar1970convex], first statement. Let $A$ be an oriented convex
process from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $B$ one from $\mathbb{R}^n$ to $\mathbb{R}^p$,
with the same orientation. Suppose that for all $z^* \in \mathbb{R}^p$ and
$u^* \in \mathbb{R}^m$ the two functions
$$x \mapsto \inf \{\langle u, u^* \rangle \mid u \in A^{-1} x\}, \qquad x \mapsto -\sup
  \{\langle z, z^* \rangle \mid z \in Bx\}$$
have an exact sum. Then
$$(BA)^* = A^* B^*.$$

The book assumes $\operatorname{ri}(\operatorname{range} A) \cap
\operatorname{ri}(\operatorname{dom} B) \neq \emptyset$. The exact-sum hypothesis
(`ConvexAnalysis.IsExactSum`) is strictly stronger, and this form of the theorem is not
formalized; see the module doc comment. As in Theorem 39.5, the equal orientations can be
expressed only because the orientation is data. The proof does not use Theorem 38.5; it obtains
a linear function between the two functions from Fenchel's duality theorem.

**Reading.** The adjoint composition formula uses exact sums instead of relative-interior overlap.
-/
theorem theorem_39_8 (A : OrientedProcess m n) (B : OrientedProcess n p)
    (hor : B.orientation = A.orientation)
    (hex : ∀ (w : Rn p) (v : Rn m), IsExactSum (pairing n)
      (fun x => ⨅ u ∈ A.process.inv.eval x, ((pairing m u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.process.eval x, ((pairing p z w : ℝ) : EReal)))) :
    (B.comp A).adjoint = A.adjoint.comp B.adjoint := by
  obtain ⟨A, oA⟩ := A
  obtain ⟨B, oB⟩ := B
  have hor' : oB = oA := hor
  subst hor'
  cases oB
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl

/-- **Theorem 39.8** of [rockafellar1970convex], second statement, closedness. Let $A$ and $B$ be
closed convex processes from $\mathbb{R}^m$ to $\mathbb{R}^n$ and from $\mathbb{R}^n$ to
$\mathbb{R}^p$, supremum oriented. Suppose that for all $u \in \mathbb{R}^m$ and
$z \in \mathbb{R}^p$ the two functions
$$x^* \mapsto \inf \{\langle z, w^* \rangle \mid w^* \in B^{*-1} x^*\}, \qquad x^* \mapsto -\sup
  \{\langle u, u^* \rangle \mid u^* \in A^* x^*\}$$
have an exact sum. Then $BA$ is closed.

The book assumes that $\operatorname{ri}(\operatorname{range} B^*)$ meets
$\operatorname{ri}(\operatorname{dom} A^*)$. The exact-sum hypothesis is strictly stronger.

**Reading.** Composition closure uses exactness and treats the supremum orientation.
-/
theorem theorem_39_8_isClosed {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    IsClosed (((B.comp A).graph : Set (Rn m × Rn p))) := by
  refine ConvexProcess.isClosed_graph_comp (pairing m) (pairing n) (pairing p) hA hB ?_
  simpa only [flip_pairing] using hex

/-- **Theorem 39.8** of [rockafellar1970convex], second statement, the adjoint of the product. Under
the hypotheses of `Rockafellar.theorem_39_8_isClosed`, the graph of $(BA)^*$ is the closure of
the graph of $A^* B^*$:
$$(BA)^* = \operatorname{cl}(A^* B^*).$$

**Reading.** Adjoint closure uses exactness and treats the supremum orientation.
-/
theorem theorem_39_8_closure {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing p) (B.comp A)).graph
        : Set (Rn p × Rn m))
      = closure ((((ConvexProcess.adjointProcess (pairing m) (pairing n) A).comp
          (ConvexProcess.adjointProcess (pairing n) (pairing p) B)).graph
            : Set (Rn p × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_comp_eq_closure (pairing m) (pairing n) (pairing p)
    hA hB ?_
  simpa only [flip_pairing] using hex

end Rockafellar
