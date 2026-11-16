/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Recession.Closedness

/-!
# Convex processes

Let $U$ and $X$ be real vector spaces. A **convex process** from $U$ to $X$ is a multivalued map
$A : u \mapsto Au \subseteq X$ with $A(u_1 + u_2) \supseteq Au_1 + Au_2$,
$A(\lambda u) = \lambda (Au)$ for $\lambda > 0$, and $0 \in A0$. These conditions say exactly that
the graph $\{(u, x) \mid x \in Au\}$ is a convex cone that contains the origin. Convex processes lie
between linear transformations and convex bifunctions: a linear transformation is a convex process,
and a convex process $A$ gives the convex bifunction $(Fu)(x) = \delta(x \mid Au)$. The sum
$A_1 + A_2$, the multiple $\lambda A$, the product $BA$ and the inverse $A^{-1}$ are convex
processes again. The presentation follows [rockafellar1970convex], §39.

Let $U$ be paired with a space $V$ and $X$ with a space $Y$, and write $u^* \in V$ and $x^* \in Y$
for the dual variables. The **adjoint** of $A$ is the convex process $A^*$ from $Y$ to $V$ with
$$A^* x^* = \{u^* \mid \langle x, x^* \rangle \le \langle u, u^* \rangle \text{ for all } (u, x) \in
  \operatorname{graph} A\}.$$
Thus $(x^*, u^*) \in \operatorname{graph} A^*$ if and only if $(-u^*, x^*)$ lies in the polar cone
of $\operatorname{graph} A$, and every topological fact about $A^*$ comes from the theory of polar
cones. The module proves that $A^*$ is closed and that $A^{**} = \operatorname{cl} A$, gives the
inner products $\langle Au, x^* \rangle = \sup \{\langle x, x^* \rangle \mid x \in Au\}$ and
$\langle u, A^* x^* \rangle = \inf \{\langle u, u^* \rangle \mid u^* \in A^* x^*\}$, and computes
the adjoints of sums, multiples and products and the conjugate of the image of a convex function.

## Main definitions

* `ConvexAnalysis.ConvexProcess`: a convex process from $U$ to $X$, given by its graph, a pointed
  convex cone in $U \times X$.
* `ConvexAnalysis.ConvexProcess.eval`, `ConvexAnalysis.ConvexProcess.dom`,
  `ConvexAnalysis.ConvexProcess.range`, `ConvexAnalysis.ConvexProcess.image`,
  `ConvexAnalysis.ConvexProcess.inv`: the value $Au$, the domain $\operatorname{dom} A$, the range
  of $A$, the image $AC$ of a set, and the inverse $A^{-1}$.
* `ConvexAnalysis.ConvexProcess.comp`: the product $(BA)u = B(Au)$; the instances `Add` and `SMul`
  give $A_1 + A_2$ and $\lambda A$.
* `ConvexAnalysis.ConvexProcess.ofLinearMap`: a linear transformation as a convex process.
* `ConvexAnalysis.ConvexProcess.indicatorBifun`: the convex bifunction
  $(Fu)(x) = \delta(x \mid Au)$.
* `ConvexAnalysis.ConvexProcess.adjointProcess`, `ConvexAnalysis.ConvexProcess.coadjointProcess`:
  the adjoint of a supremum-oriented and of an infimum-oriented process.
* `ConvexAnalysis.ConvexProcess.reflect`: the reflection of the graph through the origin, which
  exchanges the two adjoints.
* `ConvexAnalysis.ConvexProcess.coBracket`: the inner product $\langle Au, x^* \rangle = \inf
  \{\langle x, x^* \rangle \mid x \in Au\}$ of an infimum-oriented process.

## Main results

* `ConvexAnalysis.ConvexProcess.exists_linearMap_of_isBounded`: a convex process with domain $U$ and
  bounded $A0$ is a linear transformation. This is Theorem 39.1 of [rockafellar1970convex].
* `ConvexAnalysis.ConvexProcess.isClosed_graph_adjointProcess`,
  `ConvexAnalysis.ConvexProcess.coadjointProcess_adjointProcess_eq_self_iff`: $A^*$ is always
  closed, $A^{**} = \operatorname{cl} A$, and $A^{**} = A$ exactly when $A$ is closed.
* `ConvexAnalysis.ConvexProcess.bracket_indicatorBifun` and the results after it:
  $\langle Au, x^* \rangle$ is the support function of $Au$, hence closed, convex and positively
  homogeneous in $x^*$, concave and positively homogeneous in $u$, and $\langle u, A^* x^* \rangle$
  is its concave closure in $u$. This is Theorem 39.3 of [rockafellar1970convex].
* `ConvexAnalysis.ConvexProcess.adjointProcess_add`,
  `ConvexAnalysis.ConvexProcess.adjointProcess_comp`,
  `ConvexAnalysis.ConvexProcess.adjointProcess_smul`: $(A_1 + A_2)^* = A_1^* + A_2^*$,
  $(BA)^* = A^* B^*$, and $(\lambda A)^* = \lambda A^*$ for $\lambda > 0$.
* `ConvexAnalysis.ConvexProcess.isClosed_graph_add`,
  `ConvexAnalysis.ConvexProcess.graph_adjointProcess_add_eq_closure`,
  `ConvexAnalysis.ConvexProcess.isClosed_graph_comp`,
  `ConvexAnalysis.ConvexProcess.graph_adjointProcess_comp_eq_closure`: for closed processes,
  $A_1 + A_2$ and $BA$ are closed, and $(A_1 + A_2)^*$ and $(BA)^*$ are the closures of
  $A_1^* + A_2^*$ and $A^* B^*$.
* `ConvexAnalysis.ConvexProcess.convexConj_imageBifun_indicatorBifun`: $(Af)^* = (A^*)^{-1} f^*$,
  and the infimum that defines the right side is attained. This is Theorem 39.7 of
  [rockafellar1970convex].
* `ConvexAnalysis.ConvexProcess.isClosed_image`: $AC$ is closed if $A$ is closed, $C$ is nonempty,
  closed and convex, and no nonzero vector of $A^{-1} 0$ is a direction of recession of $C$.
* `ConvexAnalysis.exists_pairing_sandwich`: if $p \le q$, $q$ and $-p$ add exactly, and
  $p(0) \ge 0 \ge q(0)$, then some linear function $\langle \cdot, y \rangle$ lies between $p$ and
  $q$.

## Conventions

* The pairings are bilinear maps `Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ` and `Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ`. The Lean
  variables `y` and `v` stand for the dual vectors $x^* \in Y$ and $u^* \in V$.
* Rockafellar treats "supremum oriented" and "infimum oriented" as extra data on a convex process,
  and defines the adjoint of an infimum-oriented process by reversing the inequality. Here the two
  adjoints are two definitions, `ConvexAnalysis.ConvexProcess.adjointProcess` and
  `ConvexAnalysis.ConvexProcess.coadjointProcess`, and $A^{**}$ uses one of each. The results about
  infimum-oriented processes have `co` in their names.

## Implementation notes

* `ConvexAnalysis.ConvexProcess` is a bundled `PointedCone ℝ (U × X)`: the value `A.eval u` is the
  slice of the cone at $u$, and every elementary property is a fact about submodules.
* With `ConvexAnalysis.ConvexProcess.adjointProcess` used twice, the two sign changes add instead of
  cancelling, and the result is $\{p \mid 0 \le \langle p, w \rangle \text{ for all } w \in
  K^\circ\}$ in place of the bipolar $K^{\circ\circ}$ of the graph $K$. For this reason the second
  adjoint is the infimum-oriented one.
* Reflection through the origin (`ConvexAnalysis.ConvexProcess.reflect`) exchanges the two adjoints
  and commutes with sums and products. So every infimum-oriented statement is the supremum-oriented
  one read back through the reflection. The inner products are the exception: there the reflection
  changes the dual variable only, and `ConvexAnalysis.ConvexProcess.coBracket_eq_neg_bracket`
  records the sign.
* The adjoints of a sum and of a product take an `ConvexAnalysis.IsExactSum` hypothesis, one
  instance for each dual vector, where Rockafellar assumes $\operatorname{ri}(\operatorname{dom}
  A_1) \cap \operatorname{ri}(\operatorname{dom} A_2) \neq \emptyset$. Because
  `ConvexAnalysis.IsExactSum` also requires both summands to be proper, this hypothesis is stronger
  than the one of the source.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### The definition -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- A **convex process** from $U$ to $X$ is a multivalued map $A : u \mapsto Au \subseteq X$ with

* $A(u_1 + u_2) \supseteq Au_1 + Au_2$,
* $A(\lambda u) = \lambda (Au)$ for $\lambda > 0$,
* $0 \in A0$.

These conditions hold exactly when the graph of $A$ is a convex cone in $U \times X$ that
contains the origin. A convex process is therefore given here by its graph, a
`PointedCone ℝ (U × X)`, read as a relation. -/
structure ConvexProcess (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X]
    [Module ℝ X] where
  /-- The graph $\{(u, x) \mid x \in Au\}$ of the process, a convex cone that contains the origin.
  -/
  graph : PointedCone ℝ (U × X)

namespace ConvexProcess

variable {A : ConvexProcess U X} {u u₁ u₂ : U} {x x₁ x₂ : X}

/-- The value $Au = \{x \mid (u, x) \in \operatorname{graph} A\}$ of the process at $u$: the slice
of the graph at $u$. -/
def eval (A : ConvexProcess U X) (u : U) : Set X := {x | (u, x) ∈ A.graph}

/-- $x \in Au$ if and only if $(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_eval : x ∈ A.eval u ↔ (u, x) ∈ A.graph := Iff.rfl

/-- The graph of a convex process, as a relation from $U$ to $X$. -/
def toSetRel (A : ConvexProcess U X) : SetRel U X := (A.graph : Set (U × X))

/-- A pair lies in the relation of $A$ if and only if it lies in the graph of $A$. -/
@[simp] theorem mem_toSetRel {p : U × X} : p ∈ A.toSetRel ↔ p ∈ A.graph := Iff.rfl

/-- The **effective domain** $\operatorname{dom} A = \{u \mid Au \neq \emptyset\}$ of a convex
process. -/
def dom (A : ConvexProcess U X) : Set U := {u | (A.eval u).Nonempty}

/-- $u \in \operatorname{dom} A$ if and only if $Au$ is nonempty. -/
@[simp] theorem mem_dom : u ∈ A.dom ↔ (A.eval u).Nonempty := Iff.rfl

/-- The **range** of a convex process: the set of $x$ with $(u, x) \in \operatorname{graph} A$ for
some $u$. -/
def range (A : ConvexProcess U X) : Set X := {x | ∃ u, (u, x) ∈ A.graph}

/-- $x$ lies in the range of $A$ if and only if $(u, x) \in \operatorname{graph} A$ for some $u$. -/
@[simp] theorem mem_range : x ∈ A.range ↔ ∃ u, (u, x) ∈ A.graph := Iff.rfl

/-- The **image** of a set $C \subseteq U$ under a convex process:
$AC = \bigcup \{Au \mid u \in C\}$. -/
def image (A : ConvexProcess U X) (C : Set U) : Set X := {x | ∃ u ∈ C, (u, x) ∈ A.graph}

/-- $x \in AC$ if and only if $(u, x) \in \operatorname{graph} A$ for some $u \in C$. -/
@[simp] theorem mem_image {C : Set U} : x ∈ A.image C ↔ ∃ u ∈ C, (u, x) ∈ A.graph := Iff.rfl

/-- The image of the whole space $U$ under $A$ is the range of $A$. -/
theorem image_univ (A : ConvexProcess U X) : A.image univ = A.range := by
  ext x; simp

/-- Two convex processes with the same graph are equal. -/
@[ext] theorem ext {A B : ConvexProcess U X} (h : A.graph = B.graph) : A = B := by
  cases A
  cases B
  simp only [ConvexProcess.mk.injEq]
  exact h

/-- A linear transformation $T : U \to X$, read as a convex process. Its graph $\{(u, Tu)\}$ is a
linear subspace, and so in particular a convex cone that contains the origin. -/
def ofLinearMap (T : U →ₗ[ℝ] X) : ConvexProcess U X where
  graph :=
    { carrier := {p : U × X | p.2 = T p.1}
      zero_mem' := by simp
      add_mem' := by
        rintro ⟨u₁, x₁⟩ ⟨u₂, x₂⟩ h₁ h₂
        simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
        rw [Prod.mk_add_mk, map_add, h₁, h₂]
      smul_mem' := by
        rintro c ⟨u, x⟩ h
        simp only [Set.mem_ofPred_eq] at h ⊢
        change (c : ℝ) • x = T ((c : ℝ) • u)
        rw [map_smul, h] }

/-- $(u, x)$ lies in the graph of the process of $T$ if and only if $x = Tu$. -/
@[simp] theorem mem_graph_ofLinearMap {T : U →ₗ[ℝ] X} {p : U × X} :
    p ∈ (ofLinearMap T).graph ↔ p.2 = T p.1 := Iff.rfl

/-- The process of a linear transformation $T$ has the values $Au = \{Tu\}$. -/
@[simp] theorem eval_ofLinearMap (T : U →ₗ[ℝ] X) (u : U) : (ofLinearMap T).eval u = {T u} := by
  ext x
  simp [eval]

/-- The process of a linear transformation has domain $U$. -/
@[simp] theorem dom_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).dom = univ := by
  ext u
  simp

/-- The **inverse** of a convex process $A$ from $U$ to $X$: the convex process $A^{-1}$ from $X$ to
$U$ with $(x, u) \in \operatorname{graph} A^{-1}$ if and only if
$(u, x) \in \operatorname{graph} A$. -/
def inv (A : ConvexProcess U X) : ConvexProcess X U where
  graph :=
    { carrier := {p : X × U | (p.2, p.1) ∈ A.graph}
      zero_mem' := A.graph.zero_mem
      add_mem' := fun h₁ h₂ => A.graph.add_mem h₁ h₂
      smul_mem' := fun c _ h => Submodule.smul_mem A.graph c h }

/-- $(x, u) \in \operatorname{graph} A^{-1}$ if and only if $(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_graph_inv {p : X × U} : p ∈ A.inv.graph ↔ (p.2, p.1) ∈ A.graph := Iff.rfl

/-- $u \in A^{-1} x$ if and only if $(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_eval_inv : u ∈ A.inv.eval x ↔ (u, x) ∈ A.graph := Iff.rfl

/-- $(A^{-1})^{-1} = A$. -/
theorem inv_inv (A : ConvexProcess U X) : A.inv.inv = A := by
  ext p
  rfl

/-- The domain of $A^{-1}$ is the range of $A$. -/
theorem dom_inv (A : ConvexProcess U X) : A.inv.dom = A.range := by
  ext x
  simp only [mem_dom, mem_range, Set.Nonempty, mem_eval_inv]

/-- The range of $A^{-1}$ is the domain of $A$. -/
theorem range_inv (A : ConvexProcess U X) : A.inv.range = A.dom := by
  ext u
  simp only [mem_range, mem_dom, Set.Nonempty, mem_eval, mem_graph_inv]

/-! ### Elementary structure -/

/-- The graph of a convex process is a convex set. -/
theorem convex_graph (A : ConvexProcess U X) : Convex ℝ (A.graph : Set (U × X)) :=
  ((A.graph : ConvexCone ℝ (U × X))).convex

/-- If $a \ge 0$ and $p \in \operatorname{graph} A$, then $a p \in \operatorname{graph} A$. This is
the form of membership that the coercion of a `PointedCone` hides. -/
theorem smul_mem_graph {a : ℝ} (ha : 0 ≤ a) {p : U × X} (hp : p ∈ A.graph) : a • p ∈ A.graph := by
  have h := Submodule.smul_mem A.graph (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hp
  exact h

/-- The graph of a convex process is closed under addition. -/
theorem add_mem_graph {p q : U × X} (hp : p ∈ A.graph) (hq : q ∈ A.graph) : p + q ∈ A.graph :=
  A.graph.add_mem hp hq

/-- The graph of a convex process contains $(0, 0)$. -/
theorem zero_mem_graph (A : ConvexProcess U X) : ((0 : U), (0 : X)) ∈ A.graph :=
  A.graph.zero_mem

/-- $0 \in A0$. -/
@[simp] theorem zero_mem_eval_zero (A : ConvexProcess U X) : (0 : X) ∈ A.eval 0 :=
  A.zero_mem_graph

/-- Each value $Au$ of a convex process is a convex set. -/
theorem convex_eval (A : ConvexProcess U X) (u : U) : Convex ℝ (A.eval u) := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab
  have h : a • ((u, x₁) : U × X) + b • (u, x₂) ∈ A.graph :=
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)
  have hfst : (a • ((u, x₁) : U × X) + b • (u, x₂)) = (u, a • x₁ + b • x₂) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hfst] at h

/-- $A0$ is a cone: if $a \ge 0$ and $x \in A0$, then $a x \in A0$. -/
theorem smul_mem_eval_zero (A : ConvexProcess U X) {a : ℝ} (ha : 0 ≤ a) (hx : x ∈ A.eval 0) :
    a • x ∈ A.eval 0 := by
  have h := smul_mem_graph ha hx
  rwa [Prod.smul_mk, smul_zero] at h

/-- $Au + A0 \subseteq Au$ for every $u$, so every value of the process is invariant along the
directions in $A0$. -/
theorem add_eval_zero_subset (A : ConvexProcess U X) (u : U) :
    A.eval u + A.eval 0 ⊆ A.eval u := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have h : ((u, x) : U × X) + (0, y) ∈ A.graph := add_mem_graph hx hy
  rwa [Prod.mk_add_mk, add_zero] at h

/-- The effective domain of a convex process is convex. -/
theorem convex_dom (A : ConvexProcess U X) : Convex ℝ A.dom := by
  rintro u₁ ⟨x₁, h₁⟩ u₂ ⟨x₂, h₂⟩ a b ha hb hab
  exact ⟨a • x₁ + b • x₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

/-- The range of a convex process is convex. -/
theorem convex_range (A : ConvexProcess U X) : Convex ℝ A.range := by
  rintro x₁ ⟨u₁, h₁⟩ x₂ ⟨u₂, h₂⟩ a b ha hb hab
  exact ⟨a • u₁ + b • u₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

/-- The image $AC$ of a convex set $C$ under a convex process is convex. -/
theorem convex_image (A : ConvexProcess U X) {C : Set U} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) := by
  rintro x₁ ⟨u₁, hu₁, h₁⟩ x₂ ⟨u₂, hu₂, h₂⟩ a b ha hb hab
  refine ⟨a • u₁ + b • u₂, hC hu₁ hu₂ ha hb hab, ?_⟩
  simpa [Prod.smul_mk, Prod.mk_add_mk] using
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)

/-- The image $AC$ is the projection of $\operatorname{graph} A \cap (C \times X)$ on the second
factor. This turns closedness of $AC$ into a statement about the image of a convex set under a
linear map. -/
theorem image_eq_image_snd (A : ConvexProcess U X) (C : Set U) :
    A.image C = (LinearMap.snd ℝ U X) '' ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) := by
  ext x
  constructor
  · rintro ⟨u, hu, hp⟩
    exact ⟨(u, x), ⟨hp, hu, mem_univ x⟩, rfl⟩
  · rintro ⟨⟨u, z⟩, ⟨hp, hu, -⟩, rfl⟩
    exact ⟨u, hu, hp⟩

end ConvexProcess

end Defs

/-! ### The indicator bifunction -/

section IndicatorInjective

variable {W : Type*}

/-- The indicator function determines its set: if $\delta(\cdot \mid S) = \delta(\cdot \mid T)$,
then $S = T$.

The function $\delta(\cdot \mid S)$ takes the value $0$ exactly on $S$ and $+\infty$ off $S$,
and $0 \neq +\infty$ in `EReal`. -/
theorem indicatorFn_injective : Function.Injective (indicatorFn : Set W → W → EReal) := by
  intro S T h
  ext w
  constructor
  · intro hw
    by_contra hc
    have h0 : indicatorFn S w = 0 := indicatorFn_of_mem hw
    rw [h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)
  · intro hw
    by_contra hc
    have h0 : indicatorFn T w = 0 := indicatorFn_of_mem hw
    rw [← h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)

end IndicatorInjective

section Indicator

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

namespace ConvexProcess

/-- The **indicator bifunction** of a supremum-oriented convex process $A$: the bifunction $F$ with
$(Fu)(x) = \delta(x \mid Au)$. Through it every result about convex bifunctions applies to
convex processes. -/
noncomputable def indicatorBifun (A : ConvexProcess U X) : Bifun U X :=
  fun u => indicatorFn (A.eval u)

/-- The indicator bifunction of $A$ at $(u, x)$ is $\delta(x \mid Au)$. -/
theorem indicatorBifun_apply (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x = indicatorFn (A.eval u) x := rfl

/-- The graph function $(u, x) \mapsto (Fu)(x)$ of the indicator bifunction of $A$ is the indicator
function of the graph of $A$. -/
@[simp] theorem graphFn_indicatorBifun (A : ConvexProcess U X) :
    graphFn A.indicatorBifun = indicatorFn (A.graph : Set (U × X)) := by
  funext p
  obtain ⟨u, x⟩ := p
  rw [graphFn_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show x ∈ A.eval u from h), indicatorFn_of_mem h]
  · rw [indicatorFn_of_notMem (show x ∉ A.eval u from h), indicatorFn_of_notMem h]

/-- The indicator bifunction of a convex process never takes the value $-\infty$. -/
theorem indicatorBifun_ne_bot (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x ≠ ⊥ := indicatorFn_ne_bot _ _

/-- **A convex process is determined by its indicator bifunction**: if two convex processes have the
same indicator bifunction, they are equal.

A process is given by its graph, and the indicator function of a set determines the set. So this
is `ConvexAnalysis.indicatorFn_injective` read through
`ConvexAnalysis.ConvexProcess.graphFn_indicatorBifun`. It makes the correspondence between
processes and bifunctions one-to-one. -/
theorem indicatorBifun_injective :
    Function.Injective (indicatorBifun : ConvexProcess U X → Bifun U X) := by
  intro A₁ A₂ h
  refine ConvexProcess.ext (SetLike.ext' (indicatorFn_injective ?_))
  rw [← graphFn_indicatorBifun, ← graphFn_indicatorBifun, h]

/-- The indicator bifunction of a convex process is a convex bifunction. -/
theorem convexBifun_indicatorBifun (A : ConvexProcess U X) : ConvexBifun A.indicatorBifun := by
  rw [convexBifun_iff, graphFn_indicatorBifun]
  exact convexFn_indicatorFn.2 A.convex_graph

/-- The effective domain of the indicator bifunction of $A$ is the effective domain of $A$. -/
@[simp] theorem convexDomBifun_indicatorBifun (A : ConvexProcess U X) :
    convexDomBifun A.indicatorBifun = A.dom := by
  ext u
  simp only [mem_convexDomBifun, mem_dom, Set.Nonempty, indicatorBifun_apply]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    by_contra h
    exact hx (indicatorFn_of_notMem h)
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [indicatorFn_of_mem hx]; simp⟩

/-- For $a > 0$, the multiple $a \cdot \operatorname{graph} A$ is $\operatorname{graph} A$, because
the graph is a cone. -/
theorem smul_graph (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) :
    a • (A.graph : Set (U × X)) = (A.graph : Set (U × X)) :=
  smul_coe_pointedCone A.graph a ha

/-- For $a > 0$ and $u \in U$,
$$A(a u) = a (Au).$$
This is the axiom of positive homogeneity of a convex process.

Both inclusions are one application of `ConvexAnalysis.ConvexProcess.smul_mem_graph`, to $a$ and
to $a^{-1}$. A cone is stable under positive scaling in both directions, and this turns the
inclusion that one scaling gives into an equality. -/
theorem eval_smul_arg (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) (u : U) :
    A.eval (a • u) = a • A.eval u := by
  ext x
  constructor
  · intro hx
    have hmem : ((u, a⁻¹ • x) : U × X) ∈ A.graph := by
      have h := smul_mem_graph (A := A) (inv_nonneg.2 ha.le) hx
      rwa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
    have hval : a • a⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact ⟨a⁻¹ • x, hmem, hval⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : a • z = x := hzx
    have h := smul_mem_graph (A := A) ha.le (show ((u, z) : U × X) ∈ A.graph from hz)
    rw [Prod.smul_mk, hzx'] at h
    exact h

end ConvexProcess

end Indicator

/-! ### The algebra of convex processes, and its bifunction dictionary -/

section Algebra

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

namespace ConvexProcess

/-- The **sum** of two convex processes: $(A_1 + A_2) u = A_1 u + A_2 u$. -/
instance : Add (ConvexProcess U X) where
  add A₁ A₂ :=
    { graph :=
        { carrier := {p : U × X | ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y}
          zero_mem' := ⟨0, A₁.zero_mem_eval_zero, 0, A₂.zero_mem_eval_zero, (add_zero 0).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, y₁, k₁, rfl⟩ ⟨x₂, h₂, y₂, k₂, rfl⟩
            exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, y₁ + y₂, add_mem_graph k₁ k₂,
              add_add_add_comm x₁ y₁ x₂ y₂⟩
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, hx, y, hy, rfl⟩
            exact ⟨(c : ℝ) • x, smul_mem_graph c.2 hx, (c : ℝ) • y, smul_mem_graph c.2 hy,
              smul_add (c : ℝ) x y⟩ } }

/-- $(u, z) \in \operatorname{graph}(A_1 + A_2)$ if and only if $z = x + y$ for some $x \in A_1 u$
and $y \in A_2 u$. -/
@[simp] theorem mem_graph_add {A₁ A₂ : ConvexProcess U X} {p : U × X} :
    p ∈ (A₁ + A₂).graph ↔ ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y := Iff.rfl

/-- $(A_1 + A_2) u = A_1 u + A_2 u$. -/
@[simp] theorem eval_add (A₁ A₂ : ConvexProcess U X) (u : U) :
    (A₁ + A₂).eval u = A₁.eval u + A₂.eval u := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- **The effective domain of a sum is the intersection**: $\operatorname{dom}(A_1 + A_2) =
\operatorname{dom} A_1 \cap \operatorname{dom} A_2$. -/
@[simp] theorem dom_add (A₁ A₂ : ConvexProcess U X) : (A₁ + A₂).dom = A₁.dom ∩ A₂.dom := by
  ext u
  constructor
  · rintro ⟨_, x, hx, y, hy, -⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x + y, x, hx, y, hy, rfl⟩

/-- The **scalar multiple** $\lambda A$ of a convex process, defined by
$(\lambda A) u = \lambda (Au)$.

The graph $\{(u, \lambda x) \mid (u, x) \in \operatorname{graph} A\}$ is a convex cone that
contains the origin for every real $\lambda$, so the definition needs no positivity. The
condition $\lambda > 0$ is needed only from `ConvexAnalysis.ConvexProcess.adjointProcess_smul`
on, where the inverse scaling is used. The action satisfies $1 A = A$ and $(ab) A = a (b A)$,
but it is not additive: $2 A$ and $A + A$ differ. -/
instance : SMul ℝ (ConvexProcess U X) where
  smul a A :=
    { graph :=
        { carrier := {p : U × X | ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x}
          zero_mem' := ⟨0, A.zero_mem_graph, (smul_zero a).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, hz₁⟩ ⟨x₂, h₂, hz₂⟩
            refine ⟨x₁ + x₂, add_mem_graph h₁ h₂, ?_⟩
            have hz₁' : z₁ = a • x₁ := hz₁
            have hz₂' : z₂ = a • x₂ := hz₂
            change z₁ + z₂ = a • (x₁ + x₂)
            rw [smul_add, hz₁', hz₂']
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, h, hz⟩
            refine ⟨(c : ℝ) • x, smul_mem_graph c.2 h, ?_⟩
            have hz' : z = a • x := hz
            change (c : ℝ) • z = a • (c : ℝ) • x
            rw [hz', smul_comm] } }

/-- $(u, z) \in \operatorname{graph}(\lambda A)$ if and only if $z = \lambda x$ for some $x$ with
$(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_graph_smul {a : ℝ} {A : ConvexProcess U X} {p : U × X} :
    p ∈ (a • A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x := Iff.rfl

/-- For every real $\lambda$, $(\lambda A) u = \lambda (Au)$: the defining equation of the scalar
multiple. -/
@[simp] theorem eval_smul (a : ℝ) (A : ConvexProcess U X) (u : U) :
    (a • A).eval u = a • A.eval u := by
  ext x
  constructor
  · rintro ⟨z, hz, hx⟩
    have hx' : x = a • z := hx
    exact ⟨z, hz, hx'.symm⟩
  · rintro ⟨z, hz, hx⟩
    have hx' : a • z = x := hx
    exact ⟨z, hz, hx'.symm⟩

/-- The **product** of convex processes $A$ from $U$ to $X$ and $B$ from $X$ to $Z$: the convex
process $BA$ from $U$ to $Z$ with $(BA) u = B(Au)$. -/
def comp (B : ConvexProcess X Z) (A : ConvexProcess U X) : ConvexProcess U Z where
  graph :=
    { carrier := {p : U × Z | ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph}
      zero_mem' := ⟨0, A.zero_mem_graph, B.zero_mem_graph⟩
      add_mem' := by
        rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, k₁⟩ ⟨x₂, h₂, k₂⟩
        exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, add_mem_graph k₁ k₂⟩
      smul_mem' := by
        rintro c ⟨u, z⟩ ⟨x, h, k⟩
        exact ⟨(c : ℝ) • x, smul_mem_graph c.2 h, smul_mem_graph c.2 k⟩ }

/-- $(u, z) \in \operatorname{graph}(BA)$ if and only if there is an $x$ with
$(u, x) \in \operatorname{graph} A$ and $(x, z) \in \operatorname{graph} B$. -/
@[simp] theorem mem_graph_comp {B : ConvexProcess X Z} {A : ConvexProcess U X} {p : U × Z} :
    p ∈ (B.comp A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph := Iff.rfl

/-- $(BA) u$ is the image $B(Au)$ of the set $Au$ under $B$. -/
@[simp] theorem eval_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) (u : U) :
    (B.comp A).eval u = B.image (A.eval u) := by
  ext z
  exact Iff.rfl

/-- **The inverse of a product is the product of the inverses**: $(BA)^{-1} = A^{-1} B^{-1}$. -/
theorem inv_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).inv = A.inv.comp B.inv := by
  ext p
  constructor <;> rintro ⟨x, h, k⟩ <;> exact ⟨x, k, h⟩

/-- The indicator bifunction of $A_1 + A_2$ is the infimal convolution $F_1 \mathbin{\square} F_2$
of the indicator bifunctions $F_1$ and $F_2$ of $A_1$ and $A_2$. -/
theorem indicatorBifun_add (A₁ A₂ : ConvexProcess U X) :
    (A₁ + A₂).indicatorBifun = infConvBifun A₁.indicatorBifun A₂.indicatorBifun := by
  funext u
  change indicatorFn ((A₁ + A₂).eval u)
    = infConv (indicatorFn (A₁.eval u)) (indicatorFn (A₂.eval u))
  rw [eval_add, infConv_indicatorFn]

/-- The indicator bifunction of $BA$ is the product $GF$ of the indicator bifunctions $F$ of $A$ and
$G$ of $B$. -/
theorem indicatorBifun_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).indicatorBifun = compBifun B.indicatorBifun A.indicatorBifun := by
  funext u z
  rw [compBifun_apply]
  by_cases h : z ∈ (B.comp A).eval u
  · rw [indicatorBifun_apply, indicatorFn_of_mem h]
    obtain ⟨x₀, hx₀, hz₀⟩ := h
    symm
    refine le_antisymm ?_ (le_iInf fun x => ?_)
    · refine le_of_le_of_eq (iInf_le _ x₀) ?_
      rw [indicatorBifun_apply, indicatorFn_of_mem (show x₀ ∈ A.eval u from hx₀),
        indicatorBifun_apply, indicatorFn_of_mem (show z ∈ B.eval x₀ from hz₀), add_zero]
    · refine add_nonneg ?_ ?_
      · rw [indicatorBifun_apply]
        by_cases hx : x ∈ A.eval u <;> simp [hx]
      · rw [indicatorBifun_apply]
        by_cases hz : z ∈ B.eval x <;> simp [hz]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem h]
    symm
    refine le_antisymm le_top (le_iInf fun x => ?_)
    by_cases hx : x ∈ A.eval u
    · have hz : z ∉ B.eval x := fun hc => h ⟨x, hx, hc⟩
      rw [indicatorBifun_apply, indicatorFn_of_mem hx, indicatorBifun_apply,
        indicatorFn_of_notMem hz, zero_add]
    · rw [indicatorBifun_apply, indicatorFn_of_notMem hx]
      by_cases hz : z ∈ B.eval x
      · rw [indicatorBifun_apply, indicatorFn_of_mem hz, add_zero]
      · rw [indicatorBifun_apply, indicatorFn_of_notMem hz]
        simp

end ConvexProcess

end Algebra

/-! ### The adjoint of a convex process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {A : ConvexProcess U X}

namespace ConvexProcess

/-- The **adjoint** of a supremum-oriented convex process $A$ from $U$ to $X$: the convex process
$A^*$ from $Y$ to $V$ with
$$A^* x^* = \{u^* \in V \mid \langle x, x^* \rangle \le \langle u, u^* \rangle \text{ for all }
  (u, x) \in \operatorname{graph} A\}.$$
The adjoint is infimum oriented. -/
def adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2}
      zero_mem' := by
        intro p _
        change Bx p.2 (0 : Y) ≤ Bu p.1 (0 : V)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bx p.2 (y₁ + y₂) ≤ Bu p.1 (v₁ + v₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bx p.2 ((c : ℝ) • y) ≤ Bu p.1 ((c : ℝ) • v)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

/-- The **adjoint of an infimum-oriented convex process** $A$ from $U$ to $X$: the convex process
from $Y$ to $V$ with value
$$\{u^* \in V \mid \langle u, u^* \rangle \le \langle x, x^* \rangle \text{ for all } (u, x) \in
  \operatorname{graph} A\}$$
at $x^*$, which is the definition of `ConvexAnalysis.ConvexProcess.adjointProcess` with the
inequality reversed.

The two adjoints are kept apart so that $A^{**} = \operatorname{cl} A$ holds with the right
signs. -/
def coadjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1}
      zero_mem' := by
        intro p _
        change Bu p.1 (0 : V) ≤ Bx p.2 (0 : Y)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bu p.1 (v₁ + v₂) ≤ Bx p.2 (y₁ + y₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bu p.1 ((c : ℝ) • v) ≤ Bx p.2 ((c : ℝ) • y)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

/-- $(x^*, u^*) \in \operatorname{graph} A^*$ if and only if $\langle x, x^* \rangle \le \langle u,
u^* \rangle$ for all $(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_graph_adjointProcess {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2 :=
  Iff.rfl

/-- $(x^*, u^*)$ lies in the graph of the infimum-oriented adjoint of $A$ if and only if $\langle u,
u^* \rangle \le \langle x, x^* \rangle$ for all $(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_graph_coadjointProcess {q : Y × V} :
    q ∈ (coadjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1 :=
  Iff.rfl

/-- **The infimum-oriented adjoint is the supremum-oriented adjoint for the negated pairings**:
negating both pairings reverses the defining inequality. Every identity for the infimum-oriented
adjoint that is purely algebraic in the pairings follows from its supremum-oriented counterpart
through this. -/
theorem coadjointProcess_eq_adjointProcess_neg :
    coadjointProcess Bu Bx A = adjointProcess (-Bu) (-Bx) A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_coadjointProcess, mem_graph_adjointProcess, LinearMap.neg_apply,
    neg_le_neg_iff]

/-- $u^* \in A^* x^*$ if and only if $\langle x, x^* \rangle \le \langle u, u^* \rangle$ for all
$(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem mem_eval_adjointProcess {y : Y} {v : V} :
    v ∈ (adjointProcess Bu Bx A).eval y ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 y ≤ Bu p.1 v :=
  Iff.rfl

/-- $(x^*, u^*) \in \operatorname{graph} A^*$ if and only if $(-u^*, x^*)$ lies in the polar cone
$\{(v, y) \mid \langle u, v \rangle + \langle x, y \rangle \le 0 \text{ for all } (u, x) \in
\operatorname{graph} A\}$ of the graph of $A$. The sign change on the first factor is the one
that the adjoint of a bifunction carries. -/
theorem mem_graph_adjointProcess_iff_mem_polarCone {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔
      ((-q.2, q.1) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X)) := by
  simp only [mem_graph_adjointProcess, mem_polarCone, prodPairing_apply, map_neg,
    SetLike.mem_coe]
  constructor
  · intro h p hp
    have := h p hp
    linarith
  · intro h p hp
    have := h p hp
    linarith

/-- **The adjoint of the indicator bifunction of $A$ is the negative of the indicator bifunction of
$A^*$**: if $F$ is the indicator bifunction of $A$, then
$$(F^* x^*)(u^*) = -\delta(u^* \mid A^* x^*).$$
The negation appears because $A^*$ has the opposite orientation: an infimum-oriented set is
identified with the concave function $-\delta(\cdot \mid \cdot)$. -/
theorem convexAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx A.indicatorBifun y v =
        -((adjointProcess Bu Bx A).indicatorBifun y v) := by
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, graphFn_indicatorBifun,
    convexConj_indicatorFn_eq_indicatorFn_polarCone
      (isCone_iff_smul_eq.2 fun a ha => A.smul_graph ha)
      ⟨0, A.zero_mem_graph⟩]
  congr 1
  by_cases h : ((-v, y) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))
  · rw [indicatorFn_of_mem h, indicatorBifun_apply,
      indicatorFn_of_mem (show v ∈ (adjointProcess Bu Bx A).eval y from
        mem_graph_adjointProcess_iff_mem_polarCone.2 h)]
  · rw [indicatorFn_of_notMem h, indicatorBifun_apply,
      indicatorFn_of_notMem (show v ∉ (adjointProcess Bu Bx A).eval y from fun hc =>
        h (mem_graph_adjointProcess_iff_mem_polarCone.1 hc))]

/-- The graph of $A^{**}$, the infimum-oriented adjoint of $A^*$, is the bipolar
$(\operatorname{graph} A)^{\circ\circ}$ of the graph of $A$. The two sign changes cancel, and
for this reason the second adjoint must be the infimum-oriented one. -/
theorem graph_coadjointProcess_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = polarCone (prodPairing Bu Bx).flip
          (polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))) := by
  ext q
  simp only [SetLike.mem_coe, mem_graph_coadjointProcess, mem_polarCone, LinearMap.flip_apply,
    prodPairing_apply]
  constructor
  · rintro h ⟨a, b⟩ hab
    have hmem : ((b, -a) : Y × V) ∈ (adjointProcess Bu Bx A).graph :=
      mem_graph_adjointProcess_iff_mem_polarCone.2 (by simpa using hab)
    have hb := h (b, -a) hmem
    simp only [map_neg] at hb
    linarith
  · rintro h ⟨y, v⟩ hyv
    have hmem := mem_graph_adjointProcess_iff_mem_polarCone.1 hyv
    have hb := h (-v, y) hmem
    simp only [map_neg] at hb
    linarith

/-- **The adjoint of a scalar multiple**: for $\lambda > 0$,
$$(\lambda A)^* = \lambda A^*.$$

Rockafellar deduces this from the adjoint formula for $F\lambda$. Here it is a direct
computation on cones: $(x^*, u^*) \in \operatorname{graph}(\lambda A)^*$ says that $\lambda
\langle x, x^* \rangle \le \langle u, u^* \rangle$ on $\operatorname{graph} A$. After division
by $\lambda$ this is $(x^*, \lambda^{-1} u^*) \in \operatorname{graph} A^*$, which is
$u^* \in \lambda (A^* x^*)$. The positivity of $\lambda$ is used only for the division. -/
theorem adjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    adjointProcess Bu Bx (a • A) = a • adjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_adjointProcess, mem_graph_smul]
  constructor
  · intro h
    refine ⟨a⁻¹ • q.2, fun p hp => ?_, ?_⟩
    · have hmem : ((p.1, a • p.2) : U × X) ∈ (a • A).graph := ⟨p.2, hp, rfl⟩
      have h' := h (p.1, a • p.2) hmem
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h' ⊢
      exact (le_inv_mul_iff₀ ha).2 h'
    · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨w, hw, hv⟩ p ⟨x, hx, hz⟩
    have hz' : p.2 = a • x := hz
    have hv' : q.2 = a • w := hv
    have hle := hw (p.1, x) hx
    rw [hz', hv']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hle ha.le

/-- **The adjoint of a scalar multiple, for an infimum-oriented process**: for $\lambda > 0$,
$(\lambda A)^* = \lambda A^*$, where both adjoints are the infimum-oriented ones. This is
`ConvexAnalysis.ConvexProcess.adjointProcess_smul` for the negated pairings. -/
theorem coadjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    coadjointProcess Bu Bx (a • A) = a • coadjointProcess Bu Bx A := by
  rw [coadjointProcess_eq_adjointProcess_neg, coadjointProcess_eq_adjointProcess_neg,
    adjointProcess_smul (-Bu) (-Bx) ha]

end ConvexProcess

end Adjoint

/-! ### $A^*$ is closed, and $A^{**} = \operatorname{cl} A$ -/

section AdjointTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

section Closed

variable [TopologicalSpace V] [TopologicalSpace Y]

/-- **The adjoint of a convex process is a closed convex process.** Let $V$ and $Y$ be topological
spaces such that $\langle u, \cdot \rangle$ is continuous on $V$ for each $u \in U$ and
$\langle x, \cdot \rangle$ is continuous on $Y$ for each $x \in X$. Then the graph of $A^*$ is
closed in $Y \times V$, because it is an intersection of closed half-spaces through the origin. -/
theorem isClosed_graph_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] [IsContinuousPairing Bx.flip] (A : ConvexProcess U X) :
    IsClosed ((adjointProcess Bu Bx A).graph : Set (Y × V)) := by
  have h : ((adjointProcess Bu Bx A).graph : Set (Y × V))
      = ⋂ p ∈ (A.graph : Set (U × X)), {q : Y × V | Bx p.2 q.1 ≤ Bu p.1 q.2} := by
    ext q
    simp [mem_graph_adjointProcess]
  rw [h]
  refine isClosed_biInter fun p _ => isClosed_le ?_ ?_
  · exact (continuous_pairing Bx.flip p.2).comp continuous_fst
  · exact (continuous_pairing Bu.flip p.1).comp continuous_snd

end Closed

section Bipolar

variable [TopologicalSpace U] [TopologicalSpace X] [IsTopologicalAddGroup U]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ U] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ U]
  [LocallyConvexSpace ℝ X]

/-- $A^{**} = \operatorname{cl} A$. Let $U$ and $X$ be locally convex topological vector spaces
whose continuous linear functionals are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$ and
$\langle \cdot, x^* \rangle$ for $x^* \in Y$. Then the graph of the infimum-oriented adjoint of
$A^*$ is the closure of the graph of $A$.

Through `ConvexAnalysis.ConvexProcess.graph_coadjointProcess_adjointProcess`, this is the
bipolar theorem $K^{\circ\circ} = \operatorname{cl} K$ for the graph $K$ of $A$. -/
theorem graph_coadjointProcess_adjointProcess_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = closure (A.graph : Set (U × X)) := by
  rw [graph_coadjointProcess_adjointProcess]
  exact polarCone_polarCone A.convex_graph (isCone_iff_smul_eq.2 fun a ha => A.smul_graph ha)
    ⟨0, A.zero_mem_graph⟩

/-- **A convex process is closed exactly when it is its own second adjoint.** Let $U$ and $X$ be
locally convex topological vector spaces whose continuous linear functionals are exactly
$\langle \cdot, u^* \rangle$ for $u^* \in V$ and $\langle \cdot, x^* \rangle$ for $x^* \in Y$.
Then $A^{**} = A$, with the second adjoint infimum oriented, if and only if the graph of $A$ is
closed. -/
theorem coadjointProcess_adjointProcess_eq_self_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A) = A ↔
      IsClosed (A.graph : Set (U × X)) := by
  constructor
  · intro h
    rw [← closure_eq_iff_isClosed,
      ← graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h]
  · intro h
    refine ConvexProcess.ext (SetLike.ext' ?_)
    rw [graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h.closure_eq]

end Bipolar

end ConvexProcess

end AdjointTopology

/-!
### The two inner products

The inner product $\langle Au, x^* \rangle$ is the bracket of the indicator bifunction of $A$, and
$\langle u, A^* x^* \rangle$ is the concave bracket of its adjoint. Both are extremum problems over
the values of a process: a maximization of $\langle \cdot, x^* \rangle$ over $Au$, and a
minimization of $\langle u, \cdot \rangle$ over $A^* x^*$.
-/

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **The inner product $\langle Au, x^* \rangle$ is the support function of the convex set $Au$**:
for the indicator bifunction $F$ of $A$, the bracket $\langle Fu, \cdot \rangle = (Fu)^*$ is
$\delta^*(\cdot \mid Au)$.

Every property of $\langle Au, x^* \rangle$ in the variable $x^*$ is then a property of support
functions. The identity is `ConvexAnalysis.supportFn_eq_convexConj_indicatorFn` read backwards,
because $\langle Fu, \cdot \rangle$ is by definition the conjugate of
$Fu = \delta(\cdot \mid Au)$. -/
theorem bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    bracket Bx A.indicatorBifun u = supportFn Bx (A.eval u) :=
  (supportFn_eq_convexConj_indicatorFn Bx (A.eval u)).symm

/-- The first of Rockafellar's two extremum problems: $\langle Au, x^* \rangle = \sup \{\langle x,
x^* \rangle \mid x \in Au\}$. -/
theorem bracket_indicatorBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : bracket Bx A.indicatorBifun u y = ⨆ x ∈ A.eval u, ((Bx x y : ℝ) : EReal) := by
  rw [bracket_indicatorBifun, supportFn_apply]

/-- The function $x^* \mapsto \langle Au, x^* \rangle$ is positively homogeneous, because it is a
support function. -/
theorem posHomogeneous_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (u : U) : PosHomogeneous (bracket Bx A.indicatorBifun u) := by
  rw [bracket_indicatorBifun]
  exact posHomogeneous_supportFn Bx _

/-- The function $x^* \mapsto \langle Au, x^* \rangle$ is convex, because it is a conjugate. -/
theorem convexFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    ConvexFn (bracket Bx A.indicatorBifun u) :=
  convexFn_bracket Bx A.indicatorBifun u

/-- The function $u \mapsto \langle Au, x^* \rangle$ is positively homogeneous.

This is the one property that uses the definition of a convex process and not the general theory
of brackets: $A(\lambda u) = \lambda (Au)$ (`ConvexAnalysis.ConvexProcess.eval_smul_arg`), and
the support function of a positive multiple of a set is the same multiple of the support
function. -/
theorem posHomogeneous_bracket_indicatorBifun_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) :
    PosHomogeneous fun u => bracket Bx A.indicatorBifun u y := by
  intro a ha u
  change bracket Bx A.indicatorBifun (a • u) y = (a : EReal) * bracket Bx A.indicatorBifun u y
  rw [bracket_indicatorBifun, bracket_indicatorBifun, eval_smul_arg A ha, supportFn_smul Bx ha]

/-- The function $u \mapsto \langle Au, x^* \rangle$ is concave, because the bracket of a convex
bifunction is concave in its first variable. -/
theorem concaveFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (y : Y) : ConcaveFn fun u => bracket Bx A.indicatorBifun u y :=
  concaveFn_bracket A.convexBifun_indicatorBifun Bx y

/-- $\langle A0, 0 \rangle = 0$, because $A0$ contains $0$ and the support function of a nonempty
set is $0$ at $0$. -/
@[simp] theorem bracket_indicatorBifun_zero_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) : bracket Bx A.indicatorBifun 0 (0 : Y) = 0 := by
  rw [bracket_indicatorBifun]
  exact supportFn_zero ⟨0, A.zero_mem_eval_zero⟩

end ConvexProcess

end Bracket

section BracketClosed

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsContinuousPairing Bx.flip]

namespace ConvexProcess

/-- Let $Y$ be a topological additive group such that $\langle x, \cdot \rangle$ is continuous on
$Y$ for each $x \in X$. Then the function $x^* \mapsto \langle Au, x^* \rangle$ is a closed
convex function. -/
theorem closedConvex_bracket_indicatorBifun (A : ConvexProcess U X) (u : U) :
    ClosedConvex (bracket Bx A.indicatorBifun u) :=
  closedConvex_bracket (F := A.indicatorBifun) u

end ConvexProcess

end BracketClosed

section ConcaveBracket

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The second of Rockafellar's two extremum problems: $\langle u, A^* x^* \rangle = \inf \{\langle
u, u^* \rangle \mid u^* \in A^* x^*\}$, where $\langle u, A^* x^* \rangle$ is the concave
bracket of the adjoint $F^*$ of the indicator bifunction $F$ of $A$.

Together with `ConvexAnalysis.ConvexProcess.bracket_indicatorBifun_apply` this is a dual pair of
linear programs. The two values differ only by a closure in $u$
(`ConvexAnalysis.ConvexProcess.concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁`).
The proof is the definition of the concave bracket together with
`ConvexAnalysis.ConvexProcess.convexAdjointBifun_indicatorBifun`: the indicator of $A^* x^*$
turns the unrestricted infimum into a restricted one. -/
theorem concaveBracket_convexAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) u y
      = ⨅ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal) := by
  rw [concaveBracket_apply]
  refine iInf_congr fun v => ?_
  rw [convexAdjointBifun_indicatorBifun]
  by_cases hv : v ∈ (adjointProcess Bu Bx A).eval y
  · rw [indicatorBifun_apply, indicatorFn_of_mem hv, neg_zero, sub_zero, iInf_pos hv]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem hv, iInf_neg hv]
    simp

end ConvexProcess

end ConcaveBracket

section ConcaveBracketClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- $\langle u, A^* x^* \rangle = \operatorname{cl}_u \langle Au, x^* \rangle$: the two inner
products differ by a closure in $u$. Let $U$ be a locally convex topological vector space whose
continuous linear functionals are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$. Then for
each $x^* \in Y$ the function $u \mapsto \langle u, A^* x^* \rangle$ is the concave closure of
$u \mapsto \langle Au, x^* \rangle$.

The concave closure in the first variable is the only difference between the two inner products,
for every convex process: closedness of $A$ plays no part. This is
`ConvexAnalysis.concaveBracket_convexAdjointBifun_eq_partialCl₁` applied to the indicator
bifunction. -/
theorem concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁ (A : ConvexProcess U X)
    (y : Y) :
    (fun u => concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) u y)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2) (u, y) :=
  concaveBracket_convexAdjointBifun_eq_partialCl₁ A.convexBifun_indicatorBifun y

end ConvexProcess

end ConcaveBracketClosure

/-! ### The adjoint of a sum of processes -/

section AdjointAdd

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **The adjoint of a sum is the sum of the adjoints.** Suppose that for every $x^* \in Y$ the
functions $u \mapsto -\langle A_1 u, x^* \rangle$ and $u \mapsto -\langle A_2 u, x^* \rangle$
add exactly (`ConvexAnalysis.IsExactSum`). Then
$$(A_1 + A_2)^* = A_1^* + A_2^*.$$

Where the source assumes $\operatorname{ri}(\operatorname{dom} A_1) \cap
\operatorname{ri}(\operatorname{dom} A_2) \neq \emptyset$, the hypothesis here is the exactness
of the sum, one instance for each $x^*$. Because `ConvexAnalysis.IsExactSum` also requires both
summands to be proper, this hypothesis is stronger than the one of the source. -/
theorem adjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A₁ A₂ : ConvexProcess U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(supportFn Bx (A₁.eval u) y))
      (fun u => -(supportFn Bx (A₂.eval u) y))) :
    adjointProcess Bu Bx (A₁ + A₂) = adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂ := by
  have hex' : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx A₁.indicatorBifun u y))
      (fun u => -(bracket Bx A₂.indicatorBifun u y)) := by
    intro y
    have e₁ : (fun u => -(bracket Bx A₁.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₁.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₁ u) y)
    have e₂ : (fun u => -(bracket Bx A₂.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₂.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₂ u) y)
    rw [e₁, e₂]
    exact hex y
  have key : ∀ y : Y, (adjointProcess Bu Bx (A₁ + A₂)).eval y
      = (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂).eval y := by
    intro y
    have hL : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = convexAdjointBifun Bu Bx (A₁ + A₂).indicatorBifun y :=
      funext fun v => (convexAdjointBifun_indicatorBifun Bu Bx (A₁ + A₂) y v).symm
    have hR₁ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y) v))
        = convexAdjointBifun Bu Bx A₁.indicatorBifun y :=
      funext fun v => (convexAdjointBifun_indicatorBifun Bu Bx A₁ y v).symm
    have hR₂ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₂).eval y) v))
        = convexAdjointBifun Bu Bx A₂.indicatorBifun y :=
      funext fun v => (convexAdjointBifun_indicatorBifun Bu Bx A₂ y v).symm
    have heq : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y
            + (adjointProcess Bu Bx A₂).eval y) v) := by
      rw [hL, ← supConv_neg_indicatorFn, hR₁, hR₂, indicatorBifun_add]
      exact convexAdjointBifun_infConvBifun Bu Bx _ _ (hex' y)
    have hsets : (adjointProcess Bu Bx (A₁ + A₂)).eval y
        = (adjointProcess Bu Bx A₁).eval y + (adjointProcess Bu Bx A₂).eval y :=
      indicatorFn_injective (funext fun v => neg_injective (congrFun heq v))
    rw [hsets, eval_add]
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  obtain ⟨y, v⟩ := q
  rw [← mem_eval, ← mem_eval, key y]

end ConvexProcess

end AdjointAdd

/-! ### The adjoint of a product of processes -/

section Sandwich

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **A linear sandwich.** Let $E$ be paired with $F$, and let $p, q : E \to [-\infty, +\infty]$.
Suppose that $q$ and $-p$ add exactly (`ConvexAnalysis.IsExactSum`), that $p(x) \le q(x)$ for
all $x$, and that $p(0) \ge 0 \ge q(0)$. Then there is a $y \in F$ with
$$p(x) \le \langle x, y \rangle \le q(x) \quad \text{for all } x \in E.$$

This is Fenchel's duality theorem in the case $p(0) \ge 0 \ge q(0)$. There the concave conjugate
satisfies $p_*(y) \le 0$ and the convex conjugate satisfies $q^*(y) \ge 0$ for every $y$, so the
attained dual value $p_*(y) - q^*(y) \ge 0$ forces both to vanish. The equations $p_*(y) = 0$
and $q^*(y) = 0$ say exactly that $p \le \langle \cdot, y \rangle$ and
$\langle \cdot, y \rangle \le q$. No convexity hypothesis appears; the exactness hypothesis
takes its place. -/
theorem exists_pairing_sandwich {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {p q : E → EReal}
    (hex : IsExactSum B q fun x => -(p x)) (hle : ∀ x, p x ≤ q x)
    (hp0 : (0 : EReal) ≤ p 0) (hq0 : q 0 ≤ 0) :
    ∃ y : F, (∀ x, p x ≤ ((B x y : ℝ) : EReal)) ∧ ∀ x, ((B x y : ℝ) : EReal) ≤ q x := by
  have hex' : IsExactSum B q (-p) := hex
  have hqnb : ∀ x, q x ≠ ⊥ := hex'.properConvex_left.ne_bot
  have hpnt : ∀ x, p x ≠ ⊤ := fun x hx => hex'.properConvex_right.ne_bot x (by simp [hx])
  have hinf : (0 : EReal) ≤ ⨅ x, q x - p x := by
    refine le_iInf fun x => ?_
    rw [EReal.le_sub_iff_add_le (.inr (hqnb x)) (.inl (hpnt x)), zero_add]
    exact hle x
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_convexConj_eq (B := B) hex'
  have hcc_le : concaveConj B p y ≤ 0 := by
    have h := concaveConj_le_sub B p 0 y
    simp only [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
    refine h.trans ?_
    have hz : (0 : EReal) - p 0 = -(p 0) := zero_add _
    rw [hz]
    exact EReal.neg_le.2 (by rw [neg_zero]; exact hp0)
  have hconj_ge : (0 : EReal) ≤ convexConj B q y := by
    have h := sub_le_convexConj B q 0 y
    simp only [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
    refine le_trans ?_ h
    have hz : (0 : EReal) - q 0 = -(q 0) := zero_add _
    rw [hz]
    exact EReal.le_neg.2 (by rw [neg_zero]; exact hq0)
  have hbne : convexConj B q y ≠ ⊥ := by
    intro h
    rw [h] at hconj_ge
    exact absurd hconj_ge (by simp)
  have hcne : concaveConj B p y ≠ ⊤ := by
    intro h
    rw [h] at hcc_le
    exact absurd hcc_le (by simp)
  have hkey : convexConj B q y ≤ concaveConj B p y := by
    have h0 : (0 : EReal) ≤ concaveConj B p y - convexConj B q y := by rw [hy]; exact hinf
    rwa [EReal.le_sub_iff_add_le (.inl hbne) (.inr hcne), zero_add] at h0
  refine ⟨y, fun x => ?_, fun x => ?_⟩
  · have hmem : ((0 : ℝ) : EReal) ≤ concaveConj B p y := by
      rw [EReal.coe_zero]
      exact hconj_ge.trans hkey
    have h3 := coe_le_concaveConj_iff.1 hmem x
    rwa [affineFn_apply, EReal.coe_zero, sub_zero] at h3
  · have hmem : convexConj B q y ≤ ((0 : ℝ) : EReal) := by
      rw [EReal.coe_zero]
      exact hkey.trans hcc_le
    have h3 := convexConj_le_coe_iff.1 hmem x
    rwa [affineFn_apply, EReal.coe_zero, sub_zero] at h3

end Sandwich

section AdjointComp

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]

namespace ConvexProcess

/-- For convex processes $A$ from $U$ to $X$ and $B$ from $X$ to $Z$, the graph of $A^* B^*$ is
contained in the graph of $(BA)^*$. No hypothesis is needed.

A pair $(z^*, u^*)$ that factors through $B^*$ and then $A^*$ chains the two defining
inequalities, $\langle z, z^* \rangle \le \langle x, x^* \rangle \le \langle u, u^* \rangle$,
for every factorization $u \mapsto x \mapsto z$ in $BA$. -/
theorem comp_adjointProcess_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z) :
    ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B)).graph
      ≤ (adjointProcess Bu Bz (B.comp A)).graph := by
  rintro ⟨w, v⟩ ⟨y, hwy, hyv⟩ ⟨u, z⟩ ⟨x, hux, hxz⟩
  exact le_trans (hwy (x, z) hxz) (hyv (u, x) hux)

/-- **The adjoint of a product is the product of the adjoints.** Let $A$ be a convex process from
$U$ to $X$ and $B$ one from $X$ to $Z$, and let $Z$ be paired with $W$. Suppose that for every
$z^* \in W$ and $u^* \in V$ the functions
$$x \mapsto \inf \{\langle u, u^* \rangle \mid u \in A^{-1} x\} \quad\text{and}\quad x \mapsto
  -\sup \{\langle z, z^* \rangle \mid z \in Bx\}$$
add exactly (`ConvexAnalysis.IsExactSum`). Then
$$(BA)^* = A^* B^*.$$

Where the source assumes $\operatorname{ri}(\operatorname{range} A) \cap
\operatorname{ri}(\operatorname{dom} B) \neq \emptyset$, the hypothesis here is that condition
in the form of exactness, one instance for each $(z^*, u^*)$: the effective domains of the two
functions are $\operatorname{range} A$ and $\operatorname{dom} B$. Because
`ConvexAnalysis.IsExactSum` also requires both summands to be proper, this hypothesis is
stronger than the one of the source.

The pair $(z^*, u^*)$ lies in $\operatorname{graph}(BA)^*$ when the concave function
$x \mapsto \langle Bx, z^* \rangle$ lies below the convex function
$x \mapsto \langle u^*, A^{-1} x \rangle$. A factorization through $A^*$ and $B^*$ is a linear
function between the two, which `ConvexAnalysis.exists_pairing_sandwich` supplies. -/
theorem adjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z)
    (hex : ∀ (w : W) (v : V), IsExactSum Bx
      (fun x => ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal)))) :
    adjointProcess Bu Bz (B.comp A)
      = (adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨w, v⟩ := r
  refine ⟨fun hr => ?_, fun hr => comp_adjointProcess_le Bu Bx Bz A B hr⟩
  have hle : ∀ x : X, (⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal))
      ≤ ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal) := by
    intro x
    refine iSup₂_le fun z hz => le_iInf₂ fun u hu => ?_
    exact_mod_cast hr (u, z) ⟨x, hu, hz⟩
  have hp0 : (0 : EReal) ≤ ⨆ z ∈ B.eval (0 : X), ((Bz z w : ℝ) : EReal) :=
    le_iSup₂_of_le (0 : Z) B.zero_mem_eval_zero (by simp)
  have hq0 : (⨅ u ∈ A.inv.eval (0 : X), ((Bu u v : ℝ) : EReal)) ≤ 0 :=
    iInf₂_le_of_le (0 : U) A.inv.zero_mem_eval_zero (by simp)
  obtain ⟨y, hpy, hqy⟩ := exists_pairing_sandwich (hex w v) hle hp0 hq0
  refine ⟨y, ?_, ?_⟩
  · rintro ⟨x, z⟩ hxz
    have h := le_trans (le_iSup₂_of_le z hxz le_rfl) (hpy x)
    exact_mod_cast h
  · rintro ⟨u, x⟩ hux
    have h := le_trans (hqy x) (iInf₂_le_of_le u hux le_rfl)
    exact_mod_cast h

end ConvexProcess

end AdjointComp



/-! ### The conjugate of an image under a convex process -/

section ImageConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The indicator bifunction of $A^{-1}$ is the indicator bifunction of $A$ with the arguments
exchanged: both values at $(x, u)$ are $\delta$ of the condition
$(u, x) \in \operatorname{graph} A$. -/
@[simp] theorem indicatorBifun_inv (A : ConvexProcess U X) (x : X) (u : U) :
    A.inv.indicatorBifun x u = A.indicatorBifun u x := by
  rw [indicatorBifun_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show u ∈ A.inv.eval x from h),
      indicatorFn_of_mem (show x ∈ A.eval u from h)]
  · rw [indicatorFn_of_notMem (show u ∉ A.inv.eval x from h),
      indicatorFn_of_notMem (show x ∉ A.eval u from h)]

/-- $(A^{-1})^* = (A^*)^{-1}$. The inverse of a supremum-oriented process is infimum oriented, so
its adjoint is the infimum-oriented one. With that reading the identity is an unfolding of
definitions: both sides have the graph $\{(u^*, x^*) \mid \langle x, x^* \rangle \le \langle u,
u^* \rangle \text{ for all } (u, x) \in \operatorname{graph} A\}$. -/
theorem coadjointProcess_inv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    coadjointProcess Bx Bu A.inv = (adjointProcess Bu Bx A).inv := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  exact ⟨fun h p hp => h (p.2, p.1) hp, fun h p hp => h (p.2, p.1) hp⟩

/-- The lower adjoint $F_*^*$ of the indicator bifunction $F$ of $A$ is the indicator bifunction of
$(A^*)^{-1}$.

This is `ConvexAnalysis.ConvexProcess.convexAdjointBifun_indicatorBifun`: the two negations in
`ConvexAnalysis.lowerAdjointBifun` cancel the negation that the opposite orientation of $A^*$
puts on its indicator, and `ConvexAnalysis.ConvexProcess.indicatorBifun_inv` absorbs the
exchange of the arguments. It is the last ingredient of $(Af)^* = (A^*)^{-1} f^*$. -/
theorem lowerAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    lowerAdjointBifun Bu Bx A.indicatorBifun = (adjointProcess Bu Bx A).inv.indicatorBifun := by
  funext v y
  rw [lowerAdjointBifun_apply, convexAdjointBifun_indicatorBifun, neg_neg, indicatorBifun_inv]

/-- The indicator bifunction of a convex process is finite at $(0, 0)$, because $0 \in A0$. This is
the condition "finite somewhere" that the results on closed images ask of a bifunction. -/
theorem indicatorBifun_zero_zero_ne_top (A : ConvexProcess U X) :
    A.indicatorBifun 0 0 ≠ ⊤ := by
  rw [indicatorBifun_apply, indicatorFn_of_mem A.zero_mem_eval_zero]
  simp

/-- Let $f : U \to [-\infty, +\infty]$ be a proper convex function and let $x^* \in Y$. Write $Af$
for the image of $f$ under the indicator bifunction of $A$, that is,
$(Af)(x) = \inf \{f(u) \mid x \in Au\}$. Suppose that $f$ and
$u \mapsto -\langle Au, x^* \rangle$ add exactly (`ConvexAnalysis.IsExactSum`). Then
$$(Af)^*(x^*) = ((A^*)^{-1} f^*)(x^*) = \inf \{f^*(u^*) \mid u^* \in A^* x^*\}.$$
This is Theorem 39.7 of [rockafellar1970convex].

This specializes the conjugate of an image under a bifunction; the only work is
`ConvexAnalysis.ConvexProcess.lowerAdjointBifun_indicatorBifun`. The condition
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} A) \neq
\emptyset$ of the source becomes the exactness hypothesis of
`ConvexAnalysis.convexConj_imageBifun`, because the domain of the indicator bifunction is
$\operatorname{dom} A$. -/
theorem convexConj_imageBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) {f : U → EReal} (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    convexConj Bx (imageBifun A.indicatorBifun f) y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (convexConj Bu f) y := by
  rw [← lowerAdjointBifun_indicatorBifun]
  exact convexConj_imageBifun_eq_imageBifun A.indicatorBifun_ne_bot hf hex

/-- Under the hypotheses of `ConvexAnalysis.ConvexProcess.convexConj_imageBifun_indicatorBifun`, the
infimum that defines $((A^*)^{-1} f^*)(x^*)$ is attained: some $u^* \in V$ satisfies $f^*(u^*) +
\delta(x^* \mid (A^*)^{-1} u^*) = ((A^*)^{-1} f^*)(x^*)$. This is
`ConvexAnalysis.exists_convexConj_imageBifun_eq` read through the same identification. -/
theorem exists_imageBifun_indicatorBifun_adjointProcess_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) {f : U → EReal} (hf : ProperConvex f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    ∃ v : V, convexConj Bu f v + (adjointProcess Bu Bx A).inv.indicatorBifun v y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (convexConj Bu f) y := by
  obtain ⟨v, hv⟩ :=
      exists_convexConj_imageBifun_eq (Bu := Bu) (Bx := Bx) A.indicatorBifun_ne_bot hf hex
  refine ⟨v, ?_⟩
  rw [← convexConj_imageBifun_indicatorBifun Bu Bx A hf hex, ← hv,
      ← lowerAdjointBifun_indicatorBifun]
  rfl

end ConvexProcess

end ImageConj


/-! ### Bounded values force a linear transformation -/

section Linear

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : ConvexProcess U X}

namespace ConvexProcess

/-- Let $X$ be a real normed space. If $A0$ is bounded, then $A0 = \{0\}$, because $A0$ is a convex
cone that contains the origin. -/
theorem eval_zero_eq_zero_of_isBounded (A : ConvexProcess U X)
    (hb : Bornology.IsBounded (A.eval 0)) : A.eval 0 = {0} := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hR0 : (0 : ℝ) ≤ R := by simpa using hR _ A.zero_mem_eval_zero
  refine Set.Subset.antisymm (fun x hx => ?_) (by simpa using A.zero_mem_eval_zero)
  by_contra hx0
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hc0 : (0 : ℝ) ≤ (R + 1) / ‖x‖ := div_nonneg (by linarith) (norm_nonneg x)
  have hmem := A.smul_mem_eval_zero hc0 hx
  have hle := hR _ hmem
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, div_mul_cancel₀ _ (ne_of_gt hxn)] at hle
  linarith

/-- Let $X$ be a real normed space. If $\operatorname{dom} A = U$ and $A0$ is bounded, then every
value $Au$ is a single point. -/
theorem exists_eval_eq_singleton (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) (u : U) : ∃ x, A.eval u = {x} := by
  obtain ⟨x, hx⟩ : (A.eval u).Nonempty := by rw [← mem_dom, hdom]; trivial
  obtain ⟨y, hy⟩ : (A.eval (-u)).Nonempty := by rw [← mem_dom, hdom]; trivial
  refine ⟨x, Set.Subset.antisymm (fun z hz => ?_) (by simpa using hx)⟩
  have hzy : z + y ∈ A.eval 0 := by
    have h := add_mem_graph hz hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  have hxy : x + y ∈ A.eval 0 := by
    have h := add_mem_graph hx hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  rw [A.eval_zero_eq_zero_of_isBounded hb, Set.mem_singleton_iff] at hzy hxy
  exact Set.mem_singleton_iff.2 (add_right_cancel (hzy.trans hxy.symm))

/-- Let $U$ be a real vector space, $X$ a real normed space, and $A$ a convex process from $U$ to
$X$ with $\operatorname{dom} A = U$ and $A0$ bounded. Then there is a linear transformation
$T : U \to X$ with
$$Au = \{Tu\} \quad \text{for all } u \in U.$$
This is Theorem 39.1 of [rockafellar1970convex].

So the linear transformations are exactly the convex processes whose values are all nonempty and
bounded. The converse direction is `ConvexAnalysis.ConvexProcess.dom_ofLinearMap` together with
`ConvexAnalysis.ConvexProcess.eval_ofLinearMap`. -/
theorem exists_linearMap_of_isBounded (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : U →ₗ[ℝ] X, ∀ u, A.eval u = {T u} := by
  choose T hT using A.exists_eval_eq_singleton hdom hb
  have hmem : ∀ u, (u, T u) ∈ A.graph := by
    intro u
    have h : T u ∈ A.eval u := by rw [hT u]; exact Set.mem_singleton _
    exact h
  have hadd : ∀ u₁ u₂, T (u₁ + u₂) = T u₁ + T u₂ := by
    intro u₁ u₂
    have h := add_mem_graph (hmem u₁) (hmem u₂)
    rw [Prod.mk_add_mk] at h
    have h' : T u₁ + T u₂ ∈ A.eval (u₁ + u₂) := h
    rw [hT (u₁ + u₂), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hT0 : T 0 = 0 := by
    have h0 : (0 : X) ∈ A.eval 0 := A.zero_mem_eval_zero
    rw [hT 0, Set.mem_singleton_iff] at h0
    exact h0.symm
  have hneg : ∀ u, T (-u) = -T u := by
    intro u
    have h := hadd u (-u)
    rw [add_neg_cancel, hT0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hpos : ∀ c : ℝ, 0 < c → ∀ u, T (c • u) = c • T u := by
    intro c hc u
    have h := smul_mem_graph hc.le (hmem u)
    rw [Prod.smul_mk] at h
    have h' : c • T u ∈ A.eval (c • u) := h
    rw [hT (c • u), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hsmul : ∀ (c : ℝ) (u : U), T (c • u) = c • T u := by
    intro c u
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h1 : T ((-c) • u) = (-c) • T u := hpos _ (by linarith) u
      rw [neg_smul, hneg, neg_smul, neg_inj] at h1
      exact h1
    · simp [hT0]
    · exact hpos _ hc u
  exact ⟨{ toFun := T, map_add' := hadd, map_smul' := fun c u => hsmul c u }, hT⟩

end ConvexProcess

end Linear

/-! ### Closedness of the image -/

section Closedness

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {A : ConvexProcess U X} {C : Set U}

namespace ConvexProcess

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $A$ be a convex process from $U$
to $X$ with closed graph, and let $C \subseteq U$ be a nonempty closed convex set. Suppose that
every $v$ with $(v, 0) \in \operatorname{graph} A$ and $v \in 0^+ C$ is $0$. Then the image $AC$
is closed. In particular this holds when $C$ is bounded, because then $0^+ C = \{0\}$.

This is the recession-cone criterion for a linear image, applied to the projection
$(u, x) \mapsto x$. The set $AC$ is the image of $\operatorname{graph} A \cap (C \times X)$. The
recession cone of this set is $\operatorname{graph} A \cap (0^+ C \times X)$, because the graph
is its own recession cone, and its intersection with the kernel of the projection is
$\{(v, 0) \mid v \in A^{-1} 0 \cap 0^+ C\}$. No duality is needed. -/
theorem isClosed_image (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty)
    (h : ∀ v : U, (v, (0 : X)) ∈ A.graph → v ∈ recessionCone C → v = 0) :
    IsClosed (A.image C) := by
  have hSconv : Convex ℝ ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    Convex.inter (convex_graph A) (Convex.prod hC convex_univ)
  have hScl : IsClosed ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    hA.inter (hC'.prod isClosed_univ)
  rcases Set.eq_empty_or_nonempty ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) with hSe | hSne
  · have hempty : A.image C = ∅ := by rw [image_eq_image_snd, hSe, Set.image_empty]
    rw [hempty]
    exact isClosed_empty
  rw [image_eq_image_snd]
  refine isClosed_image_of_recessionCone_inter_ker _ hSconv hScl ?_
  rintro ⟨v, y⟩ ⟨hrec, hker⟩
  rw [recessionCone_inter (convex_graph A) hA (Convex.prod hC convex_univ)
    (hC'.prod isClosed_univ) hSne] at hrec
  obtain ⟨hg, hp⟩ := hrec
  rw [recessionCone_coe_pointedCone] at hg
  rw [recessionCone_prod hCne ⟨0, mem_univ 0⟩, recessionCone_univ] at hp
  have hy : y = 0 := by simpa using hker
  subst hy
  have hv : v = 0 := h v hg hp.1
  subst hv
  simp

/-- Let $U$ and $X$ be finite-dimensional real normed spaces. The image of a nonempty closed bounded
convex set under a convex process with closed graph is closed. This is the bounded case of
`ConvexAnalysis.ConvexProcess.isClosed_image`. -/
theorem isClosed_image_of_isBounded (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) := by
  refine isClosed_image hA hC hC' hCne fun v _ hv => ?_
  have h0 : recessionCone C = {0} := recessionCone_eq_zero_of_isBounded hCne hb
  rw [h0] at hv
  simpa using hv

end ConvexProcess

end Closedness

/-! ### The reflected process, and the dictionary between the two orientations -/

section Reflect

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

namespace ConvexProcess

/-- The **reflection** of a convex process $A$: the process whose graph is
$-\operatorname{graph} A$, the reflection of the graph of $A$ through the origin. Its values are
$u \mapsto -A(-u)$.

Reflection exchanges the two orientations. Reversing the inequality in the definition of the
adjoint is the same as reflecting the graph, so the adjoint of the reflection of $A$ is the
infimum-oriented adjoint of $A$ (`ConvexAnalysis.ConvexProcess.adjointProcess_reflect`). Read
the other way (`ConvexAnalysis.ConvexProcess.coadjointProcess_eq_reflect_adjointProcess`), this
puts the reflection on the conclusion, where `ConvexAnalysis.ConvexProcess.reflect_add` and
`ConvexAnalysis.ConvexProcess.reflect_comp` cancel it. So the infimum-oriented results carry the
hypotheses of the supremum-oriented ones unchanged. -/
def reflect (A : ConvexProcess U X) : ConvexProcess U X where
  graph :=
    { carrier := {p : U × X | -p ∈ A.graph}
      zero_mem' := by
        change -(0 : U × X) ∈ A.graph
        rw [_root_.neg_zero]
        exact A.graph.zero_mem
      add_mem' := by
        intro p q hp hq
        change -(p + q) ∈ A.graph
        rw [_root_.neg_add]
        exact A.graph.add_mem hp hq
      smul_mem' := by
        intro c p hp
        change -(c • p) ∈ A.graph
        rw [← smul_neg]
        exact Submodule.smul_mem A.graph c hp }

/-- $p$ lies in the graph of the reflection of $A$ if and only if $-p \in \operatorname{graph} A$.
-/
@[simp] theorem mem_graph_reflect {A : ConvexProcess U X} {p : U × X} :
    p ∈ A.reflect.graph ↔ -p ∈ A.graph := Iff.rfl

/-- Reflection is an involution on convex processes. -/
theorem reflect_involutive :
    Function.Involutive (reflect : ConvexProcess U X → ConvexProcess U X) := fun A => by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  rw [mem_graph_reflect, mem_graph_reflect, _root_.neg_neg]

/-- Reflecting twice gives the original process. -/
@[simp] theorem reflect_reflect (A : ConvexProcess U X) : A.reflect.reflect = A :=
  reflect_involutive A

/-- Reflection is injective on convex processes. -/
theorem reflect_injective :
    Function.Injective (reflect : ConvexProcess U X → ConvexProcess U X) :=
  reflect_involutive.injective

/-- The reflection of $A$ has the value $-A(-u)$ at $u$. -/
theorem eval_reflect (A : ConvexProcess U X) (u : U) : A.reflect.eval u = -(A.eval (-u)) := by
  ext x
  change -((u, x) : U × X) ∈ A.graph ↔ x ∈ -(A.eval (-u))
  rw [Set.mem_neg]
  exact Iff.rfl

/-- The reflection of $A_1 + A_2$ is the sum of the reflections of $A_1$ and $A_2$. -/
theorem reflect_add (A₁ A₂ : ConvexProcess U X) :
    (A₁ + A₂).reflect = A₁.reflect + A₂.reflect := by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  obtain ⟨u, x⟩ := p
  rw [← mem_eval, ← mem_eval, eval_reflect, eval_add, eval_add, eval_reflect, eval_reflect,
    _root_.neg_add]

/-- The reflection of $BA$ is the product of the reflections of $B$ and $A$, in the same order. -/
theorem reflect_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).reflect = B.reflect.comp A.reflect := by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  constructor
  · rintro ⟨x, h, k⟩
    exact ⟨-x, by simpa using h, by simpa using k⟩
  · rintro ⟨x, h, k⟩
    exact ⟨-x, by simpa using h, by simpa using k⟩

/-- Reflection, as an additive automorphism of the convex processes from $U$ to $X$.

Reflection is an involution (`ConvexAnalysis.ConvexProcess.reflect_involutive`) and is additive
(`ConvexAnalysis.ConvexProcess.reflect_add`), so injectivity and the other properties of a
bijection come from the bundled form. -/
def reflectAut : AddAut (ConvexProcess U X) where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_involutive
  right_inv := reflect_involutive
  map_add' := reflect_add

/-- The additive automorphism `ConvexAnalysis.ConvexProcess.reflectAut` sends $A$ to its reflection.
-/
@[simp] theorem reflectAut_apply (A : ConvexProcess U X) : reflectAut A = A.reflect := rfl

end ConvexProcess

end Reflect

section ReflectAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **Reversing the inequality is reflecting the graph**: the supremum-oriented adjoint of the
reflection of $A$ is the infimum-oriented adjoint of $A$. -/
theorem adjointProcess_reflect (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    adjointProcess Bu Bx A.reflect = coadjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  have hx : ∀ (p : U × X), Bx (-p).2 q.1 = -(Bx p.2 q.1) := fun p => by
    rw [Prod.snd_neg, map_neg Bx p.2, LinearMap.neg_apply]
  have hu : ∀ (p : U × X), Bu (-p).1 q.2 = -(Bu p.1 q.2) := fun p => by
    rw [Prod.fst_neg, map_neg Bu p.1, LinearMap.neg_apply]
  simp only [mem_graph_adjointProcess, mem_graph_coadjointProcess, mem_graph_reflect]
  constructor
  · intro h p hp
    have hpp := h (-p) (by rw [_root_.neg_neg]; exact hp)
    rw [hx p, hu p] at hpp
    linarith
  · intro h p hp
    have hpp := h (-p) hp
    rw [hx p, hu p] at hpp
    linarith

/-- The infimum-oriented adjoint of the reflection of $A$ is the supremum-oriented adjoint of $A$.
-/
theorem coadjointProcess_reflect (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    coadjointProcess Bu Bx A.reflect = adjointProcess Bu Bx A := by
  rw [← adjointProcess_reflect Bu Bx A.reflect, reflect_reflect]

/-- The infimum-oriented adjoint of $A$ is the reflection of the supremum-oriented adjoint of $A$.
Together with `ConvexAnalysis.ConvexProcess.adjointProcess_reflect`, this is the whole content
of the rule that the adjoint of an infimum-oriented process is defined in the same way with the
inequality reversed. -/
theorem coadjointProcess_eq_reflect_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    coadjointProcess Bu Bx A = (adjointProcess Bu Bx A).reflect := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  have hx : ∀ (p : U × X), Bx p.2 (-q).1 = -(Bx p.2 q.1) := fun p => by
    rw [Prod.fst_neg, map_neg (Bx p.2) q.1]
  have hu : ∀ (p : U × X), Bu p.1 (-q).2 = -(Bu p.1 q.2) := fun p => by
    rw [Prod.snd_neg, map_neg (Bu p.1) q.2]
  simp only [mem_graph_coadjointProcess, mem_graph_reflect, mem_graph_adjointProcess]
  constructor
  · intro h p hp
    rw [hx p, hu p]
    linarith [h p hp]
  · intro h p hp
    have hpp := h p hp
    rw [hx p, hu p] at hpp
    linarith

end ConvexProcess

end ReflectAdjoint

section ReflectTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

section ReflectClosed

variable [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X]
  [IsTopologicalAddGroup X]

/-- Let $U$ and $X$ be topological additive groups. If the graph of $A$ is closed, then the graph of
its reflection is closed, because it is the preimage of the graph under the homeomorphism
$p \mapsto -p$. -/
theorem isClosed_graph_reflect {A : ConvexProcess U X}
    (hA : IsClosed (A.graph : Set (U × X))) : IsClosed (A.reflect.graph : Set (U × X)) :=
  hA.preimage (continuous_neg (G := U × X))

end ReflectClosed

section CoadjointClosed

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y]

/-- **The adjoint of an infimum-oriented convex process is closed.** Let $V$ and $Y$ be topological
additive groups such that $\langle u, \cdot \rangle$ is continuous on $V$ for each $u \in U$ and
$\langle x, \cdot \rangle$ is continuous on $Y$ for each $x \in X$. Then the graph of the
infimum-oriented adjoint of $A$ is closed in $Y \times V$. -/
theorem isClosed_graph_coadjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] [IsContinuousPairing Bx.flip] (A : ConvexProcess U X) :
    IsClosed ((coadjointProcess Bu Bx A).graph : Set (Y × V)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess]
  exact isClosed_graph_reflect (isClosed_graph_adjointProcess Bu Bx A)

end CoadjointClosed

section Bipolar

variable [TopologicalSpace U] [TopologicalSpace X] [IsTopologicalAddGroup U]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ U] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ U]
  [LocallyConvexSpace ℝ X]

/-- Let $U$ and $X$ be locally convex topological vector spaces whose continuous linear functionals
are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$ and $\langle \cdot, x^* \rangle$ for
$x^* \in Y$. Then the supremum-oriented adjoint of the infimum-oriented adjoint of $A$ has the
graph $\operatorname{cl}(\operatorname{graph} A)$.

This is `ConvexAnalysis.ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure` read
through `ConvexAnalysis.ConvexProcess.adjointProcess_reflect`: the two sign changes still
cancel. It makes the closed halves of the sum and product theorems corollaries of their other
halves. -/
theorem graph_adjointProcess_coadjointProcess_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    ((adjointProcess Bx.flip Bu.flip (coadjointProcess Bu Bx A)).graph : Set (U × X))
      = closure (A.graph : Set (U × X)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess, adjointProcess_reflect]
  exact graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A

/-- **A convex process is closed exactly when the supremum-oriented adjoint of its infimum-oriented
adjoint is itself.** Let $U$ and $X$ be locally convex topological vector spaces whose
continuous linear functionals are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$ and
$\langle \cdot, x^* \rangle$ for $x^* \in Y$. Then this second adjoint equals $A$ if and only if
the graph of $A$ is closed. -/
theorem adjointProcess_coadjointProcess_eq_self_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    adjointProcess Bx.flip Bu.flip (coadjointProcess Bu Bx A) = A ↔
      IsClosed (A.graph : Set (U × X)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess, adjointProcess_reflect]
  exact coadjointProcess_adjointProcess_eq_self_iff Bu Bx A

end Bipolar

end ConvexProcess

end ReflectTopology

/-! ### Sums and products for infimum-oriented processes -/

section MirrorAlgebra

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]

namespace ConvexProcess

/-- **The adjoint of a sum, for two infimum-oriented processes.** Under the hypothesis of
`ConvexAnalysis.ConvexProcess.adjointProcess_add`, the infimum-oriented adjoints satisfy
$$(A_1 + A_2)^* = A_1^* + A_2^*.$$

Rockafellar states the result for two processes "with the same orientation" and leaves the
infimum-oriented case implicit. It is the supremum-oriented theorem read through
`ConvexAnalysis.ConvexProcess.coadjointProcess_eq_reflect_adjointProcess`, because reflection
distributes over sums. The hypothesis is the same as in
`ConvexAnalysis.ConvexProcess.adjointProcess_add`. -/
theorem coadjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A₁ A₂ : ConvexProcess U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(supportFn Bx (A₁.eval u) y))
      (fun u => -(supportFn Bx (A₂.eval u) y))) :
    coadjointProcess Bu Bx (A₁ + A₂)
      = coadjointProcess Bu Bx A₁ + coadjointProcess Bu Bx A₂ := by
  rw [coadjointProcess_eq_reflect_adjointProcess Bu Bx (A₁ + A₂),
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A₁,
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A₂,
    adjointProcess_add Bu Bx A₁ A₂ hex, reflect_add]

/-- **The adjoint of a product, for two infimum-oriented processes.** Under the hypothesis of
`ConvexAnalysis.ConvexProcess.adjointProcess_comp`, the infimum-oriented adjoints satisfy
$$(BA)^* = A^* B^*.$$

As in `ConvexAnalysis.ConvexProcess.coadjointProcess_add`, the proof reflects the adjoints and
not the processes, so the hypothesis is the same as in
`ConvexAnalysis.ConvexProcess.adjointProcess_comp`. `ConvexAnalysis.ConvexProcess.reflect_comp`
makes the product come out in the same order. -/
theorem coadjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z)
    (hex : ∀ (w : W) (v : V), IsExactSum Bx
      (fun x => ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal)))) :
    coadjointProcess Bu Bz (B.comp A)
      = (coadjointProcess Bu Bx A).comp (coadjointProcess Bx Bz B) := by
  rw [coadjointProcess_eq_reflect_adjointProcess Bu Bz (B.comp A),
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A,
    coadjointProcess_eq_reflect_adjointProcess Bx Bz B,
    adjointProcess_comp Bu Bx Bz A B hex, reflect_comp]

end ConvexProcess

end MirrorAlgebra

/-! ### The closed halves of the sum and product theorems -/

section ClosedHalves

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]

namespace ConvexProcess

/-- Let $U$ and $X$ be locally convex topological vector spaces whose continuous linear functionals
are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$ and $\langle \cdot, x^* \rangle$ for
$x^* \in Y$, and let $A_1$ and $A_2$ be convex processes with closed graphs. Suppose that for
every $u \in U$ the functions $x^* \mapsto -\sup \{\langle u, u^* \rangle \mid u^* \in A_i^*
x^*\}$, for $i = 1, 2$, add exactly (`ConvexAnalysis.IsExactSum`). Then $A_1 + A_2$ is the
infimum-oriented adjoint of $A_1^* + A_2^*$.

Both closed-half results about sums follow from this identity. -/
theorem add_eq_coadjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    A₁ + A₂ = coadjointProcess Bx.flip Bu.flip
      (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂) := by
  rw [coadjointProcess_add Bx.flip Bu.flip _ _ hex,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A₁).2 hA₁,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A₂).2 hA₂]

/-- **The sum of two closed convex processes is closed.** Under the hypotheses of
`ConvexAnalysis.ConvexProcess.add_eq_coadjointProcess_add`, the graph of $A_1 + A_2$ is closed.
The sum is an adjoint, and an adjoint is always closed. -/
theorem isClosed_graph_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    IsClosed (((A₁ + A₂).graph : Set (U × X))) := by
  rw [add_eq_coadjointProcess_add Bu Bx hA₁ hA₂ hex]
  exact isClosed_graph_coadjointProcess Bx.flip Bu.flip _

end ConvexProcess

end ClosedHalves

section ClosedHalvesAdjoint

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

namespace ConvexProcess

/-- $(A_1 + A_2)^*$ is the closure of $A_1^* + A_2^*$. Let $U$, $X$, $V$ and $Y$ be locally convex
topological vector spaces such that the continuous linear functionals on each of them are
exactly the pairings with its partner space, and let $A_1$ and $A_2$ be convex processes with
closed graphs. Suppose that for every $u \in U$ the functions $x^* \mapsto -\sup \{\langle u,
u^* \rangle \mid u^* \in A_i^* x^*\}$, for $i = 1, 2$, add exactly
(`ConvexAnalysis.IsExactSum`). Then
$$\operatorname{graph}(A_1 + A_2)^* = \operatorname{cl} \operatorname{graph}(A_1^* + A_2^*).$$
-/
theorem graph_adjointProcess_add_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] [IsCompatiblePairing Bu.flip]
    [IsCompatiblePairing Bx.flip] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    ((adjointProcess Bu Bx (A₁ + A₂)).graph : Set (Y × V))
      = closure (((adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂).graph : Set (Y × V))) := by
  have h := graph_adjointProcess_coadjointProcess_eq_closure Bx.flip Bu.flip
    (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂)
  simp only [LinearMap.flip_flip] at h
  rw [add_eq_coadjointProcess_add Bu Bx hA₁ hA₂ hex, h]

end ConvexProcess

end ClosedHalvesAdjoint

section ClosedHalvesComp

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]

namespace ConvexProcess

/-- Let $U$, $X$ and $Z$ be locally convex topological vector spaces whose continuous linear
functionals are exactly the pairings with $V$, $Y$ and $W$, and let $A$ from $U$ to $X$ and $B$
from $X$ to $Z$ be convex processes with closed graphs. Suppose that for every $u \in U$ and
$z \in Z$ the functions
$$x^* \mapsto \inf \{\langle z, z^* \rangle \mid z^* \in (B^*)^{-1} x^*\} \quad\text{and}\quad
  x^* \mapsto -\sup \{\langle u, u^* \rangle \mid u^* \in A^* x^*\}$$
add exactly (`ConvexAnalysis.IsExactSum`). Then $BA$ is the infimum-oriented adjoint of
$A^* B^*$.

Both closed-half results about products follow from this identity. -/
theorem comp_eq_coadjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    B.comp A = coadjointProcess Bz.flip Bu.flip
      ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B)) := by
  rw [coadjointProcess_comp Bz.flip Bx.flip Bu.flip _ _ hex,
    (coadjointProcess_adjointProcess_eq_self_iff Bx Bz B).2 hB,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A).2 hA]

/-- **The product of two closed convex processes is closed.** Under the hypotheses of
`ConvexAnalysis.ConvexProcess.comp_eq_coadjointProcess_comp`, the graph of $BA$ is closed. -/
theorem isClosed_graph_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    IsClosed (((B.comp A).graph : Set (U × Z))) := by
  rw [comp_eq_coadjointProcess_comp Bu Bx Bz hA hB hex]
  exact isClosed_graph_coadjointProcess Bz.flip Bu.flip _

end ConvexProcess

end ClosedHalvesComp

section ClosedHalvesCompAdjoint

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

namespace ConvexProcess

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- $(BA)^*$ is the closure of $A^* B^*$. Let $U$, $X$, $Z$, $V$ and $W$ be locally convex
topological vector spaces. Suppose that the continuous linear functionals on $U$, $X$ and $Z$
are exactly the pairings with $V$, $Y$ and $W$, and those on $V$ and $W$ are exactly the
pairings with $U$ and $Z$. Let $A$ from $U$ to $X$ and $B$ from $X$ to $Z$ be convex processes
with closed graphs, under the exactness hypothesis of
`ConvexAnalysis.ConvexProcess.comp_eq_coadjointProcess_comp`. Then
$$\operatorname{graph}(BA)^* = \operatorname{cl} \operatorname{graph}(A^* B^*).$$
-/
theorem graph_adjointProcess_comp_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] [IsCompatiblePairing Bu.flip] [IsCompatiblePairing Bz.flip]
    {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    ((adjointProcess Bu Bz (B.comp A)).graph : Set (W × V))
      = closure ((((adjointProcess Bu Bx A).comp
          (adjointProcess Bx Bz B)).graph : Set (W × V))) := by
  have h := graph_adjointProcess_coadjointProcess_eq_closure Bz.flip Bu.flip
    ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B))
  simp only [LinearMap.flip_flip] at h
  rw [comp_eq_coadjointProcess_comp Bu Bx Bz hA hB hex, h]

end ConvexProcess

end ClosedHalvesCompAdjoint

/-!
### The two inner products for infimum-oriented processes

For an infimum-oriented process the indicator bifunction is the concave function
$-\delta(\cdot \mid Au)$, and the inner product $\langle Au, x^* \rangle$ is its concave conjugate:
an infimum over $Au$ instead of a supremum. As with the two adjoints, the two orientations are
separate definitions and not two branches of one flag. All results below follow from the single sign
identity `ConvexAnalysis.ConvexProcess.coBracket_eq_neg_bracket`.
-/

section CoBracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The inner product of an **infimum-oriented** convex process:
$$\langle Au, x^* \rangle = \inf \{\langle x, x^* \rangle \mid x \in Au\}.$$

This is the concave conjugate of the concave indicator $-\delta(\cdot \mid Au)$, in the same way
as the bracket of `ConvexAnalysis.ConvexProcess.indicatorBifun` is the convex conjugate of
$\delta(\cdot \mid Au)$. -/
noncomputable def coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    EReal :=
  ⨅ x ∈ A.eval u, ((Bx x y : ℝ) : EReal)

/-- The first of the two extremum problems, in infimum-oriented form: $\langle Au, x^* \rangle =
\inf \{\langle x, x^* \rangle \mid x \in Au\}$. -/
theorem coBracket_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    coBracket Bx A u y = ⨅ x ∈ A.eval u, ((Bx x y : ℝ) : EReal) := rfl

/-- The sign identity between the two orientations: the infimum-oriented inner product is minus the
supremum-oriented one at the reflected dual vector,
$$\inf \{\langle x, x^* \rangle \mid x \in Au\} = -\sup \{\langle x, -x^* \rangle \mid x \in
  Au\}.$$
Only the dual variable is reflected. The primal variable $u$ is unchanged, because reversing the
orientation of a process does not reverse its argument. -/
theorem coBracket_eq_neg_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : coBracket Bx A u y = -(bracket Bx A.indicatorBifun u (-y)) := by
  rw [coBracket_apply, bracket_indicatorBifun_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [← EReal.coe_neg, map_neg (Bx x) y, _root_.neg_neg]

/-- `ConvexAnalysis.ConvexProcess.coBracket_eq_neg_bracket` as an equation of functions of $u$: for
fixed $x^*$, the infimum-oriented inner product $u \mapsto \langle Au, x^* \rangle$ is the
negative of $u \mapsto \sup \{\langle x, -x^* \rangle \mid x \in Au\}$. -/
theorem coBracket_eq_neg_bracket_fun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    (fun u => coBracket Bx A u y) = fun u => -(bracket Bx A.indicatorBifun u (-y)) :=
  funext fun u => coBracket_eq_neg_bracket Bx A u y

/-- The infimum-oriented inner product is minus a support function at the reflected dual vector:
$\inf \{\langle x, x^* \rangle \mid x \in Au\} = -\delta^*(-x^* \mid Au)$. -/
theorem coBracket_eq_neg_supportFn (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : coBracket Bx A u y = -(supportFn Bx (A.eval u) (-y)) := by
  rw [coBracket_eq_neg_bracket, bracket_indicatorBifun]

/-- The negative of the infimum-oriented inner product $x^* \mapsto \langle Au, x^* \rangle$ is the
supremum-oriented inner product composed with the linear reflection $x^* \mapsto -x^*$. In this
form the sign identity feeds the convexity and closedness results for a composition with a
linear map. -/
theorem neg_coBracket_eq_compLin (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    (fun y => -(coBracket Bx A u y))
      = compLin (bracket Bx A.indicatorBifun u) (-LinearMap.id : Y →ₗ[ℝ] Y) := by
  funext y
  rw [coBracket_eq_neg_bracket, _root_.neg_neg]
  simp only [compLin, Function.comp_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq]

/-- For an infimum-oriented process, the function $x^* \mapsto \langle Au, x^* \rangle$ is
positively homogeneous. -/
theorem posHomogeneous_coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    PosHomogeneous (coBracket Bx A u) := by
  intro a ha y
  rw [coBracket_eq_neg_bracket, coBracket_eq_neg_bracket, ← smul_neg,
    posHomogeneous_bracket_indicatorBifun Bx A u a ha (-y), ← _root_.mul_neg]

/-- For an infimum-oriented process, the function $x^* \mapsto \langle Au, x^* \rangle$ is concave,
because it is a concave conjugate. -/
theorem concaveFn_coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    ConcaveFn (coBracket Bx A u) := by
  rw [concaveFn_iff_convexFn_neg, neg_coBracket_eq_compLin]
  exact convexFn_compLin _ (convexFn_bracket_indicatorBifun Bx A u)

/-- For an infimum-oriented process, the function $u \mapsto \langle Au, x^* \rangle$ is positively
homogeneous. -/
theorem posHomogeneous_coBracket_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    PosHomogeneous fun u => coBracket Bx A u y := by
  intro a ha u
  change coBracket Bx A (a • u) y = (a : EReal) * coBracket Bx A u y
  rw [coBracket_eq_neg_bracket, coBracket_eq_neg_bracket, _root_.mul_neg]
  exact congrArg Neg.neg (posHomogeneous_bracket_indicatorBifun_arg Bx A (-y) a ha u)

/-- For an infimum-oriented process, the function $u \mapsto \langle Au, x^* \rangle$ is convex; in
the supremum-oriented case it is concave. Reversing the orientation of a process exchanges
convexity and concavity in both variables at once. -/
theorem convexFn_coBracket_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    ConvexFn fun u => coBracket Bx A u y := by
  rw [coBracket_eq_neg_bracket_fun]
  exact concaveFn_iff_convexFn_neg.1 (concaveFn_bracket_indicatorBifun Bx A (-y))

/-- For an infimum-oriented process, $\langle A0, 0 \rangle = 0$. -/
@[simp] theorem coBracket_zero_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    coBracket Bx A 0 (0 : Y) = 0 := by
  rw [coBracket_eq_neg_bracket, _root_.neg_zero, bracket_indicatorBifun_zero_zero,
    _root_.neg_zero]

end ConvexProcess

end CoBracket

section CoBracketClosed

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsContinuousPairing Bx.flip]

namespace ConvexProcess

/-- Let $Y$ be a topological additive group such that $\langle x, \cdot \rangle$ is continuous on
$Y$ for each $x \in X$. For an infimum-oriented process, the function
$x^* \mapsto \langle Au, x^* \rangle$ is a closed concave function, because the reflection
$x^* \mapsto -x^*$ is a homeomorphism. -/
theorem closedConcave_coBracket (A : ConvexProcess U X) (u : U) :
    ClosedConcave (coBracket Bx A u) := by
  rw [closedConcave_iff_closedConvex_neg, neg_coBracket_eq_compLin]
  exact closedConvex_compLin (closedConvex_bracket_indicatorBifun A u) (continuous_neg (G := Y))

end ConvexProcess

end CoBracketClosed

section CoBracketAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The second of the two extremum problems, in infimum-oriented form: with $A^*$ the
infimum-oriented adjoint,
$$\sup \{\langle u, u^* \rangle \mid u^* \in A^* x^*\} = -\langle u, F^*(-x^*) \rangle,$$
where the right side is minus the concave bracket of the adjoint $F^*$ of the indicator
bifunction $F$ of $A$ at $(u, -x^*)$. The values of the infimum-oriented adjoint are the
reflections of the values of the supremum-oriented one. -/
theorem iSup_coadjointProcess_eq_neg_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    ⨆ v ∈ (coadjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)
      = -(concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) u (-y)) := by
  rw [concaveBracket_convexAdjointBifun_indicatorBifun, coadjointProcess_eq_reflect_adjointProcess,
    eval_reflect, ← Set.image_neg_eq_neg, iSup_image, EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [EReal.neg_iInf]
  refine iSup_congr fun _ => ?_
  rw [map_neg (Bu u) v, EReal.coe_neg]

end ConvexProcess

end CoBracketAdjoint

section CoBracketClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- $\langle u, A^* x^* \rangle = \operatorname{cl}_u \langle Au, x^* \rangle$, in infimum-oriented
form. Let $U$ be a locally convex topological vector space whose continuous linear functionals
are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$, and let $A^*$ be the infimum-oriented
adjoint. Then for each $x^* \in Y$ the function $u \mapsto \sup \{\langle u, u^* \rangle \mid
u^* \in A^* x^*\}$ is the closure of the convex function $u \mapsto \inf \{\langle x, x^*
\rangle \mid x \in Au\}$.

The closure is the convex closure `ConvexAnalysis.convexCl`, because $u \mapsto \inf \{\langle
x, x^* \rangle \mid x \in Au\}$ is convex and not concave
(`ConvexAnalysis.ConvexProcess.convexFn_coBracket_arg`). In the supremum-oriented statement
`ConvexAnalysis.ConvexProcess.concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁` it
is the concave closure. As there, closedness of $A$ plays no part. -/
theorem iSup_coadjointProcess_eq_convexCl (A : ConvexProcess U X) (y : Y) :
    (fun u => ⨆ v ∈ (coadjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal))
      = fun u => convexCl (fun u' => coBracket Bx A u' y) u := by
  funext u
  have h := congrFun (concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁
    (Bu := Bu) (Bx := Bx) A (-y)) u
  simp only [partialCl₁_apply, concaveCl_apply] at h
  rw [iSup_coadjointProcess_eq_neg_concaveBracket Bu Bx, h, coBracket_eq_neg_bracket_fun,
    _root_.neg_neg]

end ConvexProcess

end CoBracketClosure

end ConvexAnalysis
