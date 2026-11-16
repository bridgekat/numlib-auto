/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Existence

/-!
# Monotonicity of the subdifferential

Let $B$ be a pairing of real vector spaces $E$ and $F$, written $\langle x, y \rangle$. The
subdifferential of a proper convex function $f \colon E \to [-\infty, +\infty]$ is **monotone**:
$\langle x_1 - x_2, y_1 - y_2 \rangle \ge 0$ whenever $y_i \in \partial f(x_i)$. It is even
**cyclically monotone**: every finite cycle $(x_0, y_0), \dots, (x_m, y_m)$ in its graph satisfies
$$\langle x_1 - x_0, y_0 \rangle + \langle x_2 - x_1, y_1 \rangle + \dots + \langle x_0 - x_m, y_m
  \rangle \le 0.$$
Conversely, a nonempty cyclically monotone multivalued mapping is contained in the subdifferential
of a closed proper convex function. This function is the supremum of the telescoping sums above,
read as affine functions of a free endpoint. A closed proper convex function is determined by its
subdifferential up to an additive constant, so on a finite-dimensional space the maximal cyclically
monotone mappings are exactly the subdifferentials of the closed proper convex functions. This is a
different condition from maximal monotonicity. The characterization is due to Rockafellar (Pacific
J. Math. 17 (1966), 497–510), and the presentation follows [rockafellar1970convex], §24.

## Main definitions

* `ConvexAnalysis.IsMonotoneRel`, `ConvexAnalysis.IsCyclicallyMonotone`: monotone and cyclically
  monotone multivalued mappings.
* `ConvexAnalysis.IsMaximalMonotoneRel`, `ConvexAnalysis.IsMaximalCyclicallyMonotone`: maximal
  monotone and maximal cyclically monotone multivalued mappings.
* `ConvexAnalysis.cyclicPotential`: the convex function reconstructed from a cyclically monotone
  mapping.

## Main results

* `ConvexAnalysis.isCyclicallyMonotone_iff_exists_convexFn`: a nonempty mapping is cyclically
  monotone if and only if it is contained in the subdifferential of a closed proper convex function.
* `ConvexAnalysis.isClosed_subgradientRel`: the graph of $\partial f$ is closed.
* `ConvexAnalysis.eq_add_coe_of_subgradientRel_subset`: if $\partial f \subseteq \partial g$ for
  closed proper convex $f$ and $g$, then $g = f + \alpha$ for a real constant $\alpha$.
* `ConvexAnalysis.isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn`: the maximal
  cyclically monotone mappings are exactly the subdifferentials of the closed proper convex
  functions.

## Notation

* `ConvexAnalysis.chainVal B s l x`: the telescoping sum $\langle x_1 - x_0, y_0 \rangle + \dots +
  \langle x - x_m, y_m \rangle$ along the chain that starts at $s = (x_0, y_0)$, runs through
  $l = [(x_1, y_1), \dots, (x_m, y_m)]$ and ends at $x$.

## Implementation notes

* A cycle is a `List (E × F)` with the starting pair given separately, so that every proof is an
  induction on a list. `ConvexAnalysis.chainVal` has the free endpoint last. Then
  `ConvexAnalysis.cyclicPotential` is a supremum of affine functions of $x$, and the cycle condition
  is `chainVal B s l s.1 ≤ 0`.
* The closedness of the graph needs joint continuity of the pairing,
  `Continuous fun p : E × F => B p.1 p.2`. Continuity of $\langle \cdot, y \rangle$ for each fixed
  $y$ is not enough to pass to the limit in $\langle z - x_i, y_i \rangle$ when both arguments move.
  In $\mathbb{R}^n$ the hypothesis holds automatically.
* The uniqueness up to a constant is proved by subdivision of segments, not by integration of
  one-sided derivatives.
* Maximal monotonicity of $\partial f$ for a closed proper convex $f$ is
  `ConvexAnalysis.isMaximalMonotoneRel_subgradientRel` in `Numlib.Analysis.Convex.Extremum.Prox`.
  Its proof uses Moreau's theorem, and that module imports this one.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### Chains and cyclic monotonicity -/

section Chain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **telescoping sum** along a finite chain in $E \times F$. The chain starts at the pair
$s = (x_0, y_0)$, runs through $l = [(x_1, y_1), \dots, (x_m, y_m)]$ and ends at the free point
$x \in E$:
$$\operatorname{chainVal}(s, l, x) = \langle x_1 - x_0, y_0 \rangle + \langle x_2 - x_1, y_1
  \rangle + \dots + \langle x - x_m, y_m \rangle.$$
For $x = x_0$ the chain is a closed cycle. -/
def chainVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : E × F → List (E × F) → E → ℝ
  | s, [], x => B (x - s.1) s.2
  | s, q :: l, x => B (q.1 - s.1) s.2 + chainVal B q l x

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- The telescoping sum of the chain with no further pairs is $\langle x - x_0, y_0 \rangle$. -/
@[simp] theorem chainVal_nil (s : E × F) (x : E) : chainVal B s [] x = B (x - s.1) s.2 := rfl

/-- The telescoping sum of the chain $s, q, l$ ending at $x$ is $\langle q_1 - s_1, s_2 \rangle$
plus the telescoping sum of the chain $q, l$ ending at $x$. -/
@[simp] theorem chainVal_cons (s q : E × F) (l : List (E × F)) (x : E) :
    chainVal B s (q :: l) x = B (q.1 - s.1) s.2 + chainVal B q l x := rfl

/-- Appending one pair $q = (q_1, q_2)$ to a chain: the telescoping sum along $l$ followed by $q$,
ending at $z$, is the telescoping sum along $l$ ending at $q_1$, plus
$\langle z - q_1, q_2 \rangle$. -/
theorem chainVal_append_singleton (s q : E × F) (l : List (E × F)) (z : E) :
    chainVal B s (l ++ [q]) z = chainVal B s l q.1 + B (z - q.1) q.2 := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [List.cons_append, chainVal_cons, ih]; ring

/-- A telescoping sum is affine in its free endpoint: for each chain there are $y \in F$ and
$c \in \mathbb{R}$ with $\operatorname{chainVal}(s, l, x) = \langle x, y \rangle - c$ for every
$x$. -/
theorem exists_chainVal_eq (l : List (E × F)) (s : E × F) :
    ∃ (y : F) (c : ℝ), ∀ x, chainVal B s l x = B x y - c := by
  induction l generalizing s with
  | nil =>
    refine ⟨s.2, B s.1 s.2, fun x => ?_⟩
    rw [chainVal_nil, map_sub, LinearMap.sub_apply]
  | cons q l ih =>
    obtain ⟨y, c, h⟩ := ih q
    refine ⟨y, c - B (q.1 - s.1) s.2, fun x => ?_⟩
    rw [chainVal_cons, h x]
    ring

end Chain

/-! ### Monotone and cyclically monotone multivalued mappings -/

section Monotone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ σ : SetRel E F}

/-- A multivalued mapping $\rho \subseteq E \times F$ is **monotone** if
$$\langle x_1 - x_2, y_1 - y_2 \rangle \ge 0 \qquad \text{for all } (x_1, y_1), (x_2, y_2) \in
  \rho.$$
-/
def IsMonotoneRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ p ∈ ρ, ∀ q ∈ ρ, 0 ≤ B (p.1 - q.1) (p.2 - q.2)

/-- A multivalued mapping $\rho \subseteq E \times F$ is **cyclically monotone** if every finite
cycle in $\rho$ has a telescoping sum that is at most $0$: for all
$(x_0, y_0), \dots, (x_m, y_m) \in \rho$,
$$\langle x_1 - x_0, y_0 \rangle + \langle x_2 - x_1, y_1 \rangle + \dots + \langle x_0 - x_m,
  y_m \rangle \le 0.$$

The cycle is a starting pair $s \in \rho$ and a list $l$ of pairs in $\rho$, and its sum is
`ConvexAnalysis.chainVal B s l s.1`. -/
def IsCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ s ∈ ρ, ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → chainVal B s l s.1 ≤ 0

/-- A multivalued mapping $\rho$ is **maximal monotone** if it is monotone and every monotone
mapping $\sigma \supseteq \rho$ is equal to $\rho$. -/
def IsMaximalMonotoneRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  IsMonotoneRel B ρ ∧ ∀ σ : SetRel E F, IsMonotoneRel B σ → ρ ⊆ σ → σ ⊆ ρ

/-- A multivalued mapping $\rho$ is **maximal cyclically monotone** if it is cyclically monotone and
every cyclically monotone mapping $\sigma \supseteq \rho$ is equal to $\rho$. On a
finite-dimensional space these are exactly the subdifferentials of the closed proper convex
functions (`ConvexAnalysis.isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn`). -/
def IsMaximalCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  IsCyclicallyMonotone B ρ ∧ ∀ σ : SetRel E F, IsCyclicallyMonotone B σ → ρ ⊆ σ → σ ⊆ ρ

/-- A subset of a monotone mapping is monotone. -/
theorem IsMonotoneRel.mono (h : IsMonotoneRel B σ) (hsub : ρ ⊆ σ) : IsMonotoneRel B ρ :=
  fun p hp q hq => h p (hsub hp) q (hsub hq)

/-- A subset of a cyclically monotone mapping is cyclically monotone. -/
theorem IsCyclicallyMonotone.mono (h : IsCyclicallyMonotone B σ) (hsub : ρ ⊆ σ) :
    IsCyclicallyMonotone B ρ :=
  fun s hs l hl => h s (hsub hs) l fun q hq => hsub (hl q hq)

/-- A cyclically monotone mapping is monotone: the monotonicity inequality is the cycle condition
for a cycle of two pairs. -/
theorem IsCyclicallyMonotone.isMonotoneRel (h : IsCyclicallyMonotone B ρ) : IsMonotoneRel B ρ := by
  intro p hp q hq
  have hcyc := h p hp [q] (by simpa using hq)
  rw [chainVal_cons, chainVal_nil] at hcyc
  have hexp : B (p.1 - q.1) (p.2 - q.2) = -(B (q.1 - p.1) p.2 + B (p.1 - q.1) q.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp]
  linarith

/-- A mapping with one pair is cyclically monotone: every cycle in it has all its terms equal to
$0$. -/
theorem isCyclicallyMonotone_singleton (p : E × F) : IsCyclicallyMonotone B {p} := by
  have key : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ({p} : Set (E × F))) → chainVal B p l p.1 = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons q l ih =>
      intro hl
      have hq : q = p := hl q (by simp)
      subst hq
      rw [chainVal_cons, ih fun r hr => hl r (by simp [hr])]
      simp
  intro s hs l hl
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact le_of_eq (key l hl)

/-- A maximal cyclically monotone mapping is nonempty, because the empty mapping is strictly
contained in the cyclically monotone mapping $\{(0, 0)\}$. -/
theorem IsMaximalCyclicallyMonotone.nonempty (h : IsMaximalCyclicallyMonotone B ρ) :
    ρ.Nonempty := by
  rcases ρ.eq_empty_or_nonempty with hem | hne
  · have hsub := h.2 {((0 : E), (0 : F))} (isCyclicallyMonotone_singleton _)
      (by rw [hem]; exact Set.empty_subset _)
    rw [hem] at hsub
    exact absurd (hsub rfl) (Set.notMem_empty _)
  · exact hne

end Monotone

/-! ### The subdifferential is cyclically monotone -/

section Necessity

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The telescoping estimate. Let $s = (x_0, y_0)$ and all pairs of the list $l$ be in the graph of
$\partial f$. Then for every $x \in E$,
$$f(x_0) + \operatorname{chainVal}(s, l, x) \le f(x).$$
It is the sum of the inequalities $\langle x_{i+1} - x_i, y_i \rangle \le f(x_{i+1}) - f(x_i)$. -/
theorem le_of_chain_mem_subgradientRel :
    ∀ (l : List (E × F)) (s : E × F), s ∈ subgradientRel B f →
      (∀ q ∈ l, q ∈ subgradientRel B f) →
        ∀ x, f s.1 + ((chainVal B s l x : ℝ) : EReal) ≤ f x := by
  intro l
  induction l with
  | nil => intro s hs _ x; simpa using hs x
  | cons q l ih =>
    intro s hs hl x
    have h₁ : f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) ≤ f q.1 := hs q.1
    have h₂ : f q.1 + ((chainVal B q l x : ℝ) : EReal) ≤ f x :=
      ih q (hl q (by simp)) (fun r hr => hl r (by simp [hr])) x
    calc f s.1 + ((chainVal B s (q :: l) x : ℝ) : EReal)
        = f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) + ((chainVal B q l x : ℝ) : EReal) := by
          rw [chainVal_cons, EReal.coe_add, add_assoc]
      _ ≤ f q.1 + ((chainVal B q l x : ℝ) : EReal) := add_le_add h₁ (le_refl _)
      _ ≤ f x := h₂

/-- If $f \colon E \to [-\infty, +\infty]$ is proper, then the graph of $\partial f$ is cyclically
monotone. Convexity is not used. Properness is used only to know that $f$ is finite at the
starting point of the cycle. -/
theorem isCyclicallyMonotone_subgradientRel (hp : ProperConvex f) :
    IsCyclicallyMonotone B (subgradientRel B f) := by
  intro s hs l hl
  have hkey := le_of_chain_mem_subgradientRel l s hs hl s.1
  have hdom : s.1 ∈ convexDom f := by
    by_contra hcon
    have hmem : s.2 ∈ subdifferential B f s.1 := hs
    rw [subdifferential_eq_empty_of_notMem_convexDom hp hcon] at hmem
    exact hmem
  have hcoe : (((f s.1).toReal : ℝ) : EReal) = f s.1 :=
    EReal.coe_toReal (ne_of_lt hdom) (hp.ne_bot s.1)
  rw [← hcoe, ← EReal.coe_add, EReal.coe_le_coe_iff] at hkey
  linarith

/-- If $f \colon E \to [-\infty, +\infty]$ is proper, then $\partial f$ is monotone:
$\langle x_1 - x_2, y_1 - y_2 \rangle \ge 0$ whenever $y_1 \in \partial f(x_1)$ and
$y_2 \in \partial f(x_2)$. -/
theorem isMonotoneRel_subgradientRel (hp : ProperConvex f) :
    IsMonotoneRel B (subgradientRel B f) :=
  (isCyclicallyMonotone_subgradientRel hp).isMonotoneRel

end Necessity

/-! ### A potential for a cyclically monotone mapping -/

section Potential

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ : SetRel E F} {s : E × F}

/-- The **potential** of a multivalued mapping $\rho \subseteq E \times F$ with the base pair $s$:
the supremum, over all finite lists $l$ of pairs in $\rho$, of the telescoping sums of the
chains that start at $s$, run through $l$ and end at $x$,
$$x \mapsto \sup_l \operatorname{chainVal}(s, l, x).$$

As a supremum of affine functions of $x$, it is a closed convex function. If $\rho$ is
cyclically monotone and $s \in \rho$, the potential is $0$ at the first component of $s$, so it
is proper. -/
noncomputable def cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F)
    (x : E) : EReal :=
  ⨆ l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}, ((chainVal B s l x : ℝ) : EReal)

/-- The telescoping sum of every chain in $\rho$ that starts at $s$ and ends at $x$ is at most the
potential at $x$. -/
theorem le_cyclicPotential {l : List (E × F)} (hl : ∀ q ∈ l, q ∈ ρ) (s : E × F) (x : E) :
    ((chainVal B s l x : ℝ) : EReal) ≤ cyclicPotential B ρ s x :=
  le_iSup₂ (f := fun l (_ : l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}) =>
    ((chainVal B s l x : ℝ) : EReal)) l hl

/-- If the telescoping sum of every chain in $\rho$ that starts at $s$ and ends at $x$ is at most
$c$, then the potential at $x$ is at most $c$. -/
theorem cyclicPotential_le {c : EReal} {x : E}
    (h : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → ((chainVal B s l x : ℝ) : EReal) ≤ c) :
    cyclicPotential B ρ s x ≤ c :=
  iSup₂_le h

/-- The potential of a multivalued mapping is convex, because it is a supremum of affine functions.
-/
theorem convexFn_cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) :
    ConvexFn (cyclicPotential B ρ s) := by
  refine convexFn_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact convexFn_affineFn y c

/-- The potential never takes the value $-\infty$: the chain with no further pairs gives a real
lower bound. -/
theorem cyclicPotential_ne_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) (x : E) :
    cyclicPotential B ρ s x ≠ ⊥ := by
  intro h
  have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s x
  rw [h, le_bot_iff] at hle
  exact EReal.coe_ne_bot _ hle

/-- If $\rho$ is cyclically monotone and $s = (x_0, y_0) \in \rho$, then the potential with the base
pair $s$ is $0$ at $x_0$. Cyclic monotonicity is exactly the condition that makes the potential
finite at $x_0$. -/
theorem cyclicPotential_eq_zero (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    cyclicPotential B ρ s s.1 = 0 := by
  refine le_antisymm (cyclicPotential_le fun l hl => ?_) ?_
  · exact_mod_cast hρ s hs l hl
  · have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s s.1
    simpa using hle

/-- If $\rho$ is cyclically monotone and $s \in \rho$, then the potential with the base pair $s$ is
proper. -/
theorem properConvex_cyclicPotential (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    ProperConvex (cyclicPotential B ρ s) := by
  refine ⟨⟨s.1, ?_⟩, cyclicPotential_ne_bot B ρ s⟩
  change cyclicPotential B ρ s s.1 < ⊤
  rw [cyclicPotential_eq_zero hρ hs, ← EReal.coe_zero]
  exact EReal.coe_lt_top 0

/-- Every pair $(x, y) \in \rho$ is a subgradient pair of the potential $f$: $y \in \partial f(x)$.

A chain that ends at $x$, followed by the pair $(x, y)$, is again a chain. Therefore the
supremum that defines $f(z)$ is at least $\operatorname{chainVal}(s, l, x) + \langle z - x, y
\rangle$ for every chain, and so $f(x) + \langle z - x, y \rangle \le f(z)$. -/
theorem mem_subdifferential_cyclicPotential {p : E × F} (hp : p ∈ ρ) :
    p.2 ∈ subdifferential B (cyclicPotential B ρ s) p.1 := by
  intro z
  have key : cyclicPotential B ρ s p.1
      ≤ cyclicPotential B ρ s z - ((B (z - p.1) p.2 : ℝ) : EReal) := by
    refine cyclicPotential_le fun l hl => ?_
    have hvalid : ∀ q ∈ l ++ [p], q ∈ ρ := by
      intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact hl q h
      · rw [List.mem_singleton.1 h]
        exact hp
    have hle := le_cyclicPotential (B := B) hvalid s z
    rw [chainVal_append_singleton, EReal.coe_add] at hle
    exact (EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
      (c := cyclicPotential B ρ s z) (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).2 hle
  exact (EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
    (c := cyclicPotential B ρ s z) (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).1 key

end Potential

/-! ### Cyclically monotone mappings and subdifferentials -/

section Main

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  {ρ : SetRel E F}

/-- Let $E$ be a real vector space with a topology that makes it a topological additive group, and
let $B$ be a pairing of $E$ and $F$ such that $\langle \cdot, y \rangle$ is continuous for each
$y$. Every nonempty cyclically monotone multivalued mapping $\rho \subseteq E \times F$ is
contained in the graph of $\partial f$ for some closed proper convex function
$f \colon E \to [-\infty, +\infty]$. The function $f$ is the potential
`ConvexAnalysis.cyclicPotential`. -/
theorem exists_convexFn_subgradientRel_of_isCyclicallyMonotone [IsContinuousPairing B]
    (hρ : IsCyclicallyMonotone B ρ) (hne : ρ.Nonempty) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedConvex f ∧ ProperConvex f ∧ ρ ⊆ subgradientRel B f := by
  obtain ⟨s, hs⟩ := hne
  refine ⟨cyclicPotential B ρ s, convexFn_cyclicPotential B ρ s, ?_,
    properConvex_cyclicPotential hρ hs, fun p hp => mem_subdifferential_cyclicPotential hp⟩
  refine (closedConvex_iff_lowerSemicontinuous (cyclicPotential_ne_bot B ρ s)).2 ?_
  refine lowerSemicontinuous_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact lowerSemicontinuous_affineFn (continuous_pairing B y)

/-- Let $E$ be a real vector space with a topology that makes it a topological additive group, let
$B$ be a pairing of $E$ and $F$ such that $\langle \cdot, y \rangle$ is continuous for each $y$,
and let $\rho \subseteq E \times F$ be a nonempty multivalued mapping. Then
$$\rho \text{ is cyclically monotone} \iff \rho \subseteq \partial f \text{ for some closed
  proper convex } f \colon E \to [-\infty, +\infty].$$

Here $\partial f$ is the graph `ConvexAnalysis.subgradientRel B f`. The forward direction is
`ConvexAnalysis.exists_convexFn_subgradientRel_of_isCyclicallyMonotone`, and the backward
direction is `ConvexAnalysis.isCyclicallyMonotone_subgradientRel`. -/
theorem isCyclicallyMonotone_iff_exists_convexFn [IsContinuousPairing B] (hne : ρ.Nonempty) :
    IsCyclicallyMonotone B ρ ↔
      ∃ f : E → EReal, ConvexFn f ∧ ClosedConvex f ∧ ProperConvex f ∧ ρ ⊆ subgradientRel B f :=
  ⟨fun h => exists_convexFn_subgradientRel_of_isCyclicallyMonotone h hne,
    fun ⟨_, _, _, hp, hsub⟩ => (isCyclicallyMonotone_subgradientRel hp).mono hsub⟩

/-- Let $E$ be a real vector space with a topology that makes it a topological additive group, and
let $B$ be a pairing of $E$ and $F$ such that $\langle \cdot, y \rangle$ is continuous for each
$y$. Every maximal cyclically monotone mapping $\rho \subseteq E \times F$ is equal to the graph
of $\partial f$ for some closed proper convex function $f$. -/
theorem exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone [IsContinuousPairing B]
    (h : IsMaximalCyclicallyMonotone B ρ) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedConvex f ∧ ProperConvex f ∧ ρ = subgradientRel B f := by
  obtain ⟨f, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone h.1 h.nonempty
  exact ⟨f, hconv, hclosed, hproper,
    Subset.antisymm hsub (h.2 _ (isCyclicallyMonotone_subgradientRel hproper) hsub)⟩

end Main

/-! ### The graph of the subdifferential is closed -/

section GraphClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Let $E$ be a real vector space with a topology that makes it a topological additive group, let
$F$ be a topological space, and let the pairing $(x, y) \mapsto \langle x, y \rangle$ be jointly
continuous on $E \times F$. If $f \colon E \to [-\infty, +\infty]$ is proper and lower
semicontinuous, then the graph of $\partial f$ is closed in $E \times F$. Equivalently, if
$y_i \in \partial f(x_i)$, $x_i \to x$ and $y_i \to y$, then $y \in \partial f(x)$.

Convexity is not used. The joint continuity is needed because the subgradient inequality at
$x_i$ contains $\langle z - x_i, y_i \rangle$, where both arguments move. -/
theorem isClosed_subgradientRel [IsTopologicalAddGroup E]
    (hB : Continuous fun p : E × F => B p.1 p.2) (hp : ProperConvex f)
    (hlsc : LowerSemicontinuous f) : IsClosed (subgradientRel B f) := by
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  have hrw : subgradientRel B f
      = ⋂ z : E, {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z} := by
    ext p
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [hrw]
  refine isClosed_iInter fun z => ?_
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · convert isClosed_univ using 1
    ext p
    simp [hz]
  · set r : ℝ := (f z).toReal with hrdef
    have hrz : ((r : ℝ) : EReal) = f z := EReal.coe_toReal hz (hp.ne_bot z)
    have hset : {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z}
        = (fun p : E × F => (p.1, r - B (z - p.1) p.2)) ⁻¹' epi f := by
      ext p
      rw [Set.mem_preimage, mem_epi, Set.mem_ofPred_eq, ← hrz, EReal.coe_sub]
      exact (EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
        (c := ((r : ℝ) : EReal)) (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _))).symm
    rw [hset]
    refine hepi.preimage (continuous_fst.prodMk ?_)
    exact continuous_const.sub
      (hB.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd))

end GraphClosed

/-! ### Increments along a chain of subgradients -/

section Increment

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- Let $f(p) = a$ and $f(q) = b$ be real, and let $u \in \partial f(p)$. Then
$\langle q - p, u \rangle \le b - a$: a subgradient at the left endpoint underestimates the
increment. -/
theorem pairing_le_sub_of_mem_subdifferential {p q : E} {a b : ℝ} {u : F}
    (hp : f p = (a : EReal)) (hq : f q = (b : EReal)) (hu : u ∈ subdifferential B f p) :
    B (q - p) u ≤ b - a := by
  have h := hu q
  rw [hp, hq, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  linarith

/-- Let $f(p) = a$ and $f(q) = b$ be real, and let $v \in \partial f(q)$. Then
$b - a \le \langle q - p, v \rangle$: a subgradient at the right endpoint overestimates the
increment. -/
theorem sub_le_pairing_of_mem_subdifferential {p q : E} {a b : ℝ} {v : F}
    (hp : f p = (a : EReal)) (hq : f q = (b : EReal)) (hv : v ∈ subdifferential B f q) :
    b - a ≤ B (q - p) v := by
  have h := hv p
  rw [hq, hp, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have hexp : B (p - q) v = -(B (q - p) v) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp] at h
  linarith

/-- The subdivision estimate. Let $\partial f \subseteq \partial g$, and let $x_0, \dots, x_N$ be
points with $x_{i+1} = x_i + d$ for $i < N$. Let $v_i \in \partial f(x_i)$, $f(x_i) = a_i$ and
$g(x_i) = b_i$ be real for $i \le N$. Then
$$|(a_N - a_0) - (b_N - b_0)| \le \langle d, v_N - v_0 \rangle.$$

Both increments lie between the same two telescoping sums, because the subgradients of $f$ are
also subgradients of $g$. A halving of the step halves the bound and does not move the ends of
the chain. This forces the two increments to agree. -/
theorem abs_sub_increment_le (hsub : subgradientRel B f ⊆ subgradientRel B g)
    {x : ℕ → E} {v : ℕ → F} {a b : ℕ → ℝ} {d : E} {N : ℕ}
    (hx : ∀ i < N, x (i + 1) = x i + d)
    (hv : ∀ i ≤ N, v i ∈ subdifferential B f (x i))
    (ha : ∀ i ≤ N, f (x i) = ((a i : ℝ) : EReal))
    (hb : ∀ i ≤ N, g (x i) = ((b i : ℝ) : EReal)) :
    |(a N - a 0) - (b N - b 0)| ≤ B d (v N - v 0) := by
  have step : ∀ i, i < N →
      |(a (i + 1) - a i) - (b (i + 1) - b i)| ≤ B d (v (i + 1)) - B d (v i) := by
    intro i hi
    have hi' : i ≤ N := hi.le
    have hd : x (i + 1) - x i = d := by rw [hx i hi]; abel
    have hvi : v i ∈ subdifferential B f (x i) := hv i hi'
    have hvi1 : v (i + 1) ∈ subdifferential B f (x (i + 1)) := hv (i + 1) hi
    have hgi : v i ∈ subdifferential B g (x i) :=
      hsub (show ((x i, v i) : E × F) ∈ subgradientRel B f from hvi)
    have hgi1 : v (i + 1) ∈ subdifferential B g (x (i + 1)) :=
      hsub (show ((x (i + 1), v (i + 1)) : E × F) ∈ subgradientRel B f from hvi1)
    have h1 := pairing_le_sub_of_mem_subdifferential (ha i hi') (ha (i + 1) hi) hvi
    have h2 := sub_le_pairing_of_mem_subdifferential (ha i hi') (ha (i + 1) hi) hvi1
    have h3 := pairing_le_sub_of_mem_subdifferential (hb i hi') (hb (i + 1) hi) hgi
    have h4 := sub_le_pairing_of_mem_subdifferential (hb i hi') (hb (i + 1) hi) hgi1
    rw [hd] at h1 h2 h3 h4
    rw [abs_le]
    constructor <;> linarith
  have hsum : ∑ i ∈ Finset.range N, ((a (i + 1) - a i) - (b (i + 1) - b i))
      = (a N - a 0) - (b N - b 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub a N, Finset.sum_range_sub b N]
  calc |(a N - a 0) - (b N - b 0)|
      = |∑ i ∈ Finset.range N, ((a (i + 1) - a i) - (b (i + 1) - b i))| := by rw [hsum]
    _ ≤ ∑ i ∈ Finset.range N, |(a (i + 1) - a i) - (b (i + 1) - b i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (B d (v (i + 1)) - B d (v i)) :=
        Finset.sum_le_sum fun i hi => step i (Finset.mem_range.1 hi)
    _ = B d (v N) - B d (v 0) := Finset.sum_range_sub (fun i => B d (v i)) N
    _ = B d (v N - v 0) := (map_sub (B d) _ _).symm

end Increment

/-! ### Raising a function by a constant -/

section AddConst

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- For $f \colon E \to [-\infty, +\infty]$ and $\alpha \in \mathbb{R}$,
$$(f + \alpha)^* = f^* - \alpha.$$
-/
theorem convexConj_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) :
    convexConj B (fun x => f x + (α : EReal)) = fun y => convexConj B f y + ((-α : ℝ) : EReal) := by
  funext y
  rw [convexConj_apply, convexConj_apply, EReal.iSup_add_coe]
  exact iSup_congr fun x => EReal.coe_sub_add_coe' _ _ _

end AddConst

/-! ### The subdifferential determines the function up to a constant -/

section Uniqueness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- If $g$ is proper and $\partial g(x)$ is nonempty, then $g(x)$ is a real number. -/
theorem exists_coe_of_subdifferential_nonempty (hpg : ProperConvex g) {x : E}
    (h : (subdifferential B g x).Nonempty) : ∃ c : ℝ, g x = (c : EReal) := by
  have hxdom : x ∈ convexDom g := by
    by_contra hc
    rw [subdifferential_eq_empty_of_notMem_convexDom hpg hc] at h
    exact absurd h Set.not_nonempty_empty
  exact EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x) hxdom

/-- Let $E$ be a finite-dimensional real normed space with a pairing $B$ that is compatible with its
topology. Let $f$ be a proper convex function and $g$ a proper function on $E$ with
$\partial f \subseteq \partial g$. Let $x_1, x_2 \in \operatorname{ri}(\operatorname{dom} f)$
with $f(x_i) = a_i$ and $g(x_i) = b_i$ real. Then
$$a_2 - a_1 = b_2 - b_1.$$

The classical proof integrates the common one-sided derivative along the segment. This proof
does not use it. It divides $[x_1, x_2]$ into $N$ equal steps and chooses
$v_i \in \partial f(x_i)$ at each node. By `ConvexAnalysis.abs_sub_increment_le`, the two
increments differ by at most $N^{-1} \langle x_2 - x_1, v_N - v_0 \rangle$, which tends to $0$. -/
theorem increment_eq_of_subgradientRel_subset [IsCompatiblePairing B]
    (hf : ConvexFn f) (hpf : ProperConvex f) (hpg : ProperConvex g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g)
    {x₁ x₂ : E} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : x₁ ∈ ri (convexDom f)) (h₂ : x₂ ∈ ri (convexDom f))
    (hfa₁ : f x₁ = (a₁ : EReal)) (hfa₂ : f x₂ = (a₂ : EReal))
    (hgb₁ : g x₁ = (b₁ : EReal)) (hgb₂ : g x₂ = (b₂ : EReal)) :
    a₂ - a₁ = b₂ - b₁ := by
  obtain ⟨u₀, hu₀⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf hpf h₁
  obtain ⟨u₁, hu₁⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf hpf h₂
  set C : ℝ := B (x₂ - x₁) (u₁ - u₀) with hC
  have key : ∀ N : ℕ, 0 < N → |(a₂ - a₁) - (b₂ - b₁)| ≤ (N : ℝ)⁻¹ * C := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    set d : E := (N : ℝ)⁻¹ • (x₂ - x₁) with hd
    set x : ℕ → E := fun i => x₁ + (i : ℝ) • d with hxdef
    have hx0 : x 0 = x₁ := by simp [hxdef]
    have hxN : x N = x₂ := by
      simp only [hxdef, hd, smul_smul, mul_inv_cancel₀ hN0, one_smul]
      abel
    have hxstep : ∀ i < N, x (i + 1) = x i + d := by
      intro i _
      simp only [hxdef]
      push_cast
      rw [add_smul, one_smul]
      abel
    have hxmem : ∀ i ≤ N, x i ∈ ri (convexDom f) := by
      intro i hi
      have ht0 : (0 : ℝ) ≤ (i : ℝ) / (N : ℝ) := by positivity
      have ht1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]
        exact_mod_cast hi
      have heq : x i = (1 - (i : ℝ) / (N : ℝ)) • x₁ + ((i : ℝ) / (N : ℝ)) • x₂ := by
        have hxi : x i = x₁ + ((i : ℝ) / (N : ℝ)) • (x₂ - x₁) := by
          simp only [hxdef, hd, smul_smul, div_eq_mul_inv]
        rw [hxi]
        module
      rw [heq]
      exact Convex.relint hf.convex_convexDom h₁ h₂ (by linarith) ht0 (by ring)
    have hex : ∀ i, ∃ u : F, i ≤ N → u ∈ subdifferential B f (x i) := by
      intro i
      by_cases hi : i ≤ N
      · obtain ⟨u, hu⟩ :=
          subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf hpf (hxmem i hi)
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun hc => absurd hc hi⟩
    choose u hu using hex
    set v : ℕ → F := fun i => if i = 0 then u₀ else if i = N then u₁ else u i with hvdef
    have hvmem : ∀ i ≤ N, v i ∈ subdifferential B f (x i) := by
      intro i hi
      simp only [hvdef]
      split
      · rename_i hi0
        subst hi0
        rw [hx0]
        exact hu₀
      · split
        · rename_i hiN
          subst hiN
          rw [hxN]
          exact hu₁
        · exact hu i hi
    have hfa : ∀ i ≤ N, f (x i) = (((f (x i)).toReal : ℝ) : EReal) := by
      intro i hi
      refine (EReal.coe_toReal ?_ (hpf.ne_bot _)).symm
      exact (mem_convexDom.1 (intrinsicInterior_subset (hxmem i hi))).ne
    have hgb : ∀ i ≤ N, g (x i) = (((g (x i)).toReal : ℝ) : EReal) := by
      intro i hi
      obtain ⟨c, hc⟩ := exists_coe_of_subdifferential_nonempty hpg
        ⟨v i, hsub (show ((x i, v i) : E × F) ∈ subgradientRel B f from hvmem i hi)⟩
      rw [hc]
      simp
    have hchain := abs_sub_increment_le hsub (x := x) (v := v)
      (a := fun i => (f (x i)).toReal) (b := fun i => (g (x i)).toReal) (d := d) (N := N)
      hxstep hvmem hfa hgb
    have hv0 : v 0 = u₀ := by simp [hvdef]
    have hvN : v N = u₁ := by simp [hvdef, hN.ne']
    have hBd : B d (v N - v 0) = (N : ℝ)⁻¹ * C := by
      rw [hvN, hv0, hd, map_smul, LinearMap.smul_apply, smul_eq_mul, hC]
    have ha0 : (f (x 0)).toReal = a₁ := by rw [hx0, hfa₁]; simp
    have haN : (f (x N)).toReal = a₂ := by rw [hxN, hfa₂]; simp
    have hb0 : (g (x 0)).toReal = b₁ := by rw [hx0, hgb₁]; simp
    have hbN : (g (x N)).toReal = b₂ := by rw [hxN, hgb₂]; simp
    simp only [ha0, haN, hb0, hbN, hBd] at hchain
    exact hchain
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * C) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const C
  have hle : |(a₂ - a₁) - (b₂ - b₁)| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with N hN using key N hN
  have hzero := abs_nonpos_iff.1 hle
  linarith

/-- Let $E$ be a finite-dimensional real normed space with a pairing $B$ that is compatible with its
topology. Let $f$ be a closed proper convex function, let $g$ be a lower semicontinuous proper
convex function, and let $\partial f \subseteq \partial g$. Then there is
$\alpha \in \mathbb{R}$ with
$$g \le f + \alpha \quad \text{on } E, \qquad g = f + \alpha \quad \text{on }
  \operatorname{cl}(\operatorname{dom} f).$$

The agreement of the increments on $\operatorname{ri}(\operatorname{dom} f)$ fixes $\alpha$. A
closed convex function is the limit of its values along a segment that runs into a boundary
point, and this carries the identity to $\operatorname{cl}(\operatorname{dom} f)$. Outside
$\operatorname{cl}(\operatorname{dom} f)$ the right-hand side $f + \alpha$ is $+\infty$. -/
theorem exists_forall_le_add_coe_of_subgradientRel_subset [IsCompatiblePairing B]
    (hf : ConvexFn f) (hpf : ProperConvex f) (hcf : ClosedConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) (hlg : LowerSemicontinuous g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g) :
    ∃ α : ℝ, (∀ y, g y ≤ f y + (α : EReal)) ∧
      ∀ y ∈ closure (convexDom f), g y = f y + (α : EReal) := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_convexDom hpf.convexDom_nonempty
  have hfinf : ∀ x ∈ ri (convexDom f), f x = (((f x).toReal : ℝ) : EReal) := fun x hx =>
    (EReal.coe_toReal (mem_convexDom.1 (intrinsicInterior_subset hx)).ne (hpf.ne_bot x)).symm
  have hfing : ∀ x ∈ ri (convexDom f), g x = (((g x).toReal : ℝ) : EReal) := by
    intro x hx
    obtain ⟨u, hu⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf hpf hx
    obtain ⟨c, hc⟩ := exists_coe_of_subdifferential_nonempty hpg
      ⟨u, hsub (show ((x, u) : E × F) ∈ subgradientRel B f from hu)⟩
    rw [hc]
    simp
  set α : ℝ := (g z).toReal - (f z).toReal with hα
  have claim1 : ∀ x ∈ ri (convexDom f), g x = f x + (α : EReal) := by
    intro x hx
    have h := increment_eq_of_subgradientRel_subset hf hpf hpg hsub hz hx
      (hfinf z hz) (hfinf x hx) (hfing z hz) (hfing x hx)
    rw [hfinf x hx, hfing x hx, ← EReal.coe_add, EReal.coe_eq_coe_iff, hα]
    linarith
  have hcf' : convexCl f = f := hcf
  have claim2 : ∀ y ∈ closure (convexDom f), g y = f y + (α : EReal) := by
    intro y hy
    have hseg : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
        g ((1 - a) • z + a • y) = f ((1 - a) • z + a • y) + (α : EReal) := by
      filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
      exact claim1 _ (Convex.segment_mem_relint hf.convex_convexDom hz hy ha.1 ha.2)
    have hftend : Tendsto (fun a : ℝ => f ((1 - a) • z + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := by
      have h := hf.tendsto_convexCl_along_segment_relint hpf hz y
      rwa [hcf'] at h
    refine le_antisymm ?_ ?_
    · by_contra hcon
      rw [not_le] at hcon
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have hfyt : f y ≠ ⊤ := by
        intro h
        rw [h, EReal.top_add_coe] at hc1
        exact absurd hc1 not_top_lt
      obtain ⟨t, ht⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot y) (lt_top_iff_ne_top.2 hfyt)
      rw [ht, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hc1
      have h1 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f ((1 - a) • z + a • y) < ((c - α : ℝ) : EReal) := by
        refine hftend.eventually_lt_const ?_
        rw [ht, EReal.coe_lt_coe_iff]
        linarith
      have h2 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((c : ℝ) : EReal) < g ((1 - a) • z + a • y) :=
        (tendsto_segment z y).eventually (hlg y (c : EReal) hc2)
      obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := ((h1.and h2).and hseg).exists
      have hlt : g ((1 - a) • z + a • y) < ((c : ℝ) : EReal) := by
        rw [ha3]
        have h := EReal.add_lt_add_right_coe ha1 α
        rwa [← EReal.coe_add, show c - α + α = c by ring] at h
      exact absurd (ha2.trans hlt) (lt_irrefl _)
    · by_contra hcon
      rw [not_le] at hcon
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      obtain ⟨s, hs⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot y) (lt_top_iff_ne_top.2 hc1.ne_top)
      have hsc : s < c := by rw [hs, EReal.coe_lt_coe_iff] at hc1; exact hc1
      have hfy : ((c - α : ℝ) : EReal) < f y := by
        by_contra hle
        rw [not_lt] at hle
        have h : f y + (α : EReal) ≤ ((c - α : ℝ) : EReal) + (α : EReal) := add_le_add hle le_rfl
        rw [← EReal.coe_add, show c - α + α = c by ring] at h
        exact absurd (hc2.trans_le h) (lt_irrefl _)
      have h1 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((c - α : ℝ) : EReal) < f ((1 - a) • z + a • y) :=
        hftend.eventually_const_lt hfy
      have h2 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
          g ((1 - a) • z + a • y) ≤ (((1 - a) * (g z).toReal + a * s : ℝ) : EReal) := by
        filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
        exact hg.epi_combo (le_of_eq (hfing z hz)) (le_of_eq hs) (by linarith [ha.2]) ha.1
          (by ring)
      have h3 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((1 - a) * (g z).toReal + a * s : ℝ) < c :=
        (tendsto_affine_nhdsLT_one _ s).eventually_lt_const hsc
      obtain ⟨a, ⟨ha1, ha2⟩, ha3, ha4⟩ := ((h1.and h2).and (h3.and hseg)).exists
      have hlt1 : ((c : ℝ) : EReal) < g ((1 - a) • z + a • y) := by
        rw [ha4]
        have h := EReal.add_lt_add_right_coe ha1 α
        rwa [← EReal.coe_add, show c - α + α = c by ring] at h
      have hlt2 : g ((1 - a) • z + a • y) < ((c : ℝ) : EReal) :=
        lt_of_le_of_lt ha2 (by exact_mod_cast ha3)
      exact absurd (hlt1.trans hlt2) (lt_irrefl _)
  refine ⟨α, fun y => ?_, claim2⟩
  by_cases hy : y ∈ closure (convexDom f)
  · exact le_of_eq (claim2 y hy)
  · have hyd : y ∉ convexDom f := fun hc => hy (subset_closure hc)
    have htop : f y = ⊤ := by
      by_contra hc
      exact hyd (mem_convexDom.2 (lt_top_iff_ne_top.2 hc))
    rw [htop, EReal.top_add_coe]
    exact le_top

end Uniqueness

/-! ### Maximality of the subdifferential -/

section MaximalCyclic

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Adding a real constant to a function does not change its subdifferential:
$\partial(f + \alpha)(x) = \partial f(x)$. -/
@[simp] theorem subdifferential_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) (x : E) :
    subdifferential B (fun x => f x + (α : EReal)) x = subdifferential B f x := by
  ext y
  simp only [mem_subdifferential]
  refine forall_congr' fun z => ?_
  rw [add_right_comm]
  exact (EReal.addLECancellable_coe α).add_le_add_iff_right

/-- Adding a real constant to a function does not change the graph of its subdifferential. -/
theorem subgradientRel_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) :
    subgradientRel B (fun x => f x + (α : EReal)) = subgradientRel B f :=
  Set.ext fun p => by
    simp only [subgradientRel, Set.mem_ofPred_eq, subdifferential_add_coe]

end MaximalCyclic

section Maximality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing $B$ such that the
continuous linear functionals on $E$ are the maps $\langle \cdot, y \rangle$ and those on $F$
are the maps $\langle x, \cdot \rangle$. Let $f, g \colon E \to [-\infty, +\infty]$ be closed
proper convex functions with $\partial f \subseteq \partial g$. Then there is
$\alpha \in \mathbb{R}$ with
$$g = f + \alpha.$$
So a closed proper convex function is determined by its subdifferential up to an additive
constant, and already by the inclusion $\partial f \subseteq \partial g$.

`ConvexAnalysis.exists_forall_le_add_coe_of_subgradientRel_subset` gives $g \le f + \alpha$. The
inversion $\partial f^* = (\partial f)^{-1}$ turns $\partial f \subseteq \partial g$ into
$\partial f^* \subseteq \partial g^*$, and the same result gives $g^* \le f^* + \beta$. Equality
in Fenchel's inequality at a pair of the graph of $\partial f$ gives $\beta = -\alpha$, and the
conjugate of $g^* \le (f + \alpha)^*$ gives $g \ge f + \alpha$. -/
theorem eq_add_coe_of_subgradientRel_subset [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  obtain ⟨α, hle, heq⟩ := exists_forall_le_add_coe_of_subgradientRel_subset hf.convex hf.proper
    hf.closed hg.convex hg.proper hg.lowerSemicontinuous hsub
  have hfstar : ClosedProperConvexFn (convexConj B f) :=
    ⟨convexFn_convexConj B f, closedConvex_convexConj, properConvex_convexConj hf⟩
  have hgstar : ClosedProperConvexFn (convexConj B g) :=
    ⟨convexFn_convexConj B g, closedConvex_convexConj, properConvex_convexConj hg⟩
  have hsub' : subgradientRel B.flip (convexConj B f) ⊆ subgradientRel B.flip (convexConj B g) := by
    rw [subgradientRel_convexConj_eq_inv hf.convex hf.closed,
      subgradientRel_convexConj_eq_inv hg.convex hg.closed]
    exact fun p hp => hsub hp
  obtain ⟨β, hleβ, heqβ⟩ := exists_forall_le_add_coe_of_subgradientRel_subset hfstar.convex
    hfstar.proper hfstar.closed hgstar.convex hgstar.proper hgstar.lowerSemicontinuous hsub'
  -- The two constants are opposite: use equality in Fenchel's inequality on the graph of `∂f`.
  obtain ⟨x, hx⟩ := Convex.relint_nonempty hf.convex.convex_convexDom hf.proper.convexDom_nonempty
  obtain ⟨y, hy⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf.convex hf.proper hx
  have hxdom : x ∈ convexDom f := intrinsicInterior_subset hx
  have hfx : f x + convexConj B f y = ((B x y : ℝ) : EReal) :=
    (ProperConvex.mem_subdifferential_iff_add_convexConj_eq hf.proper).1 hy
  have hgx : g x + convexConj B g y = ((B x y : ℝ) : EReal) :=
    (ProperConvex.mem_subdifferential_iff_add_convexConj_eq hg.proper).1
      (hsub (show ((x, y) : E × F) ∈ subgradientRel B f from hy))
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hxdom
  have hqbot : convexConj B f y ≠ ⊥ := convexConj_ne_bot (B := B) hf.proper.convexDom_nonempty y
  have hqtop : convexConj B f y ≠ ⊤ := by
    intro hc
    rw [hp, hc, EReal.coe_add_top] at hfx
    exact absurd hfx.symm (EReal.coe_ne_top _)
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hqbot (lt_top_iff_ne_top.2 hqtop)
  have hydom : y ∈ convexDom (convexConj B f) := mem_convexDom.2 (lt_top_iff_ne_top.2 hqtop)
  have hgxval : g x = ((p + α : ℝ) : EReal) := by
    rw [heq x (subset_closure hxdom), hp, ← EReal.coe_add]
  have hgyval : convexConj B g y = ((q + β : ℝ) : EReal) := by
    rw [heqβ y (subset_closure hydom), hq, ← EReal.coe_add]
  rw [hp, hq, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hfx
  rw [hgxval, hgyval, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hgx
  have hβ : β = -α := by linarith
  -- Conjugating `g* ≤ (f + α)*` back to `E`.
  have hstar : convexConj B (fun x => f x + (α : EReal)) = fun y => convexConj B f y
      + ((-α : ℝ) : EReal) :=
    convexConj_add_coe B f α
  have hgle : convexConj B g ≤ convexConj B (fun x => f x + (α : EReal)) := by
    rw [hstar]
    intro y
    rw [← hβ]
    exact hleβ y
  have hbcf : convexConj B.flip (convexConj B f) = f := convexBiconj_eq_self hf.convex hf.closed
  have hbcg : convexConj B.flip (convexConj B g) = g := convexBiconj_eq_self hg.convex hg.closed
  have hbih : convexConj B.flip (convexConj B (fun x => f x + (α : EReal))) = fun x => f x +
      (α : EReal) := by
    rw [hstar, convexConj_add_coe B.flip (convexConj B f) (-α), neg_neg]
    funext x
    rw [congrFun hbcf x]
  have hge := convexConj_antitone B.flip hgle
  rw [hbih, hbcg] at hge
  exact ⟨α, fun x => le_antisymm (hle x) (Pi.le_def.1 hge x)⟩

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing $B$ such that the
continuous linear functionals on $E$ are the maps $\langle \cdot, y \rangle$ and those on $F$
are the maps $\langle x, \cdot \rangle$. If $f \colon E \to [-\infty, +\infty]$ is a closed
proper convex function, then the graph of $\partial f$ is maximal cyclically monotone.

If $\partial f \subseteq \sigma$ with $\sigma$ cyclically monotone, then
$\sigma \subseteq \partial g$ for a closed proper convex $g$. Then $g = f + \alpha$ by
`ConvexAnalysis.eq_add_coe_of_subgradientRel_subset`, and the constant does not change the
subdifferential. -/
theorem isMaximalCyclicallyMonotone_subgradientRel [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ClosedProperConvexFn f) :
    IsMaximalCyclicallyMonotone B (subgradientRel B f) := by
  refine ⟨isCyclicallyMonotone_subgradientRel hf.proper, fun σ hσ hsub => ?_⟩
  obtain ⟨x, hx⟩ := Convex.relint_nonempty hf.convex.convex_convexDom hf.proper.convexDom_nonempty
  obtain ⟨y, hy⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hf.convex hf.proper hx
  obtain ⟨g, hgconv, hgclosed, hgproper, hgsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone hσ
      ⟨(x, y), hsub (show ((x, y) : E × F) ∈ subgradientRel B f from hy)⟩
  obtain ⟨α, hα⟩ := eq_add_coe_of_subgradientRel_subset hf ⟨hgconv, hgclosed, hgproper⟩
    (hsub.trans hgsub)
  have hgeq : g = fun x => f x + (α : EReal) := funext hα
  rw [hgeq, subgradientRel_add_coe] at hgsub
  exact hgsub

/-- Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing $B$ such that the
continuous linear functionals on $E$ are the maps $\langle \cdot, y \rangle$ and those on $F$
are the maps $\langle x, \cdot \rangle$. Then a multivalued mapping $\rho \subseteq E \times F$
is maximal cyclically monotone if and only if
$$\rho = \partial f \text{ for some closed proper convex } f \colon E \to [-\infty, +\infty].$$

Here $\partial f$ is the graph `ConvexAnalysis.subgradientRel B f`, and the hypotheses on $B$
are `[IsCompatiblePairing B]` and `[IsCompatiblePairing B.flip]`. -/
theorem isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] {ρ : SetRel E F} :
    IsMaximalCyclicallyMonotone B ρ ↔
      ∃ f : E → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel B f := by
  constructor
  · intro h
    obtain ⟨f, hconv, hclosed, hproper, heq⟩ :=
      exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone h
    exact ⟨f, ⟨hconv, hclosed, hproper⟩, heq⟩
  · rintro ⟨f, hf, rfl⟩
    exact isMaximalCyclicallyMonotone_subgradientRel hf

end Maximality

end ConvexAnalysis
