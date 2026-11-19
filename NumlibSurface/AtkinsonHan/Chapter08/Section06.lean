/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Real
import Numlib.Variational.Minimax
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson and Han, Section 8.6: Mixed and dual formulations

This module formalizes the abstract items of Section 8.6 of [han2009theoretical]. Let $A$ and $B$ be
sets and $L : A \times B \to \mathbb{R}$. A pair $(u, p) \in A \times B$ is a saddle point of $L$ if
$L(u, q) \le L(u, p) \le L(v, p)$ for all $(v, q) \in A \times B$ (Definition 8.6.1). Proposition
8.6.2 states that $(u, p)$ is a saddle point if and only if $u$ solves the primal problem (8.6.12)
$\inf_{v \in A} \sup_{q \in B} L(v, q)$, $p$ solves the dual problem (8.6.13)
$\sup_{q \in B} \inf_{v \in A} L(v, q)$, and the two values are equal to $L(u, p)$ (8.6.14). Theorem
8.6.3, which the source states without proof and attributes to [ekeland1999convex], gives conditions
for a saddle point to exist when $A$ and $B$ lie in reflexive Banach spaces, and conditions for it
to be unique.

Most of Section 8.6 is a derivation for the Dirichlet problem for the Poisson equation, which needs
$H^1_0(\Omega)$, $L^2(\Omega)^d$ and $H(\operatorname{div}; \Omega)$. The three abstract items need
no function space: $A$ and $B$ are sets and $L$ is any real function, until Theorem 8.6.3. The
existence part of Theorem 8.6.3 specializes `Numlib.Variational.Minimax`, and the saddle points of
the backbone are those of `Numlib.Analysis.Convex.Saddle.Real`.

## Main definitions

* Definition 8.6.1, `AtkinsonHan.Chapter08.IsSaddlePoint`: the saddle point condition (8.6.10).
* Equations (8.6.12) and (8.6.13), `AtkinsonHan.Chapter08.primalObjective` and
  `AtkinsonHan.Chapter08.dualObjective`: the objectives $\sup_{q \in B} L(v, q)$ and
  $\inf_{v \in A} L(v, q)$.

## Main results

* Proposition 8.6.2, `AtkinsonHan.Chapter08.proposition_8_6_2`: $(u, p)$ is a saddle point if and
  only if $u$ and $p$ solve the primal and the dual problem, with common value $L(u, p)$.
* Equation (8.6.14), `AtkinsonHan.Chapter08.equation_8_6_14`: at a saddle point the primal and the
  dual problem have the same value.
* Theorem 8.6.3, `AtkinsonHan.Chapter08.theorem_8_6_3`: under the conditions (a)–(g) a saddle point
  exists.
* Theorem 8.6.3, `AtkinsonHan.Chapter08.theorem_8_6_3_sup` and
  `AtkinsonHan.Chapter08.theorem_8_6_3_inf`: the same with (f) replaced by (f)', or with (g)
  replaced by (g)'.
* Theorem 8.6.3, `AtkinsonHan.Chapter08.theorem_8_6_3_unique_fst` and
  `AtkinsonHan.Chapter08.theorem_8_6_3_unique_snd`: strict convexity or strict concavity makes the
  corresponding component unique.

## Proof outline

The existence part of Theorem 8.6.3 applies Sion's minimax theorem in the weak topologies of $V$ and
$Q$. There the intersections of $A$ and $B$ with a large closed ball are compact (Kakutani's
theorem), and the semicontinuity hypotheses are kept (Mazur's theorem). The coercivity conditions
then keep the saddle point of the truncated problem inside the ball, where it is a saddle point of
the original problem.

## Implementation notes

* The backbone's `ConvexAnalysis.IsSaddlePointOn` follows Rockafellar: it maximizes in the first
  variable, minimizes in the second, and has an `EReal`-valued function. So the pair $(u, p)$ on
  $A \times B$ of the source is the pair $(p, u)$ on $B \times A$ of the backbone for the transposed
  function $(q, v) \mapsto L(v, q)$ (`AtkinsonHan.Chapter08.isSaddlePoint_iff`). Mathlib's
  `IsSaddlePointOn A B L u p` has the convention of the source
  (`AtkinsonHan.Chapter08.isSaddlePoint_iff_isSaddlePointOn`).
* The suprema and infima of the two objectives are `sSup` and `sInf` in $\mathbb{R}$, which have no
  meaning on unbounded sets. Proposition 8.6.2 and (8.6.14) therefore assume them bounded.
* In Theorem 8.6.3, reflexivity (a) is `NormedSpace.IsReflexive ℝ V`, which is Definition 2.7.4 by
  `AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`. A reflexive space is complete, so
  "Banach" needs no separate hypothesis. The limit in (f) is
  `AtkinsonHan.Chapter03.definition_3_3_9`, the coercive functional of Definition 3.3.9. The limit
  in (g) is the same limit to $-\infty$, written with `Filter.atBot`. The suprema and infima of (f)'
  and (g)' are taken in `EReal`, because $\sup_{q \in B} L(v, q)$ can be $+\infty$, and the
  condition of the source allows that.
* The source says that the conclusions hold when (f) is replaced by (f)' or when (g) is replaced by
  (g)'. The two replacements cannot be made together: for $L(v, q) = q - v$ on
  $\mathbb{R} \times \mathbb{R}$, $\sup_q L(v, q) = +\infty$ and $\inf_v L(v, q) = -\infty$ for all
  $v$ and $q$, so (f)' and (g)' hold, but there is no saddle point.

## Deviations from the source

* **Theorem 8.6.3** (scope). The alternative coercivity conditions use extended-real
  suprema and infima. The separate uniqueness statements concern pairs of existing
  saddle points and need only the corresponding strict convexity or concavity.
* **Proposition 8.6.2** (reading). The source does not say whether the suprema and infima are
  finite. The proposition here assumes that $L(v, \cdot)$ is bounded above on $B$ for each $v \in A$
  and that $L(\cdot, q)$ is bounded below on $A$ for each $q \in B$. See
  `AtkinsonHan.Chapter08.proposition_8_6_2`.

## Not formalized

* **The abstract mixed formulation (8.6.21)–(8.6.22).** The source states the problem and refers to
  Brezzi for every theorem about it.
* **The model-problem computations (8.6.1)–(8.6.20) and Exercises 8.6.1–8.6.4.** They are about
  $H^1_0(\Omega)$, $H(\operatorname{div}; \Omega)$ or the Stokes equations.
-/

open Bornology Filter Topology

namespace AtkinsonHan.Chapter08

variable {α β : Type*} {L : α → β → ℝ} {A : Set α} {B : Set β} {u : α} {p : β}

/-- **Definition 8.6.1** of [han2009theoretical], equation (8.6.10). Let $A$ and $B$ be sets and
$L : A \times B \to \mathbb{R}$. A pair $(u, p)$ is a **saddle point** of $L$ on $A \times B$ if
$u \in A$, $p \in B$ and
$$L(u, q) \le L(u, p) \le L(v, p) \quad \text{for all } v \in A,\ q \in B.$$
So $p$ maximizes $L(u, \cdot)$ over $B$, and $u$ minimizes $L(\cdot, p)$ over $A$.

The definition keeps the single chain of inequalities of the source.
`AtkinsonHan.Chapter08.isSaddlePoint_iff` splits it into the four clauses of the backbone. -/
def IsSaddlePoint (L : α → β → ℝ) (A : Set α) (B : Set β) (u : α) (p : β) : Prop :=
  u ∈ A ∧ p ∈ B ∧ ∀ v ∈ A, ∀ q ∈ B, L u q ≤ L u p ∧ L u p ≤ L v p

/-- A pair $(u, p)$ is a saddle point of $L$ on $A \times B$ if and only if $(p, u)$ is a saddle
point in the sense of the backbone's `ConvexAnalysis.IsSaddlePointOn` of the transposed function
$(q, v) \mapsto L(v, q)$, with values in `EReal`, on $B \times A$.

The backbone maximizes in its first variable and minimizes in its second, so the variables of
the source are exchanged. The chain of the source quantifies over $v \in A$ and $q \in B$
together. It can be split because $u \in A$ and $p \in B$ make each half hold on its own. -/
theorem isSaddlePoint_iff :
    IsSaddlePoint L A B u p ↔
      ConvexAnalysis.IsSaddlePointOn (fun q : β × α => ((L q.2 q.1 : ℝ) : EReal)) B A (p, u) := by
  constructor
  · rintro ⟨hu, hp, h⟩
    exact ⟨hp, hu, fun q hq => EReal.coe_le_coe_iff.2 (h u hu q hq).1,
      fun v hv => EReal.coe_le_coe_iff.2 (h v hv p hp).2⟩
  · rintro ⟨hp, hu, h₁, h₂⟩
    exact ⟨hu, hp, fun v hv q hq =>
      ⟨EReal.coe_le_coe_iff.1 (h₁ q hq), EReal.coe_le_coe_iff.1 (h₂ v hv)⟩⟩

/-- A pair $(u, p)$ is a saddle point of $L$ on $A \times B$ if and only if $u \in A$, $p \in B$,
and Mathlib's `IsSaddlePointOn A B L u p` holds, that is $L(u, q) \le L(v, p)$ for all $v \in A$
and $q \in B$.

Mathlib's condition does not include $u \in A$ and $p \in B$. The chain gives the single
inequality by transitivity, and the single inequality gives the chain with $v = u$ and with
$q = p$. -/
theorem isSaddlePoint_iff_isSaddlePointOn :
    IsSaddlePoint L A B u p ↔ u ∈ A ∧ p ∈ B ∧ IsSaddlePointOn A B L u p := by
  constructor
  · rintro ⟨hu, hp, h⟩
    exact ⟨hu, hp, fun v hv q hq => (h v hv q hq).1.trans (h v hv q hq).2⟩
  · rintro ⟨hu, hp, h⟩
    exact ⟨hu, hp, fun v hv q hq => ⟨h u hu q hq, h v hv p hp⟩⟩

/-- **Equation (8.6.12)** of [han2009theoretical], the primal objective. For
$L : A \times B \to \mathbb{R}$, the **primal objective** is $J(v) = \sup_{q \in B} L(v, q)$.
The primal problem is to minimize $J$ over $A$.

The supremum is the real `sSup`. It is $0$ when $B$ is empty or when $L(v, \cdot)$ is unbounded
above on $B$.

**Reading.** Real-valued supremum is total outside bounded slices.
-/
noncomputable def primalObjective (L : α → β → ℝ) (B : Set β) (v : α) : ℝ := sSup (L v '' B)

/-- **Equation (8.6.13)** of [han2009theoretical], the dual objective. For
$L : A \times B \to \mathbb{R}$, the **dual objective** is $G(q) = \inf_{v \in A} L(v, q)$. The
dual problem is to maximize $G$ over $B$.

The infimum is the real `sInf`. It is $0$ when $A$ is empty or when $L(\cdot, q)$ is unbounded
below on $A$.

**Reading.** Real-valued infimum is total outside bounded slices.
-/
noncomputable def dualObjective (L : α → β → ℝ) (A : Set α) (q : β) : ℝ :=
  sInf ((fun v => L v q) '' A)

/-- At a saddle point $(u, p)$, the primal objective at $u$ is $L(u, p)$: the supremum
$\sup_{q \in B} L(u, q)$ is attained at $q = p$. -/
theorem primalObjective_eq (h : IsSaddlePoint L A B u p) : primalObjective L B u = L u p :=
  (isSaddlePoint_iff.mp h).sSup_image_coe_eq

/-- At a saddle point $(u, p)$, the dual objective at $p$ is $L(u, p)$: the infimum
$\inf_{v \in A} L(v, p)$ is attained at $v = u$. -/
theorem dualObjective_eq (h : IsSaddlePoint L A B u p) : dualObjective L A p = L u p :=
  (isSaddlePoint_iff.mp h).sInf_image_coe_eq

/-- **Proposition 8.6.2** of [han2009theoretical], equation (8.6.11). Let $A$ and $B$ be sets and
$L : A \times B \to \mathbb{R}$, such that $L(v, \cdot)$ is bounded above on $B$ for every
$v \in A$ and $L(\cdot, q)$ is bounded below on $A$ for every $q \in B$. Let $u \in A$ and
$p \in B$. Then $(u, p)$ is a saddle point of $L$ if and only if $u$ solves the primal problem
(8.6.12), $p$ solves the dual problem (8.6.13), and the common value is $L(u, p)$:
$$\min_{v \in A} \sup_{q \in B} L(v, q) = \sup_{q \in B} L(u, q) = L(u, p) = \inf_{v \in A} L(v,
  p) = \max_{q \in B} \inf_{v \in A} L(v, q).$$

**Reading.** The source does not say whether the suprema and infima are finite. The two
boundedness hypotheses make them real numbers. Without them `sSup` and `sInf` have no meaning,
and the extremal problems say nothing.

The minimum is stated as `IsLeast` of the image of $A$ under the primal objective, and the
maximum as `IsGreatest` of the image of $B$ under the dual objective. The equality of the two
values is (8.6.14), which is `AtkinsonHan.Chapter08.equation_8_6_14`. -/
theorem proposition_8_6_2 (hu : u ∈ A) (hp : p ∈ B) (hbddA : ∀ v ∈ A, BddAbove (L v '' B))
    (hbddB : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    IsSaddlePoint L A B u p ↔
      (primalObjective L B u = L u p ∧ IsLeast (primalObjective L B '' A) (L u p)) ∧
        dualObjective L A p = L u p ∧ IsGreatest (dualObjective L A '' B) (L u p) := by
  constructor
  · intro h
    have h' := isSaddlePoint_iff.mp h
    exact ⟨⟨primalObjective_eq h, h'.isLeast_sSup_coe hbddA⟩,
      dualObjective_eq h, h'.isGreatest_sInf_coe hbddB⟩
  · rintro ⟨⟨hpu, hleast⟩, hdp, hgreatest⟩
    refine isSaddlePoint_iff.mpr
      (ConvexAnalysis.isSaddlePointOn_coe_of_isLeast_of_isGreatest hp hu (hbddA u hu) (hbddB p hp)
        ?_ ?_ ?_)
    · change IsLeast (primalObjective L B '' A) (primalObjective L B u)
      rw [hpu]
      exact hleast
    · change IsGreatest (dualObjective L A '' B) (dualObjective L A p)
      rw [hdp]
      exact hgreatest
    · exact hleast.csInf_eq.trans hgreatest.csSup_eq.symm

/-- **Equation (8.6.14)** of [han2009theoretical]. Let $L : A \times B \to \mathbb{R}$ be such that
$L(v, \cdot)$ is bounded above on $B$ for every $v \in A$ and $L(\cdot, q)$ is bounded below on
$A$ for every $q \in B$. If $L$ has a saddle point on $A \times B$, then the primal and the dual
problem have the same value:
$$\inf_{v \in A} \sup_{q \in B} L(v, q) = \sup_{q \in B} \inf_{v \in A} L(v, q).$$
So there is no duality gap, and the common value is $L(u, p)$ by
`AtkinsonHan.Chapter08.proposition_8_6_2`.

**Reading.** Equality of primal and dual optimal values assumes saddle point and bounded slices.
-/
theorem equation_8_6_14 (h : IsSaddlePoint L A B u p) (hbddA : ∀ v ∈ A, BddAbove (L v '' B))
    (hbddB : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    sInf (primalObjective L B '' A) = sSup (dualObjective L A '' B) :=
  (isSaddlePoint_iff.mp h).sInf_sSup_eq_sSup_sInf_coe hbddA hbddB

/-! ### Theorem 8.6.3: existence and uniqueness of a saddle point -/

section Existence

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {L : V → Q → ℝ} {A : Set V} {B : Set Q}

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Condition (f) of Theorem 8.6.3 of [han2009theoretical] in the form of the backbone. Let $V$ be a
real normed space, $A \subseteq V$, and $B$ a nonempty set. If $A$ is bounded, or there is
$q_0 \in B$ with $L(v, q_0) \to \infty$ as $\|v\| \to \infty$ in $A$, then there is $q_0 \in B$
such that $L(\cdot, q_0)$ is coercive on $A$ in the sense of `IsCoerciveFunctionalOn`.

On a bounded set every functional is coercive, so $B$ must be nonempty to name a $q_0$ in the
bounded case. -/
theorem exists_isCoerciveFunctionalOn_of_bounded_or_tendsto (hBne : B.Nonempty)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀) :
    ∃ q₀ ∈ B, IsCoerciveFunctionalOn (fun v => L v q₀) A := by
  rcases hf with hbd | ⟨q₀, hq₀, h⟩
  · obtain ⟨q₀, hq₀⟩ := hBne
    exact ⟨q₀, hq₀, IsCoerciveFunctionalOn.of_isBounded hbd⟩
  · exact ⟨q₀, hq₀, (Chapter03.definition_3_3_9_iff _ _).1 h⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Condition (g) of Theorem 8.6.3 of [han2009theoretical] in the form of the backbone. Let $Q$ be a
real normed space, $B \subseteq Q$, and $A$ a nonempty set. If $B$ is bounded, or there is
$v_0 \in A$ with $L(v_0, q) \to -\infty$ as $\|q\| \to \infty$ in $B$, then there is $v_0 \in A$
such that $-L(v_0, \cdot)$ is coercive on $B$ in the sense of `IsCoerciveFunctionalOn`. -/
theorem exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto (hAne : A.Nonempty)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ v₀ ∈ A, IsCoerciveFunctionalOn (fun q => -L v₀ q) B := by
  rcases hg with hbd | ⟨v₀, hv₀, h⟩
  · obtain ⟨v₀, hv₀⟩ := hAne
    exact ⟨v₀, hv₀, IsCoerciveFunctionalOn.of_isBounded hbd⟩
  · refine ⟨v₀, hv₀, (Chapter03.definition_3_3_9_iff B fun q => -L v₀ q).1 ?_⟩
    exact tendsto_neg_atBot_atTop.comp h

omit [NormedSpace ℝ V] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Condition (f)' of Theorem 8.6.3 of [han2009theoretical] in the form of the backbone. Suppose
that $A$ is bounded, or that $\sup_{q \in B} L(v, q) \to \infty$ as $\|v\| \to \infty$ in $A$,
with the supremum taken in the extended reals. Then for every $M \in \mathbb{R}$ there is $R$
such that every $v \in A$ with $\|v\| \ge R$ has some $q \in B$ with $L(v, q) \ge M$.

**Generalization.** Extended-real supremum condition gives a pointwise choice outside a large ball.
-/
theorem forall_exists_le_of_bounded_or_biSup_tendsto
    (hf : IsBounded A ∨
      Tendsto (fun v => ⨆ q ∈ B, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 A) atTop) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ v ∈ A, R ≤ ‖v‖ → ∃ q ∈ B, M ≤ L v q := by
  intro M
  rcases hf with hbd | h
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    exact ⟨C + 1, fun v hv hRv => absurd (hC v hv) (by linarith)⟩
  · have := tendsto_atTop.1 h ((M + 1 : ℝ) : EReal)
    rw [eventually_inf_principal, eventually_comap, eventually_atTop] at this
    obtain ⟨R, hR⟩ := this
    refine ⟨R, fun v hv hRv => ?_⟩
    have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (hR ‖v‖ hRv v rfl hv)
    simp only [lt_iSup_iff, EReal.coe_lt_coe_iff] at this
    obtain ⟨q, hq, hMq⟩ := this
    exact ⟨q, hq, hMq.le⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℝ Q] in
/-- Condition (g)' of Theorem 8.6.3 of [han2009theoretical] in the form of the backbone. Suppose
that $B$ is bounded, or that $\inf_{v \in A} L(v, q) \to -\infty$ as $\|q\| \to \infty$ in $B$,
with the infimum taken in the extended reals. Then for every $M \in \mathbb{R}$ there is $R$
such that every $q \in B$ with $\|q\| \ge R$ has some $v \in A$ with $L(v, q) \le M$.

**Generalization.** Extended-real infimum condition gives a pointwise choice outside a large ball.
-/
theorem forall_exists_le_of_bounded_or_biInf_tendsto
    (hg : IsBounded B ∨
      Tendsto (fun q => ⨅ v ∈ A, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ q ∈ B, R ≤ ‖q‖ → ∃ v ∈ A, L v q ≤ M := by
  intro M
  rcases hg with hbd | h
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    exact ⟨C + 1, fun q hq hRq => absurd (hC q hq) (by linarith)⟩
  · have := tendsto_atBot.1 h ((M - 1 : ℝ) : EReal)
    rw [eventually_inf_principal, eventually_comap, eventually_atTop] at this
    obtain ⟨R, hR⟩ := this
    refine ⟨R, fun q hq hRq => ?_⟩
    have := lt_of_le_of_lt (hR ‖q‖ hRq q rfl hq) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
    simp only [iInf_lt_iff, EReal.coe_lt_coe_iff] at this
    obtain ⟨v, hv, hvM⟩ := this
    exact ⟨v, hv, hvM.le⟩

variable [NormedSpace.IsReflexive ℝ V] [NormedSpace.IsReflexive ℝ Q]

/-- **Theorem 8.6.3** of [han2009theoretical], existence. Let $L : V \times Q \to \mathbb{R}$,
$A \subseteq V$ and $B \subseteq Q$, and assume:

* (a) $V$ and $Q$ are reflexive Banach spaces;
* (b) $A$ is nonempty, closed and convex;
* (c) $B$ is nonempty, closed and convex;
* (d) for every $q \in B$, $v \mapsto L(v, q)$ is convex and lower semicontinuous on $A$;
* (e) for every $v \in A$, $q \mapsto L(v, q)$ is concave and upper semicontinuous on $B$;
* (f) $A$ is bounded, or there is $q_0 \in B$ with $L(v, q_0) \to \infty$ as $\|v\| \to \infty$,
  $v \in A$;
* (g) $B$ is bounded, or there is $v_0 \in A$ with $L(v_0, q) \to -\infty$ as
  $\|q\| \to \infty$, $q \in B$.

Then $L$ has a saddle point $(u, p) \in A \times B$.

Reflexivity is `NormedSpace.IsReflexive ℝ V`, which is Definition 2.7.4 by
`AtkinsonHan.Chapter02.definition_2_7_4_iff_isReflexive`; completeness follows from it. The
limit in (f) is `AtkinsonHan.Chapter03.definition_3_3_9`. The uniqueness clauses are
`AtkinsonHan.Chapter08.theorem_8_6_3_unique_fst` and
`AtkinsonHan.Chapter08.theorem_8_6_3_unique_snd`, and the variants with (f)' or (g)' are
`AtkinsonHan.Chapter08.theorem_8_6_3_sup` and `AtkinsonHan.Chapter08.theorem_8_6_3_inf`. The
proof specializes `exists_isSaddlePointOn_of_isCoerciveFunctionalOn`: Sion's minimax theorem in
the weak topologies on the intersections with a large closed ball, which are weakly compact. -/
theorem theorem_8_6_3 (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_isCoerciveFunctionalOn hAcl hAconv hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (exists_isCoerciveFunctionalOn_of_bounded_or_tendsto hBne hf)
    (exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto hAne hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

/-- **Theorem 8.6.3** of [han2009theoretical], with (f) replaced by (f)'. Let $V$, $Q$, $A$, $B$ and
$L$ satisfy (a)–(e) and (g) of `AtkinsonHan.Chapter08.theorem_8_6_3`, and assume

* (f)' $A$ is bounded, or $\sup_{q \in B} L(v, q) \to \infty$ as $\|v\| \to \infty$, $v \in A$.

Then $L$ has a saddle point $(u, p) \in A \times B$.

The supremum in (f)' is taken in `EReal`, since it can be $+\infty$. The proof specializes
`exists_isSaddlePointOn_of_sup_coercive`: only $A$ is truncated, and the bound $L(u, q) \le
L(v_0, p) \le \max_{q \in B} L(v_0, q)$ for the saddle point $(u, p)$ of the truncated problem
keeps $u$ inside a fixed ball.

**Generalization.** Alternative coercivity uses an extended-real supremum.
-/
theorem theorem_8_6_3_sup (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨
      Tendsto (fun v => ⨆ q ∈ B, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 A) atTop)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_sup_coercive hAcl hAconv hBne hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (forall_exists_le_of_bounded_or_biSup_tendsto hf)
    (exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto hAne hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

/-- **Theorem 8.6.3** of [han2009theoretical], with (g) replaced by (g)'. Let $V$, $Q$, $A$, $B$ and
$L$ satisfy (a)–(f) of `AtkinsonHan.Chapter08.theorem_8_6_3`, and assume

* (g)' $B$ is bounded, or $\inf_{v \in A} L(v, q) \to -\infty$ as $\|q\| \to \infty$, $q \in B$.

Then $L$ has a saddle point $(u, p) \in A \times B$.

The infimum in (g)' is taken in `EReal`. The proof specializes
`exists_isSaddlePointOn_of_inf_coercive`, the transposed form of
`AtkinsonHan.Chapter08.theorem_8_6_3_sup`. The conditions (f)' and (g)' cannot be assumed
together; the module doc comment gives a counterexample.

**Generalization.** Alternative coercivity uses an extended-real infimum.
-/
theorem theorem_8_6_3_inf (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀)
    (hg : IsBounded B ∨
      Tendsto (fun q => ⨅ v ∈ A, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_inf_coercive hAne hAcl hAconv hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (exists_isCoerciveFunctionalOn_of_bounded_or_tendsto hBne hf)
    (forall_exists_le_of_bounded_or_biInf_tendsto hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

end Existence

section Uniqueness

variable {V Q : Type*} [AddCommMonoid V] [SMul ℝ V] [AddCommMonoid Q] [SMul ℝ Q]
  {L : V → Q → ℝ} {A : Set V} {B : Set Q} {u u' : V} {p p' : Q}

omit [AddCommMonoid Q] [SMul ℝ Q] in
/-- **Theorem 8.6.3** of [han2009theoretical], uniqueness of the first component. Let $V$ be an
additive commutative monoid with a scalar multiplication by $\mathbb{R}$, let $Q$ be a type, let
$A \subseteq V$, let $B \subseteq Q$ and let $L : V \times Q \to \mathbb{R}$. If
$v \mapsto L(v, q)$ is strictly convex on $A$ for every $q \in B$, and $(u, p)$ and $(u', p')$
are saddle points of $L$ on $A \times B$, then $u = u'$.

The proof uses only the strict convexity of $L(\cdot, p)$
(`IsSaddlePointOn.fst_eq_of_strictConvexOn`), and no topology.

**Reading.** Strict convexity alone suffices for equality of first components of existing saddle
points.
-/
theorem theorem_8_6_3_unique_fst (hd : ∀ q ∈ B, StrictConvexOn ℝ A fun v => L v q)
    (h : IsSaddlePoint L A B u p) (h' : IsSaddlePoint L A B u' p') : u = u' := by
  obtain ⟨hu, hp, h⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h
  obtain ⟨hu', hp', h'⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h'
  exact h.fst_eq_of_strictConvexOn (hd p hp) hu hu' hp hp' h'

omit [AddCommMonoid V] [SMul ℝ V] in
/-- **Theorem 8.6.3** of [han2009theoretical], uniqueness of the second component. Let
$A \subseteq V$, $B \subseteq Q$ and $L : V \times Q \to \mathbb{R}$. If $q \mapsto L(v, q)$ is
strictly concave on $B$ for every $v \in A$, and $(u, p)$ and $(u', p')$ are saddle points of
$L$ on $A \times B$, then $p = p'$.

The proof is `IsSaddlePointOn.snd_eq_of_strictConcaveOn`, and no topology enters.

**Reading.** Strict concavity alone suffices for equality of second components of existing saddle
points.
-/
theorem theorem_8_6_3_unique_snd (he : ∀ v ∈ A, StrictConcaveOn ℝ B (L v))
    (h : IsSaddlePoint L A B u p) (h' : IsSaddlePoint L A B u' p') : p = p' := by
  obtain ⟨hu, hp, h⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h
  obtain ⟨hu', hp', h'⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h'
  exact h.snd_eq_of_strictConcaveOn (he u hu) hu hu' hp hp' h'

end Uniqueness

end AtkinsonHan.Chapter08
