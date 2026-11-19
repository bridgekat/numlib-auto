/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Banach
import NumlibSurface.Brezis.Chapter02.Section02

/-!
# Brezis, Section 2.3: The open mapping theorem and the closed graph theorem

This module formalizes Section 2.3 of [brezis2011functional] for real Banach spaces $E$ and $F$. A
surjective bounded linear operator $T : E \to F$ maps the unit ball of $E$ onto a set that contains
a ball of $F$ (Theorem 2.6, the open mapping theorem), so $T$ is an open map (Remark 5). A bijective
bounded linear operator has a bounded inverse (Corollary 2.7). Two complete norms on one vector
space, one dominated by the other, are equivalent (Corollary 2.8). A linear operator with closed
graph is continuous (Theorem 2.9, the closed graph theorem), and conversely (Remark 6).

The results restate Mathlib's `ContinuousLinearMap.exists_preimage_norm_le` (Theorem 2.6),
`ContinuousLinearMap.isOpenMap` (Remark 5), `ContinuousLinearEquiv.ofBijective` (Corollary 2.7) and
`LinearMap.continuous_of_isClosed_graph` (Theorem 2.9). The two steps of the proof of Theorem 2.6 in
the source are Mathlib's `ContinuousLinearMap.exists_approx_preimage_norm_le` and, for closed
operators, the backbone theorem `LinearPMap.IsClosed.exists_preimage_norm_le_of_approx`.

## Main results

* Theorem 2.6, `Brezis.Chapter02.theorem_2_6`: there is $c > 0$ with
  $T(B_E(0, 1)) \supseteq B_F(0, c)$ (open mapping theorem).
* Remark 5, `Brezis.Chapter02.remark_2_5`: a surjective bounded operator is an open map.
* Corollary 2.7, `Brezis.Chapter02.corollary_2_7`: a bijective bounded operator has a bounded
  inverse, and $\|x\| \le (1/c)\|Tx\|$.
* Corollary 2.8, `Brezis.Chapter02.corollary_2_8`: two complete norms with $\|x\|_2 \le C\|x\|_1$
  are equivalent.
* Theorem 2.9, `Brezis.Chapter02.theorem_2_9`: a linear operator with closed graph is continuous
  (closed graph theorem).
* Remark 6, `Brezis.Chapter02.remark_2_6`: the graph of a continuous linear operator is closed.

## Implementation notes

* Corollary 2.8 is stated, as in the source, for one vector space with two complete norms. The norms
  are two `Norm V` structures that satisfy `NormedSpace.Core`, and the completeness hypotheses refer
  to the metrics that they induce. The proof puts each norm on a type synonym and applies Corollary
  2.7 to the identity map.

## Deviations from the source

* **Remark 6** (reading). The closed-graph property for continuous maps is stated for linear
  operators between normed spaces. See `Brezis.Chapter02.remark_2_6`.
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Theorem 2.6** of [brezis2011functional] (open mapping theorem). Let $E$ and $F$ be two Banach
spaces and let $T$ be a bounded linear operator from $E$ into $F$ that is surjective. Then there
is a constant $c > 0$ such that
$$T(B_E(0, 1)) \supseteq B_F(0, c). \qquad (7)$$

The balls are open balls. -/
theorem theorem_2_6 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : ∃ c > 0, ball (0 : F) c ⊆ T '' ball 0 1 := by
  obtain ⟨C, hC, h⟩ := T.exists_preimage_norm_le hT
  refine ⟨1 / C, by positivity, fun y hy => ?_⟩
  obtain ⟨x, hx, hxn⟩ := h y
  refine ⟨x, ?_, hx⟩
  rw [mem_ball_zero_iff] at hy ⊢
  calc ‖x‖ ≤ C * ‖y‖ := hxn
    _ < C * (1 / C) := by gcongr
    _ = 1 := by field_simp

/-- **Remark 5** of [brezis2011functional]. Let $E$ and $F$ be two Banach spaces and let
$T : E \to F$ be a surjective bounded linear operator. Then $T$ maps every open set of $E$ onto
an open set of $F$. -/
theorem remark_2_5 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : IsOpenMap T :=
  T.isOpenMap hT

/-- **Corollary 2.7** of [brezis2011functional]. Let $E$ and $F$ be two Banach spaces and let $T$ be
a bounded linear operator from $E$ into $F$ that is bijective. Then $T^{-1}$ is also continuous.
That is, there is a bounded linear operator $S : F \to E$ with $S(Tx) = x$ for all $x \in E$ and
$T(Sy) = y$ for all $y \in F$, and there is a constant $c > 0$ such that
$$\|x\| \le \frac{1}{c}\|Tx\| \quad \text{for all } x \in E.$$
-/
theorem corollary_2_7 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Bijective T) :
    (∃ S : F →L[ℝ] E, Function.LeftInverse S T ∧ Function.RightInverse S T) ∧
      ∃ c > 0, ∀ x, ‖x‖ ≤ (1 / c) * ‖T x‖ := by
  let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.2 hT.1)
    (LinearMap.range_eq_top.2 hT.2)
  refine ⟨⟨e.symm, e.symm_apply_apply, e.apply_symm_apply⟩,
    1 / (‖(e.symm : F →L[ℝ] E)‖ + 1), by positivity, fun x => ?_⟩
  rw [one_div_one_div]
  calc ‖x‖ = ‖e.symm (T x)‖ := by rw [show T x = e x from rfl, e.symm_apply_apply]
    _ ≤ ‖(e.symm : F →L[ℝ] E)‖ * ‖T x‖ := (e.symm : F →L[ℝ] E).le_opNorm _
    _ ≤ (‖(e.symm : F →L[ℝ] E)‖ + 1) * ‖T x‖ := by gcongr; linarith

/-! ### Corollary 2.8: two complete norms on one space -/

section TwoNorms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vector space $V$ with the norm $n$, as a type synonym that carries the normed space
structure given by $h$. -/
private def WithNormCore (V : Type*) [AddCommGroup V] [Module ℝ V] {n : Norm V}
    (_h : @NormedSpace.Core ℝ V _ _ _ n) : Type _ := V

variable {n : Norm V} (h : @NormedSpace.Core ℝ V _ _ _ n)

private noncomputable instance : NormedAddCommGroup (WithNormCore V h) :=
  @NormedAddCommGroup.ofCore ℝ V _ _ _ n h

private instance : Module ℝ (WithNormCore V h) := ‹Module ℝ V›

private noncomputable instance : NormedSpace ℝ (WithNormCore V h) :=
  @NormedSpace.ofCore ℝ (WithNormCore V h) _ _ _ h

/-- **Corollary 2.8** of [brezis2011functional]. Let $E$ be a real vector space with two norms
$\|\cdot\|_1$ and $\|\cdot\|_2$. Assume that $E$ is a Banach space for each of the two norms and
that there is a constant $C \ge 0$ such that
$$\|x\|_2 \le C\|x\|_1 \quad \text{for all } x \in E.$$
Then the two norms are equivalent: there is a constant $c > 0$ such that $\|x\|_1 \le c\|x\|_2$
for all $x \in E$.

The space is `V`. The norms are `Norm V` structures `n₁` and `n₂` that satisfy the norm axioms
`NormedSpace.Core`, and "Banach for the norm" refers to the metric that each norm induces. -/
theorem corollary_2_8 {n₁ n₂ : Norm V} (h₁ : @NormedSpace.Core ℝ V _ _ _ n₁)
    (h₂ : @NormedSpace.Core ℝ V _ _ _ n₂)
    (c₁ : @CompleteSpace V (@NormedAddCommGroup.ofCore ℝ V _ _ _ n₁ h₁).toUniformSpace)
    (c₂ : @CompleteSpace V (@NormedAddCommGroup.ofCore ℝ V _ _ _ n₂ h₂).toUniformSpace)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, @norm V n₂ x ≤ C * @norm V n₁ x) :
    ∃ c > 0, ∀ x, @norm V n₁ x ≤ c * @norm V n₂ x := by
  have : CompleteSpace (WithNormCore V h₁) := c₁
  have : CompleteSpace (WithNormCore V h₂) := c₂
  obtain ⟨C, -, hC⟩ := hC
  let T : WithNormCore V h₁ →L[ℝ] WithNormCore V h₂ :=
    LinearMap.mkContinuous (LinearMap.id : WithNormCore V h₁ →ₗ[ℝ] WithNormCore V h₂) C
      fun x => hC x
  obtain ⟨-, c, hc, hT⟩ := corollary_2_7 T ⟨fun x y hxy => hxy, fun y => ⟨y, rfl⟩⟩
  exact ⟨1 / c, by positivity, hT⟩

end TwoNorms

/-! ### The closed graph theorem -/

/-- **Theorem 2.9** of [brezis2011functional] (closed graph theorem). Let $E$ and $F$ be two Banach
spaces and let $T$ be a linear operator from $E$ into $F$. Assume that the graph of $T$, $G(T)$,
is closed in $E \times F$. Then $T$ is continuous. -/
theorem theorem_2_9 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F)
    (hT : IsClosed (T.graph : Set (E × F))) : Continuous T :=
  T.continuous_of_isClosed_graph hT

/-- **Remark 6** of [brezis2011functional]. The converse of Theorem 2.9 holds: let $E$ and $F$ be
real normed spaces and let $T : E \to F$ be a continuous linear operator. Then the graph $G(T)$
is closed in $E \times F$.

**Reading.** The source gives the converse for arbitrary continuous maps between the Banach
spaces of Theorem 2.9. The declaration keeps the linear-operator setting of that theorem and
allows incomplete spaces, since closedness of the graph uses continuity and the Hausdorff
property of the codomain. -/
theorem remark_2_6 (T : E →ₗ[ℝ] F) (hT : Continuous T) : IsClosed (T.graph : Set (E × F)) := by
  have : (T.graph : Set (E × F)) = {p | p.2 = T p.1} := Set.ext fun p => T.mem_graph_iff p
  rw [this]
  exact isClosed_eq continuous_snd (hT.comp continuous_fst)

end Brezis.Chapter02
