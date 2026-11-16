/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Unbounded.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed operators between normed spaces

Let $E$ and $F$ be normed spaces over a nontrivially normed field $\mathbb{K}$. An unbounded
(partially defined) linear operator $A \colon D(A) \subseteq E \to F$ is **closed** if its graph
$G(A) = \{(u, Au) : u \in D(A)\}$ is closed in $E \times F$. Write $N(A) = \{u \in D(A) : Au = 0\}$
for its kernel and $R(A) = A(D(A))$ for its range. This file proves the facts about closed operators
that need no dual space, following [brezis2011functional], §2.3, §2.6, §2.7 and Exercise 2.14: the
sequential criterion for closedness, the closedness of $N(A)$, the completeness of the graph, the
second step of the proof of the open mapping theorem for a closed operator, and the closed range
criteria.

The second step of the open mapping theorem turns approximate preimages into exact ones: if every
$y \in F$ has some $u \in D(A)$ with $\|Au - y\| \le \frac{1}{2} \|y\|$ and $\|u\| \le C \|y\|$,
then every $y$ has some $u \in D(A)$ with $Au = y$ and $\|u\| \le 2C \|y\|$. The closed range
criterion states that, for a closed operator between Banach spaces, $R(A)$ is closed if and only if
$\operatorname{dist}(u, N(A)) \le C \|Au\|$ for some constant $C$ and all $u \in D(A)$. An a priori
estimate $\|u\| \le C \|Au\|$ gives $N(A) = \{0\}$ and, when $E$ is complete, a closed range.

## Main results

* `LinearPMap.isClosed_iff_seq`: $A$ is closed if and only if $u_n \in D(A)$, $u_n \to x$ and
  $Au_n \to y$ imply $x \in D(A)$ and $Ax = y$.
* `LinearPMap.IsClosed.isClosed_ker`: the kernel of a closed operator is closed.
* `LinearPMap.IsClosed.completeSpace_graph`: the graph of a closed operator between Banach spaces is
  complete.
* `LinearPMap.IsClosed.exists_preimage_norm_le_of_approx`: the second step of the open mapping
  theorem for a closed operator, with the bound $2C$.
* `LinearPMap.IsClosed.ball_subset_image_of_ball_subset_closure_image` and
  `ContinuousLinearMap.ball_subset_image_of_ball_subset_closure_image`: the same step in the form
  $B(0, c) \subseteq \overline{A(B_{D(A)})} \Rightarrow B(0, c/2) \subseteq A(B_{D(A)})$.
* `ContinuousLinearMap.exists_preimage_norm_le_of_approx`: the same step for a bounded operator.
* `ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le`: a bounded operator $T$ between
  Banach spaces has closed range if and only if $\operatorname{dist}(x, N(T)) \le C \|Tx\|$ for some
  $C$ and all $x$.
* `LinearPMap.IsClosed.isClosed_range_iff_exists_infDist_ker_le`: the same criterion for a closed
  operator.
* `LinearPMap.IsClosed.isClosed_range_of_norm_le` and `LinearPMap.ker_eq_bot_of_norm_le`: the
  estimate $\|u\| \le C \|Au\|$ gives a closed range and a trivial kernel.

## Implementation notes

* An unbounded operator is Mathlib's `LinearPMap`, written `E →ₗ.[𝕜] F`, and closedness is
  `LinearPMap.IsClosed`. The range of $A$ is `LinearMap.range A.toFun`, a subspace of $F$, and the
  kernel is `A.ker`, a subspace of $E$.
* The space "$D(A)$ with the graph norm" is not a new type. It is the closed subspace `↥A.graph` of
  $E \times F$, with the norm $\max(\|u\|, \|Au\|)$, which is equivalent to $\|u\| + \|Au\|$. It is
  complete when $E$ and $F$ are (`LinearPMap.IsClosed.completeSpace_graph`). On it the operator
  becomes the bounded map `(ContinuousLinearMap.snd 𝕜 E F).comp A.graph.subtypeL`. This is how the
  closed range criterion for closed operators reduces to the one for bounded operators.
* Mathlib proves the second step of the open mapping theorem only inside the proof of
  `ContinuousLinearMap.exists_preimage_norm_le`, and does not state it. Here the closedness of the
  graph replaces the continuity of the operator, and only the completeness of $E$ is used.
* All results hold over a `NontriviallyNormedField`, except the two forms with balls. These scale a
  vector to a prescribed norm and therefore need a `DenselyNormedField`, such as $\mathbb{R}$ or
  $\mathbb{C}$.
-/

open Filter Function Metric Topology

namespace LinearPMap

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **sequential criterion for closedness**. Let $A \colon D(A) \subseteq E \to F$ be a linear
operator between normed spaces. Then $A$ is closed if and only if, for every sequence $(u_n)$ in
$D(A)$ and all $x \in E$, $y \in F$ with $u_n \to x$ in $E$ and $Au_n \to y$ in $F$, one has
$x \in D(A)$ and $Ax = y$. This is Remark 2.11 of [brezis2011functional].

The graph lies in the metrizable space $E \times F$, so it is closed if and only if it is
sequentially closed. -/
theorem isClosed_iff_seq (A : E →ₗ.[𝕜] F) :
    A.IsClosed ↔ ∀ (u : ℕ → A.domain) (x : E) (y : F),
      Tendsto (fun n => (u n : E)) atTop (𝓝 x) → Tendsto (fun n => A (u n)) atTop (𝓝 y) →
        ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = y := by
  rw [LinearPMap.IsClosed, ← isSeqClosed_iff_isClosed]
  constructor
  · intro h u x y hx hy
    have hmem : (x, y) ∈ A.graph :=
      @h (fun n => ((u n : E), A (u n))) (x, y) (fun n => A.mem_graph (u n)) (hx.prodMk_nhds hy)
    rw [mem_graph_iff] at hmem
    obtain ⟨z, hz, hzy⟩ := hmem
    change (z : E) = x at hz
    refine ⟨hz ▸ z.2, ?_⟩
    rwa [show (⟨x, hz ▸ z.2⟩ : A.domain) = z from Subtype.ext hz.symm]
  · intro h p q hp hpq
    choose u hu hAu using fun n => (mem_graph_iff A).1 (hp n)
    obtain ⟨hx, hy⟩ := h u q.1 q.2 (by simpa only [hu] using hpq.fst_nhds)
      (by simpa only [hAu] using hpq.snd_nhds)
    exact (mem_graph_iff A).2 ⟨⟨q.1, hx⟩, rfl, hy⟩

/-- The **kernel of a closed operator is closed**. Let $A \colon D(A) \subseteq E \to F$ be a closed
operator between normed spaces. Then $N(A) = \{u \in D(A) : Au = 0\}$ is a closed subset of $E$.
This is Remark 2.12 of [brezis2011functional].

The kernel is the preimage of the closed graph under the continuous map $x \mapsto (x, 0)$. The
range of a closed operator need not be closed. -/
theorem IsClosed.isClosed_ker {A : E →ₗ.[𝕜] F} (hA : A.IsClosed) :
    _root_.IsClosed (A.ker : Set E) := by
  have hA' : _root_.IsClosed (A.graph : Set (E × F)) := hA
  have : (A.ker : Set E) = (fun x : E => (x, (0 : F))) ⁻¹' (A.graph : Set (E × F)) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_ker_iff, mem_graph_iff]
    constructor
    · rintro ⟨y, rfl, hy⟩
      exact ⟨y, rfl, hy⟩
    · rintro ⟨y, hy, hy0⟩
      exact ⟨y, hy.symm, hy0⟩
  rw [this]
  exact hA'.preimage (continuous_id.prodMk continuous_const)

/-- The **graph of a closed operator between Banach spaces is a Banach space**. Let $E$ and $F$ be
Banach spaces and let $A \colon D(A) \subseteq E \to F$ be closed. Then the graph
$G(A) \subseteq E \times F$, with the norm $\|(u, Au)\| = \max(\|u\|, \|Au\|)$, is complete.

The subspace `↥A.graph` is the Lean form of "$D(A)$ with the graph norm $\|u\| + \|Au\|$", as in
the proof of Theorem 2.9 and in Exercise 2.14 of [brezis2011functional]; the two norms are
equivalent. On it the operator becomes the bounded map `(ContinuousLinearMap.snd 𝕜 E F).comp
A.graph.subtypeL`. -/
theorem IsClosed.completeSpace_graph [CompleteSpace E] [CompleteSpace F] {A : E →ₗ.[𝕜] F}
    (hA : A.IsClosed) : CompleteSpace A.graph :=
  (show _root_.IsClosed (A.graph : Set (E × F)) from hA).completeSpace_coe

/-- The **second step of the open mapping theorem, for a closed operator**. Let $E$ be a Banach
space, let $F$ be a normed space, let $A \colon D(A) \subseteq E \to F$ be closed, and let
$C \in \mathbb{R}$. Suppose that every $y \in F$ has an approximate preimage $u \in D(A)$ with
$$\|Au - y\| \le \tfrac{1}{2} \|y\| \quad \text{and} \quad \|u\| \le C \|y\|.$$
Then every $y \in F$ has an exact preimage $u \in D(A)$ with $Au = y$ and $\|u\| \le 2C \|y\|$.
This is Step 2 of the proof of Theorem 2.6 of [brezis2011functional].

Mathlib proves this step inside the proof of `ContinuousLinearMap.exists_preimage_norm_le` and
does not state it. The completeness of $F$ is not needed. Iterating the approximation gives a
series $u = \sum_n u_n$ that converges absolutely in $E$; its partial sums lie in $D(A)$ and
their images converge to $y$, so the closed graph gives $u \in D(A)$ and $Au = y$. The bound is
the geometric series $\sum_n 2^{-n} C \|y\| = 2C \|y\|$. -/
theorem IsClosed.exists_preimage_norm_le_of_approx [CompleteSpace E] {A : E →ₗ.[𝕜] F}
    (hA : A.IsClosed) {C : ℝ}
    (hC : ∀ y : F, ∃ u : A.domain, dist (A u) y ≤ 1 / 2 * ‖y‖ ∧ ‖(u : E)‖ ≤ C * ‖y‖) (y : F) :
    ∃ u : A.domain, A u = y ∧ ‖(u : E)‖ ≤ 2 * C * ‖y‖ := by
  have hA' : _root_.IsClosed (A.graph : Set (E × F)) := hA
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  choose g hg using hC
  -- the constant is nonnegative as soon as some `y` is nonzero
  have hC0 : 0 ≤ C := by
    have h0 := (norm_nonneg (g y : E)).trans (hg y).2
    exact (mul_nonneg_iff_of_pos_right (norm_pos_iff.2 hy)).1 h0
  -- `h y` is the part of `y` left without preimage after one approximation step
  let h : F → F := fun y => y - A (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := fun y => by
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [iterate_succ']
      refine (hle _).trans ?_
      rw [pow_succ', mul_assoc]
      gcongr
  -- `u n` is the approximate preimage of the `n`-th residual
  let u : ℕ → A.domain := fun n => g (h^[n] y)
  have ule : ∀ n, ‖(u n : E)‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n => by
    refine (hg _).2.trans ?_
    calc C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖(u n : E)‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have su : Summable fun n => (u n : E) := sNu.of_norm
  set x : E := ∑' n, (u n : E) with hx
  have x_ineq : ‖x‖ ≤ 2 * C * ‖y‖ :=
    calc ‖x‖ ≤ ∑' n, ‖(u n : E)‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
  -- the partial sums lie in `D(A)` and their images converge to `y`
  have fsumeq : ∀ n : ℕ, A (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [Finset.sum_range_succ, map_add, IH, iterate_succ_apply', sub_add]
  have hsum : Tendsto (fun n => ((∑ i ∈ Finset.range n, u i : A.domain) : E)) atTop (𝓝 x) := by
    simpa only [Submodule.coe_sum] using su.hasSum.tendsto_sum_nat
  have hh : Tendsto (fun n => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 y) := by
    simpa only [sub_zero] using hh.const_sub y
  -- the graph is closed, so `(x, y)` lies on it
  have hgraph : (x, y) ∈ A.graph := by
    refine hA'.mem_of_tendsto (hsum.prodMk_nhds L₂) (Eventually.of_forall fun n => ?_)
    rw [← fsumeq n]
    exact A.mem_graph _
  rw [mem_graph_iff] at hgraph
  obtain ⟨z, hz, hzy⟩ := hgraph
  exact ⟨z, hzy, hz ▸ x_ineq⟩

/-- An **a priori estimate gives a closed range**. Let $E$ be a Banach space, let $F$ be a normed
space, let $A \colon D(A) \subseteq E \to F$ be closed, and let $C \in \mathbb{R}$ with
$\|u\| \le C \|Au\|$ for every $u \in D(A)$. Then $R(A)$ is closed in $F$. This is the range
clause of Theorem 2.21, (b) $\Rightarrow$ (c), of [brezis2011functional].

The completeness of $F$ is not needed. If $Au_n \to y$, the estimate makes $(u_n)$ a Cauchy
sequence, so $u_n \to u$ in $E$, and the closed graph gives $y = Au$. -/
theorem IsClosed.isClosed_range_of_norm_le [CompleteSpace E] {A : E →ₗ.[𝕜] F} (hA : A.IsClosed)
    {C : ℝ} (h : ∀ u : A.domain, ‖(u : E)‖ ≤ C * ‖A u‖) :
    _root_.IsClosed (LinearMap.range A.toFun : Set F) := by
  have hA' : _root_.IsClosed (A.graph : Set (E × F)) := hA
  refine IsSeqClosed.isClosed fun w y hw hconv => ?_
  choose v hv using hw
  have hv' : ∀ n, A (v n) = w n := hv
  -- the preimages form a Cauchy sequence, by the estimate
  have hcauchy : CauchySeq fun n => (v n : E) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (ε / (max C 0 + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := h (v m - v n)
    rw [map_sub, hv', hv', Submodule.coe_sub, ← dist_eq_norm, ← dist_eq_norm] at hd
    have h₁ : dist (w m) (w n) < ε / (max C 0 + 1) := hN m hm n hn
    calc dist (v m : E) (v n) ≤ C * dist (w m) (w n) := hd
      _ ≤ max C 0 * dist (w m) (w n) := by gcongr; exact le_max_left _ _
      _ < max C 0 * (ε / (max C 0 + 1)) + ε / (max C 0 + 1) := by
        have := mul_le_mul_of_nonneg_left h₁.le (le_max_right C 0)
        linarith [div_pos hε (by positivity : (0 : ℝ) < max C 0 + 1)]
      _ = ε := by field_simp
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the graph is closed, so `(x, y)` lies on it
  have hgraph : (x, y) ∈ A.graph :=
    hA'.mem_of_tendsto (hx.prodMk_nhds hconv) (.of_forall fun n => by
      have hn := A.mem_graph (v n)
      rwa [hv' n] at hn)
  rw [mem_graph_iff] at hgraph
  obtain ⟨z, -, hz⟩ := hgraph
  exact ⟨z, hz⟩

/-- An **a priori estimate gives a trivial kernel**. Let $A \colon D(A) \subseteq E \to F$ be a
linear operator between normed spaces, and let $C \in \mathbb{R}$ with $\|u\| \le C \|Au\|$ for
every $u \in D(A)$. Then $N(A) = \{0\}$. This is the kernel clause of Theorem 2.21, (b)
$\Rightarrow$ (c), of [brezis2011functional].

Neither closedness of $A$ nor completeness is needed. -/
theorem ker_eq_bot_of_norm_le {A : E →ₗ.[𝕜] F} {C : ℝ}
    (h : ∀ u : A.domain, ‖(u : E)‖ ≤ C * ‖A u‖) : A.ker = ⊥ := by
  rw [ker_eq_bot']
  intro u hu
  have := h u
  rw [hu, norm_zero, mul_zero] at this
  exact Subtype.ext (norm_le_zero_iff.1 this)

end NontriviallyNormedField

section DenselyNormedField

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let $\mathbb{K}$ be a densely normed field, let $A \colon D(A) \subseteq E \to F$ be a linear
operator between normed spaces, and let $B_{D(A)} = \{u \in D(A) : \|u\| < 1\}$. Suppose that
the open ball $B(0, c)$ of $F$ is contained in the closure of $A(B_{D(A)})$. Then for every $s$
with $0 < s < c$ and every $y \in F$ there is $u \in D(A)$ with
$$\|Au - y\| \le \tfrac{1}{2} \|y\| \quad \text{and} \quad \|u\| \le s^{-1} \|y\|.$$

This is the approximation hypothesis of `LinearPMap.IsClosed.exists_preimage_norm_le_of_approx`,
obtained by scaling. The field is densely normed so that $y$ can be scaled to a norm strictly
between $s$ and $c$. -/
theorem exists_dist_le_of_ball_subset_closure_image (A : E →ₗ.[𝕜] F) {c : ℝ}
    (h : ball (0 : F) c ⊆ _root_.closure ((fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1}))
    {s : ℝ} (hs : 0 < s) (hsc : s < c) (y : F) :
    ∃ u : A.domain, dist (A u) y ≤ 1 / 2 * ‖y‖ ∧ ‖(u : E)‖ ≤ s⁻¹ * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  -- a scalar `t` with `s / ‖y‖ < ‖t‖ < c / ‖y‖`, so that `‖t • y‖ < c`
  obtain ⟨t, hts, htc⟩ := NormedField.exists_lt_norm_lt 𝕜 (by positivity : 0 ≤ s / ‖y‖)
    (div_lt_div_of_pos_right hsc hy')
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hts
    exact absurd hts (not_lt.2 (by positivity))
  have hmem : t • y ∈ _root_.closure ((fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1}) := by
    refine h ?_
    rw [mem_ball_zero_iff, norm_smul]
    rwa [lt_div_iff₀ hy'] at htc
  obtain ⟨z, ⟨u', hu', rfl⟩, hz⟩ := Metric.mem_closure_iff.1 hmem (s / 2) (by positivity)
  refine ⟨t⁻¹ • u', ?_, ?_⟩
  · rw [map_smul, dist_eq_norm, show t⁻¹ • A u' - y = t⁻¹ • (A u' - t • y) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul], norm_smul, norm_inv,
      ← dist_eq_norm, dist_comm]
    calc ‖t‖⁻¹ * dist (t • y) (A u') ≤ ‖t‖⁻¹ * (s / 2) := by gcongr
      _ ≤ (s / ‖y‖)⁻¹ * (s / 2) := by gcongr
      _ = 1 / 2 * ‖y‖ := by field_simp
  · rw [Submodule.coe_smul, norm_smul, norm_inv]
    calc ‖t‖⁻¹ * ‖(u' : E)‖ ≤ ‖t‖⁻¹ * 1 := by gcongr; exact hu'.le
      _ ≤ (s / ‖y‖)⁻¹ * 1 := by gcongr
      _ = s⁻¹ * ‖y‖ := by field_simp

/-- The **second step of the open mapping theorem, in the form with balls, for a closed operator**.
Let $\mathbb{K}$ be a densely normed field, let $E$ be a Banach space, let $F$ be a normed
space, let $A \colon D(A) \subseteq E \to F$ be closed, and let
$B_{D(A)} = \{u \in D(A) : \|u\| < 1\}$ be the open unit ball of $D(A)$. If the open ball
$B(0, c)$ of $F$ is contained in the closure of $A(B_{D(A)})$, then
$B(0, c/2) \subseteq A(B_{D(A)})$. This is the step (8) $\Rightarrow$ (11) of the proof of
Theorem 2.6 of [brezis2011functional], and the step (25) $\Rightarrow$ (26) of the proof of
Theorem 2.16.

Only the completeness of $E$ is used. -/
theorem IsClosed.ball_subset_image_of_ball_subset_closure_image [CompleteSpace E]
    {A : E →ₗ.[𝕜] F} (hA : A.IsClosed) {c : ℝ}
    (h : ball (0 : F) c ⊆ _root_.closure ((fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1})) :
    ball (0 : F) (c / 2) ⊆ (fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1} := by
  intro y hy
  rw [mem_ball_zero_iff] at hy
  -- choose `s` strictly between `2 ‖y‖` and `c`
  have hs : 0 < (2 * ‖y‖ + c) / 2 := by linarith [norm_nonneg y]
  have hsc : (2 * ‖y‖ + c) / 2 < c := by linarith
  obtain ⟨u, hu, hnorm⟩ := hA.exists_preimage_norm_le_of_approx
    (A.exists_dist_le_of_ball_subset_closure_image h hs hsc) y
  refine ⟨u, ?_, hu⟩
  change ‖(u : E)‖ < 1
  refine hnorm.trans_lt ?_
  rw [mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc, div_lt_one hs]
  linarith

end DenselyNormedField

end LinearPMap

/-- Let $f \colon E \to F$ be a linear map between modules over a ring. The range of $f$, viewed as
a partially defined operator with domain all of $E$, is the range of $f$. -/
theorem LinearMap.range_toPMap_top {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) :
    LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
  change LinearMap.range (f.comp (⊤ : Submodule R E).subtype) = LinearMap.range f
  rw [LinearMap.range_comp, Submodule.range_subtype, ← LinearMap.range_eq_map]

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let $T \colon E \to F$ be a bounded operator between normed spaces, and let $p$ be a closed
subspace of $E$. Then the restriction of $T$ to $p$, as an operator with domain $p$, is closed.

Its graph is the closed set $\{(x, Tx) : x \in p\}$. -/
theorem isClosed_toPMap (T : E →L[𝕜] F) {p : Submodule 𝕜 E} (hp : IsClosed (p : Set E)) :
    ((T : E →ₗ[𝕜] F).toPMap p).IsClosed := by
  have : (((T : E →ₗ[𝕜] F).toPMap p).graph : Set (E × F)) =
      {q | q.1 ∈ p} ∩ {q | T q.1 = q.2} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨z, hz⟩, rfl, rfl⟩
      exact ⟨hz, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl, rfl⟩
  change _root_.IsClosed _
  rw [this]
  exact (hp.preimage continuous_fst).inter
    (isClosed_eq (T.continuous.comp continuous_fst) continuous_snd)

/-- The **second step of the open mapping theorem, for a bounded operator**. Let $E$ be a Banach
space, let $F$ be a normed space, let $T \colon E \to F$ be bounded, and let $C \in \mathbb{R}$.
Suppose that every $y \in F$ has some $x \in E$ with $\|Tx - y\| \le \frac{1}{2} \|y\|$ and
$\|x\| \le C \|y\|$. Then every $y \in F$ has some $x \in E$ with $Tx = y$ and
$\|x\| \le 2C \|y\|$. This is Step 2 of the proof of Theorem 2.6 of [brezis2011functional].

This is the second half of the proof of Mathlib's `ContinuousLinearMap.exists_preimage_norm_le`,
stated on its own. It is `LinearPMap.IsClosed.exists_preimage_norm_le_of_approx` for $T$ on its
full domain. -/
theorem exists_preimage_norm_le_of_approx [CompleteSpace E] (T : E →L[𝕜] F) {C : ℝ}
    (hC : ∀ y : F, ∃ x : E, dist (T x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) (y : F) :
    ∃ x : E, T x = y ∧ ‖x‖ ≤ 2 * C * ‖y‖ := by
  have hA := T.isClosed_toPMap (p := ⊤) isClosed_univ
  obtain ⟨u, hu, hnorm⟩ := hA.exists_preimage_norm_le_of_approx (C := C) (fun y => by
    obtain ⟨x, hx, hxn⟩ := hC y
    exact ⟨⟨x, trivial⟩, hx, hxn⟩) y
  exact ⟨u, hu, hnorm⟩

/-- The **closed range criterion for a bounded operator**. Let $E$ and $F$ be Banach spaces and let
$T \colon E \to F$ be bounded. Then $R(T)$ is closed if and only if there is $C \in \mathbb{R}$
with
$$\operatorname{dist}(x, N(T)) \le C \|Tx\| \quad \text{for every } x \in E.$$
This is the first part of Exercise 2.14 of [brezis2011functional].

The distance is `Metric.infDist`. The kernel is closed, so $E / N(T)$ is a Banach space with
$\|[x]\| = \operatorname{dist}(x, N(T))$, and $T$ descends to an injective bounded operator on
it with the same range. By `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`,
that range is closed if and only if the descended operator is bounded below, which is the
displayed inequality. -/
theorem isClosed_range_iff_exists_infDist_ker_le [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    IsClosed (Set.range T) ↔ ∃ C : ℝ, ∀ x, infDist x (T.ker : Set E) ≤ C * ‖T x‖ := by
  have : IsClosed (T.ker : Set E) := T.isClosed_ker
  let S : E ⧸ T.ker →L[𝕜] F := T.ker.liftQL T le_rfl
  have hS : ∀ x : E, S (Submodule.Quotient.mk x) = T x := fun x => by
    simp [S, Submodule.liftQL_apply]
  have hnorm : ∀ x : E, ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ = infDist x (T.ker : Set E) :=
    fun x => QuotientAddGroup.norm_mk (S := T.ker.toAddSubgroup) x
  have hinj : Function.Injective S := by
    intro p q hpq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T.ker p
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective T.ker q
    rw [hS, hS] at hpq
    rw [Submodule.Quotient.eq, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hpq,
      sub_self]
  have hrange : Set.range S = Set.range T := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T.ker q
      exact ⟨x, (hS x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, hS x⟩
  rw [← hrange, S.isClosed_range_iff_antilipschitz_of_injective hinj]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun x => ?_⟩
    have := S.bound_of_antilipschitz hK (Submodule.Quotient.mk x)
    rwa [hnorm, hS] at this
  · rintro ⟨C, hC⟩
    refine ⟨Real.toNNReal C, S.antilipschitz_of_bound fun q => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T.ker q
    rw [hnorm, hS, Real.coe_toNNReal']
    calc infDist x (T.ker : Set E) ≤ C * ‖T x‖ := hC x
      _ ≤ max C 0 * ‖T x‖ := by gcongr; exact le_max_left _ _

end NontriviallyNormedField

section DenselyNormedField

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **second step of the open mapping theorem, in the form with balls, for a bounded operator**.
Let $\mathbb{K}$ be a densely normed field, let $E$ be a Banach space, let $F$ be a normed
space, and let $T \colon E \to F$ be bounded. If the open ball $B(0, c)$ of $F$ is contained in
the closure of $T(B(0, 1))$, then $B(0, c/2) \subseteq T(B(0, 1))$. This is the step (8)
$\Rightarrow$ (11) of the proof of Theorem 2.6 of [brezis2011functional].

This is the form in which the proof of Theorem 2.16 of [brezis2011functional] uses the step. -/
theorem ball_subset_image_of_ball_subset_closure_image [CompleteSpace E] (T : E →L[𝕜] F) {c : ℝ}
    (h : ball (0 : F) c ⊆ closure (T '' ball 0 1)) : ball (0 : F) (c / 2) ⊆ T '' ball 0 1 := by
  have h' : ball (0 : F) c ⊆ closure ((fun u : (⊤ : Submodule 𝕜 E) =>
      (T : E →ₗ[𝕜] F).toPMap ⊤ u) '' {u | ‖(u : E)‖ < 1}) :=
    h.trans (closure_mono (by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, trivial⟩, by simpa using hx, rfl⟩))
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (T.isClosed_toPMap (p := ⊤) isClosed_univ)
    |>.ball_subset_image_of_ball_subset_closure_image h' hy
  exact ⟨u, mem_ball_zero_iff.2 hu, rfl⟩

end DenselyNormedField

end ContinuousLinearMap

namespace LinearPMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **closed range criterion for a closed operator**. Let $E$ and $F$ be Banach spaces and let
$A \colon D(A) \subseteq E \to F$ be closed. Then $R(A)$ is closed if and only if there is
$C \in \mathbb{R}$ with
$$\operatorname{dist}(u, N(A)) \le C \|Au\| \quad \text{for every } u \in D(A).$$
This is Remark 2.18 and the second part of Exercise 2.14 of [brezis2011functional].

The proof applies `ContinuousLinearMap.isClosed_range_iff_exists_infDist_ker_le` to the bounded
map $(u, Au) \mapsto Au$ on the Banach space `↥A.graph` ("$D(A)$ with the graph norm"). Its
kernel is $\{(u, 0) : u \in N(A)\}$, and the distances compare with those in $E$ through
$\operatorname{dist}(u, N(A)) \le \operatorname{dist}((u, Au), N) \le \operatorname{dist}(u,
N(A)) + \|Au\|$. -/
theorem IsClosed.isClosed_range_iff_exists_infDist_ker_le [CompleteSpace E] [CompleteSpace F]
    {A : E →ₗ.[𝕜] F} (hA : A.IsClosed) :
    _root_.IsClosed (LinearMap.range A.toFun : Set F) ↔
      ∃ C : ℝ, ∀ u : A.domain, infDist (u : E) (A.ker : Set E) ≤ C * ‖A u‖ := by
  have : CompleteSpace A.graph := hA.completeSpace_graph
  let T : A.graph →L[𝕜] F := (ContinuousLinearMap.snd 𝕜 E F).comp A.graph.subtypeL
  have hT : ∀ p : A.graph, T p = (p : E × F).2 := fun p => rfl
  -- the kernel of `T` consists of the pairs `(z, 0)` with `z ∈ N(A)`
  have hker : ∀ q : A.graph, q ∈ T.ker ↔ (q : E × F).1 ∈ A.ker ∧ (q : E × F).2 = 0 := by
    intro q
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT]
    refine ⟨fun hq => ⟨?_, hq⟩, fun hq => hq.2⟩
    obtain ⟨y, hy, hAy⟩ := (mem_graph_iff A).1 q.2
    exact (mem_ker_iff).2 ⟨y, hy.symm, hAy.trans hq⟩
  have hmk : ∀ z ∈ A.ker, (z, (0 : F)) ∈ A.graph := fun z hz => by
    obtain ⟨y, rfl, hy⟩ := (mem_ker_iff).1 hz
    exact (mem_graph_iff A).2 ⟨y, rfl, hy⟩
  have hne : (T.ker : Set A.graph).Nonempty := ⟨0, T.ker.zero_mem⟩
  have hne' : (A.ker : Set E).Nonempty := ⟨0, A.ker.zero_mem⟩
  -- the two distance comparisons
  have hle₁ : ∀ p : A.graph,
      infDist (p : E × F).1 (A.ker : Set E) ≤ infDist p (T.ker : Set A.graph) := by
    intro p
    refine le_infDist hne |>.2 fun q hq => ?_
    obtain ⟨hq1, -⟩ := (hker q).1 hq
    calc infDist (p : E × F).1 (A.ker : Set E) ≤ dist (p : E × F).1 (q : E × F).1 :=
          infDist_le_dist_of_mem hq1
      _ ≤ dist p q := by rw [Subtype.dist_eq, Prod.dist_eq]; exact le_max_left _ _
  have hle₂ : ∀ p : A.graph, infDist p (T.ker : Set A.graph) ≤
      infDist (p : E × F).1 (A.ker : Set E) + ‖(p : E × F).2‖ := by
    intro p
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨z, hz, hzd⟩ := (infDist_lt_iff hne').1
      (lt_add_of_pos_right (infDist (p : E × F).1 (A.ker : Set E)) hε)
    let q : A.graph := ⟨(z, 0), hmk z hz⟩
    have hq : q ∈ T.ker := (hker q).2 ⟨hz, rfl⟩
    calc infDist p (T.ker : Set A.graph) ≤ dist p q := infDist_le_dist_of_mem hq
      _ = max (dist (p : E × F).1 z) ‖(p : E × F).2‖ := by
          rw [Subtype.dist_eq, Prod.dist_eq, dist_zero_right]
      _ ≤ dist (p : E × F).1 z + ‖(p : E × F).2‖ :=
          max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left dist_nonneg)
      _ < infDist (p : E × F).1 (A.ker : Set E) + ε + ‖(p : E × F).2‖ := by linarith
      _ = infDist (p : E × F).1 (A.ker : Set E) + ‖(p : E × F).2‖ + ε := by ring
  -- the range of `T` is the range of `A`
  have hrange : Set.range T = (LinearMap.range A.toFun : Set F) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨u, -, hAu⟩ := (mem_graph_iff A).1 p.2
      exact ⟨u, hAu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨((u : E), A u), A.mem_graph u⟩, rfl⟩
  rw [← hrange, T.isClosed_range_iff_exists_infDist_ker_le]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u => ?_⟩
    have := (hle₁ ⟨((u : E), A u), A.mem_graph u⟩).trans (hC ⟨((u : E), A u), A.mem_graph u⟩)
    simpa only [hT] using this
  · rintro ⟨C, hC⟩
    refine ⟨C + 1, fun p => ?_⟩
    obtain ⟨u, hu, hAu⟩ := (mem_graph_iff A).1 p.2
    have h1 := hC u
    rw [hu, hAu] at h1
    calc infDist p (T.ker : Set A.graph)
        ≤ infDist (p : E × F).1 (A.ker : Set E) + ‖(p : E × F).2‖ := hle₂ p
      _ ≤ C * ‖(p : E × F).2‖ + ‖(p : E × F).2‖ := by linarith
      _ = (C + 1) * ‖T p‖ := by rw [hT]; ring

end LinearPMap
