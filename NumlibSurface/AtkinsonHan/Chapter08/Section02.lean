/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange
import Numlib.Analysis.PDE.DirichletLaplacian
import Numlib.Analysis.PDE.Elliptic.Spectral
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram

/-!
# Atkinson and Han, Section 8.2: Existence and uniqueness for operator equations

This module formalizes Section 8.2 of [han2009theoretical], on the solvability of a linear operator
equation $Lu = f$ with $L : D(L) \subseteq V \to W$. If $L$ is closed (Definition 8.2.2) and
satisfies the stability estimate
$$\|Lv\| \ge c \|v\| \quad \text{for all } v \in D(L) \qquad (8.2.2)$$
with $c > 0$, then the range $R(L)$ is closed. In Hilbert spaces, $Lu = f$ is then uniquely solvable
for every $f$ as soon as $R(L)^\perp = \{0\}$ (Theorems 8.2.1 and 8.2.4). The module also proves the
closed range theorem of Banach (Theorem 8.2.7) for densely defined closed operators between Banach
spaces, the uniqueness criteria of Theorem 8.2.8 for nonlinear equations, the bijectivity of a
strongly monotone operator $L : V \to V'$ (Example 8.2.5), and two examples on a bounded open set
$\Omega \subseteq \mathbb{R}^{d+1}$: the Laplacian $-\Delta$ on $L^2(\Omega)$ as a closed operator
that is not continuous (Example 8.2.3), and the unique weak solution of the Dirichlet problem
$-\Delta u = f$ in $\Omega$, $u = 0$ on $\partial\Omega$ (Example 8.2.6).

The closed range of $L$ comes from `Numlib.Variational.LaxMilgram`, the closed range theorem from
`Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange` with the Banach adjoint of
`Numlib.Analysis.Normed.Operator.Unbounded.Adjoint`, and the examples from the Dirichlet Laplacian
of `Numlib.Analysis.PDE.DirichletLaplacian` and the Dirichlet eigenfunctions of
`Numlib.Analysis.PDE.Elliptic.Spectral`.

## Main definitions

* Definition 8.2.2, `AtkinsonHan.Chapter08.isClosed_iff_seq`: $L$ is closed if $v_n \in D(L)$,
  $v_n \to v$ and $L v_n \to w$ imply $v \in D(L)$ and $Lv = w$.
* Example 8.2.6, `AtkinsonHan.Chapter08.modelOperator`: the operator
  $L : H_0^1(\Omega) \to H^{-1}(\Omega)$ with $\langle Lu, v \rangle = \int_\Omega \nabla u \cdot
  \nabla v \, dx$.

## Main results

* Theorem 8.2.1, `AtkinsonHan.Chapter08.theorem_8_2_1`: for $L$ into a Hilbert space $W$, $R(L) = W$
  if and only if $R(L)$ is closed and $R(L)^\perp = \{0\}$.
* Example 8.2.3, `AtkinsonHan.Chapter08.example_8_2_3`: the Dirichlet Laplacian $-\Delta$ on
  $L^2(\Omega)$ is closed and not continuous.
* Theorem 8.2.4, `AtkinsonHan.Chapter08.theorem_8_2_4` and
  `AtkinsonHan.Chapter08.theorem_8_2_4_continuous`: a closed operator between Hilbert spaces with
  (8.2.2) and $R(L)^\perp = \{0\}$ is a bijection of $D(L)$ onto $W$.
* Example 8.2.5, `AtkinsonHan.Chapter08.example_8_2_5`: a strongly monotone
  $L \in \mathcal{L}(V, V')$ satisfies (8.2.2) and is a bijection of $V$ onto $V'$.
* Example 8.2.6, `AtkinsonHan.Chapter08.example_8_2_6`: the weak form of $-\Delta u = f$, $u = 0$ on
  $\partial\Omega$, has exactly one solution $u \in H_0^1(\Omega)$ for every $f \in H^{-1}(\Omega)$.
* Theorem 8.2.7, `AtkinsonHan.Chapter08.theorem_8_2_7` and
  `AtkinsonHan.Chapter08.theorem_8_2_7_hilbert`: the closed range theorem for a densely defined
  closed operator between Banach spaces, and its case of a bounded operator between Hilbert spaces.
* Theorem 8.2.8(a), `AtkinsonHan.Chapter08.theorem_8_2_8a` and
  `AtkinsonHan.Chapter08.theorem_8_2_8a_linear`: $\|Tu - Tv\| \ge c \|u - v\|$ with $c > 0$ gives
  uniqueness of a solution of $Tu = w$; for linear $T$ this is (8.2.2).
* Theorem 8.2.8(b), `AtkinsonHan.Chapter08.theorem_8_2_8b`: $\|(Tu - u) - (Tv - v)\| < \|u - v\|$
  for $u \neq v$ gives uniqueness of a solution of $Tu = w$.
* Exercise 8.2.1, `AtkinsonHan.Chapter08.exercise_8_2_1` and
  `AtkinsonHan.Chapter08.exercise_8_2_1_stability`: a linear system $Ax = b$ on $\mathbb{R}^d$ has a
  solution for every $b$ if and only if its solution is unique, and this holds under a stability
  estimate.

## Implementation notes

* An operator $L : D(L) \subseteq V \to W$ is a `LinearPMap` `V →ₗ.[ℝ] W`, whose `domain` is $D(L)$.
  Closedness is Mathlib's `LinearPMap.IsClosed`, the closedness of the graph. The stability estimate
  (8.2.2) is used in the unbundled form `∀ v, c * ‖v‖ ≤ ‖L v‖`, as in the backbone.
* The dual operator $L^*$ of Theorem 8.2.7 is the Banach adjoint `LinearPMap.strongDualAdjoint`.
* The examples use $H^1(\Omega)$ and $H_0^1(\Omega)$ in the multi-index formulation of Definition
  7.2.2, `SobolevEuclidean (d + 1) 1 2 Ω` and `SobolevEuclideanZero (d + 1) 1 2 Ω`, and
  $H^{-1}(\Omega)$ is the dual `StrongDual`. The spaces `AtkinsonHan.Chapter07.definition_7_2_9` and
  `AtkinsonHan.Chapter07.definition_7_2_12_hMinusOne` of Section 7.2 are the same closure and the
  same dual in the tensor formulation of $W^{1,2}(\Omega)$, whose norm is equivalent but not equal.
  The examples use the multi-index formulation because the Dirichlet form and Poincaré's inequality
  of the backbone are stated there.
* The seminorm $|v|_{H^1(\Omega)} = \|\nabla v\|_{L^2(\Omega)}$ is `SobolevMultiIndex.gradNorm`. On
  $H_0^1(\Omega)$ it is a norm equivalent to the norm of $H^1(\Omega)$, by Poincaré's inequality
  (`Numlib.Analysis.Sobolev.Poincare`).

## Deviations from the source

* **Definition 8.2.2 and Theorem 8.2.8** (scope). The closed-graph criterion and the nonlinear
  uniqueness tests use normed spaces. The source assumes Banach spaces. In the second
  uniqueness test the difference $T-I$ is taken for a self-map.
* **Example 8.2.3** (scope). The text treats the distributional Laplacian without a boundary
  condition in its closedness argument. The formal example uses the closed Dirichlet
  realization on a nonempty bounded open set.
* **Example 8.2.6** (generalization). The statement allows any bounded open set. The
  source assumes a Lipschitz boundary.
* **Example 8.2.6** (reading). The source takes the seminorm $|v|_{H^1}$ as the norm of
  $V = H_0^1(\Omega)$ and states $\|L\| = 1$ and $\langle Lv, v \rangle = \|v\|_V^2$. The type of
  $V$ carries the norm of $H^1(\Omega)$, so these facts are stated through the seminorm, and the
  strong monotonicity in the norm of $H^1(\Omega)$ carries the constant of Poincaré's inequality.
  See `AtkinsonHan.Chapter08.example_8_2_6`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

/-- A stability estimate applied to a difference of two solutions gives $c \|v\| \le 0$, and with
$c > 0$ this forces $v = 0$. -/
private theorem eq_zero_of_mul_norm_nonpos {V : Type*} [NormedAddCommGroup V] {c : ℝ} (hc : 0 < c)
    {v : V} (h : c * ‖v‖ ≤ 0) : v = 0 :=
  norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])

section Normed

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Definition 8.2.2** of [han2009theoretical], in the sequential form. Let $V$ and $W$ be real
normed spaces and let $T : D(T) \subseteq V \to W$ be linear. Then $T$ is closed if and only if
for all sequences $v_n \in D(T)$ and all $v \in V$, $w \in W$:
$$v_n \to v \text{ and } T v_n \to w \implies v \in D(T) \text{ and } T v = w.$$

Mathlib's `LinearPMap.IsClosed` is the closedness of the graph, which in a metric space is the
same property. The backbone statement `LinearPMap.isClosed_iff_seq` holds over any nontrivially
normed field.

**Reading.** Same sequential closed graph criterion in normed spaces.
-/
theorem isClosed_iff_seq (T : V →ₗ.[ℝ] W) :
    T.IsClosed ↔ ∀ (v : ℕ → T.domain) (x : V) (w : W),
      Tendsto (fun n => (v n : V)) atTop (𝓝 x) → Tendsto (fun n => T (v n)) atTop (𝓝 w) →
        ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = w :=
  LinearPMap.isClosed_iff_seq T

/-- The remark after Definition 8.2.2: a bounded linear operator $f : V \to W$ defined on all of $V$
is closed. -/
theorem isClosed_toPMap_top (f : V →L[ℝ] W) : ((f : V →ₗ[ℝ] W).toPMap ⊤).IsClosed := by
  rw [isClosed_iff_seq]
  intro v x w hv hw
  refine ⟨Submodule.mem_top, ?_⟩
  have hfx : Tendsto (fun n => f (v n : V)) atTop (𝓝 (f x)) := (f.continuous.tendsto x).comp hv
  exact tendsto_nhds_unique hfx hw

/-- For a bounded linear operator $L : V \to W$ and $c > 0$, the stability estimate (8.2.2),
$c \|v\| \le \|Lv\|$ for all $v \in V$, holds if and only if $L$ is antilipschitz with the
constant $c^{-1}$.

The equivalence makes Mathlib's `AntilipschitzWith` available. The theorems of this section use
the unbundled estimate. -/
theorem stabilityEstimate_iff_antilipschitz (L : V →L[ℝ] W) {c : ℝ} (hc : 0 < c) :
    (∀ v, c * ‖v‖ ≤ ‖L v‖) ↔ AntilipschitzWith (Real.toNNReal c⁻¹) L := by
  have hcoe : ((Real.toNNReal c⁻¹ : NNReal) : ℝ) = c⁻¹ := Real.coe_toNNReal _ (by positivity)
  constructor
  · intro h
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hxy := h (x - y)
    rw [hcoe, dist_eq_norm, dist_eq_norm, ← map_sub, inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  · intro h v
    have hd := h.le_mul_dist v 0
    simp only [hcoe, dist_zero_right, map_zero] at hd
    rw [inv_mul_eq_div, le_div_iff₀ hc] at hd
    linarith

/-- **Theorem 8.2.8(a)** of [han2009theoretical], the linear case. Let $V$ and $W$ be real normed
spaces, let $L : V \to W$ be bounded and linear, and let $c$ be real. Then
$$c \|u - v\| \le \|Lu - Lv\| \text{ for all } u, v \in V \iff c \|v\| \le \|Lv\| \text{ for all
  } v \in V.$$
So for a linear operator the hypothesis of Theorem 8.2.8(a) is the stability estimate (8.2.2). -/
theorem theorem_8_2_8a_linear (L : V →L[ℝ] W) {c : ℝ} :
    (∀ u v : V, c * ‖u - v‖ ≤ ‖L u - L v‖) ↔ ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
  constructor
  · intro h v
    simpa using h v 0
  · intro h u v
    rw [← map_sub]
    exact h (u - v)

end Normed

section Metric

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

/-- **Theorem 8.2.8(a)** of [han2009theoretical]. Let $V$ and $W$ be normed groups, let
$D \subseteq V$, let $T : V \to W$ be a map, which need not be linear, and let $c > 0$ with
$$c \|u - v\| \le \|Tu - Tv\| \quad \text{for all } u, v \in D.$$
If $u_1, u_2 \in D$ satisfy $T u_1 = w$ and $T u_2 = w$, then $u_1 = u_2$. So the equation
$Tu = w$ has at most one solution in $D$.

**Reading.** Same uniqueness from a positive lower Lipschitz bound without completeness.
-/
theorem theorem_8_2_8a {D : Set V} (T : V → W) {c : ℝ} (hc : 0 < c)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, c * ‖u - v‖ ≤ ‖T u - T v‖) {w : W} {u₁ u₂ : V} (h₁ : u₁ ∈ D)
    (h₂ : u₂ ∈ D) (hw₁ : T u₁ = w) (hw₂ : T u₂ = w) : u₁ = u₂ := by
  have h := hstab u₁ h₁ u₂ h₂
  rw [hw₁, hw₂, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (eq_zero_of_mul_norm_nonpos hc h)

/-- **Theorem 8.2.8(b)** of [han2009theoretical]. Let $V$ be a normed group, let $D \subseteq V$,
and let $T : V \to V$ be a map, which need not be linear, with
$$\|(Tu - u) - (Tv - v)\| < \|u - v\| \quad \text{for all } u, v \in D \text{ with } u \neq v.$$
If $u_1, u_2 \in D$ satisfy $T u_1 = w$ and $T u_2 = w$, then $u_1 = u_2$. So the equation
$Tu = w$ has at most one solution in $D$.

**Reading.** Same strict contraction test for self-map minus identity without completeness.
-/
theorem theorem_8_2_8b {D : Set V} (T : V → V)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → ‖(T u - u) - (T v - v)‖ < ‖u - v‖) {w : V} {u₁ u₂ : V}
    (h₁ : u₁ ∈ D) (h₂ : u₂ ∈ D) (hw₁ : T u₁ = w) (hw₂ : T u₂ = w) : u₁ = u₂ := by
  by_contra hne
  have h := hstab u₁ h₁ u₂ h₂ hne
  rw [hw₁, hw₂] at h
  have heq : w - u₁ - (w - u₂) = -(u₁ - u₂) := by abel
  rw [heq, norm_neg] at h
  exact absurd h (lt_irrefl _)

end Metric

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Theorem 8.2.1** of [han2009theoretical]. Let $V$ be a real inner product space, let $W$ be a
real Hilbert space, and let $L : D(L) \subseteq V \to W$ be linear. Then
$$R(L) = W \iff R(L) \text{ is closed and } R(L)^\perp = \{0\}.$$

The source separates the two directions with the Hahn–Banach theorem. The proof here uses
orthogonal projections, and it needs the completeness of $W$ only. -/
theorem theorem_8_2_1 [CompleteSpace W] (L : V →ₗ.[ℝ] W) :
    LinearMap.range L.toFun = ⊤ ↔
      IsClosed (LinearMap.range L.toFun : Set W) ∧ (LinearMap.range L.toFun)ᗮ = ⊥ := by
  constructor
  · intro h
    rw [h]
    exact ⟨by simp, Submodule.top_orthogonal_eq_bot⟩
  · rintro ⟨hc, ho⟩
    rw [← hc.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr ho

/-- **Theorem 8.2.4** of [han2009theoretical]. Let $V$ and $W$ be real Hilbert spaces and let
$L : D(L) \subseteq V \to W$ be a closed linear operator. Assume the stability estimate (8.2.2),
$c \|v\| \le \|Lv\|$ for all $v \in D(L)$ with a constant $c > 0$, and $R(L)^\perp = \{0\}$,
that is, $R(L)$ is dense in $W$. Then for every $f \in W$ there is exactly one $u \in D(L)$ with
$Lu = f$.

The closed range is the backbone theorem `LinearPMap.isClosed_range_of_isClosed_of_le_norm`.
Theorem 8.2.1 turns it into surjectivity, and (8.2.2) gives uniqueness. -/
theorem theorem_8_2_4 [CompleteSpace V] [CompleteSpace W] (L : V →ₗ.[ℝ] W) (hL : L.IsClosed) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖)
    (horth : (LinearMap.range L.toFun)ᗮ = ⊥) (f : W) : ∃! u : L.domain, L u = f := by
  have hclosed := LinearPMap.isClosed_range_of_isClosed_of_le_norm L hL hc hstab
  have htop : LinearMap.range L.toFun = ⊤ := (theorem_8_2_1 L).mpr ⟨hclosed, horth⟩
  have hmem : f ∈ LinearMap.range L.toFun := htop ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, hu, fun y hy => ?_⟩
  have hy' : L.toFun y = f := hy
  have hd : L.toFun (y - u) = 0 := by rw [map_sub, hy', hu, sub_self]
  have h : c * ‖((y - u : L.domain) : V)‖ ≤ ‖L.toFun (y - u)‖ := hstab (y - u)
  rw [hd, norm_zero] at h
  have hz : ((y : V) - (u : V)) = 0 := by simpa using eq_zero_of_mul_norm_nonpos hc h
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- **Theorem 8.2.4** of [han2009theoretical], the remark for continuous operators. Let $V$ and $W$
be real Hilbert spaces and let $L : V \to W$ be bounded and linear. If $c \|v\| \le \|Lv\|$ for
all $v \in V$ with a constant $c > 0$, and $R(L)^\perp = \{0\}$, then $L$ is a bijection of $V$
onto $W$.

A bounded operator defined on all of $V$ is closed, so Theorem 8.2.4 applies. -/
theorem theorem_8_2_4_continuous [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (horth : (LinearMap.range (L : V →ₗ[ℝ] W))ᗮ = ⊥) : Function.Bijective L :=
  ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot L hc hstab horth

/-- Let $V$ and $W$ be real Hilbert spaces, let $L : V \to W$ be bounded and linear, and let
$c \|v\| \le \|Lv\|$ for all $v$ with a constant $c > 0$. If $Lv = w$, then
$\|v\| \le \|w\| / c$. -/
theorem norm_le_of_stabilityEstimate [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v, c * ‖v‖ ≤ ‖L v‖) {v : V} {w : W} (hv : L v = w) :
    ‖v‖ ≤ ‖w‖ / c :=
  ContinuousLinearMap.norm_le_of_le_norm L hc hstab hv

end Hilbert

section StronglyMonotone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Example 8.2.5** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $L : V \to V'$
be bounded and linear, and let $c > 0$ with
$$\langle Lv, v \rangle \ge c \|v\|^2 \quad \text{for all } v \in V,$$
that is, $L$ is strongly monotone. Then $L$ satisfies the stability estimate (8.2.2) with the
same constant, $c \|v\| \le \|Lv\|$ for all $v$; if $\langle Lw, v \rangle = 0$ for all
$w \in V$, then $v = 0$, so $R(L)^\perp = \{0\}$ in the sense of duality; and $L$ is a bijection
of $V$ onto $V'$.

The pairing $\langle Lv, v \rangle$ is `L v v`. Over $\mathbb{R}$ such an operator is a bounded
bilinear form, and the hypothesis is the backbone predicate `SesqForm.IsCoerciveWith`. The three
conclusions come from `SesqForm.IsCoerciveWith.norm_le_norm_apply`, a direct computation, and
`SesqForm.laxMilgram`. -/
theorem example_8_2_5 (L : V →L[ℝ] StrongDual ℝ V) {c : ℝ} (hc : 0 < c)
    (hmono : ∀ v, c * ‖v‖ ^ 2 ≤ L v v) :
    (∀ v, c * ‖v‖ ≤ ‖L v‖) ∧ (∀ v, (∀ w, L w v = 0) → v = 0) ∧ Function.Bijective L := by
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) L c := hmono
  have hker : ∀ v : V, L v v ≤ 0 → v = 0 := by
    intro v hv
    have h1 : c * ‖v‖ ^ 2 ≤ 0 := (hmono v).trans hv
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])
  refine ⟨fun v => SesqForm.IsCoerciveWith.norm_le_norm_apply L hcoer v,
    fun v hv => hker v (le_of_eq (hv v)), ?_, ?_⟩
  · intro u₁ u₂ h
    have hL0 : L (u₁ - u₂) = 0 := by rw [map_sub, h, sub_self]
    have hz : L (u₁ - u₂) (u₁ - u₂) = 0 := by rw [hL0]; rfl
    exact sub_eq_zero.mp (hker _ (le_of_eq hz))
  · intro ℓ
    obtain ⟨u, hu, -⟩ := SesqForm.laxMilgram L ℓ hc hcoer
    exact ⟨u, ContinuousLinearMap.ext hu⟩

end StronglyMonotone

section ClosedRange

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- **Theorem 8.2.7** of [han2009theoretical], bounded operators between Hilbert spaces. Let $V$ and
$W$ be real Hilbert spaces and let $T : V \to W$ be bounded and linear with closed range $R(T)$.
Then for every $f \in W$,
$$f \in R(T) \iff (w, f) = 0 \text{ for every } w \in N(T^*).$$
So $R(T) = N(T^*)^\perp$, and $Tu = f$ is solvable exactly when $f$ is orthogonal to the kernel
of the adjoint $T^*$.

The general statement, for densely defined closed operators between Banach spaces, is
`AtkinsonHan.Chapter08.theorem_8_2_7`. -/
theorem theorem_8_2_7_hilbert (T : V →L[ℝ] W)
    (hclosed : IsClosed (LinearMap.range (T : V →ₗ[ℝ] W) : Set W)) (f : W) :
    f ∈ LinearMap.range (T : V →ₗ[ℝ] W) ↔
      ∀ w, ContinuousLinearMap.adjoint T w = 0 → ⟪w, f⟫_ℝ = 0 := by
  have hrange : LinearMap.range (T : V →ₗ[ℝ] W)
      = (LinearMap.ker (ContinuousLinearMap.adjoint T : W →ₗ[ℝ] V))ᗮ := by
    rw [← ContinuousLinearMap.orthogonal_range T, Submodule.orthogonal_orthogonal_eq_closure,
      hclosed.submodule_topologicalClosure_eq]
  rw [hrange, Submodule.mem_orthogonal]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

end ClosedRange

section ClosedRangeBanach

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Theorem 8.2.7** of [han2009theoretical] (the closed range theorem of Banach). Let $V$ and $W$
be real Banach spaces and let $L : D(L) \subseteq V \to W$ be a densely defined closed linear
operator, with the dual operator $L^* : D(L^*) \subseteq W' \to V'$, $\langle L^* w^*, v
\rangle = \langle w^*, Lv \rangle$. Then the following statements are equivalent:

* (a) $R(L)$ is closed in $W$;
* (b) $R(L) = N(L^*)^\perp = \{w \in W : \langle w^*, w \rangle = 0 \text{ for all } w^* \in
  N(L^*)\}$;
* (c) $R(L^*)$ is closed in $V'$;
* (d) $R(L^*) = N(L)^\perp = \{v^* \in V' : \langle v^*, v \rangle = 0 \text{ for all } v \in
  N(L)\}$.

The dual operator is the Banach adjoint `LinearPMap.strongDualAdjoint` of the backbone, and the
theorem is `LinearPMap.IsClosed.isClosed_range_tfae`, with the two annihilators written out as
the sets of the source. The abstract Fredholm alternative that the source draws from it, (a)
implies (b), is
`LinearPMap.range_eq_strongDualCoannihilator_ker_strongDualAdjoint_of_isClosed_range`. The case
of a bounded operator between Hilbert spaces is `AtkinsonHan.Chapter08.theorem_8_2_7_hilbert`. -/
theorem theorem_8_2_7 (L : V →ₗ.[ℝ] W) (hd : Dense (L.domain : Set V)) (hc : L.IsClosed) :
    [IsClosed (LinearMap.range L.toFun : Set W),
      (LinearMap.range L.toFun : Set W) = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0},
      IsClosed (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V)),
      (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0}].TFAE := by
  have key := hc.isClosed_range_tfae hd
  have e2 : LinearMap.range L.toFun = L.strongDualAdjoint.ker.strongDualCoannihilator ↔
      (LinearMap.range L.toFun : Set W) = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0} := by
    rw [← SetLike.coe_set_eq]
    have : (L.strongDualAdjoint.ker.strongDualCoannihilator : Set W)
        = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0} := by
      ext w
      simp
    rw [this]
  have e4 : LinearMap.range L.strongDualAdjoint.toFun = L.ker.strongDualAnnihilator ↔
      (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0} := by
    rw [← SetLike.coe_set_eq]
    have : (L.ker.strongDualAnnihilator : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0} := by
      ext v'
      simp
    rw [this]
  tfae_have 1 ↔ 2 := (key.out 1 3).trans e2
  tfae_have 1 ↔ 3 := key.out 1 2
  tfae_have 1 ↔ 4 := (key.out 1 4).trans e4
  tfae_finish

end ClosedRangeBanach

section Laplacian

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded nonempty open set, and let $e_n$ be the
Dirichlet eigenfunctions of $-\Delta$ on $\Omega$, with the eigenvalues $\lambda_n$. Then each
$e_n$ lies in the domain of the Dirichlet Laplacian, and
$$(-\Delta) e_n = \lambda_n e_n.$$

This supports Example 8.2.3. The functions $e_n$ form the Hilbert basis of $L^2(\Omega)$ of
Theorem 9.31 of [brezis2011functional], `Elliptic.dirichletEigenbasis`, and $\lambda_n$ is
`Elliptic.dirichletEigenvalue`. The weak eigenvalue equation $\int_\Omega \nabla e_n \cdot
\nabla \varphi \, dx = \lambda_n \int_\Omega e_n \varphi \, dx$ for $\varphi \in H_0^1(\Omega)$
is the defining identity of the domain with the datum $\lambda_n e_n$. -/
theorem dirichletEigenbasis_mem_dirichletLaplacian_domain
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty) (n : ℕ) :
    ∃ h : Elliptic.dirichletEigenbasis Ω hΩ hne n ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨Elliptic.dirichletEigenbasis Ω hΩ hne n, h⟩
        = Elliptic.dirichletEigenvalue Ω hΩ n • Elliptic.dirichletEigenbasis Ω hΩ hne n := by
  obtain ⟨u, hu, hfn, heq⟩ := Elliptic.dirichletEigenbasis_mem_sobolevZero Ω hΩ hne n
  have key : ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u φ
      = Elliptic.load Ω (Elliptic.dirichletEigenvalue Ω hΩ n
        • Elliptic.dirichletEigenbasis Ω hΩ hne n) φ := fun φ hφ ↦ by
    rw [heq φ hφ, Elliptic.load_smul]
    rfl
  exact ⟨⟨u, hu, hfn, _, key⟩, dirichletLaplacian_apply_unique _ hu hfn key⟩

/-- **Example 8.2.3** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
nonempty open set, and let $L v = -\Delta v$ be the Dirichlet Laplacian on $L^2(\Omega)$, with
the domain $D(L) = \{v \in H_0^1(\Omega) : \Delta v \in L^2(\Omega)\}$ and $\Delta v$ in the
weak sense. Then:

* $L$ is closed (Definition 8.2.2);
* every $\varphi \in C_0^\infty(\Omega)$ lies in $D(L)$, and $L\varphi = -\Delta\varphi$ is
  computed classically;
* $(Lv, \varphi)_{L^2} = (v, -\Delta\varphi)_{L^2}$ for all $v \in D(L)$ and
  $\varphi \in C_0^\infty(\Omega)$;
* $L$ is not continuous: there is no constant $C$ with $\|Lv\|_{L^2} \le C \|v\|_{L^2}$ for all
  $v \in D(L)$.

**Generalization.** The source assumes a Lipschitz boundary, which no clause needs.

The example shows that the converse of the remark after Definition 8.2.2 fails. The operator is
the backbone operator `dirichletLaplacian Ω`. Its closedness is `dirichletLaplacian_isClosed`,
and `AtkinsonHan.Chapter08.isClosed_iff_seq` turns it into the sequential form of the source.
The second clause is `testFunction_mem_dirichletLaplacianDomain`. The third clause is the
identity $\int_\Omega (-\Delta v) \varphi = -\int_\Omega v \Delta\varphi$ that the proof of
closedness in the source passes to the limit in; here it is the symmetry
`dirichletLaplacian_isFormalAdjoint`. The source gives no argument for the last clause. Here the
Dirichlet eigenfunctions $e_n$ of Theorem 9.31 of [brezis2011functional] witness it: they are
unit vectors of $L^2(\Omega)$ with $L e_n = \lambda_n e_n$, and $\lambda_n \to +\infty$
(`Elliptic.tendsto_dirichletEigenvalue_atTop`). The argument of the source for closedness, the
limit in the distributional identity, is how the backbone proves that weak derivatives are
closed under limits in $L^p$ (`hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm`); the closedness
of `dirichletLaplacian` itself is proved from its maximal monotonicity, which is the same fact
in a Hilbert space. -/
theorem example_8_2_3 (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty) :
    (dirichletLaplacian Ω).IsClosed ∧
    (∀ φ : 𝓓(Ω, ℝ), ∃ h : φ.toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨φ.toL2, h⟩ = φ.negLaplacian.toL2) ∧
    (∀ (f : (dirichletLaplacian Ω).domain) (φ : 𝓓(Ω, ℝ)),
      ⟪dirichletLaplacian Ω f, φ.toL2⟫_ℝ
        = ⟪(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
            φ.negLaplacian.toL2⟫_ℝ) ∧
    ¬ ∃ C : ℝ, ∀ f : (dirichletLaplacian Ω).domain,
      ‖dirichletLaplacian Ω f‖
        ≤ C * ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖ := by
  have hφ : ∀ φ : 𝓓(Ω, ℝ), ∃ h : φ.toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨φ.toL2, h⟩ = φ.negLaplacian.toL2 := fun φ ↦
    ⟨(testFunction_mem_dirichletLaplacianDomain φ).1,
      (testFunction_mem_dirichletLaplacianDomain φ).2⟩
  refine ⟨dirichletLaplacian_isClosed, hφ, fun f φ ↦ ?_, ?_⟩
  · obtain ⟨h, hh⟩ := hφ φ
    rw [← hh]
    exact dirichletLaplacian_isFormalAdjoint f ⟨φ.toL2, h⟩
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := (Elliptic.tendsto_dirichletEigenvalue_atTop Ω hΩ hne).eventually_gt_atTop C
      |>.exists
    obtain ⟨hmem, hApp⟩ := dirichletEigenbasis_mem_dirichletLaplacian_domain Ω hΩ hne n
    have h1 := hC ⟨Elliptic.dirichletEigenbasis Ω hΩ hne n, hmem⟩
    have hnorm : ‖Elliptic.dirichletEigenbasis Ω hΩ hne n‖ = 1 :=
      (Elliptic.dirichletEigenbasis Ω hΩ hne).orthonormal.1 n
    rw [hApp, norm_smul, Real.norm_eq_abs, Submodule.coe_mk, hnorm, mul_one, mul_one,
      abs_of_pos (Elliptic.dirichletEigenvalue_pos Ω hΩ hne n)] at h1
    exact absurd h1 (not_le.2 hn)

end Laplacian

section Model

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Example 8.2.6** of [han2009theoretical], the operator. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be open, $V = H_0^1(\Omega)$ and $V' = H^{-1}(\Omega)$. The operator $L : V \to V'$ is defined
by
$$\langle Lu, v \rangle = \int_\Omega \nabla u \cdot \nabla v \, dx \quad \text{for } u, v \in
  V.$$

$L$ is the restriction of the backbone Dirichlet form `Elliptic.dirichletForm` to
$H_0^1(\Omega)$, read as a bounded linear map into the dual. $V$ is
`SobolevEuclideanZero (d + 1) 1 2 Ω`, the closure of $C_0^\infty(\Omega)$ in $H^1(\Omega)$ in
the multi-index formulation of Definition 7.2.2, and $V'$ is its `StrongDual`. The spaces
`AtkinsonHan.Chapter07.definition_7_2_9 1 2 Ω` and
`AtkinsonHan.Chapter07.definition_7_2_12_hMinusOne` of Section 7.2 are the same closure and the
same dual in the tensor formulation `Sobolev ℝ 1 2 Ω volume`, whose norm is equivalent but not
equal. The example uses the multi-index formulation because the Poincaré inequality and the
Dirichlet form of the backbone are stated there. -/
noncomputable def modelOperator : SobolevEuclideanZero (d + 1) 1 2 Ω →L[ℝ]
    StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  (Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)

/-- **Example 8.2.6** of [han2009theoretical]. For $u, v \in H_0^1(\Omega)$, the pairing
$\langle Lu, v \rangle$ is the Dirichlet form $\int_\Omega \nabla u \cdot \nabla v \, dx$. -/
theorem modelOperator_apply (u v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    modelOperator Ω u v = Elliptic.dirichletForm Ω u v :=
  rfl

/-- **Example 8.2.6** of [han2009theoretical]. Let $R \ge 0$ and let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an open set contained in the ball $B(0, R)$. Let
$V = H_0^1(\Omega)$ with the seminorm $|v|_{H^1(\Omega)} = \|\nabla v\|_{L^2(\Omega)}$, let
$V' = H^{-1}(\Omega)$, and let $L : V \to V'$ be the operator with $\langle Lu, v \rangle =
\int_\Omega \nabla u \cdot \nabla v \, dx$. Then:

* $\langle Lu, v \rangle = \int_\Omega \sum_i \partial_i u \, \partial_i v \, dx$ for all
  $u, v \in V$;
* $|\langle Lu, v \rangle| \le |u|_{H^1} |v|_{H^1}$ for all $u, v \in V$, so $\|L\| \le 1$ for
  the seminorm;
* $\langle Lv, v \rangle = |v|_{H^1}^2$ for all $v \in V$, so $\|L\| = 1$ for the seminorm when
  $V \neq \{0\}$;
* $\langle Lv, v \rangle \ge (1 + (2R)^2)^{-1} \|v\|_{H^1(\Omega)}^2$ for all $v \in V$, so $L$
  is strongly monotone;
* $L$ is a bijection of $V$ onto $V'$;
* for every $f \in H^{-1}(\Omega)$ there is exactly one $u \in H_0^1(\Omega)$ with $\int_\Omega
  \nabla u \cdot \nabla v \, dx = \langle f, v \rangle$ for all $v \in V$.

**Reading.** The source takes the seminorm $|\cdot|_{H^1}$ as the norm of $V$, and states
$\|L\| = 1$ and $\langle Lv, v \rangle = \|v\|_V^2$. The type
`SobolevEuclideanZero (d + 1) 1 2 Ω` carries the norm of $H^1(\Omega)$, so these facts are
stated through `SobolevMultiIndex.gradNorm`, and the strong monotonicity in the norm of
$H^1(\Omega)$ carries the constant of Poincaré's inequality.

**Generalization.** The source assumes a Lipschitz boundary, which no clause needs.

The last clause gives the unique weak solution of the model problem $-\Delta u = f$ in $\Omega$,
$u = 0$ on $\partial\Omega$ (8.2.3). The strong monotonicity is Poincaré's inequality,
`Elliptic.dirichletForm_restrict_isCoerciveWith`, which comes from
`SobolevEuclideanZero.norm_le_gradNorm`; it also makes the seminorm a norm on $V$ that is
equivalent to the norm of $H^1(\Omega)$. The bijectivity is Example 8.2.5. -/
theorem example_8_2_6 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    (∀ u v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      modelOperator Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x) ∧
    (∀ u v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      |modelOperator Ω u v| ≤ SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 2 Ω)
        * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω)) ∧
    (∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      modelOperator Ω v v = SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω) ^ 2) ∧
    (∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      (1 + (2 * R) ^ 2)⁻¹ * ‖v‖ ^ 2 ≤ modelOperator Ω v v) ∧
    Function.Bijective (modelOperator Ω) ∧
    ∀ f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω),
      ∃! u : SobolevEuclideanZero (d + 1) 1 2 Ω, ∀ v, modelOperator Ω u v = f v := by
  have hcoer := Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  exact ⟨fun u v ↦ Elliptic.dirichletForm_apply Ω u v,
    fun u v ↦ Elliptic.abs_dirichletForm_le Ω u v,
    fun v ↦ Elliptic.dirichletForm_self_eq_gradNorm_sq Ω v, fun v ↦ hcoer v,
    (example_8_2_5 (modelOperator Ω) hpos hcoer).2.2,
    fun f ↦ SesqForm.laxMilgram (modelOperator Ω) f hpos hcoer⟩

end Model

section FiniteDimensional

/-- **Exercise 8.2.1** of [han2009theoretical]. Let $A : \mathbb{R}^d \to \mathbb{R}^d$ be linear.
Then the system $Ax = b$ has at most one solution for each $b$ if and only if it has a solution
for every $b$; that is, $A$ is injective if and only if it is surjective.

The exercise asks for a proof from Theorem 8.2.1, and the proof here is that. On $\mathbb{R}^d$,
`EuclideanSpace ℝ (Fin d)`, the range of $A$ is finite dimensional and hence closed, and
injectivity gives $R(A)^\perp = \{0\}$, so Theorem 8.2.1 gives $R(A) = \mathbb{R}^d$. The
converse is the rank-nullity theorem. -/
theorem exercise_8_2_1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Function.Injective f ↔ Function.Surjective f := by
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
    simp [LinearMap.toPMap, LinearMap.range_comp]
  constructor
  · intro hinj
    have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    rw [hker, finrank_bot, add_zero] at hrank
    have horth : (LinearMap.range f)ᗮ = ⊥ :=
      Submodule.finrank_eq_zero.mp
        (Submodule.finrank_add_finrank_orthogonal' (by simpa using hrank))
    have hclosed : IsClosed (LinearMap.range (f.toPMap ⊤).toFun :
        Set (EuclideanSpace ℝ (Fin d))) := by
      rw [hrange]
      exact (LinearMap.range f).closed_of_finiteDimensional
    have htop := (theorem_8_2_1 (f.toPMap ⊤)).mpr ⟨hclosed, by rw [hrange]; exact horth⟩
    rw [hrange] at htop
    exact LinearMap.range_eq_top.mp htop
  · intro hsurj
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-- **Exercise 8.2.1** of [han2009theoretical], with a stability estimate. Let
$A : \mathbb{R}^d \to \mathbb{R}^d$ be linear, and let $c \|x\| \le \|Ax\|$ for all $x$ with a
constant $c > 0$. Then for every $b \in \mathbb{R}^d$ the system $Ax = b$ has exactly one
solution.

This is the sufficient condition that the exercise asks Theorem 8.2.8 to supply: Theorem
8.2.8(a) makes the solution unique, and `AtkinsonHan.Chapter08.exercise_8_2_1` then gives
existence. -/
theorem exercise_8_2_1_stability {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 < c)
    (hstab : ∀ v, c * ‖v‖ ≤ ‖f v‖) (b : EuclideanSpace ℝ (Fin d)) : ∃! x, f x = b := by
  have hinj : Function.Injective f := fun u v huv =>
    theorem_8_2_8a (D := Set.univ) f hc
      (fun u _ v _ => by rw [← map_sub]; exact hstab (u - v)) (Set.mem_univ u) (Set.mem_univ v)
      rfl huv.symm
  obtain ⟨x, hx⟩ := (exercise_8_2_1 f).mp hinj b
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

end FiniteDimensional

end AtkinsonHan.Chapter08
