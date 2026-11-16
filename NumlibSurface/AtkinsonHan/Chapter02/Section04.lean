/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.Quadrature

/-!
# Atkinson and Han, Section 2.4: More results on linear operators

This module formalizes Section 2.4 of [han2009theoretical]. A bounded linear operator from a normed
space $V$ into a Banach space $W$ extends uniquely, with the same norm, to the completion of $V$
(the extension theorem). A bounded linear bijection between Banach spaces has a bounded inverse (the
bounded inverse theorem), and the condition number $\operatorname{cond}(L) = \|L^{-1}\| \, \|L\|$
bounds the relative error of the solution of $Lv = w$ by the relative error of the data. A pointwise
bounded sequence of bounded operators on a Banach space is bounded in norm (the principle of uniform
boundedness), and the Banach–Steinhaus theorem reduces pointwise convergence on the whole space to
convergence on a dense subspace together with a uniform bound. Applied to quadrature rules
$L_n v = \sum_i w_i^{(n)} v(x_i^{(n)})$ on $C[0, 1]$, it shows that rules exact on polynomials of
increasing degree converge for every $v$ if and only if the sums $\sum_i |w_i^{(n)}|$ are bounded.
Example 2.4.2 extends the differentiation operator from $C^1[0, 1]$ to $H^1(0, 1)$.

The proofs specialize Mathlib's completion, open mapping and Banach–Steinhaus theorems, the
condition number `NormedRing.condNumber` of `Numlib.Analysis.Normed.Ring.CondNumber`, the dense
subset form of the Banach–Steinhaus theorem in `Numlib.Analysis.Normed.Operator.BanachSteinhaus`,
the quadrature rules of `Numlib.Approximation.Quadrature`, and the space $H^1(0, 1)$ of
`Numlib.Analysis.Sobolev.Interval`.

## Main definitions

* Section 2.4.2, `AtkinsonHan.Chapter02.cond`: the condition number
  $\operatorname{cond}(L) = \|L^{-1}\| \, \|L\|$.

## Main results

* Theorem 2.4.1, `AtkinsonHan.Chapter02.theorem_2_4_1`: the extension theorem, for the completion of
  a normed space.
* Example 2.4.2, `AtkinsonHan.Chapter02.example_2_4_2_norm_le`,
  `AtkinsonHan.Chapter02.example_2_4_2_dense`, `AtkinsonHan.Chapter02.example_2_4_2` and
  `AtkinsonHan.Chapter02.example_2_4_2_opNorm_le`: the differentiation operator $Dv = v'$ on
  $C^1[0, 1]$ satisfies $\|Dv\|_{L^2} \le \|v\|_{1,2}$, $C^1[0, 1]$ is dense in $H^1(0, 1)$, and $D$
  extends uniquely to a bounded operator from $H^1(0, 1)$ to $L^2(0, 1)$ of norm at most $1$.
* Theorem 2.4.3, `AtkinsonHan.Chapter02.theorem_2_4_3`: the bounded inverse theorem.
* The remark after Theorem 2.4.3, `AtkinsonHan.Chapter02.stability_of_isomorphism`: $\|v - \hat v\|
  \le \|L^{-1}\| \, \|Lv - L\hat v\|$.
* Section 2.4.2, `AtkinsonHan.Chapter02.one_le_cond`: $\operatorname{cond}(L) \ge 1$.
* Equation (2.4.1), `AtkinsonHan.Chapter02.equation_2_4_1`: the relative error bound by the
  condition number.
* Theorem 2.4.4, `AtkinsonHan.Chapter02.theorem_2_4_4`: the principle of uniform boundedness.
* Theorem 2.4.5, `AtkinsonHan.Chapter02.theorem_2_4_5`: the Banach–Steinhaus theorem on a dense
  subspace.
* Equation (2.4.4) and Exercise 2.4.2, `AtkinsonHan.Chapter02.equation_2_4_4`: the norm of a
  quadrature functional with distinct nodes is the sum of the absolute values of its weights.
* Section 2.4.4 and Exercise 2.4.3, `AtkinsonHan.Chapter02.quadrature_convergence`: the convergence
  of numerical quadrature.

## Implementation notes

* `AtkinsonHan.Chapter02.cond_eq_condNumber` identifies `AtkinsonHan.Chapter02.cond`, for $V = W$,
  with the backbone's `NormedRing.condNumber`.
* The sufficiency half of Theorem 2.4.5 is also stated in the generality in which it is proved, as
  `AtkinsonHan.Chapter02.tendsto_of_tendsto_on_dense_of_bounded`: a dense subset suffices, and $V$
  need not be complete.
* Theorem 2.4.4 is Mathlib's `banach_steinhaus`, and Theorem 2.4.5 is the backbone's
  `ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace`.
* In Example 2.4.2 the book gives $C^1[0, 1]$ the norm
  $\|v\|_{1,2} = (\|v\|_2^2 + \|v'\|_2^2)^{1/2}$ and calls its completion $H^1(0, 1)$. Here
  $H^1(0, 1)$ is the backbone's `SobolevInterval 1 0 1`, and $C^1[0, 1]$ with the norm
  $\|\cdot\|_{1,2}$ is its image under the injective inclusion `ContDiffMapIcc.toSobolevInterval`,
  which carries $\|\cdot\|_{1,2}$ to the norm of $H^1(0, 1)$. That $H^1(0, 1)$ is a completion of
  $C^1[0, 1]$ is then `AtkinsonHan.Chapter02.example_2_4_2_dense` together with the completeness of
  $H^1(0, 1)$, and the extension theorem takes the form of `AtkinsonHan.Chapter02.example_2_4_2`: a
  unique continuous extension from a dense subspace.

## Deviations from the source

* **Section 2.4.4** (generalization). The book approximates the functional
  $Lv = \int_0^1 w(x) v(x) \, dx$. The statement holds for every bounded linear functional $L$ on
  $C[0, 1]$. See `AtkinsonHan.Chapter02.quadrature_convergence`.
-/

open Filter Topology NNReal

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.4.1: the extension theorem -/

/-- **Theorem 2.4.1** of [han2009theoretical] (extension theorem). Let $V$ be a normed space and $W$
a Banach space over $\mathbb{K}$, and let $L \in \mathcal{L}(V, W)$. Let $\hat V$ be the
completion of $V$. Then there is a $\hat L \in \mathcal{L}(\hat V, W)$ with $\hat L v = Lv$ for
all $v \in V$ and $\|\hat L\| = \|L\|$, and every $L' \in \mathcal{L}(\hat V, W)$ with
$L' v = Lv$ for all $v \in V$ equals $\hat L$.

The completion is Mathlib's `UniformSpace.Completion V`, and $V$ is embedded in it by the
coercion. -/
theorem theorem_2_4_1 [CompleteSpace W] (L : V →L[𝕜] W) :
    ∃ Lhat : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, Lhat ↑v = L v) ∧ ‖Lhat‖ = ‖L‖ ∧
      ∀ L' : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, L' ↑v = L v) → L' = Lhat := by
  have hdense : DenseRange (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.denseRange_coe
  have hind :
      IsUniformInducing (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.isUniformInducing_coe V
  set Lhat := L.extend (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V)
    with hLhat
  have heq : ∀ v : V, Lhat ↑v = L v := fun v => L.extend_eq hdense hind v
  refine ⟨Lhat, heq, le_antisymm ?_ ?_, ?_⟩
  · have hbound : ∀ x : V, ‖x‖ ≤ (1 : ℝ≥0) *
        ‖(UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) x‖ := by
      intro x
      simp
    simpa [hLhat] using L.opNorm_extend_le hdense hbound
  · refine L.opNorm_le_bound (norm_nonneg _) fun v => ?_
    rw [← heq v]
    simpa [UniformSpace.Completion.norm_coe] using Lhat.le_opNorm (↑v : UniformSpace.Completion V)
  · intro L' hL'
    rw [hLhat]
    exact (ContinuousLinearMap.extend_unique L hdense hind L' (by ext v; exact hL' v)).symm

/-! ### Theorem 2.4.3: the bounded inverse theorem -/

/-- **Theorem 2.4.3** of [han2009theoretical] (bounded inverse theorem). Let $V$ and $W$ be Banach
spaces over $\mathbb{K}$, and let $L \in \mathcal{L}(V, W)$ be a bijection of $V$ onto $W$. Then
$L^{-1}$ is bounded: $L$ is the underlying operator of a continuous linear equivalence of $V$
onto $W$.

The theorem is a corollary of the open mapping theorem. -/
theorem theorem_2_4_3 [CompleteSpace V] [CompleteSpace W] (L : V →L[𝕜] W)
    (hL : Function.Bijective L) : ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L := by
  refine ⟨ContinuousLinearEquiv.ofBijective L ?_ ?_, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  · exact LinearMap.ker_eq_bot.2 hL.1
  · exact LinearMap.range_eq_top.2 hL.2

/-- The remark after **Theorem 2.4.3** of [han2009theoretical], stability. Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L$ be a bijection of $V$ onto $W$ with $L$ and $L^{-1}$
bounded. Then for all $v, \hat v \in V$,
$$\|v - \hat v\| \le \|L^{-1}\| \, \|Lv - L\hat v\|.$$
Thus the solution of $Lv = w$ depends Lipschitz continuously on the data $w$, with the constant
$\|L^{-1}\|$. -/
theorem stability_of_isomorphism (L : V ≃L[𝕜] W) (v vhat : V) :
    ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := by
  have hv : (L.symm : W →L[𝕜] V) (L v - L vhat) = v - vhat := by simp
  calc ‖v - vhat‖ = ‖(L.symm : W →L[𝕜] V) (L v - L vhat)‖ := by rw [hv]
    _ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := (L.symm : W →L[𝕜] V).le_opNorm _

/-! ### The condition number (2.4.1) -/

/-- **Section 2.4.2** of [han2009theoretical], the condition number. Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L$ be a bijection of $V$ onto $W$ with $L$ and $L^{-1}$
bounded. The **condition number** of $L$ is
$$\operatorname{cond}(L) = \|L^{-1}\| \, \|L\|.$$
-/
noncomputable def cond (L : V ≃L[𝕜] W) : ℝ :=
  ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W)‖

/-- Let $V$ be a normed space over $\mathbb{K}$, and let $L$ be a bijection of $V$ onto $V$ with $L$
and $L^{-1}$ bounded. Then $\operatorname{cond}(L)$ is the backbone's condition number
`NormedRing.condNumber` of $L$ as an element of the normed ring $\mathcal{L}(V)$. -/
theorem cond_eq_condNumber (L : V ≃L[𝕜] V) :
    cond L = NormedRing.condNumber (L : V →L[𝕜] V) := by
  rw [cond, ContinuousLinearEquiv.condNumber_eq, mul_comm]

/-- **Section 2.4.2** of [han2009theoretical], the lower bound. Let $V \neq \{0\}$ and $W$ be normed
spaces over $\mathbb{K}$, and let $L$ be a bijection of $V$ onto $W$ with $L$ and $L^{-1}$
bounded. Then $\operatorname{cond}(L) \ge 1$.

The proof uses $\|I\| = 1$ for $I = L^{-1} L$, which needs $V \neq \{0\}$. -/
theorem one_le_cond [Nontrivial V] (L : V ≃L[𝕜] W) : 1 ≤ cond L := by
  rw [cond, mul_comm]
  exact L.one_le_norm_mul_norm_symm

/-- **Equation (2.4.1)** of [han2009theoretical], the relative error bound. Let $V$ and $W$ be
normed spaces over $\mathbb{K}$, and let $L$ be a bijection of $V$ onto $W$ with $L$ and
$L^{-1}$ bounded. Let $v \neq 0$ and $\hat v$ be in $V$, and let $w = Lv$ and
$\hat w = L \hat v$. Then
$$\frac{\|v - \hat v\|}{\|v\|} \le \operatorname{cond}(L) \, \frac{\|w - \hat w\|}{\|w\|}.$$
-/
theorem equation_2_4_1 (L : V ≃L[𝕜] W) {v vhat : V} (hv : v ≠ 0) :
    ‖v - vhat‖ / ‖v‖ ≤ cond L * (‖L v - L vhat‖ / ‖L v‖) := by
  have ha : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hb : 0 < ‖L v‖ := norm_pos_iff.2 fun h => hv (by simpa using congrArg L.symm h)
  have hd : ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ :=
    stability_of_isomorphism L v vhat
  have hq : ‖L v‖ ≤ ‖(L : V →L[𝕜] W)‖ * ‖v‖ := (L : V →L[𝕜] W).le_opNorm v
  rw [cond, mul_div_assoc', div_le_div_iff₀ ha hb]
  have hp : 0 ≤ ‖(L.symm : W →L[𝕜] V)‖ := norm_nonneg _
  have hr : 0 ≤ ‖L v - L vhat‖ := norm_nonneg _
  nlinarith [mul_nonneg hp hr]

/-! ### Theorems 2.4.4 and 2.4.5: uniform boundedness -/

/-- **Theorem 2.4.4** of [han2009theoretical] (principle of uniform boundedness). Let $V$ be a
Banach space and $W$ a normed space over $\mathbb{K}$, and let $L_n \in \mathcal{L}(V, W)$ for
$n \ge 0$. If for every $v \in V$ there is a $C_v$ with $\|L_n v\| \le C_v$ for all $n$, then
there is a $C$ with $\|L_n\| \le C$ for all $n$.

The proof is Mathlib's `banach_steinhaus`. -/
theorem theorem_2_4_4 [CompleteSpace V] (Ln : ℕ → V →L[𝕜] W) (h : ∀ v, ∃ C, ∀ n, ‖Ln n v‖ ≤ C) :
    ∃ C, ∀ n, ‖Ln n‖ ≤ C :=
  banach_steinhaus h

/-- The sufficiency half of **Theorem 2.4.5** of [han2009theoretical], in the generality in which it
is proved. Let $V$ and $W$ be normed spaces over $\mathbb{K}$, let
$L, L_n \in \mathcal{L}(V, W)$, and let $S \subseteq V$ be dense. Assume that $\|L_n\| \le C$
for all $n$ and that $L_n v \to Lv$ for every $v \in S$. Then $L_n v \to Lv$ for every
$v \in V$.

Neither the completeness of $V$ nor the linearity of $S$ is used. This is the $\varepsilon/3$
argument of the book, and it is the backbone's
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded` of
`Numlib.Analysis.Normed.Operator.BanachSteinhaus`, which states it along any filter on any index
type. -/
theorem tendsto_of_tendsto_on_dense_of_bounded {s : Set V} (hs : Dense s) {L : V →L[𝕜] W}
    {Ln : ℕ → V →L[𝕜] W} {C : ℝ} (hC : ∀ n, ‖Ln n‖ ≤ C)
    (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) (v : V) :
    Tendsto (fun n => Ln n v) atTop (𝓝 (L v)) :=
  ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hs hC h v

/-- **Theorem 2.4.5** of [han2009theoretical] (Banach–Steinhaus theorem). Let $V$ be a Banach space
and $W$ a normed space over $\mathbb{K}$, let $L, L_n \in \mathcal{L}(V, W)$, and let $V_0$ be a
dense subspace of $V$. Then $L_n v \to Lv$ for every $v \in V$ if and only if (a) $L_n v \to Lv$
for every $v \in V_0$, and (b) there is a $C$ with $\|L_n\| \le C$ for all $n$.

The proof is the backbone's `ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace`,
which needs only a dense set. -/
theorem theorem_2_4_5 [CompleteSpace V] (L : V →L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (V₀ : Submodule 𝕜 V)
    (hV₀ : Dense (V₀ : Set V)) :
    (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔
      (∀ v ∈ V₀, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C :=
  ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace hV₀ L Ln

/-!
### Section 2.4.4: convergence of numerical quadrature

The book studies the quadrature functionals $L_n v = \sum_{i=0}^{n} w_i^{(n)} v(x_i^{(n)})$ on
$C[0, 1]$, which approximate $Lv = \int_0^1 w(x) v(x) \, dx$. Both results specialize the backbone
to $[0, 1]$. The quadrature functional is `Quadrature.functional` of
`Numlib.Approximation.Quadrature`.
-/

/-- **Equation (2.4.4)** of [han2009theoretical] (Exercise 2.4.2). Let $x_1, \dots, x_n \in [0, 1]$
be distinct and let $w_1, \dots, w_n \in \mathbb{R}$. Then the quadrature functional
$L_n v = \sum_i w_i v(x_i)$ on $C[0, 1]$ has norm
$$\|L_n\| = \sum_{i=1}^n |w_i|.$$
-/
theorem equation_2_4_4 {n : ℕ} (w : Fin n → ℝ) {x : Fin n → Set.Icc (0 : ℝ) 1}
    (hx : Function.Injective x) : ‖Quadrature.functional w x‖ = ∑ i, |w i| :=
  Quadrature.norm_functional w hx

/-- **Section 2.4.4** and **Exercise 2.4.3** of [han2009theoretical], the convergence of numerical
quadrature. Let $L$ be a bounded linear functional on $C[0, 1]$. For each $k$ let
$L_k v = \sum_{i} w_i^{(k)} v(x_i^{(k)})$ be a quadrature rule with distinct nodes
$x_i^{(k)} \in [0, 1]$ that is exact for $L$ on the polynomials of degree at most $d_k$, and let
$d_k \to \infty$. Then (a) $L_k v \to Lv$ for every $v \in C[0, 1]$ if and only if there is a
$C$ with $\sum_i |w_i^{(k)}| \le C$ for all $k$, and (b) if all the weights $w_i^{(k)}$ are
nonnegative, then $L_k v \to Lv$ for every $v \in C[0, 1]$.

**Generalization.** The book takes $Lv = \int_0^1 w(x) v(x) \, dx$. The statement holds for
every bounded linear functional $L$ on $C[0, 1]$.

The rule $L_k$ is `Quadrature.functional (w k) (x k)` with `m k` nodes, and exactness is
`Quadrature.IsExactOn`. -/
theorem quadrature_convergence {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc (0 : ℝ) 1} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, Quadrature.IsExactOn L (w k) (x k) (d k)) :
    ((∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) ↔
        ∃ C, ∀ k, ∑ i, |w k i| ≤ C) ∧
      ((∀ k i, 0 ≤ w k i) →
        ∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) :=
  ⟨Quadrature.tendsto_iff_bddAbove_sum_abs hx hd hexact,
    fun hw => Quadrature.tendsto_of_nonneg hx hd hexact hw⟩

/-! ### Example 2.4.2: the differentiation operator on $C^1[0, 1]$ and its extension -/

section Example242

open MeasureTheory Set

/-- **Example 2.4.2** of [han2009theoretical], the bound on $C^1[0, 1]$. For every
$v \in C^1[0, 1]$,
$$\|v'\|_{L^2(0, 1)} \le \|v\|_{1,2},$$
where $\|v\|_{1,2} = (\|v\|_2^2 + \|v'\|_2^2)^{1/2}$ is the norm of $v$ in $H^1(0, 1)$. Thus the
differentiation operator $D : C^1[0, 1] \to L^2(0, 1)$ has norm at most $1$ for the norm
$\|\cdot\|_{1,2}$.

The derivative $v'$ in $L^2(0, 1)$ is `ContDiffMapIcc.derivLp v 1`, and $v$ is embedded in
$H^1(0, 1)$ by `ContDiffMapIcc.toSobolevInterval`. -/
theorem example_2_4_2_norm_le (v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1) :
    ‖v.derivLp 1‖ ≤
      ‖ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1 v‖ := by
  rw [← ContDiffMapIcc.deriv_toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one v 1]
  exact SobolevInterval.norm_deriv_le _ 1

/-- **Example 2.4.2** of [han2009theoretical], the completion. The space $C^1[0, 1]$ is dense in
$H^1(0, 1)$. Since $H^1(0, 1)$ is complete and the inclusion carries $\|\cdot\|_{1,2}$ to the
norm of $H^1(0, 1)$, the space $H^1(0, 1)$ is the completion of $C^1[0, 1]$ in the norm
$\|\cdot\|_{1,2}$.

The inclusion is `ContDiffMapIcc.toSobolevInterval`, which is injective by
`ContDiffMapIcc.toSobolevInterval_injective`. -/
theorem example_2_4_2_dense :
    DenseRange (ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1) :=
  ContDiffMapIcc.denseRange_toSobolevInterval_one zero_lt_one

/-- **Example 2.4.2** of [han2009theoretical], the extension. There is a unique bounded linear
operator $\hat D : H^1(0, 1) \to L^2(0, 1)$ with $\hat D v = v'$ for every $v \in C^1[0, 1]$.

This is the extension of Theorem 2.4.1, once $H^1(0, 1)$ is identified with the completion of
$C^1[0, 1]$ by `AtkinsonHan.Chapter02.example_2_4_2_dense`. The extension is the weak derivative
`SobolevInterval.derivL`, the "more concrete realization" that the book promises for Chapter 7,
and $\|\hat D\| \le 1$ by `AtkinsonHan.Chapter02.example_2_4_2_opNorm_le`. -/
theorem example_2_4_2 :
    ∃! D : SobolevInterval 1 0 1 →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1,
        D (ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1 v) =
          v.derivLp 1 := by
  refine ⟨SobolevInterval.derivL 1 0 1 1, fun v => rfl, fun D hD => ?_⟩
  refine ContinuousLinearMap.coe_injective (DFunLike.coe_injective ?_)
  exact example_2_4_2_dense.equalizer D.continuous
    (SobolevInterval.derivL 1 0 1 1).continuous (funext fun v => hD v)

/-- **Example 2.4.2** of [han2009theoretical], the norm of the extension. The weak derivative
$\hat D : H^1(0, 1) \to L^2(0, 1)$, $\hat D v = v'$, has norm $\|\hat D\| \le 1$.

This is what Theorem 2.4.1 and `AtkinsonHan.Chapter02.example_2_4_2_norm_le` give. The operator
is `SobolevInterval.derivL 1 0 1 1`. -/
theorem example_2_4_2_opNorm_le : ‖SobolevInterval.derivL 1 (0 : ℝ) 1 1‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Example242

end AtkinsonHan.Chapter02
