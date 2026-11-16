/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Numlib.IntegralEquations.L2Kernel

/-!
# Atkinson and Han, Section 2.6: Adjoint operators

This module formalizes Section 2.6 of [han2009theoretical]. Let $V$ and $W$ be Hilbert spaces. Every
$L \in \mathcal{L}(V, W)$ has a unique adjoint $L^* \in \mathcal{L}(W, V)$ with
$$(Lv, w)_W = (v, L^* w)_V \quad \text{for all } v \in V, \ w \in W. \qquad (2.6.1)$$
The adjoint is involutive, conjugate linear and reverses products, and $\|L^*\| = \|L\|$. An
operator $L \in \mathcal{L}(V)$ is self-adjoint if $L^* = L$. Real linear combinations, powers and
real polynomials of self-adjoint operators are self-adjoint, and a product of two self-adjoint
operators is self-adjoint if and only if they commute. The norm of a self-adjoint operator is
$$\|L\| = \sup_{\|v\| = 1} |(Lv, v)|.$$
The example of the section is the integral operator of a square-integrable kernel on $L^2(a, b)$,
whose adjoint is the integral operator of the transposed kernel.

The adjoint is Mathlib's `ContinuousLinearMap.adjoint`. The integral operator is the backbone's
`IntegralOperator.l2KernelCLM` of `Numlib.IntegralEquations.L2Kernel`.

## Main results

* Equation (2.6.1), `AtkinsonHan.Chapter02.equation_2_6_1`: the adjoint exists and is unique.
* Equation (2.6.3) and Exercise 2.6.1, `AtkinsonHan.Chapter02.equation_2_6_3`: $(L^*)^* = L$,
  $(\alpha_1 L_1 + \alpha_2 L_2)^* = \bar\alpha_1 L_1^* + \bar\alpha_2 L_2^*$ and
  $(ML)^* = L^* M^*$.
* Equations (2.6.2) and (2.6.4), `AtkinsonHan.Chapter02.equation_2_6_4`: $\|L^*\| = \|L\|$.
* Example 2.6.1, `AtkinsonHan.Chapter02.example_2_6_1`, `AtkinsonHan.Chapter02.example_2_6_1_apply`,
  `AtkinsonHan.Chapter02.example_2_6_1_adjoint` and
  `AtkinsonHan.Chapter02.example_2_6_1_isSelfAdjoint`: the integral operator $K$ of a kernel
  $k \in L^2$ on $L^2(a, b)$ has $\|K\| \le \|k\|_{L^2}$, its adjoint has the transposed kernel, and
  $K$ is self-adjoint if and only if $k$ is symmetric.
* Proposition 2.6.2, `AtkinsonHan.Chapter02.proposition_2_6_2`: a real linear combination of
  self-adjoint operators is self-adjoint.
* Proposition 2.6.3, `AtkinsonHan.Chapter02.proposition_2_6_3`: a product of two self-adjoint
  operators is self-adjoint if and only if they commute.
* Corollary 2.6.4, `AtkinsonHan.Chapter02.corollary_2_6_4` and
  `AtkinsonHan.Chapter02.corollary_2_6_4_polynomial`: powers and real polynomials of a self-adjoint
  operator are self-adjoint.
* Theorem 2.6.5, `AtkinsonHan.Chapter02.theorem_2_6_5`: $\|L\| = \sup_{\|v\| = 1} |(Lv, v)|$ for a
  self-adjoint $L$, (2.6.5).
* Exercise 2.6.3, `AtkinsonHan.Chapter02.exercise_2_6_3`: $|(Lu, v)| \le \sup_{\|w\| = 1} |(Lw, w)|
  \, \|u\| \, \|v\|$ for a self-adjoint $L$.

## Conventions

* The book's inner product $(u, v)$ is linear in its first argument, and Mathlib's `inner 𝕜 u v` is
  linear in its second argument. Therefore the book's $(u, v)$ is written `inner 𝕜 v u`, and the
  relation (2.6.1) reads with its arguments reversed.
* For a self-adjoint $L$ the number $(Lv, v)$ is real. It is written `RCLike.re (inner 𝕜 v (L v))`.
* Theorem 2.6.5 and Exercise 2.6.3 assume $V \neq \{0\}$, which is `[Nontrivial V]`: on the zero
  space the unit sphere is empty, and the supremum that the book writes has no meaning.
* `AtkinsonHan.Chapter02.equation_2_6_1` is the displayed relation (2.6.1), which defines the
  adjoint in general. It is not Example 2.6.1, and neither it nor
  `AtkinsonHan.Chapter02.equation_2_6_3` and `AtkinsonHan.Chapter02.equation_2_6_4` concerns
  integral operators. Example 2.6.1 is the group of declarations
  `AtkinsonHan.Chapter02.example_2_6_1…`.

## Implementation notes

* The bound of Example 2.6.1 is also (2.8.16)–(2.8.17) of Section 2.8.3, where $\|k\|_{L^2}$ is
  called the Hilbert–Schmidt norm of $K$. `AtkinsonHan.Chapter02.example_2_6_1` stands for both.
* In Example 2.6.1, $L^2(a, b)$ is `Lp ℝ 2 (volume.restrict (Icc a b))`, and the kernel is a
  function on $\mathbb{R}^2$ that is square integrable on $[a, b]^2$.

## Deviations from the source

* **Section 2.6** (generalization). The book restricts the section to real scalars. The statements
  about the adjoint and about self-adjoint operators hold over $\mathbb{R}$ and over $\mathbb{C}$,
  because Mathlib's adjoint is defined over both. See `AtkinsonHan.Chapter02.equation_2_6_1`.
-/

open Metric RCLike Set
open scoped InnerProduct

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

/-! ### (2.6.1)–(2.6.4): the adjoint and its algebra -/

/-- **Equation (2.6.1)** of [han2009theoretical]. Let $V$ and $W$ be Hilbert spaces over
$\mathbb{K}$ and let $L \in \mathcal{L}(V, W)$. Then there is a unique
$L^* \in \mathcal{L}(W, V)$ with
$$(Lv, w)_W = (v, L^* w)_V \quad \text{for all } v \in V, \ w \in W.$$

**Generalization.** The book takes real scalars. The statement holds over $\mathbb{R}$ and over
$\mathbb{C}$.

The book's $(Lv, w)$ is `inner 𝕜 w (L v)`. The operator $L^*$ is Mathlib's
`ContinuousLinearMap.adjoint`, which is constructed from the Riesz representation theorem,
Theorem 2.5.8. -/
theorem equation_2_6_1 (L : V →L[𝕜] W) :
    ∃! M : W →L[𝕜] V, ∀ (v : V) (w : W), inner 𝕜 w (L v) = inner 𝕜 (M w) v := by
  refine ⟨ContinuousLinearMap.adjoint L, fun v w => ?_, fun M hM => ?_⟩
  · exact (ContinuousLinearMap.adjoint_inner_left L v w).symm
  · exact (ContinuousLinearMap.eq_adjoint_iff M L).mpr fun w v => (hM v w).symm

/-- **Equation (2.6.3)** and **Exercise 2.6.1** of [han2009theoretical], the algebra of adjoints.
Let $U$, $V$ and $W$ be Hilbert spaces over $\mathbb{K}$, let
$L, L_1, L_2 \in \mathcal{L}(V, W)$, let $M \in \mathcal{L}(W, U)$, and let
$\alpha_1, \alpha_2 \in \mathbb{K}$. Then
$$(L^*)^* = L, \qquad (\alpha_1 L_1 + \alpha_2 L_2)^* = \bar\alpha_1 L_1^* + \bar\alpha_2 L_2^*,
  \qquad (ML)^* = L^* M^*.$$

**Generalization.** The book takes real scalars, where $\bar\alpha_i = \alpha_i$. The statement
holds over $\mathbb{R}$ and over $\mathbb{C}$. -/
theorem equation_2_6_3 {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
    (L : V →L[𝕜] W) (α₁ α₂ : 𝕜) (L₁ L₂ : V →L[𝕜] W) (M : W →L[𝕜] U) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint L) = L ∧
      ContinuousLinearMap.adjoint (α₁ • L₁ + α₂ • L₂) =
        starRingEnd 𝕜 α₁ • ContinuousLinearMap.adjoint L₁ +
          starRingEnd 𝕜 α₂ • ContinuousLinearMap.adjoint L₂ ∧
      ContinuousLinearMap.adjoint (M ∘L L) =
        ContinuousLinearMap.adjoint L ∘L ContinuousLinearMap.adjoint M :=
  ⟨ContinuousLinearMap.adjoint_adjoint L, by rw [map_add, map_smulₛₗ, map_smulₛₗ],
    ContinuousLinearMap.adjoint_comp M L⟩

/-- **Equations (2.6.2)** and **(2.6.4)** of [han2009theoretical]. Let $V$ and $W$ be Hilbert spaces
over $\mathbb{K}$ and let $L \in \mathcal{L}(V, W)$. Then $\|L^*\| = \|L\|$.

The book proves $\|L^*\| \le \|L\|$ and applies this to $L^*$, using $(L^*)^* = L$. -/
theorem equation_2_6_4 (L : V →L[𝕜] W) : ‖ContinuousLinearMap.adjoint L‖ = ‖L‖ :=
  ContinuousLinearMap.adjoint.norm_map L

/-! ### Self-adjoint operators -/

private theorem isSelfAdjoint_ofReal (α : ℝ) : IsSelfAdjoint (α : 𝕜) := by
  simp [isSelfAdjoint_iff, RCLike.star_def]

/-- **Proposition 2.6.2** of [han2009theoretical]. Let $V$ be a Hilbert space over $\mathbb{K}$, let
$L_1, L_2 \in \mathcal{L}(V)$ be self-adjoint, and let $\alpha_1, \alpha_2 \in \mathbb{R}$. Then
$\alpha_1 L_1 + \alpha_2 L_2$ is self-adjoint. -/
theorem proposition_2_6_2 {L₁ L₂ : V →L[𝕜] V} (h₁ : IsSelfAdjoint L₁) (h₂ : IsSelfAdjoint L₂)
    (α₁ α₂ : ℝ) : IsSelfAdjoint ((α₁ : 𝕜) • L₁ + (α₂ : 𝕜) • L₂) :=
  ((isSelfAdjoint_ofReal α₁).smul h₁).add ((isSelfAdjoint_ofReal α₂).smul h₂)

/-- **Proposition 2.6.3** of [han2009theoretical]. Let $V$ be a Hilbert space over $\mathbb{K}$ and
let $L_1, L_2 \in \mathcal{L}(V)$ be self-adjoint. Then $L_1 L_2$ is self-adjoint if and only if
$L_1 L_2 = L_2 L_1$.

The proof uses $(L_1 L_2)^* = L_2 L_1$. -/
theorem proposition_2_6_3 {L₁ L₂ : V →L[𝕜] V} (h₁ : IsSelfAdjoint L₁) (h₂ : IsSelfAdjoint L₂) :
    IsSelfAdjoint (L₁ ∘L L₂) ↔ L₁ ∘L L₂ = L₂ ∘L L₁ := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp, h₁.adjoint_eq,
    h₂.adjoint_eq]
  exact eq_comm

/-- **Corollary 2.6.4** of [han2009theoretical], powers. Let $V$ be a Hilbert space over
$\mathbb{K}$ and let $L \in \mathcal{L}(V)$ be self-adjoint. Then $L^n$ is self-adjoint for
every $n \ge 0$. -/
theorem corollary_2_6_4 {L : V →L[𝕜] V} (hL : IsSelfAdjoint L) (n : ℕ) : IsSelfAdjoint (L ^ n) :=
  hL.pow n

/-- **Corollary 2.6.4** of [han2009theoretical], polynomials. Let $V$ be a Hilbert space over
$\mathbb{K}$, let $L \in \mathcal{L}(V)$ be self-adjoint, and let
$c_0, \dots, c_{n-1} \in \mathbb{R}$. Then the operator $p(L) = \sum_{i=0}^{n-1} c_i L^i$ is
self-adjoint. -/
theorem corollary_2_6_4_polynomial {L : V →L[𝕜] V} (hL : IsSelfAdjoint L) (n : ℕ) (c : ℕ → ℝ) :
    IsSelfAdjoint (∑ i ∈ Finset.range n, (c i : 𝕜) • L ^ i) := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) (IsSelfAdjoint.zero _) ?_
  exact fun i _ => (isSelfAdjoint_ofReal (c i)).smul (hL.pow i)

/-! ### Theorem 2.6.5 -/

omit [CompleteSpace V] in
private theorem abs_re_inner_eq_abs_rayleigh (T : V →L[𝕜] V) {v : V} (hv : ‖v‖ = 1) :
    |re (inner 𝕜 v (T v))| = |T.rayleighQuotient v| := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    ← inner_conj_symm (T v) v, RCLike.conj_re, hv]
  norm_num

omit [CompleteSpace V] in
private theorem bddAbove_sphere (T : V →L[𝕜] V) :
    BddAbove (Set.range fun v : sphere (0 : V) 1 => |re (inner 𝕜 (v : V) (T v))|) := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  dsimp only
  rw [abs_re_inner_eq_abs_rayleigh T (mem_sphere_zero_iff_norm.mp v.2)]
  exact T.rayleighQuotient_le_norm (v : V)

section Norm

variable [Nontrivial V] {L : V →L[𝕜] V}

/-- **Theorem 2.6.5** of [han2009theoretical], with (2.6.5). Let $V \neq \{0\}$ be a Hilbert space
over $\mathbb{K}$ and let $L \in \mathcal{L}(V)$ be self-adjoint. Then
$$\|L\| = \sup_{\|v\| = 1} |(Lv, v)|.$$

The number $(Lv, v)$ is `RCLike.re (inner 𝕜 v (L v))`, which is the whole inner product because
$L$ is self-adjoint. The supremum is over the unit sphere `Metric.sphere 0 1`. -/
theorem theorem_2_6_5 (hL : IsSelfAdjoint L) :
    ‖L‖ = ⨆ v : sphere (0 : V) 1, |re (inner 𝕜 (v : V) (L v))| := by
  have hne : Nonempty (sphere (0 : V) 1) := NormedSpace.sphere_nonempty_rclike 𝕜 zero_le_one
  refine le_antisymm ?_ ?_
  · rw [L.norm_eq_iSup_rayleighQuotient hL.isSymmetric]
    refine ciSup_le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · obtain ⟨v⟩ := hne
      exact le_trans (by simp) (le_ciSup (bddAbove_sphere L) v)
    · have hv : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := by
        rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have hne' : (‖x‖⁻¹ : 𝕜) ≠ 0 :=
        inv_ne_zero (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
      have hmem : (‖x‖⁻¹ : 𝕜) • x ∈ sphere (0 : V) 1 := mem_sphere_zero_iff_norm.mpr hv
      have hle := le_ciSup (bddAbove_sphere L) (⟨_, hmem⟩ : sphere (0 : V) 1)
      rwa [abs_re_inner_eq_abs_rayleigh L hv, L.rayleigh_smul x hne'] at hle
  · refine ciSup_le fun v => ?_
    rw [abs_re_inner_eq_abs_rayleigh L (mem_sphere_zero_iff_norm.mp v.2)]
    exact L.rayleighQuotient_le_norm (v : V)

/-- **Exercise 2.6.3** of [han2009theoretical]. Let $V \neq \{0\}$ be a Hilbert space over
$\mathbb{K}$ and let $L \in \mathcal{L}(V)$ be self-adjoint. Then for all $u, v \in V$,
$$|(Lu, v)| \le \Big( \sup_{\|w\| = 1} |(Lw, w)| \Big) \|u\| \, \|v\|.$$
Thus the quantity of Theorem 2.6.5 bounds the whole sesquilinear form $(u, v) \mapsto (Lu, v)$. -/
theorem exercise_2_6_3 (hL : IsSelfAdjoint L) (u v : V) :
    ‖inner 𝕜 v (L u)‖ ≤ (⨆ w : sphere (0 : V) 1, |re (inner 𝕜 (w : V) (L w))|) * ‖u‖ * ‖v‖ := by
  rw [← theorem_2_6_5 hL]
  calc ‖inner 𝕜 v (L u)‖ ≤ ‖v‖ * ‖L u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖L‖ * ‖u‖) := by gcongr; exact L.le_opNorm u
    _ = ‖L‖ * ‖u‖ * ‖v‖ := by ring

end Norm

/-! ### Example 2.6.1: the integral operator of a square-integrable kernel -/

section L2Kernel

open MeasureTheory Real

variable {a b : ℝ} {k : ℝ × ℝ → ℝ}
  (hk : MemLp k 2 ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))))

include hk

/-- **Example 2.6.1** of [han2009theoretical], the bound. Let $a, b \in \mathbb{R}$ and let $k$ be a
real function with
$$B = \Big( \int_a^b \int_a^b |k(x, y)|^2 \, dx \, dy \Big)^{1/2} < \infty.$$
Then the integral operator $Kv(x) = \int_a^b k(x, y) v(y) \, dy$ is a bounded operator on
$L^2(a, b)$ with $\|K\| \le B$.

This is also (2.8.16)–(2.8.17) of Section 2.8.3, where $B$ is called the Hilbert–Schmidt norm of
$K$. The operator is `IntegralOperator.l2KernelCLM`, and the hypothesis $B < \infty$ is
`MemLp k 2` for the product measure on $[a, b]^2$. -/
theorem example_2_6_1 : ‖IntegralOperator.l2KernelCLM hk‖ ≤
    √(∫ p, k p ^ 2 ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)))) :=
  IntegralOperator.norm_l2KernelCLM_le hk

/-- **Example 2.6.1** of [han2009theoretical], the formula. Let $k$ be square integrable on
$[a, b]^2$ and let $K$ be its integral operator on $L^2(a, b)$. For every $v \in L^2(a, b)$,
$$Kv(x) = \int_a^b k(x, y) v(y) \, dy \quad \text{for almost every } x \in [a, b].$$
The equality holds only almost everywhere, because an element of $L^2(a, b)$ is a class of
functions that agree almost everywhere. -/
theorem example_2_6_1_apply (v : Lp ℝ 2 (volume.restrict (Icc a b))) :
    IntegralOperator.l2KernelCLM hk v =ᵐ[volume.restrict (Icc a b)]
      fun x => ∫ y, k (x, y) * v y ∂(volume.restrict (Icc a b)) :=
  IntegralOperator.l2KernelCLM_apply_ae hk v

/-- **Example 2.6.1** of [han2009theoretical], the adjoint. Let $k$ be square integrable on
$[a, b]^2$ and let $K$ be its integral operator on $L^2(a, b)$. For every $v \in L^2(a, b)$,
$$K^* v(y) = \int_a^b k(x, y) v(x) \, dx \quad \text{for almost every } y \in [a, b].$$
Thus $K^*$ is the integral operator of the transposed kernel $(y, x) \mapsto k(x, y)$. -/
theorem example_2_6_1_adjoint (v : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ContinuousLinearMap.adjoint (IntegralOperator.l2KernelCLM hk) v
        =ᵐ[volume.restrict (Icc a b)]
      fun y => ∫ x, k (x, y) * v x ∂(volume.restrict (Icc a b)) := by
  rw [IntegralOperator.adjoint_l2KernelCLM hk]
  exact IntegralOperator.l2KernelCLM_apply_ae _ v

/-- **Example 2.6.1** of [han2009theoretical], self-adjointness. Let $k$ be square integrable on
$[a, b]^2$ and let $K$ be its integral operator on $L^2(a, b)$. Then $K$ is self-adjoint if and
only if $k(x, y) = k(y, x)$ for almost every $(x, y) \in [a, b]^2$.

The condition holds only almost everywhere, because two kernels that agree almost everywhere
give the same operator. -/
theorem example_2_6_1_isSelfAdjoint :
    IsSelfAdjoint (IntegralOperator.l2KernelCLM hk) ↔
      ∀ᵐ p ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))),
        k p = k (p.2, p.1) :=
  IntegralOperator.isSelfAdjoint_l2KernelCLM_iff hk

end L2Kernel

end AtkinsonHan.Chapter02
