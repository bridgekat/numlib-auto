/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.IntegralEquations.Basic

/-!
# Atkinson and Han, Section 2.3: The geometric series theorem and its variants

This module formalizes Section 2.3 of [han2009theoretical]. Let $V$ be a Banach space and
$L \in \mathcal{L}(V)$. The geometric series theorem says that if $\|L\| < 1$, then $I - L$ is a
bijection of $V$ onto $V$ with bounded inverse
$$(I - L)^{-1} = \sum_{n=0}^\infty L^n, \qquad \|(I - L)^{-1}\| \le \frac{1}{1 - \|L\|}.$$
The section applies it to the equation of the second kind $(\lambda I - K) u = f$, extends it to
operators with $\|L^m\| < 1$ for some $m \ge 1$, and proves the perturbation theorem: an operator
close enough to an invertible one is invertible. With the perturbation theorem, consistency and
stability of a sequence of approximating equations give convergence of their solutions (2.3.16). The
concrete examples are integral equations on $C[a, b]$, among them the equation (2.3.17) with the
kernel $\sin(xy)$.

The proofs specialize the results on inverses in a normed ring of
`Numlib.Analysis.Normed.Ring.Inverse`, the Neumann series of Mathlib, and the integral operators of
`Numlib.IntegralEquations.Basic`.

## Main results

* Theorem 2.3.1, `AtkinsonHan.Chapter02.theorem_2_3_1`: the geometric series theorem, with (2.3.2).
* Equations (2.3.4) and (2.3.5), `AtkinsonHan.Chapter02.equation_2_3_4` and
  `AtkinsonHan.Chapter02.equation_2_3_5`: the solution of $(I - L) u = f$ depends Lipschitz
  continuously on $f$, and the partial sums of the Neumann series converge to it.
* Example 2.3.2, `AtkinsonHan.Chapter02.example_2_3_2` and
  `AtkinsonHan.Chapter02.example_2_3_2_bound`: if $\|K\| < |\lambda|$, then $\lambda I - K$ is
  invertible and $\|u\| \le \|f\| / (|\lambda| - \|K\|)$.
* Example 2.3.2, `AtkinsonHan.Chapter02.example_2_3_2_integral`: the same for an integral operator
  with continuous kernel on $C[a, b]$, with $\|K\|$ given by (2.2.8).
* Corollary 2.3.3, `AtkinsonHan.Chapter02.corollary_2_3_3`: if $\|L^m\| < 1$ for some $m \ge 1$,
  then $I - L$ is invertible, with the bound (2.3.11).
* Example 2.3.4, `AtkinsonHan.Chapter02.example_2_3_4`: if $\|L^k\| \to 0$, then $I - L$ is
  invertible.
* Example 2.3.4, `AtkinsonHan.Chapter02.example_2_3_4_volterra`: the Volterra operator $L$ with
  continuous kernel satisfies $\|L^m\| \le (\|k\|_\infty (b - a))^m / m!$, and $\lambda I - L$ is
  invertible for every $\lambda \neq 0$.
* Theorem 2.3.5, `AtkinsonHan.Chapter02.theorem_2_3_5`: the perturbation theorem, with (2.3.13),
  (2.3.14) and (2.3.15).
* Equation (2.3.16), `AtkinsonHan.Chapter02.equation_2_3_16` and
  `AtkinsonHan.Chapter02.convergence_of_consistent_stable`: if $L_n \to L$, the approximating
  equations are uniquely solvable for large $n$, and consistency with stability gives convergence.
* Example 2.3.6, `AtkinsonHan.Chapter02.example_2_3_6`: the integral operator with kernel $\sin(xy)$
  on $C[0, 1]$ has norm $1 - \cos 1$ (2.3.18), so (2.3.17) is uniquely solvable for
  $|\lambda| > 1 - \cos 1$.
* Example 2.3.6, `AtkinsonHan.Chapter02.example_2_3_6_norm_sub`: the integral operator with kernel
  $xy - \sin(xy)$, the difference between (2.3.17) and (2.3.19), has norm $\cos 1 - 1/2$.

## Implementation notes

* The book says that $L$ is "a bijection of $V$ onto $W$ whose inverse is bounded". In Lean this is
  `∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L`, and the inverse of $L$ is `e.symm`. For $V = W$, the
  theorem `AtkinsonHan.Chapter02.isUnit_iff_exists_continuousLinearEquiv` identifies this with
  `IsUnit L` in the ring $\mathcal{L}(V)$, which the backbone uses.
* `AtkinsonHan.Chapter02.corollary_2_3_3` keeps the hypothesis $m \ge 1$ of the book, although the
  proof does not use it.
* In the integral examples the kernel is a continuous function on the square, and the kernel of
  Example 2.3.6 is described by a hypothesis on its values, not constructed.

## Not formalized

* **Example 2.3.6, second half.** The explicit inverse (2.3.20) of the degenerate kernel equation
  (2.3.19), the bound $\|L^{-1}\| \le \frac{1}{|\lambda|} \big(1 + \frac{1}{2 |\lambda - 1/3|}\big)$
  that follows from it, and the resulting condition (2.3.21) with its numerical root
  $\lambda_0 \approx -0.0881$. The book leaves this analysis to the reader as Exercise 2.3.5, gives
  the constants to two decimals only, and does not use them later. The two operator norms on which
  the analysis rests, $\|K\|$ and $\|L - M\|$, are formalized.
-/

open Filter Topology

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

section Units

/-- Let $V$ be a normed space over $\mathbb{K}$ and $L \in \mathcal{L}(V)$. Then $L$ is a unit of
the ring $\mathcal{L}(V)$ if and only if $L$ is a bijection of $V$ onto $V$ with bounded
inverse, that is, the underlying operator of a continuous linear equivalence.

With this theorem the results on inverses in a normed ring of
`Numlib.Analysis.Normed.Ring.Inverse` prove the statements of Section 2.3 of
[han2009theoretical]. -/
theorem isUnit_iff_exists_continuousLinearEquiv (L : V →L[𝕜] V) :
    IsUnit L ↔ ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = L := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨ContinuousLinearEquiv.ofUnit u, ContinuousLinearEquiv.coe_ofUnit u⟩
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩

/-- A unit $L$ of $\mathcal{L}(V)$ is a continuous linear equivalence $e$ whose inverse $e^{-1}$ is
`Ring.inverse L`. -/
private theorem exists_equiv_of_isUnit {L : V →L[𝕜] V} (h : IsUnit L) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = L ∧ (e.symm : V →L[𝕜] V) = Ring.inverse L := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨ContinuousLinearEquiv.ofUnit u, ContinuousLinearEquiv.coe_ofUnit u,
    ContinuousLinearEquiv.coe_ofUnit_symm u⟩

/-- If $e$ is a continuous linear equivalence of $V$ and $\lambda \neq 0$, then $\lambda e$ is a
continuous linear equivalence with inverse $\lambda^{-1} e^{-1}$. -/
private theorem exists_smul_equiv {lam : 𝕜} (hlam : lam ≠ 0) (e₀ : V ≃L[𝕜] V) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = lam • (e₀ : V →L[𝕜] V) ∧
      (e.symm : V →L[𝕜] V) = lam⁻¹ • (e₀.symm : V →L[𝕜] V) := by
  have hcancel : (e₀ : V →L[𝕜] V) * (e₀.symm : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.apply_symm_apply x
  have hcancel' : (e₀.symm : V →L[𝕜] V) * (e₀ : V →L[𝕜] V) = 1 := by
    ext x; exact e₀.symm_apply_apply x
  refine ⟨ContinuousLinearEquiv.ofUnit
    ⟨lam • (e₀ : V →L[𝕜] V), lam⁻¹ • (e₀.symm : V →L[𝕜] V), ?_, ?_⟩,
    ContinuousLinearEquiv.coe_ofUnit _, ?_⟩
  · rw [smul_mul_smul_comm, hcancel, mul_inv_cancel₀ hlam, one_smul]
  · rw [smul_mul_smul_comm, hcancel', inv_mul_cancel₀ hlam, one_smul]
  · rw [ContinuousLinearEquiv.coe_ofUnit_symm, Ring.inverse_unit]
    rfl

/-- Every operator on the zero space has norm $0$. -/
private theorem norm_eq_zero_of_subsingleton [Subsingleton V] (T : V →L[𝕜] V) : ‖T‖ = 0 := by
  have : T = 0 := by ext x; exact Subsingleton.elim _ _
  rw [this, norm_zero]

end Units

/-! ### Theorem 2.3.1 -/

/-- **Theorem 2.3.1** of [han2009theoretical] (geometric series theorem). Let $V$ be a Banach space
over $\mathbb{K}$ and let $L \in \mathcal{L}(V)$ satisfy $\|L\| < 1$. Then $I - L$ is a
bijection of $V$ onto $V$ with bounded inverse, the series $\sum_{n \ge 0} L^n$ converges in
$\mathcal{L}(V)$ to $(I - L)^{-1}$, and
$$\|(I - L)^{-1}\| \le \frac{1}{1 - \|L\|}. \qquad (2.3.2)$$
-/
theorem theorem_2_3_1 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L ∧
      HasSum (fun n : ℕ => L ^ n) (e.symm : V →L[𝕜] V) ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (1 - ‖L‖) := by
  obtain ⟨e, he, hesymm⟩ := exists_equiv_of_isUnit (isUnit_one_sub_of_norm_lt_one hL)
  refine ⟨e, he, ?_, ?_⟩
  · rw [hesymm]
    exact hasSum_geom_series_inverse L hL
  · rw [hesymm, ← (hasSum_geom_series_inverse L hL).tsum_eq, one_div]
    have h1 : ‖(1 : V →L[𝕜] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 := tsum_geometric_le_of_norm_lt_one L hL
    linarith

/-- **Equation (2.3.4)** of [han2009theoretical]. Let $V$ be a Banach space over $\mathbb{K}$ and
let $L \in \mathcal{L}(V)$ satisfy $\|L\| < 1$. If $(I - L) u_1 = f_1$ and $(I - L) u_2 = f_2$,
then
$$\|u_1 - u_2\| \le \frac{1}{1 - \|L\|} \|f_1 - f_2\|.$$
This is the stability of the equation $(I - L) u = f$, from the remark after Theorem 2.3.1. -/
theorem equation_2_3_4 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) {u₁ u₂ f₁ f₂ : V}
    (h₁ : (1 - L) u₁ = f₁) (h₂ : (1 - L) u₂ = f₂) :
    ‖u₁ - u₂‖ ≤ 1 / (1 - ‖L‖) * ‖f₁ - f₂‖ := by
  obtain ⟨e, he, -, hb⟩ := theorem_2_3_1 L hL
  have hu : u₁ - u₂ = (e.symm : V →L[𝕜] V) (f₁ - f₂) := by
    rw [map_sub]
    have k₁ : (e.symm : V →L[𝕜] V) f₁ = u₁ := by
      rw [← h₁, ← he]; exact e.symm_apply_apply u₁
    have k₂ : (e.symm : V →L[𝕜] V) f₂ = u₂ := by
      rw [← h₂, ← he]; exact e.symm_apply_apply u₂
    rw [k₁, k₂]
  rw [hu]
  exact ((e.symm : V →L[𝕜] V).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- **Equation (2.3.5)** of [han2009theoretical]. Let $V$ be a Banach space over $\mathbb{K}$, let
$L \in \mathcal{L}(V)$ satisfy $\|L\| < 1$, and let $(I - L) u = f$. Then the partial sums of
the Neumann series converge to the solution:
$$u_n = \sum_{j=0}^n L^j f \to u \quad (n \to \infty).$$
-/
theorem equation_2_3_5 [CompleteSpace V] (L : V →L[𝕜] V) (hL : ‖L‖ < 1) {u f : V}
    (hu : (1 - L) u = f) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), (L ^ j) f) atTop (𝓝 u) := by
  obtain ⟨e, he, hsum, -⟩ := theorem_2_3_1 L hL
  have hu' : (e.symm : V →L[𝕜] V) f = u := by
    rw [← hu, ← he]; exact e.symm_apply_apply u
  have happ : HasSum (fun n : ℕ => (L ^ n) f) u := by
    rw [← hu']
    exact hsum.mapL (ContinuousLinearMap.apply 𝕜 V f)
  exact happ.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-! ### Example 2.3.2 -/

/-- **Example 2.3.2** of [han2009theoretical], abstract part. Let $V$ be a Banach space over
$\mathbb{K}$, let $K \in \mathcal{L}(V)$ and let $\lambda \in \mathbb{K}$ satisfy
$\|K\| < |\lambda|$. Then $\lambda I - K$ is a bijection of $V$ onto $V$ with bounded inverse,
and
$$\|(\lambda I - K)^{-1}\| \le \frac{1}{|\lambda| - \|K\|}.$$

The resulting bound on the solution of $(\lambda I - K) u = f$ is
`AtkinsonHan.Chapter02.example_2_3_2_bound`. The concrete part of the example, where $K$ is an
integral operator on $C[a, b]$ with norm (2.2.8), is
`AtkinsonHan.Chapter02.example_2_3_2_integral`. -/
theorem example_2_3_2 [CompleteSpace V] (K : V →L[𝕜] V) {lam : 𝕜} (h : ‖K‖ < ‖lam‖) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = lam • (1 : V →L[𝕜] V) - K ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / (‖lam‖ - ‖K‖) := by
  have hlampos : 0 < ‖lam‖ := lt_of_le_of_lt (norm_nonneg K) h
  have hlam : lam ≠ 0 := norm_pos_iff.mp hlampos
  have hLnorm : ‖lam⁻¹ • K‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_one₀ hlampos]
    exact h
  obtain ⟨e₀, he₀, -, hb₀⟩ := theorem_2_3_1 (lam⁻¹ • K) hLnorm
  obtain ⟨e, he, hesymm⟩ := exists_smul_equiv hlam e₀
  refine ⟨e, ?_, ?_⟩
  · rw [he, he₀, smul_sub, smul_inv_smul₀ hlam]
  · rw [hesymm]
    have hnorm : ‖lam⁻¹ • K‖ = ‖K‖ / ‖lam‖ := by
      rw [norm_smul, norm_inv, div_eq_inv_mul]
    rw [norm_smul, norm_inv]
    rw [hnorm] at hb₀
    have hpos : 0 < 1 - ‖K‖ / ‖lam‖ := by
      have : ‖K‖ / ‖lam‖ < 1 := (div_lt_one hlampos).2 h
      linarith
    have hsplit : 1 - ‖K‖ / ‖lam‖ = (‖lam‖ - ‖K‖) / ‖lam‖ := by
      field_simp
    have hnum : 0 < ‖lam‖ - ‖K‖ := by linarith
    calc ‖lam‖⁻¹ * ‖(e₀.symm : V →L[𝕜] V)‖
        ≤ ‖lam‖⁻¹ * (1 / (1 - ‖K‖ / ‖lam‖)) :=
          mul_le_mul_of_nonneg_left hb₀ (by positivity)
      _ = 1 / (‖lam‖ - ‖K‖) := by
          rw [hsplit, one_div_div]
          field_simp

/-- **Example 2.3.2** of [han2009theoretical], the bound on the solution. Let $V$ be a Banach space
over $\mathbb{K}$, let $K \in \mathcal{L}(V)$ and let $\lambda \in \mathbb{K}$ satisfy
$\|K\| < |\lambda|$. If $(\lambda I - K) u = f$, then
$$\|u\| \le \frac{\|f\|}{|\lambda| - \|K\|}.$$
-/
theorem example_2_3_2_bound [CompleteSpace V] (K : V →L[𝕜] V) {lam : 𝕜} (h : ‖K‖ < ‖lam‖)
    {u f : V} (hu : (lam • (1 : V →L[𝕜] V) - K) u = f) : ‖u‖ ≤ ‖f‖ / (‖lam‖ - ‖K‖) := by
  obtain ⟨e, he, hb⟩ := example_2_3_2 K h
  have hu' : (e.symm : V →L[𝕜] V) f = u := by
    rw [← hu, ← he]; exact e.symm_apply_apply u
  rw [← hu', div_eq_inv_mul, ← one_div]
  exact ((e.symm : V →L[𝕜] V).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-! ### Corollary 2.3.3 -/

set_option linter.unusedVariables false in
/-- **Corollary 2.3.3** of [han2009theoretical]. Let $V$ be a Banach space over $\mathbb{K}$ and let
$L \in \mathcal{L}(V)$ satisfy $\|L^m\| < 1$ for some integer $m \ge 1$ (2.3.10). Then $I - L$
is a bijection of $V$ onto $V$ with bounded inverse, and
$$\|(I - L)^{-1}\| \le \frac{\sum_{i=0}^{m-1} \|L^i\|}{1 - \|L^m\|}. \qquad (2.3.11)$$

The hypothesis $m \ge 1$ is kept as in the book, but the proof does not use it: for $m = 0$ the
hypothesis $\|L^0\| = \|I\| < 1$ holds only on the zero space, where the conclusion is trivial. -/
theorem corollary_2_3_3 [CompleteSpace V] (L : V →L[𝕜] V) {m : ℕ} (hm : 1 ≤ m) (hL : ‖L ^ m‖ < 1) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L ∧
      ‖(e.symm : V →L[𝕜] V)‖ ≤ (∑ i ∈ Finset.range m, ‖L ^ i‖) / (1 - ‖L ^ m‖) := by
  have hden : 0 < 1 - ‖L ^ m‖ := by linarith
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨ContinuousLinearEquiv.refl 𝕜 V, ?_, ?_⟩
    · ext x; exact Subsingleton.elim _ _
    · rw [norm_eq_zero_of_subsingleton]
      positivity
  · have hnt : Nontrivial V := hV
    obtain ⟨e, he, hesymm⟩ :=
      exists_equiv_of_isUnit (NormedRing.isUnit_one_sub_of_norm_pow_lt_one hL)
    exact ⟨e, he, hesymm ▸ NormedRing.norm_inverse_one_sub_le_of_norm_pow_lt_one hL⟩

/-- **Example 2.3.4** of [han2009theoretical], abstract part. Let $V$ be a Banach space over
$\mathbb{K}$ and let $L \in \mathcal{L}(V)$ satisfy $\|L^k\| \to 0$ as $k \to \infty$. Then
$I - L$ is a bijection of $V$ onto $V$ with bounded inverse.

The hypothesis holds for the Volterra integral operator, whose iterated kernels give
$\|L^k\| \le (MB)^k / k!$. This estimate is `AtkinsonHan.Chapter02.example_2_3_4_volterra`. -/
theorem example_2_3_4 [CompleteSpace V] (L : V →L[𝕜] V)
    (h : Tendsto (fun k : ℕ => ‖L ^ k‖) atTop (𝓝 0)) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = 1 - L := by
  obtain ⟨m, hm⟩ := ((h.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 1)).exists
  obtain ⟨e, he, -⟩ := corollary_2_3_3 L hm.2 hm.1
  exact ⟨e, he⟩

/-! ### Theorem 2.3.5 -/

/-- Let $V$ and $W$ be normed spaces over $\mathbb{K}$. If there is a continuous linear equivalence
of $V$ onto $W$ and $W$ is complete, then $V$ is complete.

Therefore the hypothesis "at least one of $V$, $W$ is complete" of Theorem 2.3.5 of
[han2009theoretical] is symmetric in the two spaces. -/
theorem completeSpace_of_equiv (L : V ≃L[𝕜] W) [CompleteSpace W] : CompleteSpace V :=
  (completeSpace_congr (e := L.toLinearEquiv.toEquiv) L.isUniformEmbedding).2 ‹_›

/-- **Theorem 2.3.5** of [han2009theoretical] (perturbation theorem). Let $V$ and $W$ be normed
spaces over $\mathbb{K}$, at least one of them complete. Let $L \in \mathcal{L}(V, W)$ be a
bijection of $V$ onto $W$ with bounded inverse, and let $M \in \mathcal{L}(V, W)$ satisfy
$$\|M - L\| < \frac{1}{\|L^{-1}\|}. \qquad (2.3.12)$$
Then $M$ is a bijection of $V$ onto $W$ with bounded inverse,
$$\|M^{-1}\| \le \frac{\|L^{-1}\|}{1 - \|L^{-1}\| \|L - M\|}, \qquad (2.3.13)$$
$$\|L^{-1} - M^{-1}\| \le \frac{\|L^{-1}\|^2 \|L - M\|}{1 - \|L^{-1}\| \|L - M\|}, \qquad
  (2.3.14)$$
and if $L v_1 = w$ and $M v_2 = w$ for some $w \in W$, then
$$\|v_1 - v_2\| \le \|M^{-1}\| \, \|(L - M) v_1\|. \qquad (2.3.15)$$

The operator $L$ is given as a continuous linear equivalence, and $L^{-1}$ is its inverse
`L.symm`. -/
theorem theorem_2_3_5 (hc : CompleteSpace V ∨ CompleteSpace W) (L : V ≃L[𝕜] W) (M : V →L[𝕜] W)
    (hM : ‖M - (L : V →L[𝕜] W)‖ < 1 / ‖(L.symm : W →L[𝕜] V)‖) :
    ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = M ∧
      ‖(e.symm : W →L[𝕜] V)‖ ≤
        ‖(L.symm : W →L[𝕜] V)‖ / (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ‖(L.symm : W →L[𝕜] V) - (e.symm : W →L[𝕜] V)‖ ≤
        ‖(L.symm : W →L[𝕜] V)‖ ^ 2 * ‖(L : V →L[𝕜] W) - M‖ /
          (1 - ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W) - M‖) ∧
      ∀ w : W, ∀ v₁ v₂ : V, L v₁ = w → M v₂ = w →
        ‖v₁ - v₂‖ ≤ ‖(e.symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - M) v₁‖ := by
  have : CompleteSpace V := hc.elim id fun _ => completeSpace_of_equiv L
  have hLpos : 0 < ‖(L.symm : W →L[𝕜] V)‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] V)) with h | h
    · rw [← h, div_zero] at hM
      exact absurd hM (not_lt.2 (norm_nonneg _))
    · exact h
  have hkey : ‖(L.symm : W →L[𝕜] V)‖ * ‖M - (L : V →L[𝕜] W)‖ < 1 := by
    rw [mul_comm, ← lt_div_iff₀ hLpos]
    exact hM
  obtain ⟨e, he, hb₁, hb₂⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add L (M - (L : V →L[𝕜] W)) hkey
  have hrev : ‖(L : V →L[𝕜] W) - M‖ = ‖M - (L : V →L[𝕜] W)‖ := norm_sub_rev _ _
  have he' : (e : V →L[𝕜] W) = M := by rw [he]; abel
  refine ⟨e, he', ?_, ?_, ?_⟩
  · rw [hrev]; exact hb₁
  · rw [hrev, norm_sub_rev]; exact hb₂
  · intro w v₁ v₂ hv₁ hv₂
    have hMe : (e : V →L[𝕜] W) v₂ = M v₂ := by rw [he']
    have happ : (L : V →L[𝕜] W) v₁ = e v₂ := by
      simp only [ContinuousLinearEquiv.coe_coe] at hMe ⊢
      rw [hv₁, hMe, hv₂]
    have hb := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (L : V →L[𝕜] W) e happ
    rwa [he'] at hb

/-! ### Consistency, stability and convergence (2.3.16) -/

/-- **Equation (2.3.16)** of [han2009theoretical], first part. Let $V$ and $W$ be normed spaces over
$\mathbb{K}$, at least one of them complete. Let $L \in \mathcal{L}(V, W)$ be a bijection of $V$
onto $W$ with bounded inverse, and let $L_n \in \mathcal{L}(V, W)$ satisfy $\|L - L_n\| \to 0$.
Then there is an $N$ such that for every $n \ge N$ the operator $L_n$ is a bijection of $V$ onto
$W$ with bounded inverse, and the solutions of $L v = w$ and $L_n v_n = w$ satisfy
$$\|v - v_n\| \le \|L_n^{-1}\| \, \|(L - L_n) v\|.$$

The inverses are given as a family $e_n$ of continuous linear equivalences for $n \ge N$. This
is the data that `AtkinsonHan.Chapter02.convergence_of_consistent_stable` takes, so that the two
parts of (2.3.16) compose. -/
theorem equation_2_3_16 (hc : CompleteSpace V ∨ CompleteSpace W) (L : V ≃L[𝕜] W)
    (Ln : ℕ → V →L[𝕜] W)
    (hLn : Tendsto (fun n => ‖(L : V →L[𝕜] W) - Ln n‖) atTop (𝓝 0)) :
    ∃ N : ℕ, ∃ en : ∀ n, N ≤ n → (V ≃L[𝕜] W),
      (∀ n hn, ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) = Ln n) ∧
        ∀ n hn, ∀ w : W, ∀ v vn : V, L v = w → Ln n vn = w →
          ‖v - vn‖ ≤ ‖((en n hn).symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - Ln n) v‖ := by
  suffices h : ∃ N : ℕ, ∀ n, N ≤ n → ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = Ln n ∧
      ∀ w : W, ∀ v vn : V, L v = w → Ln n vn = w →
        ‖v - vn‖ ≤ ‖(e.symm : W →L[𝕜] V)‖ * ‖((L : V →L[𝕜] W) - Ln n) v‖ by
    obtain ⟨N, hN⟩ := h
    choose en hen hbound using hN
    exact ⟨N, en, hen, hbound⟩
  rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] V)) with h | h
  · -- Degenerate case `‖L⁻¹‖ = 0`: both spaces are trivial and every claim is vacuous.
    have hWz : ∀ z : W, z = 0 := fun z => by
      have hb := (L.symm : W →L[𝕜] V).le_opNorm z
      rw [← h, zero_mul] at hb
      simpa using congrArg (⇑L) (norm_le_zero_iff.1 hb)
    have hVz : ∀ z : V, z = 0 := fun z => by
      simpa using congrArg (⇑(L.symm : W →L[𝕜] V)) (hWz (L z))
    refine ⟨0, fun n _ => ⟨L, ?_, fun w v vn _ _ => ?_⟩⟩
    · ext x
      rw [hWz ((L : V →L[𝕜] W) x), hWz (Ln n x)]
    · rw [hVz v, hVz vn, sub_zero, norm_zero]
      positivity
  · have hpos : (0 : ℝ) < 1 / ‖(L.symm : W →L[𝕜] V)‖ := by positivity
    obtain ⟨N, hN⟩ := (hLn.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have hlt : ‖Ln n - (L : V →L[𝕜] W)‖ < 1 / ‖(L.symm : W →L[𝕜] V)‖ := by
      rw [norm_sub_rev]
      exact hN n hn
    obtain ⟨e, he, -, -, hb⟩ := theorem_2_3_5 hc L (Ln n) hlt
    exact ⟨e, he, hb⟩

/-- **Equation (2.3.16)** of [han2009theoretical], second part. Let $V$ and $W$ be normed spaces
over $\mathbb{K}$, at least one of them complete, let $L \in \mathcal{L}(V, W)$ be a bijection
with bounded inverse, and let $L_n \in \mathcal{L}(V, W)$ be bijections with bounded inverses
for $n \ge N$. Let $L_n v_n = L v$ for $n \ge N$. Assume consistency, $\|(L - L_n) v\| \to 0$,
and stability, $\|L_n^{-1}\| \le C$ for all $n \ge N$ and a constant $C$. Then $v_n \to v$.

The families $L_n^{-1}$ and $v_n$ are defined only for $n \ge N$, as
`AtkinsonHan.Chapter02.equation_2_3_16` gives them, so the conclusion is stated as
$\|v - v_{k + N}\| \to 0$ as $k \to \infty$. -/
theorem convergence_of_consistent_stable (hc : CompleteSpace V ∨ CompleteSpace W)
    (L : V ≃L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (N : ℕ) (en : ∀ n, N ≤ n → (V ≃L[𝕜] W))
    (hen : ∀ n hn, ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) = Ln n) {v : V}
    (vn : ∀ n, N ≤ n → V) (hv : ∀ n hn, Ln n (vn n hn) = L v)
    (hcons : Tendsto (fun n => ‖((L : V →L[𝕜] W) - Ln n) v‖) atTop (𝓝 0))
    (hstab : ∃ C : ℝ, ∀ n hn, ‖((en n hn).symm : W →L[𝕜] V)‖ ≤ C) :
    Tendsto (fun k : ℕ => ‖v - vn (k + N) (Nat.le_add_left N k)‖) atTop (𝓝 0) := by
  have : CompleteSpace V := hc.elim id fun _ => completeSpace_of_equiv L
  obtain ⟨C, hC⟩ := hstab
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC N le_rfl)
  have hshift : Tendsto (fun k : ℕ => C * ‖((L : V →L[𝕜] W) - Ln (k + N)) v‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hcons.const_mul C).comp (tendsto_add_atTop_nat N)
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hshift
  set n := k + N with hn'
  have hn : N ≤ n := Nat.le_add_left N k
  have hEq : ((en n hn : V ≃L[𝕜] W) : V →L[𝕜] W) (vn n hn) = Ln n (vn n hn) := by rw [hen n hn]
  have happ : (L : V →L[𝕜] W) v = en n hn (vn n hn) := by
    simp only [ContinuousLinearEquiv.coe_coe] at hEq ⊢
    rw [← hv n hn, hEq]
  have hb := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (L : V →L[𝕜] W) (en n hn) happ
  rw [hen n hn] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (hC n hn) (norm_nonneg _))

/-! ### The integral operator instances of Examples 2.3.2 and 2.3.4 -/

section IntegralEquations

open Set IntegralOperator

open scoped Nat

variable {a b : ℝ}

/-- **Example 2.3.2 (ii)** of [han2009theoretical], the integral equation. Let $a \le b$, let $k$ be
a real continuous function on $[a, b] \times [a, b]$, and let $K$ be the integral operator
$Ku(x) = \int_a^b k(x, y) u(y) \, dy$ on $C[a, b]$. Let $\lambda \in \mathbb{R}$ satisfy
$$\max_{a \le x \le b} \int_a^b |k(x, y)| \, dy < |\lambda|.$$
Then $\lambda I - K$ is a bijection of $C[a, b]$ onto itself with bounded inverse,
$$\|(\lambda I - K)^{-1}\| \le \frac{1}{|\lambda| - \|K\|},$$
and every solution of $\lambda u - K u = f$ satisfies $\|u\| \le \|f\| / (|\lambda| - \|K\|)$.

By (2.2.8) the maximum is $\|K\|$, and the statement writes it in this form. The operator is
`IntegralOperator.fredholm`. -/
theorem example_2_3_2_integral (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) {lam : ℝ}
    (hk : (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) < |lam|) :
    ∃ e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ),
      (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
          = lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - fredholm hab k ∧
        ‖(e.symm : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))‖
          ≤ 1 / (|lam| - ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) ∧
        ∀ u f : C(Icc a b, ℝ), lam • u - fredholm hab k u = f →
          ‖u‖ ≤ ‖f‖ / (|lam| - ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) := by
  have hK : ‖fredholm hab k‖ < ‖lam‖ := by
    rw [norm_fredholm hab k, Real.norm_eq_abs]; exact hk
  obtain ⟨e, he, hb⟩ := example_2_3_2 (fredholm hab k) hK
  rw [norm_fredholm hab k, Real.norm_eq_abs] at hb
  refine ⟨e, he, hb, fun u f hu => ?_⟩
  have hu' : (lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - fredholm hab k) u = f := by
    simpa using hu
  have hbound := example_2_3_2_bound (fredholm hab k) hK hu'
  rwa [norm_fredholm hab k, Real.norm_eq_abs] at hbound

/-- **Example 2.3.4** of [han2009theoretical], the Volterra equation. Let $a \le b$, let $k$ be a
real continuous function on $[a, b] \times [a, b]$, and let $L$ be the Volterra operator
$Lu(x) = \int_a^x k(x, y) u(y) \, dy$ on $C[a, b]$. Then for every $m \ge 0$,
$$\|L^m\| \le \frac{(\|k\|_\infty (b - a))^m}{m!},$$
and for every real $\lambda \neq 0$ the operator $\lambda I - L$ is a bijection of $C[a, b]$
onto itself with bounded inverse.

By the bound, (2.3.10) holds for all large $m$. Thus a Volterra equation of the second kind is
uniquely solvable for every kernel. The operator is `IntegralOperator.volterraCLM`, and
$\|k\|_\infty$ is the supremum norm of the kernel. -/
theorem example_2_3_4_volterra (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) {lam : ℝ}
    (hlam : lam ≠ 0) :
    (∀ m : ℕ, ‖volterraCLM hab k ^ m‖ ≤ (‖k‖ * (b - a)) ^ m / m !) ∧
      ∃ e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ),
        (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
          = lam • (1 : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) - volterraCLM hab k := by
  refine ⟨norm_volterraCLM_pow_le hab k, ?_⟩
  have hbound : ∀ m : ℕ, ‖(lam⁻¹ • volterraCLM hab k) ^ m‖
      ≤ (‖lam⁻¹‖ * (‖k‖ * (b - a))) ^ m / m ! := fun m => by
    calc ‖(lam⁻¹ • volterraCLM hab k) ^ m‖
        = ‖lam⁻¹‖ ^ m * ‖volterraCLM hab k ^ m‖ := by
          rw [smul_pow, norm_smul, norm_pow]
      _ ≤ ‖lam⁻¹‖ ^ m * ((‖k‖ * (b - a)) ^ m / m !) :=
          mul_le_mul_of_nonneg_left (norm_volterraCLM_pow_le hab k m) (by positivity)
      _ = (‖lam⁻¹‖ * (‖k‖ * (b - a))) ^ m / m ! := by rw [← mul_div_assoc, ← mul_pow]
  have htend : Tendsto (fun m : ℕ => ‖(lam⁻¹ • volterraCLM hab k) ^ m‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound
      (FloorSemiring.tendsto_pow_div_factorial_atTop _)
  obtain ⟨e₀, he₀⟩ := example_2_3_4 (lam⁻¹ • volterraCLM hab k) htend
  obtain ⟨e, he, -⟩ := exists_smul_equiv hlam e₀
  exact ⟨e, by rw [he, he₀, smul_sub, smul_inv_smul₀ hlam]⟩

/-! ### Example 2.3.6: the integral equation (2.3.17) -/

section Example236

open Real

/-- Let $g$ be continuous, nonnegative and increasing on $[0, 1]$. Then the largest row integral
$\sup_{x \in [0, 1]} \int_0^1 |g(xy)| \, dy$ is attained at $x = 1$, and it equals
$\int_0^1 g(y) \, dy$. -/
private theorem iSup_integral_abs_mul {g : ℝ → ℝ} (hcont : Continuous g)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) (hmono : MonotoneOn g (Icc (0 : ℝ) 1)) :
    ⨆ x : Icc (0 : ℝ) 1, (∫ y in (0 : ℝ)..1, |g ((x : ℝ) * y)|) = ∫ y in (0 : ℝ)..1, g y := by
  have hmem : ∀ x : Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, (x : ℝ) * y ∈ Icc (0 : ℝ) 1 := by
    rintro ⟨x, hx0, hx1⟩ y ⟨hy0, hy1⟩
    exact ⟨by positivity, by nlinarith⟩
  have hle : ∀ x : Icc (0 : ℝ) 1,
      (∫ y in (0 : ℝ)..1, |g ((x : ℝ) * y)|) ≤ ∫ y in (0 : ℝ)..1, g y := by
    intro x
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hcont.abs.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun y hy => ?_
    rw [abs_of_nonneg (hnonneg _ (hmem x y hy))]
    exact hmono (hmem x y hy) hy (by nlinarith [x.2.1, x.2.2, hy.1])
  have hone : (∫ y in (0 : ℝ)..1, |g (((⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) : ℝ) * y)|)
      = ∫ y in (0 : ℝ)..1, g y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le zero_le_one] at hy
    simp [abs_of_nonneg (hnonneg y hy)]
  have hbdd : BddAbove (Set.range fun x : Icc (0 : ℝ) 1 =>
      ∫ y in (0 : ℝ)..1, |g ((x : ℝ) * y)|) := by
    refine ⟨∫ y in (0 : ℝ)..1, g y, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hle x
  refine le_antisymm (ciSup_le hle) ?_
  rw [← hone]
  exact le_ciSup hbdd (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)

/-- The sine is increasing on $[0, 1]$. -/
private theorem monotoneOn_sin_unitInterval : MonotoneOn sin (Icc (0 : ℝ) 1) := by
  refine strictMonoOn_sin.monotoneOn.mono fun t ht => ?_
  have hpi : (1 : ℝ) ≤ π / 2 := by linarith [two_le_pi]
  exact ⟨by linarith [ht.1, pi_pos], ht.2.trans hpi⟩

/-- The function $t \mapsto t - \sin t$ is increasing on $[0, 1]$. -/
private theorem monotoneOn_sub_sin : MonotoneOn (fun t : ℝ => t - sin t) (Icc (0 : ℝ) 1) := by
  intro s _ t _ hst
  have h1 : sin t - sin s ≤ |t - s| := (le_abs_self _).trans (abs_sin_sub_sin_le t s)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h1
  simp only
  linarith

/-- **Example 2.3.6** of [han2009theoretical], the formula (2.3.18). Let $K$ be the integral
operator on $C[0, 1]$ with kernel $k(x, y) = \sin(xy)$, as in (2.3.17). Then
$$\|K\| = \int_0^1 \sin y \, dy = 1 - \cos 1.$$
Let $\lambda \in \mathbb{R}$ satisfy $|\lambda| > 1 - \cos 1 \approx 0.4597$. Then
$\lambda I - K$ is a bijection of $C[0, 1]$ onto itself with bounded inverse, $\|(\lambda I -
K)^{-1}\| \le 1 / (|\lambda| - (1 - \cos 1))$, and every solution $u \in C[0, 1]$ of
$$\lambda u(x) - \int_0^1 \sin(xy) u(y) \, dy = f(x)$$
satisfies $\|u\| \le \|f\| / (|\lambda| - (1 - \cos 1))$.

This is the part of the example that the book settles with Example 2.3.2. The row integral of
(2.2.8) is largest at $x = 1$, because $\sin(xy) \le \sin y$ on the square. The kernel is a
continuous function described by the hypothesis `hk` on its values, as
`AtkinsonHan.Chapter01.example_1_1_12` describes its subspace. -/
theorem example_2_3_6 (k : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ))
    (hk : ∀ p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, k p = sin ((p.1 : ℝ) * (p.2 : ℝ))) {lam : ℝ}
    (hlam : 1 - cos 1 < |lam|) :
    ‖fredholm zero_le_one k‖ = 1 - cos 1 ∧
      ∃ e : C(Icc (0 : ℝ) 1, ℝ) ≃L[ℝ] C(Icc (0 : ℝ) 1, ℝ),
        (e : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))
            = lam • (1 : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ)) - fredholm zero_le_one k ∧
          ‖(e.symm : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))‖
            ≤ 1 / (|lam| - (1 - cos 1)) ∧
          ∀ u f : C(Icc (0 : ℝ) 1, ℝ), lam • u - fredholm zero_le_one k u = f →
            ‖u‖ ≤ ‖f‖ / (|lam| - (1 - cos 1)) := by
  have hsup : (⨆ x, ∫ y in (0 : ℝ)..1, |k (x, projIcc (0 : ℝ) 1 zero_le_one y)|) = 1 - cos 1 := by
    have hcongr : ∀ x : Icc (0 : ℝ) 1,
        (∫ y in (0 : ℝ)..1, |k (x, projIcc (0 : ℝ) 1 zero_le_one y)|)
          = ∫ y in (0 : ℝ)..1, |sin ((x : ℝ) * y)| := by
      intro x
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le zero_le_one] at hy
      rw [hk, projIcc_of_mem zero_le_one hy]
    rw [iSup_congr hcongr,
      iSup_integral_abs_mul continuous_sin
        (fun t ht => sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans (by linarith [two_le_pi])))
        monotoneOn_sin_unitInterval,
      integral_sin, cos_zero]
  refine ⟨by rw [norm_fredholm zero_le_one k, hsup], ?_⟩
  obtain ⟨e, he, hb, hu⟩ := example_2_3_2_integral zero_le_one k (lam := lam) (by rwa [hsup])
  rw [hsup] at hb hu
  exact ⟨e, he, hb, hu⟩

/-- **Example 2.3.6** of [han2009theoretical], the norm $\|L - M\|$. Let $K$ be the integral
operator on $C[0, 1]$ with kernel $k(x, y) = xy - \sin(xy)$. Then
$$\|K\| = \int_0^1 (y - \sin y) \, dy = \cos 1 - \frac{1}{2} \approx 0.0403.$$
In the book, $K$ is the difference $L - M$ between the operator $L$ of the equation (2.3.17) and
the operator $M$ of the degenerate kernel equation (2.3.19), and the perturbation comparison of
the two equations rests on this number.

The row integral of (2.2.8) is largest at $x = 1$, because $t \mapsto t - \sin t$ is increasing.
The kernel is described by the hypothesis `hk` on its values. -/
theorem example_2_3_6_norm_sub (k : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ))
    (hk : ∀ p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1,
      k p = (p.1 : ℝ) * (p.2 : ℝ) - sin ((p.1 : ℝ) * (p.2 : ℝ))) :
    ‖fredholm zero_le_one k‖ = cos 1 - 1 / 2 := by
  have hcongr : ∀ x : Icc (0 : ℝ) 1,
      (∫ y in (0 : ℝ)..1, |k (x, projIcc (0 : ℝ) 1 zero_le_one y)|)
        = ∫ y in (0 : ℝ)..1, |(fun t : ℝ => t - sin t) ((x : ℝ) * y)| := by
    intro x
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le zero_le_one] at hy
    rw [hk, projIcc_of_mem zero_le_one hy]
  rw [norm_fredholm zero_le_one k, iSup_congr hcongr,
    iSup_integral_abs_mul (by fun_prop)
      (fun t ht => sub_nonneg.2 (sin_le ht.1)) monotoneOn_sub_sin]
  rw [intervalIntegral.integral_sub (continuous_id'.intervalIntegrable _ _)
    (continuous_sin.intervalIntegrable _ _), integral_id, integral_sin, cos_zero]
  ring

end Example236

end IntegralEquations

end AtkinsonHan.Chapter02
