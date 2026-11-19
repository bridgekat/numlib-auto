/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import NumlibSurface.Brezis.Chapter02.Section01

/-!
# Brezis, Section 2.2: The uniform boundedness principle

This module formalizes Section 2.2 of [brezis2011functional] for real Banach spaces $E$ and $F$. The
space $\mathcal{L}(E, F)$ of bounded linear operators carries the norm $\|T\|_{\mathcal{L}(E,F)} =
\sup_{\|x\| \le 1} \|Tx\|$. The Banach–Steinhaus theorem (Theorem 2.2) states that a family of
bounded operators with $\sup_i \|T_i x\| < \infty$ for every $x$ satisfies
$\sup_i \|T_i\| < \infty$. Its corollaries are that a pointwise limit $T$ of bounded operators $T_n$
is bounded with $\|T\| \le \liminf \|T_n\|$ (Corollary 2.3), that a weakly bounded subset of a
Banach space is bounded (Corollary 2.4), and that a weak-$\star$ bounded set of functionals is
bounded (Corollary 2.5). Remark 3 shows that pointwise convergence does not give convergence in
norm.

Theorem 2.2 is Mathlib's `banach_steinhaus`. Corollaries 2.3 to 2.5 specialize the backbone module
`Numlib.Analysis.Normed.Operator.BanachSteinhaus`:
`ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto`, `isBounded_of_forall_dual_image_isBounded`
and `StrongDual.isBounded_of_forall_eval_isBounded`.

## Main definitions

* Section 2.2, the operator norm, `Brezis.Chapter02.opNorm_eq_sSup`: $\|T\|_{\mathcal{L}(E,F)} =
  \sup_{\|x\| \le 1} \|Tx\|$.

## Main results

* Theorem 2.2, `Brezis.Chapter02.theorem_2_2`: a pointwise bounded family of bounded operators is
  bounded in norm, with the estimate (2) (Banach–Steinhaus).
* Remark 3, `Brezis.Chapter02.remark_2_3`: on $\ell^2$ the coordinate functionals converge pointwise
  to $0$ but not in norm.
* Corollary 2.3, `Brezis.Chapter02.corollary_2_3`: the pointwise limit $T$ of bounded operators
  $T_n$ is bounded, $\sup_n \|T_n\| < \infty$, and $\|T\| \le \liminf \|T_n\|$.
* Corollary 2.4, `Brezis.Chapter02.corollary_2_4`: a set $B$ with $f(B)$ bounded for every
  $f \in G^\star$ is bounded.
* Corollary 2.5, `Brezis.Chapter02.corollary_2_5`: a set $B^\star \subseteq G^\star$ with
  $\langle B^\star, x \rangle$ bounded for every $x \in G$ is bounded.

## Conventions

* $\mathcal{L}(E, F)$ is `E →L[ℝ] F` with Mathlib's operator norm.

## Implementation notes

* The source assumes throughout that $E$ and $F$ are complete. The results carry both hypotheses as
  the source states them, although the proofs use only the completeness of $E$.
* Remark 4, "weakly bounded if and only if strongly bounded", is the equivalence form of Corollary
  2.4, the backbone theorem `isBounded_iff_forall_dual_image_isBounded`.

## Not formalized

* **Remark 2.** It is a discussion.
-/

open Bornology Filter Metric Topology

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Section 2.2** of [brezis2011functional], the norm of an operator. Let $E$ and $F$ be real
normed spaces. For $T \in \mathcal{L}(E, F)$,
$$\|T\|_{\mathcal{L}(E,F)} = \sup_{x \in E,\ \|x\| \le 1} \|Tx\|.$$
Thus the operator norm of Mathlib is the norm of the source. -/
theorem opNorm_eq_sSup (T : E →L[ℝ] F) : ‖T‖ = sSup ((fun x => ‖T x‖) '' closedBall 0 1) :=
  T.sSup_unitClosedBall_eq_norm.symm

/-- **Theorem 2.2** of [brezis2011functional] (Banach–Steinhaus, uniform boundedness principle). Let
$E$ and $F$ be two Banach spaces and let $(T_i)_{i \in I}$ be a family of bounded linear
operators from $E$ into $F$. Assume that
$$\sup_{i \in I} \|T_i x\| < \infty \quad \text{for all } x \in E.$$
Then $\sup_{i \in I} \|T_i\|_{\mathcal{L}(E,F)} < \infty$. In other words, there is a constant
$c$ such that $\|T_i\| \le c$ for all $i$ and
$$\|T_i x\| \le c\|x\| \quad \text{for all } x \in E,\ i \in I. \qquad (2)$$

The proof specializes Mathlib's `banach_steinhaus`, which does not need the completeness of $F$. -/
theorem theorem_2_2 [CompleteSpace E] [CompleteSpace F] {ι : Type*} (T : ι → E →L[ℝ] F)
    (h : ∀ x, ∃ C : ℝ, ∀ i, ‖T i x‖ ≤ C) :
    ∃ c : ℝ, (∀ i, ‖T i‖ ≤ c) ∧ ∀ x i, ‖T i x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc⟩ := banach_steinhaus h
  exact ⟨c, hc, fun x i => (T i).le_of_opNorm_le (hc i) x⟩

/-- **Corollary 2.3** of [brezis2011functional]. Let $E$ and $F$ be two Banach spaces and let
$(T_n)$ be a sequence in $\mathcal{L}(E, F)$ such that for every $x \in E$ the sequence $T_n x$
converges to a limit, denoted by $Tx$. Then (a) $\sup_n \|T_n\|_{\mathcal{L}(E,F)} < \infty$,
(b) $T \in \mathcal{L}(E, F)$, and (c) $\|T\|_{\mathcal{L}(E,F)} \le \liminf_{n \to \infty}
\|T_n\|_{\mathcal{L}(E,F)}$.

The statement gives a bounded operator $L$ with $T_n x \to Lx$ for every $x$, a bound $C$ with
$\|T_n\| \le C$ for all $n$, and $\|L\| \le \liminf \|T_n\|$. Part (c) specializes the backbone
theorem `ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto`. -/
theorem corollary_2_3 [CompleteSpace E] [CompleteSpace F] (T : ℕ → E →L[ℝ] F)
    (h : ∀ x, ∃ y, Tendsto (fun n => T n x) atTop (𝓝 y)) :
    ∃ L : E →L[ℝ] F, (∃ C : ℝ, ∀ n, ‖T n‖ ≤ C) ∧
      (∀ x, Tendsto (fun n => T n x) atTop (𝓝 (L x))) ∧
      ‖L‖ ≤ liminf (fun n => ‖T n‖) atTop := by
  choose f hf using h
  have hpt : Tendsto (fun n x => T n x) atTop (𝓝 f) := tendsto_pi_nhds.2 hf
  obtain ⟨C, hC⟩ := banach_steinhaus (g := T) fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ (hf x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  let L : E →L[ℝ] F :=
    (linearMapOfTendsto f (fun n => (T n : E →ₗ[ℝ] F)) hpt).mkContinuousOfExistsBound
      ⟨C, fun x => le_of_tendsto (hf x).norm
        (Eventually.of_forall fun n => (T n).le_of_opNorm_le (hC n) x)⟩
  refine ⟨L, ⟨C, hC⟩, fun x => hf x, ?_⟩
  exact ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto (fun x => hf x)
    ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩

/-- **Corollary 2.4** of [brezis2011functional]. Let $G$ be a real Banach space and let
$B \subseteq G$. Assume that for every $f \in G^\star$ the set
$$f(B) = \{\langle f, x \rangle : x \in B\}$$
is bounded in $\mathbb{R}$. Then $B$ is bounded.

The proof specializes the backbone theorem `isBounded_of_forall_dual_image_isBounded`. -/
theorem corollary_2_4 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : Set G} (h : ∀ f : StrongDual ℝ G, IsBounded (f '' B)) : IsBounded B :=
  isBounded_of_forall_dual_image_isBounded h

/-- **Corollary 2.5** of [brezis2011functional]. Let $G$ be a real Banach space and let
$B^\star \subseteq G^\star$. Assume that for every $x \in G$ the set
$$\langle B^\star, x \rangle = \{\langle f, x \rangle : f \in B^\star\}$$
is bounded in $\mathbb{R}$. Then $B^\star$ is bounded.

The proof specializes the backbone theorem `StrongDual.isBounded_of_forall_eval_isBounded`. -/
theorem corollary_2_5 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : Set (StrongDual ℝ G)} (h : ∀ x : G, IsBounded ((fun f : StrongDual ℝ G => f x) '' B)) :
    IsBounded B :=
  StrongDual.isBounded_of_forall_eval_isBounded h

/-! ### Remark 3: the coordinate functionals on $\ell^2$ -/

/-- The coordinates of a square-summable sequence tend to $0$: for $x \in \ell^2$, $x_n \to 0$ as
$n \to \infty$. This supports Remark 3, and Remark 9 of Chapter 3 uses it again. -/
theorem tendsto_coord_zero (x : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun n => x n) atTop (𝓝 0) := by
  have hsum := (lp.memℓp x).summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat] at hsum
  have h2 := hsum.tendsto_atTop_zero
  have h := (Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by norm_num)).tendsto 0 |>.comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (h.congr fun n => Real.rpow_rpow_inv (norm_nonneg _) two_ne_zero).mono_right ?_
  simp

/-- **Remark 3** of [brezis2011functional]. In Theorem 2.2, pointwise convergence $T_n x \to Tx$ for
every $x$ does not imply $\|T_n - T\| \to 0$. On $E = \ell^2$, the coordinate functionals
$T_n x = x_n$ converge pointwise to $T = 0$, but $\|T_n - T\|$ does not tend to $0$.

The functional $T_n$ is `lp.evalCLM ℝ (fun _ => ℝ) 2 n`. Evaluating it at the $n$th coordinate
unit vector gives the lower bound $\|T_n\| \ge 1$. This example exhibits the failure of norm
convergence asserted in the source. -/
theorem remark_2_3 :
    (∀ x : lp (fun _ : ℕ => ℝ) 2,
      Tendsto (fun n => lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n x) atTop
        (𝓝 ((0 : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] ℝ) x))) ∧
    ¬ Tendsto (fun n => ‖lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n - 0‖) atTop (𝓝 0) := by
  refine ⟨fun x => ?_, fun h => ?_⟩
  · rw [zero_apply]
    exact tendsto_coord_zero x
  have hge : ∀ n, (1 : ℝ) ≤ ‖lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n - 0‖ := fun n => by
    rw [sub_zero]
    have := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).le_opNorm (lp.single 2 n (1 : ℝ))
    rw [lp.norm_single (by norm_num), norm_one, mul_one] at this
    simpa [lp.evalCLM, lp.single_apply_self] using this
  exact absurd (ge_of_tendsto' h hge) (by norm_num)

end Brezis.Chapter02
