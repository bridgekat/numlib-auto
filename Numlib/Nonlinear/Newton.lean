/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Order

/-!
# Newton's method in Banach spaces

Let $E$ and $V$ be normed spaces over a field $\mathbb{K}$, let $F \colon E \to V$, and let $F'(x)$
be a continuous linear map from $E$ to $V$ for each $x \in E$, usually the derivative of $F$ at $x$.
Newton's method replaces $F$ near the current point by its linearization and moves to the zero of
the linearization. One step is
$$N(x) = x - F'(x)^{-1} F(x),$$
and the iterates are $x_{k+1} = N(x_k)$. This module proves the two classical convergence theorems
for $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The first is local quadratic convergence: if $x^*$ is
a zero of $F$, $F'(x^*)$ is invertible and $F'$ is $L$-Lipschitz near $x^*$, then $\|x_{k+1} - x^*\|
\le (L/2) \|F'(x_k)^{-1}\| \|x_k - x^*\|^2$ near $x^*$ ([han2009theoretical], Theorem 5.4.1;
[kress1998numerical], Corollary 6.15 with Theorem 6.20; [quarteroni2000numerical], Theorem 7.1). The
second is the Newton–Kantorovich theorem, whose hypotheses are conditions at the starting point
$x_0$ only and which proves that a zero exists, with an a priori error bound and a uniqueness ball
([han2009theoretical], Theorem 5.4.2; [kress1998numerical], Theorem 6.14). Its proof is the majorant
method of [ortega2000iterative].

The module also treats Newton-like methods $x_{k+1} = x_k - B_k^{-1} F(x_k)$, in which $B_k$
approximates $F'(x_k)$ ([quarteroni2000numerical], Property 7.1; [kress1998numerical], Theorem
6.21), and the chord method $x_{k+1} = x_k - A^{-1} F(x_k)$ with a fixed invertible $A$
([han2009theoretical], (5.4.11) and Exercise 5.4.5). Both proofs rest on the sharp second-order mean
value inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` of
`Numlib.Analysis.Calculus.MeanValue`.

## Main definitions

* `Newton.step`: the Newton step $N(x) = x - F'(x)^{-1} F(x)$.
* `Newton.iterate`: the Newton iterates $x_k = N^k(x_0)$.
* `Newton.chordStep`: the chord step $x - A^{-1} F(x)$ with a fixed invertible operator $A$.
* `Newton.chordIterate`: the iterates of the chord method.
* `Newton.majorant`: the normalized scalar majorant sequence of the Kantorovich proof.

## Main results

* `Newton.exists_ball_norm_step_sub_le`: near a zero $x^*$ with $F'(x^*)$ invertible and $F'$
  Lipschitz, $\|N(x) - x^*\| \le C \|x - x^*\|^2$.
* `Newton.norm_step_sub_le`: the explicit bound $\|N(x) - x^*\| \le (L/2) \|F'(x)^{-1}\| \|x -
  x^*\|^2$.
* `Newton.tendsto_iterate`: the Newton iterates converge to $x^*$ from every start close to $x^*$.
* `Newton.forall_norm_iterate_succ_sub_le_of_mem_ball`: Newton's method with the explicit radius
  $\min\{r, 1/(2KL)\}$ and the explicit constant $KL$.
* `Newton.norm_approxStep_sub_le`: the error of one step with an approximate derivative.
* `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le`: linear convergence of
  Newton-like methods whose approximate derivatives are close to the exact ones.
* `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le_of_mem`: the same for approximate
  derivatives that depend on the iterate.
* `Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul`: quadratic convergence when the derivative
  error is of first order in the error.
* `Newton.kantorovich`: the Newton–Kantorovich theorem, with existence of the zero and the a priori
  bound.
* `Newton.kantorovich_invertible`: under the Kantorovich hypotheses every $F'(x_k)$ is invertible.
* `Newton.kantorovich_norm_sub_le`: the sharp a priori bound $\|x_k - x^*\| \le (1 - \sqrt{1 -
  2h})^{2^k} / (2^k \beta L)$.
* `Newton.kantorovich_unique`: uniqueness of the zero in the open ball of radius $t^{**}$.
* `Newton.kantorovich_unique_closedBall`: uniqueness of the zero in the closed ball of radius $t^*$.
* `Newton.kantorovich_of_closedBall_step`: the Kantorovich theorem localized at the first iterate.
* `Newton.norm_chordStep_sub_le` and `Newton.tendsto_chordIterate`: linear convergence of the chord
  method.

## Implementation notes

* The function $F$ is `Fn`, the codomain $V$ is the type `F`, and the zero $x^*$ is `xstar`.
* The inverse $F'(x)^{-1}$ in `Newton.step` is `ContinuousLinearMap.inverse`, which is $0$ when
  $F'(x)$ is not invertible. So $N(x) = x$ where $F'(x)$ is not invertible, and the definition needs
  no hypothesis.
* An invertible derivative is given as a continuous linear equivalence `e : E ≃L[𝕜] F` together with
  the equation `(e : E →L[𝕜] F) = F' x`. Then `e.symm` is the inverse $F'(x)^{-1}$.
* The theorems that use the mean value inequality assume `[IsRCLikeNormedField 𝕜]`, that is
  $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and `[NormedSpace ℝ E]`. The sectioning comment on
  local quadratic convergence shows that these theorems are false over a general field.
-/

open Filter Topology

namespace Newton

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- One **Newton step** for $F$ with derivative $F'$: $N(x) = x - F'(x)^{-1} F(x)$.

The inverse is `ContinuousLinearMap.inverse`, which is $0$ when $F'(x)$ is not invertible; then
$N(x) = x$. -/
noncomputable def step (Fn : E → F) (F' : E → E →L[𝕜] F) (x : E) : E :=
  x - (F' x).inverse (Fn x)

/-- The **Newton iterates** from $x_0$: $x_k = N^k(x_0)$, the $k$-fold application of the Newton
step `Newton.step`. -/
noncomputable def iterate (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) : E :=
  (step Fn F')^[k] x₀

/-- The Newton recurrence: $x_{k+1} = x_k - F'(x_k)^{-1} F(x_k)$, that is, $x_{k+1} = N(x_k)$.

The definition applies the step $k$ times to $x_0$. This lemma states the recurrence with the
step applied at the last iterate, which is the form that the inductions in this module use. -/
theorem iterate_succ (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) :
    iterate Fn F' x₀ (k + 1) = step Fn F' (iterate Fn F' x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- Let $x \in E$ with $F(x) = 0$. Then $x$ is a fixed point of the Newton step: $N(x) = x$, for
every $F'$. -/
theorem step_eq_self_of_eq_zero (Fn : E → F) (F' : E → E →L[𝕜] F) {x : E} (hx : Fn x = 0) :
    step Fn F' x = x := by
  simp [step, hx]

/-- One step of the **chord method**, or modified Newton method, for $F$ and a fixed invertible
continuous linear map $A \colon E \to V$: $x \mapsto x - A^{-1} F(x)$. The derivative is frozen
at $A$ and is not recomputed and inverted at each iterate. The usual choice is $A = F'(x_0)$.

The chord method is (5.4.11) of [han2009theoretical]. Since $A$ is an equivalence, $A^{-1}$ is a
true inverse and no junk value occurs, unlike in `Newton.step`. The price is that the
convergence is only linear (`Newton.tendsto_chordIterate`) and not quadratic. -/
noncomputable def chordStep (Fn : E → F) (A : E ≃L[𝕜] F) (x : E) : E := x - A.symm (Fn x)

/-- The **chord iterates** from $x_0$: the $k$-fold application of the chord step `Newton.chordStep`
with the fixed operator $A$. -/
noncomputable def chordIterate (Fn : E → F) (A : E ≃L[𝕜] F) (x₀ : E) (k : ℕ) : E :=
  (chordStep Fn A)^[k] x₀

/-- The chord recurrence: the $(k+1)$-st chord iterate is $x_{k+1} = x_k - A^{-1} F(x_k)$. -/
theorem chordIterate_succ (Fn : E → F) (A : E ≃L[𝕜] F) (x₀ : E) (k : ℕ) :
    chordIterate Fn A x₀ (k + 1) = chordStep Fn A (chordIterate Fn A x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- Let $x \in E$ with $F(x) = 0$. Then $x$ is a fixed point of the chord step, for every invertible
$A$. -/
theorem chordStep_eq_self_of_eq_zero (Fn : E → F) (A : E ≃L[𝕜] F) {x : E} (hx : Fn x = 0) :
    chordStep Fn A x = x := by
  simp [chordStep, hx]

section Quadratic

/-!
### Local quadratic convergence

The theorems below assume `[IsRCLikeNormedField 𝕜]` and `[NormedSpace ℝ E]`, which the informal
statements do not mention. All proofs use the mean value inequality
`Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`, which is available only over $\mathbb{R}$
and $\mathbb{C}$. Over a general nontrivially normed field the statements are false. For a
counterexample, let $\mathbb{K} = E = V = \mathbb{F}_p((t))$, $F(x) = x + x^p$ and $F'(x) = 1$. In
characteristic $p$, $(x + h)^p = x^p + h^p$ and $\|h^p\| = \|h\|^p = o(\|h\|)$, so $F$ has
derivative $1$ at every $x$. Then $F'$ is constant, hence $L$-Lipschitz with $L = 0$, and
$F(0) = 0$. The conclusion of `Newton.norm_step_sub_le` at $x^* = 0$ is $\|N(x)\| \le 0$, but
$N(x) = x - (x + x^p) = -x^p \neq 0$ for $x \neq 0$.
-/

variable [CompleteSpace E] [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]

omit [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- Let $e \colon E \to V$ be invertible with $\|e^{-1}\| \le K$, and let $A$ satisfy
$K \|e - A\| \le 1/2$. Then $A$ is invertible and $\|A^{-1} y\| \le 2K \|y\|$ for all $y$
(perturbation lemma). -/
private theorem exists_equiv_of_norm_le {A : E →L[𝕜] F} (e : E ≃L[𝕜] F) {K : ℝ}
    (hK : ‖(e.symm : F →L[𝕜] E)‖ ≤ K) (h : K * ‖(e : E →L[𝕜] F) - A‖ ≤ 1 / 2) :
    ∃ B : E ≃L[𝕜] F, (B : E →L[𝕜] F) = A ∧ ∀ y : F, ‖B.symm y‖ ≤ 2 * K * ‖y‖ := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hK
  have hmul : ‖(e.symm : F →L[𝕜] E)‖ * ‖A - (e : E →L[𝕜] F)‖ ≤ 1 / 2 := by
    rw [norm_sub_rev]
    exact le_trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) h
  obtain ⟨B, hB, hBnorm, -⟩ :=
    e.exists_symm_norm_le_of_add (A - (e : E →L[𝕜] F)) (by linarith)
  refine ⟨B, by rw [hB]; abel, fun y => ?_⟩
  have hle : ‖(B.symm : F →L[𝕜] E)‖ ≤ 2 * K := by
    refine hBnorm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hK0 (by linarith :
      (0 : ℝ) ≤ 1 / 2 - ‖(e.symm : F →L[𝕜] E)‖ * ‖A - (e : E →L[𝕜] F)‖)]
  exact le_trans ((B.symm : F →L[𝕜] E).le_opNorm y)
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

omit [CompleteSpace E] [CompleteSpace F] in
/-- If $F$ has derivative $F'$ on $B(x^*, r)$ and $F'$ is $L$-Lipschitz there, then $\|F(x^*) -
F(x) - F'(x)(x^* - x)\| \le (L/2) \|x^* - x\|^2$ for every $x \in B(x^*, r)$. -/
private theorem norm_sub_apply_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} {r L : ℝ}
    (hF : ∀ z ∈ Metric.ball xstar r, HasFDerivAt Fn (F' z) z)
    (hL : ∀ z ∈ Metric.ball xstar r, ∀ w ∈ Metric.ball xstar r, ‖F' z - F' w‖ ≤ L * ‖z - w‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) :
    ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ L / 2 * ‖xstar - x‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx)
  exact Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_ball xstar r) hF hx
    (Metric.mem_ball_self hr) fun z hz => hL z hz x hx

omit [CompleteSpace F] in
/-- **Local quadratic convergence of Newton's method.** Let $E$ be a Banach space and $V$ a normed
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let
$x^* \in E$ with $F(x^*) = 0$ and $F'(x^*)$ invertible. Let $r > 0$ and $L \in \mathbb{R}$,
suppose that $F$ has derivative $F'(x)$ at every $x \in B(x^*, r)$, and suppose that
$\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in B(x^*, r)$. Then there are $\delta > 0$
and $C \in \mathbb{R}$ such that
$$\|N(x) - x^*\| \le C \|x - x^*\|^2 \qquad \text{for all } x \in B(x^*, \delta).$$

This is Theorem 5.4.1 of [han2009theoretical], and Corollary 6.15 with Theorem 6.20 of
[kress1998numerical]. The proof shrinks the radius so that $F'(x)$ stays invertible by the
Neumann series, with $\|F'(x)^{-1}\| \le 2 \|F'(x^*)^{-1}\|$; the constant is
$C = \|F'(x^*)^{-1}\| \max\{L, 0\}$. The invertible $F'(x^*)$ is given as an equivalence `e`
with `(e : E →L[𝕜] F) = F' xstar`. -/
theorem exists_ball_norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E}
    (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ}
    (hr : 0 < r) (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x ∈ Metric.ball xstar δ,
      ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2 := by
  set K : ℝ := ‖(e.symm : F →L[𝕜] E)‖ with hKdef
  set L' : ℝ := max L 0 with hL'def
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hm : 0 ≤ K * L' := mul_nonneg hK0 hL'0
  refine ⟨min r (1 / (2 * (K * L' + 1))), lt_min hr (by positivity), K * L', fun x hx => ?_⟩
  have hxr : x ∈ Metric.ball xstar r := Metric.ball_subset_ball (min_le_left _ _) hx
  have hd : ‖x - xstar‖ < 1 / (2 * (K * L' + 1)) := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
  -- `F' x` is invertible with `‖(F' x)⁻¹‖ ≤ 2 K`
  have hclose : K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ 1 / 2 := by
    have h1 : ‖(e : E →L[𝕜] F) - F' x‖ ≤ L' * ‖x - xstar‖ := by
      rw [he]
      calc ‖F' xstar - F' x‖ ≤ L * ‖xstar - x‖ := hL xstar (Metric.mem_ball_self hr) x hxr
        _ ≤ L' * ‖xstar - x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = L' * ‖x - xstar‖ := by rw [norm_sub_rev]
    have h2 : K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ K * L' * ‖x - xstar‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hK0
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_left hd.le hm) ?_)
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨B, hB, hBnorm⟩ := exists_equiv_of_norm_le e hKdef.ge hclose
  have hinv : (F' x).inverse = (B.symm : F →L[𝕜] E) := by
    rw [← hB, ContinuousLinearMap.inverse_equiv]
  have hBsymm : ∀ z : E, B.symm (F' x z) = z := by
    intro z
    simp only [← hB, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hkey : step Fn F' x - xstar = B.symm (F' x (x - xstar) - Fn x) := by
    simp only [map_sub, hBsymm, step, hinv, ContinuousLinearEquiv.coe_coe]
    abel
  have hnorm : ‖step Fn F' x - xstar‖ ≤ 2 * K * ‖F' x (x - xstar) - Fn x‖ := by
    rw [hkey]
    exact hBnorm _
  have heq : Fn xstar - Fn x - F' x (xstar - x) = F' x (x - xstar) - Fn x := by
    rw [hstar, show (xstar - x : E) = -(x - xstar) by abel, map_neg]
    abel
  have htay : ‖F' x (x - xstar) - Fn x‖ ≤ L' / 2 * ‖xstar - x‖ ^ 2 := by
    have h := norm_sub_apply_le hF hL hxr
    rw [heq] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    linarith [le_max_left L 0]
  calc ‖step Fn F' x - xstar‖ ≤ 2 * K * ‖F' x (x - xstar) - Fn x‖ := hnorm
    _ ≤ 2 * K * (L' / 2 * ‖xstar - x‖ ^ 2) := mul_le_mul_of_nonneg_left htay (by positivity)
    _ = K * L' * ‖x - xstar‖ ^ 2 := by rw [norm_sub_rev xstar x]; ring

omit [CompleteSpace E] [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- If $F'(z)$ is invertible with inverse $e^{-1}$, then $N(z) - z = -e^{-1} F(z)$. -/
private theorem step_sub_self {Fn : E → F} {F' : E → E →L[𝕜] F} {z : E} (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' z) : step Fn F' z - z = -(e.symm (Fn z)) := by
  have hinv : (F' z).inverse = (e.symm : F →L[𝕜] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  simp only [step, hinv, ContinuousLinearEquiv.coe_coe]
  abel

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Newton error bound with explicit constant.** Let $E$ and $V$ be normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let $x^* \in E$ with
$F(x^*) = 0$. Let $r, L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every
$x \in B(x^*, r)$, and suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all
$x, y \in B(x^*, r)$. If $x \in B(x^*, r)$ and $F'(x)$ is invertible, then
$$\|N(x) - x^*\| \le \frac{L \|F'(x)^{-1}\|}{2} \|x - x^*\|^2.$$

The invertible $F'(x)$ is given as an equivalence `e` with `(e : E →L[𝕜] F) = F' x`. -/
theorem norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    {r L : ℝ} (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x) :
    ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
  have htay : ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ L / 2 * ‖xstar - x‖ ^ 2 :=
    norm_sub_apply_le hF hL hx
  have hinv : (F' x).inverse = (e.symm : F →L[𝕜] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hesymm : ∀ z : E, e.symm (F' x z) = z := by
    intro z
    simp only [← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hkey : step Fn F' x - xstar = e.symm (F' x (x - xstar) - Fn x) := by
    simp only [map_sub, hesymm, step, hinv, ContinuousLinearEquiv.coe_coe]
    abel
  have heq : Fn xstar - Fn x - F' x (xstar - x) = F' x (x - xstar) - Fn x := by
    rw [hstar, show (xstar - x : E) = -(x - xstar) by abel, map_neg]
    abel
  rw [heq] at htay
  calc ‖step Fn F' x - xstar‖ = ‖(e.symm : F →L[𝕜] E) (F' x (x - xstar) - Fn x)‖ := by
        rw [hkey]; rfl
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x (x - xstar) - Fn x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖ * (L / 2 * ‖xstar - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htay (norm_nonneg _)
    _ = L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
        rw [norm_sub_rev xstar x]; ring

omit [CompleteSpace F] in
/-- **Local convergence of Newton's method.** Let $E$ be a Banach space and $V$ a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let $x^* \in E$ with
$F(x^*) = 0$ and $F'(x^*)$ invertible. Let $r > 0$ and $L \in \mathbb{R}$, suppose that $F$ has
derivative $F'(x)$ at every $x \in B(x^*, r)$, and suppose that
$\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in B(x^*, r)$. Then there is $\delta > 0$
such that for every $x_0 \in B(x^*, \delta)$ the Newton iterates $x_k$ converge to $x^*$. -/
theorem tendsto_iterate {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball xstar δ,
      Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_ball_norm_step_sub_le hstar e he hr hF hL
  set C' : ℝ := max C 1 with hC'def
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ' : ℝ := min δ (1 / (2 * C')) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ (by positivity)
  have hhalf : ∀ x ∈ Metric.ball xstar δ', ‖step Fn F' x - xstar‖ ≤ 1 / 2 * ‖x - xstar‖ := by
    intro x hx
    have hxδ : x ∈ Metric.ball xstar δ := Metric.ball_subset_ball (min_le_left _ _) hx
    have h1 : ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2 := hC x hxδ
    have h2 : ‖x - xstar‖ < 1 / (2 * C') := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
    have h3 : C * ‖x - xstar‖ ^ 2 ≤ C' * ‖x - xstar‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h5 : C' * ‖x - xstar‖ ≤ 1 / 2 := by
      calc C' * ‖x - xstar‖ ≤ C' * (1 / (2 * C')) := mul_le_mul_of_nonneg_left h2.le hC'0.le
        _ = 1 / 2 := by field_simp
    nlinarith [norm_nonneg (x - xstar)]
  have hmaps : ∀ x ∈ Metric.ball xstar δ', step Fn F' x ∈ Metric.ball xstar δ' := by
    intro x hx
    have h1 := hhalf x hx
    have h2 : ‖x - xstar‖ < δ' := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hx
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [norm_nonneg (x - xstar)]
  refine ⟨δ', hδ'0, fun x₀ hx₀ => ?_⟩
  have hind : ∀ k, iterate Fn F' x₀ k ∈ Metric.ball xstar δ' ∧
      ‖iterate Fn F' x₀ k - xstar‖ ≤ (1 / 2 : ℝ) ^ k * ‖x₀ - xstar‖ := by
    intro k
    induction k with
    | zero => exact ⟨hx₀, by simp [iterate]⟩
    | succ k ih =>
      refine ⟨by rw [iterate_succ]; exact hmaps _ ih.1, ?_⟩
      rw [iterate_succ]
      calc ‖step Fn F' (iterate Fn F' x₀ k) - xstar‖
          ≤ 1 / 2 * ‖iterate Fn F' x₀ k - xstar‖ := hhalf _ ih.1
        _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ k * ‖x₀ - xstar‖) :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) * ‖x₀ - xstar‖ := by ring
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hind k).2) ?_
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_const ‖x₀ - xstar‖


/-!
### Explicit constants and approximate derivatives

The next results keep the constants of the proof of `Newton.tendsto_iterate` visible, so that a
textbook statement with a named radius and a named constant is an instance and needs no new proof.
They then replace the exact derivative $F'(x_k)$ by an arbitrary approximation $B_k$. The chord
method, the difference-Jacobian method and the truncated Newton–SOR and Newton–Krylov methods are
instances.
-/

omit [CompleteSpace F] in
/-- **Newton's method with explicit radius and constant.** Let $E$ be a Banach space and $V$ a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let
$x^* \in E$ with $F(x^*) = 0$ and $F'(x^*)$ invertible, $\|F'(x^*)^{-1}\| \le K$. Let
$r, L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every $x \in B(x^*, r)$, and
suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in B(x^*, r)$. Let
$\delta = \min\{r, 1/(2KL)\}$ and $x_0 \in B(x^*, \delta)$. Then for every $k$ the Newton
iterate $x_k$ lies in $B(x^*, \delta)$, $F'(x_k)$ is invertible with $\|F'(x_k)^{-1}\| \le 2K$,
and
$$\|x_{k+1} - x^*\| \le K L \|x_k - x^*\|^2, \qquad \|x_{k+1} - x^*\| \le \tfrac{1}{2} \|x_k -
  x^*\|.$$

This is Theorem 7.1 of [quarteroni2000numerical] and Theorem 5.4.1 of [han2009theoretical]. No
sign conditions on $r$, $K$ or $L$ are needed: if $KL \le 0$ or $r \le 0$, then the ball is
empty and the statement is vacuous. The invertibility of $F'(x_k)$ comes from the Neumann
series. -/
theorem forall_norm_iterate_succ_sub_le_of_mem_ball {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E}
    (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {K r L : ℝ}
    (hK : ‖(e.symm : F →L[𝕜] E)‖ ≤ K)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x₀ : E} (hx₀ : x₀ ∈ Metric.ball xstar (min r (1 / (2 * K * L)))) (k : ℕ) :
    iterate Fn F' x₀ k ∈ Metric.ball xstar (min r (1 / (2 * K * L))) ∧
      (∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' (iterate Fn F' x₀ k) ∧
        ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * K) ∧
      ‖iterate Fn F' x₀ (k + 1) - xstar‖ ≤ K * L * ‖iterate Fn F' x₀ k - xstar‖ ^ 2 ∧
      ‖iterate Fn F' x₀ (k + 1) - xstar‖ ≤ ‖iterate Fn F' x₀ k - xstar‖ / 2 := by
  set δ := min r (1 / (2 * K * L)) with hδdef
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hδpos : 0 < δ := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx₀)
  have hr : 0 < r := lt_of_lt_of_le hδpos (min_le_left _ _)
  have hKL : 0 < K * L := by
    have h : 0 < 1 / (2 * K * L) := lt_of_lt_of_le hδpos (min_le_right _ _)
    rw [one_div_pos] at h
    linarith
  have hL0 : 0 < L := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hKL with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (not_lt.2 hK0)
  -- one step from a point of the ball
  have hstep : ∀ x ∈ Metric.ball xstar δ,
      (∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' x ∧ ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * K) ∧
        ‖step Fn F' x - xstar‖ ≤ K * L * ‖x - xstar‖ ^ 2 ∧
        ‖step Fn F' x - xstar‖ ≤ ‖x - xstar‖ / 2 ∧ step Fn F' x ∈ Metric.ball xstar δ := by
    intro x hx
    have hxr : x ∈ Metric.ball xstar r := Metric.ball_subset_ball (min_le_left _ _) hx
    have hxδ : ‖x - xstar‖ < δ := by rw [← dist_eq_norm]; exact hx
    have hd : ‖x - xstar‖ < 1 / (2 * K * L) := lt_of_lt_of_le hxδ (min_le_right _ _)
    have hd' : K * L * ‖x - xstar‖ ≤ 1 / 2 := by
      rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * K * L)] at hd
      linarith
    have hclose : K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ 1 / 2 := by
      have h1 : ‖(e : E →L[𝕜] F) - F' x‖ ≤ L * ‖x - xstar‖ := by
        rw [he, norm_sub_rev x xstar]
        exact hL xstar (Metric.mem_ball_self hr) x hxr
      calc K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ K * (L * ‖x - xstar‖) := by gcongr
        _ = K * L * ‖x - xstar‖ := by ring
        _ ≤ 1 / 2 := hd'
    obtain ⟨B, hB, hBnorm⟩ := exists_equiv_of_norm_le e hK hclose
    have hBle : ‖(B.symm : F →L[𝕜] E)‖ ≤ 2 * K :=
      ContinuousLinearMap.opNorm_le_bound _ (by linarith) hBnorm
    have h3 : ‖step Fn F' x - xstar‖ ≤ K * L * ‖x - xstar‖ ^ 2 := by
      calc ‖step Fn F' x - xstar‖
          ≤ L * ‖(B.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 :=
            norm_step_sub_le hstar hF hL hxr B hB
        _ ≤ L * (2 * K) / 2 * ‖x - xstar‖ ^ 2 := by gcongr
        _ = K * L * ‖x - xstar‖ ^ 2 := by ring
    have h4 : ‖step Fn F' x - xstar‖ ≤ ‖x - xstar‖ / 2 := by
      calc ‖step Fn F' x - xstar‖ ≤ K * L * ‖x - xstar‖ ^ 2 := h3
        _ = K * L * ‖x - xstar‖ * ‖x - xstar‖ := by ring
        _ ≤ 1 / 2 * ‖x - xstar‖ := mul_le_mul_of_nonneg_right hd' (norm_nonneg _)
        _ = ‖x - xstar‖ / 2 := by ring
    refine ⟨⟨B, hB, hBle⟩, h3, h4, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [norm_nonneg (x - xstar)]
  have hmem : ∀ k, iterate Fn F' x₀ k ∈ Metric.ball xstar δ := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih => rw [iterate_succ]; exact (hstep _ ih).2.2.2
  obtain ⟨h1, h2, h3, -⟩ := hstep _ (hmem k)
  exact ⟨hmem k, h1, by rw [iterate_succ]; exact h2, by rw [iterate_succ]; exact h3⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **One step with an approximate derivative.** Let $E$ and $V$ be normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let $x^* \in E$ with
$F(x^*) = 0$. Let $r, L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every
$x \in B(x^*, r)$, and suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all
$x, y \in B(x^*, r)$. Let $x \in B(x^*, r)$, and let $B \colon E \to V$ be an invertible
continuous linear map with $\|B - F'(x)\| \le \eta$. Then
$$\|x - B^{-1} F(x) - x^*\| \le \|B^{-1}\| \Bigl(\eta \|x - x^*\| + \frac{L}{2} \|x -
  x^*\|^2\Bigr).$$

The first term comes from the error of the derivative and the second from the second-order
Taylor remainder. The chord method ($\eta = \|A - F'(x)\|$), the difference-Jacobian method of
§7.1.2 of [quarteroni2000numerical] and the truncated Newton–SOR and Newton–Krylov methods are
instances, and `Newton.norm_step_sub_le` is the case $\eta = 0$. -/
theorem norm_approxStep_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E}
    (hstar : Fn xstar = 0) {r L : ℝ} (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) (B : E ≃L[𝕜] F) {η : ℝ}
    (hB : ‖(B : E →L[𝕜] F) - F' x‖ ≤ η) :
    ‖x - B.symm (Fn x) - xstar‖
      ≤ ‖(B.symm : F →L[𝕜] E)‖ * (η * ‖x - xstar‖ + L / 2 * ‖x - xstar‖ ^ 2) := by
  have htay : ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ L / 2 * ‖xstar - x‖ ^ 2 :=
    norm_sub_apply_le hF hL hx
  rw [norm_sub_rev xstar x] at htay
  have hsplit : ((B : E →L[𝕜] F) - F' x) (x - xstar) + (Fn xstar - Fn x - F' x (xstar - x))
      = B (x - xstar) - Fn x := by
    rw [hstar, sub_apply, ContinuousLinearEquiv.coe_coe,
      show xstar - x = -(x - xstar) by abel, map_neg]
    abel
  have hkey : x - B.symm (Fn x) - xstar = B.symm (B (x - xstar) - Fn x) := by
    rw [map_sub, B.symm_apply_apply]
    abel
  rw [hkey, ← hsplit]
  calc ‖B.symm (((B : E →L[𝕜] F) - F' x) (x - xstar) + (Fn xstar - Fn x - F' x (xstar - x)))‖
      ≤ ‖(B.symm : F →L[𝕜] E)‖ *
          ‖((B : E →L[𝕜] F) - F' x) (x - xstar) + (Fn xstar - Fn x - F' x (xstar - x))‖ :=
        ContinuousLinearMap.le_opNorm (B.symm : F →L[𝕜] E) _
    _ ≤ ‖(B.symm : F →L[𝕜] E)‖ *
          (‖((B : E →L[𝕜] F) - F' x) (x - xstar)‖ + ‖Fn xstar - Fn x - F' x (xstar - x)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖(B.symm : F →L[𝕜] E)‖ * (η * ‖x - xstar‖ + L / 2 * ‖x - xstar‖ ^ 2) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

omit [CompleteSpace F] in
/-- **Linear convergence of Newton-like methods with approximate derivatives.** Let $E$ be a Banach
space and $V$ a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let
$F \colon E \to V$, and let $x^* \in E$ with $F(x^*) = 0$ and $F'(x^*)$ invertible. Let $r > 0$
and $L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every $x \in B(x^*, r)$, and
suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in B(x^*, r)$. Then there are
$\delta$ with $0 < \delta \le r$ and $\eta > 0$ with the following property. Let $(x_k)$ be a
sequence in $E$ and $(B_k)$ a sequence of continuous linear maps from $E$ to $V$, with
$x_0 \in B(x^*, \delta)$, $\|B_k - F'(x_k)\| \le \eta$ for all $k$, and
$x_{k+1} = x_k - B_k^{-1} F(x_k)$ for all $k$. Then for all $k$, $x_k \in B(x^*, \delta)$, $B_k$
is invertible with $\|B_k^{-1}\| \le 2 \|F'(x^*)^{-1}\|$, and
$\|x_{k+1} - x^*\| \le \|x_k - x^*\|/2$; and $x_k \to x^*$.

This is the first part of Property 7.1 of [quarteroni2000numerical] and Theorem 6.21 of
[kress1998numerical]. In the recurrence, $B_k^{-1}$ is `ContinuousLinearMap.inverse`, as in
`Newton.step`, so that the invertibility of $B_k$ is a conclusion and not a hypothesis; it
follows from the Neumann series, since $\|B_k - F'(x^*)\| \le \eta + L\delta$ is small. The
$B_k$ form an arbitrary sequence and not a function of $x_k$, because in the applications
(Broyden's method, truncated inner iterations) they depend on the whole history. -/
theorem tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le {Fn : E → F}
    {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, δ ≤ r ∧ ∃ η > 0, ∀ (x : ℕ → E) (B : ℕ → E →L[𝕜] F), x 0 ∈ Metric.ball xstar δ →
      (∀ k, ‖B k - F' (x k)‖ ≤ η) → (∀ k, x (k + 1) = x k - (B k).inverse (Fn (x k))) →
      (∀ k, x k ∈ Metric.ball xstar δ) ∧
        (∀ k, ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = B k ∧
          ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * ‖(e.symm : F →L[𝕜] E)‖) ∧
        (∀ k, ‖x (k + 1) - xstar‖ ≤ ‖x k - xstar‖ / 2) ∧ Tendsto x atTop (𝓝 xstar) := by
  set K : ℝ := ‖(e.symm : F →L[𝕜] E)‖ with hKdef
  set L' : ℝ := max L 0 with hL'def
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hLL' : L ≤ L' := le_max_left _ _
  have h8 : (0 : ℝ) < 8 * (K + 1) * (L' + 1) := by positivity
  have h8' : (0 : ℝ) < 8 * (K + 1) := by positivity
  refine ⟨min r (1 / (8 * (K + 1) * (L' + 1))), lt_min hr (one_div_pos.2 h8), min_le_left _ _,
    1 / (8 * (K + 1)), one_div_pos.2 h8', fun x B hx0 hB hstep => ?_⟩
  set δ : ℝ := min r (1 / (8 * (K + 1) * (L' + 1))) with hδdef
  set η : ℝ := 1 / (8 * (K + 1)) with hηdef
  have hδr : δ ≤ r := min_le_left _ _
  have hKη : K * η ≤ 1 / 8 := by
    rw [hηdef, mul_one_div, div_le_div_iff₀ h8' (by norm_num)]
    nlinarith
  have hKLδ : K * L' * δ ≤ 1 / 8 := by
    calc K * L' * δ ≤ K * L' * (1 / (8 * (K + 1) * (L' + 1))) := by
          gcongr
          exact min_le_right _ _
      _ ≤ 1 / 8 := by
          rw [mul_one_div, div_le_div_iff₀ h8 (by norm_num)]
          nlinarith [mul_nonneg hK0 hL'0]
  -- one step from a point of the ball
  have hone : ∀ k, x k ∈ Metric.ball xstar δ →
      (∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = B k ∧ ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * K) ∧
        ‖x (k + 1) - xstar‖ ≤ ‖x k - xstar‖ / 2 := by
    intro k hxk
    have hxr : x k ∈ Metric.ball xstar r := Metric.ball_subset_ball hδr hxk
    have hd : ‖x k - xstar‖ < δ := by rw [← dist_eq_norm]; exact hxk
    have hn : 0 ≤ ‖x k - xstar‖ := norm_nonneg _
    have hclose : K * ‖(e : E →L[𝕜] F) - B k‖ ≤ 1 / 2 := by
      have h1 : ‖(e : E →L[𝕜] F) - B k‖ ≤ L' * ‖x k - xstar‖ + η := by
        calc ‖(e : E →L[𝕜] F) - B k‖ = ‖(F' xstar - F' (x k)) + (F' (x k) - B k)‖ := by
              rw [he]; congr 1; abel
          _ ≤ ‖F' xstar - F' (x k)‖ + ‖F' (x k) - B k‖ := norm_add_le _ _
          _ ≤ L * ‖xstar - x k‖ + η := by
              gcongr
              · exact hL xstar (Metric.mem_ball_self hr) (x k) hxr
              · rw [norm_sub_rev]; exact hB k
          _ ≤ L' * ‖x k - xstar‖ + η := by
              rw [norm_sub_rev xstar]
              gcongr
      calc K * ‖(e : E →L[𝕜] F) - B k‖ ≤ K * (L' * ‖x k - xstar‖ + η) := by gcongr
        _ ≤ K * (L' * δ + η) := by gcongr
        _ = K * L' * δ + K * η := by ring
        _ ≤ 1 / 2 := by linarith
    obtain ⟨e', he', he'n⟩ := exists_equiv_of_norm_le e hKdef.ge hclose
    have he'le : ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * K :=
      ContinuousLinearMap.opNorm_le_bound _ (by linarith) he'n
    have hinv : (B k).inverse = (e'.symm : F →L[𝕜] E) := by
      rw [← he', ContinuousLinearMap.inverse_equiv]
    have hxsucc : x (k + 1) = x k - e'.symm (Fn (x k)) := by rw [hstep k, hinv]; rfl
    refine ⟨⟨e', he', he'le⟩, ?_⟩
    have hsq : ‖x k - xstar‖ ^ 2 ≤ δ * ‖x k - xstar‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hd.le hn
    calc ‖x (k + 1) - xstar‖ = ‖x k - e'.symm (Fn (x k)) - xstar‖ := by rw [hxsucc]
      _ ≤ ‖(e'.symm : F →L[𝕜] E)‖ * (η * ‖x k - xstar‖ + L / 2 * ‖x k - xstar‖ ^ 2) :=
          norm_approxStep_sub_le hstar hF hL hxr e' (by rw [he']; exact hB k)
      _ ≤ 2 * K * (η * ‖x k - xstar‖ + L' / 2 * (δ * ‖x k - xstar‖)) := by
          have hL0 : 0 ≤ L * ‖x k - xstar‖ :=
            (norm_nonneg _).trans (hL (x k) hxr xstar (Metric.mem_ball_self hr))
          have hη0 : 0 < η := one_div_pos.2 h8'
          have hc0 : 0 ≤ η * ‖x k - xstar‖ + L / 2 * ‖x k - xstar‖ ^ 2 := by
            nlinarith [mul_nonneg hL0 hn, mul_nonneg hη0.le hn]
          refine mul_le_mul he'le (add_le_add le_rfl (mul_le_mul (by linarith) hsq
            (by positivity) (by linarith))) hc0 (by linarith)
      _ = (2 * (K * η) + K * L' * δ) * ‖x k - xstar‖ := by ring
      _ ≤ (2 * (1 / 8) + 1 / 8) * ‖x k - xstar‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hn
      _ ≤ ‖x k - xstar‖ / 2 := by linarith
  have hmem : ∀ k, x k ∈ Metric.ball xstar δ := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
      have h := (hone k ih).2
      have hd : ‖x k - xstar‖ < δ := by rw [← dist_eq_norm]; exact ih
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [norm_nonneg (x k - xstar)]
  refine ⟨hmem, fun k => (hone k (hmem k)).1, fun k => (hone k (hmem k)).2, ?_⟩
  refine tendsto_of_eventually_norm_sub_succ_le (by norm_num : (1 / 2 : ℝ) < 1)
    (Filter.Eventually.of_forall fun k => ?_)
  have h := (hone k (hmem k)).2
  linarith

omit [CompleteSpace E] [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
open scoped Classical in
/-- The Newton-like recursion $x_{k+1} = x_k - B_k(x_k)^{-1} F(x_k)$ with the approximate derivative
$B_k(x_k)$ used while $x_k \in S$ and the exact derivative $F'(x_k)$ used outside $S$. -/
private noncomputable def guardedIterate (Fn : E → F) (F' : E → E →L[𝕜] F)
    (B : ℕ → E → E →L[𝕜] F) (S : Set E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 =>
    let z := guardedIterate Fn F' B S x₀ k
    z - (if z ∈ S then B k z else F' z).inverse (Fn z)

omit [CompleteSpace F] in
/-- **Linear convergence of Newton-like methods with approximate derivatives that depend on the
iterate.** Let $E$ be a Banach space and $V$ a normed space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $F \colon E \to V$, and let $x^* \in E$ with $F(x^*) = 0$ and $F'(x^*)$
invertible. Let $r > 0$ and $L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every
$x \in B(x^*, r)$, and suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all
$x, y \in B(x^*, r)$. Then there are $\delta$ with $0 < \delta \le r$ and $\eta > 0$ with the
following property. Let $B_k(z)$, for $k \in \mathbb{N}$ and $z \in E$, be continuous linear
maps from $E$ to $V$ with $\|B_k(z) - F'(z)\| \le \eta$ for all $k$ and all
$z \in B(x^*, \delta)$, and let $(x_k)$ be a sequence with $x_0 \in B(x^*, \delta)$ and
$x_{k+1} = x_k - B_k(x_k)^{-1} F(x_k)$ for all $k$. Then for all $k$, $x_k \in B(x^*, \delta)$,
$B_k(x_k)$ is invertible with $\|B_k(x_k)^{-1}\| \le 2 \|F'(x^*)^{-1}\|$, and
$\|x_{k+1} - x^*\| \le \|x_k - x^*\|/2$; and $x_k \to x^*$.

This is Property 7.1 of [quarteroni2000numerical] in the form needed for the difference Jacobian
(7.10). The hypothesis on $B_k$ holds only on the ball, while
`Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le` asks for it along the
sequence. That theorem uses its hypothesis only at iterates in the ball, so this one follows
from it, applied to the recursion that uses the exact derivative outside the ball. -/
theorem tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le_of_mem
    {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, δ ≤ r ∧ ∃ η > 0, ∀ (B : ℕ → E → E →L[𝕜] F) (x : ℕ → E),
      x 0 ∈ Metric.ball xstar δ → (∀ k, ∀ z ∈ Metric.ball xstar δ, ‖B k z - F' z‖ ≤ η) →
      (∀ k, x (k + 1) = x k - (B k (x k)).inverse (Fn (x k))) →
      (∀ k, x k ∈ Metric.ball xstar δ) ∧
        (∀ k, ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = B k (x k) ∧
          ‖(e'.symm : F →L[𝕜] E)‖ ≤ 2 * ‖(e.symm : F →L[𝕜] E)‖) ∧
        (∀ k, ‖x (k + 1) - xstar‖ ≤ ‖x k - xstar‖ / 2) ∧ Tendsto x atTop (𝓝 xstar) := by
  classical
  obtain ⟨δ, hδ, hδr, η, hη, hmain⟩ :=
    tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le hstar e he hr hF hLip
  refine ⟨δ, hδ, hδr, η, hη, fun B x hx0 hB hstep => ?_⟩
  let x' : ℕ → E := guardedIterate Fn F' B (Metric.ball xstar δ) (x 0)
  let B' : ℕ → E →L[𝕜] F := fun k =>
    if x' k ∈ Metric.ball xstar δ then B k (x' k) else F' (x' k)
  have hx'0 : x' 0 = x 0 := rfl
  have hx'succ : ∀ k, x' (k + 1) = x' k - (B' k).inverse (Fn (x' k)) := fun k => by
    change guardedIterate Fn F' B (Metric.ball xstar δ) (x 0) (k + 1) = _
    rw [guardedIterate]
  have hB'η : ∀ k, ‖B' k - F' (x' k)‖ ≤ η := fun k => by
    change ‖(if x' k ∈ Metric.ball xstar δ then B k (x' k) else F' (x' k)) - F' (x' k)‖ ≤ η
    split_ifs with hmem
    · exact hB k _ hmem
    · rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hmem, hinv, hhalf, hlim⟩ := hmain x' B' (by rw [hx'0]; exact hx0) hB'η hx'succ
  -- the guarded sequence is the original one
  have heq : ∀ k, x' k = x k := by
    intro k
    induction k with
    | zero => exact hx'0
    | succ k ih =>
      have : B' k = B k (x k) := by
        have hm := hmem k
        rw [ih] at hm
        change (if x' k ∈ Metric.ball xstar δ then B k (x' k) else F' (x' k)) = B k (x k)
        simp only [ih, hm, ↓reduceIte]
      rw [hx'succ, hstep, ih, this]
  have hB'eq : ∀ k, B' k = B k (x k) := fun k => by
    have hm := hmem k
    rw [heq] at hm
    change (if x' k ∈ Metric.ball xstar δ then B k (x' k) else F' (x' k)) = B k (x k)
    simp only [heq, hm, ↓reduceIte]
  refine ⟨fun k => heq k ▸ hmem k, fun k => ?_, fun k => ?_, ?_⟩
  · obtain ⟨e', he', hn⟩ := hinv k
    exact ⟨e', by rw [he', hB'eq], hn⟩
  · have := hhalf k
    rwa [heq, heq] at this
  · exact hlim.congr heq

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Quadratic convergence of Newton-like methods with a first-order derivative error.** Let $E$
and $V$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$,
and let $x^* \in E$ with $F(x^*) = 0$. Let $r, L \in \mathbb{R}$, suppose that $F$ has
derivative $F'(x)$ at every $x \in B(x^*, r)$, and suppose that
$\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in B(x^*, r)$. Let $(x_k)$ be a sequence in
$B(x^*, r)$ and $(B_k)$ a sequence of invertible continuous linear maps from $E$ to $V$ with
$\|B_k^{-1}\| \le K$, $\|B_k - F'(x_k)\| \le C \|x_k - x^*\|$ and
$x_{k+1} = x_k - B_k^{-1} F(x_k)$ for all $k$. Then for every $k$,
$$\|x_{k+1} - x^*\| \le K \Bigl(C + \frac{L}{2}\Bigr) \|x_k - x^*\|^2.$$

This is the second part of Property 7.1 of [quarteroni2000numerical]. The hypotheses are the
conclusions of `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le`, with
$K = 2 \|F'(x^*)^{-1}\|$, so that theorem gives linear convergence and this one improves it to
quadratic convergence. The variant with $\|B_k - F'(x_k)\| \le c \|F(x_k)\|$ reduces to this
one, because $\|F(x)\| \le (\|F'(x^*)\| + Lr) \|x - x^*\|$ on the ball. -/
theorem norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul {Fn : E → F} {F' : E → E →L[𝕜] F}
    {xstar : E} (hstar : Fn xstar = 0) {r L : ℝ}
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : ℕ → E} {B : ℕ → E →L[𝕜] F} {K C : ℝ} (hx : ∀ k, x k ∈ Metric.ball xstar r)
    (hB : ∀ k, ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = B k ∧ ‖(e'.symm : F →L[𝕜] E)‖ ≤ K)
    (hstep : ∀ k, x (k + 1) = x k - (B k).inverse (Fn (x k)))
    (hC : ∀ k, ‖B k - F' (x k)‖ ≤ C * ‖x k - xstar‖) (k : ℕ) :
    ‖x (k + 1) - xstar‖ ≤ K * (C + L / 2) * ‖x k - xstar‖ ^ 2 := by
  obtain ⟨e', he', he'n⟩ := hB k
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp (hx k))
  have hn : 0 ≤ ‖x k - xstar‖ := norm_nonneg _
  have hC0 : 0 ≤ C * ‖x k - xstar‖ := (norm_nonneg _).trans (hC k)
  have hL0 : 0 ≤ L * ‖x k - xstar‖ :=
    (norm_nonneg _).trans (hL _ (hx k) _ (Metric.mem_ball_self hr))
  have hnn : 0 ≤ C * ‖x k - xstar‖ * ‖x k - xstar‖ + L / 2 * ‖x k - xstar‖ ^ 2 := by
    nlinarith
  have hinv : (B k).inverse = (e'.symm : F →L[𝕜] E) := by
    rw [← he', ContinuousLinearMap.inverse_equiv]
  have hxsucc : x (k + 1) = x k - e'.symm (Fn (x k)) := by rw [hstep k, hinv]; rfl
  calc ‖x (k + 1) - xstar‖ = ‖x k - e'.symm (Fn (x k)) - xstar‖ := by rw [hxsucc]
    _ ≤ ‖(e'.symm : F →L[𝕜] E)‖ *
          (C * ‖x k - xstar‖ * ‖x k - xstar‖ + L / 2 * ‖x k - xstar‖ ^ 2) :=
        norm_approxStep_sub_le hstar hF hL (hx k) e' (by rw [he']; exact hC k)
    _ ≤ K * (C * ‖x k - xstar‖ * ‖x k - xstar‖ + L / 2 * ‖x k - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_right he'n hnn
    _ = K * (C + L / 2) * ‖x k - xstar‖ ^ 2 := by ring

end Quadratic

section Kantorovich

/-!
### The Newton–Kantorovich theorem

The proof follows the majorant method of [ortega2000iterative]. Let $\|F'(x_0)^{-1}\| \le \beta$,
$\|F'(x_0)^{-1} F(x_0)\| \le \eta$, and let $F'$ be $L$-Lipschitz; put $h = \beta L \eta$. The
Newton iterates of $F$ are dominated by the Newton iterates $t_k$, from $t_0 = 0$, of the scalar
quadratic
$$p(t) = \frac{L}{2} t^2 - \frac{t}{\beta} + \frac{\eta}{\beta},$$
whose roots are $t^* = (1 - \sqrt{1 - 2h})/(\beta L)$ and $t^{**} = (1 + \sqrt{1 - 2h})/(\beta L)$.
Instead of $t_k$ the proof uses the normalized quantity $s_k = 1 - \beta L t_k$, which is
`Newton.majorant u k` with $u = \sqrt{1 - 2h}$. In this variable the three parameters $\beta$, $L$
and $\eta$ reduce to the one parameter $u$. The scalar Newton recursion becomes the Babylonian
iteration $s \mapsto (s^2 + u^2)/(2s)$ for the square root of $u^2$, and the majorant relation that
drives the induction becomes the identity `Newton.majorant_sq_div`.
-/

/-- The **normalized Kantorovich majorant**: $s_0 = 1$ and $s_{k+1} = (s_k^2 + u^2)/(2 s_k)$, the
Babylonian iteration for the square root of $u^2$. With $u = \sqrt{1 - 2\beta L \eta}$ and $t_k$
the Newton iterates of $p(t) = (L/2) t^2 - t/\beta + \eta/\beta$ from $t_0 = 0$, one has
$s_k = 1 - \beta L t_k$.

The two facts that the induction needs, that $s_k$ decreases to $u$ and that $(s_k - s_{k+1})^2
/ (2 s_{k+1}) = s_{k+1} - s_{k+2}$, are then algebra; see `Newton.majorant_sq_div` and
`Newton.majorant_sub_le`. -/
noncomputable def majorant (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (majorant u k ^ 2 + u ^ 2) / (2 * majorant u k)

/-- The majorant starts at $s_0 = 1$, that is, the scalar Newton sequence starts at $t_0 = 0$. -/
@[simp] theorem majorant_zero (u : ℝ) : majorant u 0 = 1 := rfl

/-- The recursion of the majorant: $s_{k+1} = (s_k^2 + u^2)/(2 s_k)$. -/
theorem majorant_succ (u : ℝ) (k : ℕ) :
    majorant u (k + 1) = (majorant u k ^ 2 + u ^ 2) / (2 * majorant u k) := rfl

/-- For every real $u$ and every $k$, $s_k > 0$. So every scalar iterate $t_k$ stays strictly below
$1/(\beta L)$, and the perturbed derivatives stay invertible. -/
theorem majorant_pos (u : ℝ) (k : ℕ) : 0 < majorant u k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [majorant_succ]
    exact div_pos (by nlinarith) (by linarith)

/-- For every real $u$ and every $k$, $s_k \neq 0$. -/
theorem majorant_ne_zero (u : ℝ) (k : ℕ) : majorant u k ≠ 0 := (majorant_pos u k).ne'

/-- The distance of the majorant to its limit $u$ obeys the Newton square law:
$s_{k+1} - u = (s_k - u)^2 / (2 s_k)$. -/
theorem majorant_succ_sub (u : ℝ) (k : ℕ) :
    majorant u (k + 1) - u = (majorant u k - u) ^ 2 / (2 * majorant u k) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_succ]
  field_simp
  ring

/-- The increment of the majorant: $s_k - s_{k+1} = (s_k^2 - u^2)/(2 s_k)$. -/
theorem majorant_sub_succ (u : ℝ) (k : ℕ) :
    majorant u k - majorant u (k + 1) = (majorant u k ^ 2 - u ^ 2) / (2 * majorant u k) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_succ]
  field_simp
  ring

/-- If $0 \le u \le 1$, then $u \le s_k$ for every $k$. -/
theorem le_majorant {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) : u ≤ majorant u k := by
  induction k with
  | zero => simpa using hu1
  | succ k ih =>
    have h := majorant_succ_sub u k
    have hnn : 0 ≤ (majorant u k - u) ^ 2 / (2 * majorant u k) :=
      div_nonneg (sq_nonneg _) (by linarith [majorant_pos u k])
    linarith

/-- If $0 \le u \le 1$, then $s_{k+1} \le s_k$ for every $k$, so the scalar iterates $t_k$ increase.
Together with `Newton.majorant_le_one` and `Newton.le_majorant` this gives $u \le s_k \le 1$. -/
theorem majorant_succ_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    majorant u (k + 1) ≤ majorant u k := by
  have h := majorant_sub_succ u k
  have hk := le_majorant hu hu1 k
  have hp := majorant_pos u k
  have hnn : 0 ≤ (majorant u k ^ 2 - u ^ 2) / (2 * majorant u k) :=
    div_nonneg (by nlinarith) (by linarith)
  linarith

/-- If $0 \le u \le 1$, then $s_k \le 1$ for every $k$, that is, the scalar iterates $t_k$ are
nonnegative. -/
theorem majorant_le_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) : majorant u k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (majorant_succ_le hu hu1 k) ih

/-- The majorant relation: for every real $u$ and every $k$,
$$\frac{(s_k - s_{k+1})^2}{2 s_{k+1}} = s_{k+1} - s_{k+2}.$$
In the vector induction this says that a Newton step of length $(s_k - s_{k+1})/(\beta L)$
leaves a residual whose Newton step has length at most $(s_{k+1} - s_{k+2})/(\beta L)$. -/
theorem majorant_sq_div (u : ℝ) (k : ℕ) :
    (majorant u k - majorant u (k + 1)) ^ 2 / (2 * majorant u (k + 1))
      = majorant u (k + 1) - majorant u (k + 2) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_sub_succ u (k + 1), majorant_sub_succ u k, majorant_succ u k]
  field_simp
  ring

/-- For every real $u$ and every $k$, $s_k \ge 2^{-k}$: the majorant at most halves in each step.
This gives the sharp a priori bound `Newton.majorant_sub_le_pow`, and it is an equality in the
critical case $u = 0$. -/
theorem inv_two_pow_le_majorant (u : ℝ) (k : ℕ) : (1 / 2 : ℝ) ^ k ≤ majorant u k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := majorant_pos u k
    have hhalf : majorant u k / 2 ≤ majorant u (k + 1) := by
      rw [majorant_succ, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * majorant u k)]
      nlinarith [sq_nonneg u]
    calc (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
      _ ≤ majorant u k / 2 := by linarith
      _ ≤ majorant u (k + 1) := hhalf

/-- **The sharp quadratic decay of the majorant.** If $0 \le u \le 1$, then for every $k$
$$s_k - u \le \frac{(1 - u)^{2^k}}{2^k}.$$

Since $1 - u \le 1 - u^2$, this improves `Newton.majorant_sub_le`, with equality in the critical
case $u = 0$. It gives the a priori bound that [han2009theoretical] states. The proof combines
the square law `Newton.majorant_succ_sub` with `Newton.inv_two_pow_le_majorant`. -/
theorem majorant_sub_le_pow {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    majorant u k - u ≤ (1 - u) ^ (2 ^ k) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := majorant_pos u k
    have hx : 0 ≤ majorant u k - u := by linarith [le_majorant hu hu1 k]
    have hm : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hlow : (1 / 2 : ℝ) ^ k ≤ majorant u k := inv_two_pow_le_majorant u k
    have hinv : (1 : ℝ) ≤ (2 : ℝ) ^ k * majorant u k := by
      have h := mul_le_mul_of_nonneg_left hlow hm.le
      rwa [div_pow, one_pow, mul_one_div, div_self hm.ne'] at h
    have ihm : (majorant u k - u) * 2 ^ k ≤ (1 - u) ^ 2 ^ k := (le_div_iff₀ hm).mp ih
    have hsq : ((majorant u k - u) * 2 ^ k) ^ 2 ≤ ((1 - u) ^ 2 ^ k) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (by positivity) ihm
    have hsplit : (1 - u) ^ 2 ^ (k + 1) = ((1 - u) ^ 2 ^ k) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have hexp : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [majorant_succ_sub, hsplit, div_le_div_iff₀ (by linarith) (by positivity), hexp]
    nlinarith [mul_le_mul_of_nonneg_right hsq hs.le,
      mul_nonneg (mul_nonneg (sq_nonneg (majorant u k - u)) hm.le) (sub_nonneg.2 hinv)]

/-- The uniqueness recursion in the majorant variable: $(u + s_k)^2 / (2 s_k) = u + s_{k+1}$ for
every real $u$ and every $k$. This is why a second zero at distance $t^{**} = (1 + u)/(\beta L)$
from $x_0$ is exactly the borderline case. -/
theorem majorant_add_sq_div (u : ℝ) (k : ℕ) :
    (u + majorant u k) ^ 2 / (2 * majorant u k) = u + majorant u (k + 1) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_succ]
  field_simp
  ring

/-- Bernoulli's inequality in the form $1 \le 2^k u + (1 - u^2)^{2^k}$ for $0 \le u \le 1$. -/
private theorem one_le_two_pow_mul {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    1 ≤ (2 : ℝ) ^ k * u + (1 - u ^ 2) ^ (2 ^ k) := by
  have hb : 1 + ((2 ^ k : ℕ) : ℝ) * (-u ^ 2) ≤ (1 + -u ^ 2) ^ (2 ^ k) :=
    one_add_mul_le_pow (by nlinarith) _
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast] at hb
  have hkey : (1 : ℝ) - (2 : ℝ) ^ k * u ^ 2 ≤ (1 - u ^ 2) ^ (2 ^ k) := by
    calc (1 : ℝ) - (2 : ℝ) ^ k * u ^ 2 = 1 + (2 : ℝ) ^ k * (-u ^ 2) := by ring
      _ ≤ (1 + -u ^ 2) ^ (2 ^ k) := hb
      _ = (1 - u ^ 2) ^ (2 ^ k) := by ring_nf
  nlinarith [mul_nonneg (le_of_lt (show (0 : ℝ) < (2 : ℝ) ^ k by positivity)) hu]

/-- For reals with $u, x, P \ge 0$, $m > 0$, $m x \le P$, $1 \le m u + P$ and $s = u + x > 0$, one
has $x^2/(2s) \le P^2/(2m)$. -/
private theorem majorant_step_arith {x P m s u : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hm : 0 < m) (hQ : m * x ≤ P) (hone : 1 ≤ m * u + P) (hsx : s = u + x) (hs : 0 < s) :
    x ^ 2 / (2 * s) ≤ P ^ 2 / (2 * m) := by
  subst hsx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hQ)
      (by positivity : (0 : ℝ) ≤ u * (m * x + P) + P * x),
    mul_nonneg (mul_nonneg (sq_nonneg x) hm.le) (by linarith : (0 : ℝ) ≤ m * u + P - 1)]

/-- **Quadratic decay of the majorant.** If $0 \le u \le 1$, then for every $k$
$$s_k - u \le \frac{(1 - u^2)^{2^k}}{2^k}.$$
Since $1 - u^2 = 2 \beta L \eta$, this is the a priori bound of the Newton–Kantorovich theorem,
and it is an equality for $u = 0$, that is, in the critical case $\beta L \eta = 1/2$. -/
theorem majorant_sub_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    majorant u k - u ≤ (1 - u ^ 2) ^ (2 ^ k) / 2 ^ k := by
  induction k with
  | zero => simp only [majorant_zero, pow_zero, pow_one, div_one]; nlinarith
  | succ k ih =>
    have hm : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hs := majorant_pos u k
    have hx : 0 ≤ majorant u k - u := by linarith [le_majorant hu hu1 k]
    have hone := one_le_two_pow_mul hu hu1 k
    have hQ : (2 : ℝ) ^ k * (majorant u k - u) ≤ (1 - u ^ 2) ^ (2 ^ k) := by
      rw [le_div_iff₀ hm] at ih
      linarith
    have hsplit : (1 - u ^ 2) ^ (2 ^ (k + 1)) = ((1 - u ^ 2) ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [majorant_succ_sub, hsplit, h2]
    exact majorant_step_arith hu hx (pow_nonneg (by nlinarith) _) hm hQ hone (by ring) hs

variable [CompleteSpace E] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]

omit [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- If $\beta \ge 0$, $F'(x_0)$ is invertible with $\|F'(x_0)^{-1}\| \le \beta$, $F'$ is
$L$-Lipschitz on $\bar B(x_0, r)$, $z \in \bar B(x_0, r)$ and $\beta L \|z - x_0\| < 1$, then
$F'(z)$ is invertible with $\|F'(z)^{-1}\| \le \beta / (1 - \beta L \|z - x_0\|)$. -/
private theorem exists_equiv_of_dist_le {F' : E → E →L[𝕜] F} {x₀ : E} {r β L : ℝ} (hβ0 : 0 ≤ β)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀) (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : E} (hz : z ∈ Metric.closedBall x₀ r) (hzt : β * L * ‖z - x₀‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / (1 - β * L * ‖z - x₀‖) := by
  have hx0 : x₀ ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_self]
    exact le_trans dist_nonneg (Metric.mem_closedBall.mp hz)
  have ht : ‖F' z - F' x₀‖ ≤ L * ‖z - x₀‖ := hLip z hz x₀ hx0
  have hlt : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' z - F' x₀‖ < 1 := by
    calc ‖(e.symm : F →L[𝕜] E)‖ * ‖F' z - F' x₀‖ ≤ β * (L * ‖z - x₀‖) :=
          mul_le_mul hβ' ht (norm_nonneg _) hβ0
      _ = β * L * ‖z - x₀‖ := by ring
      _ < 1 := hzt
  obtain ⟨e', he'1, he'2, -⟩ := e.exists_symm_norm_le_of_add (F' z - F' x₀) hlt
  refine ⟨e', ?_, he'2.trans ?_⟩
  · rw [he'1, he]; abel
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hβ0 (norm_nonneg (e.symm : F →L[𝕜] E)))
      (sub_nonneg.2 ht), norm_nonneg (e.symm : F →L[𝕜] E)]

omit [CompleteSpace E] in
/-- If $F$ has derivative $F'$ on $\bar B(x_0, r)$, $F'$ is $L$-Lipschitz there, $z$ and $N(z)$ lie
in $\bar B(x_0, r)$, and $F'(z)$ is invertible, then $\|F(N(z))\| \le (L/2) \|N(z) - z\|^2$. -/
private theorem norm_apply_step_le {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r L : ℝ}
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : E} (hz : z ∈ Metric.closedBall x₀ r) (hsz : step Fn F' z ∈ Metric.closedBall x₀ r)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' z) :
    ‖Fn (step Fn F' z)‖ ≤ L / 2 * ‖step Fn F' z - z‖ ^ 2 := by
  have hstep : step Fn F' z - z = -(e.symm (Fn z)) := step_sub_self e he
  have happ : F' z (step Fn F' z - z) = -Fn z := by
    rw [hstep, map_neg, ← he]
    simp
  have htay := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le
    (convex_closedBall x₀ r) hF hz hsz fun w hw => hLip w hw z hz
  rw [happ] at htay
  simpa using htay

omit [CompleteSpace E] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- If $\beta L > 0$, $0 \le u \le 1$, $(1 - u)/(\beta L) \le r$ and
$\|z - x_0\| \le (1 - s_j)/(\beta L)$, then $z \in \bar B(x_0, r)$. -/
private theorem mem_closedBall_of_le_majorant {x₀ : E} {r β L u : ℝ} (hA : 0 < β * L) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hr : (1 - u) / (β * L) ≤ r) {j : ℕ} {z : E}
    (hz : ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L)) : z ∈ Metric.closedBall x₀ r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine hz.trans (le_trans ?_ hr)
  gcongr
  exact le_majorant hu0 hu1 j

omit [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- If $\beta, L > 0$, $F'(x_0)$ is invertible with $\|F'(x_0)^{-1}\| \le \beta$, $F'$ is
$L$-Lipschitz on $\bar B(x_0, r)$, $0 \le u \le 1$, $(1 - u)/(\beta L) \le r$ and
$\|z - x_0\| \le (1 - s_j)/(\beta L)$, then $F'(z)$ is invertible with
$\|F'(z)^{-1}\| \le \beta / s_j$. -/
private theorem exists_equiv_of_le_majorant {F' : E → E →L[𝕜] F} {x₀ : E} {r β L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : (1 - u) / (β * L) ≤ r) {j : ℕ} {z : E}
    (hz : ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L)) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / majorant u j := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hsj := majorant_pos u j
  have hAz : β * L * ‖z - x₀‖ ≤ 1 - majorant u j := by
    have h := mul_le_mul_of_nonneg_left hz hA.le
    rwa [mul_div_cancel₀ _ hA.ne'] at h
  obtain ⟨e', he'1, he'2⟩ := exists_equiv_of_dist_le hβ.le e he hβ' hLip
    (mem_closedBall_of_le_majorant hA hu0 hu1 hr hz) (by linarith)
  refine ⟨e', he'1, he'2.trans ?_⟩
  gcongr
  linarith

/-- Under the Kantorovich hypotheses, with $2 \beta L \eta = 1 - u^2$, the Newton iterates satisfy
$\|x_k - x_0\| \le (1 - s_k)/(\beta L)$ and $\|x_{k+1} - x_k\| \le (s_k - s_{k+1})/(\beta L)$
for every $k$. -/
private theorem kantorovich_invariant {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) (k : ℕ) :
    ‖iterate Fn F' x₀ k - x₀‖ ≤ (1 - majorant u k) / (β * L) ∧
      ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖
        ≤ (majorant u k - majorant u (k + 1)) / (β * L) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hmem : ∀ (j : ℕ) (z : E), ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L) →
      z ∈ Metric.closedBall x₀ r := fun _ _ hzj =>
    mem_closedBall_of_le_majorant hA hu0 hu1 hr hzj
  have hinvert : ∀ (j : ℕ) (z : E), ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L) →
      ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
        ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / majorant u j := fun _ _ hzj =>
    exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr hzj
  induction k with
  | zero =>
    refine ⟨by simp [iterate], ?_⟩
    have h1 : iterate Fn F' x₀ 1 = step Fn F' x₀ := by
      rw [iterate_succ]
      rfl
    have h0 : iterate Fn F' x₀ 0 = x₀ := rfl
    rw [h1, h0, step_sub_self e he, norm_neg]
    have hs1 : majorant u 1 = (1 + u ^ 2) / 2 := by
      rw [majorant_succ, majorant_zero]
      norm_num
    rw [hs1, majorant_zero]
    have hval : (1 - (1 + u ^ 2) / 2) / (β * L) = η := by
      field_simp
      nlinarith [hueta]
    rw [hval]
    exact hη'
  | succ k ih =>
    obtain ⟨hb, hd⟩ := ih
    have hb1 : ‖iterate Fn F' x₀ (k + 1) - x₀‖ ≤ (1 - majorant u (k + 1)) / (β * L) := by
      have hsplit : iterate Fn F' x₀ (k + 1) - x₀
          = (iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k) + (iterate Fn F' x₀ k - x₀) := by
        abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ((add_le_add hd hb).trans (le_of_eq ?_))
      ring
    refine ⟨hb1, ?_⟩
    obtain ⟨ek, hek, -⟩ := hinvert k _ hb
    obtain ⟨ek1, hek1, hek1n⟩ := hinvert (k + 1) _ hb1
    have hzk : iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r := hmem k _ hb
    have hzk1 : iterate Fn F' x₀ (k + 1) ∈ Metric.closedBall x₀ r := hmem (k + 1) _ hb1
    have hstep : step Fn F' (iterate Fn F' x₀ k) = iterate Fn F' x₀ (k + 1) :=
      (iterate_succ Fn F' x₀ k).symm
    have hFn : ‖Fn (iterate Fn F' x₀ (k + 1))‖
        ≤ L / 2 * ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖ ^ 2 := by
      have h := norm_apply_step_le hF hLip hzk (by rw [hstep]; exact hzk1) ek hek
      rwa [hstep] at h
    have hnext : ‖iterate Fn F' x₀ (k + 2) - iterate Fn F' x₀ (k + 1)‖
        ≤ ‖(ek1.symm : F →L[𝕜] E)‖ * ‖Fn (iterate Fn F' x₀ (k + 1))‖ := by
      rw [iterate_succ Fn F' x₀ (k + 1), step_sub_self ek1 hek1, norm_neg]
      exact ContinuousLinearMap.le_opNorm (ek1.symm : F →L[𝕜] E)
        (Fn (iterate Fn F' x₀ (k + 1)))
    have hs1 := majorant_pos u (k + 1)
    calc ‖iterate Fn F' x₀ (k + 2) - iterate Fn F' x₀ (k + 1)‖
        ≤ ‖(ek1.symm : F →L[𝕜] E)‖ * ‖Fn (iterate Fn F' x₀ (k + 1))‖ := hnext
      _ ≤ (β / majorant u (k + 1)) *
            (L / 2 * ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖ ^ 2) :=
          mul_le_mul hek1n hFn (norm_nonneg _) (by positivity)
      _ ≤ (β / majorant u (k + 1)) *
            (L / 2 * ((majorant u k - majorant u (k + 1)) / (β * L)) ^ 2) := by gcongr
      _ = ((majorant u k - majorant u (k + 1)) ^ 2 / (2 * majorant u (k + 1))) / (β * L) := by
          field_simp
      _ = (majorant u (k + 1) - majorant u (k + 2)) / (β * L) := by rw [majorant_sq_div]

/-- Under the Kantorovich hypotheses, with $2 \beta L \eta = 1 - u^2$,
$\|x_m - x_k\| \le (s_k - u)/(\beta L)$ for all $k \le m$. -/
private theorem norm_iterate_sub_iterate_le {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E}
    {r β η L u : ℝ} (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) {k m : ℕ} (hkm : k ≤ m) :
    ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖ ≤ (majorant u k - u) / (β * L) := by
  have hd : ∀ j, ‖iterate Fn F' x₀ (j + 1) - iterate Fn F' x₀ j‖
      ≤ (majorant u j - majorant u (j + 1)) / (β * L) := fun j =>
    (kantorovich_invariant hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr j).2
  have hchain : ∀ j m : ℕ, j ≤ m → ‖iterate Fn F' x₀ m - iterate Fn F' x₀ j‖
      ≤ (majorant u j - majorant u m) / (β * L) := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => simp
    | succ m hjm ih =>
      have hsp : iterate Fn F' x₀ (m + 1) - iterate Fn F' x₀ j
          = (iterate Fn F' x₀ (m + 1) - iterate Fn F' x₀ m)
            + (iterate Fn F' x₀ m - iterate Fn F' x₀ j) := by abel
      rw [hsp]
      refine (norm_add_le _ _).trans ((add_le_add (hd m) ih).trans (le_of_eq ?_))
      ring
  refine (hchain k m hkm).trans ?_
  gcongr
  exact le_majorant hu0 hu1 m

/-- Under the Kantorovich hypotheses, with $2 \beta L \eta = 1 - u^2$, if the Newton iterates
converge to $x^*$, then $\|x_k - x^*\| \le (s_k - u)/(\beta L)$ for every $k$. -/
private theorem norm_iterate_sub_le_majorant {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E}
    {r β η L u : ℝ} (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) {xstar : E}
    (hxstar : Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar)) (k : ℕ) :
    ‖iterate Fn F' x₀ k - xstar‖ ≤ (majorant u k - u) / (β * L) := by
  have h1 : Tendsto (fun m => ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖) atTop
      (𝓝 ‖xstar - iterate Fn F' x₀ k‖) := (hxstar.sub_const _).norm
  have h2 : ‖xstar - iterate Fn F' x₀ k‖ ≤ (majorant u k - u) / (β * L) :=
    le_of_tendsto h1 (Filter.eventually_atTop.2 ⟨k, fun m hm =>
      norm_iterate_sub_iterate_le hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr hm⟩)
  rwa [norm_sub_rev] at h2

/-- The Newton–Kantorovich theorem `Newton.kantorovich` with the limit $u$ of the majorant given as
a parameter that satisfies $0 \le u \le 1$ and $2 \beta L \eta = 1 - u^2$, and with
$(1 - u)/(\beta L) \le r$. -/
private theorem kantorovich_of_sq {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) :
    ∃ xstar ∈ Metric.closedBall x₀ ((1 - u) / (β * L)),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) ∧
      (∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r) ∧
      (0 < β * L * η → ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤
        (2 * (β * L * η)) ^ (2 ^ k) * η / (2 ^ k * (β * L * η))) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hinv := fun k => kantorovich_invariant hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr k
  have hb : ∀ k, ‖iterate Fn F' x₀ k - x₀‖ ≤ (1 - majorant u k) / (β * L) := fun k => (hinv k).1
  have hd : ∀ k, ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖
      ≤ (majorant u k - majorant u (k + 1)) / (β * L) := fun k => (hinv k).2
  have hstay : ∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r := fun k =>
    mem_closedBall_of_le_majorant hA hu0 hu1 hr (hb k)
  have herr : ∀ k m : ℕ, k ≤ m → ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖
      ≤ (majorant u k - u) / (β * L) := fun _ _ hkm =>
    norm_iterate_sub_iterate_le hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr hkm
  have herr0 : ∀ k, 0 ≤ (majorant u k - u) / (β * L) := fun k =>
    div_nonneg (by linarith [le_majorant hu0 hu1 k]) hA.le
  have herrle : ∀ k, (majorant u k - u) / (β * L) ≤ ((1 : ℝ) / 2) ^ k / (β * L) := by
    intro k
    gcongr
    refine (majorant_sub_le hu0 hu1 k).trans ?_
    rw [div_pow, one_pow]
    gcongr
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have htend : Tendsto (fun k => (majorant u k - u) / (β * L)) atTop (𝓝 0) := by
    refine squeeze_zero herr0 herrle ?_
    have h : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h.div_const (β * L)
  have hcauchy : CauchySeq (iterate Fn F' x₀) := by
    refine cauchySeq_of_le_tendsto_0' (fun k => (majorant u k - u) / (β * L)) ?_ htend
    intro n m hnm
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact herr n m hnm
  obtain ⟨xstar, hxstar⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxmem : ‖xstar - x₀‖ ≤ (1 - u) / (β * L) := by
    refine le_of_tendsto ((hxstar.sub_const x₀).norm) (Filter.Eventually.of_forall fun k => ?_)
    refine (hb k).trans ?_
    gcongr
    exact le_majorant hu0 hu1 k
  have hxball : xstar ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxmem.trans hr
  have hFnzero : ∀ k, ‖Fn (iterate Fn F' x₀ (k + 1))‖
      ≤ L / 2 * ((majorant u k - majorant u (k + 1)) / (β * L)) ^ 2 := by
    intro k
    obtain ⟨ek, hek, -⟩ := exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr (hb k)
    have hstep : step Fn F' (iterate Fn F' x₀ k) = iterate Fn F' x₀ (k + 1) :=
      (iterate_succ Fn F' x₀ k).symm
    have h := norm_apply_step_le hF hLip (hstay k) (by rw [hstep]; exact hstay (k + 1)) ek hek
    rw [hstep] at h
    refine h.trans ?_
    gcongr
    exact hd k
  have hFtend0 : Tendsto (fun k => Fn (iterate Fn F' x₀ (k + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) hFnzero ?_
    have h1 : Tendsto (fun k => (majorant u k - majorant u (k + 1)) / (β * L)) atTop (𝓝 0) := by
      refine squeeze_zero
        (fun k => div_nonneg (by linarith [majorant_succ_le hu0 hu1 k]) hA.le)
        (fun k => ?_) htend
      gcongr
      linarith [le_majorant hu0 hu1 (k + 1)]
    simpa using (h1.pow 2).const_mul (L / 2)
  have hFtend : Tendsto (fun k => Fn (iterate Fn F' x₀ (k + 1))) atTop (𝓝 (Fn xstar)) :=
    ((hF xstar hxball).continuousAt.tendsto).comp
      (hxstar.comp (Filter.tendsto_add_atTop_nat 1))
  have hroot : Fn xstar = 0 := tendsto_nhds_unique hFtend hFtend0
  have hapriori : ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤ (majorant u k - u) / (β * L) :=
    norm_iterate_sub_le_majorant hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr hxstar
  refine ⟨xstar, ?_, hroot, hxstar, hstay, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxmem
  · intro hpos k
    have hηpos : 0 < η := by
      rcases lt_or_ge 0 η with h | h
      · exact h
      · exact absurd hpos (by nlinarith)
    have hEq : (2 * (β * L * η)) ^ (2 ^ k) * η / ((2 : ℝ) ^ k * (β * L * η))
        = (1 - u ^ 2) ^ (2 ^ k) / (2 : ℝ) ^ k / (β * L) := by
      rw [hueta]
      field_simp
    rw [hEq]
    refine (hapriori k).trans ?_
    gcongr
    exact majorant_sub_le hu0 hu1 k

/-- **The Newton–Kantorovich theorem.** Let $E$ be a Banach space and $V$ a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, and let $x_0 \in E$. Let
$\beta > 0$, $L > 0$, $\eta \ge 0$ and $r$ be reals. Suppose that $F'(x_0)$ is invertible with
$\|F'(x_0)^{-1}\| \le \beta$ and $\|F'(x_0)^{-1} F(x_0)\| \le \eta$, that $F$ has derivative
$F'(x)$ at every $x \in \bar B(x_0, r)$, and that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all
$x, y \in \bar B(x_0, r)$. Let $h = \beta L \eta \le 1/2$, and suppose that
$t^* = (1 - \sqrt{1 - 2h})/(\beta L) \le r$. Then there is $x^* \in \bar B(x_0, t^*)$ with
$F(x^*) = 0$ such that the Newton iterates $x_k$ converge to $x^*$ and all lie in
$\bar B(x_0, r)$. If moreover $h > 0$, then for every $k$
$$\|x_k - x^*\| \le \frac{(2h)^{2^k} \eta}{2^k h}.$$

This is Theorem 5.4.2 of [han2009theoretical] and Theorem 6.14 of [kress1998numerical]. Unlike
`Newton.exists_ball_norm_step_sub_le`, all hypotheses are conditions at the starting point, and
the existence of the zero is a conclusion. The proof is the majorant method of
[ortega2000iterative], carried by `Newton.majorant`. -/
theorem kantorovich {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L : ℝ} (hβ : 0 < β)
    (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r) :
    ∃ xstar ∈ Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) ∧
      (∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r) ∧
      (0 < β * L * η → ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤
        (2 * (β * L * η)) ^ (2 ^ k) * η / (2 ^ k * (β * L * η))) := by
  have hh0 : (0 : ℝ) ≤ β * L * η := by positivity
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (1 - 2 * (β * L * η)) ≤ 1 := by nlinarith
  exact kantorovich_of_sq hβ hL e he hβ' hη' hF hLip hu0 hu1 (by linarith) hr

/-- Under the hypotheses of `Newton.kantorovich`, every derivative at a Newton iterate is
invertible. Precisely: let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
let $\beta, L > 0$ and $\eta \ge 0$, let $F'(x_0)$ be invertible with
$\|F'(x_0)^{-1}\| \le \beta$ and $\|F'(x_0)^{-1} F(x_0)\| \le \eta$, let $F$ have derivative
$F'$ on $\bar B(x_0, r)$ with $F'$ $L$-Lipschitz there, and let $h = \beta L \eta \le 1/2$ and
$(1 - \sqrt{1 - 2h})/(\beta L) \le r$. Then $F'(x_k)$ is invertible for every $k$. -/
theorem kantorovich_invertible {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E}
    {r β η L : ℝ} (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r)
    (k : ℕ) : ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' (iterate Fn F' x₀ k) := by
  set u := Real.sqrt (1 - 2 * (β * L * η))
  have hh0 : (0 : ℝ) ≤ β * L * η := by positivity
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt (by linarith)
  have hu1 : u ≤ 1 := by nlinarith
  have hb := (kantorovich_invariant hβ hL e he hβ' hη' hF hLip hu0 hu1
    (by linarith : 2 * (β * L * η) = 1 - u ^ 2) hr k).1
  obtain ⟨e', he', -⟩ := exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr hb
  exact ⟨e', he'⟩

/-- **The sharp a priori bound of the Newton–Kantorovich theorem.** Under the hypotheses of
`Newton.kantorovich` (with $E$ a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
$\beta, L > 0$, $\eta \ge 0$, $\|F'(x_0)^{-1}\| \le \beta$, $\|F'(x_0)^{-1} F(x_0)\| \le \eta$,
$F'$ the derivative of $F$ and $L$-Lipschitz on $\bar B(x_0, r)$, $h = \beta L \eta \le 1/2$ and
$(1 - \sqrt{1 - 2h})/(\beta L) \le r$), suppose that the Newton iterates converge to $x^*$. Then
for every $k$
$$\|x_k - x^*\| \le \frac{(1 - \sqrt{1 - 2h})^{2^k}}{2^k \beta L}.$$

This improves the bound $(2h)^{2^k} \eta / (2^k h)$ of `Newton.kantorovich`, because
$1 - \sqrt{1 - 2h} \le 2h$; the two bounds agree in the critical case $h = 1/2$. Both come from
the same estimate $\|x_k - x^*\| \le t^* - t_k$ against the scalar majorant sequence, with a
different closed-form bound on $t^* - t_k$: `Newton.majorant_sub_le_pow` here and
`Newton.majorant_sub_le` there. The limit $x^*$ is a hypothesis, since `Newton.kantorovich`
produces it under the same hypotheses, and a limit of the iterates is unique. -/
theorem kantorovich_norm_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r)
    {xstar : E} (hxstar : Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar)) (k : ℕ) :
    ‖iterate Fn F' x₀ k - xstar‖
      ≤ (1 - Real.sqrt (1 - 2 * (β * L * η))) ^ 2 ^ k / (2 ^ k * (β * L)) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hh0 : (0 : ℝ) ≤ β * L * η := mul_nonneg hA.le hη
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (1 - 2 * (β * L * η)) ≤ 1 := by nlinarith
  refine (norm_iterate_sub_le_majorant hβ hL e he hβ' hη' hF hLip hu0 hu1 (by linarith) hr
    hxstar k).trans ?_
  calc (majorant (Real.sqrt (1 - 2 * (β * L * η))) k
        - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)
      ≤ (1 - Real.sqrt (1 - 2 * (β * L * η))) ^ 2 ^ k / 2 ^ k / (β * L) := by
        gcongr
        exact majorant_sub_le_pow hu0 hu1 k
    _ = (1 - Real.sqrt (1 - 2 * (β * L * η))) ^ 2 ^ k / (2 ^ k * (β * L)) := div_div _ _ _

/-!
### Uniqueness of the Kantorovich zero

A second zero $y$ is compared with the iterates by the same Newton estimate that drives the
existence proof: if $\beta L \|y - x_k\| \le \varepsilon_k$, then $\beta L \|y - x_{k+1}\| \le
\varepsilon_k^2 / (2 s_k)$. The sequence $\varepsilon_k = u + s_k$ is a fixed trajectory of this
recursion (`Newton.majorant_add_sq_div`), and it starts at $1 + u = \beta L t^{**}$. A start
strictly below it therefore contracts to zero at a doubly exponential rate, and a start on it does
not move. So uniqueness holds in the open ball of radius $t^{**}$ and fails on its boundary, where
the scalar majorant polynomial itself has its second root.
-/

/-- Under the Kantorovich hypotheses, with $2 \beta L \eta = 1 - u^2$, a zero $y \in \bar B(x_0, r)$
of $F$ with $\beta L \|y - x_0\| \le c (1 + u)$ satisfies
$\beta L \|y - x_k\| \le c^{2^k} (u + s_k)$ for every $k$. -/
private theorem norm_sub_iterate_le_of_eq_zero {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E}
    {r β η L u c : ℝ} (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) {y : E} (hy : Fn y = 0) (hyr : y ∈ Metric.closedBall x₀ r)
    (hy0 : β * L * ‖y - x₀‖ ≤ c * (u + 1)) (k : ℕ) :
    β * L * ‖y - iterate Fn F' x₀ k‖ ≤ c ^ 2 ^ k * (u + majorant u k) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  induction k with
  | zero => simpa [iterate] using hy0
  | succ k ih =>
    have hb := (kantorovich_invariant hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr k).1
    have hxk : iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r :=
      mem_closedBall_of_le_majorant hA hu0 hu1 hr hb
    obtain ⟨ek, hek, hekn⟩ := exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr hb
    have hs := majorant_pos u k
    have htay : ‖Fn y - Fn (iterate Fn F' x₀ k)
        - F' (iterate Fn F' x₀ k) (y - iterate Fn F' x₀ k)‖
        ≤ L / 2 * ‖y - iterate Fn F' x₀ k‖ ^ 2 :=
      Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_closedBall x₀ r) hF hxk hyr
        fun w hw => hLip w hw _ hxk
    have hinv : ∀ z : E, ek.symm (F' (iterate Fn F' x₀ k) z) = z := fun z => by
      simp only [← hek, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    have hstepeq : iterate Fn F' x₀ (k + 1)
        = iterate Fn F' x₀ k - ek.symm (Fn (iterate Fn F' x₀ k)) := by
      rw [iterate_succ]
      have h := step_sub_self (Fn := Fn) (F' := F') (z := iterate Fn F' x₀ k) ek hek
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      abel
    have hkey : y - iterate Fn F' x₀ (k + 1)
        = -(ek.symm (Fn y - Fn (iterate Fn F' x₀ k)
            - F' (iterate Fn F' x₀ k) (y - iterate Fn F' x₀ k))) := by
      rw [hstepeq, map_sub, map_sub, hinv, hy, map_zero]
      abel
    have hnorm : ‖y - iterate Fn F' x₀ (k + 1)‖
        ≤ ‖(ek.symm : F →L[𝕜] E)‖ * (L / 2 * ‖y - iterate Fn F' x₀ k‖ ^ 2) := by
      rw [hkey, norm_neg]
      exact (ContinuousLinearMap.le_opNorm (ek.symm : F →L[𝕜] E) _).trans
        (mul_le_mul_of_nonneg_left htay (norm_nonneg _))
    have hY : ‖y - iterate Fn F' x₀ (k + 1)‖
        ≤ β / majorant u k * (L / 2 * ‖y - iterate Fn F' x₀ k‖ ^ 2) :=
      hnorm.trans (mul_le_mul_of_nonneg_right hekn
        (mul_nonneg (by linarith) (sq_nonneg _)))
    have hstep2 : β * L * ‖y - iterate Fn F' x₀ (k + 1)‖
        ≤ (β * L * ‖y - iterate Fn F' x₀ k‖) ^ 2 / (2 * majorant u k) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * majorant u k)]
      have h := mul_le_mul_of_nonneg_left hY hA.le
      have h2 := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 2 * majorant u k)
      refine h2.trans (le_of_eq ?_)
      field_simp
    have hX : (0 : ℝ) ≤ β * L * ‖y - iterate Fn F' x₀ k‖ := mul_nonneg hA.le (norm_nonneg _)
    have hsq : (β * L * ‖y - iterate Fn F' x₀ k‖) ^ 2
        ≤ (c ^ 2 ^ k * (u + majorant u k)) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self hX ih
    calc β * L * ‖y - iterate Fn F' x₀ (k + 1)‖
        ≤ (β * L * ‖y - iterate Fn F' x₀ k‖) ^ 2 / (2 * majorant u k) := hstep2
      _ ≤ (c ^ 2 ^ k * (u + majorant u k)) ^ 2 / (2 * majorant u k) := by gcongr
      _ = (c ^ 2 ^ k) ^ 2 * ((u + majorant u k) ^ 2 / (2 * majorant u k)) := by ring
      _ = c ^ 2 ^ (k + 1) * (u + majorant u (k + 1)) := by
          rw [majorant_add_sq_div, ← pow_mul, ← pow_succ]

/-- Under the Kantorovich hypotheses, with $2 \beta L \eta = 1 - u^2$, let $y \in \bar B(x_0, r)$ be
a zero of $F$ with $\beta L \|y - x_0\| \le c (1 + u)$, where $0 \le c \le 1$ and either $c < 1$
or $u = 0$. Then the Newton iterates converge to $y$. -/
private theorem tendsto_iterate_of_eq_zero {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E}
    {r β η L u c : ℝ} (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) {y : E} (hy : Fn y = 0) (hyr : y ∈ Metric.closedBall x₀ r)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcu : c < 1 ∨ u = 0)
    (hy0 : β * L * ‖y - x₀‖ ≤ c * (u + 1)) :
    Tendsto (iterate Fn F' x₀) atTop (𝓝 y) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hbound := norm_sub_iterate_le_of_eq_zero hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr hy hyr
    hy0
  have hnn : ∀ k, (0 : ℝ) ≤ c ^ 2 ^ k * (u + majorant u k) / (β * L) := fun k =>
    div_nonneg (mul_nonneg (pow_nonneg hc0 _) (by linarith [majorant_pos u k])) hA.le
  have hlim : Tendsto (fun k => c ^ 2 ^ k * (u + majorant u k) / (β * L)) atTop (𝓝 0) := by
    rcases hcu with hc | hu
    · have hg : Tendsto (fun k : ℕ => 2 / (β * L) * c ^ k) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).const_mul (2 / (β * L))
      refine squeeze_zero hnn (fun k => ?_) hg
      have hck : c ^ 2 ^ k ≤ c ^ k :=
        pow_le_pow_of_le_one hc0 hc1 (Nat.le_of_lt Nat.lt_two_pow_self)
      have hsk : u + majorant u k ≤ 2 := by linarith [majorant_le_one hu0 hu1 k]
      rw [div_le_iff₀ hA]
      calc c ^ 2 ^ k * (u + majorant u k) ≤ c ^ k * 2 :=
            mul_le_mul hck hsk (by linarith [majorant_pos u k]) (pow_nonneg hc0 _)
        _ = 2 / (β * L) * c ^ k * (β * L) := by field_simp
    · subst hu
      have hg : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k / (β * L)) atTop (𝓝 0) := by
        have h : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        simpa using h.div_const (β * L)
      refine squeeze_zero hnn (fun k => ?_) hg
      have hsk : majorant (0 : ℝ) k ≤ (1 / 2 : ℝ) ^ k := by
        have h := majorant_sub_le_pow (le_refl (0 : ℝ)) zero_le_one k
        simpa [div_pow] using h
      have hck : c ^ 2 ^ k ≤ 1 := pow_le_one₀ hc0 hc1
      gcongr
      calc c ^ 2 ^ k * (0 + majorant (0 : ℝ) k) ≤ 1 * majorant (0 : ℝ) k := by
            rw [zero_add]
            gcongr
            exact (majorant_pos _ _).le
        _ = majorant (0 : ℝ) k := one_mul _
        _ ≤ (1 / 2 : ℝ) ^ k := hsk
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim)
  rw [norm_sub_rev, le_div_iff₀ hA]
  nlinarith [hbound k]

/-- **Uniqueness in the Newton–Kantorovich theorem.** Under the hypotheses of `Newton.kantorovich`
(with $E$ a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $\beta, L > 0$,
$\eta \ge 0$, $\|F'(x_0)^{-1}\| \le \beta$, $\|F'(x_0)^{-1} F(x_0)\| \le \eta$, $F'$ the
derivative of $F$ and $L$-Lipschitz on $\bar B(x_0, r)$, $h = \beta L \eta \le 1/2$ and
$(1 - \sqrt{1 - 2h})/(\beta L) \le r$), suppose that the Newton iterates converge to $x^*$. Let
$y \in \bar B(x_0, r)$ with $F(y) = 0$ and
$$\|y - x_0\| < t^{**} = \frac{1 + \sqrt{1 - 2h}}{\beta L}.$$
Then $y = x^*$.

This is the uniqueness part of Theorem 5.4.2 of [han2009theoretical]; see also §12.6 of
[ortega2000iterative]. The ball cannot be closed when $h < 1/2$: the scalar majorant polynomial
$p(t) = (L/2) t^2 - t/\beta + \eta/\beta$ satisfies all hypotheses at $x_0 = 0$ and has a second
zero at distance exactly $t^{**}$. For the closed ball of radius $t^*$, which includes the
critical case $h = 1/2$ where $t^* = t^{**}$, see `Newton.kantorovich_unique_closedBall`. -/
theorem kantorovich_unique {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r)
    {xstar : E} (hxstar : Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar))
    {y : E} (hy : Fn y = 0) (hyr : y ∈ Metric.closedBall x₀ r)
    (hyt : ‖y - x₀‖ < (1 + Real.sqrt (1 - 2 * (β * L * η))) / (β * L)) :
    y = xstar := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hh0 : (0 : ℝ) ≤ β * L * η := mul_nonneg hA.le hη
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (1 - 2 * (β * L * η)) ≤ 1 := by nlinarith
  set u := Real.sqrt (1 - 2 * (β * L * η)) with hudef
  have hupos : (0 : ℝ) < u + 1 := by linarith
  have hlt : β * L * ‖y - x₀‖ < 1 + u := by
    rw [lt_div_iff₀ hA] at hyt
    nlinarith
  refine tendsto_nhds_unique (tendsto_iterate_of_eq_zero hβ hL e he hβ' hη' hF hLip hu0 hu1
    (by linarith) hr hy hyr (c := β * L * ‖y - x₀‖ / (u + 1)) ?_ ?_ (Or.inl ?_) ?_) hxstar
  · exact div_nonneg (mul_nonneg hA.le (norm_nonneg _)) hupos.le
  · rw [div_le_one hupos]; linarith
  · rw [div_lt_one hupos]; linarith
  · rw [div_mul_cancel₀ _ hupos.ne']

/-- **Uniqueness in the closed ball of radius $t^*$.** Under the hypotheses of `Newton.kantorovich`
(with $E$ a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, $\beta, L > 0$,
$\eta \ge 0$, $\|F'(x_0)^{-1}\| \le \beta$, $\|F'(x_0)^{-1} F(x_0)\| \le \eta$, $F'$ the
derivative of $F$ and $L$-Lipschitz on $\bar B(x_0, r)$, $h = \beta L \eta \le 1/2$ and
$t^* = (1 - \sqrt{1 - 2h})/(\beta L) \le r$), suppose that the Newton iterates converge to
$x^*$. If $F(y) = 0$ and $\|y - x_0\| \le t^*$, then $y = x^*$.

The ball $\bar B(x_0, t^*)$ is the ball in which `Newton.kantorovich` puts the zero. This form
holds also in the critical case $h = 1/2$, where $t^* = t^{**}$ and `Newton.kantorovich_unique`
covers only the open ball. It is part of Theorem 5.4.2 of [han2009theoretical]. -/
theorem kantorovich_unique_closedBall {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r)
    {xstar : E} (hxstar : Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar))
    {y : E} (hy : Fn y = 0)
    (hyt : ‖y - x₀‖ ≤ (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)) :
    y = xstar := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hh0 : (0 : ℝ) ≤ β * L * η := mul_nonneg hA.le hη
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (1 - 2 * (β * L * η)) ≤ 1 := by nlinarith
  set u := Real.sqrt (1 - 2 * (β * L * η)) with hudef
  have hupos : (0 : ℝ) < u + 1 := by linarith
  have hyr : y ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hyt.trans hr
  have hle : β * L * ‖y - x₀‖ ≤ 1 - u := by
    rw [le_div_iff₀ hA] at hyt
    nlinarith
  refine tendsto_nhds_unique (tendsto_iterate_of_eq_zero hβ hL e he hβ' hη' hF hLip hu0 hu1
    (by linarith) hr hy hyr (c := (1 - u) / (u + 1)) ?_ ?_ ?_ ?_) hxstar
  · exact div_nonneg (by linarith) hupos.le
  · rw [div_le_one hupos]; linarith
  · rcases eq_or_lt_of_le hu0 with hu | hu
    · exact Or.inr hu.symm
    · exact Or.inl (by rw [div_lt_one hupos]; linarith)
  · rw [div_mul_cancel₀ _ hupos.ne']
    exact hle

/-- **The Newton–Kantorovich theorem localized at the first iterate.** Let $E$ be a Banach space and
$V$ a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, let
$x_0 \in E$, and let $x_1 = N(x_0)$ be the first Newton iterate. Let $\beta > 0$, $L > 0$ and
$\eta \ge 0$, and suppose that $F'(x_0)$ is invertible with $\|F'(x_0)^{-1}\| \le \beta$ and
$\|F'(x_0)^{-1} F(x_0)\| \le \eta$. Let $h = \beta L \eta \le 1/2$ and
$t^* = (1 - \sqrt{1 - 2h})/(\beta L)$. Let $D \subseteq E$ be a convex set with $x_0 \in D$ and
$\bar B(x_1, t^* - \eta) \subseteq D$, suppose that $F$ has derivative $F'(x)$ at every
$x \in D$, and suppose that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for all $x, y \in D$. Then there
is $x^* \in \bar B(x_1, t^* - \eta)$ with $F(x^*) = 0$, and the Newton iterates from $x_0$
converge to $x^*$.

This is the sharper form of Theorem 5.4.2 of [han2009theoretical]. The hypotheses are needed
only on $D$, and the ball $\bar B(x_0, t^*)$ that `Newton.kantorovich` asks for is in general
strictly larger than $\bar B(x_1, t^* - \eta)$. The proof restarts the majorant sequence one
step later and applies `Newton.kantorovich` at $x_1$. There $\|F'(x_1)^{-1}\| \le \beta / s_1$
with $s_1 = (1 + u^2)/2$ and $u = \sqrt{1 - 2h}$; the restarted problem has Kantorovich number
$((1 - u^2)/(1 + u^2))^2 / 2 \le 1/2$, and its $t^*$ is exactly
$t^* - \eta = (1 - u)^2 / (2 \beta L)$. -/
theorem kantorovich_of_closedBall_step {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {D : Set E}
    {β η L : ℝ} (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' x₀) (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β)
    (hη' : ‖e.symm (Fn x₀)‖ ≤ η) (hD : Convex ℝ D) (hx₀ : x₀ ∈ D)
    (hsub : Metric.closedBall (step Fn F' x₀)
      ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) - η) ⊆ D)
    (hF : ∀ x ∈ D, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ D, ∀ y ∈ D, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) :
    ∃ xstar ∈ Metric.closedBall (step Fn F' x₀)
        ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) - η),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hh0 : (0 : ℝ) ≤ β * L * η := mul_nonneg hA.le hη
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  set u := Real.sqrt (1 - 2 * (β * L * η)) with hudef
  clear_value u
  have hu2pos : (0 : ℝ) < 1 + u ^ 2 := by positivity
  set x₁ := step Fn F' x₀ with hx1def
  have hρ : (1 - u) / (β * L) - η = (1 - u) ^ 2 / (2 * (β * L)) := by
    field_simp
    nlinarith
  have hρ0 : (0 : ℝ) ≤ (1 - u) / (β * L) - η := by
    rw [hρ]; exact div_nonneg (sq_nonneg _) (by linarith)
  have hx1D : x₁ ∈ D := hsub (Metric.mem_closedBall_self hρ0)
  have hx1 : ‖x₁ - x₀‖ ≤ η := by
    rw [hx1def, step_sub_self e he, norm_neg]; exact hη'
  -- the derivative at `x₁` is invertible, with the majorant bound `β / s₁`
  set s₁ : ℝ := (1 + u ^ 2) / 2 with hs1def
  clear_value s₁
  have hs1pos : (0 : ℝ) < s₁ := by rw [hs1def]; linarith
  have hlipx1 : ‖F' x₁ - F' x₀‖ ≤ L * η :=
    (hLip x₁ hx1D x₀ hx₀).trans (mul_le_mul_of_nonneg_left hx1 hL.le)
  have hsmall : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x₁ - F' x₀‖ < 1 := by
    have h1 : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x₁ - F' x₀‖ ≤ β * (L * η) :=
      mul_le_mul hβ' hlipx1 (norm_nonneg _) hβ.le
    nlinarith
  obtain ⟨e₁, he₁, he₁n, -⟩ := e.exists_symm_norm_le_of_add (F' x₁ - F' x₀) hsmall
  have he₁' : (e₁ : E →L[𝕜] F) = F' x₁ := by rw [he₁, he]; abel
  have hβ₁' : ‖(e₁.symm : F →L[𝕜] E)‖ ≤ β / s₁ := by
    refine he₁n.trans ?_
    have hden : (0 : ℝ) < 1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x₁ - F' x₀‖ := by linarith
    have hbnd : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x₁ - F' x₀‖ ≤ 1 - s₁ := by
      have h1 : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x₁ - F' x₀‖ ≤ β * (L * η) :=
        mul_le_mul hβ' hlipx1 (norm_nonneg _) hβ.le
      rw [hs1def]
      nlinarith
    rw [div_le_div_iff₀ hden hs1pos]
    nlinarith [norm_nonneg (e.symm : F →L[𝕜] E)]
  -- the residual at `x₁` is second order
  have htay : ‖Fn x₁ - Fn x₀ - F' x₀ (x₁ - x₀)‖ ≤ L / 2 * ‖x₁ - x₀‖ ^ 2 :=
    Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hD hF hx₀ hx1D
      fun w hw => hLip w hw x₀ hx₀
  have hFx1 : ‖Fn x₁‖ ≤ L / 2 * η ^ 2 := by
    have happ : F' x₀ (x₁ - x₀) = -Fn x₀ := by
      rw [hx1def, step_sub_self e he, map_neg, ← he]
      simp
    rw [happ, show Fn x₁ - Fn x₀ - -Fn x₀ = Fn x₁ from by abel] at htay
    refine htay.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    nlinarith [norm_nonneg (x₁ - x₀)]
  set β₁ : ℝ := β / s₁ with hβ₁def
  set η₁ : ℝ := β₁ * (L / 2 * η ^ 2) with hη₁def
  have hβ₁pos : (0 : ℝ) < β₁ := div_pos hβ hs1pos
  have hη₁0 : (0 : ℝ) ≤ η₁ :=
    mul_nonneg hβ₁pos.le (mul_nonneg (by linarith) (sq_nonneg _))
  have hη₁ : ‖e₁.symm (Fn x₁)‖ ≤ η₁ :=
    (ContinuousLinearMap.le_opNorm (e₁.symm : F →L[𝕜] E) _).trans
      (mul_le_mul hβ₁' hFx1 (norm_nonneg _) hβ₁pos.le)
  -- the Kantorovich data of the restarted problem
  have hβ₁Lη : β₁ * L * η = (1 - u ^ 2) / (1 + u ^ 2) := by
    rw [hβ₁def, hs1def]
    field_simp
    linarith
  have hβ₁Lη₁ : β₁ * L * η₁ = (β₁ * L * η) ^ 2 / 2 := by rw [hη₁def]; ring
  clear_value η₁ β₁
  have hqle : β₁ * L * η ≤ 1 := by
    rw [hβ₁Lη, div_le_one hu2pos]
    linarith [sq_nonneg u]
  have hq0 : (0 : ℝ) ≤ β₁ * L * η := by
    rw [hβ₁Lη]
    exact div_nonneg (by linarith) hu2pos.le
  have hh₁ : β₁ * L * η₁ ≤ 1 / 2 := by
    rw [hβ₁Lη₁]
    have hsq : (β₁ * L * η) ^ 2 ≤ 1 := by
      rw [sq]
      calc (β₁ * L * η) * (β₁ * L * η) ≤ 1 * 1 := mul_le_mul hqle hqle hq0 zero_le_one
        _ = 1 := one_mul 1
    linarith
  have hsqrt : Real.sqrt (1 - 2 * (β₁ * L * η₁)) = 2 * u / (1 + u ^ 2) := by
    have h1 : 1 - 2 * (β₁ * L * η₁) = (2 * u / (1 + u ^ 2)) ^ 2 := by
      rw [hβ₁Lη₁, hβ₁Lη]
      field_simp
      ring
    rw [h1, Real.sqrt_sq (div_nonneg (by linarith) hu2pos.le)]
  have hrad₁ : (1 - Real.sqrt (1 - 2 * (β₁ * L * η₁))) / (β₁ * L)
      = (1 - u) / (β * L) - η := by
    rw [hsqrt, hρ, hβ₁def, hs1def]
    field_simp
    ring
  obtain ⟨xstar, hxmem, hroot, htend, -, -⟩ :=
    kantorovich (Fn := Fn) (F' := F') (x₀ := x₁) (r := (1 - u) / (β * L) - η)
      hβ₁pos hL hη₁0 e₁ he₁' hβ₁' hη₁
      (fun x hx => hF x (hsub hx)) (fun x hx y hy => hLip x (hsub hx) y (hsub hy)) hh₁
      (le_of_eq hrad₁)
  rw [hrad₁] at hxmem
  refine ⟨xstar, hxmem, hroot, ?_⟩
  have hshift : ∀ k, iterate Fn F' x₁ k = iterate Fn F' x₀ (k + 1) := fun k => by
    rw [iterate, iterate, hx1def, Function.iterate_succ_apply]
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (htend.congr hshift)

end Kantorovich

section Chord

/-!
### The chord method

If the derivative is frozen at a fixed invertible $A$, then the Newton map becomes
$x \mapsto x - A^{-1} F(x)$, whose derivative at a zero $x^*$ is $I - A^{-1} F'(x^*)$. The
convergence is therefore linear with the factor $\|I - A^{-1} F'(x^*)\|$, provided that this factor
is less than $1$, which says that $A$ approximates $F'(x^*)$ well enough. For $A = F'(x_0)$ with
$x_0$ close to $x^*$ this holds by continuity of $F'$.
-/

variable [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]

/-- **One chord step measured from a zero.** Let $E$ and $V$ be normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, let $x^* \in E$ with
$F(x^*) = 0$, and let $A \colon E \to V$ be an invertible continuous linear map. Let
$r, L \in \mathbb{R}$, suppose that $F$ has derivative $F'(x)$ at every $x \in \bar B(x^*, r)$,
and suppose that $\|F'(x) - F'(x^*)\| \le L \|x - x^*\|$ for all $x \in \bar B(x^*, r)$. Then
for every $x \in \bar B(x^*, r)$
$$\|x - A^{-1} F(x) - x^*\| \le \|I - A^{-1} F'(x^*)\| \, \|x - x^*\| + \|A^{-1}\|
  \frac{\max\{L, 0\}}{2} \|x - x^*\|^2.$$

The defect $I - A^{-1} F'(x^*)$ of the frozen derivative acts linearly on the error, and the
rest is the second-order Taylor remainder. This is the estimate behind Exercise 5.4.5 of
[han2009theoretical]. -/
theorem norm_chordStep_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} {r L : ℝ}
    (hstar : Fn xstar = 0) (A : E ≃L[𝕜] F)
    (hF : ∀ x ∈ Metric.closedBall xstar r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall xstar r, ‖F' x - F' xstar‖ ≤ L * ‖x - xstar‖)
    {x : E} (hx : x ∈ Metric.closedBall xstar r) :
    ‖chordStep Fn A x - xstar‖
      ≤ ‖(1 : E →L[𝕜] E) - (A.symm : F →L[𝕜] E) ∘L F' xstar‖ * ‖x - xstar‖
        + ‖(A.symm : F →L[𝕜] E)‖ * (max L 0 / 2) * ‖x - xstar‖ ^ 2 := by
  have hr : 0 ≤ r := le_trans dist_nonneg (Metric.mem_closedBall.mp hx)
  have hxs : xstar ∈ Metric.closedBall xstar r := Metric.mem_closedBall_self hr
  have htay : ‖Fn x - Fn xstar - F' xstar (x - xstar)‖ ≤ max L 0 / 2 * ‖x - xstar‖ ^ 2 :=
    Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_closedBall xstar r) hF hxs hx
      fun z hz => (hLip z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hkey : chordStep Fn A x - xstar
      = ((1 : E →L[𝕜] E) - (A.symm : F →L[𝕜] E) ∘L F' xstar) (x - xstar)
        - A.symm (Fn x - Fn xstar - F' xstar (x - xstar)) := by
    have h1 : ((1 : E →L[𝕜] E) - (A.symm : F →L[𝕜] E) ∘L F' xstar) (x - xstar)
        = (x - xstar) - A.symm (F' xstar (x - xstar)) := by
      simp [ContinuousLinearEquiv.coe_coe]
    have h2 : A.symm (Fn x - Fn xstar - F' xstar (x - xstar))
        = A.symm (Fn x) - A.symm (F' xstar (x - xstar)) := by
      rw [hstar, sub_zero, map_sub]
    rw [chordStep, h1, h2]
    abel
  rw [hkey]
  refine (norm_sub_le _ _).trans
    (add_le_add (ContinuousLinearMap.le_opNorm _ (x - xstar)) ?_)
  calc ‖A.symm (Fn x - Fn xstar - F' xstar (x - xstar))‖
      ≤ ‖(A.symm : F →L[𝕜] E)‖ * ‖Fn x - Fn xstar - F' xstar (x - xstar)‖ :=
        ContinuousLinearMap.le_opNorm (A.symm : F →L[𝕜] E) _
    _ ≤ ‖(A.symm : F →L[𝕜] E)‖ * (max L 0 / 2 * ‖x - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htay (norm_nonneg _)
    _ = ‖(A.symm : F →L[𝕜] E)‖ * (max L 0 / 2) * ‖x - xstar‖ ^ 2 := by ring

/-- **Linear convergence of the chord method.** Let $E$ and $V$ be normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $F \colon E \to V$, let $x^* \in E$ with
$F(x^*) = 0$, and let $A \colon E \to V$ be an invertible continuous linear map with
$\|I - A^{-1} F'(x^*)\| < 1$. Let $r > 0$ and $L \in \mathbb{R}$, suppose that $F$ has
derivative $F'(x)$ at every $x \in \bar B(x^*, r)$, and suppose that
$\|F'(x) - F'(x^*)\| \le L \|x - x^*\|$ for all $x \in \bar B(x^*, r)$. Then there are
$\delta > 0$ and $q$ with $0 \le q < 1$ such that for every $x_0 \in \bar B(x^*, \delta)$ the
chord iterates satisfy $\|x_k - x^*\| \le q^k \|x_0 - x^*\|$ for every $k$, and converge to
$x^*$.

This is Exercise 5.4.5 of [han2009theoretical] and Theorem 6.21 of [kress1998numerical]. The
rate cannot be improved to quadratic: the error operator $I - A^{-1} F'(x^*)$ is a fixed
operator, and when it is nonzero the leading term of the error is linear. Newton's method is the
case in which this operator vanishes at the zero, and `Newton.exists_ball_norm_step_sub_le` is
the corresponding quadratic bound. No completeness is needed, since the limit $x^*$ is a
hypothesis and not a conclusion. -/
theorem tendsto_chordIterate {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} {r L : ℝ}
    (hstar : Fn xstar = 0) (hr : 0 < r) (A : E ≃L[𝕜] F)
    (hF : ∀ x ∈ Metric.closedBall xstar r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall xstar r, ‖F' x - F' xstar‖ ≤ L * ‖x - xstar‖)
    (hA : ‖(1 : E →L[𝕜] E) - (A.symm : F →L[𝕜] E) ∘L F' xstar‖ < 1) :
    ∃ δ > 0, ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x₀ ∈ Metric.closedBall xstar δ,
      (∀ k, ‖chordIterate Fn A x₀ k - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖) ∧
        Tendsto (chordIterate Fn A x₀) atTop (𝓝 xstar) := by
  set q₀ := ‖(1 : E →L[𝕜] E) - (A.symm : F →L[𝕜] E) ∘L F' xstar‖ with hq₀def
  set K := ‖(A.symm : F →L[𝕜] E)‖ * (max L 0 / 2) with hKdef
  have hq00 : 0 ≤ q₀ := norm_nonneg _
  have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) (div_nonneg (le_max_right _ _) (by norm_num))
  set δ := min r ((1 - q₀) / (2 * (K + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min hr (div_pos (by linarith) (by linarith))
  set q := (1 + q₀) / 2 with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef]; linarith
  have hstepbd : ∀ x ∈ Metric.closedBall xstar δ,
      ‖chordStep Fn A x - xstar‖ ≤ q * ‖x - xstar‖ := by
    intro x hx
    have hxr : x ∈ Metric.closedBall xstar r :=
      Metric.closedBall_subset_closedBall (min_le_left _ _) hx
    have h := norm_chordStep_sub_le hstar A hF hLip hxr
    have hd : ‖x - xstar‖ ≤ (1 - q₀) / (2 * (K + 1)) := by
      rw [← dist_eq_norm]
      exact (Metric.mem_closedBall.mp hx).trans (min_le_right _ _)
    have hKx : K * ‖x - xstar‖ ≤ (1 - q₀) / 2 := by
      have h1 : K * ‖x - xstar‖ ≤ K * ((1 - q₀) / (2 * (K + 1))) := by gcongr
      have h2 : K * ((1 - q₀) / (2 * (K + 1))) ≤ (1 - q₀) / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      linarith
    have hXn : (0 : ℝ) ≤ ‖x - xstar‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hKx hXn]
  have hmaps : ∀ x ∈ Metric.closedBall xstar δ, chordStep Fn A x ∈ Metric.closedBall xstar δ := by
    intro x hx
    have h := hstepbd x hx
    have hd : ‖x - xstar‖ ≤ δ := by rw [← dist_eq_norm]; exact hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    nlinarith [norm_nonneg (x - xstar)]
  refine ⟨δ, hδ0, q, hq0, hq1, fun x₀ hx₀ => ?_⟩
  have hind : ∀ k, chordIterate Fn A x₀ k ∈ Metric.closedBall xstar δ ∧
      ‖chordIterate Fn A x₀ k - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖ := by
    intro k
    induction k with
    | zero => exact ⟨hx₀, by simp [chordIterate]⟩
    | succ k ih =>
      refine ⟨by rw [chordIterate_succ]; exact hmaps _ ih.1, ?_⟩
      rw [chordIterate_succ]
      calc ‖chordStep Fn A (chordIterate Fn A x₀ k) - xstar‖
          ≤ q * ‖chordIterate Fn A x₀ k - xstar‖ := hstepbd _ ih.1
        _ ≤ q * (q ^ k * ‖x₀ - xstar‖) := mul_le_mul_of_nonneg_left ih.2 hq0
        _ = q ^ (k + 1) * ‖x₀ - xstar‖ := by ring
  refine ⟨fun k => (hind k).2, ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) (fun k => (hind k).2) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖x₀ - xstar‖

end Chord

end Newton
