/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Nonlinear.Nemytskii
import Numlib.Nonlinear.Newton
import NumlibSurface.AtkinsonHan.Chapter05.Section03

/-!
# Atkinson and Han, Section 5.4: Newton's Method

This module formalizes Section 5.4 of [han2009theoretical]: Newton's method for an equation
$F(u) = 0$ between Banach spaces, its local quadratic convergence, the Newton–Kantorovich theorem,
the modified Newton (chord) method, and in Section 5.4.2 the applications to a nonlinear system in
$\mathbb{R}^d$, to a nonlinear integral equation and to a two-point boundary value problem. Newton's
method is the iteration (5.4.2),
$$u_{n+1} = u_n - [F'(u_n)]^{-1} F(u_n),$$
and the modified method replaces $F'(u_n)$ by one fixed invertible operator. The proofs specialize
the backbone module `Numlib.Nonlinear.Newton`, with the Taylor estimate of Section 5.3, the
derivative of the Urysohn operator from `Numlib.IntegralEquations.Basic`, and the Nemytskii operator
of `Numlib.Nonlinear.Nemytskii`.

## Main results

* Equation (5.4.2), `AtkinsonHan.Chapter05.equation_5_4_2`: the Newton iterates satisfy
  $u_{n+1} = T(u_n)$, with $T$ the Newton step.
* Equation (5.4.5), `AtkinsonHan.Chapter05.equation_5_4_5`: one Newton step squares the error, up to
  the factor $c_0 L / 2$.
* Theorem 5.4.1, `AtkinsonHan.Chapter05.theorem_5_4_1`: local quadratic convergence of Newton's
  method, with the estimates (5.4.3) and (5.4.4).
* Theorem 5.4.2, `AtkinsonHan.Chapter05.theorem_5_4_2`: the Newton–Kantorovich theorem, existence of
  a root and convergence of the iterates from hypotheses at the starting point.
* Theorem 5.4.2, `AtkinsonHan.Chapter05.theorem_5_4_2_step`: the root lies in the ball
  $\bar B(u_1, t^* - b)$ around the first iterate.
* Theorem 5.4.2, `AtkinsonHan.Chapter05.theorem_5_4_2_unique`: the root is unique within the
  distance $t^{**}$ of $u_0$.
* Theorem 5.4.2, `AtkinsonHan.Chapter05.theorem_5_4_2_sharp`: the a priori error bound
  $[1 - \sqrt{1 - 2h}]^{2^n} / (2^n a L)$.
* Equation (5.4.7), `AtkinsonHan.Chapter05.equation_5_4_7`: Newton's method for a nonlinear system
  in $\mathbb{R}^d$ solves a linear system at each step.
* Equation (5.4.8), `AtkinsonHan.Chapter05.equation_5_4_8`: the derivative of $F = I - \mathcal{K}$
  for the Urysohn operator $\mathcal{K}$.
* Equations (5.4.9)–(5.4.10), `AtkinsonHan.Chapter05.equation_5_4_10`: a Newton step for the
  nonlinear integral equation solves a linear integral equation of the second kind.
* Equation (5.4.11), `AtkinsonHan.Chapter05.equation_5_4_11`: the modified Newton method with a
  fixed operator.
* Equations (5.4.11)–(5.4.12), `AtkinsonHan.Chapter05.equation_5_4_12`: the modified Newton method
  for the integral equation uses one kernel at every step.
* Exercise 5.4.5, `AtkinsonHan.Chapter05.exercise_5_4_5`: the modified Newton method converges
  linearly.
* Section 5.4.2, `AtkinsonHan.Chapter05.example_5_4_bvp`: the derivative of the operator of the
  two-point boundary value problem $u'' = f(t, u)$, $u(0) = u(1) = 0$.

## Conventions

* The space $C^2_0[0, 1]$ of Section 5.4.2 is `ContDiffMapIcc.zeroBoundary (zero_le_one : (0 : ℝ)
  ≤ 1) 2` from `Numlib.Analysis.Calculus.ContDiffMapIcc`: the closed subspace of $C^2[0, 1]$ of the
  functions that vanish at both endpoints. The norm on $C^k[a, b]$ is
  $\sum_{j \le k} \|u^{(j)}\|_\infty$, which is the norm (2.1.2) of the book for $k = 1$.

## Implementation notes

* The Newton iteration is the backbone's `Newton.step` and `Newton.iterate`, and the modified method
  is `Newton.chordStep` and `Newton.chordIterate`. `Newton.step` uses Mathlib's
  `ContinuousLinearMap.inverse`, which is $0$ at an operator that is not invertible. Each theorem
  that uses the step at a point assumes that $F'$ is invertible there, as an equivalence
  `e : U ≃L[ℝ] W` with `↑e = F' u`.
* `AtkinsonHan.Chapter05.newtonStep_eq_self` (a root is a fixed point of the step),
  `AtkinsonHan.Chapter05.newtonStep_sub_eq` (the increment form $F'(u_n) \delta_n = -F(u_n)$) and
  `AtkinsonHan.Chapter05.exists_equiv_of_norm_lt` (the perturbation criterion of Theorem 2.3.5 that
  keeps $F'(u_n)$ invertible) support the numbered results.

## Deviations from the source

* **Equations (5.4.2) and (5.4.5)** (scope). The iteration uses a totalized inverse and the
  separate quadratic estimate supplies the current inverse and its bound. The estimate
  applies in normed spaces.
* **Theorem 5.4.2, convergence and error estimates** (scope). The main convergence theorem
  and the separate sharp error estimate use controls on a closed ball around $u_0$.
  The separate first-step version uses the ball around $u_1$ from the source, with an
  ambient derivative on a convex domain.
* **Theorem 5.4.2, uniqueness** (correction). The book states uniqueness of the root on the closed
  ball of radius $t^{**} = (1 + \sqrt{1 - 2h})/(aL)$ about $u_0$. This is false for $h < 1/2$; the
  statement uses the open ball. See `AtkinsonHan.Chapter05.theorem_5_4_2_unique`.
* **Equations (5.4.8), (5.4.10) and (5.4.12)** (correction and scope). The derivative
  of $F(u) = u - \mathcal{K}(u)$ has a minus sign before the integral. The two linear
  correction equations use $-F(u_n)$, so their right-hand-side integrals drop the printed
  extra factor $u_n(s)$. These results allow any nonempty closed interval $[a,b]$.
* **Exercise 5.4.5** (scope). The fixed invertible operator can satisfy the stated
  contraction condition even if it differs from the initial derivative.
-/

open Filter Metric Topology

namespace AtkinsonHan.Chapter05

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Equation (5.4.2)** of [han2009theoretical]. The Newton iterates satisfy
$$u_{n+1} = u_n - [F'(u_n)]^{-1} F(u_n).$$

The iterates are `Newton.iterate F F' u₀`, and the step is `Newton.step`. Where $F'(u_n)$ is not
invertible, the inverse is $0$ and the step leaves $u_n$ unchanged.

**Reading.** Uses a totalized operator inverse to define every step.
-/
theorem equation_5_4_2 (F : U → W) (F' : U → U →L[ℝ] W) (u₀ : U) (n : ℕ) :
    Newton.iterate F F' u₀ (n + 1) = Newton.step F F' (Newton.iterate F F' u₀ n) :=
  Newton.iterate_succ F F' u₀ n

/-- A root of $F$ is a fixed point of the Newton step: if $F(u) = 0$, then
$u - [F'(u)]^{-1} F(u) = u$.

**Reading.** A root is fixed even for a noninvertible supplied derivative under totalization.
-/
theorem newtonStep_eq_self {F : U → W} (F' : U → U →L[ℝ] W) {u : U} (hu : F u = 0) :
    Newton.step F F' u = u :=
  Newton.step_eq_self_of_eq_zero F F' hu

/-- The increment form of the Newton step. If $F'(u)$ is invertible and
$u_+ = u - [F'(u)]^{-1} F(u)$ is the Newton step from $u$, then
$$F'(u)(u_+ - u) = -F(u).$$
This is the form in which (5.4.7) and (5.4.9) write the iteration. -/
theorem newtonStep_sub_eq {F : U → W} {F' : U → U →L[ℝ] W} {u : U} (e : U ≃L[ℝ] W)
    (he : (e : U →L[ℝ] W) = F' u) : F' u (Newton.step F F' u - u) = -F u := by
  have hinv : (F' u).inverse = (e.symm : W →L[ℝ] U) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hstep : Newton.step F F' u - u = -((e.symm : W →L[ℝ] U) (F u)) := by
    rw [Newton.step, hinv]
    abel
  rw [hstep, map_neg, ← he]
  simp

section Complete

variable [CompleteSpace U] [CompleteSpace W]

omit [CompleteSpace W] in
/-- The perturbation criterion that keeps the Newton step well defined. Let $U$ be a Banach space,
let $e : U \to W$ be an invertible bounded linear operator, and let $A \in \mathcal{L}(U, W)$
with
$$\|e^{-1}\| \, \|A - e\| < 1.$$
Then $A$ is invertible.

This specializes `ContinuousLinearEquiv.exists_symm_norm_le_of_add`, which is Theorem 2.3.5 of
the book. -/
theorem exists_equiv_of_norm_lt {A : U →L[ℝ] W} (e : U ≃L[ℝ] W)
    (h : ‖(e.symm : W →L[ℝ] U)‖ * ‖A - (e : U →L[ℝ] W)‖ < 1) :
    ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = A := by
  obtain ⟨e', he', -, -⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add e (A - (e : U →L[ℝ] W)) h
  exact ⟨e', by rw [he']; abel⟩

omit [CompleteSpace U] [CompleteSpace W] in
/-- **Equation (5.4.5)** of [han2009theoretical]. Let $F : U \to W$ with $F(u^*) = 0$. Assume that
$F$ has the Fréchet derivative $F'(z)$ at every $z$ in the ball $B(u^*, r)$, and that
$\|F'(z) - F'(w)\| \le L \|z - w\|$ for all $z, w \in B(u^*, r)$. Let $u \in B(u^*, r)$, let
$F'(u)$ be invertible, and let $\|[F'(u)]^{-1}\| \le c_0$. Then the Newton step
$T(u) = u - [F'(u)]^{-1} F(u)$ satisfies
$$\|T(u) - u^*\| \le \frac{c_0 L}{2} \|u - u^*\|^2.$$

The spaces need not be complete. The proof is the Taylor estimate
`AtkinsonHan.Chapter05.norm_sub_sub_fderiv_le_half_mul_sq` of Section 5.3.

**Reading.** Uses explicit pointwise inverse bound and does not need completeness.
-/
theorem equation_5_4_5 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    {r L c₀ : ℝ}
    (hF : ∀ z ∈ ball ustar r, HasFDerivAt F (F' z) z)
    (hL : ∀ z ∈ ball ustar r, ∀ w ∈ ball ustar r, ‖F' z - F' w‖ ≤ L * ‖z - w‖) {u : U}
    (hu : u ∈ ball ustar r) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u)
    (hc₀ : ‖(e.symm : W →L[ℝ] U)‖ ≤ c₀) :
    ‖Newton.step F F' u - ustar‖ ≤ c₀ * L / 2 * ‖u - ustar‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp hu)
  have hstarmem : ustar ∈ ball ustar r := mem_ball_self hr
  have hinv : (F' u).inverse = (e.symm : W →L[ℝ] U) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hsymm : ∀ z : U, (e.symm : W →L[ℝ] U) (F' u z) = z := by
    intro z
    rw [← he]
    simp
  have htay := norm_sub_sub_fderiv_le_half_mul_sq (convex_ball ustar r) hF hL hu hstarmem
  have hkey : Newton.step F F' u - ustar
      = (e.symm : W →L[ℝ] U) (F ustar - F u - F' u (ustar - u)) := by
    rw [hroot]
    simp only [map_sub, hsymm, Newton.step, hinv, map_zero]
    abel
  have hc₀0 : 0 ≤ c₀ := le_trans (norm_nonneg _) hc₀
  rw [hkey, norm_sub_rev ustar u] at *
  calc ‖(e.symm : W →L[ℝ] U) (F ustar - F u - F' u (ustar - u))‖
      ≤ ‖(e.symm : W →L[ℝ] U)‖ * ‖F ustar - F u - F' u (ustar - u)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ c₀ * (L / 2 * ‖u - ustar‖ ^ 2) :=
        mul_le_mul hc₀ htay (norm_nonneg _) hc₀0
    _ = c₀ * L / 2 * ‖u - ustar‖ ^ 2 := by ring

omit [CompleteSpace W] in
/-- **Theorem 5.4.1** of [han2009theoretical] (local convergence of Newton's method). Let $U$ be a
Banach space and $F : U \to W$ with $F(u^*) = 0$ and $F'(u^*)$ invertible. Let $r > 0$, let $F$
have the Fréchet derivative $F'(u)$ at every $u \in B(u^*, r)$, and let
$\|F'(u) - F'(v)\| \le L \|u - v\|$ for all $u, v \in B(u^*, r)$. Then there are $\delta > 0$
and $M > 0$ with $M \delta < 1$ such that for every $u_0$ with $\|u_0 - u^*\| \le \delta$: every
$F'(u_n)$ is invertible, $u_n \to u^*$, and for all $n$
$$\|u_{n+1} - u^*\| \le M \|u_n - u^*\|^2 \quad (5.4.3), \qquad \|u_n - u^*\| \le \frac{(M
  \delta)^{2^n}}{M} \quad (5.4.4).$$

The conclusion $M > 0$ makes (5.4.4) meaningful. The backbone supplies the quadratic step
estimate `Newton.exists_ball_norm_step_sub_le` and the convergence `Newton.tendsto_iterate`. -/
theorem theorem_5_4_1 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' ustar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ u ∈ ball ustar r, HasFDerivAt F (F' u) u)
    (hL : ∀ u ∈ ball ustar r, ∀ v ∈ ball ustar r, ‖F' u - F' v‖ ≤ L * ‖u - v‖) :
    ∃ δ > 0, ∃ M > 0, M * δ < 1 ∧ ∀ u₀, ‖u₀ - ustar‖ ≤ δ →
      (∀ n, ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = F' (Newton.iterate F F' u₀ n)) ∧
      Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
        ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2) ∧
      (∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤ (M * δ) ^ 2 ^ n / M) := by
  obtain ⟨δ₀, hδ₀, C, hC⟩ := Newton.exists_ball_norm_step_sub_le hroot e he hr hF hL
  obtain ⟨δ₁, hδ₁, htend⟩ := Newton.tendsto_iterate hroot e he hr hF hL
  set K : ℝ := ‖(e.symm : W →L[ℝ] U)‖ with hKdef
  set L' : ℝ := max L 0 with hL'def
  set M : ℝ := max C 1 with hMdef
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hp0 : 0 ≤ K * L' := mul_nonneg hK0 hL'0
  set δ : ℝ := min (min (δ₀ / 2) (δ₁ / 2))
    (min (r / 2) (min (1 / (2 * M)) (1 / (2 * (K * L' + 1))))) with hδdef
  have hδ0 : 0 < δ :=
    lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (lt_min (by positivity) (by positivity)))
  have hδδ₀ : δ ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδ₁ : δ ≤ δ₁ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδr : δ ≤ r / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδM : δ ≤ 1 / (2 * M) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (min_le_left _ _))
  have hδp : δ ≤ 1 / (2 * (K * L' + 1)) := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMδ : M * δ ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hδM hM0.le
    rw [mul_one_div] at h
    calc M * δ ≤ M / (2 * M) := h
      _ = 1 / 2 := by field_simp
  -- one step: quadratic decrease, and the iterate stays within `δ` of the root
  have hstep : ∀ u : U, ‖u - ustar‖ ≤ δ →
      ‖Newton.step F F' u - ustar‖ ≤ M * ‖u - ustar‖ ^ 2 ∧
        ‖Newton.step F F' u - ustar‖ ≤ δ := by
    intro u hu
    have huball : u ∈ ball ustar δ₀ := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have h1 : ‖Newton.step F F' u - ustar‖ ≤ M * ‖u - ustar‖ ^ 2 :=
      (hC u huball).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    refine ⟨h1, h1.trans ?_⟩
    nlinarith [norm_nonneg (u - ustar), hM0]
  have hiter : ∀ u₀, ‖u₀ - ustar‖ ≤ δ → ∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤ δ := by
    intro u₀ hu₀ n
    induction n with
    | zero => simpa [Newton.iterate] using hu₀
    | succ n ih =>
      rw [Newton.iterate_succ]
      exact (hstep _ ih).2
  -- well-definedness of every step, by the perturbation theorem
  have hwell : ∀ u : U, ‖u - ustar‖ ≤ δ → ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = F' u := by
    intro u hu
    have huball : u ∈ ball ustar r := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have h1 : ‖F' u - (e : U →L[ℝ] W)‖ ≤ L' * δ := by
      rw [he]
      calc ‖F' u - F' ustar‖ ≤ L * ‖u - ustar‖ := hL u huball ustar (mem_ball_self hr)
        _ ≤ L' * ‖u - ustar‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ L' * δ := mul_le_mul_of_nonneg_left hu hL'0
    have h2 : K * (L' * δ) < 1 := by
      have h3 : K * L' * δ ≤ K * L' * (1 / (2 * (K * L' + 1))) :=
        mul_le_mul_of_nonneg_left hδp hp0
      have h4 : K * L' * (1 / (2 * (K * L' + 1))) < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
      calc K * (L' * δ) = K * L' * δ := by ring
        _ ≤ K * L' * (1 / (2 * (K * L' + 1))) := h3
        _ < 1 := h4
    refine exists_equiv_of_norm_lt e (lt_of_le_of_lt ?_ h2)
    exact mul_le_mul_of_nonneg_left h1 hK0
  refine ⟨δ, hδ0, M, hM0, by linarith, fun u₀ hu₀ => ⟨fun n => hwell _ (hiter u₀ hu₀ n), ?_,
    fun n => ?_, fun n => ?_⟩⟩
  · refine htend u₀ ?_
    rw [mem_ball, dist_eq_norm]
    linarith
  · rw [Newton.iterate_succ]
    exact (hstep _ (hiter u₀ hu₀ n)).1
  · induction n with
    | zero =>
      have h : (M * δ) ^ 2 ^ 0 / M = δ := by
        rw [pow_zero, pow_one]
        field_simp
      rw [h]
      simpa [Newton.iterate] using hu₀
    | succ n ih =>
      have h1 : ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
          ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 := by
        rw [Newton.iterate_succ]
        exact (hstep _ (hiter u₀ hu₀ n)).1
      have h2 : ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 ≤ ((M * δ) ^ 2 ^ n / M) ^ 2 := by
        have hnn : (0 : ℝ) ≤ ‖Newton.iterate F F' u₀ n - ustar‖ := norm_nonneg _
        nlinarith [ih]
      have h3 : M * ((M * δ) ^ 2 ^ n / M) ^ 2 = (M * δ) ^ 2 ^ (n + 1) / M := by
        rw [pow_succ 2 n, pow_mul]
        field_simp
      calc ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
          ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 := h1
        _ ≤ M * ((M * δ) ^ 2 ^ n / M) ^ 2 := mul_le_mul_of_nonneg_left h2 hM0.le
        _ = (M * δ) ^ 2 ^ (n + 1) / M := h3

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2** of [han2009theoretical] (Newton–Kantorovich theorem). Let $U$ and $W$ be
Banach spaces and $F : U \to W$, let $F'(u_0)$ be invertible, and let $a > 0$, $b \ge 0$ and
$L > 0$ satisfy
$$\|[F'(u_0)]^{-1}\| \le a, \qquad \|[F'(u_0)]^{-1} F(u_0)\| \le b, \qquad h = abL \le
  \tfrac12.$$
Let $t^* = (1 - \sqrt{1 - 2h})/(aL) \le r$, let $F$ have the Fréchet derivative $F'(u)$ at every
$u \in \bar B(u_0, r)$, and let $\|F'(u) - F'(v)\| \le L \|u - v\|$ for all
$u, v \in \bar B(u_0, r)$. Then there is a root $u^*$ of $F$ with $\|u^* - u_0\| \le t^*$, the
Newton iterates $u_n$ lie in $\bar B(u_0, r)$ and converge to $u^*$, and if $h > 0$, then for
all $n$
$$\|u_n - u^*\| \le \frac{(2h)^{2^n} b}{2^n h}.$$

The hypotheses $a > 0$ and $L > 0$ make $t^*$ well defined. The completeness of $W$ is kept
because the book states the theorem for Banach spaces; it follows from the completeness of $U$,
since $F'(u_0)$ is an isomorphism. The proof is the backbone's `Newton.kantorovich`. The finer
clauses of the book are `AtkinsonHan.Chapter05.theorem_5_4_2_step`,
`AtkinsonHan.Chapter05.theorem_5_4_2_unique` and `AtkinsonHan.Chapter05.theorem_5_4_2_sharp`.

**Reading.** Main compact statement uses a ball around the initial point and a coarser bound.
-/
theorem theorem_5_4_2 {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) :
    ∃ ustar ∈ closedBall u₀ ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L)),
      F ustar = 0 ∧ Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, Newton.iterate F F' u₀ n ∈ closedBall u₀ r) ∧
      (0 < a * b * L → ∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤
        (2 * (a * b * L)) ^ 2 ^ n * b / (2 ^ n * (a * b * L))) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich ha hLpos hb e he ha' hb' hF hLip (by rw [hcomm]; exact hh)
    (by rw [hcomm]; exact hr)
  rwa [hcomm] at hkey

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2** of [han2009theoretical], existence near the first iterate. Let $U$ and $W$ be
Banach spaces and $F : U \to W$, let $F'(u_0)$ be invertible, and let $a > 0$, $b \ge 0$ and
$L > 0$ satisfy $\|[F'(u_0)]^{-1}\| \le a$, $\|[F'(u_0)]^{-1} F(u_0)\| \le b$ and
$h = abL \le \frac12$. Let $t^* = (1 - \sqrt{1 - 2h})/(aL)$ and let $u_1$ be the first Newton
iterate. Let $D \subseteq U$ be convex with $u_0 \in D$ and $\bar B(u_1, t^* - b) \subseteq D$,
let $F$ have the Fréchet derivative $F'(u)$ at every $u \in D$, and let
$\|F'(u) - F'(v)\| \le L \|u - v\|$ for all $u, v \in D$. Then there is a root $u^*$ of $F$ in
$\bar B(u_1, t^* - b)$, and the Newton iterates converge to $u^*$.

This is the form in which the theorem is applied when no ball around $u_0$ is known in advance.

**Reading.** The first-step ball and existence agree, using ambient derivatives on a convex domain
without requiring openness.
-/
theorem theorem_5_4_2_step {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {D : Set U} {a b L : ℝ}
    (ha : 0 < a) (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b) (hD : Convex ℝ D)
    (hu₀ : u₀ ∈ D)
    (hsub : closedBall (Newton.step F F' u₀)
      ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) - b) ⊆ D)
    (hF : ∀ u ∈ D, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ D, ∀ v ∈ D, ‖F' u - F' v‖ ≤ L * ‖u - v‖) (hh : a * b * L ≤ 1 / 2) :
    ∃ ustar ∈ closedBall (Newton.step F F' u₀)
        ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) - b),
      F ustar = 0 ∧ Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich_of_closedBall_step ha hLpos hb e he ha' hb' hD hu₀
    (by rw [hcomm]; exact hsub) hF hLip (by rw [hcomm]; exact hh)
  rwa [hcomm] at hkey

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2** of [han2009theoretical], uniqueness. Under the hypotheses of
`AtkinsonHan.Chapter05.theorem_5_4_2`, let the Newton iterates converge to $u^*$. If
$v \in \bar B(u_0, r)$ is a root of $F$ with
$$\|v - u_0\| < t^{**} = \frac{1 + \sqrt{1 - 2h}}{aL},$$
then $v = u^*$.

**Correction.** The book states uniqueness on the closed ball of radius $t^{**}$ about $u_0$.
This is false whenever $h < \frac12$. The scalar majorant $p(t) = \frac{L}{2} t^2 - t/a + b/a$
satisfies every hypothesis at $u_0 = 0$, and it has a second root at the distance exactly
$t^{**}$. The open ball is the correct domain, and the backbone's `Newton.kantorovich_unique`
proves uniqueness there.

The closed ball of radius $t^*$ is also a domain of uniqueness, and that form remains true in
the critical case $h = \frac12$. -/
theorem theorem_5_4_2_unique {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) {ustar : U}
    (hustar : Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar)) {v : U} (hv : F v = 0)
    (hvr : v ∈ closedBall u₀ r)
    (hvt : ‖v - u₀‖ < (1 + Real.sqrt (1 - 2 * (a * b * L))) / (a * L)) :
    v = ustar := by
  have hcomm : a * L * b = a * b * L := by ring
  exact Newton.kantorovich_unique ha hLpos hb e he ha' hb' hF hLip (by rw [hcomm]; exact hh)
    (by rw [hcomm]; exact hr) hustar hv hvr (by rw [hcomm]; exact hvt)

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2** of [han2009theoretical], the sharp a priori bound. Under the hypotheses of
`AtkinsonHan.Chapter05.theorem_5_4_2`, if the Newton iterates converge to $u^*$, then for all
$n$
$$\|u_n - u^*\| \le \frac{[1 - \sqrt{1 - 2h}]^{2^n}}{2^n a L}.$$

This is the finer form of the last conclusion of `AtkinsonHan.Chapter05.theorem_5_4_2`. With
`AtkinsonHan.Chapter05.theorem_5_4_2_step` and `AtkinsonHan.Chapter05.theorem_5_4_2_unique`, it
completes Theorem 5.4.2.

**Reading.** Same sharp estimate under the separate initial-point ball hypotheses.
-/
theorem theorem_5_4_2_sharp {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) {ustar : U}
    (hustar : Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar)) (n : ℕ) :
    ‖Newton.iterate F F' u₀ n - ustar‖
      ≤ (1 - Real.sqrt (1 - 2 * (a * b * L))) ^ 2 ^ n / (2 ^ n * (a * L)) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich_norm_sub_le ha hLpos hb e he ha' hb' hF hLip
    (by rw [hcomm]; exact hh) (by rw [hcomm]; exact hr) hustar n
  rwa [hcomm] at hkey

end Complete

section Chord

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Equation (5.4.11)** of [han2009theoretical]. In the modified Newton method the derivative is
replaced by one fixed invertible operator $A$ (in the book, $A = F'(u_0)$), and the iterates
satisfy
$$u_{n+1} = u_n - A^{-1} F(u_n).$$
-/
theorem equation_5_4_11 (F : U → W) (A : U ≃L[ℝ] W) (u₀ : U) (n : ℕ) :
    Newton.chordIterate F A u₀ (n + 1) = Newton.chordStep F A (Newton.chordIterate F A u₀ n) :=
  Newton.chordIterate_succ F A u₀ n

/-- **Exercise 5.4.5** of [han2009theoretical], the modified Newton method (5.4.11). Let
$F : U \to W$ with $F(u^*) = 0$, let $r > 0$, let $F$ have the Fréchet derivative $F'(u)$ at
every $u \in \bar B(u^*, r)$, and let $\|F'(u) - F'(u^*)\| \le L \|u - u^*\|$ for these $u$. Let
$A : U \to W$ be an invertible bounded linear operator with
$$\|I - A^{-1} F'(u^*)\| < 1.$$
Then there are $\delta > 0$ and $0 \le q < 1$ such that for every $u_0 \in \bar B(u^*, \delta)$
the iterates of the modified method satisfy $\|u_n - u^*\| \le q^n \|u_0 - u^*\|$ for all $n$,
and converge to $u^*$.

The convergence is linear and not quadratic: the fixed derivative costs an order of convergence.
The book's choice $A = F'(u_0)$ satisfies the hypothesis when $u_0$ is close enough to $u^*$, by
the perturbation theorem. The Lipschitz condition is needed only at the point $u^*$, and the
spaces need not be complete.

**Reading.** A contraction criterion gives linear convergence with a general fixed inverse.
-/
theorem exercise_5_4_5 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    {r L : ℝ} (hr : 0 < r) (A : U ≃L[ℝ] W)
    (hF : ∀ u ∈ closedBall ustar r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall ustar r, ‖F' u - F' ustar‖ ≤ L * ‖u - ustar‖)
    (hA : ‖1 - (A.symm : W →L[ℝ] U) ∘L F' ustar‖ < 1) :
    ∃ δ > 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ u₀ ∈ closedBall ustar δ,
      (∀ n, ‖Newton.chordIterate F A u₀ n - ustar‖ ≤ q ^ n * ‖u₀ - ustar‖) ∧
        Tendsto (Newton.chordIterate F A u₀) atTop (𝓝 ustar) :=
  Newton.tendsto_chordIterate hroot hr A hF hLip hA

end Chord

section System

/-- **Equation (5.4.7)** of [han2009theoretical]. Newton's method for a nonlinear system $F(x) = 0$
in $\mathbb{R}^d$. If $F'(x)$ is invertible and $x_+$ is the Newton step from $x$, then
$\delta = x_+ - x$ solves the linear system $F'(x) \delta = -F(x)$, and $x_+ = x + \delta$.

The space $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`. -/
theorem equation_5_4_7 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : (e : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = F' x) :
    F' x (Newton.step F F' x - x) = -F x ∧
      Newton.step F F' x = x + (Newton.step F F' x - x) := by
  refine ⟨newtonStep_sub_eq e he, by abel⟩

end System

section IntegralEquation

open Set IntegralOperator

variable {a b : ℝ}

/-- **Equation (5.4.8)** of [han2009theoretical]. Let $a \le b$, and let $k$ and $k_z$ be continuous
functions on $[a, b] \times [a, b] \times \mathbb{R}$ such that $k_z(t, s, z)$ is the derivative
of $z \mapsto k(t, s, z)$. Let $\mathcal{K}$ be the Urysohn operator of $k$ on $C[a, b]$. Then
the operator $F(v) = v - \mathcal{K}(v)$ has, at every $u \in C[a, b]$, the Fréchet derivative
$$F'(u) = I - \mathcal{K}'(u),$$
where $\mathcal{K}'(u)$ is the Fredholm operator with the kernel $k_z(t, s, u(s))$.

This is `AtkinsonHan.Chapter05.example_5_3_10` together with the derivative of the identity.

**Correction.** The last line of the source's calculation prints a plus sign before the
integral. The residual subtracts the integral operator, so its derivative subtracts the
Fredholm term. -/
theorem equation_5_4_8 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    (hk : ∀ (x y : Icc a b) (z : ℝ), HasDerivAt (fun t => k (x, y, t)) (kz (x, y, z)) z)
    (u : C(Icc a b, ℝ)) :
    HasFDerivAt (fun v => v - urysohn hab k v) (1 - fredholm hab (urysohnDerivKernel kz u)) u :=
  (hasFDerivAt_id u).sub (example_5_3_10 hab hk u)

/-- The operator $I - \mathcal{K}$, for the Fredholm operator $\mathcal{K}$ of a kernel $K$, maps
$v$ to $t \mapsto v(t) - \int_a^b K(t, s) v(s)\, ds$. -/
private theorem one_sub_fredholm_apply (hab : a ≤ b) (K : C(Icc a b × Icc a b, ℝ))
    (v : C(Icc a b, ℝ)) (t : Icc a b) :
    (1 - fredholm hab K) v t
      = v t - ∫ s in a..b, K (t, projIcc a b hab s) * v (projIcc a b hab s) :=
  rfl

/-- **Equations (5.4.9)–(5.4.10)** of [han2009theoretical]. Let $k$ and $k_z$ be as in
`AtkinsonHan.Chapter05.equation_5_4_8`, let $F(v) = v - \mathcal{K}(v)$, and let
$F'(v) = I - \mathcal{K}'(v)$ for all $v \in C[a, b]$. Let $F'(u)$ be invertible, and let
$\delta = u_+ - u$ be the increment of the Newton step from $u$. Then $\delta$ solves the linear
integral equation of the second kind
$$\delta(t) - \int_a^b k_z(t, s, u(s))\, \delta(s)\, ds = -\Bigl(u(t) - \int_a^b k(t, s, u(s))\,
  ds\Bigr) = -F(u)(t)$$
for every $t \in [a, b]$. So each Newton step for the nonlinear integral equation costs the
solution of one linear one.

The book also assumes that $F'(u_n)$ is invertible. Here this is the equivalence `e`, as in
`AtkinsonHan.Chapter05.equation_5_4_7`.

**Correction.** In the negative residual on the right, the kernel is evaluated at the current
iterate. The printed additional factor $u_n(s)$ would change the equation. -/
theorem equation_5_4_10 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    {F : C(Icc a b, ℝ) → C(Icc a b, ℝ)} (hF : ∀ v, F v = v - urysohn hab k v)
    {F' : C(Icc a b, ℝ) → C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)}
    (hF' : ∀ v, F' v = 1 - fredholm hab (urysohnDerivKernel kz v)) (u : C(Icc a b, ℝ))
    (e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ))
    (he : (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) = F' u) (t : Icc a b) :
    Newton.step F F' u t - u t
        - ∫ s in a..b, kz (t, projIcc a b hab s, u (projIcc a b hab s))
            * (Newton.step F F' u (projIcc a b hab s) - u (projIcc a b hab s))
      = -(u t - ∫ s in a..b, k (t, projIcc a b hab s, u (projIcc a b hab s))) := by
  have h := newtonStep_sub_eq (F := F) e he
  rw [hF' u, hF u] at h
  have h2 := congrArg (fun w : C(Icc a b, ℝ) => w t) h
  simp only [one_sub_fredholm_apply hab, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    urysohnDerivKernel_apply, urysohn_apply] at h2
  exact h2

/-- **Equations (5.4.11)–(5.4.12)** of [han2009theoretical]. Let $k$, $k_z$ and $F$ be as in
`AtkinsonHan.Chapter05.equation_5_4_10`, let $u_0 \in C[a, b]$, and let
$A = I - \mathcal{K}'(u_0)$ be invertible. Let $\delta = u_+ - u$ be the increment of the
modified Newton step $u_+ = u - A^{-1} F(u)$ from any $u$. Then for every $t \in [a, b]$
$$\delta(t) - \int_a^b k_z(t, s, u_0(s))\, \delta(s)\, ds = -F(u)(t).$$
So every step solves a linear integral equation with the same kernel. This makes the modified
method cheap, and by `AtkinsonHan.Chapter05.exercise_5_4_5` only linearly convergent.

**Correction.** In the negative residual the kernel is evaluated at $u_n(s)$, and the printed
additional factor $u_n(s)$ is omitted. -/
theorem equation_5_4_12 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    {F : C(Icc a b, ℝ) → C(Icc a b, ℝ)} (hF : ∀ v, F v = v - urysohn hab k v)
    (u₀ : C(Icc a b, ℝ)) (A : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ))
    (hA : (A : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
      = 1 - fredholm hab (urysohnDerivKernel kz u₀)) (u : C(Icc a b, ℝ)) (t : Icc a b) :
    Newton.chordStep F A u t - u t
        - ∫ s in a..b, kz (t, projIcc a b hab s, u₀ (projIcc a b hab s))
            * (Newton.chordStep F A u (projIcc a b hab s) - u (projIcc a b hab s))
      = -(u t - ∫ s in a..b, k (t, projIcc a b hab s, u (projIcc a b hab s))) := by
  have hsub : Newton.chordStep F A u - u = -(A.symm (F u)) := by
    rw [Newton.chordStep]; abel
  have h : (A : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) (Newton.chordStep F A u - u) = -F u := by
    rw [hsub, ContinuousLinearEquiv.coe_coe, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  rw [hA, hF u] at h
  have h2 := congrArg (fun w : C(Icc a b, ℝ) => w t) h
  simp only [one_sub_fredholm_apply hab, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    urysohnDerivKernel_apply, urysohn_apply] at h2
  exact h2

end IntegralEquation

section BVP

open ContDiffMapIcc

local notation "C²" => ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 2

local notation "C²₀" => ContDiffMapIcc.zeroBoundary (zero_le_one : (0 : ℝ) ≤ 1) 2

/-- **Section 5.4.2** of [han2009theoretical], Newton's method for the two-point boundary value
problem $u'' = f(t, u)$ on $(0, 1)$, $u(0) = u(1) = 0$. Let $f$ and $f_u$ be continuous
functions on $[0, 1] \times \mathbb{R}$ such that $f_u(t, z)$ is the derivative of
$z \mapsto f(t, z)$. Let $F : C^2_0[0, 1] \to C[0, 1]$ be $F(v)(t) = v''(t) - f(t, v(t))$. Then
for every $u \in C^2_0[0, 1]$, $F$ has the Fréchet derivative at $u$ given by
$$F'(u)(y)(t) = y''(t) - f_u(t, u(t))\, y(t).$$
So each Newton step (5.4.9) solves a linear two-point boundary value problem, whose coefficient
$f_u(\cdot, u(\cdot))$ is taken at the current iterate.

The space $C^2_0[0, 1]$ is `ContDiffMapIcc.zeroBoundary (zero_le_one : (0 : ℝ) ≤ 1) 2` from
`Numlib.Analysis.Calculus.ContDiffMapIcc`, a closed subspace of the Banach space $C^2[0, 1]$.
The derivative has two parts: the bounded linear map $u \mapsto u''$, and the Nemytskii operator
$u \mapsto f(\cdot, u(\cdot))$ from `Numlib.Nonlinear.Nemytskii`, whose derivative is
multiplication by $f_u(\cdot, u(\cdot))$. The argument is the same as in Example 5.3.10. -/
theorem example_5_4_bvp {f fu : C(Set.Icc (0 : ℝ) 1 × ℝ, ℝ)}
    (hf : ∀ (t : Set.Icc (0 : ℝ) 1) (z : ℝ), HasDerivAt (fun s => f (t, s)) (fu (t, z)) z)
    (F : C²₀ → C(Set.Icc (0 : ℝ) 1, ℝ))
    (hF : ∀ (v : C²₀) (t : Set.Icc (0 : ℝ) 1),
      F v t = (v : C²).deriv 2 t - f (t, (v : C²) t))
    (u : C²₀) :
    ∃ F' : C²₀ →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ),
      (∀ (y : C²₀) (t : Set.Icc (0 : ℝ) 1),
          F' y t = (y : C²).deriv 2 t - fu (t, (u : C²) t) * (y : C²) t) ∧
        HasFDerivAt F F' u := by
  set D : C²₀ →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ) :=
    (derivCLM (zero_le_one : (0 : ℝ) ≤ 1) 2 2).comp (zeroBoundary _ 2).subtypeL with hD
  set E : C²₀ →L[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ) :=
    (derivCLM (zero_le_one : (0 : ℝ) ≤ 1) 2 0).comp (zeroBoundary _ 2).subtypeL with hE
  refine ⟨D - (ContinuousLinearMap.mul ℝ C(Set.Icc (0 : ℝ) 1, ℝ) (Nemytskii.op fu (E u))).comp E,
    fun y t => ?_, ?_⟩
  · simp [hD, hE]
  · have hFG : F = fun v => D v - Nemytskii.op f (E v) :=
      funext fun v => ContinuousMap.ext fun t => by rw [hF v t]; rfl
    rw [hFG]
    exact D.hasFDerivAt.sub ((Nemytskii.hasFDerivAt_op hf (E u)).comp u E.hasFDerivAt)

end BVP

end AtkinsonHan.Chapter05
