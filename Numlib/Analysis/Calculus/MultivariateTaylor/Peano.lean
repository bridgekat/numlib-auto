/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Taylor's theorem with Peano remainder

Let $E$ and $F$ be real normed spaces, and let $f \colon E \to F$ be of class $C^n$ at $x$. Let
$T_{f,n}(x, h) = \sum_{i=0}^{n} \frac{1}{i!} \nabla^i f(x)[h]^i$ be the Taylor polynomial of degree
$n$ of $f$ at $x$ (`taylorPolynomial`). This module proves **Taylor's theorem with Peano
remainder**, (A.12) of [cartis2022evaluation]:
$$f(x + h) - T_{f,n}(x, h) = o(\|h\|^n) \quad \text{as } h \to 0.$$
For $n = 0$ the Taylor polynomial is $f(x)$, and the statement is the continuity of $f$ at $x$.

## Main results

* `exists_norm_sub_taylorPolynomial_le`: for every $\eta > 0$ there is $r > 0$ such that
  $\|f(x + h) - T_{f,n}(x, h)\| \le \eta \|h\|^n$ whenever $\|h\| < r$.
* `sub_taylorPolynomial_isLittleO`: the little-o form (A.12).

## Proof outline

On a small ball about $x$, the $n$-th derivative $\nabla^n f$ is Hölder continuous with exponent
$\beta = 0$, and its Hölder constant is the oscillation of $\nabla^n f$ on the ball. This constant
is small because $\nabla^n f$ is continuous at $x$. The Hölder remainder bound (A.14) then gives the
result, since the generalized factorial $(n + 0)!$ is $n!$.

## Implementation notes

* The hypothesis is that $f$ is $C^n$ at $x$, that is, $C^n$ on a neighbourhood of $x$
  (`ContDiffAt ℝ n f x`). This is the setting of all applications of (A.12).
-/

open Filter Metric Asymptotics
open scoped Nat Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {n : ℕ} {x : E}

/-- Let $C \subseteq E$. If $\|\nabla^n f(y) - \nabla^n f(z)\| \le H$ for all $y, z \in C$, then
$\nabla^n f$ is Hölder continuous on $C$ with constant $H$ and exponent $0$
(`IteratedFDerivHolderOn`). -/
theorem iteratedFDerivHolderOn_zero_of_norm_sub_le {C : Set E} {H : ℝ}
    (h : ∀ y ∈ C, ∀ z ∈ C, ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖ ≤ H) :
    IteratedFDerivHolderOn f n H 0 C := by
  intro y hy z hz
  simpa using h y hy z hz

/-- **Peano remainder, quantitative form.** Let $f \colon E \to F$ be of class $C^n$ at $x$, and let
$\eta > 0$. Then there is $r > 0$ such that for every $h \in E$ with $\|h\| < r$,
$$\|f(x + h) - T_{f,n}(x, h)\| \le \eta \|h\|^n.$$

This is the quantitative content of (A.12) of [cartis2022evaluation]. -/
theorem exists_norm_sub_taylorPolynomial_le (hf : ContDiffAt ℝ n f x) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ h : E, ‖h‖ < r → ‖f (x + h) - taylorPolynomial f n x h‖ ≤ η * ‖h‖ ^ n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ n f y := hf.eventually (by simp)
  have hcont : ∀ᶠ y in 𝓝 x,
      ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ < η * n ! / 2 := by
    have hc : ContinuousAt (iteratedFDeriv ℝ n f) x := hf.continuousAt_iteratedFDeriv le_rfl
    simpa [dist_eq_norm] using
      Metric.tendsto_nhds.1 hc (η * n ! / 2) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and hcont)
  refine ⟨r, hr, fun h hh => ?_⟩
  have hosc : ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖ ≤ η * n ! := by
    intro y hy z hz
    calc ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖
        ≤ ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ +
          ‖iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f x‖ := by
          rw [norm_sub_rev (iteratedFDeriv ℝ n f z)]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * n ! := by linarith [(hball y hy).2, (hball z hz).2]
  have hxs : x + h ∈ ball x r := by simpa [mem_ball, dist_eq_norm] using hh
  have key := norm_sub_taylorPolynomial_le_of_holder (convex_ball x r)
    (fun y hy => (hball y hy).1) le_rfl (iteratedFDerivHolderOn_zero_of_norm_sub_le hosc)
    (mem_ball_self hr) hxs
  rwa [holderFactorial_zero_right, add_zero, Real.rpow_natCast, mul_div_cancel_right₀ _ hfac.ne']
    at key

/-- **Taylor's theorem with Peano remainder.** Let $f \colon E \to F$ be of class $C^n$ at $x$. Then
$$f(x + h) - T_{f,n}(x, h) = o(\|h\|^n) \quad \text{as } h \to 0.$$

This is (A.12) of [cartis2022evaluation]. The little-o is `Asymptotics.IsLittleO` along the
neighbourhood filter of $0$. -/
theorem sub_taylorPolynomial_isLittleO (hf : ContDiffAt ℝ n f x) :
    (fun h => f (x + h) - taylorPolynomial f n x h) =o[𝓝 0] fun h => ‖h‖ ^ n := by
  refine isLittleO_iff.2 fun η hη => ?_
  obtain ⟨r, hr, hbound⟩ := exists_norm_sub_taylorPolynomial_le hf hη
  filter_upwards [ball_mem_nhds (0 : E) hr] with h hh
  rw [mem_ball_zero_iff] at hh
  simpa [abs_of_nonneg (pow_nonneg (norm_nonneg h) n)] using hbound h hh
