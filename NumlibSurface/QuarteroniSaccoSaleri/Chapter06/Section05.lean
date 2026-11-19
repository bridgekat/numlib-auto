/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 6.5: Stopping Criteria

This module formalizes Section 6.5 of [quarteroni2000numerical], on the two tests that stop an
iteration $x^{(k)}$ that converges to a zero $\alpha$ of $f$. Each test is justified by a limit. The
residual test controls the error $e^{(k)} = \alpha - x^{(k)}$ by the residual $f(x^{(k)})$: at a
root of multiplicity $m$ the relative error behaves like $(m! / (|f^{(m)}(\alpha)|
|\alpha|^m))^{1/m} |f(x^{(k)})|^{1/m}$, which is the estimate (6.6) along the sequence, and at a
simple root the error is bound to the residual by the factor $1 / |f'(\alpha)|$. The increment test
(6.31) controls the error of a fixed-point iteration by the increment $x^{(k+1)} - x^{(k)}$, with
the factor $1 / (1 - \varphi'(\alpha))$.

The factor $1 / |f'(\alpha)|$ gives the qualitative conclusions of the source for
$|f'(\alpha)| \simeq 1$, $|f'(\alpha)| \ll 1$ and $|f'(\alpha)| \gg 1$. The proofs specialize
`IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow` in `Numlib.Analysis.Calculus.RootMultiplicity`
and `tendsto_sub_div_sub_succ_of_hasDerivAt` in `Numlib.Nonlinear.Order`.

## Main results

* Section 6.5, `QuarteroniSaccoSaleri.Chapter06.residualTest`: the error estimate of the residual
  test at a root of multiplicity $m$, as a limit of ratios.
* Section 6.5, `QuarteroniSaccoSaleri.Chapter06.residualTest_simple`: at a simple root, $|x^{(k)} -
  \alpha| / |f(x^{(k)})| \to 1 / |f'(\alpha)|$.
* Equation (6.31), `QuarteroniSaccoSaleri.Chapter06.equation_6_31`: for a fixed-point iteration,
  $e^{(k)} / (x^{(k+1)} - x^{(k)}) \to 1 / (1 - \varphi'(\alpha))$.

## Conventions

* The error is $e^{(k)} = \alpha - x^{(k)}$, as in the source. With this sign the constant of (6.31)
  is $1 / (1 - \varphi'(\alpha))$, as printed.

## Deviations from the source

* **Reading.** The residual estimate is a ratio limit for sequences approaching the root without
  hitting it. See `QuarteroniSaccoSaleri.Chapter06.residualTest`,
  `QuarteroniSaccoSaleri.Chapter06.residualTest_simple`.
* **Reading.** The increment estimate is a signed ratio limit for a converging orbit, with eventual
  nonzero increments. See `QuarteroniSaccoSaleri.Chapter06.equation_6_31`.
* **Section 6.5, residual test** (reading). The estimates are stated as limits along sequences that
  never equal $\alpha$. See `QuarteroniSaccoSaleri.Chapter06.residualTest` and
  `QuarteroniSaccoSaleri.Chapter06.residualTest_simple`.
* **Equation (6.31)** (reading). The estimate is stated as a limit along an orbit that never equals
  $\alpha$. See `QuarteroniSaccoSaleri.Chapter06.equation_6_31`.

## Not formalized

* **Example 6.9.** It is a numerical computation.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

variable {f φ : ℝ → ℝ} {α : ℝ}

-- `α ≠ 0` is the book's standing assumption for a relative error; the limit is trivially true
-- at `α = 0`, where both sides are `0` under Lean's `a / 0 = 0`.
set_option linter.unusedVariables false in
/-- **Section 6.5** of [quarteroni2000numerical], the error estimate of the residual test, in the
display after item 1. Let $m \ge 1$, let $f$ be of class $C^m$ on a neighbourhood of $\alpha$,
and let $\alpha \neq 0$ be a root of $f$ of multiplicity $m$. Let $x^{(k)} \to \alpha$ with
$x^{(k)} \neq \alpha$ for all $k$. Then
$$\lim_{k \to \infty} \frac{|x^{(k)} - \alpha| / |\alpha|}{|f(x^{(k)})|^{1/m}} = \left(
  \frac{m!}{|f^{(m)}(\alpha)| \, |\alpha|^m} \right)^{1/m}.$$

**Reading.** The source writes the estimate $|e^{(k)}| / |\alpha| \lesssim (m! /
(|f^{(m)}(\alpha)| |\alpha|^m))^{1/m} |f(x^{(k)})|^{1/m}$, obtained by applying (6.6). Here it
is the statement that the ratio of the two sides tends to $1$. The limit needs
$x^{(k)} \neq \alpha$, which the source does not say.

The condition $\alpha \neq 0$ is the standing assumption of the source for a relative error; the
proof does not use it, since at $\alpha = 0$ both sides are $0$ because division by $0$ gives
$0$ in Lean. The proof composes `QuarteroniSaccoSaleri.Chapter06.equation_6_4` with the
convergence $x^{(k)} \to \alpha$ in the punctured neighbourhood of $\alpha$, and uses
`QuarteroniSaccoSaleri.Chapter06.rpow_div_abs_eq` for the constant.

**Reading.** The error/residual estimates are ratio limits along converging sequences that avoid the
root. The relative estimate also requires a nonzero root.
-/
theorem residualTest {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) (hα0 : α ≠ 0) {x : ℕ → ℝ} (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (|x k - α| / |α|) / |f (x k)| ^ (1 / (m : ℝ))) atTop
      (𝓝 ((m.factorial / (|iteratedDeriv m f α| * |α| ^ m)) ^ (1 / (m : ℝ)))) := by
  have h := ((equation_6_4 hm hf hα).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)).div_const |α|
  rw [rpow_div_abs_eq (by positivity) hm, div_div] at h
  refine h.congr fun k => ?_
  simp only [Function.comp]
  rw [div_right_comm]

/-- **Section 6.5** of [quarteroni2000numerical], the residual test at a simple root. Let $f$ be of
class $C^1$ on a neighbourhood of $\alpha$, let $f(\alpha) = 0$ and $f'(\alpha) \neq 0$, and let
$x^{(k)} \to \alpha$ with $x^{(k)} \neq \alpha$ for all $k$. Then
$$\lim_{k \to \infty} \frac{|x^{(k)} - \alpha|}{|f(x^{(k)})|} = \frac{1}{|f'(\alpha)|}.$$

**Reading.** The source says that the error is bound to the residual by the factor
$1 / |f'(\alpha)|$. Here this is a limit, which needs $x^{(k)} \neq \alpha$.

This is the case $m = 1$ of `QuarteroniSaccoSaleri.Chapter06.residualTest` without the division
by $|\alpha|$, so $\alpha = 0$ is allowed.

**Reading.** The error/residual estimates are ratio limits along converging sequences that avoid the
root. The relative estimate also requires a nonzero root.
-/
theorem residualTest_simple (hf : ContDiffAt ℝ 1 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    {x : ℕ → ℝ} (hne : ∀ k, x k ≠ α) (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => |x k - α| / |f (x k)|) atTop (𝓝 (1 / |deriv f α|)) := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have h := (equation_6_4 le_rfl (by simpa using hf) hroot).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  simp only [Function.comp_def] at h
  simpa using h

/-- **Equation (6.31)** of [quarteroni2000numerical], the increment test. Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be differentiable at a fixed point
$\alpha = \varphi(\alpha)$ with $\varphi'(\alpha) \neq 1$. Let $x^{(k+1)} = \varphi(x^{(k)})$
for all $k$, with $x^{(k)} \to \alpha$ and $x^{(k)} \neq \alpha$ for all $k$. Then
$x^{(k+1)} - x^{(k)} \neq 0$ for all large $k$, and
$$\lim_{k \to \infty} \frac{\alpha - x^{(k)}}{x^{(k+1)} - x^{(k)}} = \frac{1}{1 -
  \varphi'(\alpha)}.$$

**Reading.** The source writes $e^{(k)} \simeq (x^{(k+1)} - x^{(k)}) / (1 - \varphi'(\alpha))$
with $e^{(k)} = \alpha - x^{(k)}$. Here this is a limit of ratios, which needs
$x^{(k)} \neq \alpha$.

So the test is unreliable when $\varphi'(\alpha)$ is close to $1$, optimal for methods of order
$2$, where $\varphi'(\alpha) = 0$ (Newton's method), and still satisfactory for
$-1 < \varphi'(\alpha) < 0$. The proof specializes `tendsto_sub_div_sub_succ_of_hasDerivAt`.

**Reading.** The approximate error formula is a limit of the signed error divided by the increment,
which is eventually nonzero under the stated hypotheses. It uses differentiability at the fixed
point and assumes a convergent orbit avoiding that point.
-/
theorem equation_6_31 (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    (∀ᶠ k in atTop, x (k + 1) - x k ≠ 0) ∧
      Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - deriv φ α))) :=
  tendsto_sub_div_sub_succ_of_hasDerivAt hφ.hasDerivAt hα h1 hx hne hlim

end QuarteroniSaccoSaleri.Chapter06
