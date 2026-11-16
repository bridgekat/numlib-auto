/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.MonotoneNewton
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 8

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 8.
Lemma B.8.1 gives the convergence of the Newton and the secant iterations for a scalar equation
$\theta(\lambda) = 0$ with a convex decreasing, or a concave increasing, function $\theta$: from a
suitable starting point the iterates increase monotonically to the root $\lambda^*$, linearly with
the factor $\gamma^N = 1 - \theta'(\lambda^*)/\theta'(\lambda_0)$, and Q-superlinearly. Lemma B.8.2
shows that the Newton step for the transformed secular equation
$\pi(\lambda)^\beta = \Delta^{2\beta}$ decreases monotonically in $\beta$. The proofs of Lemma 8.2.1
and Theorems 8.2.2–8.2.6 that the book gives in this appendix are the proofs of those results in
Chapter 8. The proofs specialize the backbone module `Numlib.Nonlinear.MonotoneNewton`.

## Main results

* Lemma B.8.1, `CartisGouldToint.AppendixB.lemma_B_8_1`: convergence of the Newton and the secant
  iterates for a convex strictly decreasing function.
* Lemma B.8.1, `CartisGouldToint.AppendixB.lemma_B_8_1_concave`: the same for a concave strictly
  increasing function.
* Lemma B.8.2, `CartisGouldToint.AppendixB.lemma_B_8_2`: the formula (B.8.7) for the Newton step of
  the transformed secular equation, and its monotonicity in $\beta$.

## Implementation notes

* Continuous differentiability of $\theta$ on $I = [\lambda_{\min}, \lambda_{\max}]$ is formalized
  as a function $\theta'$ that is a derivative of $\theta$ within $I$ at each point of $I$ and is
  continuous on $I$.

## Deviations from the source

* **Lemma B.8.1** (correction). The hypothesis $\theta'(\lambda^*) \neq 0$ is added: for
  $\theta(x) = (1 - x)^2$ on $[0, 1]$ and $\lambda_0 = 0$ the Newton iterates are $1 - 2^{-j}$,
  which converge only linearly, and $\gamma^N = 1$. See `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.1, concave case** (correction). The starting condition is $\theta(\lambda_0) < 0$, and
  $\theta(\lambda_1) < 0$ for the secant method; the book prints $> 0$ for both cases. See
  `CartisGouldToint.AppendixB.lemma_B_8_1_concave`.
* **Lemma B.8.1, (B.8.3)** (typo). The tangent inequality is printed reversed; the proof uses
  $\theta(x) \ge \theta'(\lambda^*)(x - \lambda^*)$. See `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.1, monotonicity** (correction). Iterates that reach $\lambda^*$ stay there, so the
  iterates increase monotonically but in general not strictly. See
  `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.2** (reading). The hypothesis that $\lambda^*$ is the root of
  $\pi(\lambda) = \Delta^2$ plays no role and is dropped. The hypothesis $g \neq 0$ is stated, since
  the Newton step is defined only then. See `CartisGouldToint.AppendixB.lemma_B_8_2`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

open Subproblem CartisGouldToint.Chapter08

/-- **Lemma B.8.1** of [cartis2022evaluation] (convergence rates of one-dimensional Newton-like
iteration), convex case. Let $I = [\lambda_{\min}, \lambda_{\max}]$, and let
$\theta : \mathbb{R} \to \mathbb{R}$ be convex and strictly decreasing on $I$, with a derivative
$\theta'$ within $I$ at every point of $I$ that is continuous on $I$. Let $\lambda^* \in I$ with
$\theta(\lambda^*) = 0$ and $\theta'(\lambda^*) \neq 0$, and let $\gamma^N = 1 -
\theta'(\lambda^*)/\theta'(\lambda_0)$.

(i) Let $\lambda_0 \in I$ with $\theta(\lambda_0) > 0$, and let $\lambda_{j+1} = \lambda_j -
\theta(\lambda_j)/\theta'(\lambda_j)$ be the Newton iterates (B.8.1). Then
$\lambda_j \in [\lambda_0, \lambda^*]$ for all $j$, the sequence $(\lambda_j)$ is nondecreasing
and converges to $\lambda^*$, $\gamma^N \in [0, 1)$,
$$\lambda^* - \lambda_{j+1} \le \gamma^N (\lambda^* - \lambda_j) \quad \text{for all } j,$$
and the convergence is Q-superlinear. If moreover $\theta'$ is Lipschitz continuous on a
neighborhood of $\lambda^*$ in $I$, the convergence has Q-order $2$.

(ii) Let $\lambda_0 < \lambda_1$ in $I$ with $\theta(\lambda_0) > 0$ and
$\theta(\lambda_1) > 0$, and let $(\lambda_j)$ be the secant iterates (B.8.2) from $\lambda_0$
and $\lambda_1$. Then $\lambda_j \in [\lambda_0, \lambda^*]$ for all $j \ge 1$, the sequence
$(\lambda_j)_{j \ge 1}$ is nondecreasing and converges to $\lambda^*$, $\gamma^N \in [0, 1)$,
$\lambda^* - \lambda_{j+1} \le \gamma^N (\lambda^* - \lambda_j)$ for all $j \ge 1$, and the
convergence is Q-superlinear.

**Correction.** The book does not assume $\theta'(\lambda^*) \neq 0$, and the lemma fails
without it: for $\theta(x) = (1 - x)^2$ on $[0, 1]$ and $\lambda_0 = 0$ the Newton iterates are
$1 - 2^{-j}$, which converge only linearly, and $\gamma^N = 1$. The book also prints the tangent
inequality (B.8.3) reversed; the proof uses $\theta(x) \ge \theta'(\lambda^*)(x - \lambda^*)$.
The increase of the iterates is not strict in general, because iterates that reach $\lambda^*$
stay there.

The Newton iterates are the iterates of `Newton.scalarStep θ θ'`. The secant iterates are
`Secant.iterate θ λ₀ λ₁`, with `Secant.iterate θ λ₀ λ₁ j` $= \lambda_{j+1}$. Q-superlinear
convergence is `ConvergesSuperlinearly`, and convergence with Q-order $2$ is
`ConvergesWithOrder` with order $2$. -/
theorem lemma_B_8_1 {θ θ' : ℝ → ℝ} {lmin lmax lamStar : ℝ}
    (hc : ConvexOn ℝ (Icc lmin lmax) θ) (hm : StrictAntiOn θ (Icc lmin lmax))
    (hd : ∀ x ∈ Icc lmin lmax, HasDerivWithinAt θ (θ' x) (Icc lmin lmax) x)
    (hd' : ContinuousOn θ' (Icc lmin lmax)) (hstar : lamStar ∈ Icc lmin lmax)
    (hroot : θ lamStar = 0) (hθ' : θ' lamStar ≠ 0) :
    (∀ lam₀ ∈ Icc lmin lmax, 0 < θ lam₀ →
      (∀ k, (Newton.scalarStep θ θ')^[k] lam₀ ∈ Icc lam₀ lamStar) ∧
      Monotone (fun k => (Newton.scalarStep θ θ')^[k] lam₀) ∧
      Tendsto (fun k => (Newton.scalarStep θ θ')^[k] lam₀) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - (Newton.scalarStep θ θ')^[k + 1] lam₀ ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - (Newton.scalarStep θ θ')^[k] lam₀)) ∧
      ConvergesSuperlinearly (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar ∧
      ((∃ K, ∃ U ∈ 𝓝[Icc lmin lmax] lamStar, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar 2)) ∧
    (∀ lam₀ ∈ Icc lmin lmax, ∀ lam₁ ∈ Icc lmin lmax, lam₀ < lam₁ → 0 < θ lam₀ → 0 < θ lam₁ →
      (∀ k, Secant.iterate θ lam₀ lam₁ k ∈ Icc lam₀ lamStar) ∧
      Monotone (Secant.iterate θ lam₀ lam₁) ∧
      Tendsto (Secant.iterate θ lam₀ lam₁) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - Secant.iterate θ lam₀ lam₁ (k + 1) ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - Secant.iterate θ lam₀ lam₁ k)) ∧
      ConvergesSuperlinearly (Secant.iterate θ lam₀ lam₁) lamStar) := by
  have h : Newton.IsConvexAntiRoot θ θ' (Icc lmin lmax) lamStar :=
    ⟨hc, hm, hd, hstar, hroot, hθ'⟩
  have hcont : ContinuousWithinAt θ' (Icc lmin lmax) lamStar := hd' lamStar hstar
  refine ⟨fun lam₀ h₀ hθ₀ => ?_, fun lam₀ h₀ lam₁ h₁ h01 hθ₀ hθ₁ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Newton.monotone_scalarStep_iterate_of_convexOn h h₀ hθ₀
    exact ⟨h1, h2, h3, h4, h5, h6 hcont, h7⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      Newton.monotone_secant_iterate_of_convexOn h h₀ h₁ h01 hθ₀ hθ₁
    exact ⟨h1, h2, h3, h4, h5, h6 hcont⟩

/-- **Lemma B.8.1** of [cartis2022evaluation], concave case. Let
$I = [\lambda_{\min}, \lambda_{\max}]$, and let $\theta : \mathbb{R} \to \mathbb{R}$ be concave
and strictly increasing on $I$, with a derivative $\theta'$ within $I$ at every point of $I$
that is continuous on $I$. Let $\lambda^* \in I$ with $\theta(\lambda^*) = 0$ and
$\theta'(\lambda^*) \neq 0$, and let $\gamma^N = 1 - \theta'(\lambda^*)/\theta'(\lambda_0)$.
Then the conclusions (i) and (ii) of `CartisGouldToint.AppendixB.lemma_B_8_1` hold for the
Newton iterates from $\lambda_0 \in I$ with $\theta(\lambda_0) < 0$, and for the secant iterates
from $\lambda_0 < \lambda_1$ in $I$ with $\theta(\lambda_0) < 0$ and $\theta(\lambda_1) < 0$.

**Correction.** The book prints the starting conditions $\theta(\lambda_0) > 0$ and
$\theta(\lambda_1) > 0$ for both cases. In the concave increasing case the conditions must be
$\theta(\lambda_0) < 0$ and $\theta(\lambda_1) < 0$, as the reduction of the proof to $-\theta$
shows. As in the convex case, the hypothesis $\theta'(\lambda^*) \neq 0$ is added. -/
theorem lemma_B_8_1_concave {θ θ' : ℝ → ℝ} {lmin lmax lamStar : ℝ}
    (hc : ConcaveOn ℝ (Icc lmin lmax) θ) (hm : StrictMonoOn θ (Icc lmin lmax))
    (hd : ∀ x ∈ Icc lmin lmax, HasDerivWithinAt θ (θ' x) (Icc lmin lmax) x)
    (hd' : ContinuousOn θ' (Icc lmin lmax)) (hstar : lamStar ∈ Icc lmin lmax)
    (hroot : θ lamStar = 0) (hθ' : θ' lamStar ≠ 0) :
    (∀ lam₀ ∈ Icc lmin lmax, θ lam₀ < 0 →
      (∀ k, (Newton.scalarStep θ θ')^[k] lam₀ ∈ Icc lam₀ lamStar) ∧
      Monotone (fun k => (Newton.scalarStep θ θ')^[k] lam₀) ∧
      Tendsto (fun k => (Newton.scalarStep θ θ')^[k] lam₀) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - (Newton.scalarStep θ θ')^[k + 1] lam₀ ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - (Newton.scalarStep θ θ')^[k] lam₀)) ∧
      ConvergesSuperlinearly (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar ∧
      ((∃ K, ∃ U ∈ 𝓝[Icc lmin lmax] lamStar, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar 2)) ∧
    (∀ lam₀ ∈ Icc lmin lmax, ∀ lam₁ ∈ Icc lmin lmax, lam₀ < lam₁ → θ lam₀ < 0 → θ lam₁ < 0 →
      (∀ k, Secant.iterate θ lam₀ lam₁ k ∈ Icc lam₀ lamStar) ∧
      Monotone (Secant.iterate θ lam₀ lam₁) ∧
      Tendsto (Secant.iterate θ lam₀ lam₁) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - Secant.iterate θ lam₀ lam₁ (k + 1) ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - Secant.iterate θ lam₀ lam₁ k)) ∧
      ConvergesSuperlinearly (Secant.iterate θ lam₀ lam₁) lamStar) := by
  have hcont : ContinuousWithinAt θ' (Icc lmin lmax) lamStar := hd' lamStar hstar
  refine ⟨fun lam₀ h₀ hθ₀ => ?_, fun lam₀ h₀ lam₁ h₁ h01 hθ₀ hθ₁ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      Newton.monotone_scalarStep_iterate_of_concaveOn hc hm hd hstar hroot hθ' h₀ hθ₀
    exact ⟨h1, h2, h3, h4, h5, h6 hcont, h7⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      Newton.monotone_secant_iterate_of_concaveOn hc hm hd hstar hroot hθ' h₀ h₁ h01 hθ₀ hθ₁
    exact ⟨h1, h2, h3, h4, h5, h6 hcont⟩

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Lemma B.8.2** of [cartis2022evaluation] (monotonicity of the transformed secular Newton step).
Let $H \in \mathbb{R}^{n \times n}$ be symmetric, let $M \in \mathbb{R}^{n \times n}$ be
positive definite, and let $g \in \mathbb{R}^n$ with $g \neq 0$. Let
$\pi(\lambda) = \|s(\lambda)\|_M^2$ be the secular function, where
$s(\lambda) = -(H + \lambda M)^{-1} g$, let $\lambda_c > \lambda_s$, where
$\lambda_s = \max(0, -\lambda_1)$ and $\lambda_1$ is the leftmost eigenvalue of the pencil
$(H, M)$, and let $\Delta > 0$. For $\beta \neq 0$ let $\Psi_\beta(\lambda) =
\pi(\lambda)^\beta - \Delta^{2\beta}$, and let $\mu = \Delta^2/\pi(\lambda_c)$. Then for every
$\beta \neq 0$ the Newton step for $\Psi_\beta$ from $\lambda_c$ is (B.8.7)
$$-\frac{\Psi_\beta(\lambda_c)}{\Psi_\beta'(\lambda_c)} = \delta(\beta) :=
  -\frac{\pi(\lambda_c)}{\pi'(\lambda_c)} \cdot \frac{1 - \mu^\beta}{\beta},$$
and $\delta$ is nonincreasing on $\mathbb{R} \setminus \{0\}$.

**Reading.** The book assumes that $\lambda^*$ is the root of $\pi(\lambda) = \Delta^2$. This
hypothesis plays no role and is dropped. The hypothesis $g \neq 0$ is stated, since the Newton
step is defined only then.

The secular function is `CartisGouldToint.Chapter08.secularFn g H M`, and $\lambda_s$ is
`CartisGouldToint.Chapter08.lambdaS`. The derivatives are `deriv`. -/
theorem lemma_B_8_2 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc Δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hΔ : 0 < Δ) :
    (∀ β : ℝ, β ≠ 0 →
      -(secularFn g H M lamc ^ β - Δ ^ (2 * β)) /
          deriv (fun t => secularFn g H M t ^ β - Δ ^ (2 * β)) lamc =
        -secularFn g H M lamc / deriv (secularFn g H M) lamc *
          ((1 - (Δ ^ 2 / secularFn g H M lamc) ^ β) / β)) ∧
    AntitoneOn (fun β : ℝ => -secularFn g H M lamc / deriv (secularFn g H M) lamc *
      ((1 - (Δ ^ 2 / secularFn g H M lamc) ^ β) / β)) {β | β ≠ 0} := by
  have hc' := neg_leftmost_lt_of_lambdaS_lt hH hM hc
  have hg' := scaledGrad_ne_zero (hM := hM) hg
  rw [secularFn_eq_secular hM]
  have hpos := secular_pos (hH := isSymmetric_scaledOp hH) hg' hc'
  have hneg := deriv_secular_neg (hH := isSymmetric_scaledOp hH) hg' hc'
  refine ⟨fun β hβ => ?_, fun a ha b hb hab => ?_⟩
  · have := newtonCorrection_eq (hH := isSymmetric_scaledOp hH) hg' hc' hΔ hβ
    rwa [newtonFactor_of_ne_zero _ hβ] at this
  · have ha : a ≠ 0 := ha
    have hb : b ≠ 0 := hb
    have hanti := antitone_newtonFactor (div_pos (pow_pos hΔ 2) hpos) hab
    rw [newtonFactor_of_ne_zero _ ha, newtonFactor_of_ne_zero _ hb] at hanti
    exact mul_le_mul_of_nonneg_left hanti (div_nonneg_of_nonpos (neg_nonpos.2 hpos.le) hneg.le)

end CartisGouldToint.AppendixB
