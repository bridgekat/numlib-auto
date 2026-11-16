/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson and Han, Section 12.6: Iteration methods for the discretized equations

This module formalizes Section 12.6 of [han2009theoretical]. The linear systems that the methods of
Chapter 12 produce are large and dense, so they are solved by residual correction instead of
elimination. Section 12.6.2 gives the two-grid iteration for the Nyström method: the residual of the
fine equation $(\lambda - K_n) u_n = f$ is corrected with the inverse of the coarse operator
$\lambda - K_m$, and this coarse inverse is the only inverse that the method forms. One step
multiplies the error by the operator $M_{m,n} = \lambda^{-1} (\lambda - K_m)^{-1} (K_n - K_m) K_n$
of (12.6.28). Theorem 12.6.1 shows that $\|M_{m,n}\| < 1$ for all large $m$ and all $n \ge m$, so
the iteration converges. Example 12.6.2 is a test equation with the kernel $k_\gamma$ of (12.6.43),
whose eigenvalues and eigenfunctions (12.6.44) are known in closed form.

The two-grid iteration and its error operator are the backbone definitions in
`Numlib.IntegralEquations.SecondKind`. The convergence proof uses the collectively compact framework
of Section 12.4 (`NumlibSurface.AtkinsonHan.Chapter12.Section04`). The spectrum of $k_\gamma$
follows from the Poisson integral formula of Mathlib.

## Main definitions

* (12.6.20)–(12.6.22), `AtkinsonHan.Chapter12.twoGridStep`: one step $u \mapsto u + \lambda^{-1}
  (r + (\lambda - K_m)^{-1} K_n r)$ of the two-grid iteration, with the residual
  $r = f - (\lambda - K_n) u$.
* (12.6.28), `AtkinsonHan.Chapter12.twoGridOperator`: the iteration operator $M_{m,n} = \lambda^{-1}
  (\lambda - K_m)^{-1} (K_n - K_m) K_n$.
* (12.6.43), `AtkinsonHan.Chapter12.periodicPoissonKernel`: the kernel $k_\gamma(\tau) = (1 -
  \gamma^2) / (1 + \gamma^2 - 2 \gamma \cos(2 \pi \tau))$.

## Main results

* (12.6.20)–(12.6.22), `AtkinsonHan.Chapter12.equation_12_6_20`: the residual and the update of one
  two-grid step, written out.
* (12.6.27), `AtkinsonHan.Chapter12.equation_12_6_27`: one step multiplies the error by $M_{m,n}$,
  so the error after $\kappa$ steps is at most $\|M_{m,n}\|^\kappa$ times the initial error.
* Theorem 12.6.1, `AtkinsonHan.Chapter12.theorem_12_6_1`: for a collectively compact, pointwise
  convergent family, $\|M_{m,n}\| < 1$ for all large $m$ and all $n \ge m$, and the two-grid
  iterates converge.
* Example 12.6.2, `AtkinsonHan.Chapter12.example_12_6_2`: the spectrum (12.6.44) of the integral
  operator with kernel $k_\gamma(x + y)$.

## Conventions

* The scalar $\lambda$ of the book is the Lean variable `μ`, because `λ` is the lambda binder of
  Lean. This is the same convention as in Section 12.1.
* As in Section 12.4, the family $K_n$ of the book is `K n`, and its pointwise limit $K$ is `L`.
* The coarse operator $\lambda - K_m$ is given as an equivalence `e : X ≃L[𝕜] X` with
  `↑e = μ • 1 - K m`, so that `e.symm` is its inverse.

## Deviations from the source

* **Theorem 12.6.1** (generalization). The book states the theorem for the Nyström operators of
  Section 12.4 on $C(D)$. It is stated for every collectively compact family that converges
  pointwise. See `AtkinsonHan.Chapter12.theorem_12_6_1`.

## Not formalized

* **Section 12.6.3**, the translation of the operator iteration into the linear system
  $A_n u_n = f_n$. It is implementation, with no theorem content.
* **Section 12.6.4**, the operation count. It is implementation, with no theorem content.
* **Table 12.4** of Example 12.6.2, the iteration counts, errors and empirical convergence ratios
  $\tilde\nu$ at $\gamma = 0.8$. These are computed floating-point data.
* **The limit (12.6.48)**, the mesh independence principle. The book states it without proof.
-/

open Filter Topology

open scoped Real

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The two-grid iteration -/

/-- **Equations (12.6.20)–(12.6.22)** of [han2009theoretical]. Let $X$ be a normed space over
$\mathbb{K}$, let $\lambda \in \mathbb{K}$, let $K_n$ be a bounded operator on $X$, and let $e$
be an invertible bounded operator on $X$, which stands for the coarse operator $\lambda - K_m$.
For $f, u \in X$, one **two-grid step** for the fine equation $(\lambda - K_n) u = f$ forms the
residual $r = f - (\lambda - K_n) u$, the coarse correction $\delta = e^{-1} (K_n r)$, and the
new iterate $$u + \frac{1}{\lambda} (r + \delta).$$

The inverse $e^{-1}$ is the approximate inverse $C_n$ of the residual correction method
(12.6.5)–(12.6.6), and it is the only inverse that the method forms. The definition is
`SecondKind.twoGridStep`. It does not require `↑e = μ • 1 - K m`; the theorems that use it add
this hypothesis. -/
noncomputable abbrev twoGridStep (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) : X :=
  SecondKind.twoGridStep μ e Kn f u

/-- **Equations (12.6.20)–(12.6.22)** of [han2009theoretical]. Let $\lambda \in \mathbb{K}$, let
$K_n$ be a bounded operator and let $e$ be an invertible bounded operator on $X$. For
$f, u \in X$, the residual of the fine equation at $u$ is $$r = f - (\lambda - K_n) u,$$ and the
two-grid step `AtkinsonHan.Chapter12.twoGridStep` maps $u$ to $$u + \lambda^{-1} \bigl(r +
e^{-1} (K_n r)\bigr).$$

The residual is `SecondKind.residual`. -/
theorem equation_12_6_20 (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) :
    SecondKind.residual μ Kn f u = f - (μ • 1 - Kn : X →L[𝕜] X) u ∧
      twoGridStep μ e Kn f u = u + μ⁻¹ • (SecondKind.residual μ Kn f u
        + e.symm (Kn (SecondKind.residual μ Kn f u))) :=
  ⟨rfl, rfl⟩

/-- **Equation (12.6.28)** of [han2009theoretical]. Let $\lambda \in \mathbb{K}$, let $K_m, K_n$ be
bounded operators and let $e$ be an invertible bounded operator on $X$, which stands for
$\lambda - K_m$. The **iteration operator** of the two-grid method is $$M_{m,n} =
\frac{1}{\lambda} \, e^{-1} (K_n - K_m) K_n.$$

The factor $K_n - K_m$ appears composed with $K_n$. Collective compactness makes this product
small, although $\|K_n - K_m\|$ need not tend to zero. The definition is
`SecondKind.twoGridOperator`. -/
noncomputable abbrev twoGridOperator (μ : 𝕜) (e : X ≃L[𝕜] X) (Km Kn : X →L[𝕜] X) : X →L[𝕜] X :=
  SecondKind.twoGridOperator μ e Km Kn

/-- **Equation (12.6.27)** of [han2009theoretical]. Let $\lambda \neq 0$, let $K_m, K_n$ be bounded
operators on $X$, and let $e$ be an invertible bounded operator with $e = \lambda - K_m$. Let
$u^* \in X$ solve the fine equation $(\lambda - K_n) u^* = f$, and let $u \in X$. Then one
two-grid step multiplies the error by $M_{m,n}$: $$u^* - u^{(1)} = M_{m,n} (u^* - u),$$ where
$u^{(1)}$ is the two-grid step from $u$. Hence, for every $\kappa \ge 0$, the $\kappa$-th
iterate $u^{(\kappa)}$ satisfies $$\|u^* - u^{(\kappa)}\| \le \|M_{m,n}\|^\kappa \, \|u^* -
u\|.$$

The identity is algebra: it uses no compactness, no completeness and no bound on $M_{m,n}$. The
book writes the solution of the fine equation as $u_n$; it is `ustar` here. -/
theorem equation_12_6_27 {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u : X) :
    ustar - twoGridStep μ e Kn f u = twoGridOperator μ e Km Kn (ustar - u) ∧
      ∀ k : ℕ, ‖ustar - (twoGridStep μ e Kn f)^[k] u‖ ≤
        ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u‖ :=
  ⟨SecondKind.twoGrid_error_eq hμ he hstar u,
    SecondKind.norm_sub_twoGridStep_iterate_le hμ he hstar u⟩

/-! ### Convergence -/

variable {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}

/-- **Theorem 12.6.1** of [han2009theoretical]. Let $X$ be a Banach space, let $\{K_n\}$ be a
collectively compact family of bounded operators on $X$ that converges pointwise to $K$, and let
$\lambda \neq 0$ with $\lambda - K$ invertible. Then for every sufficiently large coarse index
$m$ the operator $\lambda - K_m$ is invertible, and for every fine index $n \ge m$:
$$\|M_{m,n}\| < 1,$$ and for every $f \in X$, every solution $u_n$ of $(\lambda - K_n) u_n = f$
and every starting point $u^{(0)}$, the two-grid iterates $u^{(\kappa)}$ converge to $u_n$ as
$\kappa \to \infty$.

**Generalization.** The book states the theorem for the Nyström operators of Section 12.4 on
$C(D)$. The proof uses only the assumptions A1–A3, which are
`AtkinsonHan.Chapter12.IsCollectivelyCompactFamily`, so the theorem is stated for every such
family, and the Nyström case is an instance.

The hypothesis `IsCollectivelyCompactFamily K L` gives the collective compactness and the
pointwise convergence, and the limit $K$ is the Lean variable `L`. The equivalence `e` with
`↑e = μ • 1 - L` gives the invertibility of $\lambda - K$.
The equivalence `em` gives the invertibility of $\lambda - K_m$. Both indices
have to be large, a fact that the book's "$n, m \to \infty$" hides: $(K_n - K_m) K_n$ splits
into $(K_n - K) K_n$, which `AtkinsonHan.Chapter12.lemma_12_4_7_d` makes small for large $n$,
and $(K - K_m) K_n$, which must be small uniformly in $n$; the second bound is
`SecondKind.eventually_forall_opNorm_sub_comp_lt`. The convergence is geometric, by
`AtkinsonHan.Chapter12.equation_12_6_27`. -/
theorem theorem_12_6_1 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    (h : IsCollectivelyCompactFamily K L) {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∀ᶠ m in atTop, ∃ em : X ≃L[𝕜] X, (em : X →L[𝕜] X) = μ • 1 - K m ∧
      ∀ n ≥ m, ‖twoGridOperator μ em (K m) (K n)‖ < 1 ∧
        ∀ f un : X, (μ • 1 - K n : X →L[𝕜] X) un = f → ∀ u₀ : X,
          Tendsto (fun k => (twoGridStep μ em (K n) f)^[k] u₀) atTop (𝓝 un) := by
  filter_upwards [SecondKind.eventually_norm_twoGridOperator_lt_one hμ h.isCollectivelyCompact
    h.tendsto he] with m hm
  obtain ⟨em, hem, hlt⟩ := hm
  exact ⟨em, hem, fun n hn =>
    ⟨hlt n hn, fun f un hun u₀ => SecondKind.tendsto_twoGridIterate hμ hem (hlt n hn) hun u₀⟩⟩

section Poisson

open Complex InnerProductSpace Metric

variable {γ : ℝ}

private theorem poissonKernel_circleMap (γ θ : ℝ) (hγ0 : 0 ≤ γ) :
    poissonKernel 0 (γ : ℂ) (circleMap 0 1 θ)
      = (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [poissonKernel_def, hz]
  have h1 : ‖Complex.exp (θ * Complex.I) - 0‖ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖(γ : ℂ) - 0‖ = γ := by simp [abs_of_nonneg hγ0]
  have h3 : ‖Complex.exp (θ * Complex.I) - 0 - ((γ : ℂ) - 0)‖ ^ 2
      = 1 + γ ^ 2 - 2 * γ * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h1, h2, h3]
  norm_num

private theorem circleMap_pow_re (j : ℕ) (θ : ℝ) :
    ((circleMap 0 1 θ) ^ j).re = Real.cos (j * θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [hz, ← Complex.exp_nat_mul,
    show (j : ℂ) * ((θ : ℂ) * Complex.I) = ((j * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

private theorem circleMap_pow_im (j : ℕ) (θ : ℝ) :
    ((circleMap 0 1 θ) ^ j).im = Real.sin (j * θ) := by
  have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
  rw [hz, ← Complex.exp_nat_mul,
    show (j : ℂ) * ((θ : ℂ) * Complex.I) = ((j * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im]

private theorem integral_poisson_cos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ))
      = 2 * π * γ ^ j := by
  have hw : (γ : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [Complex.norm_real, abs_of_nonneg hγ0, hγ1]
  have hana : ∀ x : ℂ, AnalyticAt ℂ (fun z : ℂ => z ^ j) x := fun _ =>
    AnalyticAt.pow analyticAt_id j
  have hf : HarmonicOnNhd (fun z : ℂ => (z ^ j).re) (closedBall (0 : ℂ) 1) := fun x _ =>
    AnalyticAt.harmonicAt_re (hana x)
  have key := hf.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at key
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      (poissonKernel 0 (γ : ℂ) • fun z : ℂ => (z ^ j).re) (circleMap 0 1 θ))
      = ∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [poissonKernel_circleMap γ θ hγ0, circleMap_pow_re]
  rw [hint] at key
  rw [show ((γ : ℂ) ^ j).re = γ ^ j by rw [← Complex.ofReal_pow, Complex.ofReal_re],
    smul_eq_mul] at key
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have h : (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos (j * θ))
      = (2 * π) * γ ^ j := by rw [key]
  rwa [← mul_assoc, mul_inv_cancel₀ h2π, one_mul] at h

private theorem integral_poisson_sin (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ)) = 0 := by
  have hw : (γ : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [Complex.norm_real, abs_of_nonneg hγ0, hγ1]
  have hana : ∀ x : ℂ, AnalyticAt ℂ (fun z : ℂ => z ^ j) x := fun _ =>
    AnalyticAt.pow analyticAt_id j
  have hf : HarmonicOnNhd (fun z : ℂ => (z ^ j).im) (closedBall (0 : ℂ) 1) := fun x _ =>
    AnalyticAt.harmonicAt_im (hana x)
  have key := hf.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at key
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      (poissonKernel 0 (γ : ℂ) • fun z : ℂ => (z ^ j).im) (circleMap 0 1 θ))
      = ∫ θ in (0 : ℝ)..(2 * π),
        (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [poissonKernel_circleMap γ θ hγ0, circleMap_pow_im]
  rw [hint] at key
  rw [show ((γ : ℂ) ^ j).im = 0 by rw [← Complex.ofReal_pow, Complex.ofReal_im],
    smul_eq_mul] at key
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have h : (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin (j * θ))
      = (2 * π) * 0 := by rw [key]
  rwa [← mul_assoc, mul_inv_cancel₀ h2π, one_mul, mul_zero] at h

/-- **Equation (12.6.43)** of [han2009theoretical]. For real $\gamma$ and $\tau$, the **kernel**
$k_\gamma$ of Example 12.6.2 is $$k_\gamma(\tau) = \frac{1 - \gamma^2}{1 + \gamma^2 - 2 \gamma
\cos(2 \pi \tau)}.$$ It is the Poisson kernel of the unit disk, read as a $1$-periodic function
of the parameter.

The book takes $0 \le \gamma < 1$. The definition is made for every real $\gamma$, and the
lemmas below add the hypothesis $0 \le \gamma < 1$; where the denominator vanishes, Lean's
division gives the value $0$. The book also writes $k_\gamma$ as its Fourier series
$1 + 2 \sum_j \gamma^j \cos(2 j \pi \tau)$. This expansion is not formalized, because the
eigenvalue relations (12.6.44) follow from the Poisson integral formula directly. The equation
(12.6.43) with this kernel is a reformulation of the Dirichlet problem for Laplace's equation on
an elliptical region, which is why its spectrum is known in closed form. -/
noncomputable def periodicPoissonKernel (γ τ : ℝ) : ℝ :=
  (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))

/-- For $0 \le \gamma < 1$ and every real $\tau$, the denominator of the kernel $k_\gamma$ of
(12.6.43) is positive: $$1 + \gamma^2 - 2 \gamma \cos(2 \pi \tau) > 0.$$

The proof writes the denominator as $(1 - \gamma)^2 + 2 \gamma (1 - \cos(2 \pi \tau)) \ge (1 -
\gamma)^2 > 0$. -/
theorem periodicPoissonKernel_denom_pos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (τ : ℝ) :
    0 < 1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ) := by
  nlinarith [mul_nonneg hγ0 (sub_nonneg.2 (Real.cos_le_one (2 * π * τ))),
    mul_pos (sub_pos.2 hγ1) (sub_pos.2 hγ1)]

/-- For $0 \le \gamma < 1$, the kernel $k_\gamma$ of (12.6.43) is continuous on $\mathbb{R}$,
because its denominator is positive. -/
theorem continuous_periodicPoissonKernel (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Continuous (periodicPoissonKernel γ) :=
  continuous_const.div (by fun_prop) fun τ => (periodicPoissonKernel_denom_pos hγ0 hγ1 τ).ne'

/-- For every real $\gamma$, the kernel $k_\gamma$ of (12.6.43) has period $1$:
$k_\gamma(\tau + 1) = k_\gamma(\tau)$ for all $\tau$. This lets the operator of Example 12.6.2
be read on the Fourier modes of the interval $[0, 1]$. -/
theorem periodic_periodicPoissonKernel (γ : ℝ) :
    Function.Periodic (periodicPoissonKernel γ) 1 := by
  intro τ
  rw [periodicPoissonKernel, periodicPoissonKernel,
    show 2 * π * (τ + 1) = 2 * π * τ + 2 * π by ring, Real.cos_add_two_pi]

/-- For $0 \le \gamma < 1$ and $j \in \mathbb{N}$, the $j$-th cosine coefficient of the kernel
$k_\gamma$ of (12.6.43) is $\gamma^j$: $$\int_0^1 k_\gamma(\tau) \cos(2 j \pi \tau) \, d\tau =
\gamma^j.$$

This is the Poisson integral formula, Mathlib's
`HarmonicOnNhd.circleAverage_poissonKernel_smul`, for the harmonic function
$z \mapsto \operatorname{Re}(z^j)$ at the interior point $\gamma$, rescaled from $[0, 2\pi]$ to
$[0, 1]$. -/
theorem integral_periodicPoissonKernel_mul_cos (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ)) = γ ^ j := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hcomp : (∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
        * Real.cos ((j : ℝ) * (2 * π * τ)))
      = (2 * π)⁻¹ • ∫ θ in (2 * π * 0)..(2 * π * 1),
          (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos ((j : ℝ) * θ) :=
    intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.cos ((j : ℝ) * θ)) h2π
  rw [mul_zero, mul_one, integral_poisson_cos hγ0 hγ1 j, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ h2π, one_mul] at hcomp
  calc (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))
      = ∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
          * Real.cos ((j : ℝ) * (2 * π * τ)) :=
        intervalIntegral.integral_congr fun τ _ => by
          rw [periodicPoissonKernel, show (j : ℝ) * (2 * π * τ) = 2 * j * π * τ by ring]
    _ = γ ^ j := hcomp

/-- For $0 \le \gamma < 1$ and $j \in \mathbb{N}$, the $j$-th sine coefficient of the kernel
$k_\gamma$ of (12.6.43) vanishes: $$\int_0^1 k_\gamma(\tau) \sin(2 j \pi \tau) \, d\tau = 0.$$

This is the Poisson integral formula for $z \mapsto \operatorname{Im}(z^j)$, whose value at the
real point $\gamma$ is zero. -/
theorem integral_periodicPoissonKernel_mul_sin (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) :
    (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ)) = 0 := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hcomp : (∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
        * Real.sin ((j : ℝ) * (2 * π * τ)))
      = (2 * π)⁻¹ • ∫ θ in (2 * π * 0)..(2 * π * 1),
          (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin ((j : ℝ) * θ) :=
    intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos θ) * Real.sin ((j : ℝ) * θ)) h2π
  rw [mul_zero, mul_one, integral_poisson_sin hγ0 hγ1 j, smul_eq_mul, mul_zero] at hcomp
  calc (∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))
      = ∫ τ in (0 : ℝ)..1, (1 - γ ^ 2) / (1 + γ ^ 2 - 2 * γ * Real.cos (2 * π * τ))
          * Real.sin ((j : ℝ) * (2 * π * τ)) :=
        intervalIntegral.integral_congr fun τ _ => by
          rw [periodicPoissonKernel, show (j : ℝ) * (2 * π * τ) = 2 * j * π * τ by ring]
    _ = 0 := hcomp

/-- **Example 12.6.2** of [han2009theoretical], equation (12.6.44). Let $0 \le \gamma < 1$ and let
$K$ be the integral operator of (12.6.43), $$K u(x) = \int_0^1 k_\gamma(x + y) \, u(y) \, dy.$$
Then for every $j \in \mathbb{N}$ and every real $x$, $$K \bigl[\cos(2 j \pi \cdot)\bigr](x) =
\gamma^j \cos(2 j \pi x), \qquad K \bigl[\sin(2 j \pi \cdot)\bigr](x) = -\gamma^j \sin(2 j \pi
x).$$ So $\cos(2 j \pi x)$, $j = 0, 1, 2, \dots$, are eigenfunctions with eigenvalues
$\gamma^j$, and $\sin(2 j \pi x)$, $j = 1, 2, \dots$, are eigenfunctions with eigenvalues
$-\gamma^j$. This makes the equation a test problem: the exact solution of $(\lambda - K) u = f$
is known for every trigonometric $f$, and $\lambda$ can be placed anywhere relative to the
spectrum.

The two identities are stated for every $j \in \mathbb{N}$; the case $j = 0$ of the sine
identity is $0 = 0$. The operator is not formed as a Lean operator: the statement is the two
integral identities. The proof uses the periodicity of $k_\gamma$ to absorb the shift $x + y$,
and the addition formulas to split the integral into the cosine and sine coefficients of
$k_\gamma$. Table 12.4 of the example, with the measured iteration counts and error reductions
at $\gamma = 0.8$, is not formalized; the convergence it shows is
`AtkinsonHan.Chapter12.theorem_12_6_1`. -/
theorem example_12_6_2 (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (j : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * y))
        = γ ^ j * Real.cos (2 * j * π * x) ∧
      (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * y))
        = -(γ ^ j) * Real.sin (2 * j * π * x) := by
  have hcont := continuous_periodicPoissonKernel hγ0 hγ1
  have hper := periodic_periodicPoissonKernel γ
  have hcos : Continuous fun τ : ℝ => periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ) :=
    hcont.mul (by fun_prop)
  have hsin : Continuous fun τ : ℝ => periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ) :=
    hcont.mul (by fun_prop)
  have shift : ∀ g : ℝ → ℝ, Function.Periodic g 1 →
      (∫ y in (0 : ℝ)..1, g (x + y)) = ∫ τ in (0 : ℝ)..1, g τ := by
    intro g hg
    rw [intervalIntegral.integral_comp_add_left g x, add_zero]
    have h := hg.intervalIntegral_add_eq x 0
    rwa [zero_add] at h
  constructor
  · have hg : Function.Periodic
        (fun τ : ℝ => periodicPoissonKernel γ τ * Real.cos (2 * j * π * (τ - x))) 1 := fun τ => by
      simp only [hper τ,
        show 2 * (j : ℝ) * π * (τ + 1 - x) = 2 * j * π * (τ - x) + j * (2 * π) by ring,
        Real.cos_add_nat_mul_two_pi]
    calc (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * y))
        = ∫ y in (0 : ℝ)..1,
            periodicPoissonKernel γ (x + y) * Real.cos (2 * j * π * (x + y - x)) :=
          intervalIntegral.integral_congr fun y _ => by rw [show x + y - x = y by ring]
      _ = ∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.cos (2 * j * π * (τ - x)) :=
          shift _ hg
      _ = ∫ τ in (0 : ℝ)..1,
            (Real.cos (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))
              + Real.sin (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))) :=
          intervalIntegral.integral_congr fun τ _ => by
            rw [show 2 * (j : ℝ) * π * (τ - x) = 2 * j * π * τ - 2 * j * π * x by ring,
              Real.cos_sub]
            ring
      _ = γ ^ j * Real.cos (2 * j * π * x) := by
          rw [intervalIntegral.integral_add ((hcos.const_mul _).intervalIntegrable 0 1)
              ((hsin.const_mul _).intervalIntegrable 0 1),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            integral_periodicPoissonKernel_mul_cos hγ0 hγ1 j,
            integral_periodicPoissonKernel_mul_sin hγ0 hγ1 j]
          ring
  · have hg : Function.Periodic
        (fun τ : ℝ => periodicPoissonKernel γ τ * Real.sin (2 * j * π * (τ - x))) 1 := fun τ => by
      simp only [hper τ,
        show 2 * (j : ℝ) * π * (τ + 1 - x) = 2 * j * π * (τ - x) + j * (2 * π) by ring,
        Real.sin_add_nat_mul_two_pi]
    calc (∫ y in (0 : ℝ)..1, periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * y))
        = ∫ y in (0 : ℝ)..1,
            periodicPoissonKernel γ (x + y) * Real.sin (2 * j * π * (x + y - x)) :=
          intervalIntegral.integral_congr fun y _ => by rw [show x + y - x = y by ring]
      _ = ∫ τ in (0 : ℝ)..1, periodicPoissonKernel γ τ * Real.sin (2 * j * π * (τ - x)) :=
          shift _ hg
      _ = ∫ τ in (0 : ℝ)..1,
            (Real.cos (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.sin (2 * j * π * τ))
              + -Real.sin (2 * j * π * x) *
                (periodicPoissonKernel γ τ * Real.cos (2 * j * π * τ))) :=
          intervalIntegral.integral_congr fun τ _ => by
            rw [show 2 * (j : ℝ) * π * (τ - x) = 2 * j * π * τ - 2 * j * π * x by ring,
              Real.sin_sub]
            ring
      _ = -(γ ^ j) * Real.sin (2 * j * π * x) := by
          rw [intervalIntegral.integral_add ((hsin.const_mul _).intervalIntegrable 0 1)
              ((hcos.const_mul _).intervalIntegrable 0 1),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            integral_periodicPoissonKernel_mul_cos hγ0 hγ1 j,
            integral_periodicPoissonKernel_mul_sin hγ0 hγ1 j]
          ring

end Poisson

end AtkinsonHan.Chapter12
