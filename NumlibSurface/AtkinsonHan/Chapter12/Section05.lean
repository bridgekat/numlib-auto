/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Numlib.Approximation.GradedMesh
import Numlib.IntegralEquations.ProductIntegration
import NumlibSurface.AtkinsonHan.Chapter12.Section01
import NumlibSurface.AtkinsonHan.Chapter12.Section04

/-!
# Atkinson and Han, Section 12.5: Product integration

This module formalizes Section 12.5 of [han2009theoretical]. The equation is $\lambda u - K u = f$
with a weakly singular kernel $k(x, y) = l(x, y) g(x, y)$, where $l$ is continuous and $g$ is
singular but satisfies the two conditions (12.5.15) and (12.5.16). The product integration method
replaces the smooth factor $y \mapsto l(x, y) u(y)$ of the integrand by its piecewise polynomial
interpolant $[l(x, \cdot) u(\cdot)]_n$ and integrates the singular factor exactly: $$K_n u(x) = \int
[l(x, \cdot) u(\cdot)]_n(y) \, g(x, y)\, dy.$$ The family $\{K_n\}$ satisfies assumptions A1–A3 of
Section 12.4, so the theory of collectively compact operators gives $\|u - u_n\|_\infty \le c \|K
u - K_n u\|_\infty$ (Theorem 12.5.1). Piecewise linear interpolation then gives the rate $O(h^2)$
for a smooth solution (Example 12.5.2), and interpolation on a graded mesh restores the rate
$O(n^{-(m+1)})$ for a solution with endpoint singularities (Lemma 12.5.5 and Theorem 12.5.6).

The operator $K_n$, for an arbitrary bounded operator in place of the interpolation, is
`IntegralOperator.productCLM` of `Numlib.IntegralEquations.ProductIntegration`. The conditions on
$g$ are `IntegralOperator.IsAdmissibleKernel` of `Numlib.IntegralEquations.WeaklySingular`, and the
graded meshes of §12.5.3 and §12.5.4 are in `Numlib.Approximation.GradedMesh`. Each result of this
module specializes one of these.

## Main results

* `AtkinsonHan.Chapter12.isCollectivelyCompactFamily_productCLM`: the product integration operators
  satisfy A1–A3 of §12.4.3; A2 is Exercise 12.5.1, and A3 is the compactness part of the proof of
  Theorem 12.5.1.
* Theorem 12.5.1, `AtkinsonHan.Chapter12.theorem_12_5_1`: for large $n$ the approximating equations
  are uniquely solvable with uniformly bounded inverses, and $\|u - u_n\|_\infty \le c \|K u - K_n
  u\|_\infty$, which is (12.5.17).
* Example 12.5.2, `AtkinsonHan.Chapter12.example_12_5_2`: the rate $\|u - u_n\|_\infty \le c (h^2/8)
  \max |\partial_y^2 (l u)|$ of the product trapezoidal rule, (12.5.18).
* Example 12.5.3, `AtkinsonHan.Chapter12.example_12_5_3`: the factorization of the kernel of
  (12.5.21) that underlies the splitting (12.5.22), and the exact solution
  $u \equiv 1/(1 + \pi \log 2)$.
* Lemma 12.5.5, `AtkinsonHan.Chapter12.lemma_12_5_5`: the interpolation error
  $\|u - P_n u\|_\infty \le C n^{-(m+1)}$ of (12.5.35) on the graded mesh $x_j = (j/n)^q$ of
  (12.5.30), for a function of type $(\gamma, m + 1)$ and $q \ge (m + 1)/\gamma$.
* Theorem 12.5.6, `AtkinsonHan.Chapter12.theorem_12_5_6`: the convergence
  $\|u - u_n\|_\infty \le c n^{-(m+1)}$ of product integration on a mesh graded towards both
  endpoints, (12.5.41).

## Conventions

* The scalar $\lambda$ of the source is `μ` (in Theorem 12.5.6, `lam`), because `λ` is the Lean
  lambda binder, and the measure is `ν`.
* The interval $[a, b]$ carries Lebesgue measure `IntegralOperator.iccMeasure a b`.
* The kernel $k = l g$ is `fun p => g p * l p`, admissible by
  `IntegralOperator.IsAdmissibleKernel.mul_continuousMap`, and $K$ is
  `IntegralOperator.admissibleKernelCLM` of it. The function $y \mapsto l(x, y) u(y)$ is
  `IntegralOperator.prodFactor l x u`.

## Implementation notes

* The interpolation $[\cdot]_n$ is any sequence of bounded operators $P_n$ on $C(X)$ with uniformly
  bounded norms that converges pointwise to the identity. The piecewise linear interpolation of the
  source is `piecewiseLinearInterpCLM`, whose norm is $1$.
* `IntegralOperator.productCLM` is not a Nyström operator, because the weights
  $\int g(x, y) \varphi_j(y)\, dy$ depend on $x$.
* Weakly singular kernels of the forms in Theorem 12.5.4 are admissible:
  `IntegralOperator.isAdmissibleKernel_abs_sub_rpow` treats $|x - y|^{-\gamma}$ with
  $0 < \gamma < 1$ on an interval, and `IntegralOperator.isAdmissibleKernel_of_abs_le_rpow` with
  `abs_log_le_two_mul_rpow` treats $\log |x - y|$.
* The hypothesis of `AtkinsonHan.Chapter12.theorem_12_5_6` is that $y \mapsto l(x, y) u(y)$ is of
  type $(\gamma, m + 1)$ uniformly in $x$. This is the only consequence of Theorem 12.5.4 that the
  chapter uses, and it would follow from the regularity of $u$ by the Leibniz rule and the
  smoothness of $l$.

## Deviations from the source

* **Theorem 12.5.1** (generalization). The source takes for $[\cdot]_n$ piecewise polynomial
  interpolation on $[a, b]$. The statement holds for every uniformly bounded sequence of operators
  that converges pointwise to the identity, on every compact metric space with a measure on its
  Borel sets. See `AtkinsonHan.Chapter12.theorem_12_5_1`.
* **Example 12.5.2** (generalization). The product trapezoidal estimate uses any sequence of
  partitions whose mesh size tends to zero, including the source's equally spaced meshes.
* **Lemma 12.5.5 and Theorem 12.5.6** (restriction). The interpolation nodes include both ends
  of each panel, so the interpolant is continuous. Lemma 12.5.5 gives the uniform error estimate
  (12.5.35). The book also allows interior-only nodes and gives the $L^p$ estimate (12.5.37).
* **Theorem 12.5.6** (reading). The source applies Theorem 12.5.4 to obtain the regularity of the
  solution. The statement assumes the regularity that the proof uses: each function
  $y \mapsto l(x, y) u(y)$ is of type $(\gamma, m + 1)$ at both endpoints, with constants
  independent of $x$, and $0 < \gamma < 1$. See `AtkinsonHan.Chapter12.theorem_12_5_6`.

## Not formalized

* **Theorem 12.5.4** (regularity of the solution of a weakly singular equation). For (12.5.26) with
  $g_\gamma(u) = u^{\gamma - 1}$, $0 < \gamma < 1$, or $g_\gamma(u) = \log |u|$, $\gamma = 1$, a
  $C^{k+1}$ coefficient $l$ and data $f$ of the stated class, the solution satisfies
  $u \in C^{(0,\gamma)}[a, b] \cap C^k(a, b)$, with $(x - a)^i (b - x)^i u^{(i)}(x) \in
  C^{(0,\gamma)}[a, b]$ vanishing at the endpoints and $|u^{(i)}(x)| \le c_i (x - a)^{\gamma - i}$
  near $a$. The source cites Schneider and gives no proof. Two pieces are missing. The first is
  differentiation under a weakly singular integral sign with a moving singularity: the derivative of
  $\int_a^b l(x, y) g_\gamma(x - y) u(y)\, dy$ is not the integral of the differentiated integrand,
  because $|x - y|^{\gamma - 2}$ is not integrable, so
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` does not apply, and the
  classical substitution $y = x + s$ with the singularity split off is not available. The second is
  the Hölder class $C^{(0,1)}[a, b]$ with modulus $|x - \xi| \log |B / (x - \xi)|$, $B > b - a$,
  needed for $\gamma = 1$; `AtkinsonHan.Chapter03.HolderClass` covers only exponents
  $0 < \beta < 1$.
* **§12.5.2**, the generalizations to kernels that are not of the form $l g$.
* **The numerical part of Example 12.5.3.** Table 12.3 contains measured errors of the product
  trapezoidal and product Simpson rules for (12.5.21). The remark that the first splitting
  $l = |x - y|^{1/2} \log |\cos x - \cos y|$ is continuous but not differentiable concerns a
  function that the example replaces by the splitting (12.5.22).
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

/-! ### The product integration operator -/

section ProductIntegration

open IntegralOperator MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {g : X × X → ℝ}

/-- Let $X$ be a compact metric space with a measure $\nu$ on its Borel sets, let $g$ be an
admissible kernel, and let $l$ be a continuous kernel on $X \times X$. Let $P_n$ be bounded
operators on $C(X)$ with $\|P_n\| \le C_P$ for all $n$ and $P_n v \to v$ for every $v$. Then the
product integration operators $$K_n u(x) = \int g(x, y) \, P_n\big(l(x, \cdot)
u(\cdot)\big)(y)\, d\nu(y)$$ satisfy assumptions A1–A3 of §12.4.3 with limit the integral
operator $K$ of the kernel $l g$. This is the core of the proof of Theorem 12.5.1 of
[han2009theoretical].

A1 is part of the type of the operators. A2 is `IntegralOperator.tendsto_productCLM`, which is
Exercise 12.5.1, and A3 is `IntegralOperator.isCollectivelyCompact_productCLM`, translated to
the form (12.4.53) by
`AtkinsonHan.Chapter12.isCollectivelyCompactFamily_of_isCollectivelyCompact`. The limit $K$ is
`productCLM hg l 1`, the case $P_n = I$.

**Reading.** Arbitrary strongly convergent uniformly bounded interpolation operators on a compact
measured metric space.
-/
theorem isCollectivelyCompactFamily_productCLM (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v)) :
    IsCollectivelyCompactFamily (fun n => productCLM hg l (P n)) (productCLM hg l 1) :=
  isCollectivelyCompactFamily_of_isCollectivelyCompact
    (isCollectivelyCompact_productCLM hg l hCp) fun v => tendsto_productCLM hg l hP v

end ProductIntegration

/-! ### Theorem 12.5.1 -/

section Theorem1

open IntegralOperator MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} {g : X × X → ℝ}

/-- **Theorem 12.5.1** of [han2009theoretical] (convergence of product integration). Let $X$ be a
compact metric space with a measure $\nu$ on its Borel sets, let $g$ satisfy the weak
singularity conditions (12.5.15) and (12.5.16), that is, let $g$ be an admissible kernel, let
$l$ be continuous, and let $K$ be the integral operator on $C(X)$ of the kernel $k = l g$. Let
$\lambda \neq 0$ be such that $\lambda - K$ is invertible. Let $P_n$ be bounded operators on
$C(X)$ with $\|P_n\| \le C_P$ for all $n$ and $P_n v \to v$ for every $v$, and let $K_n$ be the
product rule obtained by replacing $l(x, \cdot) u(\cdot)$ by $P_n (l(x, \cdot) u(\cdot))$. Then
there is a constant $c$ such that for all large $n$ the operator $\lambda - K_n$ is invertible
with $\|(\lambda - K_n)^{-1}\| \le c$, so the approximating equations are uniquely solvable, and
the solutions of $(\lambda - K) u = f$ and $(\lambda - K_n) u_n = f$ satisfy $$\|u -
u_n\|_\infty \le c \, \|K u - K_n u\|_\infty,$$ which is (12.5.17): the consistency error at the
exact solution.

**Generalization.** The source takes for $P_n$ piecewise polynomial interpolation on an
interval, such as the piecewise linear interpolation of (12.5.4). The statement allows any
uniformly bounded sequence of operators that converges pointwise to the identity, on any compact
metric space.

The conditions (12.5.15) and (12.5.16) are the conditions (A₂) and (A₁) of
`IntegralOperator.IsAdmissibleKernel`. The proof follows the source:
`AtkinsonHan.Chapter12.isCollectivelyCompactFamily_productCLM` verifies A1–A3, and
`AtkinsonHan.Chapter12.exists_norm_inverse_le_of_isCollectivelyCompactFamily` of §12.4.3, which
is Lemma 12.4.7 followed by Theorem 12.4.3, gives the rest. -/
theorem theorem_12_5_1 (hg : IsAdmissibleKernel ν g) (l : C(X × X, ℝ))
    {P : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ)} {Cp : ℝ} (hCp : ∀ n, ‖P n‖ ≤ Cp)
    (hP : ∀ v : C(X, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v))
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(X, ℝ) ≃L[ℝ] C(X, ℝ)}
    (he : (e : C(X, ℝ) →L[ℝ] C(X, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(X, ℝ) ≃L[ℝ] C(X, ℝ),
      (en : C(X, ℝ) →L[ℝ] C(X, ℝ)) = μ • 1 - productCLM hg l (P n) ∧
        ‖(en.symm : C(X, ℝ) →L[ℝ] C(X, ℝ))‖ ≤ c ∧
        ∀ f u un : C(X, ℝ),
          (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
            C(X, ℝ) →L[ℝ] C(X, ℝ)) u = f →
          (μ • 1 - productCLM hg l (P n) : C(X, ℝ) →L[ℝ] C(X, ℝ)) un = f →
          ‖u - un‖ ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
            - productCLM hg l (P n) u‖ := by
  have hone := productCLM_one hg l
  have hfam := isCollectivelyCompactFamily_productCLM hg l hCp hP
  rw [hone] at hfam
  exact exists_norm_inverse_le_of_isCollectivelyCompactFamily hμ hfam he

end Theorem1

/-! ### Example 12.5.2: the product trapezoidal rule -/

section Trapezoidal

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **Example 12.5.2** of [han2009theoretical] (the product trapezoidal rule, (12.5.18)). Let $g$ be
an admissible kernel on $[a, b]$, let $l$ be continuous, let $K$ be the integral operator of
$l g$, and let $\lambda \neq 0$ be such that $\lambda - K$ is invertible. For each $n$ let
$a = y_{n,0} < \dots < y_{n,N_n+1} = b$ be a partition whose subintervals have length at most
$h_n$, with $h_n \to 0$, and let $K_n$ be the product rule with piecewise linear interpolation
at the nodes. Then there is a constant $c$ such that for all large $n$:

* for every $f$ the equation $(\lambda - K_n) u_n = f$ has exactly one solution;
* if $(\lambda - K) u = f$, $(\lambda - K_n) u_n = f$, and for every $x$ the function
  $y \mapsto l(x, y) u(y)$ is the restriction of a $C^2$ function $G_x$ with $|G_x''| \le M_2$
  on $[a, b]$, then $$\|u - u_n\|_\infty \le c \, \frac{h_n^2}{8} M_2.$$

Theorem 12.5.1 applies, because the interpolation operators have norm $1$ and converge
pointwise. The interpolation error $\|z - P_n z\| \le h^2 \|z''\|/8$ is
`norm_sub_piecewiseLinearInterpCLM_le`, and
`IntegralOperator.norm_admissibleKernelCLM_sub_productCLM_le` turns it into a bound on the
consistency error $\|K u - K_n u\|$. The constant $c$ contains the uniform bound on
$\|(\lambda - K_n)^{-1}\|$ and the bound on $\int |g(x, y)|\, dy$.

**Reading.** Allows nonuniform meshes tending to zero and uses explicit derivative witnesses.
-/
theorem example_12_5_2 {g : Set.Icc a b × Set.Icc a b → ℝ}
    (hg : IsAdmissibleKernel (iccMeasure a b) g) (l : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) {μ : ℝ} (hμ : μ ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l)) :
    ∃ c : ℝ, ∀ᶠ n in atTop,
      (∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f) ∧
      ∀ (G : Set.Icc a b → ℝ → ℝ) (M₂ : ℝ) (f u un : C(Set.Icc a b, ℝ)),
        (∀ x, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (G x)) →
        (∀ x, ∀ t : Set.Icc a b, l (x, t) * u t = G x (t : ℝ)) →
        (∀ x, ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 (G x) t| ≤ M₂) →
        (μ • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
        (μ • 1 - productCLM hg l (piecewiseLinearInterpCLM (N n) (y n)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ c * (h n ^ 2 / 8 * M₂) := by
  classical
  set P : ℕ → C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
    fun n => piecewiseLinearInterpCLM (N n) (y n) with hPdef
  have hnormP : ∀ n, ‖P n‖ = 1 := fun n =>
    norm_piecewiseLinearInterpCLM ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩
  have hCp : ∀ n, ‖P n‖ ≤ 1 := fun n => le_of_eq (hnormP n)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ), Tendsto (fun n => P n v) atTop (𝓝 v) :=
    tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh
  obtain ⟨c, hc⟩ := theorem_12_5_1 hg l hCp hPconv hμ he
  refine ⟨c * rowBound (iccMeasure a b) g, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ := hn
  have hsolve : ∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (μ • 1 - productCLM hg l (P n) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f := fun f => by
    simpa only [← hencoe, ContinuousLinearEquiv.coe_coe] using en.bijective.existsUnique f
  refine ⟨hsolve, fun G M₂ f u un hG hGval hM₂ hu hun => ?_⟩
  -- the consistency error is the interpolation error of `l (x, ·) u (·)`, uniformly in `x`
  have hM0 : (0 : ℝ) ≤ h n ^ 2 / 8 * M₂ := by
    have h1 : (0 : ℝ) ≤ M₂ :=
      le_trans (abs_nonneg _) (hM₂ (y n 0) ((y n 0 : ℝ)) (y n 0).2)
    positivity
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖
      ≤ rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) :=
    norm_admissibleKernelCLM_sub_productCLM_le hg l (P n) u hM0 fun x =>
      norm_sub_piecewiseLinearInterpCLM_le ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩
        (hG x) (f := prodFactor l x u) (fun t => hGval x t) (hmesh n) (hM₂ x)
  calc ‖u - un‖
      ≤ c * ‖admissibleKernelCLM (hg.mul_continuousMap l) u - productCLM hg l (P n) u‖ :=
        herr f u un hu hun
    _ ≤ c * (rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂)) :=
        mul_le_mul_of_nonneg_left hcons (le_trans (norm_nonneg _) hennorm)
    _ = c * rowBound (iccMeasure a b) g * (h n ^ 2 / 8 * M₂) := by ring

end Trapezoidal

/-! ### Lemma 12.5.5: interpolation on a graded mesh -/

section GradedMesh

/-- **Lemma 12.5.5** of [han2009theoretical] (interpolation on a graded mesh). Let $0 < \gamma < 1$,
and let $u \in C[0, 1]$ be of type $(\gamma, m + 1)$: $u$ is the restriction of a function $U$
with $|U(s) - U(t)| \le H |s - t|^\gamma$ for $s, t \in [0, 1]$, $U$ is $C^{m+1}$ on
$(0, \infty)$, and $|U^{(m+1)}(s)| \le c\, s^{\gamma - (m+1)}$ for $s \in (0, 1]$. Let
$0 = \mu_0 < \mu_1 < \dots < \mu_m = 1$, and let $P_n$ be piecewise polynomial interpolation of
degree $m$ on the graded mesh $x_j = (j/n)^q$, $0 \le j \le n$, of (12.5.30), at the nodes
$x_j + \mu_i (x_{j+1} - x_j)$ of each panel, as in (12.5.31) and (12.5.32). If
$q \ge (m + 1)/\gamma$, then there is a constant $C$ with $$\|u - P_n u\|_\infty \le
\frac{C}{n^{m+1}} \qquad \text{for all } n,$$ which is (12.5.35).

The source states the lemma without proof and cites Rice and Atkinson. The statement is
`norm_sub_piecewisePolyInterpCLM_le_graded`. The Lean index $N$ counts $N + 1 = n$ panels, so
the bound reads $C / (N + 1)^{m+1}$.

**Reading.** Only the uniform bound is stated, with panel endpoints required as interpolation nodes.
-/
theorem lemma_12_5_5 {m : ℕ} {γ q H c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hq : ((m : ℝ) + 1) / γ ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {U : ℝ → ℝ} {u : C(Set.Icc (0 : ℝ) 1, ℝ)} (hu : ∀ t : Set.Icc (0 : ℝ) 1, u t = U ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |U s - U t| ≤ H * |s - t| ^ γ)
    (hUC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) U (Set.Ioi 0))
    (hUd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, |iteratedDeriv (m + 1) U s| ≤ c * s ^ (γ - ((m : ℝ) + 1)))
    {x : ℕ → ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ N, ∀ j ≤ N + 1, (x N j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ N, ∀ j ≤ N, ∀ i, (node N j i : ℝ)
      = (x N j : ℝ) + μ i * ((x N (j + 1) : ℝ) - (x N j : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖u - piecewisePolyInterpCLM N m (x N) (node N) u‖ ≤ C / ((N : ℝ) + 1) ^ (m + 1) :=
  norm_sub_piecewisePolyInterpCLM_le_graded hγ0 hγ1 hq hμ0 hμ1 hμmono hu hH hUC hUd hx hnode

end GradedMesh


/-! ### Theorem 12.5.6 -/

section Theorem6

open IntegralOperator MeasureTheory

/-- **Theorem 12.5.6** of [han2009theoretical] (convergence of product integration on a graded
mesh). Let $a < b$, $0 < \gamma < 1$, $m \in \mathbb{N}$ and $q \ge (m + 1)/\gamma$. Let $g$ be
an admissible kernel on $[a, b]$, let $l$ be continuous, let $K$ be the integral operator of
$l g$, let $\lambda \neq 0$ be such that $\lambda - K$ is invertible, and let
$(\lambda - K) u = f$. For $p \in \mathbb{N}$ let $n = 2(p + 1)$, and let the mesh be graded
towards both endpoints: $$x_j = a + \left(\frac{j}{p + 1}\right)^q \frac{b - a}{2}, \qquad
x_{n - j} = a + b - x_j, \qquad 0 \le j \le p + 1,$$ with the nodes
$x_j + \mu_i (x_{j+1} - x_j)$ on the left half and the reflected nodes
$x_j + (1 - \mu_{m-i})(x_{j+1} - x_j)$ on the right half, for fixed
$0 = \mu_0 < \dots < \mu_m = 1$. Let $K_n$ be the product rule (12.5.38) with piecewise
polynomial interpolation of degree $m$ on this mesh. Assume that for every $x$ the function
$y \mapsto l(x, y) u(y)$ is the restriction of a function $W_x$ with

* $|W_x(s) - W_x(t)| \le H |s - t|^\gamma$ for $s, t \in [a, b]$,
* $W_x$ of class $C^{m+1}$ on $(a, b)$,
* $|W_x^{(m+1)}(s)| \le c_R (s - a)^{\gamma - (m+1)}$ for $s \in (a, (a + b)/2]$ and
  $|W_x^{(m+1)}(s)| \le c_R (b - s)^{\gamma - (m+1)}$ for $s \in [(a + b)/2, b)$,

with $H$ and $c_R$ independent of $x$. Then there is a constant $C$ such that for all large $n$
the equation $(\lambda - K_n) u_n = h$ has exactly one solution for every $h$, and the solution
for $f$ satisfies $$\|u - u_n\|_\infty \le \frac{C}{n^{m+1}},$$ which is (12.5.41).

**Reading.** The source obtains the regularity of the functions $y \mapsto l(x, y) u(y)$ from
Theorem 12.5.4, which is not formalized. The statement assumes this regularity, which is what
the proof of the source uses, and covers only $0 < \gamma < 1$.

The proof follows the source. `AtkinsonHan.Chapter12.theorem_12_5_1` gives
$\|u - u_n\| \le c \|K u - K_n u\|$,
`IntegralOperator.norm_admissibleKernelCLM_sub_productCLM_le` bounds the consistency error by
the interpolation error of the functions $y \mapsto l(x, y) u(y)$, and
`norm_sub_piecewisePolyInterpCLM_le_gradedSym`, Lemma 12.5.5 on the two-sided mesh, bounds that
by $c n^{-(m+1)}$ uniformly in $x$. The mesh facts are `isPanelNodes_gradedSym`,
`sub_le_gradedSym` and `exists_isPanelLebesgueBound_of_affine`. In Lean the fractions $\mu_i$
are `ν`, the functions $W_x$ are `W`, and the operator has $2p + 2$ panels. -/
theorem theorem_12_5_6 {a b : ℝ} (hab : a < b) {m : ℕ} {γ q : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hq : ((m : ℝ) + 1) / γ ≤ q)
    {ν : Fin (m + 1) → ℝ} (hν0 : ν 0 = 0) (hν1 : ν (Fin.last m) = 1) (hνmono : StrictMono ν)
    {x : ℕ → ℕ → Set.Icc a b} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ p, ∀ j ≤ p + 1,
      (x p j : ℝ) = a + ((j : ℝ) / ((p + 1 : ℕ) : ℝ)) ^ q * ((b - a) / 2))
    (hxR : ∀ p, ∀ j ≤ p + 1, (x p (2 * (p + 1) - j) : ℝ) = a + b - (x p j : ℝ))
    (hnodeL : ∀ p, ∀ j < p + 1, ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + ν i * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    (hnodeR : ∀ p, ∀ j, p + 1 ≤ j → j ≤ 2 * p + 1 → ∀ i, (node p j i : ℝ)
      = (x p j : ℝ) + (1 - ν i.rev) * ((x p (j + 1) : ℝ) - (x p j : ℝ)))
    {g : Set.Icc a b × Set.Icc a b → ℝ} (hg : IsAdmissibleKernel (iccMeasure a b) g)
    (l : C(Set.Icc a b × Set.Icc a b, ℝ)) {lam : ℝ} (hlam : lam ≠ 0)
    {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l))
    {f u : C(Set.Icc a b, ℝ)}
    (hu : (lam • 1 - admissibleKernelCLM (hg.mul_continuousMap l) :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f)
    {W : Set.Icc a b → ℝ → ℝ} {H cR : ℝ}
    (hW : ∀ z : Set.Icc a b, ∀ t : Set.Icc a b, prodFactor l z u t = W z ((t : ℝ)))
    (hWH : ∀ z : Set.Icc a b, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      |W z s - W z t| ≤ H * |s - t| ^ γ)
    (hWC : ∀ z : Set.Icc a b, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (W z) (Set.Ioo a b))
    (hWL : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ioc a ((a + b) / 2),
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (s - a) ^ (γ - ((m : ℝ) + 1)))
    (hWR : ∀ z : Set.Icc a b, ∀ s ∈ Set.Ico ((a + b) / 2) b,
      |iteratedDeriv (m + 1) (W z) s| ≤ cR * (b - s) ^ (γ - ((m : ℝ) + 1))) :
    ∃ C : ℝ, ∀ᶠ p in atTop,
      (∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h) ∧
      ∀ un : C(Set.Icc a b, ℝ),
        (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
        ‖u - un‖ ≤ C / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  -- the nodes sit at fixed fractions of every panel — at the reference partition `ν` on the
  -- panels of the left half and at its reflection on those of the right — so a single Lebesgue
  -- bound, depending on `ν` alone, serves every `p`
  have hnodes : ∀ p : ℕ, IsPanelNodes (2 * p + 1) m (x p) (node p) := fun p =>
    isPanelNodes_gradedSym hab (Nat.succ_pos p) (by omega) hq1 hν0 hν1 hνmono (hxL p) (hxR p)
      (hnodeL p) (hnodeR p)
  have hinj : ∀ k : Fin 2, Function.Injective (![ν, fun i => 1 - ν i.rev] k) := by
    intro k
    fin_cases k
    · exact hνmono.injective
    · refine fun i i' hii => Fin.rev_injective (hνmono.injective ?_)
      have hii' : (1 : ℝ) - ν i.rev = 1 - ν i'.rev := hii
      linarith
  obtain ⟨Λ, hΛfam⟩ := exists_isPanelLebesgueBound_of_affine hinj
  have hΛb : ∀ p : ℕ, IsPanelLebesgueBound (2 * p + 1) m (x p) (node p) Λ := by
    intro p
    refine hΛfam (c := fun j => if j < p + 1 then 0 else 1) (hnodes p) fun j hj i => ?_
    by_cases hjr : j < p + 1
    · simp only [hjr, ↓reduceIte]
      exact hnodeL p j hjr i
    · simp only [hjr, ↓reduceIte]
      exact hnodeR p j (by omega) hj i
  -- the mesh tends to zero, so the projections converge pointwise
  have hmesh : ∀ p : ℕ, ∀ j ≤ 2 * p + 1,
      (x p (j + 1) : ℝ) - (x p j : ℝ) ≤ (b - a) / 2 * q / ((p : ℝ) + 1) := by
    intro p
    have h := sub_le_gradedSym (r := p + 1) (N := 2 * p + 1) hab (Nat.succ_pos p) (by omega) hq1
      (hxL p) (hxR p)
    rwa [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 by push_cast; ring] at h
  have htend : Tendsto (fun p : ℕ => (b - a) / 2 * q / ((p : ℝ) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hPconv : ∀ v : C(Set.Icc a b, ℝ),
      Tendsto (fun p => piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p) v) atTop (𝓝 v) :=
    fun v => tendsto_piecewisePolyInterpCLM (N := fun p => 2 * p + 1) hnodes hΛb hmesh htend v
  have hnormP : ∀ p : ℕ, ‖piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)‖ ≤ Λ := fun p =>
    norm_piecewisePolyInterpCLM_le (hnodes p) (hΛb p)
  -- Theorem 12.5.1
  obtain ⟨c₀, hc₀⟩ := theorem_12_5_1 hg l hnormP hPconv hlam he
  set Cst : ℝ := (1 + Λ) * H * ((b - a) / 2) ^ γ
    + cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hΛ0 : (0 : ℝ) ≤ Λ := (hΛb 0).nonneg (hnodes 0)
  have hSγ0 : (0 : ℝ) ≤ ((b - a) / 2) ^ γ := Real.rpow_nonneg hS0.le γ
  have hH0 : 0 ≤ H := by
    have h := hWH (x 0 0) a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at h
    have h2 : (0 : ℝ) < (b - a) ^ γ := Real.rpow_pos_of_pos (by linarith) γ
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (W (x 0 0) a - W (x 0 0) b)]
  have hcR0 : 0 ≤ cR := by
    have h := hWL (x 0 0) ((a + b) / 2) ⟨by linarith, le_rfl⟩
    have h2 : (0 : ℝ) < ((a + b) / 2 - a) ^ (γ - ((m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (iteratedDeriv (m + 1) (W (x 0 0)) ((a + b) / 2))]
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    have h1 : (0 : ℝ) ≤ (1 + Λ) * H * ((b - a) / 2) ^ γ :=
      mul_nonneg (mul_nonneg (by linarith) hH0) hSγ0
    have h2 : (0 : ℝ)
        ≤ cR * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
      div_nonneg (mul_nonneg (mul_nonneg hcR0 hSγ0) (pow_nonneg (by positivity) _)) hfact0.le
    linarith
  refine ⟨c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1), ?_⟩
  filter_upwards [hc₀] with p hp
  obtain ⟨en, hencoe, hennorm, herr⟩ := hp
  have hsolve : ∀ h : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
      (lam • 1 - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = h := fun h => by
    simpa only [← hencoe, ContinuousLinearEquiv.coe_coe] using en.bijective.existsUnique h
  refine ⟨hsolve, fun un hun => ?_⟩
  -- the consistency error is the interpolation error of the rows, uniformly in the row
  have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  have hcons : ‖admissibleKernelCLM (hg.mul_continuousMap l) u
        - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖
      ≤ rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1)) :=
    norm_admissibleKernelCLM_sub_productCLM_le hg l _ u
      (div_nonneg hCst0 (by positivity)) fun z => by
      have hint := norm_sub_piecewisePolyInterpCLM_le_gradedSym (r := p + 1) hab
        (Nat.succ_pos p) (by omega) hγ0 hγ1 hq hν0 hν1 hνmono (hxL p) (hxR p) (hnodeL p) (hnodeR p)
        (hΛb p) (hW z) (hWH z) (hWC z) (hWL z) (hWR z)
      rwa [hcast] at hint
  -- assemble
  have hfinal := herr f u un hu hun
  have hpos : (0 : ℝ) < ((p : ℝ) + 1) ^ (m + 1) := by positivity
  have hc₀0 : (0 : ℝ) ≤ c₀ := le_trans (norm_nonneg _) hennorm
  calc ‖u - un‖
      ≤ c₀ * ‖admissibleKernelCLM (hg.mul_continuousMap l) u
          - productCLM hg l (piecewisePolyInterpCLM (2 * p + 1) m (x p) (node p)) u‖ := hfinal
    _ ≤ c₀ * (rowBound (iccMeasure a b) g * (Cst / ((p : ℝ) + 1) ^ (m + 1))) :=
        mul_le_mul_of_nonneg_left hcons hc₀0
    _ = c₀ * rowBound (iccMeasure a b) g * Cst * 2 ^ (m + 1)
          / (2 * ((p : ℝ) + 1)) ^ (m + 1) := by
        rw [mul_pow]
        field_simp

end Theorem6



/-! ### Example 12.5.3: the logarithmic kernel of (12.5.21) -/

section LogKernel

open MeasureTheory Set

open scoped Interval Real

/-- **Example 12.5.3** of [han2009theoretical]. The equation of the example is (12.5.21), $$u(x) -
\int_0^\pi u(y) \log |\cos x - \cos y|\, dy = 1, \qquad 0 \le x \le \pi.$$ For every real $x$:

* $\log |\cos x - \cos y| = \log |2 \sin((x - y)/2) \sin((x + y)/2)|$ for every real $y$, the
  first line of (12.5.22);
* the constant $u \equiv 1/(1 + \pi \log 2) \doteq 0.3147$ satisfies (12.5.21) at $x$.

The factorization shows that the singularities of the kernel are at $y = x$, $y = -x$ and
$y = 2\pi - x$. This is why (12.5.22) separates $\log |x - y|$, $\log(x + y)$ and
$\log(2\pi - x - y)$ and leaves an infinitely differentiable factor $l_1$. The constant solves
the equation because $\int_0^\pi \log |\cos x - \cos y|\, dy = -\pi \log 2$ for every $x$
(`integral_log_abs_cos_sub_cos`). It is the solution against which the source measures the
errors of Table 12.3. The table and the remark on the first splitting are not formalized. -/
theorem example_12_5_3 (x : ℝ) :
    (∀ y : ℝ, Real.log |Real.cos x - Real.cos y|
        = Real.log |2 * Real.sin ((x - y) / 2) * Real.sin ((x + y) / 2)|) ∧
      (1 + π * Real.log 2)⁻¹
          - ∫ y in (0 : ℝ)..π, (1 + π * Real.log 2)⁻¹ * Real.log |Real.cos x - Real.cos y|
        = 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < 1 + π * Real.log 2 := by positivity
  refine ⟨fun y => ?_, ?_⟩
  · rw [Real.cos_sub_cos,
      show -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)
        = -(2 * Real.sin ((x - y) / 2) * Real.sin ((x + y) / 2)) by ring, abs_neg]
  · rw [intervalIntegral.integral_const_mul, integral_log_abs_cos_sub_cos x]
    field_simp
    ring

end LogKernel

end AtkinsonHan.Chapter12
