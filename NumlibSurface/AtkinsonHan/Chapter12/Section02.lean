/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.Truncation
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Jackson
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson and Han, Section 12.2: Examples of projection methods

This module formalizes Section 12.2 of [han2009theoretical]. The section applies the projection
method of Section 12.1 to the second kind equation $(\lambda - K) u = f$ with four families of
projections $P_n$: interpolation by continuous piecewise linear functions (§12.2.1), trigonometric
interpolation (§12.2.2), the $L^2$-orthogonal projection onto the continuous piecewise linear
functions (§12.2.3), and the truncation of the Fourier series (§12.2.4). For each family the module
supplies the two inputs of Theorem 12.1.2: the convergence $\|K - P_n K\| \to 0$, and a bound on the
approximation error $\|u - P_n u\|$, which (12.1.24) turns into a bound on the error $\|u - u_n\|$
of the projection solution.

For piecewise linear interpolation and for the two orthogonal projections, the $P_n$ are uniformly
bounded and converge pointwise to the identity, so Lemma 12.1.4 gives $\|K - P_n K\| \to 0$.
Trigonometric interpolation and the Fourier truncation on $C_p(2\pi)$ are not uniformly bounded:
their norms grow like $\log n$. There $\|K - P_n K\| \to 0$ comes from the Hölder condition
(12.2.16) on the kernel. It makes $K u$ Hölder continuous with constant $c \|u\|$, so Jackson's
theorem bounds the best approximation error of $K u$ by $c \|u\| (\pi^2/2)^\alpha n^{-\alpha}$, and
the Lebesgue lemma gives $\|(I - P_n) K u\| \le (1 + \|P_n\|) c \|u\| (\pi^2/2)^\alpha n^{-\alpha}$.
The proofs use `Numlib.Approximation.Interpolation`, `Numlib.Approximation.Jackson`,
`Numlib.Approximation.TrigonometricInterpolation`, `Numlib.Approximation.PiecewiseLinearL2`,
`Numlib.Analysis.Fourier.Truncation` and `Numlib.IntegralEquations.Basic`.

## Main results

* Equation (12.2.5), `AtkinsonHan.Chapter12.equation_12_2_5`: for piecewise linear collocation on
  partitions of vanishing mesh $h_n$, $\|K - P_n K\| \to 0$, the collocation equations are uniquely
  solvable for large $n$, and $\|u - u_n\|_\infty \le c h_n^2 \|u''\|_\infty$ for a $C^2$ solution.
* Equation (12.2.17), `AtkinsonHan.Chapter12.equation_12_2_17`: for trigonometric collocation with a
  kernel that satisfies the Hölder condition (12.2.16), $\|K - P_n K\| \le c' \log n / n^\alpha$,
  and the error of the method is proportional to $\|u - P_n u\|_\infty$.
* Equation (12.2.19), `AtkinsonHan.Chapter12.equation_12_2_19`: for the piecewise linear Galerkin
  method, $\|K - P_n K\| \to 0$, unique solvability for large $n$, and $\|u - u_n\|_{L^2} \le
  |\lambda| M \sqrt{b - a}\, h_n^2 \|u''\|_\infty / 8$ for a $C^2$ solution.
* Equation (12.2.24), `AtkinsonHan.Chapter12.equation_12_2_24`: the truncation error
  $\|u - P_n u\|_{L^2} \le \|u\|_{H^r} / n^r$ of a Fourier series.
* Equation (12.2.25), `AtkinsonHan.Chapter12.equation_12_2_25`: the Fourier–Galerkin method in
  $L^2(0, 2\pi)$ converges at the rate $\|u - u_n\|_{L^2} \le |\lambda| M \|u\|_{H^r} / n^r$.
* Equation (12.2.27), `AtkinsonHan.Chapter12.equation_12_2_27`: the Fourier truncation on
  $C_p(2\pi)$ has $\|P_n\| \le 1 + \log(2n + 1)$ and is not uniformly bounded, and the
  Fourier–Galerkin method still converges in the uniform norm for a Hölder kernel.

## Conventions

* The scalar $\lambda$ of the source is `μ`, because `λ` is the Lean lambda binder.
* A partition of $[a, b]$ is a sequence of nodes `y n : ℕ → Set.Icc a b` together with a count
  `N n`. Only the nodes `y n 0, …, y n (N n + 1)` are used, as in `piecewiseLinearInterpCLM`, so the
  partition has $N_n + 1$ subintervals. The mesh $h_n$ is an upper bound for their lengths.
* $C_p(2\pi)$ is `C(AddCircle (2 * Real.pi), ℝ)`. The integral operator on it integrates against the
  normalized Haar measure `AddCircle.haarAddCircle`, of total mass $1$ instead of $2\pi$. This
  rescales the kernel and changes no statement below, because each statement quantifies over an
  arbitrary constant. The Hölder condition (12.2.16) is stated for representatives
  $x, \xi \in \mathbb{R}$, as the source writes it.
* $L^2(0, 2\pi)$ is `Lp ℝ 2 haarAddCircle`, also with the normalized measure. The norm of
  $H^r(0, 2\pi)$ is the weighted $\ell^2$ norm $\left(|c_0|^2 + \sum_{m \neq 0} |m|^{2r}
  |c_m|^2\right)^{1/2}$ of the real Fourier coefficients `realFourierCoeff`, with the weight
  `periodicSobolevWeight`. It is a `HasSum` hypothesis on the coefficients, not membership in the
  space `PeriodicSobolev r`, which is complex and has no map to `Lp ℝ 2 haarAddCircle`.

## Implementation notes

* Compactness of $K$ on $L^2$ is a hypothesis of `AtkinsonHan.Chapter12.equation_12_2_19` and
  `AtkinsonHan.Chapter12.equation_12_2_25`. On $C[a, b]$ an operator with a continuous kernel is
  compact by `IntegralOperator.isCompactOperator_fredholm` and
  `IntegralOperator.isCompactOperator_kernelCLM`. On $L^2$ the fact is the Hilbert–Schmidt theorem,
  which the library does not have: `IntegralOperator.l2KernelCLM` bounds the operator and computes
  its adjoint, but does not show that it is compact. The source takes the fact from its Chapter 2.
* The error bound of §12.2.3 is (12.2.19). As in the source, it goes through the uniform norm of the
  interpolation error, so `norm_sub_piecewiseLinearInterpCLM_le` supplies all of the approximation
  theory and no $L^2$ interpolation estimate is needed.

## Deviations from the source

* **Equations (12.2.5) and (12.2.19)** (generalization). The source uses the uniform mesh
  $h = (b - a)/n$. The statements hold for every sequence of partitions whose mesh tends to zero.
  See `AtkinsonHan.Chapter12.equation_12_2_5` and `AtkinsonHan.Chapter12.equation_12_2_19`.
* **Equations (12.2.24) and (12.2.25)** (reading). The periodic estimates use real coefficients
  in an orthonormal sine and cosine system. The theorem for (12.2.24) states the full Sobolev
  norm bound with constant $1$. The Galerkin estimates (12.2.19) and (12.2.25) assume compactness
  of the operator directly, which the book obtains from its integral kernel.

## Not formalized

* **Example 12.2.1.** Table 12.1 and the two remarks on it are measured numerical data: the nodal
  errors and their ratios, the observed rate for $u = \sqrt{x}$, and the ratio of the nodal error to
  the uniform error. The bound that the table illustrates is
  `AtkinsonHan.Chapter12.equation_12_2_5`, and the superconvergence at the nodes is the subject of
  Section 12.3.
-/

open Filter Topology

open scoped ContDiff

namespace AtkinsonHan.Chapter12

/-! ### Piecewise linear collocation -/

/-- **Equation (12.2.5)** of [han2009theoretical] (piecewise linear collocation). Let $a \le b$, let
$k$ be a continuous kernel on $[a, b] \times [a, b]$ with Fredholm operator
$K u(x) = \int_a^b k(x, y) u(y)\, dy$ on $C[a, b]$, and let $\lambda \neq 0$ be such that
$\lambda - K$ is invertible. For each $n$ let $a = y_{n,0} < y_{n,1} < \dots < y_{n,N_n+1} = b$
be a partition whose subintervals have length at most $h_n$, with $h_n \to 0$, and let $P_n$ be
piecewise linear interpolation at its nodes. Then $\|K - P_n K\| \to 0$, and there is a constant
$c$ such that for all large $n$:

* for every $f \in C[a, b]$ the collocation equations $u_n \in \operatorname{range} P_n$,
  $P_n (\lambda - K) u_n = P_n f$ have exactly one solution;
* if $(\lambda - K) u = f$, $u$ is the restriction of a $C^2$ function $g$ with $|g''| \le M$ on
  $[a, b]$, and $u_n$ solves the collocation equations, then $$\|u - u_n\|_\infty \le c\, h_n^2
  M.$$

**Generalization.** The source uses the uniform mesh $h = (b - a)/n$, which is the case
$y_{n,j} = a + j h$.

The convergence $\|K - P_n K\| \to 0$ is hypothesis (12.1.21). It follows from
`AtkinsonHan.Chapter12.lemma_12_1_4`, since $K$ is compact by
`IntegralOperator.isCompactOperator_fredholm`. The error bound combines
`AtkinsonHan.Chapter12.theorem_12_1_2`, (12.1.24) and the interpolation error
$\|u - P_n u\| \le h_n^2 M / 8$ of `norm_sub_piecewiseLinearInterpCLM_le`. The proof gives
$c = |\lambda| \|(\lambda - K)^{-1}\| / 4$. -/
theorem equation_12_2_5 {a b : ℝ} (hab : a ≤ b) {μ : ℝ} (hμ : μ ≠ 0)
    (k : C(Set.Icc a b × Set.Icc a b, ℝ)) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - IntegralOperator.fredholm hab k) :
    Tendsto (fun n => ‖IntegralOperator.fredholm hab k -
        piecewiseLinearInterpCLM (N n) (y n) ∘L IntegralOperator.fredholm hab k‖) atTop (𝓝 0) ∧
      ∃ c : ℝ, ∀ᶠ n in atTop,
        (∀ f : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ),
          IsProjectionSolution μ (IntegralOperator.fredholm hab k)
            (piecewiseLinearInterpCLM (N n) (y n)) f un) ∧
        ∀ (g : ℝ → ℝ) (M : ℝ) (f u un : C(Set.Icc a b, ℝ)),
          ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g → (∀ t : Set.Icc a b, u t = g (t : ℝ)) →
          (∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) →
          (μ • 1 - IntegralOperator.fredholm hab k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
          IsProjectionSolution μ (IntegralOperator.fredholm hab k)
            (piecewiseLinearInterpCLM (N n) (y n)) f un →
          ‖u - un‖ ≤ c * h n ^ 2 * M := by
  set K : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) := IntegralOperator.fredholm hab k with hK
  set A : ℝ := ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hcpt : IsCompactOperator K := IntegralOperator.isCompactOperator_fredholm hab k
  have hP : ∀ u : C(Set.Icc a b, ℝ),
      Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) u) atTop (𝓝 u) :=
    tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh
  have hconv : Tendsto (fun n => ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hcpt hP
  refine ⟨hconv, ⟨‖μ‖ * A / 4, ?_⟩⟩
  have hsmall : ∀ᶠ n in atTop, A * ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - piecewiseLinearInterpCLM (N n) (y n) ∘L K‖) atTop
        (𝓝 0) := by simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  have hidem : IsIdempotentElem (piecewiseLinearInterpCLM (N n) (y n)) :=
    isIdempotentElem_piecewiseLinearInterpCLM ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩
  obtain ⟨e', he'coe, he'norm, huniq⟩ := theorem_12_1_2 hμ hidem e he (by rw [← hA]; linarith)
  have hb1 : ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [← hA, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - piecewiseLinearInterpCLM (N n) (y n) ∘L K)]
  refine ⟨huniq, fun g M f u un hg hu hM hueq hun => ?_⟩
  have hb2 : ‖u - piecewiseLinearInterpCLM (N n) (y n) u‖ ≤ h n ^ 2 / 8 * M :=
    norm_sub_piecewiseLinearInterpCLM_le ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩ hg hu
      (hmesh n) hM
  have hkey := (equation_12_1_24 hidem he'coe hueq hun).2
  calc ‖u - un‖
      ≤ ‖μ‖ * ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
          ‖u - piecewiseLinearInterpCLM (N n) (y n) u‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (h n ^ 2 / 8 * M) := by gcongr
    _ = ‖μ‖ * A / 4 * h n ^ 2 * M := by ring

/-! ### Projection methods on the circle in the uniform norm -/

section Periodic

open AddCircle IntegralOperator MeasureTheory PeriodicCont

open scoped Real

local notation "Cₚ" => C(AddCircle (2 * Real.pi), ℝ)

/-- If the kernel satisfies $|k(s, y) - k(t, y)| \le c |s - t|^\alpha$ for all $s, t \in \mathbb{R}$
and all $y$, with $c \ge 0$, then $|K u(s) - K u(t)| \le c \|u\| |s - t|^\alpha$ for every
$u \in C_p(2\pi)$. -/
private theorem holder_kernelCLM_apply {α c : ℝ} (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    (u : Cₚ) (s t : ℝ) :
    |Jackson.lift (kernelCLM haarAddCircle k u) s - Jackson.lift (kernelCLM haarAddCircle k u) t|
      ≤ c * ‖u‖ * |s - t| ^ α := by
  have hs : Integrable (fun y => k ((s : AddCircle (2 * Real.pi)), y) * u y) haarAddCircle :=
    integrable_kernel_mul haarAddCircle k u _
  have ht : Integrable (fun y => k ((t : AddCircle (2 * Real.pi)), y) * u y) haarAddCircle :=
    integrable_kernel_mul haarAddCircle k u _
  have hb : ∀ y : AddCircle (2 * Real.pi),
      |k ((s : AddCircle (2 * Real.pi)), y) * u y - k ((t : AddCircle (2 * Real.pi)), y) * u y|
        ≤ c * |s - t| ^ α * ‖u‖ := by
    intro y
    have hu : |u y| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using u.norm_coe_le_norm y
    rw [← sub_mul, abs_mul]
    exact mul_le_mul (hk s t y) hu (abs_nonneg _) (by positivity)
  simp only [Jackson.lift, kernelCLM_apply]
  rw [← integral_sub hs ht]
  calc |∫ y, (k ((s : AddCircle (2 * Real.pi)), y) * u y
        - k ((t : AddCircle (2 * Real.pi)), y) * u y) ∂haarAddCircle|
      ≤ ∫ y, |k ((s : AddCircle (2 * Real.pi)), y) * u y
          - k ((t : AddCircle (2 * Real.pi)), y) * u y| ∂haarAddCircle :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y : AddCircle (2 * Real.pi), c * |s - t| ^ α * ‖u‖ ∂haarAddCircle :=
        integral_mono (hs.sub ht).abs (integrable_const _) hb
    _ = c * ‖u‖ * |s - t| ^ α := by
        rw [integral_const, probReal_univ, one_smul]
        ring

/-- If the kernel satisfies the Hölder condition (12.2.16) with $0 \le \alpha \le 1$, $n \ge 1$, and
$P$ is a bounded operator with $\|f - P f\| \le L \operatorname{dist}(f, \mathcal{T}_n)$ for all
$f$, where $\mathcal{T}_n$ is the space of trigonometric polynomials of degree at most $n$, then
$\|K - P K\| \le L c (\pi^2/2)^\alpha / n^\alpha$. -/
private theorem norm_sub_comp_kernelCLM_le {α c : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {n : ℕ} (hn : 1 ≤ n) {P : Cₚ →L[ℝ] Cₚ} {L : ℝ} (hL : 0 ≤ L)
    (hPL : ∀ f : Cₚ, ‖f - P f‖ ≤ L * Metric.infDist f (trigPolyLE (2 * Real.pi) n : Set Cₚ)) :
    ‖kernelCLM haarAddCircle k - P ∘L kernelCLM haarAddCircle k‖
      ≤ L * (c * (Real.pi ^ 2 / 2) ^ α) / (n : ℝ) ^ α := by
  have hpi := Real.pi_pos
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (mul_nonneg hL (mul_nonneg hc hrpow)) hnpos.le) fun u => ?_
  have hbound : Metric.infDist (kernelCLM haarAddCircle k u) (trigPolyLE (2 * Real.pi) n : Set Cₚ)
      ≤ c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α) := by
    refine (Jackson.infDist_le_of_holder (by positivity) hα0 hα1
      (holder_kernelCLM_apply hc hk u) n).trans ?_
    have h1 : Real.pi * Real.sin (Jackson.angle n / 2) ≤ Real.pi ^ 2 / 2 / (n : ℝ) := by
      refine (Jackson.pi_mul_sin_half_angle_le n).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have h2 : (Real.pi * Real.sin (Jackson.angle n / 2)) ^ α
        ≤ (Real.pi ^ 2 / 2 / (n : ℝ)) ^ α :=
      Real.rpow_le_rpow (mul_pos hpi (Jackson.sin_half_angle_pos n)).le h1 hα0
    calc c * ‖u‖ * (Real.pi * Real.sin (Jackson.angle n / 2)) ^ α
        ≤ c * ‖u‖ * (Real.pi ^ 2 / 2 / (n : ℝ)) ^ α :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α) := by
          rw [Real.div_rpow (by positivity) (Nat.cast_nonneg n)]
  have happ : (kernelCLM haarAddCircle k - P ∘L kernelCLM haarAddCircle k) u
      = kernelCLM haarAddCircle k u - P (kernelCLM haarAddCircle k u) := rfl
  rw [happ]
  calc ‖kernelCLM haarAddCircle k u - P (kernelCLM haarAddCircle k u)‖
      ≤ L * Metric.infDist (kernelCLM haarAddCircle k u)
          (trigPolyLE (2 * Real.pi) n : Set Cₚ) := hPL _
    _ ≤ L * (c * ‖u‖ * ((Real.pi ^ 2 / 2) ^ α / (n : ℝ) ^ α)) := by gcongr
    _ = L * (c * (Real.pi ^ 2 / 2) ^ α) / (n : ℝ) ^ α * ‖u‖ := by
        field_simp

/-- For $A, B \ge 0$ and $n \ge 2$, $A + B \log(2n + 1) \le (A / \log 2 + B(\log 3 / \log 2 + 1))
\log n$. -/
private theorem add_mul_log_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    A + B * Real.log (2 * (n : ℝ) + 1)
      ≤ (A / Real.log 2 + B * (Real.log 3 / Real.log 2 + 1)) * Real.log n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have h2 : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
    calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
  have hA' : A ≤ A / Real.log 2 * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogn hA
  have hratio : (1 : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).2 (by linarith)
  have hB' : B * Real.log 3 ≤ B * (Real.log 3 / Real.log 2) * Real.log n := by
    have hrw : B * (Real.log 3 / Real.log 2) * Real.log n
        = B * Real.log 3 * (Real.log n / Real.log 2) := by
      field_simp
    rw [hrw]
    nlinarith [mul_nonneg hB hlog3]
  have hBlog : B * Real.log (2 * (n : ℝ) + 1) ≤ B * Real.log 3 + B * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]
  nlinarith

/-- For $\alpha > 0$, $\log n / n^\alpha \to 0$ as $n \to \infty$ along the natural numbers. -/
private theorem tendsto_log_div_rpow {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ α) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

/-- If $P_n$ are bounded projections on a Banach space, $\lambda \neq 0$, $\lambda - K$ is
invertible and $\|K - P_n K\| \to 0$, then for all large $n$ the projection equations have
exactly one solution for every right-hand side. -/
private theorem eventually_existsUnique_projectionSolution {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {μ : ℝ} (hμ : μ ≠ 0) {K : X →L[ℝ] X} {P : ℕ → X →L[ℝ] X}
    (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[ℝ] X} (he : (e : X →L[ℝ] X) = μ • 1 - K)
    (hconv : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ f : X, ∃! un : X, IsProjectionSolution μ K (P n) f un := by
  have hsmall : ∀ᶠ n in atTop, ‖(e.symm : X →L[ℝ] X)‖ * ‖K - P n ∘L K‖ < 1 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[ℝ] X)‖ * ‖K - P n ∘L K‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul ‖(e.symm : X →L[ℝ] X)‖
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  obtain ⟨-, -, -, huniq⟩ := theorem_12_1_2 hμ (hP n) e he hn
  exact huniq

/-- **Equation (12.2.17)** of [han2009theoretical] (trigonometric collocation). Let
$K u(x) = \int k(x, y) u(y)\, dy$ be the integral operator on $C_p(2\pi)$ of a continuous kernel
$k$ that satisfies the Hölder condition (12.2.16), $$|k(x, y) - k(\xi, y)| \le c |x -
\xi|^\alpha \qquad \text{for all } x, \xi \in \mathbb{R} \text{ and all } y,$$ with
$0 < \alpha \le 1$ and $c \ge 0$. Let $\lambda \neq 0$ be such that $\lambda - K$ is invertible,
and let $P_n$ be interpolation by trigonometric polynomials of degree at most $n$ at $2n + 1$
equidistant nodes. Then:

* there is $c' > 0$ with $$\|K - P_n K\| \le c' \frac{\log n}{n^\alpha} \qquad \text{for all } n
  \ge 2,$$ which is (12.2.17), and hence $\|K - P_n K\| \to 0$, hypothesis (12.1.21) of Theorem
  12.1.2;
* there is a sequence $\gamma_n \to 0$ such that for all large $n$ the collocation equations
  have exactly one solution $u_n$ for every $f$, and $(\lambda - K) u = f$ implies $$\|u -
  u_n\|_\infty \le |\lambda| (1 + \gamma_n) \|(\lambda - K)^{-1}\| \|u - P_n u\|_\infty.$$

Lemma 12.1.4 does not apply, because the Lebesgue constants of trigonometric interpolation grow
like $\log n$ and $P_n u \to u$ fails for some continuous $u$. The estimate is proved directly
from Jackson's theorem for the Hölder function $K u$ and the bound `norm_trigInterpCLM_le` on
the Lebesgue constants. The second clause is Theorem 12.1.2 together with Exercise 12.1.3. The
lower bound of (12.1.24), `AtkinsonHan.Chapter12.equation_12_1_24`, gives the converse, so
$\|u - u_n\|_\infty \to 0$ if and only if $\|u - P_n u\|_\infty \to 0$, as the source observes. -/
theorem equation_12_2_17 {α c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {μ : ℝ} (hμ : μ ≠ 0) {e : Cₚ ≃L[ℝ] Cₚ}
    (he : (e : Cₚ →L[ℝ] Cₚ) = μ • 1 - kernelCLM haarAddCircle k) :
    (∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
        ‖kernelCLM haarAddCircle k
            - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖
          ≤ c' * Real.log n / (n : ℝ) ^ α) ∧
      Tendsto (fun n => ‖kernelCLM haarAddCircle k
        - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) ∧
      ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ f : Cₚ, ∃! un : Cₚ, IsProjectionSolution μ (kernelCLM haarAddCircle k)
          (trigInterpCLM (2 * Real.pi) n) f un) ∧
        ∀ f u un : Cₚ, (μ • 1 - kernelCLM haarAddCircle k : Cₚ →L[ℝ] Cₚ) u = f →
          IsProjectionSolution μ (kernelCLM haarAddCircle k)
            (trigInterpCLM (2 * Real.pi) n) f un →
          ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : Cₚ →L[ℝ] Cₚ)‖ *
            ‖u - trigInterpCLM (2 * Real.pi) n u‖ := by
  have hpi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  set c₀ : ℝ := 3 / Real.log 2 + 2 / Real.pi * (Real.log 3 / Real.log 2 + 1) with hc₀
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set c' : ℝ := c₀ * (c * (Real.pi ^ 2 / 2) ^ α) + 1 with hc'
  have hc'0 : 0 < c' := by
    rw [hc']
    nlinarith [mul_nonneg hc₀0.le (mul_nonneg hc hrpow)]
  have hmain : ∀ n : ℕ, 2 ≤ n →
      ‖kernelCLM haarAddCircle k
          - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖
        ≤ c' * Real.log n / (n : ℝ) ^ α := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
    have hLnn : (0 : ℝ) ≤ 1 + ‖trigInterpCLM (2 * Real.pi) n‖ := by positivity
    have hLle : 1 + ‖trigInterpCLM (2 * Real.pi) n‖ ≤ c₀ * Real.log n := by
      refine le_trans ?_ (add_mul_log_le (A := 3) (B := 2 / Real.pi) (by norm_num)
        (by positivity) hn)
      have := norm_trigInterpCLM_le (n := n)
      linarith
    have hstep := norm_sub_comp_kernelCLM_le hc hα0.le hα1 hk hn1 hLnn
      (fun f => norm_sub_trigInterpCLM_le n f)
    refine hstep.trans ?_
    rw [div_le_div_iff₀ hnpos hnpos]
    have hkey : (1 + ‖trigInterpCLM (2 * Real.pi) n‖) * (c * (Real.pi ^ 2 / 2) ^ α)
        ≤ c₀ * Real.log n * (c * (Real.pi ^ 2 / 2) ^ α) :=
      mul_le_mul_of_nonneg_right hLle (mul_nonneg hc hrpow)
    have hextra : (0 : ℝ) ≤ Real.log n * (n : ℝ) ^ α := by positivity
    rw [hc']
    nlinarith
  have htend : Tendsto (fun n => ‖kernelCLM haarAddCircle k
      - trigInterpCLM (2 * Real.pi) n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.mono (eventually_ge_atTop 2) hmain) ?_
    have h := (tendsto_log_div_rpow hα0).const_mul c'
    rw [mul_zero] at h
    exact h.congr fun n => (mul_div_assoc c' (Real.log n) ((n : ℝ) ^ α)).symm
  obtain ⟨γ, hγ, hev⟩ := exercise_12_1_3 (μ := μ) (K := kernelCLM haarAddCircle k)
    (P := fun n => trigInterpCLM (2 * Real.pi) n) (fun _ => isIdempotentElem_trigInterpCLM) he
    htend
  refine ⟨⟨c', hc'0, hmain⟩, htend, γ, hγ, ?_⟩
  filter_upwards [hev, eventually_existsUnique_projectionSolution hμ
    (P := fun n => trigInterpCLM (2 * Real.pi) n) (fun _ => isIdempotentElem_trigInterpCLM) he
    htend] with n h1 h2
  exact ⟨h2, h1⟩

/-- **Equation (12.2.27)** of [han2009theoretical], with the convergence analysis of §12.2.4 in the
uniform norm. Let $P_n$ be the truncation of the Fourier series at degree $n$, as an operator on
$C_p(2\pi)$. Then $$\|P_n\| \le 1 + \log(2n + 1) \qquad \text{for all } n,$$ which is (12.2.27),
and the norms $\|P_n\|$ are not bounded, so Lemma 12.1.4 does not apply. Let $K$ be the integral
operator on $C_p(2\pi)$ of a continuous kernel with
$|k(x, y) - k(\xi, y)| \le c |x - \xi|^\alpha$ for all $x, \xi \in \mathbb{R}$ and all $y$,
where $0 < \alpha \le 1$ and $c \ge 0$, and let $\lambda \neq 0$ be such that $\lambda - K$ is
invertible. Then:

* there is $c' > 0$ with $\|K - P_n K\| \le c' \log n / n^\alpha$ for all $n \ge 2$, and hence
  $\|K - P_n K\| \to 0$;
* there is a sequence $\gamma_n \to 0$ such that for all large $n$ the Galerkin equations have
  exactly one solution $u_n$ for every $f$, and $(\lambda - K) u = f$ implies $$\|u -
  u_n\|_\infty \le |\lambda| (1 + \gamma_n) \|(\lambda - K)^{-1}\| \|u - P_n u\|_\infty.$$

The truncation is `PeriodicCont.fourierProj`, whose norm is the $n$-th Lebesgue constant. The
upper bound is `PeriodicCont.lebesgueConstant_le`, and the unboundedness follows from the lower
bound $(4/\pi^2) \log n \le L_n$ of `PeriodicCont.log_le_lebesgueConstant`, which is (3.7.10) of
the source. -/
theorem equation_12_2_27 {α c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {k : C(AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi), ℝ)}
    (hk : ∀ (s t : ℝ) (y : AddCircle (2 * Real.pi)), |k (↑s, y) - k (↑t, y)| ≤ c * |s - t| ^ α)
    {μ : ℝ} (hμ : μ ≠ 0) {e : Cₚ ≃L[ℝ] Cₚ}
    (he : (e : Cₚ →L[ℝ] Cₚ) = μ • 1 - kernelCLM haarAddCircle k) :
    (∀ n : ℕ, ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1)) ∧
      ¬ BddAbove (Set.range fun n : ℕ => ‖fourierProj n‖) ∧
      (∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
        ‖kernelCLM haarAddCircle k - fourierProj n ∘L kernelCLM haarAddCircle k‖
          ≤ c' * Real.log n / (n : ℝ) ^ α) ∧
      Tendsto (fun n => ‖kernelCLM haarAddCircle k
        - fourierProj n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) ∧
      ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ f : Cₚ, ∃! un : Cₚ,
          IsProjectionSolution μ (kernelCLM haarAddCircle k) (fourierProj n) f un) ∧
        ∀ f u un : Cₚ, (μ • 1 - kernelCLM haarAddCircle k : Cₚ →L[ℝ] Cₚ) u = f →
          IsProjectionSolution μ (kernelCLM haarAddCircle k) (fourierProj n) f un →
          ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : Cₚ →L[ℝ] Cₚ)‖ * ‖u - fourierProj n u‖ := by
  have hpi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrpow : (0 : ℝ) ≤ (Real.pi ^ 2 / 2) ^ α := Real.rpow_nonneg (by positivity) α
  -- (12.2.27) itself, and the unboundedness that makes Lemma 12.1.4 unavailable
  have hnorm : ∀ n : ℕ, ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1) := fun n => by
    rw [norm_fourierProj]
    exact lebesgueConstant_le n
  have hunbdd : ¬ BddAbove (Set.range fun n : ℕ => ‖fourierProj n‖) := by
    rintro ⟨C, hC⟩
    have hlog : Tendsto (fun n : ℕ => 4 / Real.pi ^ 2 * Real.log n) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    obtain ⟨n, hn⟩ := (hlog.eventually_gt_atTop C).exists
    have hle : 4 / Real.pi ^ 2 * Real.log n ≤ ‖fourierProj n‖ := by
      rw [norm_fourierProj]
      exact log_le_lebesgueConstant n
    exact absurd (hC ⟨n, rfl⟩) (not_le.2 (lt_of_lt_of_le hn hle))
  set c₀ : ℝ := 2 / Real.log 2 + (Real.log 3 / Real.log 2 + 1) with hc₀
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set c' : ℝ := c₀ * (c * (Real.pi ^ 2 / 2) ^ α) + 1 with hc'
  have hc'0 : 0 < c' := by
    rw [hc']
    nlinarith [mul_nonneg hc₀0.le (mul_nonneg hc hrpow)]
  have hmain : ∀ n : ℕ, 2 ≤ n →
      ‖kernelCLM haarAddCircle k - fourierProj n ∘L kernelCLM haarAddCircle k‖
        ≤ c' * Real.log n / (n : ℝ) ^ α := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos (by linarith) α
    have hLnn : (0 : ℝ) ≤ 1 + lebesgueConstant n := by
      rw [← norm_fourierProj n]
      positivity
    have hLle : 1 + lebesgueConstant n ≤ c₀ * Real.log n := by
      have h := add_mul_log_le (A := 2) (B := 1) (by norm_num) (by norm_num) hn
      have h2 := lebesgueConstant_le n
      rw [hc₀]
      linarith
    have hstep := norm_sub_comp_kernelCLM_le hc hα0.le hα1 hk hn1 hLnn
      (fun f => norm_sub_fourierProj_le n f)
    refine hstep.trans ?_
    rw [div_le_div_iff₀ hnpos hnpos]
    have hkey : (1 + lebesgueConstant n) * (c * (Real.pi ^ 2 / 2) ^ α)
        ≤ c₀ * Real.log n * (c * (Real.pi ^ 2 / 2) ^ α) :=
      mul_le_mul_of_nonneg_right hLle (mul_nonneg hc hrpow)
    have hextra : (0 : ℝ) ≤ Real.log n * (n : ℝ) ^ α := by positivity
    rw [hc']
    nlinarith
  have htend : Tendsto (fun n => ‖kernelCLM haarAddCircle k
      - fourierProj n ∘L kernelCLM haarAddCircle k‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.mono (eventually_ge_atTop 2) hmain) ?_
    have h := (tendsto_log_div_rpow hα0).const_mul c'
    rw [mul_zero] at h
    exact h.congr fun n => (mul_div_assoc c' (Real.log n) ((n : ℝ) ^ α)).symm
  obtain ⟨γ, hγ, hev⟩ := exercise_12_1_3 (μ := μ) (K := kernelCLM haarAddCircle k)
    (P := fun n => fourierProj n) (fun n => isIdempotentElem_fourierProj n) he htend
  refine ⟨hnorm, hunbdd, ⟨c', hc'0, hmain⟩, htend, γ, hγ, ?_⟩
  filter_upwards [hev, eventually_existsUnique_projectionSolution hμ
    (P := fun n => fourierProj n) (fun n => isIdempotentElem_fourierProj n) he htend] with n h1 h2
  exact ⟨h2, h1⟩

end Periodic

/-! ### The Fourier–Galerkin method in $L^2$ -/

section Fourier

open AddCircle MeasureTheory

open scoped Real

local notation "L²p" => Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

/-- **Equation (12.2.24)** of [han2009theoretical]. Let $r \ge 0$, $n \ge 1$ and
$u \in L^2(0, 2\pi)$, and let $S \ge 0$ satisfy $$\|u\|_{H^r}^2 = |c_0|^2 + \sum_{m \neq 0}
|m|^{2r} |c_m|^2 = S^2,$$ where $c_m$ are the real Fourier coefficients of $u$. Let $P_n$ be the
orthogonal projection of $L^2(0, 2\pi)$ onto the trigonometric polynomials of degree at most
$n$. Then $$\|u - P_n u\|_{L^2} \le \frac{S}{n^r},$$ which is (12.2.24) with the constant $1$.

The orthogonal projection is at least as good as the partial sum of the Fourier series. The
squared error of the partial sum is the tail $\sum_{|m| > n} c_m^2$ of Parseval's identity, and
on that tail $c_m^2 \le n^{-2r} |m|^{2r} c_m^2$. The weight is `periodicSobolevWeight`, the
weight of Definition 7.5.1 of the source, here on the real trigonometric system instead of the
complex exponentials. The projection is `trigProjCLM` and the coefficients are
`realFourierCoeff`.

**Reading.** Real orthonormal coefficient norm and sharp full-norm constant, omitting the separate
tail inequality.
-/
theorem equation_12_2_24 {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 1 ≤ n) (u : L²p) {S : ℝ}
    (hS0 : 0 ≤ S)
    (hS : HasSum (fun m : ℤ => periodicSobolevWeight r m ^ 2 *
      realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) (S ^ 2)) :
    ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ S / (n : ℝ) ^ r := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := Real.rpow_pos_of_pos (by linarith) r
  have hnr2 : (0 : ℝ) < (n : ℝ) ^ (2 * r) := Real.rpow_pos_of_pos (by linarith) _
  -- the projection is at least as good as the partial sum
  have hbest : ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ ‖u - trigPartialSum n u‖ :=
    (isBestApprox_starProjection (trigPolyLp (2 * Real.pi) n) u).2 _
      (trigPartialSum_mem_trigPolyLp n u)
  -- the squared truncation error is the Parseval tail, and the tail is bounded by the weighted sum
  have hpt : ∀ m : ℤ,
      (if m.natAbs ≤ n then 0 else realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2)
        ≤ ((n : ℝ) ^ (2 * r))⁻¹ * (periodicSobolevWeight r m ^ 2 *
            realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) := by
    intro m
    by_cases hm : m.natAbs ≤ n
    · rw [ite_eq_left hm]
      have h1 : (0 : ℝ) ≤ periodicSobolevWeight r m ^ 2 *
          realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2 := by positivity
      positivity
    · rw [ite_eq_right hm]
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hm (by omega)
      have hmn : (n : ℝ) ≤ |(m : ℝ)| := by
        have h1 : n ≤ m.natAbs := Nat.le_of_lt (Nat.lt_of_not_le hm)
        have h2 : (n : ℝ) ≤ ((m.natAbs : ℕ) : ℝ) := by exact_mod_cast h1
        rwa [Nat.cast_natAbs, Int.cast_abs] at h2
      have hpow : (n : ℝ) ^ (2 * r) ≤ |(m : ℝ)| ^ (2 * r) :=
        Real.rpow_le_rpow (by linarith) hmn (by linarith)
      have hc : (0 : ℝ) ≤ realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2 := sq_nonneg _
      rw [periodicSobolevWeight_sq r hm0, ← mul_assoc, ← div_eq_inv_mul]
      have hratio : (1 : ℝ) ≤ |(m : ℝ)| ^ (2 * r) / (n : ℝ) ^ (2 * r) :=
        (one_le_div hnr2).2 hpow
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ |(m : ℝ)| ^ (2 * r) / (n : ℝ) ^ (2 * r) - 1 by
        linarith) hc]
  have hle : ‖u - trigPartialSum n u‖ ^ 2 ≤ ((n : ℝ) ^ (2 * r))⁻¹ * S ^ 2 :=
    hasSum_le hpt (hasSum_sq_realFourierCoeff_compl n u) (hS.mul_left _)
  have hrw : ((n : ℝ) ^ (2 * r))⁻¹ * S ^ 2 = (S / (n : ℝ) ^ r) ^ 2 := by
    rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ r) 2, ← Real.rpow_mul (by linarith)]
    rw [show r * (2 : ℕ) = 2 * r by push_cast; ring]
    field_simp
  rw [hrw] at hle
  refine hbest.trans ?_
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- **Equation (12.2.25)** of [han2009theoretical] (the Fourier–Galerkin method in $L^2(0, 2\pi)$).
Let $K$ be a compact operator on $L^2(0, 2\pi)$, let $\lambda \neq 0$ be such that $\lambda - K$
is invertible, let $r \ge 0$, and let $P_n$ be the truncation of the Fourier series at degree
$n$. Then there is a constant $M$ such that for all large $n$ the Galerkin equations have
exactly one solution $u_n$ for every $f$, and if $(\lambda - K) u = f$ with $\|u\|_{H^r} = S$,
then $$\|u - u_n\|_{L^2} \le |\lambda| M \frac{S}{n^r}.$$

The norm $\|u\|_{H^r} = S$ is the hypothesis of `AtkinsonHan.Chapter12.equation_12_2_24`. The
projections are orthogonal, so $\|P_n\| \le 1$ (`norm_trigProjCLM_le_one`), and they converge
pointwise (`tendsto_trigProjCLM`). Lemma 12.1.4 therefore gives $\|K - P_n K\| \to 0$, Theorem
12.1.2 applies, and the rate is `AtkinsonHan.Chapter12.equation_12_2_24` inserted into
(12.1.24). Compactness of $K$ is a hypothesis: for an operator with a kernel on $L^2$ it is the
Hilbert–Schmidt theorem, which the library does not have, and the source takes it from its
Chapter 2.

**Reading.** Uses the real coefficient norm and assumes compactness of the operator directly.
-/
theorem equation_12_2_25 {K : L²p →L[ℝ] L²p} (hK : IsCompactOperator K) {μ : ℝ} (hμ : μ ≠ 0)
    {e : L²p ≃L[ℝ] L²p} (he : (e : L²p →L[ℝ] L²p) = μ • 1 - K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ M : ℝ, ∀ᶠ n in atTop,
      (∀ f : L²p, ∃! un : L²p,
        IsProjectionSolution μ K (trigProjCLM (2 * Real.pi) n) f un) ∧
      ∀ (f u un : L²p) (S : ℝ), 0 ≤ S →
        HasSum (fun m : ℤ => periodicSobolevWeight r m ^ 2 *
          realFourierCoeff (u : AddCircle (2 * Real.pi) → ℝ) m ^ 2) (S ^ 2) →
        (μ • 1 - K : L²p →L[ℝ] L²p) u = f →
        IsProjectionSolution μ K (trigProjCLM (2 * Real.pi) n) f un →
        ‖u - un‖ ≤ ‖μ‖ * M * (S / (n : ℝ) ^ r) := by
  set A : ℝ := ‖(e.symm : L²p →L[ℝ] L²p)‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  have hconv : Tendsto (fun n => ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hK fun x => tendsto_trigProjCLM x
  refine ⟨2 * A, ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      A * ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - trigProjCLM (2 * Real.pi) n ∘L K‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨e', he'coe, he'norm, huniq⟩ :=
    theorem_12_1_2 hμ (isIdempotentElem_trigProjCLM (2 * Real.pi) n) e he (by linarith)
  have hb1 : ‖(e'.symm : L²p →L[ℝ] L²p)‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - trigProjCLM (2 * Real.pi) n ∘L K)]
  refine ⟨huniq, fun f u un S hS0 hS hu hun => ?_⟩
  have hrate : ‖u - trigProjCLM (2 * Real.pi) n u‖ ≤ S / (n : ℝ) ^ r :=
    equation_12_2_24 hr hn1 u hS0 hS
  have hkey := (equation_12_1_24 (isIdempotentElem_trigProjCLM (2 * Real.pi) n) he'coe hu hun).2
  calc ‖u - un‖
      ≤ ‖μ‖ * ‖(e'.symm : L²p →L[ℝ] L²p)‖ * ‖u - trigProjCLM (2 * Real.pi) n u‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (S / (n : ℝ) ^ r) := by gcongr

end Fourier

/-! ### The piecewise linear Galerkin method in $L^2$ -/

section Galerkin

open MeasureTheory IntegralOperator

variable {a b : ℝ}

/-- **Equation (12.2.19)** of [han2009theoretical] (the piecewise linear Galerkin method of
§12.2.3). Let $a \le b$, let $K$ be a compact operator on $L^2(a, b)$, and let $\lambda \neq 0$
be such that $\lambda - K$ is invertible. For each $n$ let
$a = y_{n,0} < \dots < y_{n,N_n+1} = b$ be a partition whose subintervals have length at most
$h_n$, with $h_n \to 0$, and let $P_n$ be the $L^2$-orthogonal projection onto the continuous
functions that are linear on each subinterval. Then $\|K - P_n K\| \to 0$, and there is a
constant $M$ such that for all large $n$:

* for every $f \in L^2(a, b)$ the Galerkin equations have exactly one solution $u_n$;
* if $(\lambda - K) u = f$, where $u$ is the class of a continuous function on $[a, b]$ that is
  the restriction of a $C^2$ function $g$ with $|g''| \le M_2$ on $[a, b]$, and $u_n$ solves the
  Galerkin equations, then $$\|u - u_n\|_{L^2} \le |\lambda| M \sqrt{b - a}\, \frac{h_n^2}{8}
  M_2.$$

**Generalization.** The source uses the uniform mesh $h = (b - a)/n$, which is a special case.

The projections are orthogonal and converge pointwise by `tendsto_piecewiseLinearProjCLM`, so
Lemma 12.1.4 applies. The approximation bound is (12.2.18), that is
`norm_sub_piecewiseLinearProjCLM_le` and `IntegralOperator.norm_iccToLp_le`, followed by the
uniform interpolation bound `norm_sub_piecewiseLinearInterpCLM_le`, as in the source. The proof
gives $M = 2 \|(\lambda - K)^{-1}\|$. The measure is `IntegralOperator.iccMeasure a b`, and
`IntegralOperator.iccToLp` maps a continuous function to its class. Compactness of $K$ is a
hypothesis, as in `AtkinsonHan.Chapter12.equation_12_2_25`. -/
theorem equation_12_2_19 (hab : a ≤ b) {μ : ℝ} (hμ : μ ≠ 0)
    {K : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)} (hK : IsCompactOperator K)
    {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0))
    {e : Lp ℝ 2 (IntegralOperator.iccMeasure a b) ≃L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)}
    (he : (e : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b)) = μ • 1 - K) :
    Tendsto (fun n => ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖) atTop (𝓝 0) ∧
      ∃ M : ℝ, ∀ᶠ n in atTop,
        (∀ f : Lp ℝ 2 (IntegralOperator.iccMeasure a b),
          ∃! un : Lp ℝ 2 (IntegralOperator.iccMeasure a b),
            IsProjectionSolution μ K (piecewiseLinearProjCLM a b (N n) (y n)) f un) ∧
        ∀ (g : ℝ → ℝ) (M₂ : ℝ) (uc : C(Set.Icc a b, ℝ))
          (f un : Lp ℝ 2 (IntegralOperator.iccMeasure a b)),
          ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g → (∀ t : Set.Icc a b, uc t = g (t : ℝ)) →
          (∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M₂) →
          (μ • 1 - K : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
            Lp ℝ 2 (IntegralOperator.iccMeasure a b)) (iccToLp a b uc) = f →
          IsProjectionSolution μ K (piecewiseLinearProjCLM a b (N n) (y n)) f un →
          ‖iccToLp a b uc - un‖ ≤ ‖μ‖ * M * (√(b - a) * (h n ^ 2 / 8 * M₂)) := by
  set A : ℝ := ‖(e.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
    Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  have hconv : Tendsto (fun n => ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖) atTop (𝓝 0) :=
    lemma_12_1_4 hK (tendsto_piecewiseLinearProjCLM hab hstep hfirst hlast hmesh hh)
  refine ⟨hconv, ⟨2 * A, ?_⟩⟩
  have hsmall : ∀ᶠ n in atTop,
      A * ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K‖)
        atTop (𝓝 0) := by simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  obtain ⟨e', he'coe, he'norm, huniq⟩ :=
    theorem_12_1_2 hμ (isIdempotentElem_piecewiseLinearProjCLM a b (N n) (y n)) e he
      (by linarith)
  have hb1 : ‖(e'.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
      Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (K - piecewiseLinearProjCLM a b (N n) (y n) ∘L K)]
  refine ⟨huniq, fun g M₂ uc f un hg huc hM₂ hu hun => ?_⟩
  have hb2 : ‖iccToLp a b uc - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b uc)‖
      ≤ √(b - a) * (h n ^ 2 / 8 * M₂) := by
    refine (norm_sub_piecewiseLinearProjCLM_le hab (N n) (y n) uc).trans ?_
    exact mul_le_mul_of_nonneg_left
      (norm_sub_piecewiseLinearInterpCLM_le ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩
        hg huc (hmesh n) hM₂)
      (Real.sqrt_nonneg _)
  have hkey := (equation_12_1_24 (isIdempotentElem_piecewiseLinearProjCLM a b (N n) (y n))
    he'coe hu hun).2
  calc ‖iccToLp a b uc - un‖
      ≤ ‖μ‖ * ‖(e'.symm : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ]
            Lp ℝ 2 (IntegralOperator.iccMeasure a b))‖ *
          ‖iccToLp a b uc - piecewiseLinearProjCLM a b (N n) (y n) (iccToLp a b uc)‖ := hkey
    _ ≤ ‖μ‖ * (2 * A) * (√(b - a) * (h n ^ 2 / 8 * M₂)) := by gcongr

end Galerkin

end AtkinsonHan.Chapter12
