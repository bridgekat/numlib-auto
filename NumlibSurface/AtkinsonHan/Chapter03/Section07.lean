/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Jackson
import Numlib.Approximation.LeastSquares
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.Approximation.Trigonometric
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.Krylov.OrthogonalPolynomials
import NumlibSurface.AtkinsonHan.Chapter03.Section06

/-!
# Atkinson and Han, Section 3.7: Uniform error bounds

This module formalizes §3.7 of [han2009theoretical], which bounds the uniform error of three
projection methods: the Fourier projection $\mathcal{F}_n$ on $C_p(2\pi)$, the least squares
projection $P_N$ on $C[-1, 1]$, and trigonometric interpolation $\mathcal{I}_n$ at $2n + 1$
equispaced nodes. Two abstract facts carry the section. The Lebesgue lemma says that for a bounded
projection $\mathcal{P}$ and any $q$ in its range, $\|u - \mathcal{P}u\| \le (1 + \|\mathcal{P}\|)
\|u - q\|$. This is the common form of (3.7.11), (3.7.14) and (3.7.21). The non-convergence lemma
says that if the norms of a sequence of bounded operators on a Banach space are unbounded, then some
vector is not the limit of its images.

The norm of $\mathcal{F}_n$ is the Lebesgue constant $L_n = (1/\pi) \int_{-\pi}^{\pi} |D_n|$ of the
Dirichlet kernel $D_n$, and $L_n$ grows like $\log n$. So the Fourier series of some continuous
periodic function does not converge uniformly. Jackson's theorems bound the best approximation error
of a function with a Hölder continuous $k$-th derivative by $c^{k+1} M_k / n^{k + \alpha}$, and with
the Lebesgue lemma they give the rate $c_k \log n / n^{k+\alpha}$ for $\mathcal{F}_n$ and
$\mathcal{I}_n$. For the Chebyshev weight, $\|P_N\|$ is exactly $L_N$. The proofs specialize the
backbone modules `Numlib.Approximation.Jackson`, `Numlib.Approximation.Trigonometric`,
`Numlib.Approximation.TrigonometricInterpolation`, `Numlib.Approximation.LeastSquares`,
`Numlib.Approximation.OrthogonalPolynomial` and `Numlib.Analysis.Normed.Operator.BanachSteinhaus`.

## Main definitions

* `AtkinsonHan.Chapter03.HolderClass`: the class $C_p^{k,\alpha}(2\pi)$ of Theorem 3.7.1.
* `AtkinsonHan.Chapter03.HolderClassIcc`: the class $C^{k,\alpha}[-1, 1]$ of Theorem 3.7.2.

## Main results

* `AtkinsonHan.Chapter03.lebesgue_lemma`: $\|u - \mathcal{P}u\| \le (1 + \|\mathcal{P}\|) \|u - q\|$
  for a bounded projection $\mathcal{P}$ and $q$ in its range.
* `AtkinsonHan.Chapter03.exists_not_tendsto_of_not_bddAbove`: if $\|\mathcal{P}_n\|$ is unbounded,
  then $\mathcal{P}_n f \to f$ fails for some $f$.
* Equation (3.7.5), `AtkinsonHan.Chapter03.equation_3_7_5`: $\|f - \mathcal{F}_n f\|_{L^2} \le
  \sqrt{2\pi}\, \|f - \mathcal{F}_n f\|_\infty$.
* Equation (3.7.6), `AtkinsonHan.Chapter03.equation_3_7_6`: $\mathcal{F}_n f$ is the integral of $f$
  against the Dirichlet kernel.
* Equations (3.7.7)–(3.7.8), `AtkinsonHan.Chapter03.equation_3_7_8`: the two forms of the Dirichlet
  kernel $D_n$.
* Equation (3.7.9), `AtkinsonHan.Chapter03.equation_3_7_9`:
  $\|\mathcal{F}_n\| = (2/\pi) \int_0^\pi |D_n|$.
* `AtkinsonHan.Chapter03.norm_fourierProj_asymptotics`: $(4/\pi^2) \log n \le \|\mathcal{F}_n\| \le
  1 + \log(2n + 1)$, in place of (3.7.10).
* Section 3.7, `AtkinsonHan.Chapter03.exists_not_tendsto_fourierProj`: the Fourier series of some
  $f \in C_p(2\pi)$ does not converge uniformly to $f$.
* Theorem 3.7.1, `AtkinsonHan.Chapter03.theorem_3_7_1`: Jackson's theorem for trigonometric
  approximation of $g \in C_p^{k,\alpha}(2\pi)$.
* Equation (3.7.11), `AtkinsonHan.Chapter03.equation_3_7_11`: the Lebesgue lemma combined with
  Jackson's theorem for $\mathcal{F}_n$.
* Equation (3.7.12), `AtkinsonHan.Chapter03.equation_3_7_12`: $\|g - \mathcal{F}_n g\|_\infty \le
  c_k M_k \log n / n^{k+\alpha}$.
* Theorem 3.7.2, `AtkinsonHan.Chapter03.theorem_3_7_2`: Jackson's theorem for polynomial
  approximation of $f \in C^{k,\alpha}[-1, 1]$.
* Equation (3.7.13), `AtkinsonHan.Chapter03.equation_3_7_13`: the least squares projection is
  $P_N u = \sum_n (u, p_n) p_n$.
* Equation (3.7.14), `AtkinsonHan.Chapter03.equation_3_7_14`: the Lebesgue lemma for $P_N$.
* Equations (3.7.15)–(3.7.16), `AtkinsonHan.Chapter03.equation_3_7_15`: $P_N$ is the integral
  operator of the kernel $K(x, t) = \sum_n p_n(x) p_n(t)$.
* Equation (3.7.17), `AtkinsonHan.Chapter03.equation_3_7_17`:
  $\|P_N\| = \max_x \int |K(x, t)|\, dt$.
* Theorem 3.7.3, `AtkinsonHan.Chapter03.theorem_3_7_3` and
  `AtkinsonHan.Chapter03.theorem_3_7_3_confluent`: the Christoffel–Darboux identity for orthonormal
  polynomials, and its confluent case.
* Example 3.7.4, `AtkinsonHan.Chapter03.example_3_7_4`: for the Chebyshev weight, $\|P_N\| = L_N$.
* `AtkinsonHan.Chapter03.norm_chebyshevProj_asymptotics`: $(4/\pi^2) \log N \le \|P_N\| \le 1 +
  \log(2N + 1)$ for the Chebyshev weight.
* Equation (3.7.19), `AtkinsonHan.Chapter03.equation_3_7_19`: the Dirichlet kernel form of
  $\mathcal{I}_n$.
* Equation (3.7.20), `AtkinsonHan.Chapter03.not_equation_3_7_20` and
  `AtkinsonHan.Chapter03.norm_trigInterpCLM_bound`: the printed bound on $\|\mathcal{I}_n\|$ is
  false, and $\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$ holds.
* Equation (3.7.21), `AtkinsonHan.Chapter03.equation_3_7_21`: the Lebesgue lemma combined with
  Jackson's theorem for $\mathcal{I}_n$.
* Equation (3.7.22), `AtkinsonHan.Chapter03.equation_3_7_22`: $\|g - \mathcal{I}_n g\|_\infty \le
  c_k M_k \log n / n^{k+\alpha}$.

## Conventions

* $C_p(2\pi)$ is `AtkinsonHan.Chapter03.PeriodicCont`, the continuous functions on the circle
  $\mathbb{R}/2\pi\mathbb{Z}$ with the uniform norm, from §3.6. A continuous $2\pi$-periodic
  $g : \mathbb{R} \to \mathbb{R}$ enters it through
  `AtkinsonHan.Chapter03.PeriodicCont.ofIsPeriodicCont`.
* The Fourier projection $\mathcal{F}_n$ is `PeriodicCont.fourierProj n`.
* The Lebesgue constant $L_n$ is `PeriodicCont.lebesgueConstant n`.
* The Dirichlet kernel $D_n$ is `dirichletKernel n`.
* The interpolatory projection $\mathcal{I}_n$ is `trigInterpCLM (2 * π) n`.
* The error $\inf_{q \in \mathcal{T}_n} \|g - q\|_\infty$ of the best approximation is written with
  `Metric.infDist`.
* The book's hypothesis $\alpha > 0$ in Theorems 3.7.1 and 3.7.2 and in (3.7.11)–(3.7.22) is kept,
  although the proofs do not use it.

## Deviations from the source

* **Jackson's theorems and the Fourier comparison** (reading). The estimates use infimum
  distances and allow a zero Hölder constant. Equation (3.7.5) uses periodic data on the
  circle with the unnormalized measure. Equation (3.7.9) uses the equality in the following
  sentence of the book.
* **Equations (3.7.13)–(3.7.18)** (generalization and correction). The expansion and row
  norm formulas allow a finite measure and continuous families. The printed integrals in
  (3.7.15) and (3.7.17) omit the weight needed by the weighted expansion. The
  Christoffel–Darboux identity allows finite-moment measures beyond weight densities.
* **Example 3.7.4** (correction). The final integral for the operator norm requires the
  absolute value of the Dirichlet kernel. The orthonormal Chebyshev family determines the
  kernel. See `AtkinsonHan.Chapter03.example_3_7_4`.
* **(3.7.20)** (correction). The book quotes the bound $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$
  for $n \ge 1$. It is false at $n = 1$, where $\|\mathcal{I}_1\| \ge 5/3$. The library proves its
  negation and the bound $\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$. See
  `AtkinsonHan.Chapter03.not_equation_3_7_20` and `AtkinsonHan.Chapter03.norm_trigInterpCLM_bound`.

## Not formalized

* **(3.7.10)**, the asymptotics $L_n = (4/\pi^2) \log n + O(1)$. The backbone proves the two bounds
  $(4/\pi^2) \log n \le L_n \le 1 + \log(2n + 1)$, which is what the divergence argument and the
  convergence rates use (`AtkinsonHan.Chapter03.norm_fourierProj_asymptotics`).
* **The last step of Example 3.7.4**, $\|P_N\| = (4/\pi^2) \log N + O(1)$. It is (3.7.10) applied to
  the identity $\|P_N\| = L_N$, which is `AtkinsonHan.Chapter03.example_3_7_4`.
-/

open Filter Topology

namespace AtkinsonHan.Chapter03

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The Lebesgue lemma -/

/-- The **Lebesgue lemma**. Let $\mathcal{P}$ be a bounded linear operator on a normed space $V$
over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ with $\mathcal{P}^2 = \mathcal{P}$, and let $q$
be in the range of $\mathcal{P}$. Then for every $u \in V$,
$$\|u - \mathcal{P}u\| \le (1 + \|\mathcal{P}\|)\, \|u - q\|.$$

This is the common form of (3.7.11), (3.7.14) and (3.7.21) in [han2009theoretical]: the error of
a projection method is at most $1 + \|\mathcal{P}\|$ times the best approximation error from the
range of $\mathcal{P}$.

**Generalization.** The concrete approximation inequalities in the book follow from this
form for any bounded idempotent on a real or complex normed space. -/
theorem lebesgue_lemma (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) {q : V}
    (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ :=
  norm_sub_apply_le_of_isIdempotentElem_of_mem P hP u hq

/-- The **Lebesgue lemma** with the best approximation error. Let $\mathcal{P}$ be a bounded linear
operator on a normed space $V$ with $\mathcal{P}^2 = \mathcal{P}$. Then for every $u \in V$,
$$\|u - \mathcal{P}u\| \le (1 + \|\mathcal{P}\|) \inf_{w \in \mathcal{P}(V)} \|u - w\|.$$

**Generalization.** Takes the infimum of the comparison errors in the general normed-space
lemma, where the printed projection bound compares to an arbitrary approximation. -/
theorem lebesgue_lemma_iInf (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-- The **Lebesgue lemma** with the constant $\|I - \mathcal{P}\|$, which is at most
$1 + \|\mathcal{P}\|$. Let $\mathcal{P}$ be a bounded linear operator on a normed space $V$ with
$\mathcal{P}^2 = \mathcal{P}$. Then for every $u \in V$,
$$\|u - \mathcal{P}u\| \le \|I - \mathcal{P}\| \inf_{w \in \mathcal{P}(V)} \|u - w\|.$$

**Generalization.** The constant $\|I-P\|$ sharpens the general bound with $1+\|P\|$. -/
theorem lebesgue_lemma_one_sub (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem' P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-! ### Non-convergence from unbounded operator norms -/

/-- Let $V$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$\mathcal{P}_0, \mathcal{P}_1, \ldots$ be bounded linear operators on $V$ whose norms
$\|\mathcal{P}_n\|$ are unbounded. Then there is $f \in V$ such that $\mathcal{P}_n f$ does not
converge to $f$.

This is the argument of the paragraph after (3.7.10) in [han2009theoretical]. Applied to the
Fourier projections $\mathcal{F}_n$ on $C_p(2\pi)$, whose norms are the Lebesgue constants
$L_n$, it gives a continuous periodic function whose Fourier series does not converge uniformly;
see `AtkinsonHan.Chapter03.exists_not_tendsto_fourierProj`. The proof is the backbone's
`ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove` with the identity as the limit
operator.

**Generalization.** The book argues for the Fourier projections. The uniform boundedness
argument applies to any sequence of bounded linear operators on a Banach space. -/
theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] (P : ℕ → V →L[𝕜] V)
    (h : ¬ BddAbove (Set.range fun n => ‖P n‖)) :
    ∃ f : V, ¬ Tendsto (fun n => P n f) atTop (𝓝 f) :=
  ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove h (ContinuousLinearMap.id 𝕜 V)

/-!
### The Hölder classes of Theorems 3.7.1 and 3.7.2

The space $C_p(2\pi)$ on which these classes live, with the passage between periodic functions on
$\mathbb{R}$ and functions on the circle, is defined in §3.6, where Example 3.6.8 first needs it.
-/

section Spaces

open Real NNReal

/-- The class $C_p^{k,\alpha}(2\pi)$ of [han2009theoretical], with Hölder constant $M$. A function
$g : \mathbb{R} \to \mathbb{R}$ is in the class if it is continuous and $2\pi$-periodic, $k$
times continuously differentiable, and its $k$-th derivative satisfies
$$|g^{(k)}(x) - g^{(k)}(y)| \le M |x - y|^\alpha \quad \text{for all } x, y \in \mathbb{R}.$$

Here $\alpha, M \ge 0$, and the Hölder condition is Mathlib's `HolderWith M α`.

**Reading.** The predicate also permits $M=0$ and arbitrary nonnegative exponents. The Jackson
estimates separately require $0<\alpha\le 1$. -/
def HolderClass (k : ℕ) (α M : ℝ≥0) (g : ℝ → ℝ) : Prop :=
  IsPeriodicCont g ∧ ContDiff ℝ k g ∧ HolderWith M α (iteratedDeriv k g)

/-- The class $C^{k,\alpha}[-1, 1]$ of [han2009theoretical], with Hölder constant $M$, used in
Theorem 3.7.2. A function $f : \mathbb{R} \to \mathbb{R}$ is in the class if it is $k$ times
continuously differentiable on $[-1, 1]$ and its $k$-th derivative within $[-1, 1]$ satisfies
$$|f^{(k)}(x) - f^{(k)}(y)| \le M |x - y|^\alpha \quad \text{for all } x, y \in [-1, 1].$$

The derivative is `iteratedDerivWithin k f (Set.Icc (-1) 1)`, which is one-sided at the
endpoints.

**Reading.** The predicate also permits $M=0$ and arbitrary nonnegative exponents. The Jackson
estimates separately require $0<\alpha\le 1$. -/
def HolderClassIcc (k : ℕ) (α M : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ k f (Set.Icc (-1) 1) ∧
    HolderOnWith M α (iteratedDerivWithin k f (Set.Icc (-1) 1)) (Set.Icc (-1) 1)

end Spaces

/-! ### (3.7.6)–(3.7.9): the Fourier projection and the Lebesgue constants -/

section FourierProjection

open Real _root_.PeriodicCont

/-- **Equation (3.7.6)** of [han2009theoretical]. Let $f \in C_p(2\pi)$ and $n \ge 0$. The $n$-th
partial sum $\mathcal{F}_n f$ of the Fourier series of $f$ is the integral of $f$ against the
Dirichlet kernel $D_n$: for every $x \in \mathbb{R}$,
$$\mathcal{F}_n f(x) = \frac{1}{\pi} \int_{-\pi}^{\pi} D_n(x - y) f(y)\, dy.$$
-/
theorem equation_3_7_6 (n : ℕ) (f : PeriodicCont) (x : ℝ) :
    fourierProj n f ↑x = 1 / π * ∫ y in -π..π, dirichletKernel n (x - y) * f ↑y := by
  have hf : Function.Periodic (fun t : ℝ => f ↑t) (2 * π) := fun t => by
    simp only []
    rw [AddCircle.coe_add_period]
  have hper : Function.Periodic (fun y : ℝ => dirichletKernel n (x - y) * f ↑y) (2 * π) := by
    intro y
    have h1 : dirichletKernel n (x - (y + 2 * π)) = dirichletKernel n (x - y) := by
      rw [show x - (y + 2 * π) = (x - y) - 2 * π by ring]
      exact (dirichletKernel_periodic n).sub_eq (x - y)
    have h2 : f ((y + 2 * π : ℝ) : AddCircle (2 * π)) = f ((y : ℝ) : AddCircle (2 * π)) := hf y
    simp only []
    rw [h1, h2]
  have hshift : (∫ y in -π..π, dirichletKernel n (x - y) * f ↑y)
      = ∫ r in -π..π, dirichletKernel n r * f ↑(x + r) := by
    have h1 := hper.intervalIntegral_add_eq (-π) (x + -π)
    rw [show -π + 2 * π = π by ring, show x + -π + 2 * π = x + π by ring] at h1
    rw [h1, ← intervalIntegral.integral_comp_add_left
      (fun y : ℝ => dirichletKernel n (x - y) * f ↑y) x]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [show x - (x + r) = -r by ring, dirichletKernel_neg]
  rw [hshift, fourierProj_apply, integral_addCircle_eq
    (fun y => fourierKernel n (↑x, y) * f y) x, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hsub : ((↑(x + r) : AddCircle (2 * π)) - ↑x) = ((r : ℝ) : AddCircle (2 * π)) := by
    have h : ((↑(x + r) : AddCircle (2 * π))) = (↑x : AddCircle (2 * π)) + ↑r := rfl
    rw [h, add_sub_cancel_left]
  simp only [fourierKernel_apply, hsub, dirichletCM_coe]
  field_simp

/-- **Equations (3.7.7)–(3.7.8)** of [han2009theoretical]. Let $n \ge 0$ and let $t \in \mathbb{R}$
with $\sin(t/2) \neq 0$. Then the Dirichlet kernel satisfies
$$D_n(t) = \frac{1}{2} + \sum_{j=1}^{n} \cos(jt) = \frac{\sin((n + 1/2) t)}{2 \sin(t/2)}.$$

The first equality is the definition of `dirichletKernel` and holds for all $t$.

**Reading.** The two formulas are bundled under the nonvanishing denominator hypothesis.
The finite cosine sum alone is valid for every argument. -/
theorem equation_3_7_8 (n : ℕ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel n t = 1 / 2 + ∑ j ∈ Finset.Icc 1 n, Real.cos (j * t) ∧
      dirichletKernel n t = Real.sin ((n + 1 / 2) * t) / (2 * Real.sin (t / 2)) :=
  ⟨dirichletKernel_apply n t, dirichletKernel_eq_sin_div ht⟩

/-- **Equation (3.7.9)** of [han2009theoretical]. For $n \ge 0$, the norm of the Fourier projection
$\mathcal{F}_n$ on $C_p(2\pi)$ is the $n$-th Lebesgue constant
$$\|\mathcal{F}_n\| = L_n = \frac{2}{\pi} \int_0^\pi |D_n(t)|\, dt.$$

That $\mathcal{F}_n$ is a bounded projection onto $\mathcal{T}_n$ is
`AtkinsonHan.Chapter03.example_3_6_8`.

**Reading.** The printed display gives an upper bound. The next sentence states equality,
which is the form proved here. -/
theorem equation_3_7_9 (n : ℕ) :
    ‖fourierProj n‖ = 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  rw [norm_fourierProj, lebesgueConstant_eq]

/-- For $n \ge 0$, the norm of the Fourier projection $\mathcal{F}_n$ on $C_p(2\pi)$ satisfies
$$\frac{4}{\pi^2} \log n \le \|\mathcal{F}_n\| \le 1 + \log(2n + 1).$$
So the Lebesgue constants $L_n = \|\mathcal{F}_n\|$ are of exact order $\log n$. This two-sided
bound stands in for Zygmund's asymptotics (3.7.10) of [han2009theoretical],
$L_n = (4/\pi^2) \log n + O(1)$, which is not formalized.

The lower bound makes the norms unbounded, and so gives a continuous periodic function whose
Fourier series does not converge uniformly
(`AtkinsonHan.Chapter03.exists_not_tendsto_fourierProj`). The upper bound gives the convergence
rate (3.7.12). At $n = 0$ the left side is $0$, since `Real.log 0 = 0`.

**Reading.** The bounds give logarithmic growth and imply the divergence result, without
asserting the bounded remainder in the sharper source formula (3.7.10). -/
theorem norm_fourierProj_asymptotics (n : ℕ) :
    4 / π ^ 2 * Real.log n ≤ ‖fourierProj n‖ ∧
      ‖fourierProj n‖ ≤ 1 + Real.log (2 * (n : ℝ) + 1) := by
  rw [norm_fourierProj]
  exact ⟨log_le_lebesgueConstant n, lebesgueConstant_le n⟩

/-- **Equation (3.7.5)** of [han2009theoretical]. Let $f \in C_p(2\pi)$ and $n \ge 0$. Then
$$\|f - \mathcal{F}_n f\|_{L^2(-\pi, \pi)} \le \sqrt{2\pi}\, \|f - \mathcal{F}_n f\|_\infty.$$

The $L^2$ norm is taken for the standard measure `volume` of the circle
$\mathbb{R}/2\pi\mathbb{Z}$, which has total mass $2\pi$ and is the Lebesgue measure of one
period. The constant $\sqrt{2\pi}$ is the square root of that mass. The inequality holds for
$f - q$ with any $q \in C_p(2\pi)$, not only for $q = \mathcal{F}_n f$.

**Reading.** The book's displayed comparison allows continuous data on $[-\pi,\pi]$.
This version uses continuous periodic data on the circle with the unnormalized measure. -/
theorem equation_3_7_5 (n : ℕ) (f : PeriodicCont) :
    ‖ContinuousMap.toLp (E := ℝ) 2 (MeasureTheory.volume : MeasureTheory.Measure
        (AddCircle (2 * π))) ℝ (f - fourierProj n f)‖
      ≤ √(2 * π) * ‖f - fourierProj n f‖ := by
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  have hmass : (MeasureTheory.measureUnivNNReal
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (2 * π))) : ℝ) = 2 * π := by
    rw [MeasureTheory.measureUnivNNReal, AddCircle.measure_univ, ENNReal.ofReal,
      ENNReal.toNNReal_coe, Real.coe_toNNReal _ h2pi]
  have hop : ‖(ContinuousMap.toLp (E := ℝ) 2 (MeasureTheory.volume : MeasureTheory.Measure
      (AddCircle (2 * π))) ℝ)‖ ≤ √(2 * π) := by
    refine (ContinuousMap.toLp_norm_le (E := ℝ) (p := 2) (𝕜 := ℝ)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (2 * π))))).trans ?_
    rw [Real.sqrt_eq_rpow, hmass]
    norm_num
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- **Section 3.7** of [han2009theoretical], the paragraph after (3.7.10). There is a function
$f \in C_p(2\pi)$ whose Fourier series does not converge uniformly to $f$:
$\|f - \mathcal{F}_n f\|_\infty \not\to 0$.

The Lebesgue constants $L_n = \|\mathcal{F}_n\|$ grow like $\log n$
(`AtkinsonHan.Chapter03.norm_fourierProj_asymptotics`), so they are unbounded, and
`AtkinsonHan.Chapter03.exists_not_tendsto_of_not_bddAbove` gives $f$. -/
theorem exists_not_tendsto_fourierProj :
    ∃ f : PeriodicCont, ¬ Tendsto (fun n => fourierProj n f) atTop (𝓝 f) := by
  refine exists_not_tendsto_of_not_bddAbove (fun n => fourierProj n) fun hbd => ?_
  obtain ⟨C, hC⟩ := hbd
  have hlog : Tendsto (fun n : ℕ => 4 / π ^ 2 * Real.log n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := (hlog.eventually_gt_atTop C).exists
  exact absurd (hC ⟨n, rfl⟩) (not_le.2 (lt_of_lt_of_le hn (norm_fourierProj_asymptotics n).1))

end FourierProjection

/-! ### Section 3.7.3 and (3.7.19): the trigonometric interpolatory projection -/

section TrigonometricInterpolation

open Real _root_.PeriodicCont

/-- **Equation (3.7.19)** of [han2009theoretical]. Let $n \ge 0$, let $x_j = 2\pi j / (2n + 1)$ for
$j = 0, \ldots, 2n$ be the equispaced nodes of (3.2.16), and let $\mathcal{I}_n f$ be the
trigonometric polynomial of degree at most $n$ that interpolates $f \in C_p(2\pi)$ at these
nodes. Then for every $x \in \mathbb{R}$,
$$\mathcal{I}_n f(x) = \frac{2}{2n + 1} \sum_{j=0}^{2n} D_n(x - x_j) f(x_j).$$

This is the discrete analogue of the formula (3.7.6) for the Fourier projection: the cardinal
functions of the interpolation problem are $2 D_n(x - x_j) / (2n + 1)$ (Exercise 3.7.5). The
operator is `trigInterpCLM (2 * π) n`, and $x_j$ is `trigInterpNode (2 * π) n j`. The bound on
$\|\mathcal{I}_n\|$ that the book pairs with this formula is
`AtkinsonHan.Chapter03.norm_trigInterpCLM_bound`; `AtkinsonHan.Chapter03.not_equation_3_7_20`
shows why it is not the bound that (3.7.20) prints. -/
theorem equation_3_7_19 (n : ℕ) (f : PeriodicCont) (x : ℝ) :
    trigInterpCLM (2 * π) n f ↑x
      = 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          dirichletKernel n (x - (j : ℕ) * (2 * π) / (2 * n + 1)) *
            f (trigInterpNode (2 * π) n j) :=
  trigInterpCLM_coe_apply n f x

end TrigonometricInterpolation

/-! ### Theorem 3.7.1 and (3.7.11)–(3.7.12): Jackson's theorem and the Fourier series -/

section JacksonTheorem

open Real NNReal _root_.PeriodicCont

set_option linter.unusedVariables false in
/-- **Theorem 3.7.1** of [han2009theoretical] (Jackson's theorem). Let $k \ge 0$, $n \ge 1$ and
$0 < \alpha \le 1$, and let $g \in C_p^{k,\alpha}(2\pi)$ with Hölder constant $M_k \ge 0$: $g$
is $2\pi$-periodic and $k$ times continuously differentiable, and $|g^{(k)}(\theta_1) -
g^{(k)}(\theta_2)| \le M_k |\theta_1 - \theta_2|^\alpha$. Then the error of the best uniform
approximation of $g$ from $\mathcal{T}_n$ satisfies
$$\inf_{q \in \mathcal{T}_n} \|g - q\|_\infty \le \frac{c^{k+1} M_k}{n^{k+\alpha}}, \qquad c =
  1 + \frac{\pi^2}{2}.$$

The hypothesis $\alpha > 0$ is the book's, and the proof does not use it: the bound also holds
for $\alpha = 0$. The book requires $M_k > 0$; the statement also allows $M_k = 0$. The proof
specializes the backbone's `Jackson.infDist_le_of_holder_deriv'`.

**Reading.** The bound is on the infimum distance to the trigonometric subspace, which is the
error of the best approximant. The declaration allows $M=0$ and requires $n\ge 1$ explicitly. -/
theorem theorem_3_7_1 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
        (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ))
      ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  obtain ⟨hper, hcd, hhol⟩ := hg
  have hlift : _root_.Jackson.lift (PeriodicCont.ofIsPeriodicCont hper) = g :=
    funext fun x => PeriodicCont.ofIsPeriodicCont_coe hper x
  refine _root_.Jackson.infDist_le_of_holder_deriv' (D := fun j => iteratedDeriv j g) hn ?_ ?_ ?_
    M.coe_nonneg α.coe_nonneg (by exact_mod_cast hα1) ?_
  · rw [iteratedDeriv_zero, hlift]
  · exact fun j hj => hcd.continuous_iteratedDeriv j (by exact_mod_cast hj)
  · intro j hj x
    have hdiff : Differentiable ℝ (iteratedDeriv j g) :=
      hcd.differentiable_iteratedDeriv j (by exact_mod_cast hj)
    have h := (hdiff x).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  · intro u v
    have h := hhol.dist_le u v
    rwa [Real.dist_eq, Real.dist_eq] at h

set_option linter.unusedVariables false in
/-- **Theorem 3.7.2** of [han2009theoretical] (Jackson's theorem, polynomial case). Let
$0 \le k < n$ and $0 < \alpha \le 1$, and let $f \in C^{k,\alpha}[-1, 1]$ with Hölder constant
$M_k \ge 0$: $f$ is $k$ times continuously differentiable on $[-1, 1]$, and $|f^{(k)}(x_1) -
f^{(k)}(x_2)| \le M_k |x_1 - x_2|^\alpha$ for $x_1, x_2 \in [-1, 1]$. Let $d_k \ge 0$ satisfy
$$d_k \ge \frac{n^{k+\alpha}}{n (n - 1) \cdots (n - k + 1)\, (n - k)^\alpha}.$$
Then the error of the best uniform approximation of $f$ from the polynomials $\mathcal{P}_n$ of
degree at most $n$ satisfies
$$\inf_{p \in \mathcal{P}_n} \max_{-1 \le x \le 1} |f(x) - p(x)| \le \frac{d_k\, c^{k+1}
  M_k}{n^{k+\alpha}}, \qquad c = 1 + \frac{\pi^2}{2}.$$

The $k$-th derivative is `iteratedDerivWithin k f (Set.Icc (-1) 1)`, which is one-sided at the
two endpoints; this is what `ContDiffOn` on a closed interval provides. As in Theorem 3.7.1, the
hypothesis $\alpha > 0$ is the book's and is not used. The backbone proof transfers the problem
to the trigonometric case through the substitution $x = \cos\theta$ and then uses a recursion in
the degree, which for algebraic polynomials loses nothing. It proves the smaller
constant $(\pi^2/2)^{k+1}$ in place of $c^{k+1}$; see `Jackson.infDist_le_of_holder_poly`.

**Reading.** The bound is on the infimum distance to the polynomial subspace. The constant
bound is assumed for the given degree and $M$ may be zero. -/
theorem theorem_3_7_2 {k n : ℕ} {α M d : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hkn : k < n)
    {f : ℝ → ℝ} (hf : HolderClassIcc k α M f)
    (hd : (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) /
        ((∏ i ∈ Finset.range k, ((n : ℝ) - i)) * ((n : ℝ) - k) ^ (α : ℝ)) ≤ (d : ℝ)) :
    Metric.infDist (_root_.Jackson.restrictIcc hf.1.continuousOn)
        (_root_.polyLE (Set.Icc (-1 : ℝ) 1) n : Set C(Set.Icc (-1 : ℝ) 1, ℝ))
      ≤ (d : ℝ) * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hs : UniqueDiffOn ℝ (Set.Icc (-1 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  refine _root_.Jackson.infDist_le_of_holder_poly
    (D := fun j => iteratedDerivWithin j f (Set.Icc (-1 : ℝ) 1)) ?_ ?_ ?_
    M.coe_nonneg α.coe_nonneg (by exact_mod_cast hα1) ?_ hkn hd
  · intro x
    rw [iteratedDerivWithin_zero]
    rfl
  · intro j hj
    exact hf.1.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  · intro j hj x hx
    rw [iteratedDerivWithin_succ]
    exact (hf.1.differentiableOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj) hs
      x hx).hasDerivWithinAt
  · intro u hu v hv
    have h := hf.2.dist_le hu hv
    rwa [Real.dist_eq, Real.dist_eq] at h

/-- **Equation (3.7.11)** of [han2009theoretical]. Let $k \ge 0$, $n \ge 1$ and $0 < \alpha \le 1$,
and let $g \in C_p^{k,\alpha}(2\pi)$ with Hölder constant $M_k$. Then the Lebesgue lemma and
Jackson's theorem give
$$\|g - \mathcal{F}_n g\|_\infty \le (1 + \|\mathcal{F}_n\|)\, \frac{c^{k+1} M_k}{n^{k+\alpha}},
  \qquad c = 1 + \frac{\pi^2}{2}.$$
-/
theorem equation_3_7_11 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖fourierProj n‖) *
        ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) := by
  have h := norm_sub_fourierProj_le n (PeriodicCont.ofIsPeriodicCont hg.1)
  rw [← norm_fourierProj] at h
  exact h.trans (mul_le_mul_of_nonneg_left (theorem_3_7_1 hα0 hα1 hn hg) (by positivity))

/-- **Equation (3.7.12)** of [han2009theoretical]. Let $k \ge 0$ and $0 < \alpha \le 1$. There is a
constant $c_k > 0$, which depends only on $k$ and $\alpha$, such that for every $M_k \ge 0$,
every $g \in C_p^{k,\alpha}(2\pi)$ with Hölder constant $M_k$, and every $n \ge 2$,
$$\|g - \mathcal{F}_n g\|_\infty \le \frac{c_k M_k \log n}{n^{k+\alpha}}.$$

The constant is explicit in the proof, because the bound $L_n \le 1 + \log(2n + 1)$ on the
Lebesgue constants is.

**Reading.** The constant is split into a positive constant independent of the Hölder
constant and function, and the explicit factor $M$. -/
theorem equation_3_7_12 (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℝ≥0) (g : ℝ → ℝ) (hg : HolderClass k α M g) (n : ℕ), 2 ≤ n →
      ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
        ≤ c * (M : ℝ) * Real.log n / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set c₀ : ℝ := 1 + (2 + Real.log 3) / Real.log 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hcpos : 0 < c₀ * (1 + π ^ 2 / 2) ^ (k + 1) := by
    refine mul_pos hc₀pos (pow_pos ?_ _)
    positivity
  refine ⟨c₀ * (1 + π ^ 2 / 2) ^ (k + 1), hcpos, fun M g hg n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn
  -- the Lebesgue constants grow at most like `log n`
  have hleb : 1 + ‖fourierProj n‖ ≤ c₀ * Real.log n := by
    rw [norm_fourierProj]
    have h1 := lebesgueConstant_le n
    have h2 : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      have h3 : (2 : ℝ) * (n : ℝ) + 1 ≤ 3 * (n : ℝ) := by linarith
      calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
            Real.log_le_log (by linarith) h3
        _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
    have h4 : (2 : ℝ) + Real.log 3 ≤ (2 + Real.log 3) / Real.log 2 * Real.log n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    rw [hc₀]
    nlinarith
  -- Jackson's theorem
  have hjack := theorem_3_7_1 hα0 hα1 hn1 hg
  have hden : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hnum : (0 : ℝ) ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) := by positivity
  have h := norm_sub_fourierProj_le n (PeriodicCont.ofIsPeriodicCont hg.1)
  rw [← norm_fourierProj] at h
  calc ‖PeriodicCont.ofIsPeriodicCont hg.1 - fourierProj n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖fourierProj n‖) *
          Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
            (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) := h
    _ ≤ (c₀ * Real.log n) *
          ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) := by
        refine mul_le_mul hleb hjack (Metric.infDist_nonneg) (by positivity)
    _ = c₀ * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) * Real.log n /
          (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
        field_simp

end JacksonTheorem

/-! ### (3.7.21)–(3.7.22): the convergence of trigonometric interpolation -/

section TrigonometricInterpolationRate

open Real NNReal _root_.PeriodicCont

/-- **Equation (3.7.21)** of [han2009theoretical]. Let $k \ge 0$, $n \ge 1$ and $0 < \alpha \le 1$,
and let $g \in C_p^{k,\alpha}(2\pi)$ with Hölder constant $M_k$. Then the Lebesgue lemma for the
interpolatory projection $\mathcal{I}_n$ and Jackson's theorem give
$$\|g - \mathcal{I}_n g\|_\infty \le (1 + \|\mathcal{I}_n\|)\, \frac{c^{k+1} M_k}{n^{k+\alpha}},
  \qquad c = 1 + \frac{\pi^2}{2}.$$

No bound on $\|\mathcal{I}_n\|$ enters here: the statement is about the operator norm itself, as
in the book. -/
theorem equation_3_7_21 {k n : ℕ} {α M : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : HolderClass k α M g) :
    ‖PeriodicCont.ofIsPeriodicCont hg.1
        - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖trigInterpCLM (2 * π) n‖) *
        ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) :=
  (norm_sub_trigInterpCLM_le n _).trans
    (mul_le_mul_of_nonneg_left (theorem_3_7_1 hα0 hα1 hn hg) (by positivity))

/-- **Equation (3.7.20)** of [han2009theoretical] is false as printed. It is not true that
$\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$ for all $n \ge 1$.

**Correction.** The book quotes Rivlin for the bound $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$
for $n \ge 1$. At $n = 1$ its right side is $1$, but the Lebesgue function of interpolation at
the three nodes $0, 2\pi/3, 4\pi/3$ takes the value $5/3$ at $\pi/3$, so
$\|\mathcal{I}_1\| \ge 5/3$ (`le_norm_trigInterpCLM_one`). Rivlin's $n$ counts the interpolation
nodes, which here number $2n + 1$. The bound proved in its place is
`AtkinsonHan.Chapter03.norm_trigInterpCLM_bound`. -/
theorem not_equation_3_7_20 :
    ¬ ∀ n : ℕ, 1 ≤ n → ‖trigInterpCLM (2 * π) n‖ ≤ 1 + 2 / π * Real.log n := by
  intro h
  have h1 := h 1 le_rfl
  rw [Nat.cast_one, Real.log_one, mul_zero, add_zero] at h1
  linarith [le_norm_trigInterpCLM_one]

/-- **Equation (3.7.20)** of [han2009theoretical], in a form that holds. For every $n \ge 0$,
$$\|\mathcal{I}_n\| \le 2 + \frac{2}{\pi} \log(2n + 1).$$

**Correction.** The book prints $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$, which is false
(`AtkinsonHan.Chapter03.not_equation_3_7_20`). The bound here keeps the coefficient $2/\pi$ of
the printed bound, which is sharp, and so gives the same $O(\log n)$ growth. The additive
constant is $2$ instead of $1$, one unit for each of the two nodes nearest the evaluation point.
The sharp statement $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log(2n + 1)$ is not proved: its two
sides differ by about $0.04$ for every $n$.

This is the backbone's `norm_trigInterpCLM_le`. -/
theorem norm_trigInterpCLM_bound (n : ℕ) :
    ‖trigInterpCLM (2 * π) n‖ ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 1) :=
  norm_trigInterpCLM_le n

/-- **Equation (3.7.22)** of [han2009theoretical]. Let $k \ge 0$ and $0 < \alpha \le 1$. There is a
constant $c_k > 0$, which depends only on $k$ and $\alpha$, such that for every $M_k \ge 0$,
every $g \in C_p^{k,\alpha}(2\pi)$ with Hölder constant $M_k$, and every $n \ge 2$,
$$\|g - \mathcal{I}_n g\|_\infty \le \frac{c_k M_k \log n}{n^{k+\alpha}}.$$

The constant is explicit in the proof, because the bound
$\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$ is.

**Reading.** The source's linear dependence on the Hölder constant is written as an
explicit factor $M$, with the remaining constant independent of the function. -/
theorem equation_3_7_22 (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℝ≥0) (g : ℝ → ℝ) (hg : HolderClass k α M g) (n : ℕ), 2 ≤ n →
      ‖PeriodicCont.ofIsPeriodicCont hg.1
          - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
        ≤ c * (M : ℝ) * Real.log n / (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set c₀ : ℝ := 1 + (3 + Real.log 3) / Real.log 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hcpos : 0 < c₀ * (1 + π ^ 2 / 2) ^ (k + 1) := by
    refine mul_pos hc₀pos (pow_pos ?_ _)
    positivity
  refine ⟨c₀ * (1 + π ^ 2 / 2) ^ (k + 1), hcpos, fun M g hg n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn
  -- the norms of the interpolation projections grow at most like `log n`
  have hleb : 1 + ‖trigInterpCLM (2 * π) n‖ ≤ c₀ * Real.log n := by
    have h1 := norm_trigInterpCLM_le n
    have hlogNnn : 0 ≤ Real.log (2 * (n : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogN : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      calc Real.log (2 * (n : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log n := Real.log_mul (by norm_num) (by linarith)
    have hpi2 : (2 : ℝ) / π ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      exact Real.two_le_pi
    have h2 : 2 / π * Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
      nlinarith
    have h4 : (3 : ℝ) + Real.log 3 ≤ (3 + Real.log 3) / Real.log 2 * Real.log n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    rw [hc₀]
    nlinarith
  -- Jackson's theorem
  have hjack := theorem_3_7_1 hα0 hα1 hn1 hg
  have hden : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hnum : (0 : ℝ) ≤ (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) := by positivity
  calc ‖PeriodicCont.ofIsPeriodicCont hg.1
          - trigInterpCLM (2 * π) n (PeriodicCont.ofIsPeriodicCont hg.1)‖
      ≤ (1 + ‖trigInterpCLM (2 * π) n‖) *
          Metric.infDist (PeriodicCont.ofIsPeriodicCont hg.1)
            (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) :=
        norm_sub_trigInterpCLM_le n _
    _ ≤ (c₀ * Real.log n) *
          ((1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) / (n : ℝ) ^ ((k : ℝ) + (α : ℝ))) :=
        mul_le_mul hleb hjack Metric.infDist_nonneg (by positivity)
    _ = c₀ * (1 + π ^ 2 / 2) ^ (k + 1) * (M : ℝ) * Real.log n /
          (n : ℝ) ^ ((k : ℝ) + (α : ℝ)) := by
        field_simp

end TrigonometricInterpolationRate

/-! ### Theorem 3.7.3: the Christoffel–Darboux identity -/

section ChristoffelDarboux

open MeasureTheory OrthogonalPolynomial Polynomial

variable {μ : MeasureTheory.Measure ℝ}

/-- **Theorem 3.7.3** of [han2009theoretical] (Christoffel–Darboux identity). Let $\mu$ be a measure
on $\mathbb{R}$ with finite moments that no finite set carries, and let $p_0, p_1, \ldots$ be
its orthonormal polynomials, with leading coefficients $A_n$. Let $N \ge 0$,
$a_N = A_{N+1} / A_N$, and $x, t \in \mathbb{R}$ with $x \neq t$. Then
$$\sum_{n=0}^{N} p_n(x) p_n(t) = \frac{p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t)}{a_N (x - t)}.$$

The hypothesis on $\mu$ is `OrthogonalPolynomial.IsWeight`, and $p_n$ is
`OrthogonalPolynomial.orthonormalFamily μ n`, the monic orthogonal polynomial scaled to norm $1$
in $L^2(\mu)$.

**Generalization.** The book uses a weight density. The theorem applies to any measure with
finite moments whose mass is not carried by a finite set. -/
theorem theorem_3_7_3 (hw : IsWeight μ) (N : ℕ) {x t : ℝ} (hxt : x ≠ t) :
    ∑ n ∈ Finset.range (N + 1),
        (orthonormalFamily μ n).eval x * (orthonormalFamily μ n).eval t
      = ((orthonormalFamily μ (N + 1)).eval x * (orthonormalFamily μ N).eval t
          - (orthonormalFamily μ N).eval x * (orthonormalFamily μ (N + 1)).eval t)
        / ((orthonormalFamily μ (N + 1)).leadingCoeff /
            (orthonormalFamily μ N).leadingCoeff * (x - t)) := by
  rw [← cdA_eq_leadingCoeff_div hw]
  exact Polynomial.christoffel_darboux_div (orthonormalFamily_one hw)
    (orthonormalFamily_recurrence hw) (cdC_mul_cdA hw) N (cdA_pos hw N).ne' hxt

/-- **Theorem 3.7.3** of [han2009theoretical], the confluent case $x = t$. Let $\mu$, $p_n$ and
$a_N$ be as in `AtkinsonHan.Chapter03.theorem_3_7_3`. Then for every $t \in \mathbb{R}$,
$$\sum_{n=0}^{N} p_n(t)^2 = \frac{p_{N+1}'(t) p_N(t) - p_N'(t) p_{N+1}(t)}{a_N}.$$

**Generalization.** The same finite-moment measure assumptions replace the book's weight
density as in the off-diagonal case. -/
theorem theorem_3_7_3_confluent (hw : IsWeight μ) (N : ℕ) (t : ℝ) :
    ∑ n ∈ Finset.range (N + 1), (orthonormalFamily μ n).eval t ^ 2
      = ((derivative (orthonormalFamily μ (N + 1))).eval t * (orthonormalFamily μ N).eval t
          - (derivative (orthonormalFamily μ N)).eval t *
            (orthonormalFamily μ (N + 1)).eval t)
        / ((orthonormalFamily μ (N + 1)).leadingCoeff /
            (orthonormalFamily μ N).leadingCoeff) := by
  rw [← cdA_eq_leadingCoeff_div hw]
  exact Polynomial.christoffel_darboux_confluent_div (orthonormalFamily_one hw)
    (orthonormalFamily_recurrence hw) (cdC_mul_cdA hw) N t (cdA_pos hw N).ne'

end ChristoffelDarboux

/-! ### (3.7.13)–(3.7.17) and Example 3.7.4: least squares projections on $C[-1, 1]$ -/

section LeastSquares

open MeasureTheory Real Approximation _root_.PeriodicCont

/-- The interval $[-1, 1]$ is nonempty, so the norm formula (3.7.17) applies to operators on
$C[-1, 1]$. -/
instance : Nonempty (Set.Icc (-1 : ℝ) 1) :=
  Set.nonempty_coe_sort.2 (Set.nonempty_Icc.2 (by norm_num))

variable {N : ℕ} (μ : Measure (Set.Icc (-1 : ℝ) 1)) [IsFiniteMeasure μ]
  (p : Fin (N + 1) → C(Set.Icc (-1 : ℝ) 1, ℝ))

/-- **Equation (3.7.13)** of [han2009theoretical]. Let $\mu$ be a finite measure on $[-1, 1]$, let
$p_0, \ldots, p_N \in C[-1, 1]$, and let $P_N$ be the integral operator on $C[-1, 1]$ with
kernel $K(x, t) = \sum_{n=0}^{N} p_n(x) p_n(t)$. Then for every $u \in C[-1, 1]$,
$$P_N u = \sum_{n=0}^{N} \xi_n p_n, \qquad \xi_n = \int u(t) p_n(t)\, d\mu(t) = (u,
  p_n)_{0,w}.$$

When the $p_n$ are orthonormal in $L^2(\mu)$, $P_N$ is the least squares projection onto their
span. The book takes $\mu = w(x)\, dx$ and the $p_n$ the orthonormal polynomials of the weight
$w$; the statement here uses only that the $p_n$ are continuous. The operator is
`Approximation.expansionCLM μ p`.

**Generalization.** The expansion formula works with any finite measure and continuous
family. The orthonormal polynomial setting gives the projection interpretation. -/
theorem equation_3_7_13 (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) :
    expansionCLM μ p u = ∑ n, (∫ t, u t * p n t ∂μ) • p n :=
  expansionCLM_eq_sum μ p u

/-- **Equation (3.7.14)** of [han2009theoretical], the Lebesgue lemma for the least squares
projection. Let $\mu$ be a finite measure on $[-1, 1]$, let $p_0, \ldots, p_N \in C[-1, 1]$ be
orthonormal in $L^2(\mu)$, and let $P_N$ be the least squares projection onto their span. Then
for every $u \in C[-1, 1]$,
$$\|u - P_N u\|_\infty \le (1 + \|P_N\|) \inf_{q \in \operatorname{span}\{p_n\}} \|u -
  q\|_\infty.$$

Orthonormality is `Approximation.IsOrthonormal μ p`.

**Generalization.** The comparison applies to the span of any finite orthonormal
continuous family for a finite measure. It takes the infimum over comparison functions. -/
theorem equation_3_7_14 (h : IsOrthonormal μ p) (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) :
    ‖u - expansionCLM μ p u‖
      ≤ (1 + ‖expansionCLM μ p‖) *
          Metric.infDist u (Submodule.span ℝ (Set.range p) : Set C(Set.Icc (-1 : ℝ) 1, ℝ)) :=
  h.norm_sub_expansionCLM_le u

/-- **Equations (3.7.15)–(3.7.16)** of [han2009theoretical]. Let $\mu$ be a finite measure on
$[-1, 1]$ and let $p_0, \ldots, p_N \in C[-1, 1]$. Then the operator $P_N$ of (3.7.13) is the
integral operator of the kernel $K(x, t) = \sum_{n=0}^{N} p_n(x) p_n(t)$: for all
$u \in C[-1, 1]$ and $x \in [-1, 1]$,
$$P_N u(x) = \int K(x, t)\, u(t)\, d\mu(t).$$

**Correction.** Equation (3.7.15) integrates against plain $dt$. Its expansion in (3.7.13)
uses the weighted inner product, so the kernel must be integrated against $w(t)\,dt$.
The declaration states this for an arbitrary finite measure and continuous family. -/
theorem equation_3_7_15 (u : C(Set.Icc (-1 : ℝ) 1, ℝ)) (x : Set.Icc (-1 : ℝ) 1) :
    expansionCLM μ p u x = ∫ t, (∑ n, p n x * p n t) * u t ∂μ :=
  rfl

/-- **Equation (3.7.17)** of [han2009theoretical]. Let $\mu$ be a finite measure on $[-1, 1]$ and
let $p_0, \ldots, p_N \in C[-1, 1]$. Then the norm of the operator $P_N$ of (3.7.13) on
$C[-1, 1]$ is the largest row integral of its kernel:
$$\|P_N\| = \sup_{x \in [-1, 1]} \int |K(x, t)|\, d\mu(t).$$

This is (2.2.8), the norm of an integral operator with continuous kernel, applied to (3.7.15).

**Correction.** The weight must also enter the row integral in the norm formula. The
formal supremum is a maximum by compactness and continuity of the row integral. -/
theorem equation_3_7_17 :
    ‖expansionCLM μ p‖ = ⨆ x, ∫ t, |∑ n, p n x * p n t| ∂μ :=
  norm_expansionCLM μ p

/-! ### Example 3.7.4: the Chebyshev least squares projection -/

/-- **Example 3.7.4** of [han2009theoretical]. Let $P_N$ be the least squares projection on
$C[-1, 1]$ for the Chebyshev weight $(1 - x^2)^{-1/2}$, onto the span of the orthonormal
Chebyshev polynomials of degree at most $N$. Then its norm is exactly the $N$-th Lebesgue
constant of the Fourier projection:
$$\|P_N\| = L_N.$$

The proof is the book's derivation. The change of variables $x = \cos\theta$, $t = \cos\varphi$
turns the kernel into $(1/\pi)[D_N(\theta - \varphi) + D_N(\theta + \varphi)]$
(`Approximation.chebyshevKernel_cos`), and the row integral into $(1/\pi) \int_0^\pi
|D_N(\theta - \varphi) + D_N(\theta + \varphi)|\, d\varphi$. This is largest at $\theta = 0$,
where it is $(2/\pi) \int_0^\pi |D_N| = L_N$. The book then quotes (3.7.10) for
$L_N = (4/\pi^2) \log N + O(1)$. These asymptotics are not formalized;
`AtkinsonHan.Chapter03.norm_chebyshevProj_asymptotics` gives the two-sided bound that the
backbone proves. The operator is `Approximation.chebyshevProj N`.

**Correction.** The printed final integral for $\|P_N\|$ omits the absolute value of the
Dirichlet kernel. The equality uses the integral of its absolute value, as in (3.7.9).
The formal projection also uses the orthonormal, rather than unnormalized, Chebyshev family. -/
theorem example_3_7_4 (N : ℕ) : ‖chebyshevProj N‖ = lebesgueConstant N :=
  norm_chebyshevProj N

/-- Let $P_N$ be the Chebyshev least squares projection of Example 3.7.4 of [han2009theoretical].
Then
$$\frac{4}{\pi^2} \log N \le \|P_N\| \le 1 + \log(2N + 1).$$
So $\|P_N\| \to \infty$, and by `AtkinsonHan.Chapter03.exists_not_tendsto_of_not_bddAbove` some
$u \in C[-1, 1]$ has $P_N u \not\to u$ uniformly. This is the conclusion that the book draws
from Example 3.7.4 and (3.7.10), here with the two-sided bound in place of the sharp constant.

**Reading.** The two-sided bounds replace the source's sharper bounded-remainder asymptotic. -/
theorem norm_chebyshevProj_asymptotics (N : ℕ) :
    4 / π ^ 2 * Real.log N ≤ ‖chebyshevProj N‖ ∧
      ‖chebyshevProj N‖ ≤ 1 + Real.log (2 * (N : ℝ) + 1) := by
  rw [example_3_7_4]
  exact ⟨log_le_lebesgueConstant N, lebesgueConstant_le N⟩

end LeastSquares

end AtkinsonHan.Chapter03
