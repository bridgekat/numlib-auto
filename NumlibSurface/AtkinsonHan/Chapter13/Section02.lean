/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.LogSingleLayer
import Numlib.Approximation.CompositeQuadrature
import Mathlib.Topology.Instances.AddCircle.Real
import NumlibSurface.AtkinsonHan.Chapter12.Section04
import NumlibSurface.AtkinsonHan.Chapter13.Section01

/-!
# Atkinson and Han, Section 13.2: The Nyström method for the boundary integral equation

This module formalizes Section 13.2 of [han2009theoretical]. The interior Dirichlet problem for the
Laplace equation on a planar region with smooth boundary $S$ is reformulated as the boundary
integral equation of the second kind $$-\pi \rho(P) + \int_S \rho(Q) \frac{\partial}{\partial n_Q}
\log |P - Q| \, dS_Q = f(P).$$ After a regular $C^2$ parametrization of $S$ by arclength, this is an
integral equation $(-\pi + K) \rho = f$ on the space $C_p(L)$ of continuous $L$-periodic functions,
with a continuous kernel: the parametrized double layer kernel
`AtkinsonHan.Chapter13.doubleLayerKernelCP` of Section 13.1. Its sign is the sign of the book, so
the row integral $\int_0^L k(t, s) \, ds$ is $-\pi$, and the equations (13.1.32) and (13.2.3) read
as in the book. The book says that the natural function space setting for (13.2.3) is $C_p(L)$ with
the uniform norm, and that $(-\pi + K)^{-1}$ exists as a bounded operator on $C_p(L)$; it quotes
this from the literature without proof, and the invertibility is a hypothesis here, as in the book.

The error analysis of the Nyström method is Theorem 12.4.4 at $\lambda = -\pi$ on $C_p(L)$
(`AtkinsonHan.Chapter12.theorem_12_4_4`), and the concrete scheme uses the periodic trapezoidal rule
of `Numlib.Approximation.CompositeQuadrature`. The module also states the kernel identity and the
peaking factor of Example 13.2.1, the properties of the test solution of Example 13.2.3, and the
Fourier diagonalization (13.2.32) of the logarithmic single layer operator of Section 13.2.3, from
`Numlib.Analysis.Fourier.LogSingleLayer`. No Sobolev space occurs; Sobolev spaces are needed only
for Section 13.2.2, the exterior Neumann problem, and for Section 13.3.

## Main definitions

* (13.2.9), `AtkinsonHan.Chapter13.ellipseDoubleLayerKernel`: the function $\kappa(\theta) = -a b /
  (2 (a^2 \sin^2 \theta + b^2 \cos^2 \theta))$ of Example 13.2.1.

## Main results

* (13.2.4)–(13.2.5), `AtkinsonHan.Chapter13.equation_13_2_4`: the Nyström method with the periodic
  trapezoidal rule is uniquely solvable for large $n$, with uniformly bounded inverses and $\|\rho -
  \rho_n\|_\infty \le c \|K \rho - K_n \rho\|_\infty$.
* (13.2.6), `AtkinsonHan.Chapter13.equation_13_2_6`: the Nyström interpolation formula, which
  extends the discrete solution off the quadrature nodes.
* (13.2.7), `AtkinsonHan.Chapter13.equation_13_2_7`: the same error analysis for every convergent
  quadrature with bounded absolute weight sums.
* Example 13.2.1, `AtkinsonHan.Chapter13.example_13_2_1`: for the ellipse, the double layer kernel
  is $k(t, s) = \kappa((s + t)/2)$.
* Example 13.2.1, `AtkinsonHan.Chapter13.example_13_2_1_peakingFactor`: the peaking factor of the
  ellipse kernel is $(\max\{a, b\} / \min\{a, b\})^2$.
* Example 13.2.3, `AtkinsonHan.Chapter13.example_13_2_3`: the test solution
  $u(x, y) = x / (x^2 + y^2)$ is the Kelvin transform of $x$, harmonic away from the origin, and
  tends to $0$ at infinity.
* (13.2.32), `AtkinsonHan.Chapter13.equation_13_2_32`: the logarithmic single layer operator $A$
  satisfies $A \psi_m = \psi_m / \max\{1, |m|\}$ on the Fourier modes $\psi_m(t) = e^{i m t}$.
* Exercise 13.3.1, `AtkinsonHan.Chapter13.exercise_13_3_1`: the first kind equation
  $A \varphi = \cos(k t)$ is solved by $\varphi(t) = \max\{1, k\} \cos(k t)$.

## Conventions

* $C_p(L)$ is `C(AddCircle L, ℝ)`, and the integral $\int_0^L \cdots \, ds$ is the integral against
  the Haar measure `MeasureTheory.volume` of `AddCircle L`.
* The invertibility of $-\pi + K$ is an equivalence `e` with `↑e = (-π) • 1 + kernelCLM volume k`.
* The Nyström operator $K_n$ with weights $w_j$ and nodes $x_j$ is
  `IntegralOperator.nystromCLM w x k`.

## Deviations from the source

* **(13.2.4)–(13.2.7)** (generalization). The book states the error analysis for the double layer
  kernel. The theorems hold for every continuous kernel on the torus. See
  `AtkinsonHan.Chapter13.equation_13_2_7`.

## Not formalized

* **The identification of $K$ with the boundary integral** $\int_S \rho(Q) \frac{\partial}{\partial
  n_Q} \log |P - Q| \, dS_Q$. It needs the jump relations of the layer potentials; only the
  parametrized kernel of Section 13.1 is formalized.
* **The rate of convergence of the trapezoidal rule**, spectral convergence for a smooth periodic
  integrand. It is Proposition 7.5.6 and needs the periodic Sobolev scale $H^s(2\pi)$. Only the
  convergence for every continuous periodic integrand is used, which is
  `Quadrature.tendsto_circleTrapezoid`.
* **(13.2.19)**, and with it (13.2.14)–(13.2.23), the evaluation of the potential near the boundary:
  with $u_n$ the double layer potential of the Nyström density $\rho_n$, $\max_{\bar D_i} |u - u_n|
  \le (\pi + \|K\|) \|\rho - \rho_n\|_\infty$. The derivation of the book, (13.2.16) with (13.2.17),
  uses the maximum principle and the jump relation $u(P) - u_n(P) = -\pi (\rho - \rho_n)(P) + \int_S
  (\rho - \rho_n)(Q) \frac{\partial}{\partial n_Q} \log |P - Q| \, dS_Q$. The jump relations
  (13.1.7)–(13.1.8) are a singular integral statement about the principal value of the kernel at a
  boundary point, which neither Mathlib nor the backbone has. The derivation uses no singularity
  subtraction.
* **Exercise 13.2.5 and (13.2.20)**, that $\|K\| = \pi$ for a bounded convex region with smooth
  boundary, so that $(-\pi + K)^{-1}$ cannot be obtained from a Neumann series. By
  `IntegralOperator.norm_kernelCLM` the statement is $\sup_t \int_0^L |k(t, s)| \, ds = \pi$.
  Convexity is needed for the whole statement and not only for the lower bound: for a non-convex
  smooth curve the chord direction reverses, so $\int_0^L |k(t, s)| \, ds > |\int_0^L k(t, s) \,
  ds| = \pi$ and $\|K\| > \pi$. The two results need a continuous argument along a plane curve and a
  turning number, which Mathlib does not have.
* **The bound (13.2.33)**, $\|A\|_{C_p \to C_p} \le \sqrt{1 + \pi^2/3}$. The book quotes it from
  Atkinson.
* **The numerical parts of Examples 13.2.1, 13.2.2 and 13.2.3**: Tables 13.1–13.3 and Figures
  13.1–13.5, which are measured errors. Example 13.2.2 consists only of such data.
* **Section 13.2.2**, the exterior Neumann problem. Its boundary integral equation (13.2.24) is
  (13.1.30) of the potential theory of Section 13.1, and the splitting (13.2.25)–(13.2.30) of its
  right-hand side is an identity between integrals over $S$. Its error analysis also needs the
  trigonometric interpolation and Euler–Maclaurin rates (13.2.36), (13.2.39), (13.2.41) and
  (13.2.43).
-/

open Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter13

open IntegralOperator

variable {L : ℝ} [Fact (0 < L)]

/-- **Equation (13.2.6)** of [han2009theoretical] (Nyström interpolation formula). Let $L > 0$, let
$w_1, \dots, w_m \in \mathbb{R}$ be weights and $x_1, \dots, x_m$ nodes on the circle
$\mathbb{R}/L\mathbb{Z}$, and let $k$ be a continuous kernel on the torus. If
$\rho_n, f \in C_p(L)$ satisfy the discrete equation $(-\pi + K_n) \rho_n = f$, with
$K_n \rho(t) = \sum_j w_j k(t, x_j) \rho(x_j)$, then for every point $t$ $$\rho_n(t) =
\frac{1}{\pi} \Bigl(\sum_j w_j k(t, x_j) \rho_n(x_j) - f(t)\Bigr).$$

This is the equation solved for $\rho_n(t)$. It determines $\rho_n$ at every point from its
values at the nodes, so the Nyström method gives a function and not only a table of values. -/
theorem equation_13_2_6 {m : ℕ} (w : Fin m → ℝ) (x : Fin m → AddCircle L)
    (k : C(AddCircle L × AddCircle L, ℝ)) (f ρn : C(AddCircle L, ℝ))
    (h : ((-π) • 1 + nystromCLM w x k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f)
    (t : AddCircle L) :
    ρn t = (∑ j, w j * k (t, x j) * ρn (x j) - f t) / π := by
  have ht := congrArg (fun g : C(AddCircle L, ℝ) => g t) h
  simp only [add_apply, ContinuousMap.add_apply, smul_apply,
    ContinuousMap.smul_apply, one_apply_eq_self, smul_eq_mul, nystromCLM_apply] at ht
  field_simp
  linarith [ht]

/-- **Equation (13.2.7)** of [han2009theoretical], with (13.2.4)–(13.2.6). Let $L > 0$ and let $k$
be a continuous kernel on the torus $\mathbb{R}/L\mathbb{Z} \times \mathbb{R}/L\mathbb{Z}$, with
the integral operator $K$ on $C_p(L)$. For each $n$ let $K_n$ be the Nyström operator of a
quadrature rule with weights $w_{n,j}$ and nodes $x_{n,j}$, such that $\sum_j |w_{n,j}| \le W$
for all $n$ and the rules converge to $\int_0^L v \, ds$ for every $v \in C_p(L)$. Let
$-\pi + K$ be invertible on $C_p(L)$. Then there is a constant $c$ such that, for all
sufficiently large $n$, the operator $-\pi + K_n$ is invertible, $\|(-\pi + K_n)^{-1}\| \le c$,
and whenever $(-\pi + K) \rho = f$ and $(-\pi + K_n) \rho_n = f$, $$\|\rho - \rho_n\|_\infty \le
c \, \|K \rho - K_n \rho\|_\infty.$$

**Generalization.** The book states this for the parametrized double layer kernel. The theorem
holds for every continuous kernel on the torus.

The book assumes the invertibility of $-\pi + K$, quoting the literature, and says that the
error analysis is straightforward from Theorem 12.4.4. The proof is
`AtkinsonHan.Chapter12.theorem_12_4_4` at $\lambda = -\pi$, read for the kernel $-k$ to absorb
the sign. The quadrature rule is `Quadrature.functional`, and the integral is
`IntegralOperator.integralCLM` for the Haar measure of the circle. -/
theorem equation_13_2_7 (k : C(AddCircle L × AddCircle L, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → AddCircle L} {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(AddCircle L, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM volume v)))
    {e : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ)}
    (he : (e : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ),
      (en : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
          = (-π) • 1 + nystromCLM (w n) (x n) k ∧
      ‖(en.symm : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))‖ ≤ c ∧
      ∀ f ρ ρn : C(AddCircle L, ℝ),
        ((-π) • 1 + kernelCLM volume k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρ = f →
        ((-π) • 1 + nystromCLM (w n) (x n) k :
          C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f →
        ‖ρ - ρn‖ ≤ c * ‖kernelCLM volume k ρ - nystromCLM (w n) (x n) k ρ‖ := by
  have hker : ((-π) • 1 - kernelCLM volume (-k) : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k := by rw [kernelCLM_neg, sub_neg_eq_add]
  have hnys : ∀ n, ((-π) • 1 - nystromCLM (w n) (x n) (-k) :
      C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) = (-π) • 1 + nystromCLM (w n) (x n) k := by
    intro n
    rw [nystromCLM_neg, sub_neg_eq_add]
  obtain ⟨c, hc⟩ := AtkinsonHan.Chapter12.theorem_12_4_4 (ν := volume)
    (neg_ne_zero.2 Real.pi_ne_zero) (-k) hW hQ (e := e) (by rw [hker]; exact he)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ := hn
  refine ⟨en, by rw [hencoe, hnys n], hennorm, fun f ρ ρn hρ hρn => ?_⟩
  refine (herr f ρ ρn (by rw [hker]; exact hρ) (by rw [hnys n]; exact hρn)).trans ?_
  rw [kernelCLM_neg, nystromCLM_neg]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) ?_
  · rw [neg_apply, neg_apply, ← neg_sub, norm_neg, neg_sub_neg]
  · exact le_trans (norm_nonneg _) hennorm

/-- **Equations (13.2.4)–(13.2.5)** of [han2009theoretical], the Nyström method with the periodic
trapezoidal rule. Let $L > 0$ and let $k$ be a continuous kernel on the torus
$\mathbb{R}/L\mathbb{Z} \times \mathbb{R}/L\mathbb{Z}$ with $-\pi + K$ invertible on $C_p(L)$.
Let $h = L/n$ and $$K_n \rho(t) = h \sum_{j=0}^{n-1} k(t, j h) \, \rho(j h).$$ Then there is a
constant $c$ such that, for all sufficiently large $n$, the operator $-\pi + K_n$ is invertible,
$\|(-\pi + K_n)^{-1}\| \le c$, and whenever $(-\pi + K) \rho = f$ and $(-\pi + K_n) \rho_n = f$,
$$\|\rho - \rho_n\|_\infty \le c \, \|K \rho - K_n \rho\|_\infty.$$

**Generalization.** The book uses the parametrized double layer kernel
`AtkinsonHan.Chapter13.doubleLayerKernelCP`. The theorem holds for every continuous kernel on
the torus.

This is `AtkinsonHan.Chapter13.equation_13_2_7` with its two quadrature hypotheses proved:
`Quadrature.sum_abs_circleTrapezoid` bounds the absolute weight sums by $L$, and
`Quadrature.tendsto_circleTrapezoid` is the convergence of Riemann sums on the circle. -/
theorem equation_13_2_4 (k : C(AddCircle L × AddCircle L, ℝ))
    {e : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ)}
    (he : (e : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
      = (-π) • 1 + kernelCLM volume k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(AddCircle L, ℝ) ≃L[ℝ] C(AddCircle L, ℝ),
      (en : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))
          = (-π) • 1 + nystromCLM (fun _ : Fin n => L / n)
            (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k ∧
      ‖(en.symm : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ))‖ ≤ c ∧
      ∀ f ρ ρn : C(AddCircle L, ℝ),
        ((-π) • 1 + kernelCLM volume k : C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρ = f →
        ((-π) • 1 + nystromCLM (fun _ : Fin n => L / n)
          (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k :
          C(AddCircle L, ℝ) →L[ℝ] C(AddCircle L, ℝ)) ρn = f →
        ‖ρ - ρn‖ ≤ c * ‖kernelCLM volume k ρ - nystromCLM (fun _ : Fin n => L / n)
          (fun j : Fin n => (((j : ℕ) * (L / n) : ℝ) : AddCircle L)) k ρ‖ :=
  equation_13_2_7 k (W := L) (fun n => Quadrature.sum_abs_circleTrapezoid n)
    (fun v => by
      simpa only [integralCLM_apply, Quadrature.circleTrapezoid] using
        Quadrature.tendsto_circleTrapezoid v) he

/-! ### Example 13.2.1: the ellipse -/

/-- **Equation (13.2.9)** of [han2009theoretical]. For real $a$, $b$ and $\theta$, the function
$\kappa$ of Example 13.2.1 is $$\kappa(\theta) = -\frac{a b}{2 (a^2 \sin^2 \theta + b^2 \cos^2
\theta)}.$$

For the ellipse $r(t) = (a \cos t, b \sin t)$ the parametrized double layer kernel is
$k(t, s) = \kappa((s + t)/2)$ (`AtkinsonHan.Chapter13.example_13_2_1`). On the circle $a = b$ it
is the constant $-1/(2a)$, which for $a = 1$ is the value $-1/2$ of
`AtkinsonHan.Chapter13.doubleLayerKernel_circle_self`. Where the denominator vanishes, Lean's
division gives the value $0$. -/
noncomputable def ellipseDoubleLayerKernel (a b θ : ℝ) : ℝ :=
  -(a * b) / (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2))

/-- **Example 13.2.1** of [han2009theoretical], the kernel identity (13.2.9). Let
$a, b \in \mathbb{R}$ and let $r(t) = (a \cos t, b \sin t)$ be the ellipse. Let
$t, s \in \mathbb{R}$ with $t = s$ or $\sin((t - s)/2) \neq 0$. Then the parametrized double
layer kernel of $r$ is $$k(t, s) = \kappa\Bigl(\frac{s + t}{2}\Bigr), \qquad \kappa(\theta) =
-\frac{a b}{2 (a^2 \sin^2 \theta + b^2 \cos^2 \theta)}.$$

The identity makes the integral equation (13.2.10) cheap to assemble: one function of one
variable gives the whole matrix. It is algebraic: it uses no positivity of $a$ or $b$, and it
holds on the diagonal too, where it is (13.1.34). The hypothesis excludes the case that $s - t$
is a nonzero multiple of $2\pi$; there `AtkinsonHan.Chapter13.doubleLayerKernel` is $0$, because
it divides the vanishing chord by $s - t$. This is the fact that
`AtkinsonHan.Chapter13.doubleLayerKernel_add_period` records, and the reason why Section 13.2
works on the circle and not on the line. The derivatives are passed as $\xi' = -a \sin$,
$\eta' = b \cos$, $\xi'' = -a \cos$, $\eta'' = -b \sin$. -/
theorem example_13_2_1 (a b : ℝ) {t s : ℝ} (hts : t = s ∨ Real.sin ((t - s) / 2) ≠ 0) :
    doubleLayerKernel (fun u => -(a * Real.sin u)) (fun u => b * Real.cos u)
        (fun u => -(a * Real.cos u)) (fun u => -(b * Real.sin u)) t s
      = ellipseDoubleLayerKernel a b ((s + t) / 2) := by
  have hξ : ∀ x : ℝ, HasDerivAt (fun u => a * Real.cos u) (-(a * Real.sin x)) x := fun x => by
    simpa using (Real.hasDerivAt_cos x).const_mul a
  have hη : ∀ x : ℝ, HasDerivAt (fun u => b * Real.sin u) (b * Real.cos x) x := fun x =>
    (Real.hasDerivAt_sin x).const_mul b
  have hξ' : ∀ x : ℝ, HasDerivAt (fun u => -(a * Real.sin u)) (-(a * Real.cos x)) x := fun x =>
    ((Real.hasDerivAt_sin x).const_mul a).neg
  have hη' : ∀ x : ℝ, HasDerivAt (fun u => b * Real.cos u) (-(b * Real.sin x)) x := fun x => by
    simpa using (Real.hasDerivAt_cos x).const_mul b
  rcases hts with rfl | hsin
  · rw [equation_13_1_34, ellipseDoubleLayerKernel, show (t + t) / 2 = t by ring]
    congr 1
    · linear_combination (-(a * b)) * Real.sin_sq_add_cos_sq t
    · ring
  · have hst : s ≠ t := fun h => hsin (by rw [h, sub_self]; simp)
    rw [equation_13_1_33 hξ hξ' hη hη' (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hst,
      ellipseDoubleLayerKernel]
    set θ : ℝ := (s + t) / 2 with hθ
    set d : ℝ := (t - s) / 2 with hd
    have htd : t = θ + d := by rw [hθ, hd]; ring
    have hsd : s = θ - d := by rw [hθ, hd]; ring
    rw [htd, hsd, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    have hnum : b * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d) *
          (a * (Real.cos θ * Real.cos d - Real.sin θ * Real.sin d)
            - a * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d))
        - -(a * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d)) *
          (b * (Real.sin θ * Real.cos d + Real.cos θ * Real.sin d)
            - b * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d))
        = Real.sin d ^ 2 * (-(2 * (a * b))) := by
      linear_combination (-(2 * a * b * Real.sin d ^ 2)) * Real.sin_sq_add_cos_sq θ
    have hden : (a * (Real.cos θ * Real.cos d - Real.sin θ * Real.sin d)
            - a * (Real.cos θ * Real.cos d + Real.sin θ * Real.sin d)) ^ 2
        + (b * (Real.sin θ * Real.cos d + Real.cos θ * Real.sin d)
            - b * (Real.sin θ * Real.cos d - Real.cos θ * Real.sin d)) ^ 2
        = Real.sin d ^ 2 * (4 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) := by
      ring
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hsin),
      show -(2 * (a * b)) = 2 * -(a * b) by ring,
      show (4 : ℝ) * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)
        = 2 * (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) by ring,
      mul_div_mul_left _ _ two_ne_zero]

/-- **Example 13.2.1** of [han2009theoretical], the peaking factor. Let $a, b > 0$. Then the largest
value of $|\kappa(\theta)|$ over $\theta \in \mathbb{R}$ is $a b / (2 \min\{a, b\}^2)$, the
smallest value is $a b / (2 \max\{a, b\}^2)$, and their ratio is the **peaking factor** $$p(a,
b) = \frac{\max_\theta |\kappa(\theta)|}{\min_\theta |\kappa(\theta)|} = \Bigl(\frac{\max\{a,
b\}}{\min\{a, b\}}\Bigr)^2.$$

The book measures with $p(a, b)$ how hard the equation (13.2.10) is to solve: $p(1, 2) = 4$,
$p(1, 5) = 25$ and $p(1, 8) = 64$. The more elongated the ellipse, the more peaked the kernel
and the larger the $n$ needed for a given accuracy, as Table 13.1 shows. The extremes are
attained at $\theta = 0$ and $\theta = \pi/2$, because $a^2 \sin^2 \theta + b^2 \cos^2 \theta$
takes all values in $[\min\{a, b\}^2, \max\{a, b\}^2]$. -/
theorem example_13_2_1_peakingFactor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsGreatest (Set.range fun θ : ℝ => |ellipseDoubleLayerKernel a b θ|)
        (a * b / (2 * min a b ^ 2)) ∧
      IsLeast (Set.range fun θ : ℝ => |ellipseDoubleLayerKernel a b θ|)
        (a * b / (2 * max a b ^ 2)) ∧
      a * b / (2 * min a b ^ 2) / (a * b / (2 * max a b ^ 2)) = (max a b / min a b) ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hmin : 0 < min a b := lt_min ha hb
  have hmax : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have hlb : ∀ θ : ℝ, min a b ^ 2 ≤ a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 := by
    intro θ
    have h1 : min a b ^ 2 ≤ a ^ 2 := by nlinarith [min_le_left a b, hmin]
    have h2 : min a b ^ 2 ≤ b ^ 2 := by nlinarith [min_le_right a b, hmin]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (Real.sin θ)),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (Real.cos θ))]
  have hub : ∀ θ : ℝ, a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 ≤ max a b ^ 2 := by
    intro θ
    have h1 : a ^ 2 ≤ max a b ^ 2 := by nlinarith [le_max_left a b, ha]
    have h2 : b ^ 2 ≤ max a b ^ 2 := by nlinarith [le_max_right a b, hb]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ),
      mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (Real.sin θ)),
      mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (Real.cos θ))]
  have hDpos : ∀ θ : ℝ, 0 < a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 := fun θ =>
    lt_of_lt_of_le (pow_pos hmin 2) (hlb θ)
  have habs : ∀ θ : ℝ, |ellipseDoubleLayerKernel a b θ|
      = a * b / (2 * (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2)) := by
    intro θ
    rw [ellipseDoubleLayerKernel, abs_div, abs_neg, abs_of_pos hab,
      abs_of_pos (by have := hDpos θ; positivity)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rcases le_total a b with h | h
    · exact ⟨π / 2, by
        simp only [habs, Real.sin_pi_div_two, Real.cos_pi_div_two, min_eq_left h]; norm_num⟩
    · exact ⟨0, by simp only [habs, Real.sin_zero, Real.cos_zero, min_eq_right h]; norm_num⟩
  · rintro _ ⟨θ, rfl⟩
    simp only [habs]
    rw [div_le_div_iff₀ (by have := hDpos θ; positivity) (by positivity)]
    nlinarith [hlb θ, hab.le]
  · rcases le_total a b with h | h
    · exact ⟨0, by simp only [habs, Real.sin_zero, Real.cos_zero, max_eq_right h]; norm_num⟩
    · exact ⟨π / 2, by
        simp only [habs, Real.sin_pi_div_two, Real.cos_pi_div_two, max_eq_left h]; norm_num⟩
  · rintro _ ⟨θ, rfl⟩
    simp only [habs]
    rw [div_le_div_iff₀ (by positivity) (by have := hDpos θ; positivity)]
    nlinarith [hub θ, hab.le]
  · field_simp

/-! ### Example 13.2.3: the test solution of the exterior Neumann problem -/

/-- **Example 13.2.3** of [han2009theoretical], the test solution. The example solves the exterior
Neumann problem outside an ellipse with boundary data from $$u(x, y) = \frac{x}{x^2 + y^2}.$$
Identifying the plane with $\mathbb{C}$: $u$ is the Kelvin transform of the coordinate function
$\operatorname{Re}$, that is $u(z) = \operatorname{Re} z / \|z\|^2$ for every $z$; $u$ is
harmonic at every $z \neq 0$; and $u(z) \to 0$ as $\|z\| \to \infty$.

The book says of $u$ that it is harmonic and tends to $0$ at infinity, the condition at infinity
of an exterior problem. Harmonicity is `AtkinsonHan.Chapter13.kelvin_harmonic` applied to the
harmonic function $\operatorname{Re}$, and the decay is $|x| / (x^2 + y^2) \le 1 / \|(x, y)\|$.
At $z = 0$, Lean's division gives $u(0) = 0$. The limit at infinity is along the filter
`cocompact ℂ`. -/
theorem example_13_2_3 :
    (∀ z : ℂ, kelvin Complex.re z = z.re / ‖z‖ ^ 2) ∧
      (∀ z : ℂ, z ≠ 0 → InnerProductSpace.HarmonicAt (kelvin Complex.re) z) ∧
      Tendsto (kelvin Complex.re) (cocompact ℂ) (𝓝 0) := by
  have hval : ∀ z : ℂ, kelvin Complex.re z = z.re / ‖z‖ ^ 2 := by
    intro z
    rw [kelvin, Complex.div_ofReal_re]
  refine ⟨hval, fun z hz => kelvin_harmonic hz (analyticAt_id (𝕜 := ℂ)).harmonicAt_re, ?_⟩
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h1 : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [hnorm.eventually_gt_atTop 0] with z hz
  rw [hval z, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2),
    div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hz]
  calc |z.re| * ‖z‖ ≤ ‖z‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg z)
    _ = ‖z‖ ^ 2 := by ring

/-! ### Section 13.2.3: The first kind equation and the logarithmic single layer operator -/

/-- **Equation (13.2.32)** of [han2009theoretical], with (13.2.31) and (13.2.37), the Fourier
diagonalization of the logarithmic single layer operator. Let $$A \varphi(t) = -\frac{1}{\pi}
\int_0^{2\pi} \varphi(s) \log \bigl|2 e^{-1/2} \sin\bigl(\tfrac{t - s}{2}\bigr)\bigr| \, ds$$ be
the single layer operator of the unit circle in the arclength parameter. Then for every
$m \in \mathbb{Z}$ and every real $t$, the Fourier mode $\psi_m(s) = e^{i m s}$ satisfies $$A
\psi_m(t) = \frac{\psi_m(t)}{\max\{1, |m|\}}.$$

This is (13.2.37), and read on the Fourier expansion of $\varphi$ it is (13.2.32). It is the
reason why $A$ is a bijection of $H^0(2\pi)$ onto $H^1(2\pi)$, and it makes the operator algebra
of Section 13.3 elementary. The book quotes it from Yan and Sloan. The proof is in
`Numlib.Analysis.Fourier.LogSingleLayer`, where the eigenvalue is the $m$-th Fourier coefficient
of $u \mapsto \log |2 e^{-1/2} \sin(u/2)|$. The bound (13.2.33),
$\|A\|_{C_p \to C_p} \le \sqrt{1 + \pi^2/3}$, which the book quotes from Atkinson, is not
formalized. -/
theorem equation_13_2_32 (m : ℤ) (t : ℝ) :
    -(1 / π) * ∫ s in (0 : ℝ)..(2 * π), Complex.exp (m * s * Complex.I)
        * (Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)| : ℂ)
      = Complex.exp (m * t * Complex.I) / max 1 |m| := by
  rw [← logSingleLayerC_fourier m t, logSingleLayerC, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [logSingleLayerKernel]
  push_cast
  ring

/-- **Exercise 13.3.1** of [han2009theoretical]. For every integer $k \ge 0$ and every real $t$, the
function $\varphi(s) = \max\{1, k\} \cos(k s)$ solves the first kind equation $$-\frac{1}{\pi}
\int_0^{2\pi} \varphi(s) \log \bigl|2 e^{-1/2} \sin\bigl(\tfrac{t - s}{2}\bigr)\bigr| \, ds =
\cos(k t).$$ So the solution is $k \cos(k t)$ for $k \ge 1$, and the constant $1$ for $k = 0$.

The proof reads `AtkinsonHan.Chapter13.equation_13_2_32` on the real Fourier modes. -/
theorem exercise_13_3_1 (k : ℕ) (t : ℝ) :
    -(1 / π) * ∫ s in (0 : ℝ)..(2 * π), ((max 1 k : ℕ) : ℝ) * Real.cos (k * s)
        * Real.log |2 * Real.exp (-(1 / 2)) * Real.sin ((t - s) / 2)|
      = Real.cos (k * t) := by
  have hk : ((max 1 k : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (le_max_left 1 k))
  have h : logSingleLayer (fun s => ((max 1 k : ℕ) : ℝ) * Real.cos ((k : ℝ) * s)) t
      = Real.cos ((k : ℝ) * t) := by
    rw [logSingleLayer_const_mul, logSingleLayer_cos]
    field_simp
  rw [← h, logSingleLayer, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [logSingleLayerKernel]
  ring

end AtkinsonHan.Chapter13

