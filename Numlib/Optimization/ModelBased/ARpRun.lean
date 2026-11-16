/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.ModelBased.ARRun

/-!
# The ARp method as a generic AR run

The adaptive-regularization method ARp of [cartis2022evaluation] (Algorithm 4.1.1) minimizes
$f : E \to \mathbb{R}$ with the regularized Taylor model
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1}.$$
This file presents ARp as an instance of the generic run `Optimization.IsARRun`, with the Step-1
termination test as a parameter. Chapter 4 of the source uses the tests (4.1.5)–(4.1.9). ARpLE
(Algorithm 5.1.1) runs ARp on $\Phi_\ell = \|r\|^\ell / \ell$ with tests scaled by the residual, and
the measure-dominated analysis of Section 5.3 uses no test at all. The Step-2 conditions
(4.1.10)–(4.1.14) and their consequences for one iteration (Lemmas 4.1.3 and 4.1.4) do not depend on
the test, so they are proved once here.

The number $q \in \{1, 2, 3\}$ is the order of criticality sought. The case
$\varepsilon_2 = \varepsilon_3 = \infty$ of the source is $q = 1$, the case
$\varepsilon_2 < \infty = \varepsilon_3$ is $q = 2$, and the case with both tolerances finite is
$q = 3$. The second-order step condition (4.1.12) is imposed if and only if $q \ge 2$, and the
third-order condition (4.1.13) if and only if $q \ge 3$. The ratio is the Taylor ratio (4.1.15), and
the weight update (4.1.16) is the rule (2.4.4).

## Main definitions

* `Optimization.ARpParams`: the AR constants and the step-termination constants
  $\theta_1, \theta_2, \theta_3 \in (0, 1]$.
* `Optimization.smallCurvatureDirections`: the unit directions along which a bilinear form has
  curvature at most $c$ in absolute value; these give the sets $\mathcal{M}_k$ of (4.1.14) and
  $\mathcal{Z}_\varepsilon$ of (4.1.4).
* `Optimization.IsARpStep`: the step conditions (4.1.10)–(4.1.13).
* `Optimization.IsARpRun`: a run of ARp.

## Main results

* `Optimization.IsARpRun.sigma_le`: Lemma 4.1.2, the bound $\sigma_k \le \sigma_{\max}$.
* `Optimization.IsARpRun.density`: the number of iterations is bounded by the number of successful
  ones.
* `Optimization.IsARpRun.step_lower_bounds`: Lemma 4.1.3, lower bounds on the step length.
* `Optimization.IsARpRun.decrease_ge`: Lemma 4.1.4, lower bounds on the decrease of $f$.
* `Optimization.exists_isARpStep`, `Optimization.exists_isARpRun`,
  `Optimization.exists_isARpRun_prev`: existence of steps and of runs.

## Implementation notes

* The model $m_k$ is `Optimization.regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)`, and the
  ratio is `Optimization.taylorRatio f p x s`.
* The least curvature $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$ of a bilinear form is
  `minCurvature A`. It is $0$ on the zero space.
* The exponents $p - 1$ and $p - 2$ in the step conditions are differences of natural numbers, so
  they are $0$ when $p$ is too small.
-/

open Set
open scoped Nat

namespace Optimization

/-- The constants of the ARp method, Step 0 of Algorithm 4.1.1 of [cartis2022evaluation]. They
consist of the constants of an AR method (`Optimization.ARParams`) and the step-termination
constants $\theta_1, \theta_2, \theta_3 \in (0, 1]$.

The structure does not require $\sigma_{\min} > 0$: the inherited condition
$\sigma_{\min} \ge 0$ suffices for every result. With $\sigma_{\min} = 0$ the decrease bounds of
`Optimization.IsARpRun.decrease_ge` are trivial. -/
structure ARpParams extends ARParams where
  /-- The first-order step-termination constant $\theta_1$ of (4.1.11). -/
  θ₁ : ℝ
  /-- The second-order step-termination constant $\theta_2$ of (4.1.12) and (4.1.14). -/
  θ₂ : ℝ
  /-- The third-order step-termination constant $\theta_3$ of (4.1.13). -/
  θ₃ : ℝ
  /-- The first-order constant is positive: $\theta_1 > 0$. -/
  θ₁_pos : 0 < θ₁
  /-- The first-order constant is at most one: $\theta_1 \le 1$. -/
  θ₁_le_one : θ₁ ≤ 1
  /-- The second-order constant is positive: $\theta_2 > 0$. -/
  θ₂_pos : 0 < θ₂
  /-- The second-order constant is at most one: $\theta_2 \le 1$. -/
  θ₂_le_one : θ₂ ≤ 1
  /-- The third-order constant is positive: $\theta_3 > 0$. -/
  θ₃_pos : 0 < θ₃
  /-- The third-order constant is at most one: $\theta_3 \le 1$. -/
  θ₃_le_one : θ₃ ≤ 1

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **directions of small curvature** of a bilinear form $A$ on $E$ with bound $c$ are the unit
vectors along which $A$ has curvature at most $c$ in absolute value:
$$\{d \in E \mid \|d\| = 1, \ |A[d, d]| \le c\}.$$

With $A = \nabla^2 m_k(s_k)$ and $c = \theta_2 \|s_k\|^{p-1}$ this is the set
$\mathcal{M}_{k+1}$ of (4.1.14) of [cartis2022evaluation]. With $A = \nabla^2 f(x_\varepsilon)$
and $c = \varepsilon_2$ it is the set $\mathcal{Z}_\varepsilon$ of (4.1.4). -/
def smallCurvatureDirections (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (c : ℝ) :
    Set E :=
  {d | ‖d‖ = 1 ∧ |A (fun _ => d)| ≤ c}

/-- A vector $d$ is a direction of small curvature of $A$ with bound $c$ if and only if $\|d\| = 1$
and $|A[d, d]| \le c$. -/
@[simp]
theorem mem_smallCurvatureDirections {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    {c : ℝ} {d : E} :
    d ∈ smallCurvatureDirections A c ↔ ‖d‖ = 1 ∧ |A (fun _ => d)| ≤ c :=
  Iff.rfl

/-- **The step conditions of one ARp iteration**, Step 2 of Algorithm 4.1.1 of
[cartis2022evaluation]. Let $x \in E$ and $\sigma \in \mathbb{R}$, let $m(s) = T_{f,p}(x, s) +
\sigma \|s\|^{p+1} / (p+1)!$, and let $q$ be the order sought. A step $s$ satisfies the
conditions if

* the model decreases (4.1.10): $m(s) < m(0)$;
* the model gradient is small (4.1.11): $\|\nabla m(s)\| \le \theta_1 \|s\|^p$;
* if $q \ge 2$, the model curvature is not too negative (4.1.12): $\lambda_{\min}[\nabla^2 m(s)]
  \ge -\theta_2 \|s\|^{p-1}$;
* if $q \ge 3$, the third model derivative is small along the directions of small curvature
  (4.1.13): $|\nabla^3 m(s)[d]^3| \le \theta_3 \|s\|^{p-2}$ for every $d \in \mathcal{M}$, where
  $\mathcal{M} = \{d \mid \|d\| = 1, \ |\nabla^2 m(s)[d, d]| \le \theta_2 \|s\|^{p-1}\}$ is the
  set of (4.1.14).

The last condition holds trivially when $\mathcal{M}$ is empty. The set $\mathcal{M}$ is
`Optimization.smallCurvatureDirections`. -/
structure IsARpStep (f : E → ℝ) (p : ℕ) (P : ARpParams) (q : ℕ) (x : E) (σ : ℝ) (s : E) :
    Prop where
  /-- Condition (4.1.10): the step decreases the model, $m(s) < m(0)$. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- Condition (4.1.11): the model gradient is small, $\|\nabla m(s)\| \le \theta_1 \|s\|^p$. -/
  gradient : ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤ P.θ₁ * ‖s‖ ^ p
  /-- Condition (4.1.12): if $q \ge 2$, the model curvature is not too negative,
  $\lambda_{\min}[\nabla^2 m(s)] \ge -\theta_2 \|s\|^{p-1}$. -/
  curvature : 2 ≤ q →
    -(P.θ₂ * ‖s‖ ^ (p - 1)) ≤
      minCurvature (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
  /-- Condition (4.1.13): if $q \ge 3$, then $|\nabla^3 m(s)[d]^3| \le \theta_3 \|s\|^{p-2}$ for
  every unit vector $d$ with $|\nabla^2 m(s)[d, d]| \le \theta_2 \|s\|^{p-1}$. -/
  third : 3 ≤ q → ∀ d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (P.θ₂ * ‖s‖ ^ (p - 1)),
    |iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      P.θ₃ * ‖s‖ ^ (p - 2)

/-- **A run of the ARp method**, Steps 2–4 of Algorithm 4.1.1 of [cartis2022evaluation], and of
Algorithm 5.1.1. Let $\mathrm{test}(k)$ be any Step-1 termination test, which may refer to the
run. A run of ARp is a generic AR run (`Optimization.IsARRun`) with the step conditions
`Optimization.IsARpStep` at $(x_k, \sigma_k)$, no post-step test, and the Taylor ratio
$$\rho_k = \frac{f(x_k) - f(x_k + s_k)}{T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k)}$$
of (4.1.15). Iteration $k$ is successful if $\eta_1 \le \rho_k$. -/
def IsARpRun (f : E → ℝ) (p : ℕ) (P : ARpParams) (q : ℕ) (test : ℕ → Prop) (x s : ℕ → E)
    (σ : ℕ → ℝ) : Prop :=
  IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

/-- A run of ARp is, by definition, the generic AR run with the ARp step conditions, no post-step
test and the Taylor ratio. -/
theorem isARpRun_iff {f : E → ℝ} {p : ℕ} {P : ARpParams} {q : ℕ} {test : ℕ → Prop}
    {x s : ℕ → E} {σ : ℕ → ℝ} :
    IsARpRun f p P q test x s σ ↔
      IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
        (taylorRatio f p x s) x s σ :=
  Iff.rfl

end Defs

namespace IsARpRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}
  {P : ARpParams} {test : ℕ → Prop} {x s : ℕ → E} {σ : ℕ → ℝ}

/-- A run of ARp is a generic AR run with the ARp step conditions, no post-step test and the Taylor
ratio. -/
theorem toIsARRun (h : IsARpRun f p P q test x s σ) :
    IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
      (taylorRatio f p x s) x s σ :=
  h

/-- In a run of ARp, the step conditions (4.1.10)–(4.1.13) hold at every iteration before
termination. -/
theorem step_spec (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) :
    IsARpStep f p P q (x k) (σ k) (s k) :=
  h.toIsARRun.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)

/-- **Lemma 4.1.2** of [cartis2022evaluation] for ARp. Let $f$ be $C^p$ with $\nabla^p f$ Lipschitz
continuous on $E$ with constant $L$ (assumption f.DpL). Then in a run of ARp, every reached
iteration $k$ satisfies
$$\sigma_{\min} \le \sigma_k \le \sigma_{\max} = \max\Bigl(\sigma_0, \frac{\gamma_3 L}{1 -
  \eta_2}\Bigr),$$
the bound (4.1.19). -/
theorem sigma_le (h : IsARpRun f p P q test x s σ) {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams L := by
  have := h.toIsARRun.sigma_le convex_univ (fun y _ => hf.contDiffAt) hL (mem_univ _)
    (fun k _ hstep => ⟨mem_univ _, hstep.decrease⟩) k (IsARRun.forall_lt_not_stop_iff.2 hk)
  exact this.2

/-- In a run of ARp, $\sigma_k > 0$ at every reached iteration $k$. -/
theorem sigma_pos (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    0 < σ k :=
  h.toIsARRun.sigma_pos (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

/-- In a run of ARp, an unsuccessful iteration $k$ before termination keeps the iterate: if
$\rho_k < \eta_1$, then $x_{k+1} = x_k$. -/
theorem eq_of_not_succ (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j)
    (hs : ¬ P.η₁ ≤ taylorRatio f p x s k) : x (k + 1) = x k :=
  h.toIsARRun.eq_of_not_succ (IsARRun.forall_le_not_stop_iff.2 hk) (not_le.1 hs)

/-- **Density of the successful iterations**: Lemma 2.4.1 of [cartis2022evaluation] together with
the bound $\sigma_k \le \sigma_{\max}$ of Lemma 4.1.2, in the form (5.3.9). Let $f$ be $C^p$
with $\nabla^p f$ Lipschitz continuous on $E$ with constant $L$. In a run of ARp, let iteration
$k$ be reached. Then
$$k \le \Bigl(1 + \frac{|\log \gamma_1|}{\log \gamma_2}\Bigr) |\mathcal{S}_k| +
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2},$$
where $\mathcal{S}_k = \{j \le k \mid \eta_1 \le \rho_j\}$ and $\sigma_{\max} = \max(\sigma_0,
\gamma_3 L / (1 - \eta_2))$.

The set $\mathcal{S}_k$ is `Optimization.successSet (fun j => P.η₁ ≤ taylorRatio f p x s j) k`. -/
theorem density (h : IsARpRun f p P q test x s σ) {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    (k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (successSet (fun j => P.η₁ ≤ taylorRatio f p x s j) k).card +
      Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂ := by
  have := h.toIsARRun.le_succ_count (k := k) (IsARRun.forall_lt_not_stop_iff.2 hk)
    (h.sigma_le hf hL hk).2
  linarith

variable {L : ℝ}

/-- **Lemma 4.1.3**, (4.1.20) of [cartis2022evaluation], at the trial point. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L$, and let $p \ge 1$. In a run of ARp,
every iteration $k$ before termination satisfies
$$\|\nabla f(x_k + s_k)\| \le \frac{L + \sigma_{\max} + \theta_1 \, p!}{p!} \|s_k\|^p.$$
-/
theorem norm_fderiv_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) :
    ‖fderiv ℝ f (x k + s k)‖ ≤
      (L + arSigmaMax P.toARParams L + P.θ₁ * p !) / (p ! : ℝ) * ‖s k‖ ^ p := by
  have hst := h.step_spec hk
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := norm_fderiv_le_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt) hp hL
    (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le
  have hfac : (0 : ℝ) < p ! := by positivity
  calc ‖fderiv ℝ f (x k + s k)‖ ≤ (L + σ k) / (p ! : ℝ) * ‖s k‖ ^ p + P.θ₁ * ‖s k‖ ^ p :=
        h1.trans (by gcongr; exact hst.gradient)
    _ ≤ (L + arSigmaMax P.toARParams L) / (p ! : ℝ) * ‖s k‖ ^ p + P.θ₁ * ‖s k‖ ^ p := by
        gcongr; exact hσ.2
    _ = _ := by field_simp

/-- **Lemma 4.1.3**, (4.1.21) of [cartis2022evaluation], at the trial point. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L$, and let $p \ge 2$ and $q \ge 2$. In
a run of ARp, every iteration $k$ before termination satisfies
$$-\lambda_{\min}[\nabla^2 f(x_k + s_k)] \le \frac{L + \sigma_{\max} + \theta_2 (p-1)!}{(p-1)!}
  \|s_k\|^{p-1}.$$
-/
theorem neg_minCurvature_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 2 ≤ p) (hq : 2 ≤ q) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) :
    -minCurvature (iteratedFDeriv ℝ 2 f (x k + s k)) ≤
      (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
  have hst := h.step_spec hk
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := minCurvature_ge_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt) hp hL
    (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le
  have h2 := hst.curvature hq
  have hfac : (0 : ℝ) < (p - 1)! := by positivity
  have h3 : (L + σ k) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) ≤
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
    gcongr; exact hσ.2
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) =
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) +
        P.θ₂ * ‖s k‖ ^ (p - 1) := by
    field_simp
  linarith

/-- **Lemma 4.1.3**, (4.1.30) of [cartis2022evaluation], at the trial point. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L$. In a run of ARp, let iteration $k$
be before termination, let $j \le p$, and let $\|d\| = 1$. Then
$$|\nabla^j f(x_k + s_k)[d]^j| \le \frac{L + \sigma_{\max}}{(p-j+1)!} \|s_k\|^{p-j+1} +
  |\nabla^j m_k(s_k)[d]^j|.$$
-/
theorem abs_iteratedFDeriv_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) {j : ℕ}
    (hj : j ≤ p) {d : E} (hd : ‖d‖ = 1) :
    |iteratedFDeriv ℝ j f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) +
        |iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| := by
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := abs_iteratedFDeriv_apply_le_of_regularizedModel convex_univ
    (fun y _ => hf.contDiffAt) hL (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le hj d
  rw [hd, one_pow, mul_one] at h1
  have h2 : (L + σ k) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) ≤
      (L + arSigmaMax P.toARParams L) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) := by
    gcongr; exact hσ.2
  have h3 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ j f (x k + s k) (fun _ => d))
    (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k) (fun _ => d))
  linarith

/-- **Lemma 4.1.3**, (4.1.23) of [cartis2022evaluation], at the trial point. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L$, and let $p \ge 2$. In a run of ARp,
let iteration $k$ be before termination. Then every $d \in \mathcal{M}_{k+1}$ satisfies
$$|\nabla^2 f(x_k + s_k)[d]^2| \le \frac{L + \sigma_{\max} + \theta_2 (p-1)!}{(p-1)!}
  \|s_k\|^{p-1},$$
and the right side is $\|s_k\|^{p-1} / \kappa_{s2}$ in the notation of the source.

The set $\mathcal{M}_{k+1}$ is `Optimization.smallCurvatureDirections` applied to
`iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)` with the bound
$\theta_2 \|s_k\|^{p-1}$. -/
theorem abs_second_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 2 ≤ p) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j)
    {d : E} (hd : d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))) :
    |iteratedFDeriv ℝ 2 f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
  have h1 := h.abs_iteratedFDeriv_le hf hL hk hp hd.1
  have hpe : p - 2 + 1 = p - 1 := by omega
  rw [hpe] at h1
  have hfac : (0 : ℝ) < (p - 1)! := by positivity
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) =
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) +
        P.θ₂ * ‖s k‖ ^ (p - 1) := by
    field_simp
  linarith [hd.2]

/-- **Lemma 4.1.3**, (4.1.22) of [cartis2022evaluation], at the trial point. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L$, and let $p \ge 3$ and $q \ge 3$. In
a run of ARp, let iteration $k$ be before termination. Then every $d \in \mathcal{M}_{k+1}$
satisfies
$$|\nabla^3 f(x_k + s_k)[d]^3| \le \frac{L + \sigma_{\max} + \theta_3 (p-2)!}{(p-2)!}
  \|s_k\|^{p-2}.$$
-/
theorem abs_third_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 3 ≤ p) (hq : 3 ≤ q) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j)
    {d : E} (hd : d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))) :
    |iteratedFDeriv ℝ 3 f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) := by
  have h1 := h.abs_iteratedFDeriv_le hf hL hk hp hd.1
  have hpe : p - 3 + 1 = p - 2 := by omega
  rw [hpe] at h1
  have h2 := (h.step_spec hk).third hq d hd
  have hfac : (0 : ℝ) < (p - 2)! := by positivity
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) =
      (L + arSigmaMax P.toARParams L) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) +
        P.θ₃ * ‖s k‖ ^ (p - 2) := by
    field_simp
  linarith

omit [InnerProductSpace ℝ E] in
private theorem constant_pos (hL0 : 0 ≤ L) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 < L + arSigmaMax P.toARParams L + θ * m ! := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem div_mul_le_of_le_div_mul {K m a t : ℝ} (hK : 0 < K) (hm : 0 < m)
    (h : a ≤ K / m * t) : m / K * a ≤ t := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  rw [div_mul_eq_mul_div, le_div_iff₀ hm] at h
  linarith

/-- **Lemma 4.1.3** of [cartis2022evaluation] on a successful iteration. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L \ge 0$, let $1 \le p$ and $q \le p$,
and let $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$. In a run of ARp, let
iteration $k$ be before termination and successful. Then $x_{k+1} = x_k + s_k$, and

* (4.1.20) $\|s_k\|^p \ge \dfrac{p!}{L + \sigma_{\max} + \theta_1 \, p!} \|\nabla f(x_{k+1})\|$;
* (4.1.21) if $q \ge 2$, $\|s_k\|^{p-1} \ge \dfrac{(p-1)!}{L + \sigma_{\max} + \theta_2 (p-1)!}
  \max(0, -\lambda_{\min}[\nabla^2 f(x_{k+1})])$;
* (4.1.22) if $q \ge 3$, $\|s_k\|^{p-2} \ge \dfrac{(p-2)!}{L + \sigma_{\max} + \theta_3 (p-2)!}
  |\nabla^3 f(x_{k+1})[d]^3|$ for every $d \in \mathcal{M}_{k+1}$;
* (4.1.23) if $q \ge 2$, $|\nabla^2 f(x_{k+1})[d]^2| \le \dfrac{L + \sigma_{\max} + \theta_2
  (p-1)!}{(p-1)!} \|s_k\|^{p-1} = \|s_k\|^{p-1} / \kappa_{s2}$ for every
  $d \in \mathcal{M}_{k+1}$.

The set $\mathcal{M}_{k+1}$ is `Optimization.smallCurvatureDirections` applied to
`iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)` with the bound
$\theta_2 \|s_k\|^{p-1}$. -/
theorem step_lower_bounds (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x (k + 1) = x k + s k ∧
    (p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !) * ‖fderiv ℝ f (x (k + 1))‖ ≤
      ‖s k‖ ^ p ∧
    (2 ≤ q → ((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) *
      max 0 (-minCurvature (iteratedFDeriv ℝ 2 f (x (k + 1)))) ≤ ‖s k‖ ^ (p - 1)) ∧
    (3 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      ((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 2)) ∧
    (2 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| ≤
        (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1)) := by
  have hx : x (k + 1) = x k + s k :=
    h.toIsARRun.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs
  have hK := constant_pos (P := P) hL0
  rw [hx]
  refine ⟨rfl, ?_, fun hq => ?_, fun hq d hd => ?_, fun hq d hd => ?_⟩
  · exact div_mul_le_of_le_div_mul (hK _ P.θ₁_pos p) (by positivity)
      (h.norm_fderiv_le hf hL hp hk)
  · have h1 := h.neg_minCurvature_le hf hL (hq.trans hqp) hq hk
    refine div_mul_le_of_le_div_mul (hK _ P.θ₂_pos (p - 1)) (by positivity) ?_
    exact max_le (by have := hK _ P.θ₂_pos (p - 1); positivity) h1
  · exact div_mul_le_of_le_div_mul (hK _ P.θ₃_pos (p - 2)) (by positivity)
      (h.abs_third_le hf hL (hq.trans hqp) hq hk hd)
  · exact h.abs_second_le hf hL (hq.trans hqp) hk hd

/-- From a step bound $a v \le t^m$ and a decrease $D \ge c \, t^n$ with $a, v, t, c \ge 0$ and
$m > 0$, the decrease satisfies $D \ge c \, a^{n/m} v^{n/m}$. -/
private theorem decrease_ge_of_step_bound {a v t c D : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hv : 0 ≤ v)
    (ht : 0 ≤ t) (hm : 0 < m) (hc : 0 ≤ c) (hstep : a * v ≤ t ^ m) (hD : c * t ^ n ≤ D) :
    c * a ^ ((n : ℝ) / m) * v ^ ((n : ℝ) / m) ≤ D := by
  rw [mul_assoc, ← Real.mul_rpow ha hv]
  exact (mul_le_mul_of_nonneg_left (Real.rpow_div_le_pow_of_le_pow (mul_nonneg ha hv) ht hm hstep)
    hc).trans hD

/-- **Lemma 4.1.4** of [cartis2022evaluation] on a successful iteration. Let $f$ be $C^p$ with
$\nabla^p f$ Lipschitz continuous on $E$ with constant $L \ge 0$, let $1 \le p$ and $q \le p$,
and let $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$. In a run of ARp, let
iteration $k$ be before termination and successful. Then

* (4.1.37) $f(x_k) - f(x_{k+1}) \ge \dfrac{\eta_1 \sigma_{\min}}{(p+1)!} \|s_k\|^{p+1}$;
* (4.1.31) $f(x_k) - f(x_{k+1}) \ge \kappa_1 \|\nabla f(x_{k+1})\|^{(p+1)/p}$;
* (4.1.33) if $q \ge 2$, $f(x_k) - f(x_{k+1}) \ge \kappa_2 \max(0, -\lambda_{\min}[\nabla^2
  f(x_{k+1})])^{(p+1)/(p-1)}$;
* (4.1.35) if $q \ge 3$, $f(x_k) - f(x_{k+1}) \ge \kappa_3 |\nabla^3
  f(x_{k+1})[d]^3|^{(p+1)/(p-2)}$ for every $d \in \mathcal{M}_{k+1}$.

The constants are, as in (4.1.32), (4.1.34) and (4.1.36), for $j = 1, 2, 3$,
$$\kappa_j = \frac{\eta_1 \sigma_{\min}}{(p+1)!} \Bigl(\frac{(p-j+1)!}{L + \sigma_{\max} +
  \theta_j (p-j+1)!}\Bigr)^{(p+1)/(p-j+1)}.$$

The powers with fractional exponents are real powers `Real.rpow`. -/
theorem decrease_ge (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) ∧
    P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p) *
        ‖fderiv ℝ f (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤ f (x k) - f (x (k + 1)) ∧
    (2 ≤ q → P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        (max 0 (-minCurvature (iteratedFDeriv ℝ 2 f (x (k + 1))))) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ f (x k) - f (x (k + 1))) ∧
    (3 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤
          f (x k) - f (x (k + 1))) := by
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  obtain ⟨-, hdec⟩ := h.toIsARRun.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk)
    (h.step_spec hk).decrease hs
  have h37 : P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) := by
    refine le_trans ?_ hdec
    have := P.η₁_pos
    rw [show P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) =
      P.η₁ * (P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) by ring]
    gcongr
    exact hσ.1
  obtain ⟨-, b1, b2, b3, -⟩ := h.step_lower_bounds hf hL hL0 hp hqp hk hs
  have hc : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_nonneg; positivity
  have hK := constant_pos (P := P) hL0
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨h37, ?_, fun hq => ?_, fun hq d hd => ?_⟩
  · rw [hn]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₁_pos p; positivity) (norm_nonneg _)
      (norm_nonneg _) (by omega) hc b1 h37
  · have hm : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hp)]; push_cast; ring
    rw [hn, hm]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₂_pos (p - 1); positivity) (le_max_left _ _)
      (norm_nonneg _) (by omega) hc (b2 hq) h37
  · have hm : ((p : ℝ) - 2) = ((p - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hn, hm]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₃_pos (p - 2); positivity) (abs_nonneg _)
      (norm_nonneg _) (by omega) hc (b3 hq d hd) h37

end IsARpRun

/-!
### Existence of runs

For $q = 3$ an admissible step need not exist when the test fails. Take $E = \mathbb{R}$, $p = 3$
and $f(x) = a x^2 / 2 + b x^3 / 6 + x^4$ with $0 < a \le \varepsilon_2$ and $|b| > \varepsilon_3$,
and take $x_0 = 0$ and $\sigma_0 \ge b^2 / (3a)$. The test (4.1.5)–(4.1.9) fails at $x_0$, because
$\mathcal{M}_0 = \{\pm 1\}$ and $|\nabla^3 f(0)| = |b| > \varepsilon_3$. But $m_0(s) = s^2 (a/2 + b
s / 6 + \sigma_0 s^2 / 24) \ge 0 = m_0(0)$, so the model decrease (4.1.10) has no solution.
Existence is therefore proved without further hypotheses for $q \le 2$
(`Optimization.exists_isARpRun`), and for general $q$ under the hypothesis that an admissible step
exists whenever the test fails (`Optimization.exists_isARpRun_prev`).
-/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}

/-- **Existence of ARp steps for $q \le 2$**, Section 4.1.1 of [cartis2022evaluation]. Let $E$ be
finite-dimensional, let $f$ be $C^p$ at $x$, and let $p \ge 1$, $q \le 2$, $p \ge 2$ if $q = 2$,
and $\sigma > 0$. Assume that $\nabla f(x) \ne 0$, or that $q = 2$ and
$\lambda_{\min}[\nabla^2 f(x)] < 0$. Then there is a step $s$ that satisfies the ARp step
conditions at $x$ with weight $\sigma$.

The proof takes a global minimizer of the model. The gradient and the Hessian of the model at
$0$ are those of $f$ at $x$, so $0$ is not a global minimizer of the model. -/
theorem exists_isARpStep [FiniteDimensional ℝ E] (P : ARpParams) {x : E} {σ : ℝ}
    (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) (hq : q ≤ 2) (hqp : 2 ≤ q → 2 ≤ p) (hσ : 0 < σ)
    (hcrit : fderiv ℝ f x ≠ 0 ∨ (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 f x) < 0)) :
    ∃ s, IsARpStep f p P q x σ s := by
  obtain ⟨s, hmin, hd, hc, -⟩ :=
    exists_isMinOn_regularizedModel (D := ftaylorSeries ℝ f x) (σ := σ) hσ hp
  refine ⟨s, ⟨?_, ?_, fun _ => ?_, fun h3 => absurd h3 (by omega)⟩⟩
  · rcases hcrit with h1 | ⟨h2, h2'⟩
    · exact regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin
        (by rwa [fderiv_regularizedModel_ftaylorSeries_zero hf hp])
    · exact regularizedModel_lt_of_isMinOn_of_minCurvature_neg (hqp h2) hmin
        (by rwa [iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero hf (hqp h2)])
  · rw [hd, norm_zero]
    exact mul_nonneg P.θ₁_pos.le (by positivity)
  · exact (neg_nonpos.2 (mul_nonneg P.θ₂_pos.le (by positivity))).trans hc

/-- **Existence of ARp runs for $q \le 2$**, Algorithm 4.1.1 of [cartis2022evaluation]. Let $E$ be
finite-dimensional, let $f$ be $C^p$, and let $p \ge 1$, $q \le 2$, and $p \ge 2$ if $q = 2$.
Let the termination test read only the current iterate, and let its failure at $y$ imply
$\nabla f(y) \ne 0$, or $q = 2$ and $\lambda_{\min}[\nabla^2 f(y)] < 0$. Then for every $x_0$
there is a run of ARp from $x_0$.

The tests (4.1.5)–(4.1.7) with $\varepsilon_1 > 0$ have this property. -/
theorem exists_isARpRun [FiniteDimensional ℝ E] (P : ARpParams) (hf : ContDiff ℝ p f)
    (hp : 1 ≤ p) (hq : q ≤ 2) (hqp : 2 ≤ q → 2 ≤ p) {test : E → Prop}
    (htest : ∀ y, ¬ test y →
      fderiv ℝ f y ≠ 0 ∨ (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 f y) < 0))
    (x₀ : E) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ IsARpRun f p P q (fun k => test (x k)) x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := test) (stepOK := fun y σ s => IsARpStep f p P q y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ _ _ hσ ht => by
      obtain ⟨s, hs⟩ := exists_isARpStep P hf.contDiffAt hp hq hqp hσ (htest y ht)
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hrun⟩

/-- **Existence of ARp runs for any $q$, under an explicit hypothesis**, Algorithm 4.1.1 of
[cartis2022evaluation]. Let the termination test read the current iterate, the current weight
and the previous iteration (`Optimization.prevIterate`). Assume that for every previous
iteration, every iterate $y$ and every weight $\sigma \ge \sigma_{\min}$ with $\sigma > 0$ at
which the test fails, there is a step that satisfies the ARp step conditions at $y$ with weight
$\sigma$. Then for every $x_0$ there is a run of ARp from $x_0$.

The third-order test reads the previous iteration through the set $\mathcal{M}_k$, which
(4.1.14) builds from the previous model. For $q = 3$ the hypothesis can fail; see the sectioning
comment above. -/
theorem exists_isARpRun_prev (P : ARpParams) {test : Option (E × ℝ × E) → E → ℝ → Prop}
    (hstep : ∀ prev y σ, P.σmin ≤ σ → 0 < σ → ¬ test prev y σ → ∃ s, IsARpStep f p P q y σ s)
    (x₀ : E) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARpRun f p P q (fun k => test (prevIterate x s σ k) (x k) (σ k)) x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun_prev P.toARParams (Inv := fun _ => True)
    (test := test) (stepOK := fun y σ s => IsARpStep f p P q y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun prev y σ _ hσ hσ0 ht => by
      obtain ⟨s, hs⟩ := hstep prev y σ hσ hσ0 ht
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hrun⟩

end Existence

end Optimization
