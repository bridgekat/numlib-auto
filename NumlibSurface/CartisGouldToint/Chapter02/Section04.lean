/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.ARRun
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis, Gould and Toint, Section 2.4: The adaptive-regularization method

This module formalizes §2.4 of [cartis2022evaluation]: the first-order adaptive-regularization
algorithm AR1 for the minimization of a function $f : \mathbb{R}^n \to \mathbb{R}$. At iteration $k$
the method minimizes the regularized model (2.4.1)
$$m_k(s) = T_{f,1}(x_k, s) + \tfrac12 \sigma_k \|s\|^2 = f(x_k) + \langle \nabla f(x_k), s \rangle +
  \tfrac12 \sigma_k \|s\|^2,$$
whose minimizer is $s_k = -\nabla f(x_k)/\sigma_k$. It accepts the trial point when the ratio
(2.4.3) of achieved to predicted decrease is at least $\eta_1$, and it updates the regularization
weight $\sigma_k$ by (2.4.4). The method stops at the first iterate with
$\|\nabla f(x_k)\| \le \epsilon$.

Under f.Bb and f.gL, AR1 stops after $O(\epsilon^{-2})$ evaluations of $f$ and $\nabla f$ (Theorem
2.4.4), and this order is attained (Theorem 2.4.5). AR1 is an instance of the generic
adaptive-regularization run of `Numlib.Optimization.ModelBased.ARRun`. Section 2.5 of the source has
no numbered results.

## Main definitions

* (2.4.1), `CartisGouldToint.Chapter02.ar1Model`: the regularized model
  $m(s) = T_{f,1}(x, s) + \frac12 \sigma \|s\|^2$.
* (2.4.2), `CartisGouldToint.Chapter02.ARParams`: the constants of adaptive-regularization methods,
  also used by AR2 and ARp in later chapters.
* Algorithm 2.4.1, `CartisGouldToint.Chapter02.algorithm_2_4_1`: AR1 as a predicate on the sequences
  of a run.
* (2.4.9), `CartisGouldToint.Chapter02.sigmaMaxAR1`: the bound $\sigma_{\max} = \max(\sigma_0,
  \gamma_3 L / (2(1 - \eta_2)))$ on the regularization weights.
* (2.4.11), `CartisGouldToint.Chapter02.kappaSAR1`: the constant $\kappa^S_{\mathrm{AR1}}$ of the
  bound on successful iterations.
* Theorem 2.4.4, `CartisGouldToint.Chapter02.kappaAAR1` and `CartisGouldToint.Chapter02.kappaCAR1`:
  the constants $\kappa^A_{\mathrm{AR1}}$ and $\kappa^C_{\mathrm{AR1}}$ of the evaluation bound.

## Main results

* (2.4.5)–(2.4.7), `CartisGouldToint.Chapter02.ar1_step_eq`: the model minimizer is
  $s = -\nabla f(x)/\sigma$, the Taylor decrease is $\|\nabla f(x)\|^2/\sigma$, and $\rho = \sigma
  (f(x) - f(x + s))/\|\nabla f(x)\|^2$.
* `CartisGouldToint.Chapter02.exists_algorithm_2_4_1`: an AR1 run exists from every starting point.
* Lemma 2.4.1, `CartisGouldToint.Chapter02.lemma_2_4_1`: while $\sigma_k \le \sigma_{\max}$, the
  number of iterations is bounded by a multiple of the number of successful iterations plus a
  constant.
* Lemma 2.4.2, `CartisGouldToint.Chapter02.lemma_2_4_2`: under f.gL, $\sigma_k \le \max(\sigma_0,
  \gamma_3 L/(2(1 - \eta_2)))$.
* Lemma 2.4.3, `CartisGouldToint.Chapter02.lemma_2_4_3`: before termination there are at most
  $\kappa^S_{\mathrm{AR1}} (f(x_0) - f_{\mathrm{low}})/\epsilon^2$ successful iterations.
* Theorem 2.4.4, `CartisGouldToint.Chapter02.theorem_2_4_4`: AR1 stops after $O(\epsilon^{-2})$
  evaluations of $f$ and of $\nabla f$.
* Theorem 2.4.5, `CartisGouldToint.Chapter02.theorem_2_4_5`: there is a one-dimensional example on
  which AR1 needs exactly $\epsilon^{-2} + 1$ evaluations.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* The Taylor model $T_{f,1}(x, \cdot)$ is built from `ftaylorSeries ℝ f x`, and the predicted
  decrease $T_{f,1}(x, 0) - T_{f,1}(x, s)$ is `FormalMultilinearSeries.taylorDecrement`.

## Implementation notes

* The model is `Optimization.regularizedModel (ftaylorSeries ℝ f x) 1 σ`, and the ratio (2.4.3) is
  `Optimization.taylorRatio f 1 x s`.
* An AR1 run is `Optimization.IsARRun`. Steps 3–4 are `Optimization.ARAcceptance`, and the update
  (2.4.4) is `Optimization.ARUpdate`.

## Deviations from the source

* **Equations (2.4.1), (2.4.3), and (2.4.7)** (reading). The model formula is defined
  for any regularization weight, with positivity enforced by the run. The ratio uses
  the Taylor decrease as its denominator and is total at a zero gradient. A run
  terminates before using that case. See `CartisGouldToint.Chapter02.ar1Model` and
  `CartisGouldToint.Chapter02.ar1_step_eq`.
* **Lemma 2.4.2** (reading). The parameter bound holds through the termination index.
  Later sequence values are unconstrained by the run predicate.
* **Proof of Lemma 2.4.3** (typo). The gradient test is required starting at index $0$, since
  $\mathcal{S}_k$ can contain $0$. See `CartisGouldToint.Chapter02.lemma_2_4_3`.
* **"Reasonable values" after Algorithm 2.4.1** (typo). The values $\gamma_1 = 2$,
  $\gamma_2 = \gamma_3 = 0.5$ contradict (2.4.2). They are not used.
* **Theorem 2.4.5** (reading). The example assumes an integral $\epsilon^{-2}$ and
  counts the initial evaluations, for $\epsilon^{-2}+1$ objective and gradient
  evaluations.
-/

open Set Finset
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- **Equation (2.4.2)** of [cartis2022evaluation]. The constants of an adaptive-regularization
method consist of an initial weight $\sigma_0 > 0$, a lower bound
$\sigma_{\min} \in (0, \sigma_0]$, acceptance thresholds $0 < \eta_1 \le \eta_2 < 1$ and update
factors $0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$.

The structure extends `Optimization.ARParams`, which allows $\sigma_{\min} = 0$ and
$\gamma_2 = \gamma_3$, by the strict inequalities $\sigma_{\min} > 0$ and $\gamma_2 < \gamma_3$.
The same constants serve AR2 and ARp in later chapters. -/
structure ARParams extends Optimization.ARParams where
  /-- The lower bound on the regularization weight satisfies $\sigma_{\min} > 0$. -/
  σmin_pos : 0 < σmin
  /-- The update factors satisfy $\gamma_2 < \gamma_3$. -/
  γ₂_lt_γ₃ : γ₂ < γ₃

/-- **Equation (2.4.1)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$x \in \mathbb{R}^n$ and $\sigma \in \mathbb{R}$. The **regularized model** of AR1 at $x$ is
$$m(s) = T_{f,1}(x, s) + \tfrac12 \sigma \|s\|^2,$$
where $T_{f,1}(x, s) = f(x) + \langle \nabla f(x), s \rangle$ is the first-order Taylor
polynomial of $f$ at $x$.

The model is `Optimization.regularizedModel` of `ftaylorSeries ℝ f x` with $p = 1$; its explicit
form is `CartisGouldToint.Chapter02.ar1Model_apply`.

**Reading.** The raw model is defined for every real weight, with positive weights enforced in the
algorithm.
-/
noncomputable def ar1Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  regularizedModel (ftaylorSeries ℝ f x) 1 σ

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)} {σ : ℝ}

/-- The AR1 model is $m(s) = f(x) + \langle \nabla f(x), s \rangle + \frac12 \sigma \|s\|^2$.

**Reading.** The displayed model formula also holds for zero or negative regularization weights.
-/
theorem ar1Model_apply :
    ar1Model f x σ s = f x + ⟪gradient f x, s⟫ + 1 / 2 * σ * ‖s‖ ^ 2 := by
  rw [ar1Model, regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_one_eq_inner,
    show ((Nat.factorial (1 + 1) : ℕ) : ℝ) = 2 by norm_num [Nat.factorial]]
  ring

/-- The first-order Taylor decrease is $T_{f,1}(x, 0) - T_{f,1}(x, s) = -\langle \nabla f(x), s
\rangle$. -/
theorem taylorDecrement_one :
    (ftaylorSeries ℝ f x).taylorDecrement 1 s = -⟪gradient f x, s⟫ := by
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_one_eq_inner]
  ring

/-- Completing the square: for $\sigma \neq 0$,
$$m(s) = f(x) - \frac{\|\nabla f(x)\|^2}{2\sigma} + \frac12 \sigma \|s + \sigma^{-1} \nabla
  f(x)\|^2.$$
-/
theorem ar1Model_eq_sq (hσ : σ ≠ 0) :
    ar1Model f x σ s = f x - ‖gradient f x‖ ^ 2 / (2 * σ) +
      1 / 2 * σ * ‖s + σ⁻¹ • gradient f x‖ ^ 2 := by
  rw [ar1Model_apply, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm]
  field_simp
  ring

/-- **Equations (2.4.5)–(2.4.7)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
$x \in \mathbb{R}^n$ and $\sigma > 0$, and let $m$ be the AR1 model at $x$ with weight $\sigma$.
Then:

* (2.4.5) a step $s$ is a global minimizer of $m$ if and only if $s = -\nabla f(x)/\sigma$;
* (2.4.6) the Taylor decrease at this step is $T_{f,1}(x, 0) - T_{f,1}(x, -\nabla f(x)/\sigma) =
  \|\nabla f(x)\|^2/\sigma$;
* (2.4.7) the ratio of achieved to predicted decrease at this step is
$$\rho = \frac{\sigma \left( f(x) - f(x - \nabla f(x)/\sigma) \right)}{\|\nabla f(x)\|^2}.$$

The ratio is `Optimization.reductionRatio` with the Taylor decrease as predicted decrease. When
$\nabla f(x) = 0$, both sides of (2.4.7) are $0$ by Lean's division.

**Reading.** Consolidates unique minimization, Taylor decrease and ratio, with total ratio at zero
gradient.
-/
theorem ar1_step_eq (hσ : 0 < σ) :
    (IsMinOn (ar1Model f x σ) univ s ↔ s = -(σ⁻¹ • gradient f x)) ∧
      (ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x)) =
        ‖gradient f x‖ ^ 2 / σ ∧
      reductionRatio f x (-(σ⁻¹ • gradient f x))
          ((ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x))) =
        σ * (f x - f (x + -(σ⁻¹ • gradient f x))) / ‖gradient f x‖ ^ 2 := by
  have hdec : (ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x)) =
      ‖gradient f x‖ ^ 2 / σ := by
    rw [taylorDecrement_one, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  refine ⟨⟨fun hmin => ?_, fun hs => ?_⟩, hdec, ?_⟩
  · have := hmin (mem_univ (-(σ⁻¹ • gradient f x)))
    simp only [mem_ofPred_eq] at this
    rw [ar1Model_eq_sq hσ.ne', ar1Model_eq_sq hσ.ne', neg_add_cancel, norm_zero] at this
    have h0 : ‖s + σ⁻¹ • gradient f x‖ ^ 2 ≤ 0 := by nlinarith
    have : s + σ⁻¹ • gradient f x = 0 := by
      have := le_antisymm h0 (sq_nonneg _)
      exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)
    exact eq_neg_of_add_eq_zero_left this
  · intro y _
    simp only [mem_ofPred_eq]
    rw [ar1Model_eq_sq hσ.ne', ar1Model_eq_sq hσ.ne', hs, neg_add_cancel, norm_zero]
    have : 0 ≤ 1 / 2 * σ * ‖y + σ⁻¹ • gradient f x‖ ^ 2 := by positivity
    linarith
  · rw [hdec, reductionRatio_def]
    rcases eq_or_ne ‖gradient f x‖ 0 with h0 | h0
    · simp [h0]
    · field_simp

end Model

/-- **Algorithm 2.4.1** of [cartis2022evaluation] (AR1). Let $f : \mathbb{R}^n \to \mathbb{R}$, let
the constants (2.4.2) be given, and let $\epsilon \in \mathbb{R}$. Sequences of iterates $x_k$,
trial steps $s_k$ and regularization weights $\sigma_k$ form an **AR1 run** if $\epsilon > 0$,
$\sigma_0$ is the initial weight of the constants, and the following holds at every iteration
$k$ at which the test $\|\nabla f(x_j)\| \le \epsilon$ has failed for all $j \le k$.

* Step 2: $s_k$ is a global minimizer of the model $m_k$ of (2.4.1).
* Step 3: $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise, where
  $\rho_k$ is the ratio (2.4.3) of $f(x_k) - f(x_k + s_k)$ to
  $T_{f,1}(x_k, 0) - T_{f,1}(x_k, s_k)$.
* Step 4: the update (2.4.4), that is, $\sigma_{k+1} \in [\max(\sigma_{\min}, \gamma_1
  \sigma_k), \sigma_k]$ if $\rho_k \ge \eta_2$, $\sigma_{k+1} \in [\sigma_k, \gamma_2 \sigma_k]$
  if $\eta_1 \le \rho_k < \eta_2$, and $\sigma_{k+1} \in [\gamma_2 \sigma_k, \gamma_3 \sigma_k]$
  if $\rho_k < \eta_1$.

The run stops at the first $k$ with $\|\nabla f(x_k)\| \le \epsilon$. The structure is the
generic run `Optimization.IsARRun` with no termination test after the step and the ratio
`Optimization.taylorRatio f 1`. -/
structure algorithm_2_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARParams) (ε : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The accuracy level satisfies $\epsilon > 0$. -/
  ε_pos : 0 < ε
  /-- Steps 1–4 hold in the form of the generic adaptive-regularization run `Optimization.IsARRun`.
  -/
  run : IsARRun P.toARParams (fun k => ‖gradient f (x k)‖ ≤ ε)
    (fun k => IsMinOn (ar1Model f (x k) (σ k)) univ (s k)) (fun _ => False)
    (taylorRatio f 1 x s) x s σ

/-- Existence of runs of Algorithm 2.4.1 of [cartis2022evaluation]. Let
$f : \mathbb{R}^n \to \mathbb{R}$, let the constants (2.4.2) be given, let $\epsilon > 0$, and
let $x_0 \in \mathbb{R}^n$. Then there is an AR1 run that starts at $x_0$.

The proof takes the step $-\nabla f(x_k)/\sigma_k$ of (2.4.5) and the left ends of the intervals
of (2.4.4). -/
theorem exists_algorithm_2_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARParams) {ε : ℝ}
    (hε : 0 < ε) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_2_4_1 f P ε x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := fun y => ‖gradient f y‖ ≤ ε)
    (stepOK := fun y σ s => IsMinOn (ar1Model f y σ) univ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 1 t))
    (fun y σ _ _ hσ _ => ⟨_, (ar1_step_eq hσ).1.2 rfl, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hε, hrun⟩

namespace algorithm_2_4_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : ARParams} {ε : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- In an AR1 run, if the termination test fails at every iteration $j < k$, then $\sigma_k > 0$. -/
theorem sigma_pos (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : 0 < σ k :=
  h.run.sigma_pos (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

/-- In an AR1 run, at every iteration $k$ before termination, the step is
$s_k = -\nabla f(x_k)/\sigma_k$, as in (2.4.5). -/
theorem step_eq (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) : s k = -((σ k)⁻¹ • gradient f (x k)) :=
  ((ar1_step_eq (h.sigma_pos fun j hj => hk j hj.le)).1).1
    (h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk))

/-- In an AR1 run, at every iteration $k$ before termination, the Taylor decrease is
$T_{f,1}(x_k, 0) - T_{f,1}(x_k, s_k) = \|\nabla f(x_k)\|^2/\sigma_k$, as in (2.4.6). -/
theorem taylorDecrement_eq (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) = ‖gradient f (x k)‖ ^ 2 / σ k := by
  rw [h.step_eq hk]
  exact (ar1_step_eq (s := s k) (h.sigma_pos fun j hj => hk j hj.le)).2.1

/-- In an AR1 run, at every iteration $k$ before termination, the Taylor decrease
$T_{f,1}(x_k, 0) - T_{f,1}(x_k, s_k)$ is positive. -/
theorem taylorDecrement_pos (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    0 < (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) := by
  rw [h.taylorDecrement_eq hk]
  have : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have := h.sigma_pos fun j hj => hk j hj.le
  positivity

end algorithm_2_4_1

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : ARParams} {ε L flow : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 2.4.1** of [cartis2022evaluation]. Consider an AR1 run, and let $k$ be an iteration with
$\|\nabla f(x_j)\| > \epsilon$ for all $j < k$. Let $\sigma_{\max} \in \mathbb{R}$ with
$\sigma_k \le \sigma_{\max}$. Then (2.4.8) holds:
$$k \le |\mathcal{S}_k| \left( 1 + \frac{|\log \gamma_1|}{\log \gamma_2} \right) +
  \frac{\log(\sigma_{\max}/\sigma_0)}{\log \gamma_2},$$
where $\mathcal{S}_k = \{j \le k : \rho_j \ge \eta_1\}$ is the set of successful iterations up
to $k$.

The proof uses only the update (2.4.4). The set $\mathcal{S}_k$ is `Optimization.successSet`. -/
theorem lemma_2_4_1 (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) {σmax : ℝ} (hσ : σ k ≤ σmax) :
    (k : ℝ) ≤ (successSet (fun j => P.η₁ ≤ taylorRatio f 1 x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
  h.run.le_succ_count (IsARRun.forall_lt_not_stop_iff.2 hk) hσ

/-- The bound (2.4.9) of [cartis2022evaluation] on the regularization weights,
$$\sigma_{\max} = \max\left( \sigma_0, \frac{\gamma_3 L}{2(1 - \eta_2)} \right).$$
It is `Optimization.arSigmaMax` with the Lipschitz constant $L/2$; the explicit form is
`CartisGouldToint.Chapter02.sigmaMaxAR1_eq`. -/
noncomputable def sigmaMaxAR1 (P : ARParams) (L : ℝ) : ℝ :=
  arSigmaMax P.toARParams (L / 2)

/-- The bound $\sigma_{\max}$ of AR1 equals $\max(\sigma_0, \gamma_3 L / (2(1 - \eta_2)))$, the
formula (2.4.9). -/
theorem sigmaMaxAR1_eq (P : ARParams) (L : ℝ) :
    sigmaMaxAR1 P L = max P.σ₀ (P.γ₃ * L / (2 * (1 - P.η₂))) := by
  rw [sigmaMaxAR1, arSigmaMax_def, mul_div_assoc', div_div]

/-- The bound $\sigma_{\max}$ of AR1 is positive. -/
theorem sigmaMaxAR1_pos (P : ARParams) (L : ℝ) : 0 < sigmaMaxAR1 P L :=
  arSigmaMax_pos _ _

/-- **Lemma 2.4.2** of [cartis2022evaluation]. Assume f.gL with constant $L$ and consider an AR1
run. Let $k$ be an iteration with $\|\nabla f(x_j)\| > \epsilon$ for all $j < k$. Then (2.4.9)
holds:
$$\sigma_k \le \max\left( \sigma_0, \frac{\gamma_3 L}{2(1 - \eta_2)} \right).$$
So the bound holds at every iteration up to and including the termination index.

**Reading.** The uniform upper bound holds through algorithm termination, without a condition on
sequence tails.
-/
theorem lemma_2_4_2 (hf : AssumptionGL f L) (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : σ k ≤ sigmaMaxAR1 P L := by
  have hforce : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => ‖gradient f (x k)‖ ≤ ε)
      (fun _ => False) j) → L / (2 * (1 - P.η₂)) ≤ σ k → P.η₂ ≤ taylorRatio f 1 x s k := by
    intro k hk hσk
    rw [IsARRun.forall_le_not_stop_iff] at hk
    have hσ := h.sigma_pos fun j hj => hk j hj.le
    have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
    have hs : s k ≠ 0 := by
      rw [h.step_eq hk, neg_ne_zero, smul_ne_zero_iff]
      exact ⟨inv_ne_zero hσ.ne', norm_pos_iff.1 hg⟩
    have hdec : 1 * σ k * ‖s k‖ ^ (1 + 1) ≤ (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) := by
      rw [h.taylorDecrement_eq hk, h.step_eq hk, norm_neg, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.2 hσ.le)]
      apply le_of_eq
      rw [show (1 + 1 : ℕ) = 2 from rfl]
      field_simp
    refine le_reductionRatio_of_lipschitz convex_univ (fun y _ => hf.contDiff.contDiffAt)
      hf.iteratedFDerivLipschitzOn (mem_univ _) (mem_univ _) hs one_pos hσ hdec ?_
    rw [div_le_iff₀ (by linarith [P.η₂_lt_one])] at hσk
    norm_num [Nat.factorial]
    linarith
  have := (h.run.sigma_le_max hforce (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl).2.2
  rw [sigmaMaxAR1_eq]
  convert this using 2
  ring

/-- The constant of (2.4.11) of [cartis2022evaluation],
$$\kappa^S_{\mathrm{AR1}} = \frac{1}{\eta_1} \max\left( \sigma_0, \frac{\gamma_3 L}{2(1 -
  \eta_2)} \right).$$
-/
noncomputable def kappaSAR1 (P : ARParams) (L : ℝ) : ℝ :=
  P.η₁⁻¹ * sigmaMaxAR1 P L

/-- Under f.gL, a successful AR1 iteration $k$ before termination decreases $f$ by at least
$\eta_1 \epsilon^2/\sigma_{\max}$. -/
private theorem sub_ge_of_succ (hf : AssumptionGL f L) (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) (hs : P.η₁ ≤ taylorRatio f 1 x s k) :
    P.η₁ * ε ^ 2 / sigmaMaxAR1 P L ≤ f (x k) - f (x (k + 1)) := by
  have hsub := (h.run.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k))
    (IsARRun.forall_le_not_stop_iff.2 hk) rfl (h.taylorDecrement_pos hk) hs).2
  rw [h.taylorDecrement_eq hk] at hsub
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_2_4_2 hf h fun j hj => hk j hj.le
  have hg : ε ≤ ‖gradient f (x k)‖ := (not_le.1 (hk k le_rfl)).le
  have h1 : ε ^ 2 / sigmaMaxAR1 P L ≤ ‖gradient f (x k)‖ ^ 2 / σ k :=
    div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ h.ε_pos.le hg 2) hσ hσmax
  have := mul_le_mul_of_nonneg_left h1 P.η₁_pos.le
  rw [mul_div_assoc]
  linarith

/-- **Lemma 2.4.3** of [cartis2022evaluation]. Assume f.Bb with lower bound $f_{\mathrm{low}}$ and
f.gL with constant $L$, and consider an AR1 run. Let $k$ be an iteration with
$\|\nabla f(x_j)\| > \epsilon$ for all $j \le k$. Then the number of successful iterations up to
$k$ satisfies (2.4.11):
$$|\mathcal{S}_k| \le \kappa^S_{\mathrm{AR1}} \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2}.$$

**Typo.** The proof in the source writes $j \in [1 : k]$ for the gradient test. The hypothesis
uses $j \in [0 : k]$, since $0$ can belong to the success set $\mathcal{S}_k$ in the sum.

The set $\mathcal{S}_k$ is `Optimization.successSet`. -/
theorem lemma_2_4_3 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 1 x s j) k).card : ℝ) ≤
      kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
  have hc : 0 < P.η₁ * ε ^ 2 / sigmaMaxAR1 P L := by
    have := P.η₁_pos; have := h.ε_pos; have := sigmaMaxAR1_pos P L; positivity
  have hcard := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
    (fun j hj hs => by
      rw [h.run.eq_of_not_succ (IsARRun.forall_le_not_stop_iff.2 fun i hi => hk i (hi.trans hj))
        (not_le.1 hs)])
    (fun j hj hs => sub_ge_of_succ hf h (fun i hi => hk i (hi.trans hj)) hs) (hb (x (k + 1)))
  refine hcard.trans_eq ?_
  have := P.η₁_pos; have := h.ε_pos; have := sigmaMaxAR1_pos P L
  rw [kappaSAR1]
  field_simp

/-- The constant $\kappa^A_{\mathrm{AR1}}$ of Theorem 2.4.4 of [cartis2022evaluation],
$$\kappa^A_{\mathrm{AR1}} = \frac{1}{\eta_1} \max\left( \sigma_0, \frac{\gamma_3 L}{1 - \eta_2}
  \right) \left( 1 + \frac{|\log \gamma_1|}{\log \gamma_2} \right).$$
The maximum is `Optimization.arSigmaMax` with the constant $L$. -/
noncomputable def kappaAAR1 (P : ARParams) (L : ℝ) : ℝ :=
  P.η₁⁻¹ * arSigmaMax P.toARParams L * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- The constant $\kappa^A_{\mathrm{AR1}}$ equals $\eta_1^{-1} \max(\sigma_0, \gamma_3 L/(1 -
\eta_2)) (1 + |\log \gamma_1|/\log \gamma_2)$, the formula of the source. -/
theorem kappaAAR1_eq (P : ARParams) (L : ℝ) :
    kappaAAR1 P L =
      P.η₁⁻¹ * max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) * (1 + |Real.log P.γ₁| / Real.log P.γ₂) :=
  rfl

/-- The constant $\kappa^C_{\mathrm{AR1}}$ of Theorem 2.4.4 of [cartis2022evaluation],
$$\kappa^C_{\mathrm{AR1}} = \frac{\log \max\left( 1, \frac{\gamma_3 L}{\sigma_0 (1 - \eta_2)}
  \right)}{\log \gamma_2} + 1.$$
-/
noncomputable def kappaCAR1 (P : ARParams) (L : ℝ) : ℝ :=
  Real.log (max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂)))) / Real.log P.γ₂ + 1

/-- **Theorem 2.4.4** of [cartis2022evaluation]. Assume f.Bb with lower bound $f_{\mathrm{low}}$ and
f.gL with constant $L$, and consider an AR1 run. Then the run terminates: there is a first
iteration $k_\epsilon$ with $\|\nabla f(x_{k_\epsilon})\| \le \epsilon$. Up to termination the
method uses at most
$$\kappa^A_{\mathrm{AR1}} \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2} +
  \kappa^C_{\mathrm{AR1}}$$
evaluations of $f$ and at most
$$\kappa^S_{\mathrm{AR1}} \frac{f(x_0) - f_{\mathrm{low}}}{\epsilon^2} + 1$$
evaluations of $\nabla f$.

The number of evaluations of $f$ is `Optimization.funEvalCount`, which is $k_\epsilon + 1$. The
number of evaluations of $\nabla f$ is `Optimization.derivEvalCount`: one at $x_0$ and one after
each successful iteration before $k_\epsilon$. -/
theorem theorem_2_4_4 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (h : algorithm_2_4_1 f P ε x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAAR1 P L * (f (x 0) - flow) / ε ^ 2 + kappaCAR1 P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε : ℝ) ≤
        kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set σmax := sigmaMaxAR1 P L
  have hσmax := sigmaMaxAR1_pos P L
  have hε := h.ε_pos
  have hη := P.η₁_pos
  have hδ : 0 < P.η₁ * ε ^ 2 / σmax := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease_of_le (σmax := σmax)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_2_4_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (h.taylorDecrement_pos (IsARRun.forall_le_not_stop_iff.1 hk)))
    (fun k _ => hb (x k))
    (fun k hk hs => sub_ge_of_succ hf h (IsARRun.forall_le_not_stop_iff.1 hk) hs)
  have hN : (f (x 0) - flow) / (P.η₁ * ε ^ 2 / σmax) =
      kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSAR1]; field_simp; rfl
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, hF.trans ?_, hD⟩
  -- comparison with the book's (larger) constants
  have hL0 := hf.nonneg
  have h1η := P.one_sub_η₂_pos
  have hlog := P.log_γ₂_pos
  have hf0 : 0 ≤ f (x 0) - flow := sub_nonneg.2 (hb (x 0))
  have hσ₁ : σmax ≤ max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) := by
    refine max_le_max le_rfl ?_
    rw [div_le_div_iff₀ (by positivity) h1η]
    nlinarith [P.γ₃_pos, mul_nonneg P.γ₃_pos.le hL0]
  have hA : kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) ≤
      kappaAAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSAR1, kappaAAR1_eq]
    have : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
    have : 0 ≤ (f (x 0) - flow) / ε ^ 2 := by positivity
    have key : P.η₁⁻¹ * σmax * ((f (x 0) - flow) / ε ^ 2) *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) ≤
        P.η₁⁻¹ * max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) * ((f (x 0) - flow) / ε ^ 2) *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by gcongr
    calc P.η₁⁻¹ * σmax * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂)
        = P.η₁⁻¹ * σmax * ((f (x 0) - flow) / ε ^ 2) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by ring
      _ ≤ _ := key
      _ = _ := by ring
  have hC : Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ≤ kappaCAR1 P L := by
    rw [kappaCAR1]
    gcongr
    · exact div_pos hσmax P.σ₀_pos
    · rw [div_le_iff₀ P.σ₀_pos, max_mul_of_nonneg _ _ P.σ₀_pos.le, one_mul]
      refine hσ₁.trans (max_le_max le_rfl (le_of_eq ?_))
      have := P.σ₀_pos
      field_simp
  calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1
      = kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        (Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1) := by ring
    _ ≤ _ := add_le_add hA hC

end Lemmas

/-! ### Theorem 2.4.5 -/

/-- **Theorem 2.4.5** of [cartis2022evaluation] (sharpness of AR1). For all AR1 constants there are
$L \ge 1$ and $f_{\mathrm{low}}$ with the following property. Let $\epsilon \in (0, 1]$ be such
that $k_\epsilon = \epsilon^{-2}$ is an integer. Then there are a function
$f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies f.Bb with $f_{\mathrm{low}}$ and f.gL with $L$,
and an AR1 run from $x_0 = 0$, such that:

* $\sigma_k = \sigma_0$ for all $k$;
* $\rho_k = 1$ for all $k < k_\epsilon$;
* the run terminates exactly at iteration $k_\epsilon$;
* the run uses $k_\epsilon + 1$ evaluations of $f$ and $k_\epsilon + 1$ evaluations of
  $\nabla f$.

The example is that of Theorem 2.2.3 with $t_{\mathrm{ini}} = \sigma_0^{-1}$. The condition that
$\epsilon^{-2}$ is an integer is stated as $k_\epsilon \epsilon^2 = 1$ for a natural number
$k_\epsilon$.

**Reading.** Uses integral inverse-square tolerances and includes initial evaluations in the
constant-weight unit-ratio example.
-/
theorem theorem_2_4_5 (P : ARParams) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ), x 0 = 0 ∧
          algorithm_2_4_1 f P ε x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < kε, taylorRatio f 1 x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
          funEvalCount kε = kε + 1 ∧
          derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε = kε + 1 := by
  set t := P.σ₀⁻¹
  have ht : 0 < t := inv_pos.2 P.σ₀_pos
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example ht
  refine ⟨L, flow, hL, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1 hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX t ε kε k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => -(P.σ₀⁻¹ • gradient f (x k))
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  have hbefore : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => ‖gradient f (x k)‖ ≤ ε)
      (fun _ => False) j) → k < kε := fun k hk =>
    not_le.1 fun hle => (IsARRun.forall_le_not_stop_iff.1 hk) kε hle hhit.test
  have hfx : ∀ j ≤ kε, f (x j) = slowF t ε kε j := fun j hj => (hfk j hj).1
  have hg : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    simp only [x]
    rw [(hfk k hk).2, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by rw [slowOmega_def]; positivity
    linarith
  have hstep : ∀ k < kε, x k + s k = x (k + 1) := fun k hk => by
    simp only [x, s]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hratio : ∀ k < kε, taylorRatio f 1 x s k = 1 := fun k hk => by
    have hgk : 0 < ‖gradient f (x k)‖ := by rw [hg k hk.le]; linarith [slowOmega_pos hε hk]
    rw [taylorRatio_def, (ar1_step_eq (s := 0) P.σ₀_pos).2.2, hstep k hk, hfx k hk.le,
      hfx (k + 1) hk, slowF_succ, ← hg k hk.le]
    simp only [t]
    rw [sub_sub_cancel]
    have := P.σ₀_pos.ne'
    have := hgk.ne'
    field_simp
  have hrun : algorithm_2_4_1 f P ε x s fun _ => P.σ₀ := by
    refine ⟨hε, rfl, fun k _ _ => (ar1_step_eq P.σ₀_pos).1.2 rfl, fun k hk => ?_⟩
    have hk := hbefore k hk
    have h1 : P.η₁ ≤ taylorRatio f 1 x s k := by
      rw [hratio k hk]; linarith [P.η₁_le_η₂, P.η₂_lt_one]
    refine ⟨by rw [ite_eq_left h1, hstep k hk], fun _ => ⟨max_le P.σmin_le_σ₀
      (mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one), le_rfl⟩, fun _ h2 => ?_,
      fun h3 => absurd h3 (not_lt.2 h1)⟩
    rw [hratio k hk] at h2
    exact absurd h2 (not_lt.2 (by linarith [P.η₂_lt_one]))
  refine ⟨f, hb, hgl, x, s, fun _ => P.σ₀, by simp [x, slowX], hrun, fun _ => rfl, hratio, hhit,
    funEvalCount_eq kε, ?_⟩
  classical
  rw [derivEvalCount_eq_count]
  have : Nat.count (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε = kε := by
    rw [Nat.count_eq_card_filter_range, filter_true_of_mem, card_range]
    intro k hk
    rw [hratio k (mem_range.1 hk)]
    linarith [P.η₁_le_η₂, P.η₂_lt_one]
  rw [this]

end CartisGouldToint.Chapter02
