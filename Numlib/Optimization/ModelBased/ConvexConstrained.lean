/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.ARpRun
import Numlib.Optimization.Optimality.ConstrainedMeasure

/-!
# Adaptive regularization over a convex set: one-iteration estimates

Let $E$ be a real inner product space, $C \subseteq E$ convex, and $f : E \to \mathbb{R}$ of class
$C^p$ at the points of $C$, with $\nabla^p f$ Lipschitz continuous on $C$ with constant $L \ge 0$
(assumption f.DpL.C of [cartis2022evaluation]). At a point $x \in C$ with weight $\sigma \ge 0$,
adaptive regularization uses the model
$$m(s) = T_{f,p}(x, s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1},$$
where $T_{f,p}(x, \cdot)$ is the Taylor polynomial of degree $p$ of $f$ at $x$. This file gives the
one-iteration estimates for this model over the convex feasible set $C$, as in §6.2 of
[cartis2022evaluation]. The same estimates serve §6.3 and §7.2, and with $C = E$ the unconstrained
method ARp of Chapter 4.

The feasible displacements at $y$ are $\mathcal{C}(y) = \{d \mid y + d \in C\}$. For a $j$-linear
form $A$ and a set $T$ of displacements, the criticality measure is
$$\omega(A, T) = \sup \{-A[d]^j \mid d \in T, \ \|d\| \le 1\},$$
and the first-order measure of $f$ at $y$ is $\omega_{f,\mathcal{C},1}(y) = \omega(\nabla f(y),
\mathcal{C}(y))$. The main estimate (6.2.23) compares the derivatives of $f$ at $x + s$ with those
of $m$ at $s$:
$$\bigl|\nabla^j f(x+s)[d]^j - \nabla^j m(s)[d]^j\bigr| \le \frac{L + \sigma}{(p-j+1)!}
  \|s\|^{p-j+1} \qquad (j \le p, \ \|d\| \le 1).$$
From it follow the step-length bound and the decrease of Lemma 6.2.4 for the first-order method
ARp1-CC (Algorithm 6.2.2).

## Main definitions

* `Optimization.IsFirstOrderCCStep`: the Step-2 conditions (6.2.29) of ARp1-CC.

## Main results

* `Optimization.abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall`: the estimate (6.2.23)
  for $\|d\| \le 1$.
* `Optimization.formCriticality_le_regularizedModel`: the measure of $f$ at $x + s$ exceeds the
  measure of the model at $s$ by at most $(L + \sigma) \|s\|^{p-j+1} / (p-j+1)!$.
* `Optimization.inter_closedBall_restrictedSteps_subset_regularizedModel`: the transfer
  (6.2.18)–(6.2.19) of restricted sets from $f$ to the model, the core of Lemma 6.2.1.
* `Optimization.isFirstOrderCCStep_univ_iff`: for $C = E$ the ARp1-CC conditions are the first-order
  ARp conditions (4.1.10)–(4.1.11).
* `Optimization.IsFirstOrderCCStep.measure_le_mul_pow`: the step-length bound
  $\omega_{f,\mathcal{C},1}(x+s) \le (L + \sigma + \theta p!) \|s\|^p / p!$.
* `Optimization.IsFirstOrderCCStep.sub_ge`: Lemma 6.2.4, the decrease of $f$ on a successful
  iteration.
* `Optimization.exists_isMinOn_regularizedModel_of_isClosed`: in finite dimension the model attains
  its minimum on every closed set that contains $0$.
* `Optimization.exists_isFirstOrderCCStep`: in finite dimension, ARp1-CC steps exist at every point
  that is not first-order critical.

## Implementation notes

* The model $m$ is `Optimization.regularizedModel (ftaylorSeries ℝ f x) p σ`.
* The measure $\omega(A, T)$ is `Optimization.formCriticality A T`.
* The set $\mathcal{C}(y)$ is `Optimization.feasibleSteps C y`. The model's set $\mathcal{M}^0(s)$
  of (6.2.1) is $\mathcal{C}(x + s)$.
* The estimate (6.2.23) holds only for $\|d\| \le 1$, because the error grows like $\|d\|^j$. The
  transfer (6.2.18)–(6.2.19) of the restricted sets $\mathcal{C}^1(x_{k+1}, \varepsilon_1)$ and
  $\mathcal{C}^2(\ldots)$ is therefore stated on the unit ball. The measures use only displacements
  in the unit ball.
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Estimates

variable {f : E → ℝ} {p : ℕ} {L σ : ℝ} {C : Set E} {x s : E}

/-- **Equation (6.2.23)** of [cartis2022evaluation], from the proof of Lemma 6.2.1, on the unit
ball. Let $C \subseteq E$ be convex, let $f$ be $C^p$ at every point of $C$, and let
$\nabla^p f$ be Lipschitz continuous on $C$ with constant $L \ge 0$. Let $x, x + s \in C$,
$\sigma \ge 0$, $j \le p$ and $\|d\| \le 1$. With $m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1} /
(p+1)!$,
$$\bigl|\nabla^j f(x+s)[d]^j - \nabla^j m(s)[d]^j\bigr| \le \frac{L + \sigma}{(p-j+1)!}
  \|s\|^{p-j+1}.$$

The model is `Optimization.regularizedModel (ftaylorSeries ℝ f x) p σ`, and $\nabla^j$ is
`iteratedFDeriv ℝ j`. The proof specializes
`Optimization.abs_iteratedFDeriv_apply_le_of_regularizedModel`. -/
theorem abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {d : E}
    (hd : d ∈ closedBall (0 : E) 1) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  refine (abs_iteratedFDeriv_apply_le_of_regularizedModel hC hf hL hx hxs hσ hj d).trans ?_
  have h1 : ‖d‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) (by simpa using hd)
  have h0 : 0 ≤ (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
  calc _ ≤ (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- **Measure form of (6.2.23)**, from the proof of Lemma 6.2.1 of [cartis2022evaluation]. Under the
hypotheses of `Optimization.abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall` ($C$
convex, $f$ of class $C^p$ on $C$ with $L$-Lipschitz $\nabla^p f$, $L \ge 0$, $x, x + s \in C$,
$\sigma \ge 0$, $j \le p$), let $T$ be a set of displacements with $0 \in T$. Then
$$\omega(\nabla^j f(x+s), T) \le \omega(\nabla^j m(s), T) + \frac{L + \sigma}{(p-j+1)!}
  \|s\|^{p-j+1},$$
where $\omega(A, T) = \sup \{-A[d]^j \mid d \in T, \|d\| \le 1\}$.

The measure $\omega$ is `Optimization.formCriticality`, and $m$ is
`Optimization.regularizedModel (ftaylorSeries ℝ f x) p σ`. -/
theorem formCriticality_le_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {T : Set E}
    (hT : 0 ∈ T) :
    formCriticality (iteratedFDeriv ℝ j f (x + s)) T ≤
      formCriticality (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) T +
        (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
  formCriticality_le_add_of_abs_sub_le _ _ ⟨0, zero_mem_closedBall_inter hT⟩ fun _ hd =>
    abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf hL hL0 hx hxs hσ hj hd.1

/-- **Equations (6.2.18)–(6.2.19)** of [cartis2022evaluation], Lemma 6.2.1. Under the hypotheses of
`Optimization.abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall`, let $T$ be a set of
displacements and $a, b \in \mathbb{R}$ with
$$\frac{L + \sigma}{(p-j+1)!} \|s\|^{p-j+1} + a \le b.$$
Then every $d \in T$ with $\|d\| \le 1$ and $|\nabla^j f(x+s)[d]^j| \le a$ satisfies
$|\nabla^j m(s)[d]^j| \le b$.

The sets are `Optimization.restrictedSteps`: the conclusion is `closedBall 0 1 ∩ restrictedSteps
(∇^j f(x+s)) a T ⊆ restrictedSteps (∇^j m(s)) b T`. -/
theorem inter_closedBall_restrictedSteps_subset_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {T : Set E} {a b : ℝ}
    (hab : (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) + a ≤ b) :
    closedBall 0 1 ∩ restrictedSteps (iteratedFDeriv ℝ j f (x + s)) a T ⊆
      restrictedSteps (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) b T :=
  inter_closedBall_restrictedSteps_subset _ (fun _ hd =>
    abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf hL hL0 hx hxs hσ hj hd.1)
    hab

end Estimates

section Step

/-- **The step conditions of ARp1-CC**, Step 2 of Algorithm 6.2.2 of [cartis2022evaluation]. Let
$C \subseteq E$, $x \in E$, $\sigma \in \mathbb{R}$, $\theta \in \mathbb{R}$, and let $m(s) =
T_{f,p}(x, s) + \sigma \|s\|^{p+1} / (p+1)!$. A step $s$ satisfies the conditions if

* the trial point is feasible: $x + s \in C$;
* the model decreases: $m(s) < m(0)$;
* the first-order measure of the model over $\mathcal{M}^0(s) = \mathcal{C}(x + s)$ is small
  (6.2.29): $\omega(\nabla m(s), \mathcal{C}(x + s)) \le \theta \|s\|^p$.

For $C = E$ the last condition is the condition (4.1.11) $\|\nabla m(s)\| \le \theta \|s\|^p$ of
ARp; see `Optimization.isFirstOrderCCStep_univ_iff`. The measure is
`Optimization.formCriticality` applied to `iteratedFDeriv ℝ 1 m s`, and $\mathcal{C}(y)$ is
`Optimization.feasibleSteps C y`. -/
structure IsFirstOrderCCStep (f : E → ℝ) (C : Set E) (p : ℕ) (θ : ℝ) (x : E) (σ : ℝ) (s : E) :
    Prop where
  /-- The trial point $x + s$ lies in $C$. -/
  mem : x + s ∈ C
  /-- The step decreases the model: $m(s) < m(0)$. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- Condition (6.2.29): the first-order measure of the model at $s$ over $\mathcal{C}(x + s)$ is
  at most $\theta \|s\|^p$. -/
  measure : formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (feasibleSteps C (x + s)) ≤ θ * ‖s‖ ^ p

variable {f : E → ℝ} {C : Set E} {p : ℕ} {θ σ L : ℝ} {x s : E}

/-- For $C = E$, a step $s$ satisfies the ARp1-CC conditions if and only if it satisfies the
first-order ARp conditions (4.1.10)–(4.1.11) of [cartis2022evaluation]:
$$m(s) < m(0) \quad \text{and} \quad \|\nabla m(s)\| \le \theta \|s\|^p,$$
where $m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1} / (p+1)!$.

The derivative $\nabla m(s)$ is `fderiv ℝ m s`, and the norm is its operator norm. -/
theorem isFirstOrderCCStep_univ_iff :
    IsFirstOrderCCStep f univ p θ x σ s ↔
      regularizedModel (ftaylorSeries ℝ f x) p σ s <
          regularizedModel (ftaylorSeries ℝ f x) p σ 0 ∧
        ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤ θ * ‖s‖ ^ p := by
  have hU : feasibleSteps (univ : Set E) (x + s) = univ := by ext; simp
  constructor
  · rintro ⟨-, h1, h2⟩
    rw [hU, formCriticality_iteratedFDeriv_one_univ] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_univ _, h1, ?_⟩
    rwa [hU, formCriticality_iteratedFDeriv_one_univ]

/-- Let $s$ satisfy the ARp step conditions `Optimization.IsARpStep` at $x$ with weight $\sigma$,
for constants $P$ and any order $q$. Then $s$ satisfies the ARp1-CC conditions for $C = E$ and
$\theta = \theta_1$, the first-order constant of $P$. -/
theorem IsARpStep.isFirstOrderCCStep {P : ARpParams} {q : ℕ}
    (h : IsARpStep f p P q x σ s) : IsFirstOrderCCStep f univ p P.θ₁ x σ s :=
  isFirstOrderCCStep_univ_iff.2 ⟨h.decrease, h.gradient⟩

/-- **Step-length bound for ARp1-CC**, from the proof of Lemma 6.2.4 of [cartis2022evaluation]. Let
$C$ be convex, let $f$ be $C^p$ at every point of $C$ with $\nabla^p f$ Lipschitz continuous on
$C$ with constant $L \ge 0$, and let $x \in C$, $\sigma \ge 0$ and $p \ge 1$. If $s$ satisfies
the ARp1-CC conditions with constant $\theta$, then
$$\omega_{f,\mathcal{C},1}(x + s) \le \frac{L + \sigma + \theta \, p!}{p!} \|s\|^p.$$
Equivalently, $\|s\|^p \ge p! \, \omega_{f,\mathcal{C},1}(x+s) / (L + \sigma + \theta \, p!)$
when the denominator is positive.

Here $\omega_{f,\mathcal{C},1}(y)$ is `Optimization.formCriticality (iteratedFDeriv ℝ 1 f y)
(Optimization.feasibleSteps C y)`. The measures of $f$ and of the model use the same set of
displacements, because $\mathcal{M}^0(s) = \mathcal{C}(x + s)$. -/
theorem IsFirstOrderCCStep.measure_le_mul_pow (h : IsFirstOrderCCStep f C p θ x σ s)
    (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L) (hx : x ∈ C) (hσ : 0 ≤ σ) (hp : 1 ≤ p) :
    formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s)) ≤
      (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p := by
  have h1 := formCriticality_le_regularizedModel hC hf hL hL0 hx h.mem hσ hp
    (zero_mem_feasibleSteps.2 (by simpa using h.mem))
  rw [Nat.sub_add_cancel hp] at h1
  have h2 := h.measure
  have : (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p = (L + σ) / (p ! : ℝ) * ‖s‖ ^ p + θ * ‖s‖ ^ p := by
    field_simp
  rw [this]
  linarith

/-- **Lemma 6.2.4** of [cartis2022evaluation]; for $C = E$ it is the first part (4.1.31) of Lemma
4.1.4. Let $C$ be convex, let $f$ be $C^p$ at every point of $C$ with $\nabla^p f$ Lipschitz
continuous on $C$ with constant $L \ge 0$, and let $x \in C$, $p \ge 1$ and $\theta \ge 0$. Let
$0 \le \sigma_{\min} \le \sigma \le \sigma_{\max}$ and $\eta_1 > 0$. Let $s$ satisfy the ARp1-CC
conditions with constant $\theta$, and let the iteration be successful:
$$\eta_1 \le \rho = \frac{f(x) - f(x+s)}{T_{f,p}(x, 0) - T_{f,p}(x, s)}.$$
Then
$$f(x) - f(x + s) \ge \kappa_1 \, \omega_{f,\mathcal{C},1}(x + s)^{(p+1)/p}, \qquad \kappa_1 =
  \frac{\eta_1 \sigma_{\min}}{(p+1)!} \Bigl(\frac{p!}{L + \sigma_{\max} + \theta \,
  p!}\Bigr)^{(p+1)/p},$$
which is the constant (4.1.32).

The ratio is `Optimization.reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s)`.
The powers with exponent $(p+1)/p$ are real powers `Real.rpow`. -/
theorem IsFirstOrderCCStep.sub_ge (h : IsFirstOrderCCStep f C p θ x σ s) (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hp : 1 ≤ p) (hθ : 0 ≤ θ) {σmin σmax η₁ : ℝ} (hσmin : 0 ≤ σmin)
    (hσ1 : σmin ≤ σ) (hσ2 : σ ≤ σmax) (hη : 0 < η₁)
    (hρ : η₁ ≤ reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s)) :
    η₁ * σmin / ((p + 1)! : ℝ) * ((p ! : ℝ) / (L + σmax + θ * p !)) ^ (((p : ℝ) + 1) / p) *
        formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s)) ^
          (((p : ℝ) + 1) / p) ≤ f x - f (x + s) := by
  set ω := formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s))
  have hσ : 0 ≤ σ := hσmin.trans hσ1
  have hω : 0 ≤ ω := formCriticality_nonneg _ le_rfl (zero_mem_feasibleSteps.2 (by
    simpa using h.mem))
  -- the decrease (4.1.37)
  have hpred := lt_taylorDecrement_of_regularizedModel_lt h.decrease
  have hpred0 : 0 < (ftaylorSeries ℝ f x).taylorDecrement p s :=
    lt_of_le_of_lt (by positivity) hpred
  have hdec := sub_le_of_le_reductionRatio hpred0 hρ
  set c := η₁ * σmin / ((p + 1)! : ℝ)
  have hc : 0 ≤ c := by positivity
  have h37 : c * ‖s‖ ^ (p + 1) ≤ f x - f (x + s) := by
    refine le_trans ?_ hdec
    calc c * ‖s‖ ^ (p + 1) = η₁ * (σmin / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) := by ring
      _ ≤ η₁ * (σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hpred.le hη.le
  -- the step-length bound
  set K := L + σmax + θ * (p ! : ℝ)
  have hK : 0 ≤ K := by have := hσ.trans hσ2; positivity
  have hstep : (p ! : ℝ) / K * ω ≤ ‖s‖ ^ p := by
    rcases hK.lt_or_eq with hK | hK
    · have h1 := h.measure_le_mul_pow hC hf hL hL0 hx hσ hp
      have h2 : (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p ≤ K / (p ! : ℝ) * ‖s‖ ^ p := by
        gcongr
        simp only [K]
        linarith
      have h3 := h1.trans h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h3
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      linarith
    · rw [← hK, div_zero, zero_mul]; positivity
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hn, mul_assoc, ← Real.mul_rpow (by positivity) hω]
  exact (mul_le_mul_of_nonneg_left (Real.rpow_div_le_pow_of_le_pow (by positivity) (norm_nonneg _)
    (by omega) hstep) hc).trans h37

end Step

section Existence

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ}

/-- **Model minimizers over a closed set**, §6.2.1 of [cartis2022evaluation]. Let $E$ be
finite-dimensional, let $D$ be any derivative data, $p \in \mathbb{N}$ and $\sigma > 0$, and let
$S \subseteq E$ be closed with $0 \in S$. Then the model
$m(s) = T_p(s) + \sigma \|s\|^{p+1} / (p+1)!$ attains its minimum on $S$.

The model is `Optimization.regularizedModel D p σ`, with $T_p$ = `D.taylorSum p`. It is coercive
because the regularization term dominates the polynomial $T_p$. -/
theorem exists_isMinOn_regularizedModel_of_isClosed [FiniteDimensional ℝ E] {S : Set E}
    (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hσ : 0 < σ) :
    ∃ s ∈ S, IsMinOn (regularizedModel D p σ) S s := by
  have := FiniteDimensional.proper_real E
  have htend : Filter.Tendsto (regularizedModel D p σ) (Filter.cocompact E) Filter.atTop := by
    rw [regularizedModel_eq_powRegularizedModel]
    exact tendsto_powRegularizedModel_cocompact hσ (by linarith)
  exact (continuous_regularizedModel D p σ).continuousOn.exists_isMinOn' hS h0
    ((htend.eventually (Filter.eventually_ge_atTop _)).filter_mono inf_le_left)

variable {f : E → ℝ} {C : Set E} {θ : ℝ} {x : E}

/-- **Existence of ARp1-CC steps**, Algorithms 6.2.1–6.2.2 of [cartis2022evaluation]. Let $E$ be
finite-dimensional, $C \subseteq E$ closed and convex, $x \in C$, and let $f$ be $C^p$ at $x$
with $p \ge 1$. Let $\sigma > 0$ and $\theta \ge 0$, and let $x$ not be first-order critical:
$\omega_{f,\mathcal{C},1}(x) > 0$. Then there is a step $s$ such that

* $s$ minimizes the model $m(s) = T_{f,p}(x, s) + \sigma \|s\|^{p+1} / (p+1)!$ over the feasible
  steps $\mathcal{C}(x)$;
* $s$ satisfies the ARp1-CC conditions with constant $\theta$;
* the first-order measure of the model at $s$ vanishes:
  $\omega(\nabla m(s), \mathcal{C}(x + s)) = 0$.

The last property means that $s$ also satisfies the condition (6.2.10) of the first-order ARp-CC
Step 2, so Step 2 of both methods is well defined. -/
theorem exists_isFirstOrderCCStep [FiniteDimensional ℝ E] (hCc : IsClosed C) (hC : Convex ℝ C)
    (hx : x ∈ C) (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) (hσ : 0 < σ) (hθ : 0 ≤ θ)
    (hcrit : 0 < formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x)) :
    ∃ s, IsMinOn (regularizedModel (ftaylorSeries ℝ f x) p σ) (feasibleSteps C x) s ∧
      IsFirstOrderCCStep f C p θ x σ s ∧
      formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
        (feasibleSteps C (x + s)) = 0 := by
  set m := regularizedModel (ftaylorSeries ℝ f x) p σ
  set S := feasibleSteps C x
  have hS0 : (0 : E) ∈ S := zero_mem_feasibleSteps.2 hx
  have hSc : Convex ℝ S := convex_feasibleSteps hC x
  have hdiff : Differentiable ℝ m :=
    (contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := p) (σ := σ)).differentiable
      (by norm_cast; omega)
  obtain ⟨s, hs, hmin⟩ := exists_isMinOn_regularizedModel_of_isClosed
    (D := ftaylorSeries ℝ f x) (isClosed_feasibleSteps hCc x) hS0 hσ
  have hSS : ∀ t, feasibleSteps S t = feasibleSteps C (x + t) := fun t => by
    ext d; simp [S, add_assoc]
  have hzero : formCriticality (iteratedFDeriv ℝ 1 m s) (feasibleSteps C (x + s)) = 0 := by
    rw [← hSS]
    exact formCriticality_eq_zero_of_isLocalMinOn hSc hs hmin.isLocalMinOn
      (hdiff s)
  have hdec : m s < m 0 := by
    refine lt_of_le_of_ne (hmin hS0) fun heq => hcrit.ne' ?_
    have hmin0 : IsMinOn m S 0 := fun y hy => by rw [← heq]; exact hmin hy
    have h0 := formCriticality_eq_zero_of_isLocalMinOn hSc hS0 hmin0.isLocalMinOn
      (hdiff 0)
    rw [formCriticality_fderiv_eq_zero_iff hSc hS0,
      fderiv_regularizedModel_ftaylorSeries_zero hf hp] at h0
    rw [formCriticality_fderiv_eq_zero_iff hC hx]
    intro y hy
    have := h0 (y - x) (by simpa [S] using hy)
    simpa using this
  refine ⟨s, hmin, ⟨by simpa [S] using hs, hdec, ?_⟩, hzero⟩
  rw [hzero]
  positivity

end Existence

end Optimization
