/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.ARqpC
import Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity
import Numlib.Optimization.ModelBased.RatioTest

/-!
# Evaluation complexity of ARqpC

This file proves the evaluation complexity of the adaptive-regularization method ARqpC for composite
problems of [cartis2022evaluation], §14.1, Algorithm 14.1.1. The problem is to minimize
$w = f + h \circ c$ on a feasible set $X$, where $f : E \to \mathbb{R}$ and $c : E \to F$ are smooth
and $h : F \to \mathbb{R}$ is Lipschitz and possibly nonsmooth. The case $X = E$ is ARqpC, and a
closed $X$ is ARqpC-SC of §14.2. The model of iteration $k$ keeps $h$ exactly: $$\hat m_k(s) =
T_{f,p}(x_k, s) + h(T_{c,p}(x_k, s)) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1},$$ and the predicted
decrease is $\Delta T_{w,p}(x_k, s) = w(x_k) - T_{f,p}(x_k, s) - h(T_{c,p}(x_k, s))$. The run is the
generic ARqp run `Optimization.IsARqpRun` for the objective $w$ with the composite model data
`Optimization.arqpcData`. For $h = 0$ these are the data of exact ARqp
(`Optimization.ARqpData.ofComposite_zero_fun`). The main result, Theorem 14.1.10 of the source, is
that a run terminates at an $(\varepsilon, \delta)$-approximate $q$-th order minimizer after
$O(\max_j \varepsilon_j^{-(j+1)})$ evaluations, and after $O(\varepsilon_1^{-(p+1)/p})$ evaluations
when $q = 1$ and $h$ and $X$ are convex.

The smoothness hypotheses are those of `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity`.
Let $C \supseteq X$ be open and convex, and let $\nabla^p f$ and $\nabla^p c$ be $L_{f,p}$- and
$L_{c,p}$-Lipschitz anchored at the points of a set $A$ with respect to $C$
(`LipschitzDerivsAnchored f C A p p Lf` and `LipschitzDerivsAnchored c C A p p Lc`). The set $A$
contains the sublevel set $\{y \in X : w(y) \le w(x_0)\}$, which contains every iterate
(`Optimization.IsARqpRun.mem_compositeSublevel`). The constants enter through a number
$L_w \ge L_{f,p} + L_h L_{c,p}$, the Lipschitz constant (14.1.27) of the remainder of the composite
model, where $L_h$ is a Lipschitz constant of $h$. The radii of the detailed Step 2 also use a
number $K_w \ge K_f + L_h K_c$, where $K_f$ and $K_c$ bound the jets $\|\nabla^i f\|$ and
$\|\nabla^i c\|$, $i \in [2, p]$, at the points of $A$; this is the constant $L_w$ of (14.1.3) of
the source. With $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_w / (1 - \eta_2))$ the radius constant
is $\kappa_{\delta, \min} = \kappa_\delta(\sigma_{\max}) = \varsigma \theta / (8 (3 K_w +
\sigma_{\max}))$, as in (14.1.29); it is the same function `Optimization.arqpKappaDelta` as for
ARqp.

## Main definitions

* `Optimization.arqpcStepBoundUnit`, `Optimization.arqpcStepBound`: the lower bounds on the step
  length in the two cases of (14.1.31).
* `Optimization.arqpcKappaDmUnit`, `Optimization.arqpcKappaDm`: the decrease constants
  $\kappa_{\Delta m}$ of Lemma 14.1.9 in the two cases.

## Main results

* `Optimization.IsARqpRun.compositeTaylorDecrement_ge`: the model decrease is at least
  $\sigma_k \|s_k\|^{p+1} / (p+1)!$ (Lemma 14.1.5).
* `Optimization.IsARqpRun.mem_compositeSublevel`: the iterates stay in
  $\{y \in X : w(y) \le w(x_0)\}$.
* `Optimization.IsARqpRun.sigma_le_of_compositeAnchored`: the weights stay below $\sigma_{\max}$
  (Lemma 14.1.6).
* `Optimization.IsARqpRun.exists_composite_radius_ineq`: the inequality (14.1.30) after a successful
  iteration (Lemma 14.1.7).
* `Optimization.IsARqpRun.composite_norm_step_ge`: the lower bounds (14.1.31) on the step length
  (Lemma 14.1.8).
* `Optimization.IsARqpRun.composite_decrease_unit`, `Optimization.IsARqpRun.composite_decrease`: a
  successful iteration decreases the model and $w$ (Lemma 14.1.9).
* `Optimization.IsARqpRun.arqpKappaDelta_mul_le_radius_composite`: every output of the detailed Step
  2 satisfies the radius policy (14.1.28) (Lemma 14.1.3).
* `Optimization.IsARqpRun.exists_isEpsDeltaApproxComposite_of_stop₂`: a termination in Step 2 gives
  an approximate minimizer (Lemma 14.1.4(ii)).
* `Optimization.IsARqpRun.compositeModel_lt_of_convex`: for $q = 1$ and convex $h$ and $X$ there is
  no termination in Step 2 (Lemma 14.1.4(i)).
* `Optimization.IsARqpRun.complexity_composite`, `Optimization.IsARqpRun.complexity_composite_unit`:
  the evaluation complexity, parts 2 and 1 of Theorem 14.1.10.
* `Optimization.IsARqpCRun.arqpKappaDelta_mul_le_radius`, `Optimization.IsARqpCRun.complexity`,
  `Optimization.IsARqpCRun.complexity_unit`: the radius policy and Theorem 14.1.10 for every ARqpC
  run (`Optimization.IsARqpCRun`).

## Proof outline

Both analyses rest on the model lemma
`Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge` (Lemma 12.2.8 is its case $h = 0$),
the radius inequalities of `Numlib.Optimization.ModelBased.HighOrderModel`, the step-length lemmas
`Optimization.norm_step_ge_of_measure_ineq` and `Optimization.pow_ge_of_measure_ineq`, the radius
constant `Optimization.arqpKappaDelta`, and the existence of runs
`Optimization.exists_isARqpRun_of_forall`. The analysis of this file uses the lower bound on the
radii at every order and the step bounds (14.1.31), which give decreases of order
$\varepsilon_j^{j+1}$ (Lemma 14.1.9). For $h = 0$ and $c = 0$ the run is an exact ARqp run, and the
analysis of `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` also applies; it distinguishes
two radii modes with the exponents `Optimization.arqpPiOf`.

## Implementation notes

* The notions "iteration $k$ is reached", "does not terminate", "successful" and the evaluation
  counts are those of `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity`, for the termination
  test `Optimization.arqpcStop` and the ratio of $w$.
* The counts `Optimization.funEvalCount` and `Optimization.derivEvalCount` count the evaluations of
  $w$, that is, of $f$ and $c$ together, and of their derivatives.
-/

open Set Metric Filter
open scoped Nat

namespace Optimization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {p q : ℕ}

/-- The predicted decrease of the composite model at $x$ along $t$ is $\Delta T_{w,p}(x, t) =
(f(x) + h(c(x))) - (T_{f,p}(x, t) + h(T_{c,p}(x, t)))$. -/
theorem compositeTaylorDecrement_ftaylorSeries_eq_sub (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (y t : E) :
    compositeTaylorDecrement (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h p t =
      (f y + h (c y)) - (taylorPolynomial f p y t + h ((ftaylorSeries ℝ c y).taylorSum p t)) := by
  rw [compositeTaylorDecrement, ← taylorPolynomial_eq_taylorSum f,
    ← taylorPolynomial_eq_taylorSum c, taylorPolynomial_zero_right, taylorPolynomial_zero_right]

/-! ### Constants -/

section Constants

variable (P : ARqpParams) (Lw Kw : ℝ) (p q : ℕ)

/-- The lower bound on the step length in the unit-radius case of (14.1.31) of
[cartis2022evaluation]: $$\left(\frac{\varsigma - \theta}{j! \, (L_w + \sigma_{\max})} \cdot
\frac{\varepsilon_j}{3}\right)^{1/(p-j+1)},$$ where $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_w
/ (1 - \eta_2))$. -/
noncomputable def arqpcStepBoundUnit (j : ℕ) (εj : ℝ) : ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) * εj / 3) ^
    (1 / ((p : ℝ) - j + 1))

/-- The lower bound on the step length in the case of (14.1.31) of [cartis2022evaluation] where the
radii satisfy the lower bound (14.1.28): $$\left(\frac{(\varsigma - \theta) \kappa^j}{3 \, j! \,
(L_w + \sigma_{\max})}\right)^{1/(p-j+1)} \varepsilon_j^{(j+1)/(p+1)},$$ where $\sigma_{\max} =
\max(\sigma_0, \gamma_3 L_w / (1 - \eta_2))$ and $\kappa = \kappa_\delta(\sigma_{\max})$ is
computed with $K_w$. -/
noncomputable def arqpcStepBound (j : ℕ) (εj : ℝ) : ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
      arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ j / 3) ^ (1 / ((p : ℝ) - j + 1)) *
    εj ^ (((j : ℝ) + 1) / ((p : ℝ) + 1))

/-- The decrease constant $\kappa_{\Delta m}$ of Lemma 14.1.9 of [cartis2022evaluation] in the
unit-radius case: $$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{\varsigma -
\theta}{3 (L_w + \sigma_{\max})}\right)^{(p+1)/p}.$$
-/
noncomputable def arqpcKappaDmUnit : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) / (Lw + arSigmaMax P.toARParams Lw) / 3) ^
    (((p : ℝ) + 1) / p)

/-- The decrease constant $\kappa_{\Delta m}$ of Lemma 14.1.9 of [cartis2022evaluation] in the case
where the radii satisfy the lower bound (14.1.28): $$\kappa_{\Delta m} =
\frac{\sigma_{\min}}{(p+1)!} \left(\frac{(\varsigma - \theta) \kappa^q}{3 \, q! \, (L_w +
\sigma_{\max})}\right)^{(p+1)/(p-q+1)},$$ where $\kappa = \kappa_\delta(\sigma_{\max})$ is
computed with $K_w$. -/
noncomputable def arqpcKappaDm : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) / ((q ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
    arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ q / 3) ^
      (((p : ℝ) + 1) / ((p : ℝ) - q + 1))

variable {P Lw Kw p q}

/-- The defining formula of `Optimization.arqpcKappaDm`: $\kappa_{\Delta m} = \sigma_{\min} / (p+1)!
\cdot ((\varsigma - \theta) \kappa^q / (3 \, q! \, (L_w + \sigma_{\max})))^{(p+1)/(p-q+1)}$. -/
theorem arqpcKappaDm_def : arqpcKappaDm P Lw Kw p q =
    P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) / ((q ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
      arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ q / 3) ^
        (((p : ℝ) + 1) / ((p : ℝ) - q + 1)) := rfl

/-- The sizes of the constants of Lemmas 14.1.8–14.1.9 and Theorem 14.1.10 of
[cartis2022evaluation]. Let $p \ge 1$, $\theta < \varsigma$, $L_{f,p} + L_h L_{c,p} \le L_w$,
$L_{f,p} \ge 1$, $L_{c,p} \ge 0$, $L_h \ge 0$ and $K_w \ge 1$, and let $j \in \mathbb{N}$. With
$A = L_w + \sigma_{\max}$, $B = 2 L_h L_{c,p} / (p+1)!$ and
$\kappa = \kappa_\delta(\sigma_{\max})$ computed with $K_w$, $$0 < \varsigma - \theta \le j! \,
A, \quad A > 0, \quad 0 \le B \le A, \quad 0 < \kappa \le 1.$$
-/
theorem arqpc_consts (hp : 1 ≤ p) (hθς : P.θ < P.ς) {Lfp Lcp Lh : ℝ} (hLw : Lfp + Lh * Lcp ≤ Lw)
    (hLf : 1 ≤ Lfp) (hLc : 0 ≤ Lcp) (hLh : 0 ≤ Lh) (hKw : 1 ≤ Kw) (j : ℕ) :
    0 < P.ς - P.θ ∧ P.ς - P.θ ≤ (j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw) ∧
    0 < Lw + arSigmaMax P.toARParams Lw ∧ 0 ≤ 2 * Lh * Lcp / ((p + 1)! : ℝ) ∧
    2 * Lh * Lcp / ((p + 1)! : ℝ) ≤ Lw + arSigmaMax P.toARParams Lw ∧
    0 < arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ∧
    arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ≤ 1 := by
  have hσ := arSigmaMax_pos P.toARParams Lw
  have hB0 : 0 ≤ Lh * Lcp := mul_nonneg hLh hLc
  have hLw1 : 1 ≤ Lw := by linarith
  have hfac2 : (2 : ℝ) ≤ ((p + 1)! : ℝ) := by
    have : 2 ≤ (p + 1)! := by
      calc 2 = (1 + 1)! := rfl
        _ ≤ (p + 1)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have hjf : (1 : ℝ) ≤ (j ! : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
  have hς1 := P.ς_le_one
  have hθ := P.θ_pos
  refine ⟨by linarith, ?_, by positivity, by positivity, ?_,
    arqpKappaDelta_pos P (by linarith) hσ, (arqpKappaDelta_lt_one P hKw hσ.le).le⟩
  · calc P.ς - P.θ ≤ 1 * (Lw + arSigmaMax P.toARParams Lw) := by linarith
      _ ≤ _ := by gcongr
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- For $b \ge 0$, $(b^{1/e})^{p+1} = b^{(p+1)/e}$. -/
private theorem rpow_one_div_pow_succ {b e : ℝ} (hb : 0 ≤ b) (p : ℕ) :
    (b ^ (1 / e)) ^ (p + 1) = b ^ (((p : ℝ) + 1) / e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  push_cast
  ring

end Constants

variable {f : E → ℝ} {c : E → F} {h : F → ℝ} {P : ARqpParams} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E}
  {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {X C A : Set E} {Lf Lc : ℕ → ℝ}
  {Lh Lw Kw : ℝ}

namespace IsARqpRun

/-! ### Decrease and sublevel set -/

/-- **Lemma 14.1.5** of [cartis2022evaluation] (Taylor decrease for ARqpC). Consider an ARqp run on
$X$ for $w = f + h \circ c$ with the composite model data, and an iteration $k$ that is reached
and at which the Step-1 test fails. Then $$\Delta T_{w,p}(x_k, s_k) \ge \frac{\sigma_k}{(p+1)!}
\|s_k\|^{p+1}, \qquad (14.1.25)$$ and $\Delta T_{w,p}(x_k, s_k) > 0$ unless the Step-2 test
$\hat m_k(s_k) = \hat m_k(0)$ holds. -/
theorem compositeTaylorDecrement_ge
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (s k) ∧
    (¬ arqpStop₂ (arqpcData f c h p x σ) s k →
      0 < compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p
        (s k)) := by
  have hstep := hr.step hk h1
  refine ⟨le_compositeTaylorDecrement_of_compositeRegularizedModel_le hstep.model_le,
    fun h2 => ?_⟩
  have hlt := lt_compositeTaylorDecrement_of_compositeRegularizedModel_lt
    (lt_of_le_of_ne hstep.model_le h2)
  have hσ := hr.toIsARRun.sigma_pos hk k le_rfl
  exact lt_of_le_of_lt (by positivity) hlt

/-- The objective $w = f + h \circ c$ does not increase along an ARqp run with the composite model
data: if iteration $k$ is reached and does not terminate, then $w(x_{k+1}) \le w(x_k)$. -/
theorem composite_objective_succ_le
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i) :
    f (x (k + 1)) + h (c (x (k + 1))) ≤ f (x k) + h (c (x k)) := by
  by_cases hs : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k
  · have hk' : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i := fun i hi => hk i hi.le
    have hpos := (hr.compositeTaylorDecrement_ge hk' (fun h' => hk k le_rfl (Or.inl h'))).2
      (fun h' => hk k le_rfl (Or.inr h'))
    have := (hr.toIsARRun.sub_ge_of_succ (w := fun y => f y + h (c y))
      (pred := fun k => compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) hk rfl hpos hs).2
    have := mul_pos P.η₁_pos hpos
    linarith
  · rw [hr.toIsARRun.eq_of_not_succ hk (not_le.1 hs)]

/-- The iterates of an ARqp run on $X$ with the composite model data stay in the sublevel set: every
iteration $k$ that is reached satisfies $x_k \in X$ and $w(x_k) \le w(x_0)$.

This includes the termination index. -/
theorem mem_compositeSublevel
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) :
    x k ∈ X ∧ f (x k) + h (c (x k)) ≤ f (x 0) + h (c (x 0)) := by
  refine ⟨hr.mem k hk, ?_⟩
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    exact (hr.composite_objective_succ_le fun i hi => hk i (Nat.lt_succ_of_le hi)).trans
      (ih fun i hi => hk i (hi.trans k.lt_succ_self))

/-! ### Lemma 14.1.6: the regularization weights stay bounded -/

/-- **Lemma 14.1.6** of [cartis2022evaluation] (upper bound on the regularization weight of ARqpC),
anchored form. Let $X \subseteq C$, let $\nabla^p f$ and $\nabla^p c$ be $L_{f,p}$- and
$L_{c,p}$-Lipschitz anchored at the points of $A$ with respect to $C$, let $A$ contain
$\{y \in X : w(y) \le w(x_0)\}$, let $h$ have the Lipschitz constant $L_h$, and let
$L_{f,p} + L_h L_{c,p} \le L_w$. Consider an ARqp run on $X$ for $w$ with the composite model
data, and let iteration $K$ be reached. Then $$\sigma_k \le \sigma_{\max} = \max\left(\sigma_0,
\frac{\gamma_3 L_w}{1 - \eta_2}\right) \qquad (14.1.26)$$ for all $k \le K$. -/
theorem sigma_le_of_compositeAnchored (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hLw : Lf p + Lh * Lc p ≤ Lw) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {K : ℕ} (hK : ∀ i < K, ¬ arqpcStop f c h P p q ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arSigmaMax P.toARParams Lw := by
  have hη := P.one_sub_η₂_pos
  have hpp : p ∈ Finset.Icc p p := Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩
  have hforce : ∀ k, (∀ j ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d j) →
      Lw / (1 - P.η₂) ≤ σ k →
        P.η₂ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k := by
    intro k hk hσk
    have hk' : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i := fun i hi => hk i hi.le
    have h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k := fun h' => hk k le_rfl (Or.inl h')
    obtain ⟨hdec, hpos⟩ := hr.compositeTaylorDecrement_ge hk' h1
    have hpos := hpos fun h' => hk k le_rfl (Or.inr h')
    set pred := compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p
      (s k)
    obtain ⟨hxX, hxw⟩ := hr.mem_compositeSublevel hk'
    have hxA := hA _ hxX hxw
    have hxs : x k + s k ∈ X := (hr.step hk' h1).mem
    have hrem := abs_sub_compositeTaylor_le_of_lipschitzAnchored hf.convex hf.contDiffAt
      hc.contDiffAt (hf.lipschitzAt hpp hxA) (hc.lipschitzAt hpp hxA) hLh (hf.subset hxA)
      (hXC hxs)
    have hσL : Lw ≤ (1 - P.η₂) * σ k := by
      rw [div_le_iff₀ hη] at hσk; linarith
    have hfac : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
    have hR : (Lf p + Lh * Lc p) / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ (1 - P.η₂) * pred := by
      calc (Lf p + Lh * Lc p) / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)
          ≤ (1 - P.η₂) * σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by gcongr; linarith
        _ = (1 - P.η₂) * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by ring
        _ ≤ (1 - P.η₂) * pred := by gcongr
    have hval : f (x k) + h (c (x k)) - pred =
        taylorPolynomial f p (x k) (s k) + h ((ftaylorSeries ℝ c (x k)).taylorSum p (s k)) := by
      have := compositeTaylorDecrement_ftaylorSeries_eq_sub f c h p (x k) (s k)
      linarith
    have := le_reductionRatio_of_abs_sub_le (f := fun y => f y + h (c y))
      (x := x k) (s := s k) hpos (c := 1 - P.η₂) (by
        rw [hval]
        exact hrem.trans hR)
    change P.η₂ ≤ reductionRatio _ _ _ pred
    linarith
  intro k hkK
  have := (hr.toIsARRun.sigma_le_max hforce hK k hkK).2.2
  refine this.trans (le_of_eq ?_)
  rw [arSigmaMax_def, mul_div_assoc]

/-! ### Lemmas 14.1.7 and 14.1.8: the step is long -/

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC), anchored form. Let
$X \subseteq C$, let $\nabla^p f$ and $\nabla^p c$ be $L_{f,p}$- and $L_{c,p}$-Lipschitz
anchored at the points of $A$ with respect to $C$, with $L_{f,p} \ge 1$ and $L_{c,p} \ge 0$, let
$A$ contain $\{y \in X : w(y) \le w(x_0)\}$, let $h$ have the Lipschitz constant $L_h$, and let
$L_{f,p} + L_h L_{c,p} \le L_w$. Let $1 \le q \le p$, $\varepsilon \in (0, 1]^q$ and
$\delta_0 \in (0, 1]^q$. Consider an ARqp run on $X$ for $w$ with the composite model data and
initial radii $\delta_0$, and an iteration $k$ that is reached, does not terminate and is
successful, such that the Step-1 test fails at $k + 1$. Then for some $j \in [1, q]$
$$\frac{(\varsigma - \theta) \varepsilon_j \delta_{k+1,j}^j}{j!} < (L_w + \sigma_{\max})
\sum_{\ell = 1}^j \frac{\delta_{k+1,j}^\ell}{\ell!} \|s_k\|^{p - \ell + 1} + \frac{2 L_h
L_{c,p}}{(p+1)!} \|s_k\|^{p+1}.$$

This is the form (14.1.30) of the source for approximate measure evaluations with accuracy
$\varsigma$. For a short step the inequality comes from the model test (14.1.13); for a long
step it holds trivially. -/
theorem exists_composite_radius_ineq (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p) (hLw : Lf p + Lh * Lc p ≤ Lw) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hsucc : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (Lw + arSigmaMax P.toARParams Lw) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  have hk' : ∀ i < k + 1, ¬ arqpcStop f c h P p q ε x s σ δ d i :=
    fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  have hLh0 := hLh.nonneg
  have hσmax0 := arSigmaMax_pos P.toARParams Lw
  rcases lt_or_ge ‖s k‖ 1 with hshort | hlong
  · have hstep := hr.step (fun i hi => hk i hi.le) fun h' => hk k le_rfl (Or.inl h')
    have hbr := hstep.branch.resolve_left (not_le.2 hshort)
    have hrad := (hr.radii k hk).1 hsucc
    have hx1 : x (k + 1) = x k + s k := hr.toIsARRun.eq_add_of_succ hk hsucc
    obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses h1
    refine ⟨j, hj, ?_⟩
    have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
    have hw := hr.witness (k + 1) hk' j hj
    have hδ := (hr.delta_mem hδ₀ (k + 1) hk' j hj).1
    have hmem : x (k + 1) ∈ X := hr.mem (k + 1) hk'
    have hS0 : (0 : E) ∈ {e | x k + s k + e ∈ X} := by simpa [← hx1] using hmem
    have hσ0 : 0 ≤ σ k := (hr.toIsARRun.sigma_pos hk' k k.le_succ).le
    have hσmax := hr.sigma_le_of_compositeAnchored hf hc hLh hLw hXC hA hk' k k.le_succ
    -- the measure at `x_{k+1}` exceeds `ς ε δ^j/j!`
    have h₁ : P.ς * ε j * δ (k + 1) j ^ j / (j ! : ℝ) - 0 <
        compositeTaylorMeasure (ftaylorSeries ℝ f (x k + s k))
          (ftaylorSeries ℝ c (x k + s k)) h j (δ (k + 1) j) {e | x k + s k + e ∈ X} := by
      rw [sub_zero]
      have hdm : compositeTaylorDecrement (ftaylorSeries ℝ f (x (k + 1)))
          (ftaylorSeries ℝ c (x (k + 1))) h j (d (k + 1) j) ≤
          compositeTaylorMeasure (ftaylorSeries ℝ f (x (k + 1)))
            (ftaylorSeries ℝ c (x (k + 1))) h j (δ (k + 1) j) {e | x (k + 1) + e ∈ X} :=
        compositeTaylorDecrement_le_compositeTaylorMeasure hLh hw.1
      change P.ς * ε j * δ (k + 1) j ^ j / (j ! : ℝ) <
        compositeTaylorDecrement (ftaylorSeries ℝ f (x (k + 1)))
          (ftaylorSeries ℝ c (x (k + 1))) h j (d (k + 1) j) at hlt
      rw [hx1] at hdm hlt
      exact hlt.trans_le hdm
    -- the model measure at `s_k` is at most `θ ε δ^j/j!`
    have h₂ : compositeTaylorMeasure
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (ftaylorSeries ℝ ((ftaylorSeries ℝ c (x k)).taylorSum p) (s k)) h j (δ (k + 1) j)
        {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δ (k + 1) j ^ j / j ! := by
      obtain ⟨happ, hsmall⟩ := hbr j hj
      rw [hrad]
      have hm := happ.2.trans hsmall
      have : P.ς * compositeTaylorMeasure
          (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
          (ftaylorSeries ℝ ((ftaylorSeries ℝ c (x k)).taylorSum p) (s k)) h j (δs k j)
          {e | x k + s k + e ∈ X} ≤ P.ς * (P.θ * ε j * δs k j ^ j / j !) := by
        refine hm.trans (le_of_eq ?_)
        ring
      exact le_of_mul_le_mul_left this P.ς_pos
    obtain ⟨hxX, hxw⟩ := hr.mem_compositeSublevel fun i hi => hk i hi.le
    have hxA := hA _ hxX hxw
    have hpp : p ∈ Finset.Icc p p := Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩
    have := radius_inequality_of_compositeTaylorMeasure_gt_anchored hf.convex hf.contDiffAt
      hc.contDiffAt (hf.lipschitzAt hpp hxA) (hc.lipschitzAt hpp hxA) hLh (by linarith) hLc
      (hf.subset hxA) (hXC (hx1 ▸ hmem)) hσ0 hσmax hjp hS0 hδ.le h₁ h₂
    have hsum : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) := by
      have := hδ.le
      positivity
    have hmono : (Lf p + Lh * Lc p + arSigmaMax P.toARParams Lw) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) ≤
        (Lw + arSigmaMax P.toARParams Lw) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) := by
      gcongr
    rw [add_zero] at this
    linarith
  · have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    refine ⟨1, hj1, ?_⟩
    have hδ := (hr.delta_mem hδ₀ (k + 1) hk' 1 hj1).1
    have hε1 := hε 1 hj1
    have hA1 : 1 ≤ Lw + arSigmaMax P.toARParams Lw := by nlinarith
    have hB : 0 ≤ 2 * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by positivity
    have hsp : 1 ≤ ‖s k‖ ^ (p - 1 + 1) := one_le_pow₀ hlong
    have hlhs : (P.ς - P.θ) * ε 1 < 1 := by
      have := P.ς_le_one; have := P.θ_pos
      nlinarith [hε1.1, hε1.2]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, Nat.factorial_one, Nat.cast_one,
      div_one]
    nlinarith [mul_le_mul_of_nonneg_left hsp hδ.le]

/-- **Lemma 14.1.8** of [cartis2022evaluation] (lower bound on the step of ARqpC). Assume the
hypotheses of `Optimization.IsARqpRun.exists_composite_radius_ineq`, and also
$\theta < \varsigma$ and $K_w \ge 1$. Let $A = L_w + \sigma_{\max}$ and let $\kappa_{\delta,
\min} = \kappa_\delta(\sigma_{\max})$ be computed with $K_w$. Then there is $j \in [1, q]$ such
that

* if $\delta_{k+1,j} = 1$, then $\|s_k\| \ge ((\varsigma - \theta) / (j! \, A) \cdot
  \varepsilon_j / 3)^{1/(p-j+1)}$, the first case of (14.1.31);
* if $\delta_{k+1,j} \ge \kappa_{\delta, \min} \varepsilon_j$, then $\|s_k\| \ge ((\varsigma -
  \theta) \kappa_{\delta, \min}^j / (3 \, j! \, A))^{1/(p-j+1)} \varepsilon_j^{(j+1)/(p+1)}$,
  the second case of (14.1.31).

The bounds are `Optimization.arqpcStepBoundUnit` and `Optimization.arqpcStepBound`. A long step
($\|s_k\| \ge 1$) satisfies both bounds. -/
theorem composite_norm_step_ge (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p) (hLw : Lf p + Lh * Lc p ≤ Lw) (hKw : 1 ≤ Kw)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hsucc : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q,
      (δ (k + 1) j = 1 → arqpcStepBoundUnit P Lw p j (ε j) ≤ ‖s k‖) ∧
      (arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) * ε j ≤ δ (k + 1) j →
        arqpcStepBound P Lw Kw p j (ε j) ≤ ‖s k‖) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hk' : ∀ i < k + 1, ¬ arqpcStop f c h P p q ε x s σ δ d i :=
    fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  have hLh0 := hLh.nonneg
  -- both bounds are at most `1`
  have hsmall : ∀ j ∈ Finset.Icc 1 q, arqpcStepBoundUnit P Lw p j (ε j) ≤ 1 ∧
      arqpcStepBound P Lw Kw p j (ε j) ≤ 1 := by
    intro j hj
    obtain ⟨ha, haA, hA, -, -, hκ, hκ1⟩ := arqpc_consts hp hθς hLw hLf hLc hLh0 hKw j
    have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
    have hεj := hε j hj
    have hα : 0 ≤ (P.ς - P.θ) / ((j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) := by
      positivity
    have hα1 : (P.ς - P.θ) / ((j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact haA
    have he : 0 ≤ 1 / ((p : ℝ) - j + 1) := by
      have : (j : ℝ) ≤ p := by exact_mod_cast hjp
      exact div_nonneg zero_le_one (by linarith)
    refine ⟨Real.rpow_le_one (by have := hεj.1.le; positivity)
      (by nlinarith [hεj.2, hεj.1]) he, ?_⟩
    have hb1 : ((P.ς - P.θ) / ((j ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
        arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ j / 3) ^
          (1 / ((p : ℝ) - j + 1)) ≤ 1 := by
      have : arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ j ≤ 1 := pow_le_one₀ hκ.le hκ1
      exact Real.rpow_le_one (by positivity) (by nlinarith [pow_nonneg hκ.le j]) he
    have hb2 : ε j ^ (((j : ℝ) + 1) / ((p : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one hεj.1.le hεj.2 (by positivity)
    unfold arqpcStepBound
    calc _ ≤ 1 * 1 := mul_le_mul hb1 hb2 (Real.rpow_nonneg hεj.1.le _) zero_le_one
      _ = 1 := one_mul 1
  rcases le_or_gt 1 ‖s k‖ with hlong | hshort
  · have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    exact ⟨1, hj1, fun _ => (hsmall 1 hj1).1.trans hlong,
      fun _ => (hsmall 1 hj1).2.trans hlong⟩
  · obtain ⟨j, hj, hlt⟩ := hr.exists_composite_radius_ineq hf hc hLh hLf hLc hLw hXC hA hq hqp hε
      hδ₀ hk hsucc h1
    refine ⟨j, hj, ?_⟩
    obtain ⟨ha, haA, hA, hB, hBA, hκ, hκ1⟩ := arqpc_consts hp hθς hLw hLf hLc hLh0 hKw j
    have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
    have hεj := hε j hj
    have hδ := (hr.delta_mem hδ₀ (k + 1) hk' j hj).1
    -- the step is nonzero: the predicted decrease is positive
    have ht : 0 < ‖s k‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have hpos := (hr.compositeTaylorDecrement_ge (fun i hi => hk i hi.le)
        (fun h' => hk k le_rfl (Or.inl h'))).2 (fun h' => hk k le_rfl (Or.inr h'))
      rw [h0, compositeTaylorDecrement_zero_right] at hpos
      exact lt_irrefl _ hpos
    have hineq : MeasureIneq (Lw + arSigmaMax P.toARParams Lw)
        (2 * Lh * Lc p / ((p + 1)! : ℝ)) (P.ς - P.θ) (ε j) (δ (k + 1) j) ‖s k‖ j p := by
      rw [measureIneq_iff]
      exact hlt.le
    obtain ⟨hc1, hc2⟩ := norm_step_ge_of_measure_ineq hineq hA hB hBA ha haA hεj.1 hεj.2 ht hδ
      hjp
    exact ⟨fun hδ1 => hc1 (by rw [hδ1]; exact hshort.le), fun hpol => hc2 _ hκ hκ1 hpol⟩

/-! ### The radius policy (Lemma 14.1.3 for every output of the detailed Step 2) -/

/-- **The radii of the detailed Step 2 are bounded below** ([cartis2022evaluation], Lemma 14.1.3,
for every execution of Algorithm 14.1.2). Let $X \subseteq C$, let $\nabla^p f$ and $\nabla^p c$
be $L_{f,p}$- and $L_{c,p}$-Lipschitz anchored at the points of $A$ with respect to $C$, let $A$
contain $\{y \in X : w(y) \le w(x_0)\}$, and let $h$ be subadditive with $h(0) = 0$ and have the
Lipschitz constant $L_h$, with $L_{f,p} + L_h L_{c,p} \le L_w$. Let $\|\nabla^i f(y)\| \le K_f$
and $\|\nabla^i c(y)\| \le K_c$ for $i \in [2, p]$ and $y \in A$, with $K_f, K_c \ge 0$,
$K_f + L_h K_c \le K_w$ and $K_w \ge 1$. Let $1 \le q \le p$ and $\varepsilon \in (0, 1]^q$.
Consider an ARqp run on $X$ for $w$ with the composite model data, and an iteration $k$ that is
reached and whose Step-2 pair $(s_k, \delta_{s_k})$ is an output of the detailed Step 2
(`Optimization.IsARqpCDetailedStep`) with some halving set $J$. Then $$\delta_{s_k, j} \ge
\kappa_{\delta, \min} \varepsilon_j \quad \text{for all } j \in [1, q],$$ where $\kappa_{\delta,
\min} = \kappa_\delta(\sigma_{\max})$ is computed with $K_w$.

The bound holds whatever the length of the step. -/
theorem arqpKappaDelta_mul_le_radius_composite (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0) (hLw : Lf p + Lh * Lc p ≤ Lw) {Kf Kc : ℝ}
    (hKf : 0 ≤ Kf) (hKc : 0 ≤ Kc) (hKw : Kf + Lh * Kc ≤ Kw) (hKw1 : 1 ≤ Kw)
    (hjf : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Kf)
    (hjc : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i c y‖ ≤ Kc) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {J : Set ℕ}
    {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hdet : IsARqpCDetailedStep f c h X p q P ε J (σ k) (x k) (s k) (δs k)) :
    ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) * ε j ≤ δs k j := by
  intro j hj
  obtain ⟨hxX, hxw⟩ := hr.mem_compositeSublevel hk
  have hxA := hA _ hxX hxw
  have hDf : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f (x k) i‖ ≤ Kf := fun i hi =>
    hjf i hi _ hxA
  have hDc : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c (x k) i‖ ≤ Kc := fun i hi =>
    hjc i hi _ hxA
  have hLh0 := hLh.nonneg
  have hεj := hε j hj
  have hσ : 0 < σ k := hr.toIsARRun.sigma_pos hk k le_rfl
  have hσmax := hr.sigma_le_of_compositeAnchored hf hc hLh hLw hXC hA hk k le_rfl
  have hς := P.ς_pos
  have hθ := P.θ_pos
  set K := 3 * Kw + σ k
  have hK : 3 ≤ K := by simp only [K]; linarith
  have hκ1 : arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) * ε j ≤
      P.ς * P.θ / (8 * K) * ε j := by
    rw [arqpKappaDelta_def]
    gcongr
    · exact hεj.1.le
    · simp only [K]; linarith
  refine hκ1.trans ?_
  have hδout := hdet.spec.2.2.2.1
  by_cases hJ : j ∈ J
  · set δbar : ℕ → ℝ := fun i => min 1 (P.ς * P.θ * ε i / (4 * K))
    have hsm : P.ς * P.θ * ε j / (4 * K) ≤ 1 := by
      have hςθ : P.ς * P.θ ≤ 1 := by nlinarith [P.ς_le_one, P.θ_lt_one]
      rw [div_le_one (by positivity)]
      nlinarith [hεj.2, hεj.1]
    have hge := hdet.radius_ge (δbar := δbar) hq (fun i _ _ => min_le_left _ _)
      (fun s' hs' hs'1 i _ hiq δ' hδ' d' hd' hdec => by
        have hi' : i ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.1 hiq).1, (Finset.mem_Icc.1 hiq).2.trans hqp⟩
        have hεi := (hε i hiq).1
        have hK' : 0 < 3 * (Kf + Lh * Kc) + σ k := by
          have : 0 ≤ Lh * Kc := mul_nonneg hLh0 hKc
          linarith
        have hδα : 4 * (3 * (Kf + Lh * Kc) + σ k) * δ' ≤ P.ς * P.θ * ε i := by
          have h2 := hδ'.2.trans (min_le_right _ _)
          rw [le_div_iff₀ (by positivity)] at h2
          have : 4 * (3 * (Kf + Lh * Kc) + σ k) * δ' ≤ 4 * K * δ' := by
            gcongr
            · exact hδ'.1.le
            · simp only [K]; linarith
          linarith
        have := compositeRegularizedModel_sub_ge_of_decrement_ge hLh hS h0 hKf hKc hDf hDc
          hσ.le hi' hs'1.le hδ'.1.le (hδ'.2.trans (min_le_left _ _)) hδα
          (mem_closedBall_zero_iff.1 hd'.1) hdec
        calc P.ς * P.θ * ε i * δ' ^ i / (2 * i !) = P.ς * P.θ * ε i / 2 * δ' ^ i / i ! := by
              field_simp
          _ ≤ _ := this) j hJ hj
    refine le_trans (le_of_eq ?_) hge
    simp only [δbar, min_eq_right hsm]
    field_simp
    ring
  · rw [hδout j hJ]
    have : P.ς * P.θ / (8 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [P.ς_le_one, P.θ_lt_one]
    nlinarith [hεj.2, hεj.1, div_nonneg (by positivity : (0 : ℝ) ≤ P.ς * P.θ)
      (by positivity : (0 : ℝ) ≤ 8 * K)]

/-! ### Lemma 14.1.9: the decrease of a successful iteration -/

/-- Let iteration $k$ of an ARqp run with the composite model data be reached, not terminate, and be
successful. Then $$\frac{\sigma_{\min}}{(p+1)!} \|s_k\|^{p+1} \le \Delta T_{w,p}(x_k, s_k)
\quad\text{and}\quad \eta_1 \Delta T_{w,p}(x_k, s_k) \le w(x_k) - w(x_{k+1}).$$
-/
theorem composite_pred_bounds
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hsucc : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k) :
    P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (s k) ∧
    P.η₁ * compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p
        (s k) ≤ (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hk' : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i := fun i hi => hk i hi.le
  obtain ⟨hpred5, hpos⟩ := hr.compositeTaylorDecrement_ge hk' fun h' => hk k le_rfl (Or.inl h')
  have hpos := hpos fun h' => hk k le_rfl (Or.inr h')
  have hσmin : P.σmin ≤ σ k := hr.toIsARRun.sigmaMin_le hk' k le_rfl
  have hfac : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
  exact ⟨le_trans (by gcongr) hpred5,
    (hr.toIsARRun.sub_ge_of_succ (w := fun y => f y + h (c y))
      (pred := fun k => compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) hk rfl hpos hsucc).2⟩

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases of ARqpC), unit-radius
case. Assume the hypotheses of `Optimization.IsARqpRun.exists_composite_radius_ineq` with
$q = 1$ in place of $1 \le q$, and also $\theta < \varsigma$ and $\delta_{k+1, 1} = 1$. Then
$$\Delta T_{w,p}(x_k, s_k) \ge \kappa_{\Delta m} \varepsilon_1^{(p+1)/p} \qquad (14.1.32)$$ and
$$w(x_k) - w(x_{k+1}) \ge \eta_1 \kappa_{\Delta m} \varepsilon_1^{(p+1)/p}, \qquad (14.1.33)$$
where $\kappa_{\Delta m}$ is `Optimization.arqpcKappaDmUnit` for $L_w$. -/
theorem composite_decrease_unit (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p) (hLw : Lf p + Lh * Lc p ≤ Lw) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : q = 1) (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hsucc : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1)) (hδ1 : δ (k + 1) 1 = 1) :
    arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p) ≤
        compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (s k) ∧
      P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p)) ≤
        (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hq1 : 1 ≤ q := hq.ge
  have hp : 1 ≤ p := hq1.trans hqp
  obtain ⟨hpred, hdecr⟩ := hr.composite_pred_bounds hk hsucc
  obtain ⟨j₀, hj₀, hb1, -⟩ := hr.composite_norm_step_ge (Kw := 1) hf hc hLh hLf hLc hLw le_rfl
    hXC hA hq1 hqp hθς hε hδ₀ hk hsucc h1
  have hj₀1 : j₀ = 1 := by have := Finset.mem_Icc.1 hj₀; omega
  subst hj₀1
  have hb := hb1 hδ1
  obtain ⟨ha, -, hApos, -⟩ := arqpc_consts (Kw := 1) hp hθς hLw hLf hLc hLh.nonneg le_rfl 1
  have hε1 := hε 1 hj₀
  have hbase : 0 ≤ (P.ς - P.θ) / (((1 : ℕ)! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
      ε 1 / 3 :=
    div_nonneg (mul_nonneg (div_nonneg ha.le (mul_nonneg (by positivity) hApos.le)) hε1.1.le)
      (by norm_num)
  have hη := P.η₁_pos
  have hσm : 0 ≤ P.σmin := P.σmin_nonneg
  have hv : arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p) ≤
      compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (s k) := by
    refine (le_of_eq ?_).trans (le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hbase _) hb (p + 1)) (by positivity)) hpred)
    unfold arqpcKappaDmUnit
    have hexp : (p : ℝ) - ((1 : ℕ) : ℝ) + 1 = p := by push_cast; ring
    rw [hexp, rpow_one_div_pow_succ hbase, Nat.factorial_one, Nat.cast_one, one_mul,
      show (P.ς - P.θ) / (Lw + arSigmaMax P.toARParams Lw) * ε 1 / 3 =
        ((P.ς - P.θ) / (Lw + arSigmaMax P.toARParams Lw) / 3) * ε 1 by ring,
      Real.mul_rpow (by positivity) hε1.1.le]
    ring
  exact ⟨hv, (mul_le_mul_of_nonneg_left hv hη.le).trans hdecr⟩

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases of ARqpC), general
case. Assume the hypotheses of `Optimization.IsARqpRun.composite_norm_step_ge`, and assume that
$\|s_k\| \ge 1$ or $\delta_{k+1,j} \ge \kappa_{\delta, \min} \varepsilon_j$ for all
$j \in [1, q]$ (the radius policy (14.1.28)). Then for some $j \in [1, q]$ $$\Delta T_{w,p}(x_k,
s_k) \ge \kappa_{\Delta m} \varepsilon_j^{j+1} \quad\text{and}\quad w(x_k) - w(x_{k+1}) \ge
\eta_1 \kappa_{\Delta m} \varepsilon_j^{j+1},$$ where $\kappa_{\Delta m}$ is
`Optimization.arqpcKappaDm` for $L_w$ and $K_w$. -/
theorem composite_decrease (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p) (hLw : Lf p + Lh * Lc p ≤ Lw) (hKw : 1 ≤ Kw)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (hsucc : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1))
    (hpol : 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) * ε j ≤ δ (k + 1) j) :
    ∃ j ∈ Finset.Icc 1 q,
      arqpcKappaDm P Lw Kw p q * ε j ^ (j + 1) ≤
        compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (s k) ∧
      P.η₁ * (arqpcKappaDm P Lw Kw p q * ε j ^ (j + 1)) ≤
        (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLh0 := hLh.nonneg
  obtain ⟨hpred, hdecr⟩ := hr.composite_pred_bounds hk hsucc
  have hη := P.η₁_pos
  have hσm : 0 ≤ P.σmin := P.σmin_nonneg
  have finish : ∀ v : ℝ, v ≤ compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
      (ftaylorSeries ℝ c (x k)) h p (s k) →
      v ≤ compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p
          (s k) ∧
        P.η₁ * v ≤ (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) :=
    fun v hv => ⟨hv, (mul_le_mul_of_nonneg_left hv hη.le).trans hdecr⟩
  obtain ⟨j₀, hj₀, -, hb2⟩ := hr.composite_norm_step_ge hf hc hLh hLf hLc hLw hKw hXC hA hq hqp
    hθς hε hδ₀ hk hsucc h1
  obtain ⟨ha1, -, hA1, -, -, hκ, hκ1⟩ := arqpc_consts hp hθς hLw hLf hLc hLh0 hKw 1
  set Aw := Lw + arSigmaMax P.toARParams Lw
  set κ := arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw)
  have hq1 : (1 : ℝ) ≤ (q ! : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero q)
  have hBq0 : 0 < (P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3 := by positivity
  have hqp' : (q : ℝ) ≤ p := by exact_mod_cast hqp
  have hBq1 : (P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3 ≤ 1 := by
    have h1' : (P.ς - P.θ) / ((q ! : ℝ) * Aw) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact (arqpc_consts hp hθς hLw hLf hLc hLh0 hKw q).2.1
    have h2' : κ ^ q ≤ 1 := pow_le_one₀ hκ.le hκ1
    have : 0 ≤ (P.ς - P.θ) / ((q ! : ℝ) * Aw) := by positivity
    nlinarith [pow_nonneg hκ.le q]
  have hKdm : arqpcKappaDm P Lw Kw p q ≤ P.σmin / ((p + 1)! : ℝ) := by
    unfold arqpcKappaDm
    have : ((P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3) ^ (((p : ℝ) + 1) / ((p : ℝ) - q + 1))
        ≤ 1 := Real.rpow_le_one hBq0.le hBq1 (div_nonneg (by positivity) (by linarith))
    calc _ ≤ P.σmin / ((p + 1)! : ℝ) * 1 := by gcongr
      _ = _ := mul_one _
  rcases le_or_gt 1 ‖s k‖ with hlong | hshort
  · -- a long step
    have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    refine ⟨1, hj1, finish _ (le_trans ?_ hpred)⟩
    have hε1 := hε 1 hj1
    have h1' : ε 1 ^ (1 + 1) ≤ 1 := pow_le_one₀ hε1.1.le hε1.2
    have h2' : 1 ≤ ‖s k‖ ^ (p + 1) := one_le_pow₀ hlong
    have h3' : 0 ≤ arqpcKappaDm P Lw Kw p q := by
      unfold arqpcKappaDm; exact mul_nonneg (by positivity) (Real.rpow_nonneg hBq0.le _)
    calc arqpcKappaDm P Lw Kw p q * ε 1 ^ (1 + 1) ≤ arqpcKappaDm P Lw Kw p q * 1 :=
          mul_le_mul_of_nonneg_left h1' h3'
      _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
          have : 0 ≤ P.σmin / ((p + 1)! : ℝ) := by positivity
          nlinarith
  · have hpol' := hpol.resolve_left (not_le.2 hshort)
    have hb := hb2 (hpol' j₀ hj₀)
    refine ⟨j₀, hj₀, finish _ (le_trans ?_ hpred)⟩
    have hεj := hε j₀ hj₀
    obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj₀
    have hjq' : (j₀ : ℝ) ≤ q := by exact_mod_cast hjq
    have hBj0 : 0 < (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3 := by positivity
    -- `B_q ≤ B_j`
    have hBqj : (P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3 ≤
        (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3 := by
      have hf' : (j₀ ! : ℝ) ≤ (q ! : ℝ) := by exact_mod_cast Nat.factorial_le hjq
      have hk' : κ ^ q ≤ κ ^ j₀ := pow_le_pow_of_le_one hκ.le hκ1 hjq
      have hd : (P.ς - P.θ) / ((q ! : ℝ) * Aw) ≤ (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) :=
        div_le_div_of_nonneg_left ha1.le (by positivity) (by gcongr)
      have : 0 ≤ (P.ς - P.θ) / ((q ! : ℝ) * Aw) := by positivity
      gcongr
    have hBj1 : (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3 ≤ 1 := by
      have h1' : (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact (arqpc_consts hp hθς hLw hLf hLc hLh0 hKw j₀).2.1
      have h2' : κ ^ j₀ ≤ 1 := pow_le_one₀ hκ.le hκ1
      have : 0 ≤ (P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) := by positivity
      nlinarith [pow_nonneg hκ.le j₀]
    have hej : 0 < (p : ℝ) - j₀ + 1 := by linarith
    have heq : 0 < (p : ℝ) - q + 1 := by linarith
    have hexp : ((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1) ≤ ((p : ℝ) + 1) / ((p : ℝ) - q + 1) :=
      div_le_div_of_nonneg_left (by positivity) heq (by linarith)
    have hmono : ((P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3) ^
          (((p : ℝ) + 1) / ((p : ℝ) - q + 1)) ≤
        ((P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3) ^
          (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) :=
      (Real.rpow_le_rpow hBq0.le hBqj (by positivity)).trans
        (Real.rpow_le_rpow_of_exponent_ge hBj0 hBj1 hexp)
    have hsb : (arqpcStepBound P Lw Kw p j₀ (ε j₀)) ^ (p + 1) =
        ((P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3) ^
          (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) * ε j₀ ^ (j₀ + 1) := by
      unfold arqpcStepBound
      rw [mul_pow, rpow_one_div_pow_succ hBj0.le, ← Real.rpow_natCast (ε j₀ ^ _),
        ← Real.rpow_mul hεj.1.le, ← Real.rpow_natCast (ε j₀) (j₀ + 1)]
      congr 2
      have : (p : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
    have hsb0 : 0 ≤ arqpcStepBound P Lw Kw p j₀ (ε j₀) :=
      mul_nonneg (Real.rpow_nonneg hBj0.le _) (Real.rpow_nonneg hεj.1.le _)
    have hpow := pow_le_pow_left₀ hsb0 hb (p + 1)
    rw [hsb] at hpow
    unfold arqpcKappaDm
    calc P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) / ((q ! : ℝ) * Aw) * κ ^ q / 3) ^
          (((p : ℝ) + 1) / ((p : ℝ) - q + 1)) * ε j₀ ^ (j₀ + 1)
        ≤ P.σmin / ((p + 1)! : ℝ) * (((P.ς - P.θ) / ((j₀ ! : ℝ) * Aw) * κ ^ j₀ / 3) ^
          (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) * ε j₀ ^ (j₀ + 1)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono
            (pow_nonneg hεj.1.le _)) (by positivity)
      _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by gcongr

/-! ### Lemma 14.1.4: termination in Step 2 -/

/-- **Lemma 14.1.4(ii)** of [cartis2022evaluation]. Let $h$ be subadditive with $h(0) = 0$ and have
the Lipschitz constant $L_h$, and let $q \le p$ and $\varepsilon_j > 0$ for $j \in [1, q]$.
Consider an ARqp run on $X$ for $w$ with the composite model data, and an iteration $k$ that is
reached, at which the Step-1 test fails and Step 2 terminates: $\hat m_k(s_k) = \hat m_k(0)$.
Then there are radii $\delta \in (0, 1]^q$ such that $x_k$ is an
$(\varepsilon, \delta)$-approximate $q$-th order minimizer (14.1.9) of $w$ over $X$, that is,
$\varphi^{\delta_j}_{w,j}(x_k) \le \varepsilon_j \delta_j^j / j!$ for $j \in [1, q]$, with the
measures taken over $\{e : x_k + e \in X\}$.

No smoothness of $f$ or $c$ is needed. The certificate is
`Optimization.IsEpsDeltaApproxComposite`. -/
theorem exists_isEpsDeltaApproxComposite_of_stop₂ (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k)
    (heq : compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p
        (σ k) (s k) =
      compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (σ k) 0) :
    ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
      IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h
        {e | x k + e ∈ X} q ε δ' := by
  have hmin := (hr.step hk h1).isMinOn_of_eq heq
  have hT0 : (0 : E) ∈ {e | x k + e ∈ X} := by simpa using hr.mem k hk
  have hσ : 0 ≤ σ k := (hr.toIsARRun.sigma_pos hk k le_rfl).le
  have hex : ∀ j, ∃ δ' : ℝ, j ∈ Finset.Icc 1 q → 0 < δ' ∧ δ' ≤ 1 ∧
      compositeTaylorMeasure (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
        h j δ' {e | x k + e ∈ X} ≤ ε j * δ' ^ j / j ! := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 q
    · obtain ⟨δ₁, h1, h2, h3⟩ := exists_radius_of_isMinOn_compositeRegularizedModel_zero hLh hS
        h0 hσ hT0 hmin ((Finset.mem_Icc.1 hj).2.trans hqp) (hε j hj)
      exact ⟨δ₁, fun _ => ⟨h1, h2, h3 δ₁ h1.le le_rfl⟩⟩
    · exact ⟨1, fun h' => absurd h' hj⟩
  choose δ' hδ' using hex
  exact ⟨δ', fun j hj => ⟨(hδ' j hj).1, (hδ' j hj).2.1⟩, fun j hj => (hδ' j hj).2.2⟩

/-- **Lemma 14.1.4(i)** of [cartis2022evaluation]. Let $q = 1$ and $p \ge 1$, let $h$ be convex and
have the Lipschitz constant $L_h$, let $X$ be convex, let $f$ and $c$ be of class $C^p$ at every
point of $X$, let $\varepsilon_1 > 0$ and $\delta_{0,1} \in (0, 1]$. Consider an ARqp run on $X$
for $w$ with the composite model data and initial radii $\delta_0$. Then ARqpC never terminates
in Step 2: at every iteration $k$ that is reached and at which the Step-1 test fails,
$\hat m_k(s_k) < \hat m_k(0)$. -/
theorem compositeModel_lt_of_convex (hLh : HasLipschitzConst h Lh) (hconv : ConvexOn ℝ univ h)
    (hXc : Convex ℝ X) (hfC : ∀ y ∈ X, ContDiffAt ℝ p f y) (hcC : ∀ y ∈ X, ContDiffAt ℝ p c y)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : q = 1) (hp : 1 ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k) :
    compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (σ k)
        (s k) <
      compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h p (σ k)
        0 := by
  have hstep := hr.step hk h1
  refine lt_of_le_of_ne hstep.model_le fun heq => h1 ?_
  have hmin := hstep.isMinOn_of_eq heq
  -- `0` minimizes the model on the feasible displacements: the Step-1 test passes
  intro j hj
  have hj1 : j = 1 := by have := Finset.mem_Icc.1 hj; omega
  subst hj1
  have hw := hr.witness k hk 1 hj
  have hxk := hr.mem k hk
  have hTconv : Convex ℝ {e | x k + e ∈ X} := hXc.translate_preimage_right (x k)
  have hT0 : (0 : E) ∈ {e | x k + e ∈ X} := by simpa using hxk
  have hdec := compositeTaylorDecrement_one_nonpos_of_isLocalMinOn_compositeRegularizedModel hLh
    hconv ((hfC _ hxk).isSymm_ftaylorSeries le_rfl) ((hcC _ hxk).isSymm_ftaylorSeries le_rfl) hp
    hTconv hT0 hmin.isLocalMinOn hw.mem
  change compositeTaylorDecrement _ _ h 1 (d k 1) ≤ _
  refine hdec.trans ?_
  have := P.ς_pos
  have := (hε 1 hj).le
  have := (hr.delta_mem hδ₀ k hk 1 hj).1.le
  positivity

/-! ### Theorem 14.1.10: evaluation complexity -/

/-- If iteration $k$ of an ARqp run on $X$ with the composite model data is reached and the Step-1
test holds at $k$, then $x_k$ satisfies the condition (14.1.9) of [cartis2022evaluation] with
the current radii $\delta_k$, over $\{e : x_k + e \in X\}$. -/
theorem isEpsDeltaApproxComposite_of_stop₁
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (h1 : arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k) :
    IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k)) h
      {e | x k + e ∈ X} q ε (δ k) :=
  MeasureTestPasses.isEpsDeltaApproxComposite P.ς_pos (fun j hj => hr.witness k hk j hj) h1

/-- **Theorem 14.1.10, part 2** of [cartis2022evaluation] ($h$ nonconvex or $q > 1$), anchored form.
Let $X \subseteq C$, let $\nabla^p f$ and $\nabla^p c$ be $L_{f,p}$- and $L_{c,p}$-Lipschitz
anchored at the points of $A$ with respect to $C$, with $L_{f,p} \ge 1$ and $L_{c,p} \ge 0$, and
let $A$ contain $\{y \in X : w(y) \le w(x_0)\}$. Let $h$ be subadditive with $h(0) = 0$ and have
the Lipschitz constant $L_h$, with $L_{f,p} + L_h L_{c,p} \le L_w$. Let
$\|\nabla^i f(y)\| \le K_f$ and $\|\nabla^i c(y)\| \le K_c$ for $i \in [2, p]$ and $y \in A$,
with $K_f, K_c \ge 0$, $K_f + L_h K_c \le K_w$ and $K_w \ge 1$. Let $1 \le q \le p$,
$\theta < \varsigma$, $\sigma_{\min} > 0$, $\varepsilon \in (0, 1]^q$, $\delta_0 \in (0, 1]^q$,
and let $w \ge w_{\mathrm{low}}$ on $X$. Let $0 < m_\varepsilon \le \varepsilon_j^{j+1}$ for
$j \in [1, q]$, for example $m_\varepsilon = \min_j \varepsilon_j^{j+1}$. Consider an ARqp run
on $X$ for $w$ with the composite model data and initial radii $\delta_0$, whose Step-2 pair is
an output of the detailed Step 2 with a halving set $J$ at every iteration that is reached and
at which the Step-1 test fails. Then the run terminates at some $k_\varepsilon$, the point
$x_{k_\varepsilon}$ is an $(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer
(14.1.9) for some $\delta_\varepsilon \in (0, 1]^q$, and with $\delta = \eta_1 \kappa_{\Delta m}
m_\varepsilon$ the run uses at most $$\kappa_A \frac{w(x_0) - w_{\mathrm{low}}}{\delta} +
\kappa_C \text{ evaluations of } f \text{ and } c \text{ (14.1.36)}, \qquad \frac{w(x_0) -
w_{\mathrm{low}}}{\delta} + 2 \text{ evaluations of their derivatives (14.1.37)}.$$ Here
$\kappa_{\Delta m}$ is `Optimization.arqpcKappaDm` for $L_w$ and $K_w$,
$\kappa_A = 1 + |\log \gamma_1| / \log \gamma_2$ and $\kappa_C = (|\log \gamma_1| +
\log(\sigma_{\max} / \sigma_0)) / \log \gamma_2 + 2$. The bound is
$O(\max_j \varepsilon_j^{-(j+1)})$.

The detailed Step 2 makes the radius policy (14.1.28) hold for every run, by
`Optimization.IsARqpRun.arqpKappaDelta_mul_le_radius_composite`; the decreases come from
`Optimization.IsARqpRun.composite_decrease`. -/
theorem complexity_composite (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0) (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p)
    (hLw : Lf p + Lh * Lc p ≤ Lw) {Kf Kc : ℝ} (hKf : 0 ≤ Kf) (hKc : 0 ≤ Kc)
    (hKw : Kf + Lh * Kc ≤ Kw) (hKw1 : 1 ≤ Kw)
    (hjf : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Kf)
    (hjc : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i c y‖ ≤ Kc) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hθς : P.θ < P.ς) (hσmin : 0 < P.σmin)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    {J : Set ℕ}
    (hdet : ∀ k, (∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) →
      ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k →
      IsARqpCDetailedStep f c h X p q P ε J (σ k) (x k) (s k) (δs k))
    {wlow : ℝ} (hb : ∀ y ∈ X, wlow ≤ f y + h (c y)) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, IsFirstHit (arqpcStop f c h P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε)) h
          {e | x kε + e ∈ X} q ε δε) ∧
      (funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (arqpcKappaDm P Lw Kw p q * mε))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams Lw / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + h (c y))
          (arqpcData f c h p x σ) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (arqpcKappaDm P Lw Kw p q * mε)) + 2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLh0 := hLh.nonneg
  obtain ⟨ha, -, hApos, -, -, hκδ, hκδ1⟩ := arqpc_consts hp hθς hLw hLf hLc hLh0 hKw1 1
  have hBq0 : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) *
      arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) ^ q / 3 := by
    have : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (Lw + arSigmaMax P.toARParams Lw)) :=
      div_pos ha (by positivity)
    positivity
  have hκ : 0 < arqpcKappaDm P Lw Kw p q := by
    unfold arqpcKappaDm
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hBq0 _)
  have hδ : 0 < P.η₁ * (arqpcKappaDm P Lw Kw p q * mε) :=
    mul_pos P.η₁_pos (mul_pos hκ hmε0)
  obtain ⟨kε, hhit, hF, hD⟩ := hr.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams Lw)
    (fun k hk => hr.sigma_le_of_compositeAnchored hf hc hLh hLw hXC hA hk k le_rfl)
    (V := fun k => f (x k) + h (c (x k))) (Vlow := wlow) hδ
    (fun k hk => hr.composite_objective_succ_le hk)
    (fun k hk => hb _ (hr.mem k hk))
    (fun k hk hs => by
      have hk' : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i :=
        fun i hi => hk i (hi.trans k.le_succ)
      have h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1) :=
        fun h' => hk (k + 1) le_rfl (Or.inl h')
      have hrad : δ (k + 1) = δs k := (hr.radii k hk').1 hs
      have hk'' : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i := fun i hi => hk' i hi.le
      have h1k : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k :=
        fun h' => hk' k le_rfl (Or.inl h')
      have hpol := hr.arqpKappaDelta_mul_le_radius_composite hf hc hLh hS h0 hLw hKf hKc hKw
        hKw1 hjf hjc hXC hA hq hqp hε hk'' (hdet k hk'' h1k)
      rw [← hrad] at hpol
      obtain ⟨j, hj, -, hdec⟩ := hr.composite_decrease hf hc hLh hLf hLc hLw hKw1 hXC hA hq hqp
        hθς hε hδ₀ hk' hs h1 (Or.inr hpol)
      refine le_trans ?_ hdec
      gcongr
      · exact P.η₁_pos.le
      · exact hmε j hj)
  refine ⟨kε, hhit, ?_, hF, hD⟩
  have hbef := hhit.2
  rcases em (arqpStop₁ P q ε (arqpcData f c h p x σ) δ d kε) with h1 | h1
  · exact ⟨δ kε, hr.delta_mem hδ₀ kε hbef, hr.isEpsDeltaApproxComposite_of_stop₁ hbef h1⟩
  · exact hr.exists_isEpsDeltaApproxComposite_of_stop₂ hLh hS h0 hqp (fun j hj => (hε j hj).1)
      hbef h1 (hhit.1.resolve_left h1)

/-- Let $\delta_{0,1} = 1$, and let the Step-2 radius of order $1$ be $\delta_{s_k, 1} = 1$ at every
iteration $k$ that is reached and at which the Step-1 test fails. Then $\delta_{k,1} = 1$ at
every iteration $k$ that is reached. -/
theorem delta_one_eq
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hδ₀ : δ₀ 1 = 1)
    (hpol : ∀ k, (∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) →
      ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k → δs k 1 = 1) :
    ∀ k, (∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) → δ k 1 = 1 := by
  intro k
  induction k with
  | zero => intro _; rw [hr.delta_zero, hδ₀]
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨h1, h2⟩ := hr.radii k hk'
    by_cases hs : P.η₁ ≤ arqpRatio (fun y => f y + h (c y)) (arqpcData f c h p x σ) x s k
    · rw [h1 hs]
      exact hpol k (fun i hi => hk' i hi.le) fun h' => hk' k le_rfl (Or.inl h')
    · rw [(h2 hs).1]
      exact ih fun i hi => hk' i hi.le

/-- **Theorem 14.1.10, part 1** of [cartis2022evaluation] ($q = 1$, $h$ and $X$ convex), anchored
form. Let $X \subseteq C$ be convex, let $\nabla^p f$ and $\nabla^p c$ be $L_{f,p}$- and
$L_{c,p}$-Lipschitz anchored at the points of $A$ with respect to $C$, with $L_{f,p} \ge 1$ and
$L_{c,p} \ge 0$, and let $A$ contain $\{y \in X : w(y) \le w(x_0)\}$. Let $h$ be convex and have
the Lipschitz constant $L_h$, with $L_{f,p} + L_h L_{c,p} \le L_w$. Let $q = 1 \le p$,
$\theta < \varsigma$, $\sigma_{\min} > 0$, $\varepsilon_1 \in (0, 1]$, $\delta_{0,1} = 1$, and
let $w \ge w_{\mathrm{low}}$ on $X$. Consider an ARqp run on $X$ for $w$ with the composite
model data and initial radii $\delta_0$, whose Step-2 radius is $\delta_{s_k, 1} = 1$ at every
iteration $k$ that is reached and at which the Step-1 test fails. Then the run terminates at
some $k_\varepsilon$ with $\varphi^1_{w,1}(x_{k_\varepsilon}) \le \varepsilon_1$, and with
$\delta = \eta_1 \kappa_{\Delta m} \varepsilon_1^{(p+1)/p}$ it uses at most $$\kappa_A
\frac{w(x_0) - w_{\mathrm{low}}}{\delta} + \kappa_C \text{ evaluations of } f \text{ and } c
\text{ (14.1.34)}, \qquad \frac{w(x_0) - w_{\mathrm{low}}}{\delta} + 2 \text{ evaluations of
their derivatives (14.1.35)}.$$ Here $\kappa_{\Delta m}$ is `Optimization.arqpcKappaDmUnit` for
$L_w$, and $\kappa_A$ and $\kappa_C$ are as in `Optimization.IsARqpRun.complexity_composite`.
The bound is $O(\varepsilon_1^{-(p+1)/p})$.

The detailed Step 2 computes such radii: it never halves the first-order radius when $h$ and $X$
are convex. The measure $\varphi^1_{w,1}$ is `Optimization.compositeTaylorMeasure` of order $1$
and radius $1$ over $\{e : x_{k_\varepsilon} + e \in X\}$. -/
theorem complexity_composite_unit (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hconv : ConvexOn ℝ univ h) (hXc : Convex ℝ X) (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p)
    (hLw : Lf p + Lh * Lc p ≤ Lw) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A)
    (hr : IsARqpRun (fun y => f y + h (c y)) X P q ε δ₀ (arqpcData f c h p x σ) x s σ δ δs d dm)
    (hq : q = 1) (hqp : q ≤ p) (hθς : P.θ < P.ς) (hσmin : 0 < P.σmin)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (hδ₀1 : δ₀ 1 = 1)
    (hδs : ∀ k, (∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i) →
      ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k → δs k 1 = 1)
    {wlow : ℝ} (hb : ∀ y ∈ X, wlow ≤ f y + h (c y)) :
    ∃ kε, IsFirstHit (arqpcStop f c h P p q ε x s σ δ d) kε ∧
      compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε)) h 1 1
        {e | x kε + e ∈ X} ≤ ε 1 ∧
      (funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams Lw / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + h (c y))
          (arqpcData f c h p x σ) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 := by
  have hq1 : 1 ≤ q := hq.ge
  have hp : 1 ≤ p := hq1.trans hqp
  have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq1⟩
  have hε1 := hε 1 hj1
  obtain ⟨ha, -, hApos, -⟩ := arqpc_consts (Kw := 1) hp hθς hLw hLf hLc hLh.nonneg le_rfl 1
  have hκ : 0 < arqpcKappaDmUnit P Lw p := by
    unfold arqpcKappaDmUnit
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos
      (div_pos (div_pos ha hApos) (by norm_num)) _)
  have hδ : 0 < P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p)) :=
    mul_pos P.η₁_pos (mul_pos hκ (Real.rpow_pos_of_pos hε1.1 _))
  obtain ⟨kε, hhit, hF, hD⟩ := hr.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams Lw)
    (fun k hk => hr.sigma_le_of_compositeAnchored hf hc hLh hLw hXC hA hk k le_rfl)
    (V := fun k => f (x k) + h (c (x k))) (Vlow := wlow) hδ
    (fun k hk => hr.composite_objective_succ_le hk)
    (fun k hk => hb _ (hr.mem k hk))
    (fun k hk hs => by
      have hk' : ∀ i ≤ k, ¬ arqpcStop f c h P p q ε x s σ δ d i :=
        fun i hi => hk i (hi.trans k.le_succ)
      have h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d (k + 1) :=
        fun h' => hk (k + 1) le_rfl (Or.inl h')
      have hδ1 := hr.delta_one_eq hδ₀1 hδs (k + 1) fun i hi => hk i hi.le
      exact (hr.composite_decrease_unit hf hc hLh hLf hLc hLw hXC hA hq hqp hθς hε hδ₀ hk' hs h1
        hδ1).2)
  refine ⟨kε, hhit, ?_, hF, hD⟩
  -- termination is in Step 1, with `δ_{k_ε,1} = 1`
  have hbef := hhit.2
  have h1 : arqpStop₁ P q ε (arqpcData f c h p x σ) δ d kε := by
    rcases hhit.1 with h1 | h2
    · exact h1
    · by_contra hn
      exact ne_of_lt (hr.compositeModel_lt_of_convex hLh hconv hXc
        (fun y hy => hf.contDiffAt y (hXC hy)) (fun y hy => hc.contDiffAt y (hXC hy)) hq hp
        (fun j hj => (hε j hj).1) hδ₀ hbef hn) h2
  have happ := hr.isEpsDeltaApproxComposite_of_stop₁ hbef h1 1 hj1
  rw [hr.delta_one_eq hδ₀1 hδs kε hbef] at happ
  simpa using happ

end IsARqpRun

/-! ### ARqpC runs -/

namespace IsARqpCRun

variable {J : Set ℕ}

/-- **The radius policy (14.1.28) holds for every ARqpC run** ([cartis2022evaluation], Lemma 14.1.3
for every output of Algorithm 14.1.2). Let `Optimization.IsARqpCRun` hold for $f$, $c$, $h$, $X$
and a halving set $J$. Assume the hypotheses of
`Optimization.IsARqpRun.arqpKappaDelta_mul_le_radius_composite` on $f$, $c$, $h$, $C$, $A$,
$L_w$, $K_f$, $K_c$ and $K_w$. Then at every iteration $k$ that is reached and at which the
Step-1 test fails, $\delta_{s_k, j} \ge \kappa_{\delta, \min} \varepsilon_j$ for all
$j \in [1, q]$.

The conditions $1 \le q \le p$ and $\varepsilon \in (0, 1]^q$ and the detailed Step 2 are part
of `Optimization.IsARqpCRun`. -/
theorem arqpKappaDelta_mul_le_radius (hr : IsARqpCRun f c h X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p Lf) (hc : LipschitzDerivsAnchored c C A p p Lc)
    (hLh : HasLipschitzConst h Lh) (hS : IsSubadditive h) (h0 : h 0 = 0)
    (hLw : Lf p + Lh * Lc p ≤ Lw) {Kf Kc : ℝ} (hKf : 0 ≤ Kf) (hKc : 0 ≤ Kc)
    (hKw : Kf + Lh * Kc ≤ Kw) (hKw1 : 1 ≤ Kw)
    (hjf : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Kf)
    (hjc : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i c y‖ ≤ Kc) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpcData f c h p x σ) δ d k) :
    ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P Kw (arSigmaMax P.toARParams Lw) * ε j ≤ δs k j :=
  hr.run.arqpKappaDelta_mul_le_radius_composite hf hc hLh hS h0 hLw hKf hKc hKw hKw1 hjf hjc hXC
    hA hr.one_le_q hr.q_le_p hr.ε_mem hk (hr.detailed k hk h1)

/-- **Theorem 14.1.10, part 2** of [cartis2022evaluation] for every ARqpC run. Let
`Optimization.IsARqpCRun` hold for $f$, $c$, $h$, $X$ and a halving set $J$. Assume the
hypotheses of `Optimization.IsARqpRun.complexity_composite` on $f$, $c$, $h$, $C$, $A$, the
constants, $w_{\mathrm{low}}$ and $m_\varepsilon$. Then the run terminates at some
$k_\varepsilon$ at an $(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer for
some $\delta_\varepsilon \in (0, 1]^q$, with the evaluation bounds of
`Optimization.IsARqpRun.complexity_composite`.

The constant $\kappa_A$ is written `Optimization.arqpKappaUns`. -/
theorem complexity (hr : IsARqpCRun f c h X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hS : IsSubadditive h) (h0 : h 0 = 0) (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p)
    (hLw : Lf p + Lh * Lc p ≤ Lw) {Kf Kc : ℝ} (hKf : 0 ≤ Kf) (hKc : 0 ≤ Kc)
    (hKw : Kf + Lh * Kc ≤ Kw) (hKw1 : 1 ≤ Kw)
    (hjf : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Kf)
    (hjc : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i c y‖ ≤ Kc) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A) (hθς : P.θ < P.ς)
    (hσmin : 0 < P.σmin) {wlow : ℝ} (hb : ∀ y ∈ X, wlow ≤ f y + h (c y)) {mε : ℝ}
    (hmε0 : 0 < mε) (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, IsFirstHit (arqpcStop f c h P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε)) h
          {e | x kε + e ∈ X} q ε δε) ∧
      (funEvalCount kε : ℝ) ≤
        arqpKappaUns P *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (arqpcKappaDm P Lw Kw p q * mε))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams Lw / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + h (c y))
          (arqpcData f c h p x σ) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (arqpcKappaDm P Lw Kw p q * mε)) + 2 :=
  hr.run.complexity_composite hf hc hLh hS h0 hLf hLc hLw hKf hKc hKw hKw1 hjf hjc hXC hA
    hr.one_le_q hr.q_le_p hθς hσmin hr.ε_mem hr.δ₀_mem hr.detailed hb hmε0 hmε

/-- **Theorem 14.1.10, part 1** of [cartis2022evaluation] for every ARqpC run. Let
`Optimization.IsARqpCRun` hold for $f$, $c$, $h$, $X$ with $q = 1$ and a halving set $J$ with
$1 \notin J$, and let $\delta_{0,1} = 1$. Assume the hypotheses of
`Optimization.IsARqpRun.complexity_composite_unit` on $f$, $c$, $h$, $X$, $C$, $A$, the
constants and $w_{\mathrm{low}}$. Then the run terminates at some $k_\varepsilon$ with
$\varphi^1_{w,1}(x_{k_\varepsilon}) \le \varepsilon_1$, with the evaluation bounds of
`Optimization.IsARqpRun.complexity_composite_unit`.

The halving set `compositeHalvingSet h X` of the source does not contain $1$ when $h$ and $X$
are convex (`Optimization.one_notMem_compositeHalvingSet`). The constant $\kappa_A$ is written
`Optimization.arqpKappaUns`. -/
theorem complexity_unit (hr : IsARqpCRun f c h X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p Lf)
    (hc : LipschitzDerivsAnchored c C A p p Lc) (hLh : HasLipschitzConst h Lh)
    (hconv : ConvexOn ℝ univ h) (hXc : Convex ℝ X) (hLf : 1 ≤ Lf p) (hLc : 0 ≤ Lc p)
    (hLw : Lf p + Lh * Lc p ≤ Lw) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y + h (c y) ≤ f (x 0) + h (c (x 0)) → y ∈ A) (hq : q = 1)
    (hθς : P.θ < P.ς) (hσmin : 0 < P.σmin) (hδ₀1 : δ₀ 1 = 1) (h1J : 1 ∉ J) {wlow : ℝ}
    (hb : ∀ y ∈ X, wlow ≤ f y + h (c y)) :
    ∃ kε, IsFirstHit (arqpcStop f c h P p q ε x s σ δ d) kε ∧
      compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε)) h 1 1
        {e | x kε + e ∈ X} ≤ ε 1 ∧
      (funEvalCount kε : ℝ) ≤
        arqpKappaUns P *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams Lw / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + h (c y))
          (arqpcData f c h p x σ) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (arqpcKappaDmUnit P Lw p * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 :=
  hr.run.complexity_composite_unit hf hc hLh hconv hXc hLf hLc hLw hXC hA hq hr.q_le_p hθς hσmin
    hr.ε_mem hr.δ₀_mem hδ₀1 (fun _ hk h1 => hr.radius_eq_one hk h1 h1J) hb

end IsARqpCRun

end Optimization
