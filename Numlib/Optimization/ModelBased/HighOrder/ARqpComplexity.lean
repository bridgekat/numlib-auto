/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.HighOrderModel
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Optimality.HighOrder

/-!
# Evaluation complexity of ARqp with exact derivatives

This file proves the evaluation complexity of the high-order adaptive-regularization method ARqp of
[cartis2022evaluation], §12.2.2, Algorithm 12.2.2, when the model is built from the exact
derivatives of $f : E \to \mathbb{R}$. At iteration $k$ the model is the regularized Taylor model
$$m_k(s) = T_{f,p}(x_k, s) + \frac{\sigma_k}{(p+1)!} \|s\|^{p+1},$$ the predicted decrease is
$\Delta T_{f,p}(x_k, s) = f(x_k) - T_{f,p}(x_k, s)$, and the ratio is $\rho_k = (f(x_k) - f(x_k +
s_k)) / \Delta T_{f,p}(x_k, s_k)$. The run may be restricted to a feasible set $X$: $X = E$ is the
unconstrained method, and a closed $X$ is the method ARqp-SC of §14.2. The main result, Theorem
12.2.14 of the source, is that a run terminates at an $(\varepsilon, \delta)$-approximate $q$-th
order minimizer after $O((f(x_0) - f_{\mathrm{low}}) / \min_j \varepsilon_j^{\pi_j})$ evaluations of
$f$ and of its derivatives.

The smoothness hypothesis is anchored at the iterates. Let $C \supseteq X$ be open and convex, and
let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of a set $A$ with respect to $C$:
$\|\nabla^p f(x) - \nabla^p f(y)\| \le L_p \|x - y\|$ for $x \in A$ and $y \in C$
(`LipschitzDerivsAnchored f C A p p L`). The set $A$ contains the sublevel set $\{y \in X : f(y) \le
f(x_0)\}$, which contains every iterate (`Optimization.IsARqpRun.mem_sublevel`). The models are
built at the iterates, and Taylor's theorem anchored at the iterate relates them to the trial
points. Lipschitz derivatives on $C$ are the case $A = C$. Some results also use the jet bounds
$\|\nabla^i f(y)\| \le L_f$ for $i \in [2, p]$ and $y \in A$, where $L_f = \max(1, L_1, \dots,
L_p)$. These bounds are used only to certify a termination in Step 2 and to construct runs with the
radii property.

The constants of the method are those of `Optimization.ARqpParams`: $\varsigma \in (0, 1]$,
$\theta \in (0, 1)$, $\eta_1$, $\eta_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$, $\sigma_0$ and
$\sigma_{\min}$. The weights stay below $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p / (1 -
\eta_2))$ (`Optimization.arSigmaMax`). The Step-2 radii $\delta_{s_k}$ are handled in a *radii mode*
$u$, which is a proposition: if $u$ holds, the radii are $1$; if $u$ fails, the step is long
($\|s_k\| \ge 1$) or $\delta_{s_k, j} \ge \kappa_\delta(\sigma_{\max}) \varepsilon_j$ at every
order, as in (12.2.51). The source analyses the mode $u = (q \le 2)$. The exponents are
$\pi_j = (p+1)/(p-j+1)$ if $u$ holds and $\pi_j = j(p+1)/p$ otherwise.

## Main definitions

* `Optimization.arqpData`, `Optimization.arqpStop`, `Optimization.arqpRho`: the exact model data,
  the termination test and the ratio of iteration $k$.
* `Optimization.arqpKappaDelta`: the radius constant $\kappa_\delta(\sigma) = \varsigma \theta / (8
  (3 L_f + \sigma))$.
* `Optimization.arqpTau`, `Optimization.arqpKappaHat`: the constants $\tau_j$ and $\hat\kappa =
  \min(\kappa_\delta(\sigma_{\max}), \tau_q / 2)$ of the step-length bound.
* `Optimization.arqpPiOf`, `Optimization.arqpKappaDmOf`: the exponents $\pi_j$ and the decrease
  constant $\kappa_{\Delta m}$ of Lemma 12.2.13 in a radii mode $u$.
* `Optimization.arqpKappaUns`, `Optimization.kappaSARqpOf`, `Optimization.kappaAARqpOf`,
  `Optimization.kappaCARqp`: the constants $\kappa_{\mathrm{uns}}$, $\kappa^s$, $\kappa^a$ and
  $\kappa^c$ of Theorem 12.2.14.

## Main results

* `Optimization.IsARqpRun.mem_sublevel`: the iterates stay in $\{y \in X : f(y) \le f(x_0)\}$.
* `Optimization.IsARqpRun.sigma_le_of_anchored`: the weights satisfy
  $\sigma_{\min} \le \sigma_k \le \sigma_{\max}$ (Lemma 4.1.2 for ARqp).
* `Optimization.exists_isARqpRun_of_anchored`: in finite dimension there are runs with the radii
  property (12.2.50).
* `Optimization.ARqpStep.exists_radius_ineq`: the inequality (12.2.52) for one short step (Lemma
  12.2.11, local form).
* `Optimization.ARqpStep.exists_norm_pow_ge`: a lower bound on the length of a step (Lemma 12.2.12,
  local form).
* `Optimization.ARqpStep.taylorDecrement_ge`, `Optimization.IsARqpRun.decrease`: a successful
  iteration decreases the model and $f$ by at least a multiple of $\min_j \varepsilon_j^{\pi_j}$
  (Lemma 12.2.13).
* `Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet`: if $0$ minimizes the model, the iterate is
  an $(\varepsilon, \delta)$-approximate minimizer with explicit radii (Lemma 12.2.10).
* `Optimization.IsARqpRun.complexity`: a run terminates at an $(\varepsilon, \delta)$-approximate
  $q$-th order minimizer within $O((f(x_0) - f_{\mathrm{low}}) / \min_j \varepsilon_j^{\pi_j})$
  evaluations (Theorem 12.2.14).

## Implementation notes

* A hypothesis `∀ i < k, ¬ arqpStop … i` says that iteration $k$ is reached. A hypothesis
  `∀ i ≤ k, ¬ arqpStop … i` says that iteration $k$ is reached and does not terminate. A run
  terminates at $k_\varepsilon$ if `IsFirstHit (arqpStop …) kε` holds.
* An iteration $k$ is successful if $\rho_k \ge \eta_1$. The number of evaluations of $f$ up to the
  termination index $k_\varepsilon$ is $k_\varepsilon + 1$ (`Optimization.funEvalCount`).
  The number of evaluations of the derivatives is
  $1 + |\{k < k_\varepsilon : \rho_k \ge \eta_1\}|$ (`Optimization.derivEvalCount`).
* The expression `finMax 1 L p` is $\max(1, L_1, \dots, L_p)$.
* The expression `finMin 1 u q` is $\min(1, u_1, \dots, u_q)$. For $\varepsilon_j \in (0, 1]$ and
  $\pi_j \ge 0$, the minimum $\min(1, \varepsilon_1^{\pi_1}, \dots, \varepsilon_q^{\pi_q})$ is
  $\min_j \varepsilon_j^{\pi_j}$.
* The Lean division is $0$ when the denominator is $0$. In `Optimization.arqpPiOf` and
  `Optimization.arqpKappaDmOf` the numbers $p - j + 1$ and $p - q + 1$ are natural numbers with
  truncated subtraction.
-/

open Set Metric Filter
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p q : ℕ}

/-- The **model data of exact ARqp** at iteration $k$ ([cartis2022evaluation], (12.2.23)) is
`ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)`. It consists of the Taylor decrements
$\Delta T_{f,j}(x_k, \cdot)$ of $f$ at $x_k$, the model $$m_k(s) = T_{f,p}(x_k, s) +
\frac{\sigma_k}{(p+1)!} \|s\|^{p+1},$$ the Taylor decrements of $m_k$ at a trial step, and the
predicted decrease $\Delta T_{f,p}(x_k, \cdot)$. -/
noncomputable abbrev arqpData (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    ARqpData E :=
  ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)

/-- The model $m_k(s) = T_{f,p}(x_k, s) + \sigma_k \|s\|^{p+1} / (p+1)!$ of (12.2.23) of
[cartis2022evaluation], at the iterate $x_k$ with the weight $\sigma_k$. -/
noncomputable abbrev arqpModel (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) : E → ℝ :=
  regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)

/-- The **termination test of exact ARqp** at iteration $k$ holds if the Step-1 test holds, that is,
$\Delta T_{f,j}(x_k, d_{k,j}) \le \varsigma \varepsilon_j \delta_{k,j}^j / j!$ for all
$j \in [1, q]$, or if the Step-2 test $m_k(s_k) = m_k(0)$ holds.

The Step-1 test is `Optimization.arqpStop₁` and the Step-2 test is `Optimization.arqpStop₂`,
both for the data `Optimization.arqpData`. -/
abbrev arqpStop (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (x s : ℕ → E) (σ : ℕ → ℝ)
    (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  IsARRun.Stop (arqpStop₁ P q ε (arqpData f p x σ) δ d) (arqpStop₂ (arqpData f p x σ) s) k

/-- The **ratio of exact ARqp** at iteration $k$ ([cartis2022evaluation], (12.2.30)) is $$\rho_k =
\frac{f(x_k) - f(x_k + s_k)}{\Delta T_{f,p}(x_k, s_k)}.$$

The value is $0$ when $\Delta T_{f,p}(x_k, s_k) = 0$, by the Lean convention for division. -/
noncomputable abbrev arqpRho (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  arqpRatio f (arqpData f p x σ) x s k

/-- The Step-1 decrements of `Optimization.arqpData` are the Taylor decrements
$\Delta T_{f,j}(x_k, \cdot)$ of $f$ at $x_k$. -/
@[simp] theorem arqpData_dec (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    (arqpData f p x σ k).dec = fun j => (ftaylorSeries ℝ f (x k)).taylorDecrement j :=
  rfl

/-- The model of `Optimization.arqpData` is the regularized Taylor model $m_k$ of $f$ at $x_k$ with
weight $\sigma_k$. -/
@[simp] theorem arqpData_model (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    (arqpData f p x σ k).model = regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) :=
  rfl

/-- The Step-2 decrements of `Optimization.arqpData` at a trial step $t$ are the Taylor decrements
of the model $m_k$ at $t$. -/
@[simp] theorem arqpData_modelDec (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    (arqpData f p x σ k).modelDec = fun j t =>
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) t).taylorDecrement j :=
  rfl

/-- The predicted decrease of `Optimization.arqpData` is $\Delta T_{f,p}(x_k, \cdot)$. -/
@[simp] theorem arqpData_pred (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    (arqpData f p x σ k).pred = (ftaylorSeries ℝ f (x k)).taylorDecrement p :=
  rfl

/-- The ratio of exact ARqp is $\rho_k = (f(x_k) - f(x_k + s_k)) / \Delta T_{f,p}(x_k, s_k)$. -/
theorem arqpRho_eq (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    arqpRho f p x s σ k = (f (x k) - f (x k + s k)) /
      (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
  rfl

/-- The **radius constant** $$\kappa_\delta(\sigma) = \frac{\varsigma \theta}{8 (3 L_f + \sigma)}$$
of Lemma 12.2.9 of [cartis2022evaluation], (12.2.45). The lower bound (12.2.51) on the radii
uses $\kappa_{\delta, \min} = \kappa_\delta(\sigma_{\max})$.

The argument `Lf` is the jet bound $L_f$; the analysis uses $L_f = \max(1, L_1, \dots, L_p)$. -/
noncomputable def arqpKappaDelta (P : ARqpParams) (Lf σ : ℝ) : ℝ :=
  P.ς * P.θ / (8 * (3 * Lf + σ))

/-- $\kappa_\delta(\sigma) = \varsigma \theta / (8 (3 L_f + \sigma))$. -/
theorem arqpKappaDelta_def (P : ARqpParams) (Lf σ : ℝ) :
    arqpKappaDelta P Lf σ = P.ς * P.θ / (8 * (3 * Lf + σ)) := rfl

/-- If $L_f \ge 0$ and $\sigma > 0$, then $\kappa_\delta(\sigma) > 0$. -/
theorem arqpKappaDelta_pos (P : ARqpParams) {Lf σ : ℝ} (hL : 0 ≤ Lf) (hσ : 0 < σ) :
    0 < arqpKappaDelta P Lf σ := by
  have := P.ς_pos; have := P.θ_pos
  unfold arqpKappaDelta; positivity

/-- If $L_f \ge 1$ and $\sigma \ge 0$, then $\kappa_\delta(\sigma) < 1$. -/
theorem arqpKappaDelta_lt_one (P : ARqpParams) {Lf σ : ℝ} (hL : 1 ≤ Lf) (hσ : 0 ≤ σ) :
    arqpKappaDelta P Lf σ < 1 := by
  have := P.ς_pos; have := P.θ_pos; have := P.ς_le_one; have := P.θ_lt_one
  unfold arqpKappaDelta
  rw [div_lt_one (by positivity)]
  nlinarith

/-- If $L_f \ge 1$ and $0 \le \sigma \le \sigma'$, then $\kappa_\delta(\sigma') \le
\kappa_\delta(\sigma)$. In particular $\kappa_{\delta, \min} = \kappa_\delta(\sigma_{\max}) \le
\kappa_\delta(\sigma_k)$ when $\sigma_k \le \sigma_{\max}$. -/
theorem arqpKappaDelta_anti (P : ARqpParams) {Lf σ σ' : ℝ} (hL : 1 ≤ Lf) (hσ : 0 ≤ σ)
    (hσσ' : σ ≤ σ') : arqpKappaDelta P Lf σ' ≤ arqpKappaDelta P Lf σ := by
  have := P.ς_pos; have := P.θ_pos
  have : 0 < 3 * Lf + σ := by linarith
  unfold arqpKappaDelta
  gcongr

/-- The constant $$\tau_j = \frac{\varsigma - \theta}{j! \, (L_p + \sigma_{\max})}$$ of Lemma
12.2.12 of [cartis2022evaluation], (12.2.58), where $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p
/ (1 - \eta_2))$. -/
noncomputable def arqpTau (P : ARqpParams) (L : ℕ → ℝ) (p j : ℕ) : ℝ :=
  (P.ς - P.θ) / (j ! * (L p + arSigmaMax P.toARParams (L p)))

/-- The radius constant $\hat\kappa = \min(\kappa_\delta(\sigma_{\max}), \tau_q / 2)$ of the
step-length bound when the radii satisfy the lower bound (12.2.51). Here $\kappa_\delta$ is
computed with $L_f = \max(1, L_1, \dots, L_p)$, and $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p
/ (1 - \eta_2))$. -/
noncomputable def arqpKappaHat (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  min (arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p))) (arqpTau P L p q / 2)

section Constants

variable (P : ARqpParams) (L : ℕ → ℝ)

/-- If $\theta < \varsigma$ and $L_p \ge 0$, then $\tau_j > 0$. -/
theorem arqpTau_pos (hθς : P.θ < P.ς) (hL : 0 ≤ L p) (j : ℕ) : 0 < arqpTau P L p j := by
  have := arSigmaMax_pos P.toARParams (L p)
  unfold arqpTau
  have : 0 < P.ς - P.θ := sub_pos.2 hθς
  positivity

/-- If $L_p \ge 1$, then $\tau_j \le 1$. -/
theorem arqpTau_le_one (hL : 1 ≤ L p) (j : ℕ) : arqpTau P L p j ≤ 1 := by
  have := arSigmaMax_pos P.toARParams (L p)
  have hj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 j.factorial_ne_zero
  have h1 : 1 ≤ (j ! : ℝ) * (L p + arSigmaMax P.toARParams (L p)) := by nlinarith
  unfold arqpTau
  rw [div_le_one (by linarith)]
  have := P.θ_pos; have := P.ς_le_one
  linarith

/-- If $\theta < \varsigma$, $L_p \ge 0$ and $j \le q$, then $\tau_q \le \tau_j$. -/
theorem arqpTau_anti (hθς : P.θ < P.ς) (hL : 0 ≤ L p) {j q : ℕ} (hjq : j ≤ q) :
    arqpTau P L p q ≤ arqpTau P L p j := by
  have := arSigmaMax_pos P.toARParams (L p)
  have : 0 < P.ς - P.θ := sub_pos.2 hθς
  unfold arqpTau
  apply div_le_div_of_nonneg_left this.le (by positivity)
  gcongr

/-- If $\theta < \varsigma$ and $L_p \ge 1$, then $\hat\kappa > 0$. -/
theorem arqpKappaHat_pos (hθς : P.θ < P.ς) (hL : 1 ≤ L p) (q : ℕ) :
    0 < arqpKappaHat P L p q :=
  lt_min (arqpKappaDelta_pos P (zero_le_one.trans le_finMax_left) (arSigmaMax_pos _ _))
    (half_pos (arqpTau_pos P L hθς (zero_le_one.trans hL) q))

/-- $\hat\kappa \le 1$. -/
theorem arqpKappaHat_le_one (q : ℕ) : arqpKappaHat P L p q ≤ 1 :=
  (min_le_left _ _).trans (arqpKappaDelta_lt_one P le_finMax_left
    (arSigmaMax_pos _ _).le).le

end Constants

/-- The **exponents** $\pi_j$ of Lemma 12.2.13 of [cartis2022evaluation] in the radii mode $u$.
If $u$ holds (unit radii), then $\pi_j = (p+1)/(p-j+1)$. If $u$ fails (the lower bound (12.2.51)
at every order), then $\pi_j = j(p+1)/p$.

The number $p - j + 1$ is a natural number with truncated subtraction, so it is $1$ for $j > p$.
For $p = 0$ the second case is $0$, by the Lean convention for division. -/
noncomputable def arqpPiOf (u : Prop) [Decidable u] (p j : ℕ) : ℝ :=
  if u then ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) * (p + 1) / p

/-- The **decrease constant** $\kappa_{\Delta m}$ of Lemma 12.2.13 of [cartis2022evaluation] in the
radii mode $u$. If $u$ holds, then
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!} \left(\frac{\tau_q}{2}\right)^{(p+1)/(p-q+1)}.$$
If $u$ fails, then
$$\kappa_{\Delta m} = \frac{\sigma_{\min}}{(p+1)!}
  \left(\frac{\tau_q}{2} \hat\kappa^{q-1}\right)^{q(p+1)/p}.$$

The number $p - q + 1$ is a natural number with truncated subtraction. -/
noncomputable def arqpKappaDmOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  if u then
    P.σmin / ((p + 1)! : ℝ) * (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ))
  else
    P.σmin / ((p + 1)! : ℝ) * (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^
      ((q : ℝ) * (p + 1) / p)

/-- If $u$ holds, then $\pi_j = (p+1)/(p-j+1)$. -/
theorem arqpPiOf_of_pos {u : Prop} [Decidable u] (hu : u) (p j : ℕ) :
    arqpPiOf u p j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) := by
  rw [arqpPiOf, ite_eq_left hu]

/-- If $u$ fails, then $\pi_j = j(p+1)/p$. -/
theorem arqpPiOf_of_neg {u : Prop} [Decidable u] (hu : ¬ u) (p j : ℕ) :
    arqpPiOf u p j = (j : ℝ) * (p + 1) / p := by
  rw [arqpPiOf, ite_eq_right hu]

/-- If $p \ge 1$, then $\pi_1 = (p+1)/p$ in both radii modes. -/
theorem arqpPiOf_one (u : Prop) [Decidable u] {p : ℕ} (hp : 1 ≤ p) :
    arqpPiOf u p 1 = ((p : ℝ) + 1) / p := by
  by_cases hu : u
  · rw [arqpPiOf_of_pos hu, Nat.sub_add_cancel hp]; push_cast; ring
  · rw [arqpPiOf_of_neg hu]; ring

/-- If $p \ge 2$, then the exponent of order $1$ satisfies $\pi_1 = (p+1)/p \le 3/2$, in both radii
modes. This is the exponent of order $1$ in the ARqp-SC row of (14.2.12) of
[cartis2022evaluation]. -/
theorem arqpPiOf_one_le (unit : Prop) [Decidable unit] {p : ℕ} (hp : 2 ≤ p) :
    arqpPiOf unit p 1 ≤ 3 / 2 := by
  rw [arqpPiOf_one unit (by omega)]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- If $1 \le p \le 3$, then the exponent of order $1$ satisfies $\pi_1 = (p+1)/p \ge 4/3$, in both
radii modes. Together with `Optimization.arqpPiOf_one_le`, $\pi_1 \in [4/3, 3/2]$ for
$p \in \{2, 3\}$; this is the exponent of order $1$ in the ARqp-SC row of (14.2.12) of
[cartis2022evaluation]. -/
theorem four_thirds_le_arqpPiOf_one (unit : Prop) [Decidable unit] {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 3) : 4 / 3 ≤ arqpPiOf unit p 1 := by
  rw [arqpPiOf_one unit hp1]
  have h3 : (p : ℝ) ≤ 3 := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- If $p \ge 1$ and $j \in [1, q]$, then the exponents of the lower-bound radii mode satisfy
$1 < j(p+1)/p \le q(p+1)/p$. -/
theorem arqpPiOf_false_mem {p q j : ℕ} (hp : 1 ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < arqpPiOf False p j ∧ arqpPiOf False p j ≤ arqpPiOf False p q := by
  rw [arqpPiOf_of_neg not_false, arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hjq : (j : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  refine ⟨by rw [lt_div_iff₀ hp0]; nlinarith, by gcongr⟩

/-- If $p \ge 1$, then the exponent of order $p$ of the lower-bound radii mode is
$p(p+1)/p = p + 1$. -/
theorem arqpPiOf_false_self {p : ℕ} (hp : 1 ≤ p) : arqpPiOf False p p = (p : ℝ) + 1 := by
  rw [arqpPiOf_of_neg not_false]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by omega))

/-- If $q \le p$ and $j \in [1, q]$, then the unit-radius exponents satisfy
$1 < (p+1)/(p-j+1) \le (p+1)/(p-q+1)$. -/
theorem arqpPiOf_true_mem_Icc {p q j : ℕ} (hqp : q ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < arqpPiOf True p j ∧ arqpPiOf True p j ≤ arqpPiOf True p q := by
  rw [arqpPiOf_of_pos trivial, arqpPiOf_of_pos trivial]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have h0 : (0 : ℝ) < ((p - j + 1 : ℕ) : ℝ) := by positivity
  have h0' : (0 : ℝ) < ((p - q + 1 : ℕ) : ℝ) := by positivity
  have h1 : ((p - j + 1 : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : ((p - q + 1 : ℕ) : ℝ) ≤ ((p - j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  exact ⟨(one_lt_div h0).2 h1, div_le_div_of_nonneg_left (by positivity) h0' h2⟩

/-- If $p = q \le 2$ and $j \in [1, q]$, then the unit-radius exponent $(p+1)/(p-j+1)$ equals the
exponent $j(p+1)/p$ of the lower-bound radii mode. -/
theorem arqpPiOf_true_eq_false {q j : ℕ} (hq2 : q ≤ 2) (hj : j ∈ Finset.Icc 1 q) :
    arqpPiOf True q j = arqpPiOf False q j := by
  rw [arqpPiOf_of_pos trivial, arqpPiOf_of_neg not_false]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  interval_cases q <;> interval_cases j <;> norm_num

/-- $\min(1, \min_{j \in [1, q]} \varepsilon_j^{j+1})$ is the same with the natural powers
$\varepsilon_j^{j+1}$ and with the real powers $\varepsilon_j^{(j : \mathbb{R}) + 1}$. -/
theorem finMin_pow_succ_eq_rpow (ε : ℕ → ℝ) (q : ℕ) :
    finMin 1 (fun j => ε j ^ (j + 1)) q = finMin 1 (fun j => ε j ^ ((j : ℝ) + 1)) q := by
  congr 1
  funext j
  rw [← Real.rpow_natCast]
  push_cast
  rfl

/-- The exponents $\pi_j$ are nonnegative. -/
theorem arqpPiOf_nonneg (u : Prop) [Decidable u] (p j : ℕ) : 0 ≤ arqpPiOf u p j := by
  unfold arqpPiOf
  split_ifs <;> positivity

/-- If $u$ holds, then $\kappa_{\Delta m} = \sigma_{\min} / (p+1)! \cdot (\tau_q /
2)^{(p+1)/(p-q+1)}$. -/
theorem arqpKappaDmOf_of_pos {u : Prop} [Decidable u] (hu : u) (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) := by
  rw [arqpKappaDmOf, ite_eq_left hu]

/-- If $u$ fails, then $\kappa_{\Delta m} = \sigma_{\min} / (p+1)! \cdot (\tau_q \hat\kappa^{q-1} /
2)^{q(p+1)/p}$. -/
theorem arqpKappaDmOf_of_neg {u : Prop} [Decidable u] (hu : ¬ u) (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^ ((q : ℝ) * (p + 1) / p) := by
  rw [arqpKappaDmOf, ite_eq_right hu]

/-- If $\theta < \varsigma$ and $L_p \ge 1$, then $\kappa_{\Delta m} \ge 0$ in both radii modes. -/
theorem arqpKappaDmOf_nonneg {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 ≤ arqpKappaDmOf u P L p q := by
  have := P.σmin_nonneg
  have hτ := arqpTau_pos P L hθς (zero_le_one.trans hL) q
  have hκ := arqpKappaHat_pos P L hθς hL q
  unfold arqpKappaDmOf
  split_ifs <;> positivity

/-- The constant $$\kappa_{\mathrm{uns}} = 1 + \frac{|\log \gamma_1|}{\log \gamma_2}$$ of Lemmas
2.4.1 and 14.2.3 of [cartis2022evaluation]. The number of iterations of an
adaptive-regularization run is at most $\kappa_{\mathrm{uns}}$ times the number of successful
iterations, plus a term in $\log(\sigma_{\max} / \sigma_0)$. -/
noncomputable def arqpKappaUns (P : ARqpParams) : ℝ :=
  1 + |Real.log P.γ₁| / Real.log P.γ₂

/-- $\kappa_{\mathrm{uns}} = 1 + |\log \gamma_1| / \log \gamma_2$. -/
theorem arqpKappaUns_eq (P : ARqpParams) :
    arqpKappaUns P = 1 + |Real.log P.γ₁| / Real.log P.γ₂ := rfl

/-- $\kappa_{\mathrm{uns}} \ge 1$. -/
theorem one_le_arqpKappaUns {P : ARqpParams} : 1 ≤ arqpKappaUns P := by
  rw [arqpKappaUns_eq]
  have := P.log_γ₂_pos
  have : 0 ≤ |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
  linarith

/-- $\kappa_{\mathrm{uns}} \ge 0$. -/
theorem arqpKappaUns_nonneg {P : ARqpParams} : 0 ≤ arqpKappaUns P :=
  zero_le_one.trans one_le_arqpKappaUns

/-- The constant $$\kappa^s = \frac{1}{\eta_1 \kappa_{\Delta m}}$$ of Theorem 12.2.14 of
[cartis2022evaluation] in the radii mode $u$, where $\kappa_{\Delta m}$ is
`Optimization.arqpKappaDmOf` for $u$.

The constant of the source is the mode $u = (q \le 2)$, which is
`CartisGouldToint.Chapter12.kappaSARqp`. -/
noncomputable def kappaSARqpOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  1 / (P.η₁ * arqpKappaDmOf u P L p q)

/-- The constant $\kappa^a = \kappa^s \kappa_{\mathrm{uns}}$ of Theorem 12.2.14 of
[cartis2022evaluation] in the radii mode $u$.

The constant of the source is the mode $u = (q \le 2)$, which is
`CartisGouldToint.Chapter12.kappaAARqp`. -/
noncomputable def kappaAARqpOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  kappaSARqpOf u P L p q * arqpKappaUns P

/-- The constant $$\kappa^c = \frac{|\log \gamma_1| + \log(\sigma_{\max} / \sigma_0)}{\log
\gamma_2} + 2$$ of Theorem 12.2.14 of [cartis2022evaluation], where $\sigma_{\max} =
\max(\sigma_0, \gamma_3 L_p / (1 - \eta_2))$. -/
noncomputable def kappaCARqp (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀)) / Real.log P.γ₂ + 2

/-- $\kappa^s = 1 / (\eta_1 \kappa_{\Delta m})$. -/
theorem kappaSARqpOf_def (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) :
    kappaSARqpOf u P L p q = 1 / (P.η₁ * arqpKappaDmOf u P L p q) := rfl

/-- $\kappa^a = \kappa^s \kappa_{\mathrm{uns}}$. -/
theorem kappaAARqpOf_def (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) :
    kappaAARqpOf u P L p q = kappaSARqpOf u P L p q * arqpKappaUns P := rfl

/-- $\kappa^c = (|\log \gamma_1| + \log(\sigma_{\max} / \sigma_0)) / \log \gamma_2 + 2$. -/
theorem kappaCARqp_def (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) :
    kappaCARqp P L p =
      (|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀)) / Real.log P.γ₂ + 2 :=
  rfl

/-- Jet bounds from anchored Lipschitz derivatives of all orders. If the derivatives $\nabla^j f$ of
the orders $j \in [1, p]$ are $L_j$-Lipschitz anchored at the points of $A$ with respect to $C$,
and $L_j \ge 0$ for $j \in [1, p]$, then $\|\nabla^j f(x)\| \le \max(1, L_1, \dots, L_p)$ for
all $j \in [2, p]$ and $x \in A$. -/
theorem _root_.LipschitzDerivsAnchored.norm_iteratedFDeriv_le_finMax {f : E → ℝ} {C A : Set E}
    {p : ℕ} {L : ℕ → ℝ} (h : LipschitzDerivsAnchored f C A 1 p L)
    (hL : ∀ j ∈ Finset.Icc 1 p, 0 ≤ L j) :
    ∀ j ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p := by
  intro j hj x hx
  have hj' : j - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2
    ⟨by have := (Finset.mem_Icc.1 hj).1; omega, by have := (Finset.mem_Icc.1 hj).2; omega⟩
  have := h.norm_iteratedFDeriv_le hj' (hL _ hj') hx
  rw [Nat.sub_add_cancel (by have := (Finset.mem_Icc.1 hj).1; omega)] at this
  exact this.trans (le_finMax hj')

/-- $\kappa^c \ge 0$. -/
theorem kappaCARqp_nonneg (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) : 0 ≤ kappaCARqp P L p := by
  rw [kappaCARqp_def]
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (σ₀_le_arSigmaMax _ _))
  positivity

/-- If $\sigma_{\min} > 0$, $\theta < \varsigma$ and $L_p \ge 1$, then $\kappa_{\Delta m} > 0$ in
both radii modes. -/
theorem arqpKappaDmOf_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < arqpKappaDmOf u P L p q := by
  have hτ := arqpTau_pos P L hθς (zero_le_one.trans hL) q
  have hκ := arqpKappaHat_pos P L hθς hL q
  unfold arqpKappaDmOf
  split_ifs <;> positivity

/-- If $\sigma_{\min} > 0$, $\theta < \varsigma$ and $L_p \ge 1$, then $\kappa^s > 0$ in both radii
modes. -/
theorem kappaSARqpOf_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < kappaSARqpOf u P L p q := by
  have := arqpKappaDmOf_pos (q := q) u hσmin hθς hL
  have := P.η₁_pos
  unfold kappaSARqpOf; positivity

variable {f : E → ℝ} {L : ℕ → ℝ} {P : ARqpParams} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E}
  {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {X C A : Set E}

/-- Let iteration $k$ of an ARqp run with exact data be reached, not terminate, and be successful
($\rho_k \ge \eta_1$). Then $x_{k+1} = x_k + s_k$ and $\delta_{k+1} = \delta_{s_k}$. -/
theorem IsARqpRun.succ_eq (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    x (k + 1) = x k + s k ∧ δ (k + 1) = δs k :=
  ⟨h.toIsARRun.eq_add_of_succ hk hs, (h.radii k hk).1 hs⟩

/-- Let iteration $k$ of an ARqp run with exact data be reached and not terminate. Then $s_k \neq 0$
and $$\frac{\sigma_k}{(p+1)!} \|s_k\|^{p+1} < \Delta T_{f,p}(x_k, s_k).$$ This is Lemma 4.1.1 of
[cartis2022evaluation] for ARqp. -/
theorem IsARqpRun.taylorDecrement_gt (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    s k ≠ 0 ∧ σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
      (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
  have hm := h.model_lt hk
  exact ⟨ne_zero_of_regularizedModel_lt hm, lt_taylorDecrement_of_regularizedModel_lt hm⟩

/-- Let iteration $k$ of an ARqp run with exact data be reached and not terminate. Then
$f(x_{k+1}) \le f(x_k)$. -/
theorem IsARqpRun.objective_le
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) : f (x (k + 1)) ≤ f (x k) := by
  have hσ := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
  have hdec := (IsARqpRun.taylorDecrement_gt h hk).2
  exact (h.toIsARRun.accept k hk).le (w := f) rfl (lt_of_le_of_lt (by positivity) hdec)

/-- The **iterates stay in the sublevel set**. For an ARqp run with exact data on $X$, every
iteration $k$ that is reached satisfies $x_k \in X$ and $f(x_k) \le f(x_0)$. -/
theorem IsARqpRun.mem_sublevel (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → x k ∈ X ∧ f (x k) ≤ f (x 0) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨h.mem_zero, le_rfl⟩
  | succ k ih =>
    intro hk
    exact ⟨h.mem (k + 1) hk,
      (IsARqpRun.objective_le h fun i hi => hk i (Nat.lt_succ_of_le hi)).trans
      (ih fun i hi => hk i (Nat.lt_succ_of_lt hi)).2⟩

/-- **The regularization weights stay bounded** ([cartis2022evaluation], Lemma 4.1.2 for ARqp,
(4.1.19)). Let $X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of
$A$ with respect to $C$, and let $A$ contain $\{y \in X : f(y) \le f(x_0)\}$. Then every
iteration $k$ that is reached by an ARqp run with exact data on $X$ satisfies $$\sigma_{\min}
\le \sigma_k \le \sigma_{\max} = \max\left(\sigma_0, \frac{\gamma_3 L_p}{1 - \eta_2}\right).$$

The bound includes the termination index. -/
theorem IsARqpRun.sigma_le_of_anchored (hf : LipschitzDerivsAnchored f C A p p L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams (L p) := by
  intro k hk
  have := IsARRun.sigma_le_anchored (f := f) (p := p) (x := x) (s := s) h.toIsARRun (C := C)
    hf.convex hf.contDiffAt (fun k hk => by
      obtain ⟨hxk, hfk⟩ := IsARqpRun.mem_sublevel h k fun i hi => hk i hi.le
      exact hf.lipschitzAt (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩) (hA _ hxk hfk))
    (hXC h.mem_zero) (fun k hk hst => ⟨hXC hst.mem, h.model_lt hk⟩) k hk
  exact ⟨this.2.1, this.2.2⟩

/-- **Runs with the radii property (12.2.50)** ([cartis2022evaluation], Lemmas 12.2.9 and 12.2.10).
Let $E$ be finite-dimensional, let $1 \le q \le p$, $\varepsilon \in (0, 1]^q$ and
$\delta_0 \in (0, 1]^q$, and let $\|\nabla^j f(y)\| \le L_f = \max(1, L_1, \dots, L_p)$ for all
$j \in [2, p]$ and all $y$ in a set $A$ that contains $\{y : f(y) \le f(x_0)\}$. Then from $x_0$
there is an unconstrained ARqp run with exact data and initial radii $\delta_0$ such that

* at every iteration $k$ that is reached, the Step-2 radii satisfy $\delta_{s_k, j} = 1$ for
  $j \in [1, q]$ with $j \le 2$ (12.2.44);
* at every iteration $k$ that is reached and does not terminate, $\delta_{s_k, j} \ge
  \kappa_\delta(\sigma_k) \varepsilon_j$ for all $j \in [1, q]$ ((12.2.45), (12.2.50)).

The radii of Lemma 12.2.9 are computed from the jet of $f$ at the iterate, which lies in $A$.
The theorem has no smoothness hypothesis on $f$. The run is the case `X = univ` of
`Optimization.IsARqpRun`. -/
theorem exists_isARqpRun_of_anchored [FiniteDimensional ℝ E]
    (hjet : ∀ j ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p) (P : ARqpParams)
      (hq : 1 ≤ q) (hqp : q ≤ p)
    {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (x₀ : E) (hA : ∀ y, f y ≤ f x₀ → y ∈ A) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun f univ P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm ∧
      (∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
      ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j := by
  classical
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  -- the jet bound `L_f` at the anchors, and any bound elsewhere
  let M : E → ℝ := fun y => if y ∈ A then finMax 1 L p else
    max (finMax 1 L p) (∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖)
  have hM0 : ∀ y, 0 ≤ M y := fun y => by
    simp only [M]
    split_ifs
    · linarith
    · exact le_max_of_le_left (by linarith)
  have hM : ∀ y, ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ M y := fun y i hi => by
    simp only [M]
    split_ifs with hy
    · exact hjet _ hi _ hy
    · exact le_max_of_le_right (Finset.single_le_sum
        (f := fun i => ‖iteratedFDeriv ℝ i f y‖) (fun _ _ => norm_nonneg _) hi)
  obtain ⟨x, s, σ, δ, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hqp
    (fun j hj => (hε j hj).1) hδ₀ M hM0 hM x₀
  refine ⟨x, s, σ, δ, δs, d, dm, h0, h, fun k hk => (hrad k hk).1, fun k hk j hj => ?_⟩
  have hk' : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i hi.le
  have hσ : 0 < σ k := h.toIsARRun.sigma_pos hk' k le_rfl
  have hxA : x k ∈ A := by
    have := (IsARqpRun.mem_sublevel (X := univ) h k hk').2
    rw [h0] at this
    exact hA _ this
  have hMk : M (x k) = finMax 1 L p := ite_eq_left hxA
  obtain ⟨hεj, hεj1⟩ := hε j hj
  have hκ1 := (arqpKappaDelta_lt_one P hL1 hσ.le).le
  by_cases hj2 : j ≤ 2
  · rw [(hrad k hk').1 j hj hj2]
    calc arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ 1 * 1 :=
          mul_le_mul hκ1 hεj1 hεj.le zero_le_one
      _ = 1 := one_mul 1
  · rw [(hrad k hk').2 j (Finset.mem_Icc.2 ⟨by omega, (Finset.mem_Icc.1 hj).2⟩), hMk]
    have hK : 0 < 3 * finMax 1 L p + σ k := by linarith
    have := P.ς_pos; have := P.θ_pos
    refine le_min ?_ ?_
    · calc arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ 1 * 1 :=
            mul_le_mul hκ1 hεj1 hεj.le zero_le_one
        _ = 1 := one_mul 1
    · rw [arqpKappaDelta]
      calc P.ς * P.θ / (8 * (3 * finMax 1 L p + σ k)) * ε j =
          P.ς * P.θ * ε j / (8 * (3 * finMax 1 L p + σ k)) := by ring
        _ ≤ P.ς * P.θ * ε j / (4 * (3 * finMax 1 L p + σ k)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **The radius inequality for one iteration** ([cartis2022evaluation], Lemma 12.2.11, local form).
Let $X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with
respect to $C$, with $L_p \ge 1$, and let $1 \le q \le p$ and $y \in A$. Let
$0 \le \sigma_k \le \sigma_{\max}$, and let the step $t$ with radii $\delta_k$ satisfy the
Step-2 conditions of ARqp for the exact data at $y$ with weight $\sigma_k$. Assume that the step
is short, $\|t\| < 1$, so that (12.2.29) holds. Let $d'_j$ be $\varsigma$-approximate optimality
displacements of $\Delta T_{f,j}(y + t, \cdot)$ with radii $\delta_{k,j}$ over
$\{e : y + t + e \in X\}$, and assume that the Step-1 test at $y + t$ fails for them. Then for
some $j \in [1, q]$ the inequality (12.2.52) holds: $$\frac{(\varsigma - \theta) \varepsilon_j
\delta_{k,j}^j}{j!} < (L_p + \sigma_{\max}) \sum_{\ell = 1}^j \frac{\delta_{k,j}^\ell}{\ell!}
\|t\|^{p - \ell + 1}.$$

The Step-2 conditions are `Optimization.ARqpStep` for
`ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk`, and the failed Step-1 test is the negation of
`Optimization.MeasureTestPasses`. -/
theorem ARqpStep.exists_radius_ineq (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) {y t : E} (hy : y ∈ A)
    {σk : ℝ} (hσ0 : 0 ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ}
    {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hshort : ‖t‖ < 1) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d') :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δk j ^ j / j ! <
      (L p + arSigmaMax P.toARParams (L p)) *
        ∑ ℓ ∈ Finset.Icc 1 j, δk j ^ ℓ / ℓ ! * ‖t‖ ^ (p - ℓ + 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses hfail
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
  have hδ0 : 0 ≤ δk j := (norm_nonneg _).trans (hw j hj).norm_le
  have h₁ : P.ς * ε j * δk j ^ j / (j ! : ℝ) - 0 <
      taylorMeasure (ftaylorSeries ℝ f (y + t)) j (δk j) {e | y + t + e ∈ X} := by
    rw [sub_zero]
    exact hlt.trans_le (taylorDecrement_le_taylorMeasure _ j (hw j hj).1)
  obtain ⟨hdm, hsmall⟩ := (hstep.branch.resolve_left (not_le.2 hshort)) j hj
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f y) p σk) t) j
      (δk j) {e | y + t + e ∈ X} ≤ P.θ * ε j * δk j ^ j / j ! := by
    have h2 := hdm.2.trans hsmall
    have : P.ς * P.θ * ε j * δk j ^ j / j ! = P.ς * (P.θ * ε j * δk j ^ j / j !) := by ring
    rw [this] at h2
    exact le_of_mul_le_mul_left h2 P.ς_pos
  have hS0 : (0 : E) ∈ {e | y + t + e ∈ X} := by
    change y + t + 0 ∈ X; rw [add_zero]; exact hstep.mem
  have := radius_inequality_of_measure_gt_anchored hf.convex hf.contDiffAt
    (hf.lipschitzAt (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩) hy) (zero_le_one.trans hL) (hf.subset hy)
      (hXC hstep.mem)
    (jetApprox_self (ftaylorSeries ℝ f y) p) le_rfl le_rfl
    (fun i _ => by simp) hσ0 hσmax hjp hS0 hδ0 h₁ h₂
  refine ⟨j, hj, this.trans_eq ?_⟩
  ring

/-- Let iteration $k$ of an ARqp run with exact data on $X$ be reached, not terminate, and be
successful. Then for every $j \in [1, q]$ the Step-1 witness $d_{k+1, j}$ is a
$\varsigma$-approximate optimality displacement of $\Delta T_{f,j}(x_k + s_k, \cdot)$ with
radius $\delta_{s_k, j}$ over $\{e : x_k + s_k + e \in X\}$. -/
theorem IsARqpRun.next_witness
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) (δs k j) {e | x k + s k + e ∈ X} P.ς
        (d (k + 1) j) := by
  obtain ⟨hx1, hδ1⟩ := IsARqpRun.succ_eq h hk hs
  intro j hj
  have hw := h.witness (k + 1) (fun i hi => hk i (by omega)) j hj
  change IsApproxMeasureStep ((ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j) (δ (k + 1) j)
    {e | x (k + 1) + e ∈ X} P.ς (d (k + 1) j) at hw
  rwa [hx1, hδ1] at hw

/-- Let iteration $k$ of an ARqp run with exact data be reached, not terminate, and be successful,
and let the Step-1 test fail at $k + 1$. Then the Step-1 test at $x_k + s_k$ with the radii
$\delta_{s_k}$ and the witnesses $d_{k+1}$ fails. -/
theorem IsARqpRun.next_not_measureTestPasses
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) q P.ς ε
      (δs k) (d (k + 1)) := by
  obtain ⟨hx1, hδ1⟩ := IsARqpRun.succ_eq h hk hs
  change ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j) q P.ς
    ε (δ (k + 1)) (d (k + 1)) at hk1
  rwa [hx1, hδ1] at hk1

/-- **The step is long** ([cartis2022evaluation], Lemma 12.2.12, local form; this is the common core
of Lemmas 12.2.12 and 12.2.13). Let $X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz
anchored at the points of $A$ with respect to $C$, with $L_p \ge 1$, let $1 \le q \le p$,
$\theta < \varsigma$, $\varepsilon \in (0, 1]^q$ and $y \in A$, and let
$0 \le \sigma_k \le \sigma_{\max}$. Let the step $t$ with radii $\delta_k$ satisfy the Step-2
conditions of ARqp for the exact data at $y$ with weight $\sigma_k$, and let it decrease the
model: $m(t) < m(0)$ for the model $m(e) = T_{f,p}(y, e) + \sigma_k \|e\|^{p+1} / (p+1)!$. Let
$d'_j$ be $\varsigma$-approximate optimality displacements of $\Delta T_{f,j}(y + t, \cdot)$
with radii $\delta_{k,j}$ over $\{e : y + t + e \in X\}$ for which the Step-1 test at $y + t$
fails. Let the radii be in the radii mode $u$: if $u$, then $\delta_{k,j} = 1$ for all
$j \in [1, q]$; if not $u$, then $\|t\| \ge 1$ or $\delta_{k,j} \ge \kappa_\delta(\sigma_{\max})
\varepsilon_j$ for all $j \in [1, q]$. Then for some $j \in [1, q]$

* if $u$, then $\tau_j \varepsilon_j / 2 \le \|t\|^{p - j + 1}$;
* if not $u$, then $(\tau_j / 2) \hat\kappa^{j-1} \varepsilon_j^j \le \|t\|^p$.

Here $\kappa_\delta$ is computed with $L_f = \max(1, L_1, \dots, L_p)$. -/
theorem ARqpStep.exists_norm_pow_ge (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {y t : E}
    (hy : y ∈ A) {σk : ℝ}
    (hσ0 : 0 ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ} {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hlt : regularizedModel (ftaylorSeries ℝ f y) p σk t <
      regularizedModel (ftaylorSeries ℝ f y) p σk 0) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d')
    {u : Prop} (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δk j = 1) ∧
      (¬ u → 1 ≤ ‖t‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δk j)) :
    ∃ j ∈ Finset.Icc 1 q,
      (u → arqpTau P L p j * ε j / 2 ≤ ‖t‖ ^ (p - j + 1)) ∧
      (¬ u → arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j ≤ ‖t‖ ^ p) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  have ht : 0 < ‖t‖ := norm_pos_iff.2 (ne_zero_of_regularizedModel_lt hlt)
  set A := L p + arSigmaMax P.toARParams (L p) with hA_def
  have hA : 0 < A := by have := arSigmaMax_pos P.toARParams (L p); linarith
  have hκ := arqpKappaHat_pos P L hθς hLp q
  have hκ1 := arqpKappaHat_le_one P L (p := p) q
  -- the trivial long-step case
  by_cases hlong : 1 ≤ ‖t‖
  · have h1 : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    obtain ⟨hε0, hε1⟩ := hε 1 h1
    have hτ1 := arqpTau_le_one P L hLp 1
    have hτ0 := (arqpTau_pos P L hθς (zero_le_one.trans hLp) 1).le
    refine ⟨1, h1, fun _ => ?_, fun _ => ?_⟩
    · calc arqpTau P L p 1 * ε 1 / 2 ≤ 1 * 1 / 2 := by gcongr
        _ ≤ 1 := by norm_num
        _ ≤ ‖t‖ ^ (p - 1 + 1) := one_le_pow₀ hlong
    · calc arqpTau P L p 1 / 2 * arqpKappaHat P L p q ^ (1 - 1) * ε 1 ^ 1 ≤ 1 / 2 * 1 * 1 := by
            rw [Nat.sub_self, pow_zero, pow_one]; gcongr
        _ ≤ 1 := by norm_num
        _ ≤ ‖t‖ ^ p := one_le_pow₀ hlong
  have hshort : ‖t‖ < 1 := not_le.1 hlong
  obtain ⟨j, hj, hineq⟩ := ARqpStep.exists_radius_ineq hf hL hXC hq hqp hy hσ0
    hσmax hstep hshort hw
    hfail
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  obtain ⟨hε0, hε1⟩ := hε j hj
  have hMI : MeasureIneq A 0 (P.ς - P.θ) (ε j) (δk j) ‖t‖ j p := by
    rw [measureIneq_iff, zero_mul, add_zero]; exact hineq.le
  have ha : 0 < P.ς - P.θ := sub_pos.2 hθς
  have hfac : (0 : ℝ) < j ! := by exact_mod_cast j.factorial_pos
  have hτ : arqpTau P L p j = (P.ς - P.θ) / (A * j !) := by
    rw [arqpTau, hA_def, mul_comm]
  refine ⟨j, hj, fun hq2 => ?_, fun hq2 => ?_⟩
  · -- `δ_{k+1,j} = 1 ≥ ‖s_k‖`
    have hδ1 : δk j = 1 := hrad.1 hq2 j hj
    have h1 := hMI.div_le_of_le hA.le le_rfl ht (by rw [hδ1]; exact hshort.le) hjp
    rw [hτ]
    have e : (P.ς - P.θ) / (A * j !) * ε j / 2 = (P.ς - P.θ) * ε j / j ! / (2 * A) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  · have hrad' := (hrad.2 hq2).resolve_left hlong j hj
    have hκδ : 0 < arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
      arqpKappaDelta_pos P (zero_le_one.trans le_finMax_left) (arSigmaMax_pos _ _)
    have hδpos : 0 < δk j := lt_of_lt_of_le (by positivity) hrad'
    have h1 := pow_ge_of_measure_ineq hMI hA ha hε0 ht hshort.le hδpos hj1 hjp hκδ hrad'
    rw [← hτ] at h1
    refine le_trans ?_ h1
    have hmin : arqpKappaHat P L p q ≤ min (arqpKappaDelta P (finMax 1 L p)
        (arSigmaMax P.toARParams (L p))) (arqpTau P L p j / 2) :=
      min_le_min le_rfl (by
        have := arqpTau_anti P L hθς (zero_le_one.trans hLp) (Finset.mem_Icc.1 hj).2
        linarith)
    have hτj := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    gcongr

/-- **The model decrease for one iteration** ([cartis2022evaluation], Lemma 12.2.13, local form).
Under the hypotheses of `Optimization.ARqpStep.exists_norm_pow_ge`, with the condition
$0 \le \sigma_k$ replaced by $\sigma_{\min} \le \sigma_k$, $$\Delta T_{f,p}(y, t) \ge
\kappa_{\Delta m} \min_{j \in [1, q]} \varepsilon_j^{\pi_j},$$ where $\kappa_{\Delta m}$ and
$\pi_j$ are `Optimization.arqpKappaDmOf` and `Optimization.arqpPiOf` for the radii mode $u$.

The minimum is `finMin 1 (fun j => ε j ^ arqpPiOf u p j) q`, which is also bounded by $1$. -/
theorem ARqpStep.taylorDecrement_ge (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {y t : E}
    (hy : y ∈ A) {σk : ℝ}
    (hσmin : P.σmin ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ}
    {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hlt : regularizedModel (ftaylorSeries ℝ f y) p σk t <
      regularizedModel (ftaylorSeries ℝ f y) p σk 0) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d')
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δk j = 1) ∧
      (¬ u → 1 ≤ ‖t‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δk j)) :
    arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q ≤
      (ftaylorSeries ℝ f y).taylorDecrement p t := by
  have hσ0 : 0 ≤ σk := P.σmin_nonneg.trans hσmin
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  have hT := lt_taylorDecrement_of_regularizedModel_lt hlt
  have ht : 0 < ‖t‖ := norm_pos_iff.2 (ne_zero_of_regularizedModel_lt hlt)
  set m := finMin 1 (fun j => ε j ^ arqpPiOf u p j) q with hm_def
  have hm0 : 0 < m := finMin_pos one_pos fun j hj => Real.rpow_pos_of_pos (hε j hj).1 _
  have hfacp : (0 : ℝ) < (p + 1)! := by positivity
  have hσmin0 := P.σmin_nonneg
  -- the decrease at the step
  have hlow : P.σmin / ((p + 1)! : ℝ) * ‖t‖ ^ (p + 1) ≤
      (ftaylorSeries ℝ f y).taylorDecrement p t := by
    refine le_trans ?_ hT.le
    gcongr
  have hκq := arqpKappaHat_pos P L hθς hLp q
  have hκq1 := arqpKappaHat_le_one P L (p := p) q
  have hτq := arqpTau_pos P L hθς (zero_le_one.trans hLp) q
  have hτq1 := arqpTau_le_one P L hLp q
  obtain ⟨j, hj, h1, h2⟩ :=
    ARqpStep.exists_norm_pow_ge hf hL hXC hq hqp hθς hε hy hσ0 hσmax hstep hlt
      hw hfail hrad
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ p := hjq.trans hqp
  obtain ⟨hε0, hε1⟩ := hε j hj
  have hτj := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
  have hτqj := arqpTau_anti P L hθς (zero_le_one.trans hLp) hjq
  have hmj : m ≤ ε j ^ arqpPiOf u p j := finMin_le hj
  -- the key bound `B m ≤ ‖s_k‖^{p+1}`, with `κ_{Δm} = σ_min/(p+1)! B`
  have key : ∃ B, arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) * B ∧
      B * m ≤ ‖t‖ ^ (p + 1) := by
    by_cases hq2 : u
    · refine ⟨(arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)),
        arqpKappaDmOf_of_pos hq2 P L p q, ?_⟩
      have hπ : arqpPiOf u p j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) :=
        arqpPiOf_of_pos hq2 p j
      rw [hπ] at hmj
      have hexp : ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) ≤
          ((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast (show p - q + 1 ≤ p - j + 1 by omega)
      have hB : (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) ≤
          (arqpTau P L p j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) hexp).trans
          (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity))
      calc (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) * m
          ≤ (arqpTau P L p j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) *
              ε j ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
            mul_le_mul hB hmj hm0.le (by positivity)
        _ = (arqpTau P L p j * ε j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) := by
            rw [← Real.mul_rpow (by positivity) hε0.le]; ring_nf
        _ ≤ (‖t‖ ^ (p - j + 1)) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (h1 hq2) (by positivity)
        _ = ‖t‖ ^ (p + 1) := by rw [pow_rpow_div (by omega) ht.le, Real.rpow_natCast]
    · have hq2' : ¬ u := hq2
      set bq := arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1) with hbq
      set bj := arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) with hbj
      refine ⟨bq ^ ((q : ℝ) * (p + 1) / p), arqpKappaDmOf_of_neg hq2 P L p q, ?_⟩
      have hπ : arqpPiOf u p j = (j : ℝ) * (p + 1) / p := arqpPiOf_of_neg hq2 p j
      rw [hπ] at hmj
      have hbq0 : 0 < bq := by positivity
      have hbq1 : bq ≤ 1 := by
        have : arqpKappaHat P L p q ^ (q - 1) ≤ 1 := pow_le_one₀ hκq.le hκq1
        calc bq ≤ 1 / 2 * 1 := by rw [hbq]; gcongr
          _ ≤ 1 := by norm_num
      have hbqj : bq ≤ bj := by
        rw [hbq, hbj]
        exact mul_le_mul (by linarith) (pow_le_pow_of_le_one hκq.le hκq1 (by omega))
          (by positivity) (by positivity)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      have hexp : ((p + 1 : ℕ) : ℝ) / (p : ℝ) ≤ (q : ℝ) * (p + 1) / p := by
        push_cast
        apply div_le_div_of_nonneg_right _ hp0.le
        have : (1 : ℝ) ≤ q := by exact_mod_cast hq
        nlinarith
      have hB : bq ^ ((q : ℝ) * (p + 1) / p) ≤ bj ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_ge hbq0 hbq1 hexp).trans
          (Real.rpow_le_rpow hbq0.le hbqj (by positivity))
      have hεe : ε j ^ ((j : ℝ) * (p + 1) / p) = (ε j ^ j) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) := by
        rw [← Real.rpow_natCast (ε j) j, ← Real.rpow_mul hε0.le]
        push_cast
        ring_nf
      calc bq ^ ((q : ℝ) * (p + 1) / p) * m
          ≤ bj ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) * ε j ^ ((j : ℝ) * (p + 1) / p) :=
            mul_le_mul hB hmj hm0.le (by positivity)
        _ = (bj * ε j ^ j) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) := by
            rw [hεe, ← Real.mul_rpow (by positivity) (by positivity)]
        _ ≤ (‖t‖ ^ p) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (h2 hq2') (by positivity)
        _ = ‖t‖ ^ (p + 1) := by rw [pow_rpow_div (by omega) ht.le, Real.rpow_natCast]
  obtain ⟨B, hκ, hBm⟩ := key
  have hdec : arqpKappaDmOf u P L p q * m ≤ (ftaylorSeries ℝ f y).taylorDecrement p t := by
    rw [hκ]
    calc P.σmin / ((p + 1)! : ℝ) * B * m = P.σmin / ((p + 1)! : ℝ) * (B * m) := by ring
      _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖t‖ ^ (p + 1) := by gcongr
      _ ≤ _ := hlow
  exact hdec

/-- **Sufficient decrease of ARqp** ([cartis2022evaluation], Lemmas 12.2.13 and 14.2.2). Let
$X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect
to $C$, with $L_p \ge 1$, and let $A$ contain $\{y \in X : f(y) \le f(x_0)\}$. Let
$1 \le q \le p$, $\theta < \varsigma$ and $\varepsilon \in (0, 1]^q$. Consider an ARqp run with
exact data on $X$, and an iteration $k$ that is reached, does not terminate and is successful,
such that the Step-1 test fails at $k + 1$. Let the radii $\delta_{k+1}$ be in the radii mode
$u$: if $u$, then $\delta_{k+1, j} = 1$ for all $j \in [1, q]$; if not $u$, then $\|s_k\| \ge 1$
or $\delta_{k+1, j} \ge \kappa_\delta(\sigma_{\max}) \varepsilon_j$ for all $j \in [1, q]$. Then
$$\Delta T_{f,p}(x_k, s_k) \ge \kappa_{\Delta m} \min_{j \in [1, q]} \varepsilon_j^{\pi_j}
\quad\text{and}\quad f(x_k) - f(x_{k+1}) \ge \eta_1 \kappa_{\Delta m} \min_{j \in [1, q]}
\varepsilon_j^{\pi_j},$$ with $\kappa_{\Delta m}$ and $\pi_j$ for the radii mode $u$.

The minimum is `finMin 1 (fun j => ε j ^ arqpPiOf u p j) q`. The proof specializes
`Optimization.ARqpStep.taylorDecrement_ge` to $y = x_k$ and $t = s_k$. -/
theorem IsARqpRun.decrease (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hq : 1 ≤ q)
    (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hσ := IsARqpRun.sigma_le_of_anchored hf hXC hA h k fun i hi => hk i hi.le
  obtain ⟨hxk, hfk⟩ := IsARqpRun.mem_sublevel h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(IsARqpRun.succ_eq h hk hs).2] at hrad
  have hdec := ARqpStep.taylorDecrement_ge hf hL hXC hq hqp hθς hε
    (hA _ hxk hfk) hσ.1
    hσ.2 hstep
    (h.model_lt hk)
    (IsARqpRun.next_witness h hk hs) (IsARqpRun.next_not_measureTestPasses h hk hs hk1) hrad
  refine ⟨hdec, ?_⟩
  have hT := (IsARqpRun.taylorDecrement_gt h hk).2
  have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
    have hσ0 := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
    exact lt_of_le_of_lt (by positivity) hT
  have := (h.toIsARRun.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk rfl hpos hs).2
  exact (mul_le_mul_of_nonneg_left hdec P.η₁_pos.le).trans this

/-- **No Step-2 termination for $q \le 2$** ([cartis2022evaluation], Lemma 12.2.10, first part). Let
$q \le 2$, $q \le p$, $\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. If an
unconstrained ARqp run with exact data terminates at $k$ and $f$ is of class $C^p$ at $x_k$,
then the Step-1 test holds at $k$.

If the Step-1 test failed, then $0$ would minimize the model, so the model measures of the
orders $j \le 2$ would vanish at $0$, and this contradicts the failed test. -/
theorem IsARqpRun.arqpStop₁_of_isFirstHit_of_le_two
    (h : IsARqpRun f univ P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hfk : ContDiffAt ℝ p f (x k)) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (hk : IsFirstHit (arqpStop f P p q ε x s σ δ d) k) (hq2 : q ≤ 2) :
    arqpStop₁ P q ε (arqpData f p x σ) δ d k := by
  by_contra h1
  have hstep := h.step hk.2 h1
  have h2 : arqpStop₂ (arqpData f p x σ) s k := hk.1.resolve_left h1
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  have hmin := hstep.isMinOn_of_eq h2
  rw [hU] at hmin
  set m := regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)
  obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses h1
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
  have hw := h.witness k hk.2 j hj
  rw [hU] at hw
  have hδk := h.delta_mem hδ₀ k hk.2 j hj
  have hcd : ContDiffAt ℝ j m 0 :=
    (contDiff_regularizedModel (D := ftaylorSeries ℝ f (x k))).contDiffAt.of_le
      (by exact_mod_cast hjp)
  have hφ := taylorMeasure_eq_zero_of_isLocalMin hcd (hmin.isLocalMin univ_mem)
    (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hq2⟩)
    hδk.1.le
  rw [taylorMeasure_regularizedModel_zero hfk (σ k) hjp] at hφ
  have := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ f (x k)) j hw.1
  rw [hφ] at this
  have := P.ς_pos
  have := (hε j hj).1
  have : 0 ≤ P.ς * ε j * δ k j ^ j / j ! := by have := hδk.1; positivity
  change P.ς * ε j * δ k j ^ j / j ! <
    (ftaylorSeries ℝ f (x k)).taylorDecrement j (d k j) at hlt
  linarith

/-- Let the initial radii of an ARqp run with exact data be $\delta_{0,j} = 1$ for $j \in [1, q]$,
and let the Step-2 radii be $\delta_{s_k, j} = 1$ for $j \in [1, q]$ at every iteration $k$ that
is reached and does not terminate. Then $\delta_{k,j} = 1$ for $j \in [1, q]$ at every iteration
$k$ that is reached. Lemma 12.2.9 of [cartis2022evaluation] allows such radii for $q \le 2$. -/
theorem IsARqpRun.delta_eq_one (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, δ₀ j = 1)
    (hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δ k j = 1 := by
  intro k
  induction k with
  | zero => exact fun _ j hj => by rw [h.delta_zero]; exact hδ₀ j hj
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]; exact hδs k hk' j hj
    · rw [(hu hρ).1]; exact ih (fun i hi => hk' i hi.le) j hj

/-- **The counting argument of Theorem 12.2.14** ([cartis2022evaluation]). Let
$f \ge f_{\mathrm{low}}$ on $X$, let $X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz
anchored at the points of $A$ with respect to $C$, with $L_p \ge 1$, and let $A$ contain
$\{y \in X : f(y) \le f(x_0)\}$. Let $1 \le q \le p$, $\sigma_{\min} > 0$, $\theta < \varsigma$
and $\varepsilon \in (0, 1]^q$. Consider an ARqp run with exact data on $X$ whose radii
$\delta_{k+1}$ are in the radii mode $u$ after every successful iteration $k$ for which the
iterations up to $k + 1$ do not terminate. Then the run terminates at some $k_\varepsilon$, and
with $m_\varepsilon = \min_{j \in [1, q]} \varepsilon_j^{\pi_j}$ it uses at most
$$\frac{\kappa^a (f(x_0) - f_{\mathrm{low}})}{m_\varepsilon} + \kappa^c \text{ evaluations of }
f \quad\text{and}\quad \frac{\kappa^s (f(x_0) - f_{\mathrm{low}})}{m_\varepsilon} + 2 \text{
evaluations of its derivatives}.$$

The constants $\kappa^a$, $\kappa^s$ and the exponents $\pi_j$ are those of the radii mode $u$.
The evaluation counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount`, the
latter for the successful iterations. -/
theorem IsARqpRun.exists_isFirstHit_of_anchored {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {u : Prop} [Decidable u] (hrad : ∀ k, (∀ i ≤ k + 1, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.η₁ ≤ arqpRho f p x s σ k →
      (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqpOf u P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqpOf u P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPiOf u p j) q +
          2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  set m := finMin 1 (fun j => ε j ^ arqpPiOf u p j) q with hm_def
  have hm0 : 0 < m := finMin_pos one_pos fun j hj => Real.rpow_pos_of_pos (hε j hj).1 _
  have hκ := arqpKappaDmOf_pos (q := q) u hσmin hθς hLp
  have hη := P.η₁_pos
  have hδ : 0 < P.η₁ * (arqpKappaDmOf u P L p q * m) := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams (L p))
    (fun k hk => (IsARqpRun.sigma_le_of_anchored hf hXC hA h k hk).2)
    (V := fun k => f (x k)) (Vlow := flow) hδ (fun k hk => IsARqpRun.objective_le h hk)
    (fun k hk => hb _ (h.mem k hk))
    (fun k hk hs =>
      (IsARqpRun.decrease hf hL hXC hA hq hqp hθς hε h
        (fun i hi => hk i (by omega))
      hs
      (fun h1 => hk (k + 1) le_rfl (Or.inl h1)) (hrad k hk hs)).2)
  have hlog := P.toARParams.log_γ₂_pos
  refine ⟨kε, hk, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · rw [kappaAARqpOf, kappaSARqpOf, kappaCARqp, arqpKappaUns]
    field_simp
  · rw [kappaSARqpOf]
    field_simp

/-- **Certification at a model minimizer $0$, from the jet at $y$** ([cartis2022evaluation], Lemma
12.2.10; §14.2). Let $y \in X$, let $f$ be of class $C^p$ at $y$, and let $\|\nabla^i f(y)\| \le
L_f = \max(1, L_1, \dots, L_p)$ for $i \in [2, p]$. Let $q \le p$, $\varepsilon \in (0, 1]^q$
and $\sigma_k > 0$, and let $0$ minimize the model $m(e) = T_{f,p}(y, e) + \sigma_k \|e\|^{p+1}
/ (p+1)!$ over $\{e : y + e \in X\}$. Then the radii $$r_j = \min\left(1, \frac{\varepsilon_j}{4
(3 L_f + \sigma_k)}\right)$$ lie in $(0, 1]$ for $j \in [1, q]$, and $y$ is an
$(\varepsilon, r)$-approximate $q$-th order minimizer over $\{e : y + e \in X\}$
(`Optimization.IsEpsDeltaApprox`).

The proof specializes `Optimization.taylorMeasure_regularizedModel_le_of_isMinOn`. Only $C^p$ at
$y$ and the jet bounds at $y$ are needed; the anchored hypotheses give both at the iterates. -/
theorem isEpsDeltaApprox_of_isMinOn_zero_of_jet {y : E} (hy : y ∈ X)
    (hy0 : ContDiffAt ℝ p f y)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p) {σk : ℝ} (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hσ : 0 < σk)
    (hmin : IsMinOn (regularizedModel (ftaylorSeries ℝ f y) p σk) {e | y + e ∈ X} 0) :
    (∀ j ∈ Finset.Icc 1 q, min 1 (ε j / (4 * (3 * finMax 1 L p + σk))) ∈ Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε
        (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))) := by
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hK : 0 < 3 * finMax 1 L p + σk := by linarith
  have hS0 : (0 : E) ∈ {e | y + e ∈ X} := by change y + 0 ∈ X; rw [add_zero]; exact hy
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := (hε j hj).1
    exact ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  · have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
    have hεj := (hε j hj).1
    have hδα : 4 * (3 * finMax 1 L p + σk) * min 1 (ε j / (4 * (3 * finMax 1 L p + σk))) ≤
        ε j := by
      calc 4 * (3 * finMax 1 L p + σk) * min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))
          ≤ 4 * (3 * finMax 1 L p + σk) * (ε j / (4 * (3 * finMax 1 L p + σk))) := by
            gcongr; exact min_le_right _ _
        _ = ε j := by field_simp
    have := taylorMeasure_regularizedModel_le_of_isMinOn (D := ftaylorSeries ℝ f y)
      (zero_le_one.trans hL1)
      hjet hσ.le
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, hjp⟩) (by rw [norm_zero]; exact zero_le_one)
      hS0 (fun e he => by rw [zero_add]; exact hmin he) hεj
      (lt_min one_pos (by positivity)) (min_le_left _ _) hδα
    rw [taylorMeasure_regularizedModel_zero hy0 σk hjp] at this
    exact this

/-- **Evaluation complexity of ARqp** ([cartis2022evaluation], Theorem 12.2.14; Theorem 14.2.4 for
ARqp-SC). Let $f \ge f_{\mathrm{low}}$ on $X$, let $X \subseteq C$, let $\nabla^p f$ be
$L_p$-Lipschitz anchored at the points of $A$ with respect to $C$, with $L_p \ge 1$, let
$\|\nabla^j f(y)\| \le L_f = \max(1, L_1, \dots, L_p)$ for $j \in [2, p]$ and $y \in A$, and let
$A$ contain $\{y \in X : f(y) \le f(x_0)\}$. Let $1 \le q \le p$, $\sigma_{\min} > 0$,
$\theta < \varsigma$, $\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. Consider an ARqp
run with exact data on $X$ whose radii follow the radii mode $u$:

* if $u$, then $\delta_{0,j} = 1$, and $\delta_{s_k, j} = 1$ at every iteration $k$ that is
  reached and does not terminate, for all $j \in [1, q]$;
* if not $u$, then $\delta_{s_k, j} \ge \kappa_\delta(\sigma_k) \varepsilon_j$ for all
  $j \in [1, q]$ at every iteration $k$ that is reached, does not terminate, and has
  $\|s_k\| < 1$.

Then the run terminates at some $k_\varepsilon$ with $x_{k_\varepsilon} \in X$, there are radii
$\delta_\varepsilon \in (0, 1]^q$ such that $x_{k_\varepsilon}$ is an
$(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer over
$\{e : x_{k_\varepsilon} + e \in X\}$, and the run uses at most $$\frac{\kappa^a (f(x_0) -
f_{\mathrm{low}})}{m_\varepsilon} + \kappa^c \text{ evaluations of } f \quad\text{and}\quad
\frac{\kappa^s (f(x_0) - f_{\mathrm{low}})}{m_\varepsilon} + 2 \text{ evaluations of its
derivatives},$$ where $m_\varepsilon = \min_{j \in [1, q]} \varepsilon_j^{\pi_j}$.

The constants and the exponents are those of the radii mode $u$; the source analyses the mode
$u = (q \le 2)$. The certificate is `Optimization.IsEpsDeltaApprox`, and the evaluation bounds
are those of `Optimization.IsARqpRun.exists_isFirstHit_of_anchored`. -/
theorem IsARqpRun.complexity {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ j ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p) (hXC : X ⊆ C)
      (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqpOf u P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqpOf u P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPiOf u p j) q +
          2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored hb hf hL hXC hA hq hqp
    hσmin hθς hε h (u := u)
    fun k hk hs => by
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    refine ⟨fun hq2 => ?_, fun hq2 => ?_⟩
    · exact IsARqpRun.delta_eq_one h (hrad.1 hq2).1 (hrad.1 hq2).2
        (k + 1) fun i hi => hk i (by omega)
    · by_cases hlong : 1 ≤ ‖s k‖
      · exact Or.inl hlong
      refine Or.inr fun j hj => ?_
      rw [(IsARqpRun.succ_eq h hk' hs).2]
      have hσ := IsARqpRun.sigma_le_of_anchored hf hXC hA h k fun i hi => hk' i hi.le
      have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
      refine le_trans ?_ (hrad.2 hq2 k hk' (not_le.1 hlong) j hj)
      exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2) (hε j hj).1.le
  have hxk := h.mem kε hk.2
  have hxA := hA _ hxk (IsARqpRun.mem_sublevel h kε hk.2).2
  refine ⟨kε, hk, hxk, ?_, hF, hD⟩
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · exact ⟨δ kε, fun j hj => h.delta_mem hδ₀ kε hk.2 j hj,
      MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hk.2) h1⟩
  · have hstep := h.step hk.2 h1
    have h2 : arqpStop₂ (arqpData f p x σ) s kε := hk.1.resolve_left h1
    have hσ : 0 < σ kε := h.toIsARRun.sigma_pos hk.2 kε le_rfl
    obtain ⟨hδ, hcert⟩ := isEpsDeltaApprox_of_isMinOn_zero_of_jet hxk
      (hf.contDiffAt _ (hf.subset hxA))
      (fun _ hi => hjet _ hi _ hxA) hqp hε hσ
      (hstep.isMinOn_of_eq h2)
    exact ⟨_, hδ, hcert⟩

end Optimization
