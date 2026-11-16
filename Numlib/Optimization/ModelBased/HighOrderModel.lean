/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Composite.RegularizedModel
import Numlib.Optimization.ModelBased.InexactTaylor
import Numlib.Optimization.Optimality.HighOrder

/-!
# The regularized model of high-order adaptive-regularization methods

The high-order adaptive-regularization methods ARqp ([cartis2022evaluation], §12.2.2), ARqpIDA
(§13.1.4) and ARqpEDA (§13.3.2) minimize the regularized model of order $p$,
$$m(s) = T_p(D, s) + \frac{\sigma}{(p+1)!}\|s\|^{p+1}, \qquad T_p(D, s) = \sum_{i=0}^{p}
  \frac{D_i[s]^i}{i!},$$
built from a jet $D$: the exact jet of $f$ at the iterate, or an inexact jet. The approximate
optimality of a trial step $s$ is measured by the model measure
$$\phi^\delta_{m,j}(s) = \sup\{\Delta T_{m,j}(s, d) : \|d\| \le \delta,\ d \in S\},$$
where $\Delta T_{m,j}(s, d) = T_{m,j}(s, 0) - T_{m,j}(s, d)$ is the decrement of the Taylor
polynomial $T_{m,j}(s, \cdot)$ of degree $j$ of $m$ at $s$. In the same way $\phi^\delta_{f,j}(y)$
is the measure of the jet of $f$ at $y$.

The results hold for arbitrary data, with an explicit error budget where the data are inexact; the
exact-data lemmas of Chapter 12 are the special cases with exact data and zero errors. The file
bounds the derivatives of the model, derives a model decrease from a large decrement, constructs a
step with its optimality radii from a global model minimizer, compares the exact and the inexact
model measures, transfers the measure from the model to the function, and derives the radius
inequality. The composite model of ARqpC (§14.1) is treated in
`Numlib.Optimization.Composite.RegularizedModel`, whose lemmas with $h = 0$ give the model-decrease
results here.

## Main results

* `Optimization.iteratedFDerivLipschitzOn_regularizedModel`,
  `Optimization.norm_iteratedFDeriv_regularizedModel_le`,
  `Optimization.abs_iteratedFDeriv_regularizedModel_apply_le`: Lemma 12.2.7, the $p$-th derivative
  of $m$ is $\sigma$-Lipschitz, and the derivatives of orders $2, \dots, p$ are bounded by
  $3L + \sigma$ on the unit ball.
* `Optimization.sub_regularizedModel_ge_of_taylorDecrement_ge`: Lemma 12.2.8, a large model
  decrement gives a model decrease; its corollary
  `Optimization.taylorMeasure_regularizedModel_le_of_isMinOn` bounds the model measure at a model
  minimizer.
* `Optimization.regularizedModel_decrease_ge_of_taylorDecrement_ge`: Lemma 13.1.10, the model
  decrease along a displacement with a large Taylor decrement of the data.
* `Optimization.exists_highOrderStep`: the existence part of Lemmas 12.2.9 and 13.1.12, a global
  model minimizer with its optimality radii; the termination of the inner Algorithm 12.2.3 is not
  covered.
* `Optimization.taylorMeasure_regularizedModel_le_add`: (13.1.48)–(13.1.50), the exact model measure
  is at most the inexact one plus an error term.
* `Optimization.taylorMeasure_le_of_regularizedModel`: the transfer of the measure from the model to
  the function behind Lemma 12.2.11.
* `Optimization.sub_mul_lt_of_measure_comparison`: the radius inequality from an abstract one-step
  comparison, with the instances `Optimization.radius_inequality_of_measure_gt` (Lemmas 12.2.11 and
  13.1.16, with an error budget) and `Optimization.radius_inequality_of_compositeTaylorMeasure_gt`
  (Lemma 14.1.7). The factor in these inequalities is $\varsigma - \theta$, which requires
  $\theta < \varsigma$.

## Implementation notes

* The model is `Optimization.regularizedModel D p σ`. Its jet at a step $s$ is
  `ftaylorSeries ℝ (regularizedModel D p σ) s`, and the model measure $\phi^\delta_{m,j}(s)$ is
  `Optimization.taylorMeasure` of this jet. The norms of derivatives are operator norms of
  continuous multilinear maps.
* The step-length algebra that follows the radius inequality (Lemmas 12.2.12, 13.1.17 and 14.1.8) is
  `Optimization.pow_ge_of_measure_ineq` and `Optimization.norm_step_ge_of_measure_ineq`. The measure
  at a local minimizer for the orders $1$ and $2$ (Theorem 12.1.4) is
  `Optimization.taylorMeasure_eq_zero_of_isLocalMin`.
-/

open Set Metric Finset Filter
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Derivatives of the model (Lemma 12.2.7) -/

section Derivatives

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ L : ℝ}

/-- Let $D$ be a jet, $p \in \mathbb{N}$ and $\sigma \ge 0$, and let $m$ be the regularized model of
$D$. Then the $p$-th derivative of $m$ is $\sigma$-Lipschitz on $E$:
$$\|\nabla^p m(s) - \nabla^p m(s')\| \le \sigma\|s - s'\| \quad \text{for } s, s' \in E.$$
This is the first part of Lemma 12.2.7 of [cartis2022evaluation], (12.2.39).

The $p$-th derivative of $T_p(D, \cdot)$ is constant, and that of $s \mapsto \|s\|^{p+1}$ is
$(p+1)!$-Lipschitz by (B.4.3). -/
theorem iteratedFDerivLipschitzOn_regularizedModel (hσ : 0 ≤ σ) :
    IteratedFDerivLipschitzOn (regularizedModel D p σ) p σ univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro a _ b _
  have hT := (D.iteratedFDerivLipschitzOn_taylorSum p) a (mem_univ a) b (mem_univ b)
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hT
  have hN := iteratedFDerivLipschitzOn_norm_pow (E := E) (r := p + 1) (by omega)
  rw [Nat.add_sub_cancel, iteratedFDerivLipschitzOn_iff] at hN
  rw [iteratedFDeriv_regularizedModel (Or.inl le_rfl), iteratedFDeriv_regularizedModel
    (Or.inl le_rfl), hT, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  calc σ / ((p + 1)! : ℝ) * ‖iteratedFDeriv ℝ p (fun y : E => ‖y‖ ^ (p + 1)) a -
        iteratedFDeriv ℝ p (fun y : E => ‖y‖ ^ (p + 1)) b‖
      ≤ σ / ((p + 1)! : ℝ) * (((p + 1)! : ℝ) * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left (hN a (mem_univ a) b (mem_univ b)) (by positivity)
    _ = σ * ‖a - b‖ := by field_simp

/-- Let $\sigma \ge 0$ and $s, d \in E$. The model differs from its own Taylor polynomial of degree
$p$ at $s$ by at most
$$|m(s + d) - T_{m,p}(s, d)| \le \frac{\sigma}{(p+1)!}\|d\|^{p+1}.$$
This follows from Lemma 12.2.7 of [cartis2022evaluation] with Corollary A.8.4.

The Taylor polynomial $T_{m,p}(s, \cdot)$ is `taylorPolynomial (Optimization.regularizedModel D
p σ) p s`. -/
theorem abs_regularizedModel_sub_taylorPolynomial_le (hσ : 0 ≤ σ) (s d : E) :
    |regularizedModel D p σ (s + d) - taylorPolynomial (regularizedModel D p σ) p s d| ≤
      σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) :=
  abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun _ _ => (contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt)
    (iteratedFDerivLipschitzOn_regularizedModel hσ) (mem_univ s) (mem_univ (s + d))

/-- Let $L \ge 0$ with $\|D_i\| \le L$ for $i = 2, \dots, p$, let $\sigma \ge 0$ and $\|s\| \le 1$.
Then
$$\|\nabla^\ell m(s)\| \le 3L + \sigma \quad \text{for } \ell = 2, \dots, p.$$
This is (12.2.38) of Lemma 12.2.7 of [cartis2022evaluation]. -/
theorem norm_iteratedFDeriv_regularizedModel_le (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {ℓ : ℕ} (hℓ : ℓ ∈ Finset.Icc 2 p) {s : E}
    (hs : ‖s‖ ≤ 1) : ‖iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s‖ ≤ 3 * L + σ := by
  obtain ⟨hℓ2, hℓp⟩ := Finset.mem_Icc.1 hℓ
  rw [iteratedFDeriv_regularizedModel (Or.inl hℓp)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact D.norm_iteratedFDeriv_taylorSum_le_three_mul hL
      (fun i hi => hD i (Finset.mem_Icc.2 ⟨hℓ2.trans (Finset.mem_Icc.1 hi).1,
        (Finset.mem_Icc.1 hi).2⟩)) hs
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc σ / ((p + 1)! : ℝ) * ‖iteratedFDeriv ℝ ℓ (fun y : E => ‖y‖ ^ (p + 1)) s‖
        ≤ σ / ((p + 1)! : ℝ) * ((p + 1)! : ℝ) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_norm_pow_le_factorial (by omega)
            (Or.inr (by omega)) hs) (by positivity)
      _ = σ := by field_simp

/-- Let $L \ge 0$ with $\|D_i\| \le L$ for $i = 2, \dots, p$, let $\sigma \ge 0$ and $\|s\| \le 1$.
Then for every $d \in E$ and $\ell = 2, \dots, p$,
$$|\nabla^\ell m(s)[d]^\ell| \le (3L + \sigma)\|d\|^\ell.$$
This is the diagonal form of (12.2.38) of Lemma 12.2.7 of [cartis2022evaluation]. -/
theorem abs_iteratedFDeriv_regularizedModel_apply_le (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {ℓ : ℕ} (hℓ : ℓ ∈ Finset.Icc 2 p) {s : E}
    (hs : ‖s‖ ≤ 1) (d : E) :
    |iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s (fun _ => d)| ≤ (3 * L + σ) * ‖d‖ ^ ℓ := by
  rw [← Real.norm_eq_abs]
  refine ((ftaylorSeries ℝ (regularizedModel D p σ) s).norm_apply_diagonal_le ℓ d).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_regularizedModel_le hL hD hσ hℓ hs)
    (by positivity)

end Derivatives

/-! ### Model decrease from a large decrement (Lemmas 12.2.8, 13.1.10) -/

section Decrease

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ L : ℝ}

/-- Let $L \ge 0$ with $\|D_i\| \le L$ for $i = 2, \dots, p$, let $\sigma \ge 0$, $\|s\| \le 1$ and
$1 \le j \le p$, and let $0 \le \delta \le 1$ with $4(3L + \sigma)\delta \le \alpha$ (the
condition (12.2.41)). If $\|d\| \le \delta$ and $\Delta T_{m,j}(s, d) \ge \alpha\delta^j/j!$
(12.2.42), then
$$m(s) - m(s + d) \ge \frac{\alpha}{2}\frac{\delta^j}{j!},$$
which is (12.2.43). This is Lemma 12.2.8 of [cartis2022evaluation].

It is the case $h = 0$ of the composite Lemma 14.1.2,
`Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge`. The decrement
$\Delta T_{m,j}(s, d)$ is `(ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d`. -/
theorem sub_regularizedModel_ge_of_taylorDecrement_ge (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p)
    {s d : E} (hs : ‖s‖ ≤ 1) {α δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * (3 * L + σ) * δ ≤ α) (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ s - regularizedModel D p σ (s + d) := by
  have h := compositeRegularizedModel_sub_ge_of_decrement_ge
    (Dc := (0 : FormalMultilinearSeries ℝ E ℝ))
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl hD (fun _ _ => by simp) hσ hj hs
    hδ0 hδ1 (by simpa using hδα) hd (by rwa [compositeModelDecrement_zero_fun])
  simpa using h

/-- **Radii at a minimizer of the model.** Let $L \ge 0$ with $\|D_i\| \le L$ for $i = 2, \dots, p$,
let $\sigma \ge 0$, $1 \le j \le p$ and $\|s\| \le 1$. Let $0 \in S$, and let $s$ minimize the
model over $s + S$: $m(s) \le m(s + d)$ for every $d \in S$. If $\alpha > 0$ and
$0 < \delta \le 1$ with $4(3L + \sigma)\delta \le \alpha$, then
$$\phi^\delta_{m,j}(s) \le \frac{\alpha\delta^j}{j!}.$$
This is the content of Lemma 12.2.9 of [cartis2022evaluation].

It is the case $h = 0$ of `Optimization.compositeTaylorMeasure_model_le_of_isMinOn`. -/
theorem taylorMeasure_regularizedModel_le_of_isMinOn (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p)
    {s : E} (hs : ‖s‖ ≤ 1) {S : Set E} (hS0 : (0 : E) ∈ S)
    (hmin : ∀ d ∈ S, regularizedModel D p σ s ≤ regularizedModel D p σ (s + d)) {α δ : ℝ}
    (hα : 0 < α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδα : 4 * (3 * L + σ) * δ ≤ α) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤ α * δ ^ j / j ! := by
  have h := compositeTaylorMeasure_model_le_of_isMinOn
    (Dc := (0 : FormalMultilinearSeries ℝ E ℝ)) hasLipschitzConst_zero isSubadditive_zero rfl hL
    le_rfl hD (fun _ _ => by simp) hσ hj hs hS0 (by simpa using hmin) hα hδ0 hδ1
    (by simpa using hδα)
  simpa using h

/-- Let $\sigma \ge 0$ and $j \le p$, let $\|D_\ell\| \le L$ for $\ell = j + 1, \dots, p$, and let
$0 \le \delta \le 1$ with $4\max(L, \sigma)\delta \le \alpha$ (13.1.64). If $\|d\| \le \delta$
and the decrement of the data satisfies $\Delta T_j(D, d) \ge \alpha\delta^j/j!$, then
$$m(0) - m(d) \ge \frac{\alpha}{2}\frac{\delta^j}{j!},$$
which is (13.1.65). This is Lemma 13.1.10 of [cartis2022evaluation].

Here $\Delta T_j(D, d)$ is `D.taylorDecrement j d`, the decrement of the data at $0$, not of the
model at a trial step. -/
theorem regularizedModel_decrease_ge_of_taylorDecrement_ge {j : ℕ} (hjp : j ≤ p) (hσ : 0 ≤ σ)
    (hD : ∀ ℓ ∈ Finset.Icc (j + 1) p, ‖D ℓ‖ ≤ L) {α δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * max L σ * δ ≤ α) {d : E} (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ D.taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ 0 - regularizedModel D p σ d := by
  set M := max L σ with hM
  have hM0 : 0 ≤ M := hσ.trans (le_max_right _ _)
  have hdiff : regularizedModel D p σ 0 - regularizedModel D p σ d =
      D.taylorDecrement j d - (D.taylorSum p d - D.taylorSum j d) -
        σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
    rw [regularizedModel_zero_right, regularizedModel_def, FormalMultilinearSeries.taylorDecrement,
      D.taylorSum_zero_right, D.taylorSum_zero_right]
    ring
  set S := ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ)
  have hhi : D.taylorSum p d - D.taylorSum j d ≤ M * S := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact D.norm_taylorSum_sub_taylorSum_le_of_norm_le hjp
      (fun ℓ hℓ => (hD ℓ hℓ).trans (le_max_left _ _)) hd
  have hreg : σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) ≤ M * (δ ^ (p + 1) / ((p + 1)! : ℝ)) := by
    rw [div_mul_eq_mul_div, mul_div_assoc']
    gcongr
    exact le_max_right _ _
  have hST : S + δ ^ (p + 1) / ((p + 1)! : ℝ) ≤ 2 * δ ^ (j + 1) / j ! := by
    have := sum_pow_div_factorial_Icc_succ_le hδ0 hδ1 j p
    rwa [Finset.sum_Icc_succ_top (by omega)] at this
  have h2 : M * (S + δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ M * (2 * δ ^ (j + 1) / j !) :=
    mul_le_mul_of_nonneg_left hST hM0
  refine half_mul_pow_div_factorial_le hδ0 hδα hdec ?_
  rw [hdiff]
  have e : 2 * M * δ ^ (j + 1) / (j ! : ℝ) = M * (2 * δ ^ (j + 1) / j !) := by ring
  linarith

end Decrease

/-! ### Existence of a step (Lemmas 12.2.9, 13.1.12) -/

section Step

variable {D : FormalMultilinearSeries ℝ E ℝ} {p q : ℕ} {σ L : ℝ}

/-- **Existence of an admissible high-order step.** Let $E$ be finite-dimensional, $1 \le p$,
$q \le p$ and $\sigma > 0$, let $L \ge 0$ with $\|D_i\| \le L$ for $i = 2, \dots, p$, let
$\theta > 0$ and $0 < \varsigma \le 1$, and let $\varepsilon_\ell > 0$ for $\ell = 1, \dots, q$.
Then there are a global minimizer $s$ of the model $m$ on $E$, radii $\delta_\ell$ and
displacements $d_\ell$ with the following properties.
* For $\ell = 1, \dots, q$: $0 < \delta_\ell \le 1$; $\delta_\ell = 1$ if $\ell \le 2$
  (12.2.44); and $\delta_\ell = \min(1, \varsigma\theta\varepsilon_\ell/(4(3L + \sigma)))$ if
  $\ell \ge 3$ (12.2.45).
* Either $\|s\| \ge 1$, or for every $\ell = 1, \dots, q$ the displacement $d_\ell$ is a
  $\varsigma$-approximate optimality displacement of the model at $s$ for the radius
  $\delta_\ell$ with $\Delta T_{m,\ell}(s, d_\ell) \le
  \varsigma\theta\varepsilon_\ell\delta_\ell^\ell/\ell!$ (12.2.29).

This is the existence part of Lemmas 12.2.9 and 13.1.12 of [cartis2022evaluation], for arbitrary
data.

A global minimizer satisfies $m(s) \le m(0)$ (12.2.27) and is always acceptable. Taking it
avoids the limiting argument of Algorithm 12.2.3, whose termination is not covered here. An
approximate optimality displacement is `Optimization.IsApproxMeasureStep` with the feasible set
$E$: $\|d_\ell\| \le \delta_\ell$ and $\varsigma\,\phi^{\delta_\ell}_{m,\ell}(s) \le \Delta
T_{m,\ell}(s, d_\ell)$. -/
theorem exists_highOrderStep [FiniteDimensional ℝ E] (hp : 1 ≤ p) (hq : q ≤ p) (hσ : 0 < σ)
    (hL : 0 ≤ L) (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {θ ς : ℝ} (hθ : 0 < θ) (hς : 0 < ς)
    (hς1 : ς ≤ 1) {ε : ℕ → ℝ} (hε : ∀ ℓ ∈ Finset.Icc 1 q, 0 < ε ℓ) :
    ∃ s : E, ∃ δs : ℕ → ℝ, ∃ dm : ℕ → E, IsMinOn (regularizedModel D p σ) univ s ∧
      (∀ ℓ ∈ Finset.Icc 1 q, 0 < δs ℓ ∧ δs ℓ ≤ 1) ∧
      (∀ ℓ ∈ Finset.Icc 1 q, ℓ ≤ 2 → δs ℓ = 1) ∧
      (∀ ℓ ∈ Finset.Icc 3 q, δs ℓ = min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))) ∧
      (1 ≤ ‖s‖ ∨ ∀ ℓ ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement ℓ)
          (δs ℓ) univ ς (dm ℓ) ∧
        (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement ℓ (dm ℓ) ≤
          ς * θ * ε ℓ * δs ℓ ^ ℓ / ℓ !) := by
  obtain ⟨s, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) (σ := σ) hσ hp
  set m := regularizedModel D p σ
  let δs : ℕ → ℝ := fun ℓ => if ℓ ≤ 2 then 1 else min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))
  -- maximizers of the model decrements
  have hdm : ∀ ℓ, ∃ d : E, 0 ≤ δs ℓ → d ∈ closedBall 0 (δs ℓ) ∩ univ ∧
      (ftaylorSeries ℝ m s).taylorDecrement ℓ d =
        taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ :=
    fun ℓ => by
      by_cases h : 0 ≤ δs ℓ
      · obtain ⟨d, hd, hdeq⟩ := exists_taylorMeasure_eq (ftaylorSeries ℝ m s) ℓ isClosed_univ
          (mem_univ 0) h
        exact ⟨d, fun _ => ⟨hd, hdeq⟩⟩
      · exact ⟨0, fun h' => absurd h' h⟩
  choose dm hdm using hdm
  have hK : 0 < 3 * L + σ := by positivity
  have hδs : ∀ ℓ ∈ Finset.Icc 1 q, 0 < δs ℓ ∧ δs ℓ ≤ 1 := fun ℓ hℓ => by
    have := hε ℓ hℓ
    by_cases h2 : ℓ ≤ 2
    · simp [δs, h2]
    · simp only [δs, h2, ite_false]
      exact ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  refine ⟨s, δs, dm, hmin, hδs, fun ℓ _ h2 => by simp [δs, h2], fun ℓ hℓ => ?_, ?_⟩
  · simp [δs, show ¬ ℓ ≤ 2 by have := (Finset.mem_Icc.1 hℓ).1; omega]
  by_cases hs : 1 ≤ ‖s‖
  · exact Or.inl hs
  refine Or.inr fun ℓ hℓ => ?_
  obtain ⟨hδ0, hδ1⟩ := hδs ℓ hℓ
  obtain ⟨hdmem, hdeq⟩ := hdm ℓ hδ0.le
  have hℓp : ℓ ≤ p := (Finset.mem_Icc.1 hℓ).2.trans hq
  have hφ0 := taylorMeasure_nonneg (ftaylorSeries ℝ m s) ℓ (mem_univ (0 : E)) hδ0.le
  -- the model measure is small
  have hφ : taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ ≤
      ς * θ * ε ℓ * δs ℓ ^ ℓ / ℓ ! := by
    have hεℓ := hε ℓ hℓ
    by_cases h2 : ℓ ≤ 2
    · have hcd : ContDiffAt ℝ ℓ m s :=
        (contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt.of_le (by exact_mod_cast hℓp)
      rw [taylorMeasure_eq_zero_of_isLocalMin hcd (hmin.isLocalMin univ_mem)
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, h2⟩) hδ0.le]
      positivity
    · have hδsℓ : δs ℓ = min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ))) := by simp [δs, h2]
      have hδα : 4 * (3 * L + σ) * δs ℓ ≤ ς * θ * ε ℓ := by
        rw [hδsℓ]
        calc 4 * (3 * L + σ) * min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))
            ≤ 4 * (3 * L + σ) * (ς * θ * ε ℓ / (4 * (3 * L + σ))) := by
              gcongr; exact min_le_right _ _
          _ = ς * θ * ε ℓ := by field_simp
      exact taylorMeasure_regularizedModel_le_of_isMinOn hL hD hσ.le
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩) (not_le.1 hs).le (mem_univ 0)
        (fun d _ => hmin (mem_univ _)) (by positivity) hδ0 hδ1 hδα
  refine ⟨⟨hdmem, ?_⟩, ?_⟩
  · change ς * taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ ≤ _
    rw [hdeq]
    exact mul_le_of_le_one_left hφ0 hς1
  · rw [hdeq]; exact hφ

end Step

/-! ### Exact versus inexact model measures ((13.1.48)–(13.1.50)) -/

section Inexact

variable {D Dbar : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ} {err : ℕ → ℝ}

/-- Let $D$ and $\bar D$ be jets, $\ell \le p$ and $s \in E$, and let $m$ and $\bar m$ be the
regularized models of $D$ and $\bar D$ with the same $p$ and $\sigma$. Then
$\nabla^\ell m(s) - \nabla^\ell \bar m(s)$ is the $\ell$-th derivative at $s$ of the Taylor sum
$T_p(D - \bar D, \cdot)$. -/
theorem iteratedFDeriv_regularizedModel_sub {ℓ : ℕ} (hℓ : ℓ ≤ p) (s : E) :
    iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s -
        iteratedFDeriv ℝ ℓ (regularizedModel Dbar p σ) s =
      iteratedFDeriv ℝ ℓ ((D - Dbar).taylorSum p) s := by
  rw [iteratedFDeriv_regularizedModel (Or.inl hℓ), iteratedFDeriv_regularizedModel (Or.inl hℓ),
    FormalMultilinearSeries.iteratedFDeriv_taylorSum_sub]
  abel

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$
(`Optimization.JetApprox D Dbar p err`), let $j \le p$, $s \in E$, $0 \in S$ and $\delta \ge 0$,
and let $m$ and $\bar m$ be the regularized models of $D$ and $\bar D$ with the same $p$ and
$\sigma$. Then
$$\phi^\delta_{m,j}(s) \le \phi^\delta_{\bar m,j}(s) + \sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!} \sum_{i=\ell}^{p} \frac{e_i\|s\|^{i-\ell}}{(i-\ell)!}.$$
This is the first inequality of (13.1.48)–(13.1.49) of [cartis2022evaluation].

The regularization terms cancel. The approximation relation is symmetric, so the bound also
holds with $m$ and $\bar m$ exchanged. -/
theorem taylorMeasure_regularizedModel_le_add (h : JetApprox D Dbar p err) {j : ℕ} (hjp : j ≤ p)
    (s : E) {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S +
        ∑ ℓ ∈ Finset.Icc 1 j,
          δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
  have habs := abs_taylorMeasure_sub_le (ftaylorSeries ℝ (regularizedModel D p σ) s)
    (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j hS0 hδ
  have hb : ∑ i ∈ Finset.Icc 1 j, ‖ftaylorSeries ℝ (regularizedModel D p σ) s i -
      ftaylorSeries ℝ (regularizedModel Dbar p σ) s i‖ * δ ^ i / i ! ≤
      ∑ ℓ ∈ Finset.Icc 1 j,
        δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
    refine sum_le_sum fun ℓ hℓ => ?_
    obtain ⟨hℓ1, hℓj⟩ := Finset.mem_Icc.1 hℓ
    have hn : ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
        ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ ≤
          ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
      change ‖iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s -
        iteratedFDeriv ℝ ℓ (regularizedModel Dbar p σ) s‖ ≤ _
      rw [iteratedFDeriv_regularizedModel_sub (hℓj.trans hjp)]
      refine ((D - Dbar).norm_iteratedFDeriv_taylorSum_le p ℓ s).trans
        (sum_le_sum fun i hi => ?_)
      have hi1 : i ∈ Finset.Icc 1 p :=
        Finset.mem_Icc.2 ⟨hℓ1.trans (Finset.mem_Icc.1 hi).1, (Finset.mem_Icc.1 hi).2⟩
      have : ‖(D - Dbar) i‖ ≤ err i := by
        change ‖D i - Dbar i‖ ≤ err i
        rw [norm_sub_rev]; exact h i hi1
      gcongr
    calc ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
          ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ * δ ^ ℓ / ℓ !
        = δ ^ ℓ / ℓ ! * ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
          ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ := by ring
      _ ≤ _ := by gcongr
  linarith [(abs_le.1 habs).2]

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$, let $\kappa, \kappa_s \ge 0$, and
let $e_i \le \kappa\kappa_s\|s\|^{p-i+1}$ for $i = 1, \dots, p$ (the accuracy requirement
(13.1.46)). Let $j \le p$, $0 \in S$ and $\delta \ge 0$. Then
$$\phi^\delta_{m,j}(s) \le \phi^\delta_{\bar m,j}(s) + 3\kappa\kappa_s \sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!}\|s\|^{p-\ell+1}.$$
This is (13.1.49) of [cartis2022evaluation]. -/
theorem taylorMeasure_regularizedModel_le_add_of_stepAccuracy (h : JetApprox D Dbar p err)
    {κ κs : ℝ} (hκ : 0 ≤ κ) (hκs : 0 ≤ κs) {s : E}
    (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ κ * κs * ‖s‖ ^ (p - i + 1)) {j : ℕ} (hjp : j ≤ p)
    {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S +
        3 * κ * κs * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) := by
  refine (taylorMeasure_regularizedModel_le_add h hjp s hS0 hδ).trans (add_le_add le_rfl ?_)
  rw [mul_sum]
  refine sum_le_sum fun ℓ hℓ => ?_
  obtain ⟨hℓ1, hℓj⟩ := Finset.mem_Icc.1 hℓ
  have hin : ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) ≤
      3 * κ * κs * ‖s‖ ^ (p - ℓ + 1) := by
    calc ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
        ≤ ∑ i ∈ Finset.Icc ℓ p, κ * κs * ‖s‖ ^ (p - ℓ + 1) * ((1 : ℝ) ^ (i - ℓ) / (i - ℓ)!) := by
          refine sum_le_sum fun i hi => ?_
          obtain ⟨hℓi, hip⟩ := Finset.mem_Icc.1 hi
          have he := herr i (Finset.mem_Icc.2 ⟨hℓ1.trans hℓi, hip⟩)
          have hpow : ‖s‖ ^ (p - i + 1) * ‖s‖ ^ (i - ℓ) = ‖s‖ ^ (p - ℓ + 1) := by
            rw [← pow_add]; congr 1; omega
          calc err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
              ≤ κ * κs * ‖s‖ ^ (p - i + 1) * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by gcongr
            _ = κ * κs * ‖s‖ ^ (p - ℓ + 1) * ((1 : ℝ) ^ (i - ℓ) / (i - ℓ)!) := by
              rw [one_pow, mul_assoc (κ * κs), hpow]; ring
      _ = κ * κs * ‖s‖ ^ (p - ℓ + 1) * ∑ i ∈ Finset.Icc ℓ p, (1 : ℝ) ^ (i - ℓ) / (i - ℓ)! :=
          (mul_sum _ _ _).symm
      _ ≤ κ * κs * ‖s‖ ^ (p - ℓ + 1) * (1 + 2 * 1) := by
          gcongr; exact sum_pow_div_factorial_le_one_add_two_mul zero_le_one le_rfl ℓ p
      _ = 3 * κ * κs * ‖s‖ ^ (p - ℓ + 1) := by ring
  calc δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
      ≤ δ ^ ℓ / ℓ ! * (3 * κ * κs * ‖s‖ ^ (p - ℓ + 1)) := by gcongr
    _ = 3 * κ * κs * (δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1)) := by ring

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$, let $e_{\max} \ge 0$ with
$e_i \le e_{\max}$ for $i = 1, \dots, p$, and let $\|s\| \le 1$, $j \le p$, $0 \in S$ and
$0 \le \delta \le 1$. Then
$$\phi^\delta_{m,j}(s) \le \phi^\delta_{\bar m,j}(s) + 6e_{\max}.$$
This is (13.1.50) of [cartis2022evaluation]. -/
theorem taylorMeasure_regularizedModel_le_add_six_mul (h : JetApprox D Dbar p err) {e : ℝ}
    (he0 : 0 ≤ e) (he : ∀ i ∈ Finset.Icc 1 p, err i ≤ e) {s : E} (hs : ‖s‖ ≤ 1) {j : ℕ}
    (hjp : j ≤ p) {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S + 6 * e := by
  refine (taylorMeasure_regularizedModel_le_add h hjp s hS0 hδ0).trans (add_le_add le_rfl ?_)
  calc ∑ ℓ ∈ Finset.Icc 1 j,
        δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
      ≤ ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (3 * e) := by
        refine sum_le_sum fun ℓ hℓ => ?_
        have hℓ1 := (Finset.mem_Icc.1 hℓ).1
        have hin : ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) ≤ 3 * e := by
          calc ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
              ≤ ∑ i ∈ Finset.Icc ℓ p, e * (‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)) := by
                refine sum_le_sum fun i hi => ?_
                rw [mul_div_assoc]
                gcongr
                exact he i (Finset.mem_Icc.2 ⟨hℓ1.trans (Finset.mem_Icc.1 hi).1,
                  (Finset.mem_Icc.1 hi).2⟩)
            _ = e * ∑ i ∈ Finset.Icc ℓ p, ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := (mul_sum _ _ _).symm
            _ ≤ e * (1 + 2 * ‖s‖) := by
                gcongr; exact sum_pow_div_factorial_le_one_add_two_mul (norm_nonneg _) hs ℓ p
            _ ≤ 3 * e := by nlinarith
        gcongr
    _ = 3 * e * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ 3 * e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ0 hδ1 j
    _ ≤ 6 * e := by nlinarith

end Inexact

/-! ### Measure transfer and the radius inequality (Lemmas 12.2.11, 13.1.16) -/

section Transfer

variable {f : E → ℝ} {p : ℕ} {σ L : ℝ} {C : Set E} {x s : E}

/-- **Measure transfer from the model to the function, anchored.** Let $C \subseteq E$ be convex,
let $f$ be of class $C^p$ at every point of $C$, let $x, x + s \in C$ and $L \ge 0$, and let
$\nabla^p f$ be $L$-Lipschitz anchored at $x$:
$$\|\nabla^p f(y) - \nabla^p f(x)\| \le L\|y - x\| \quad \text{for } y \in C,$$
the condition (14.2.9) of [cartis2022evaluation]. Let $\sigma \ge 0$, let $m$ be the regularized
model of the jet of $f$ at $x$, and let $j \le p$, $0 \in S$ and $\delta \ge 0$. Then
$$\phi^\delta_{f,j}(x + s) \le \phi^\delta_{m,j}(s) + (L + \sigma)\sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!}\,\frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!}.$$

This is `Optimization.taylorMeasure_le_of_regularizedModel` with a weaker Lipschitz condition. -/
theorem taylorMeasure_le_of_regularizedModel_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ L * ‖y - x‖)
    (hL0 : 0 ≤ L) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s) j δ S +
        (L + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) := by
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  refine (taylorDecrement_le_add_of_regularizedModel_anchored hC hf hL hx hxs hσ hjp d).trans
    (add_le_add (taylorDecrement_le_taylorMeasure _ j hd) ?_)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) (by positivity)
  gcongr

/-- **Measure transfer from the model to the function.** Let $C \subseteq E$ be convex, let $f$ be
of class $C^p$ at every point of $C$ with $\nabla^p f$ $L$-Lipschitz on $C$ and $L \ge 0$, and
let $x, x + s \in C$. Let $\sigma \ge 0$, let $m$ be the regularized model of the jet of $f$ at
$x$, and let $j \le p$, $0 \in S$ and $\delta \ge 0$. Then
$$\phi^\delta_{f,j}(x + s) \le \phi^\delta_{m,j}(s) + (L + \sigma)\sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!}\,\frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!}.$$
This is (12.2.53)–(12.2.56) of [cartis2022evaluation] for exact data; the bound is (12.2.56),
with the exponent $p - \ell + 1$.

It is the case $h = 0$ of `Optimization.compositeTaylorMeasure_le_of_step`. -/
theorem taylorMeasure_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s) j δ S +
        (L + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) :=
  taylorMeasure_le_of_regularizedModel_anchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy x hx) hL0 hx hxs hσ hjp hS0 hδ

/-- **The radius inequality, abstract form.** Let $\Phi, \Phi_m, R, a, \theta, \varepsilon, \delta,
e_0 \in \mathbb{R}$ and $j \in \mathbb{N}$. If
$$\frac{a\varepsilon\delta^j}{j!} - e_0 < \Phi, \qquad \Phi \le \Phi_m + R, \qquad \Phi_m \le
  \frac{\theta\varepsilon\delta^j}{j!},$$
then
$$(a - \theta)\frac{\varepsilon\delta^j}{j!} < R + e_0.$$
This is the common step of Lemmas 12.2.11, 13.1.16 and 14.1.7 of [cartis2022evaluation].

In the applications, $\Phi$ is the measure at the new iterate, which is not small;
$\Phi \le \Phi_m + R$ is a one-step comparison with a model measure $\Phi_m$; and the last
hypothesis says that the step approximately minimizes the model ((12.2.29), (14.1.13)). The
instances are `Optimization.radius_inequality_of_measure_gt` (smooth, with inexact data) and
`Optimization.radius_inequality_of_compositeTaylorMeasure_gt` (composite). -/
theorem sub_mul_lt_of_measure_comparison {Φ Φm R a θ ε δ e₀ : ℝ} {j : ℕ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ < Φ) (hcomp : Φ ≤ Φm + R)
    (h₂ : Φm ≤ θ * ε * δ ^ j / j !) : (a - θ) * ε * δ ^ j / j ! < R + e₀ := by
  have e : (a - θ) * ε * δ ^ j / (j ! : ℝ) =
      a * ε * δ ^ j / (j ! : ℝ) - θ * ε * δ ^ j / (j ! : ℝ) := by ring
  rw [e]
  linarith

/-- For $A, \delta, t \ge 0$ and $A \le A'$, $A\sum_{\ell=1}^{j}
\frac{\delta^\ell}{\ell!}\frac{t^{p-\ell+1}}{(p-\ell+1)!} \le A'\sum_{\ell=1}^{j}
\frac{\delta^\ell}{\ell!}t^{p-\ell+1}$. -/
private theorem mul_sum_le_mul_sum_of_factorial {A A' δ t : ℝ} {j p : ℕ} (hA : 0 ≤ A)
    (hAA' : A ≤ A') (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (t ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) ≤
      A' * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by
  have hT0 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by positivity
  calc A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (t ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))
      ≤ A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) hA
        gcongr
        exact div_le_self (by positivity)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
    _ ≤ A' * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by gcongr

/-- **The radius inequality, anchored.** Let $C \subseteq E$ be convex, let $f$ be of class $C^p$ at
every point of $C$, let $x, x + s \in C$, and let $L_p \ge 0$ with $\|\nabla^p f(y) - \nabla^p
f(x)\| \le L_p\|y - x\|$ for $y \in C$ (the condition (14.2.9) of [cartis2022evaluation]). Let
$\bar D$ approximate the jet of $f$ at $x$ up to order $p$ with errors
$e_i \le \kappa\kappa_s\|s\|^{p-i+1}$ for $i = 1, \dots, p$, where $\kappa, \kappa_s \ge 0$. Let
$0 \le \sigma \le \sigma_{\max}$, let $\bar m$ be the regularized model of $\bar D$, and let
$j \le p$, $0 \in S$ and $\delta \ge 0$. If
$$\frac{a\varepsilon\delta^j}{j!} - e_0 < \phi^\delta_{f,j}(x + s) \quad \text{and} \quad
  \phi^\delta_{\bar m,j}(s) \le \frac{\theta\varepsilon\delta^j}{j!},$$
then
$$(a - \theta)\frac{\varepsilon\delta^j}{j!} < (L_p + \sigma_{\max} +
  3\kappa\kappa_s)\sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!}\|s\|^{p-\ell+1} + e_0.$$

This is `Optimization.radius_inequality_of_measure_gt` with $\nabla^p f$ only Lipschitz anchored
at $x$. -/
theorem radius_inequality_of_measure_gt_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) {Lp : ℝ}
    (hLp : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lp * ‖y - x‖)
    (hLp0 : 0 ≤ Lp) (hx : x ∈ C)
    (hxs : x + s ∈ C) {Dbar : FormalMultilinearSeries ℝ E ℝ} {err : ℕ → ℝ}
    (happrox : JetApprox (ftaylorSeries ℝ f x) Dbar p err) {κ κs : ℝ} (hκ : 0 ≤ κ)
    (hκs : 0 ≤ κs) (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ κ * κs * ‖s‖ ^ (p - i + 1))
    {σmax : ℝ} (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ < taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S)
    (h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lp + σmax + 3 * κ * κs) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) + e₀ := by
  have h3 := taylorMeasure_le_of_regularizedModel_anchored hC hf hLp hLp0 hx hxs hσ hjp hS0 hδ
  have h4 := taylorMeasure_regularizedModel_le_add_of_stepAccuracy (σ := σ) happrox hκ hκs herr
    hjp hS0 hδ
  have h5 := mul_sum_le_mul_sum_of_factorial (j := j) (p := p) (A' := Lp + σmax)
    (add_nonneg hLp0 hσ)
    (by linarith) hδ (norm_nonneg s)
  refine sub_mul_lt_of_measure_comparison h₁ ?_ h₂
  linarith

/-- **The radius inequality.** Let $C \subseteq E$ be convex, let $f$ be of class $C^p$ at every
point of $C$ with $\nabla^p f$ $L_p$-Lipschitz on $C$ and $L_p \ge 0$, and let $x, x + s \in C$.
Let $\bar D$ approximate the jet of $f$ at $x$ up to order $p$ with errors
$e_i \le \kappa\kappa_s\|s\|^{p-i+1}$ for $i = 1, \dots, p$, where $\kappa, \kappa_s \ge 0$. Let
$0 \le \sigma \le \sigma_{\max}$, let $\bar m$ be the regularized model of $\bar D$, and let
$j \le p$, $0 \in S$ (feasible displacements at $x + s$) and $\delta \ge 0$. Suppose that the
measure at the new iterate is not small and that the step approximately minimizes the inexact
model at order $j$ (12.2.29):
$$\frac{a\varepsilon\delta^j}{j!} - e_0 < \phi^\delta_{f,j}(x + s) \quad \text{and} \quad
  \phi^\delta_{\bar m,j}(s) \le \frac{\theta\varepsilon\delta^j}{j!}.$$
Then
$$(a - \theta)\frac{\varepsilon\delta^j}{j!} < (L_p + \sigma_{\max} +
  3\kappa\kappa_s)\sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!}\|s\|^{p-\ell+1} + e_0.$$
This is Lemmas 12.2.11 and 13.1.16 of [cartis2022evaluation], with an explicit error budget.

For exact ARqp (Lemma 12.2.11), $\bar D$ is the exact jet, $\kappa = 0$, $e_0 = 0$ and
$a = \varsigma$: the failed Step-1 test at $x + s$ only certifies $\phi^\delta_{f,j}(x + s) >
\varsigma\varepsilon\delta^j/j!$, hence the factor $\varsigma - \theta$, and the analysis needs
$\theta < \varsigma$. For ARqpIDA (Lemma 13.1.16), $\kappa = \kappa_{\nabla,\max}$. -/
theorem radius_inequality_of_measure_gt (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    {Lp : ℝ} (hLp : IteratedFDerivLipschitzOn f p Lp C) (hLp0 : 0 ≤ Lp) (hx : x ∈ C)
    (hxs : x + s ∈ C) {Dbar : FormalMultilinearSeries ℝ E ℝ} {err : ℕ → ℝ}
    (happrox : JetApprox (ftaylorSeries ℝ f x) Dbar p err) {κ κs : ℝ} (hκ : 0 ≤ κ)
    (hκs : 0 ≤ κs) (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ κ * κs * ‖s‖ ^ (p - i + 1))
    {σmax : ℝ} (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ < taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S)
    (h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lp + σmax + 3 * κ * κs) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) + e₀ :=
  radius_inequality_of_measure_gt_anchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLp y hy x hx) hLp0 hx hxs happrox hκ hκs herr hσ
    hσmax hjp hS0 hδ h₁ h₂

/-- **The radius inequality for composite problems, anchored.** Let $F$ be a real normed space,
$c : E \to F$, and let $h : F \to \mathbb{R}$ have the Lipschitz constant $L_h$. Let
$C \subseteq E$ be convex, let $f$ and $c$ be of class $C^p$ at every point of $C$, let
$x, x + s \in C$, and let $L_f, L_c \ge 0$ with
$$\|\nabla^p f(y) - \nabla^p f(x)\| \le L_f\|y - x\|, \qquad \|\nabla^p c(y) - \nabla^p c(x)\|
  \le L_c\|y - x\| \qquad (y \in C).$$
Let $0 \le \sigma \le \sigma_{\max}$, $j \le p$, $0 \in S$ and $\delta \ge 0$. Write
$\phi^\delta_{w,j}(x + s)$ for the composite measure of the jets of $f$ and $c$ at $x + s$, and
$\phi^\delta_{\hat m,j}(s)$ for the composite measure at $s$ of the jets of the regularized
model of $f$ at $x$ and of the Taylor polynomial of degree $p$ of $c$ at $x$. If
$$\frac{a\varepsilon\delta^j}{j!} - e_0 < \phi^\delta_{w,j}(x + s) \quad \text{and} \quad
  \phi^\delta_{\hat m,j}(s) \le \frac{\theta\varepsilon\delta^j}{j!},$$
then
$$(a - \theta)\frac{\varepsilon\delta^j}{j!} < (L_f + L_hL_c + \sigma_{\max})\sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!}\|s\|^{p-\ell+1} + \frac{2L_hL_c}{(p+1)!}\|s\|^{p+1} + e_0.$$
This is Lemma 14.1.7 of [cartis2022evaluation] with Lipschitz conditions anchored at $x$.

This is `Optimization.radius_inequality_of_compositeTaylorMeasure_gt` with $\nabla^p f$ and
$\nabla^p c$ only Lipschitz anchored at $x$, between $x$ and the points of $C$. The composite
measure is `Optimization.compositeTaylorMeasure`. -/
theorem radius_inequality_of_compositeTaylorMeasure_gt_anchored {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : E → F} {h : F → ℝ} {Lf Lc Lh σmax : ℝ} (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lf * ‖y - x‖)
    (hLc : ∀ y ∈ C, ‖iteratedFDeriv ℝ p c y - iteratedFDeriv ℝ p c x‖ ≤ Lc * ‖y - x‖)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ <
      compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S)
    (h₂ : compositeTaylorMeasure
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
        (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lf + Lh * Lc + σmax) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + e₀ := by
  have h3 := compositeTaylorMeasure_le_of_step_anchored hC hf hc hLf hLc hLip hLf0 hLc0 hx hxs hσ
    hjp hS0 hδ
  have hLh := hLip.nonneg
  have h5 := mul_sum_le_mul_sum_of_factorial (j := j) (p := p) (A' := Lf + Lh * Lc + σmax)
    (by positivity : 0 ≤ Lf + Lh * Lc + σ) (by linarith) hδ (norm_nonneg s)
  refine sub_mul_lt_of_measure_comparison h₁ ?_ h₂
  linarith

/-- **The radius inequality for composite problems.** Let $F$ be a real normed space, $c : E \to F$,
and let $h : F \to \mathbb{R}$ have the Lipschitz constant $L_h$. Let $C \subseteq E$ be convex,
let $f$ and $c$ be of class $C^p$ at every point of $C$ with $\nabla^p f$ $L_f$-Lipschitz and
$\nabla^p c$ $L_c$-Lipschitz on $C$, $L_f, L_c \ge 0$, and let $x, x + s \in C$. Let
$0 \le \sigma \le \sigma_{\max}$, $j \le p$, $0 \in S$ and $\delta \ge 0$. With the composite
measures $\phi^\delta_{w,j}$ and $\phi^\delta_{\hat m,j}$ of
`Optimization.radius_inequality_of_compositeTaylorMeasure_gt_anchored`, suppose that
$$\frac{a\varepsilon\delta^j}{j!} - e_0 < \phi^\delta_{w,j}(x + s) \quad \text{and} \quad
  \phi^\delta_{\hat m,j}(s) \le \frac{\theta\varepsilon\delta^j}{j!},$$
the second condition being (14.1.13) for the composite model $\hat m$ built at $x$. Then
$$(a - \theta)\frac{\varepsilon\delta^j}{j!} < (L_f + L_hL_c + \sigma_{\max})\sum_{\ell=1}^{j}
  \frac{\delta^\ell}{\ell!}\|s\|^{p-\ell+1} + \frac{2L_hL_c}{(p+1)!}\|s\|^{p+1} + e_0.$$
This is Lemma 14.1.7 of [cartis2022evaluation].

The hypotheses are those of `Optimization.compositeTaylorMeasure_le_of_step`, together with
$\sigma \le \sigma_{\max}$. For ARqpC, $a = \varsigma$ and $e_0 = 0$, and the inequality is
(14.1.30), with the factors $\varsigma - \theta$ and $2$ on the last term (see
`Optimization.compositeTaylorDecrement_le_of_step`). -/
theorem radius_inequality_of_compositeTaylorMeasure_gt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : E → F} {h : F → ℝ} {Lf Lc Lh σmax : ℝ} (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ <
      compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S)
    (h₂ : compositeTaylorMeasure
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
        (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lf + Lh * Lc + σmax) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + e₀ :=
  radius_inequality_of_compositeTaylorMeasure_gt_anchored hC hf hc
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLf y hy x hx)
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLc y hy x hx) hLip hLf0 hLc0 hx hxs hσ hσmax hjp
    hS0 hδ h₁ h₂

end Transfer


/-! ### The model at the zero step -/

section Zero

/-- Let $f$ be of class $C^p$ at $x$, let $\sigma \in \mathbb{R}$, $j \le p$ and $d \in E$, and let
$m$ be the regularized model of the jet of $f$ at $x$. Then the Taylor decrement of order $j$ of
$m$ at $0$ is that of $f$ at $x$:
$$\Delta T_{m,j}(0, d) = \Delta T_{f,j}(x, d).$$
This is (12.2.49) of [cartis2022evaluation]. -/
theorem taylorDecrement_regularizedModel_zero {f : E → ℝ} {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x)
    (σ : ℝ) {j : ℕ} (hj : j ≤ p) (d : E) :
    (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) 0).taylorDecrement j d =
      (ftaylorSeries ℝ f x).taylorDecrement j d := by
  have hsymm := hf.isSymm_ftaylorSeries (p := p) le_rfl
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ftaylorSeries_regularizedModel_zero hsymm ((Finset.mem_Icc.1 hi).2.trans hj)]

/-- Let $f$ be of class $C^p$ at $x$, let $\sigma \in \mathbb{R}$ and $j \le p$, and let $m$ be the
regularized model of the jet of $f$ at $x$. Then for every $\delta$ and $S$ the measure of order
$j$ of $m$ at $0$ is that of $f$ at $x$: $\phi^\delta_{m,j}(0) = \phi^\delta_{f,j}(x)$. -/
theorem taylorMeasure_regularizedModel_zero {f : E → ℝ} {p : ℕ} {x : E} (hf : ContDiffAt ℝ p f x)
    (σ : ℝ) {j : ℕ} (hj : j ≤ p) (δ : ℝ) (S : Set E) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) 0) j δ S =
      taylorMeasure (ftaylorSeries ℝ f x) j δ S := by
  unfold taylorMeasure
  congr 1
  funext d
  exact taylorDecrement_regularizedModel_zero hf σ hj d

end Zero

end Optimization
