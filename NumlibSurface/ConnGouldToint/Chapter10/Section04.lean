/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import NumlibSurface.ConnGouldToint.Chapter09.Section02

/-!
# Conn, Gould and Toint, Section 10.4: Iterations with an objective-improving correction

This module formalizes two variants of the reduction ratio from Section 10.4 of [conn2000trust]. In
the first variant (Algorithm 10.4.1), a trust-region step $s_k$ from $x_k$ is followed by a
correction $c_k$ that does not increase the objective, $f(x_k + s_k + c_k) \le f(x_k + s_k)$. The
predicted decrease is augmented by the exact improvement of the correction,
$$\delta_k = m_k(x_k) - m_k(x_k + s_k) + f(x_k + s_k) - f(x_k + s_k + c_k),$$
and the ratio is $\rho_k = (f(x_k) - f(x_k + s_k + c_k)) / \delta_k$. The improvement of the
correction then cancels from the ratio error, so that the usual radius argument of Chapter 6 gives
very successful iterations at small radii (Theorem 10.4.1), a small gradient infinitely often
(Theorem 10.4.2), and convergence of the gradients to zero (Theorem 10.4.3). In the second variant,
a quadratic term $\frac12 \langle y - x, M (y - x) \rangle$ is added to the model and subtracted
from the actual reduction, and it cancels from the ratio error (10.4.16).

The proofs use the parameters and the radius update (6.1.5) of
`NumlibSurface.ConnGouldToint.Chapter06.Section01`.

## Main definitions

* Equations (10.4.1)–(10.4.4), `ConnGouldToint.Chapter10.magicalStepDecrease`: the augmented
  predicted decrease $\delta_k$.
* Equation (10.4.2), `ConnGouldToint.Chapter10.magicalStepRatio`: the reduction ratio $\rho_k$ of
  the corrected step.
* Algorithm 10.4.1, `ConnGouldToint.Chapter10.MagicalStepRun`: an infinite run of the trust-region
  method with corrections.
* Equation (10.4.12), `ConnGouldToint.Chapter10.quadraticAugmentedModel`: the model with an added
  quadratic term.
* Equation (10.4.15), `ConnGouldToint.Chapter10.quadraticAugmentedRatio`: the compensated reduction
  ratio.
* Equation (10.4.17), `ConnGouldToint.Chapter10.quadraticAugmentedError`: the difference between the
  actual and the predicted reduction of the base model.

## Main results

* Equations (10.4.3)–(10.4.5), `ConnGouldToint.Chapter10.magicalStepRatio_sub_one`: $|\rho_k - 1| =
  |m_k(x_k + s_k) - f(x_k + s_k)| / \delta_k$.
* Theorem 10.4.1, `ConnGouldToint.Chapter10.theorem_10_4_1`: a sufficiently small radius gives a
  very successful iteration, and the radius does not decrease.
* Theorem 10.4.2, `ConnGouldToint.Chapter10.theorem_10_4_2`: the gradient norm is smaller than any
  $\varepsilon > 0$ infinitely often.
* Theorem 10.4.3, `ConnGouldToint.Chapter10.theorem_10_4_3`: if the steps and corrections are
  bounded by multiples of the radius, then $\|\nabla f(x_k)\| \to 0$.
* Equation (10.4.16), `ConnGouldToint.Chapter10.quadraticAugmentedRatio_sub_one`: the error of the
  compensated ratio is the error (10.4.17) divided by the decrease of the augmented model.
* Equation (10.4.17), `ConnGouldToint.Chapter10.quadraticAugmentedError_eq_trial_error`: under
  agreement at the center, the error (10.4.17) is the model error at the trial point.

## Deviations from the source

* **Theorem 10.4.1** (correction). The lower bound (10.4.6) is assumed for the augmented decrease
  $\delta_k$, not for the decrease of the original model. See
  `ConnGouldToint.Chapter10.theorem_10_4_1`.
* **Equation (10.4.12)** (reading). The quadratic term uses the displacement of the argument from
  the center, as in (10.4.15), so it cancels from the ratio error (10.4.16). See
  `ConnGouldToint.Chapter10.quadraticAugmentedModel`.
-/

open Filter Topology
open ConnGouldToint.Chapter06

namespace ConnGouldToint.Chapter10

/-! ### Corrected steps -/

section MagicalSteps

variable {E : Type*} [NormedAddCommGroup E]

/-- **Equations (10.4.1)–(10.4.4)** of [conn2000trust]. For an objective $f$, a model $m$, a point
$x$, a step $s$ and a correction $c$, the **augmented predicted decrease** is
$$\delta(x, s, c) = m(x) - m(x + s) + \bigl(f(x + s) - f(x + s + c)\bigr),$$
the decrease of the model along $s$ plus the exact improvement of the objective from the
correction. -/
def magicalStepDecrease (f m : E → ℝ) (x s c : E) : ℝ :=
  m x - m (x + s) + (f (x + s) - f (x + s + c))

/-- **Equation (10.4.2)** of [conn2000trust]. The **reduction ratio of the corrected step** is
$$\rho(x, s, c) = \frac{f(x) - f(x + s + c)}{\delta(x, s, c)},$$
with $\delta$ the augmented predicted decrease `ConnGouldToint.Chapter10.magicalStepDecrease`.

Division is the Lean division, so the ratio is $0$ when $\delta(x, s, c) = 0$. -/
noncomputable def magicalStepRatio (f m : E → ℝ) (x s c : E) : ℝ :=
  (f x - f (x + s + c)) / magicalStepDecrease f m x s c

/-- **Algorithm 10.4.1** of [conn2000trust]. An infinite run of the trust-region method with
corrections, for parameters $P$ of (6.1.3) and an objective $f$, consists of iterates $x_k$,
steps $s_k$, corrections $c_k$, models $m_k$ and radii $\Delta_k$ with $\Delta_0 > 0$. Each step
decreases its model, each correction does not increase $f$, the next iterate is
$x_k + s_k + c_k$ if $\rho_k \ge \eta_1$ and $x_k$ otherwise, and the radius is updated by the
rule (6.1.5) with the ratio $\rho_k$ of the corrected step.

The structure contains neither the norm bound on the step $s_k$ nor the sufficient-decrease
bound on the augmented decrease $\delta_k$; it requires only $m_k(x_k) - m_k(x_k + s_k) > 0$.
The theorems that need these bounds take them as hypotheses. -/
structure MagicalStepRun (P : BTRParams) (f : E → ℝ) where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The trust-region steps $s_k$. -/
  s : ℕ → E
  /-- The corrections $c_k$, applied after the steps. -/
  correction : ℕ → E
  /-- The models $m_k$. -/
  model : ℕ → E → ℝ
  /-- The trust-region radii $\Delta_k$. -/
  radius : ℕ → ℝ
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  initial_pos : 0 < radius 0
  /-- Each step decreases its model: $m_k(x_k) - m_k(x_k + s_k) > 0$. -/
  base_decrease : ∀ k, 0 < model k (x k) - model k (x k + s k)
  /-- Each correction does not increase the objective: $f(x_k + s_k + c_k) \le f(x_k + s_k)$. -/
  correction_improves : ∀ k, f (x k + s k + correction k) ≤ f (x k + s k)
  /-- The next iterate is $x_k + s_k + c_k$ if $\rho_k \ge \eta_1$, and $x_k$ otherwise. -/
  iterate_update : ∀ k, x (k + 1) =
    if P.η₁ ≤ magicalStepRatio f (model k) (x k) (s k) (correction k) then
      x k + s k + correction k else x k
  /-- The radius is updated by the rule (6.1.5) with the ratio $\rho_k$ of the corrected step. -/
  radius_update : ∀ k, BTRRadiusUpdate P
    (magicalStepRatio f (model k) (x k) (s k) (correction k)) (radius k) (radius (k + 1))

/-- **Equations (10.4.3)–(10.4.5)** of [conn2000trust]. Let $f$ and $m$ satisfy $f(x) = m(x)$, and
let $\delta(x, s, c) > 0$. Then the ratio of the corrected step satisfies
$$|\rho(x, s, c) - 1| = \frac{|m(x + s) - f(x + s)|}{\delta(x, s, c)}.$$
The improvement from the correction cancels, and the error of the model at the original trial
point $x + s$ is divided by the augmented decrease. -/
theorem magicalStepRatio_sub_one {f m : E → ℝ} {x s c : E}
    (hval : f x = m x) (hpred : 0 < magicalStepDecrease f m x s c) :
    |magicalStepRatio f m x s c - 1| =
      |m (x + s) - f (x + s)| / magicalStepDecrease f m x s c := by
  rw [magicalStepRatio, show (f x - f (x + s + c)) / magicalStepDecrease f m x s c - 1 =
    (m (x + s) - f (x + s)) / magicalStepDecrease f m x s c by
      field_simp [hpred.ne']; unfold magicalStepDecrease; rw [hval]; ring,
    abs_div, abs_of_pos hpred]

/-- **Theorem 10.4.1** of [conn2000trust]. Let $P$ be parameters of (6.1.3), let $0 < \kappa \le 1$
and $a, C, \Delta > 0$, and let $f(x) = m(x)$. Assume
$$\kappa a \min\{a / C, \Delta\} \le \delta(x, s, c), \qquad |m(x + s) - f(x + s)| \le C
  \Delta^2, \qquad \Delta \le \frac{\kappa a (1 - \eta_2)}{C},$$
and let $\Delta'$ be obtained from $\Delta$ by the update (6.1.5) with the ratio
$\rho(x, s, c)$. Then $\rho(x, s, c) \ge \eta_2$ and $\Delta \le \Delta'$.

**Correction.** The source assumes the lower bound (10.4.6) for the decrease $m(x) - m(x + s)$
of the original model. The statement here assumes it for the augmented decrease
$\delta(x, s, c)$, which is the denominator of the ratio. The nonnegativity of the improvement
from the correction does not give the printed lower bound for the original model decrease.

The number $a$ plays the role of the gradient norm at $x$. -/
theorem theorem_10_4_1 {P : BTRParams} {f m : E → ℝ} {x s c : E}
    {κ a C Δ Δ' : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (ha : 0 < a)
    (hC : 0 < C) (hΔ : 0 < Δ) (hval : f x = m x)
    (hdec : κ * a * min (a / C) Δ ≤ magicalStepDecrease f m x s c)
    (herr : |m (x + s) - f (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * a * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (magicalStepRatio f m x s c) Δ Δ') :
    P.η₂ ≤ magicalStepRatio f m x s c ∧ Δ ≤ Δ' := by
  have hη : 0 < P.η₂ := P.eta₁_pos.trans_le P.eta₁_le_eta₂
  have hη' : 0 ≤ 1 - P.η₂ := sub_nonneg.mpr P.eta₂_lt_one.le
  have hs := (le_div_iff₀ hC).mp hsmall
  have hΔ' : Δ ≤ a / C := by
    apply (le_div_iff₀ hC).mpr
    refine hs.trans ?_
    have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ha.le hκ') hη'
    exact hh.trans (mul_le_of_le_one_right ha.le (by linarith))
  rw [min_eq_right hΔ'] at hdec
  have hp := (mul_pos (mul_pos hκ ha) hΔ).trans_le hdec
  have hr : |magicalStepRatio f m x s c - 1| ≤ 1 - P.η₂ := by
    rw [magicalStepRatio_sub_one hval hp]
    apply (div_le_iff₀ hp).mpr
    refine herr.trans ?_
    nlinarith only [mul_le_mul_of_nonneg_right hs hΔ.le,
      mul_le_mul_of_nonneg_left hdec hη']
  have hsuccess : P.η₂ ≤ magicalStepRatio f m x s c := by
    linarith only [hr, neg_abs_le (magicalStepRatio f m x s c - 1)]
  exact ⟨hsuccess, hupdate.very_successful hsuccess⟩

private def MagicalStepRun.successful {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) : Set ℕ :=
  {k | P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k)}

private theorem MagicalStepRun.radius_pos {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) (k : ℕ) : 0 < run.radius k := by
  induction k with
  | zero => exact run.initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

private theorem MagicalStepRun.decrease_pos {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) (k : ℕ) :
    0 < magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k) :=
  add_pos_of_pos_of_nonneg (run.base_decrease k) (sub_nonneg.mpr (run.correction_improves k))

private theorem MagicalStepRun.objective_drop {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) {k : ℕ} (hk : k ∈ run.successful) :
    P.η₁ * magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k) ≤
      f (run.x k) - f (run.x (k + 1)) := by
  have hr : P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k) := hk
  rw [run.iterate_update, ite_eq_left hr]
  exact (le_div_iff₀ (run.decrease_pos k)).mp hr

private theorem MagicalStepRun.stay {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) {k : ℕ} (hk : k ∉ run.successful) : run.x (k + 1) = run.x k := by
  have hn : ¬ P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k)
      (run.correction k) := hk
  rw [run.iterate_update, ite_eq_right hn]

private theorem MagicalStepRun.objective_antitone {P : BTRParams} {f : E → ℝ}
    (run : MagicalStepRun P f) : Antitone (fun k ↦ f (run.x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k ∈ run.successful
  · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (run.decrease_pos k)).le.trans
      (run.objective_drop hk))
  · rw [run.stay hk]

variable [NormedSpace ℝ E]

/-- **Theorem 10.4.2** of [conn2000trust]. Let $f$ be bounded below, and consider a run of Algorithm
10.4.1 with constants $0 < \kappa \le 1$ and $C > 0$ such that, for all $k$,
$f(x_k) = m_k(x_k)$,
$$\kappa \|Df(x_k)\| \min\left\{\frac{\|Df(x_k)\|}{C}, \Delta_k\right\} \le \delta_k, \qquad
  |m_k(x_k + s_k) - f(x_k + s_k)| \le C \Delta_k^2.$$
Then for every $\varepsilon > 0$ there are infinitely many $k$ with $\|Df(x_k)\| < \varepsilon$.

The proof uses only these agreement and decrease estimates. Here $Df$ is `fderiv ℝ f`, which is
$0$ at a point where $f$ is not differentiable. -/
theorem theorem_10_4_2 {P : BTRParams} {f : E → ℝ} (run : MagicalStepRun P f)
    {κ C : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (hC : 0 < C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * ‖fderiv ℝ f (run.x k)‖ *
      min (‖fderiv ℝ f (run.x k)‖ / C) (run.radius k) ≤
      magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k))
    (herr : ∀ k, |run.model k (run.x k + run.s k) - f (run.x k + run.s k)| ≤ C * run.radius k ^ 2)
    (hlower : BddBelow (Set.range f)) :
    ∀ ε > (0 : ℝ), ∃ᶠ k in atTop, ‖fderiv ℝ f (run.x k)‖ < ε := by
  intro ε hε
  by_contra! h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let θ := κ * ε * (1 - P.η₂) / C
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ hε) hη) hC
  have hforce (k : ℕ) (hk : N ≤ k) (hsmall : run.radius k ≤ θ) :
      P.η₂ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k) := by
    have hg := hN k hk
    refine (theorem_10_4_1 hκ hκ' (hε.trans_le hg) hC (run.radius_pos k)
      (hval k) (hdec k) (herr k) (hsmall.trans ?_) (run.radius_update k)).1
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hκ.le) hη.le) hC.le
  let r := min (run.radius N) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (run.radius_pos N) (mul_pos P.gamma₁_pos hθ)
  have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.radius k := by
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      let ρ := magicalStepRatio f (run.model k) (run.x k) (run.s k) (run.correction k)
      have hu := run.radius_update k
      by_cases hv : P.η₂ ≤ ρ
      · exact ih.trans (hu.very_successful hv)
      have hlarge : θ < run.radius k := lt_of_not_ge (fun hs ↦ hv (hforce k hk hs))
      have hγ : P.γ₁ * run.radius k ≤ run.radius (k + 1) := by
        by_cases hs : P.η₁ ≤ ρ
        · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.radius_pos k).le).trans
            (hu.successful hs (lt_of_not_ge hv)).1
        · exact (hu.unsuccessful (lt_of_not_ge hs)).1
      exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left hlarge.le P.gamma₁_pos.le).trans hγ)
  let v (k : ℕ) := f (run.x k)
  have ht := tendsto_atTop_ciInf run.objective_antitone
    (hlower.mono (show Set.range v ⊆ Set.range f from fun _ ⟨k, hk⟩ ↦ ⟨run.x k, hk⟩))
  have hdiff : Tendsto (fun k ↦ v k - v (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  let d := P.η₁ * (κ * ε * min (ε / C) r)
  have hd : 0 < d := mul_pos P.eta₁_pos
    (mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hC) hr))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hdiff.eventually_lt_const hd)
  let L := max N M
  have hfail (k : ℕ) (hk : L ≤ k) : k ∉ run.successful := by
    intro hs
    have hkN := (le_max_left N M).trans hk
    have hg := hN k hkN
    have hp := (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ.le)
      (min_le_min (div_le_div_of_nonneg_right hg hC.le) (hrad k hkN))
      (le_min (div_nonneg hε.le hC.le) hr.le) (by positivity)).trans (hdec k)
    exact (hM k ((le_max_right N M).trans hk)).not_ge
      ((mul_le_mul_of_nonneg_left hp P.eta₁_pos.le).trans (run.objective_drop hs))
  have hγ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hpow (j : ℕ) : run.radius (L + j) ≤ P.γ₂ ^ j * run.radius L := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hh := ((run.radius_update (L + j)).unsuccessful
        (lt_of_not_ge (hfail _ (Nat.le_add_right _ _)))).2
      rw [Nat.add_succ, pow_succ, mul_comm (P.γ₂ ^ j), mul_assoc]
      exact hh.trans (mul_le_mul_of_nonneg_left ih hγ.le)
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.radius L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const
      (run.radius L)
  obtain ⟨j, hj⟩ := (hlim.eventually_lt_const hr).exists
  exact hj.not_ge ((hrad _ ((le_max_left N M).trans (Nat.le_add_right L j))).trans (hpow j))

/-- **Theorem 10.4.3** of [conn2000trust]. Under the hypotheses of Theorem 10.4.2, assume in
addition that $Df$ is Lipschitz with constant $L \ge 0$, and that $\|s_k\| \le K \Delta_k$ and
$\|c_k\| \le M \Delta_k$ for constants $K, M \ge 0$. Then $\|Df(x_k)\| \to 0$. -/
theorem theorem_10_4_3 {P : BTRParams} {f : E → ℝ} (run : MagicalStepRun P f)
    {κ C K M L : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1) (hC : 0 < C)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * ‖fderiv ℝ f (run.x k)‖ *
      min (‖fderiv ℝ f (run.x k)‖ / C) (run.radius k) ≤
      magicalStepDecrease f (run.model k) (run.x k) (run.s k) (run.correction k))
    (herr : ∀ k, |run.model k (run.x k + run.s k) - f (run.x k + run.s k)| ≤ C * run.radius k ^ 2)
    (hs : ∀ k, ‖run.s k‖ ≤ K * run.radius k)
    (hc : ∀ k, ‖run.correction k‖ ≤ M * run.radius k)
    (hgrad : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hlower : BddBelow (Set.range f)) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0) := by
  refine (Chapter09.theorem_9_2_6 (S := run.successful) P.eta₁_pos hκ hC
    (εc := 1) (A := 1) zero_lt_one zero_lt_one hL (add_nonneg hK hM)
    (fun _ ↦ norm_nonneg _) run.radius_pos (fun _ _ ↦ by rw [one_mul])
    hgrad hdec (fun _ hk ↦ run.objective_drop hk) ?_ (fun _ hk ↦ run.stay hk)
    hlower (theorem_10_4_2 run hκ hκ' hC hval hdec herr hlower)).1
  intro k hk
  have hratio : P.η₁ ≤ magicalStepRatio f (run.model k) (run.x k) (run.s k)
      (run.correction k) := hk
  have he : run.x k - (run.x k + run.s k + run.correction k) =
      -(run.s k + run.correction k) := by abel
  rw [run.iterate_update, ite_eq_left hratio, he, norm_neg, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hs k) (hc k))

end MagicalSteps

/-! ### Quadratic augmentation of the model -/

section ModifiedModel

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- **Equation (10.4.17)** of [conn2000trust]. The **reduction error** of the step $s$ for the base
model $m$ is the actual reduction minus the predicted reduction,
$$e(x, s) = f(x) - f(x + s) - \bigl(m(x) - m(x + s)\bigr).$$
-/
def quadraticAugmentedError (f m : E → ℝ) (x s : E) : ℝ :=
  f x - f (x + s) - m x + m (x + s)

/-- **Equation (10.4.17)** of [conn2000trust], under agreement at the center (AM.2). If
$f(x) = m(x)$, then the reduction error is the model error at the trial point:
$e(x, s) = m(x + s) - f(x + s)$. -/
theorem quadraticAugmentedError_eq_trial_error {f m : E → ℝ} {x s : E}
    (hval : f x = m x) : quadraticAugmentedError f m x s = m (x + s) - f (x + s) := by
  unfold quadraticAugmentedError
  rw [hval]
  ring

variable [InnerProductSpace ℝ E]

/-- **Equation (10.4.12)** of [conn2000trust]. For a model $m$, a center $x$ and a linear map
$M : E \to E$, the **quadratically augmented model** is
$$\hat m(y) = m(y) + \frac12 \langle y - x, M (y - x) \rangle.$$

**Reading.** The quadratic term uses the displacement $y - x$ of the argument from the center,
as in (10.4.15), and not a fixed trial step. With this choice the quadratic term cancels from
the ratio error (10.4.16). -/
noncomputable def quadraticAugmentedModel (m : E → ℝ) (x : E) (M : E →ₗ[ℝ] E) (y : E) : ℝ :=
  m y + (1 / 2) * ⟪y - x, M (y - x)⟫

/-- **Equation (10.4.15)** of [conn2000trust]. The **compensated reduction ratio** of the step $s$
subtracts the same quadratic term from the actual reduction as the augmented model adds to the
predicted reduction:
$$\hat\rho(x, s) = \frac{f(x) - f(x + s) - \frac12 \langle s, M s \rangle}{\hat m(x) - \hat
  m(x + s)}.$$
-/
noncomputable def quadraticAugmentedRatio (f m : E → ℝ) (x s : E)
    (M : E →ₗ[ℝ] E) : ℝ :=
  (f x - f (x + s) - (1 / 2) * ⟪s, M s⟫) /
    (quadraticAugmentedModel m x M x - quadraticAugmentedModel m x M (x + s))

/-- **Equation (10.4.16)** of [conn2000trust]. If the augmented model decreases,
$\hat m(x) - \hat m(x + s) > 0$, then
$$|\hat\rho(x, s) - 1| = \frac{|e(x, s)|}{\hat m(x) - \hat m(x + s)},$$
with $e$ the reduction error (10.4.17) of the base model. The quadratic term cancels from the
numerator. -/
theorem quadraticAugmentedRatio_sub_one {f m : E → ℝ} {x s : E} {M : E →ₗ[ℝ] E}
    (hpred : 0 < quadraticAugmentedModel m x M x - quadraticAugmentedModel m x M (x + s)) :
    |quadraticAugmentedRatio f m x s M - 1| =
      |quadraticAugmentedError f m x s| /
        (quadraticAugmentedModel m x M x - quadraticAugmentedModel m x M (x + s)) := by
  let d := quadraticAugmentedModel m x M x - quadraticAugmentedModel m x M (x + s)
  have hcancel : f x - f (x + s) - (1 / 2) * ⟪s, M s⟫ - d =
      quadraticAugmentedError f m x s := by
    simp only [d, quadraticAugmentedModel, sub_self, inner_zero_left, mul_zero, add_zero,
      add_sub_cancel_left, quadraticAugmentedError]
    ring
  change |(f x - f (x + s) - (1 / 2) * ⟪s, M s⟫) / d - 1| = _
  have he : (f x - f (x + s) - (1 / 2) * ⟪s, M s⟫) / d - 1 =
      (f x - f (x + s) - (1 / 2) * ⟪s, M s⟫ - d) / d := by
    field_simp [show d ≠ 0 from hpred.ne']
  rw [he, hcancel, abs_div, abs_of_pos hpred]

end ModifiedModel

end ConnGouldToint.Chapter10
