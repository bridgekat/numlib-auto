/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Normed
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-!
# Conn, Gould and Toint, Section 6.3: The Cauchy point of a quadratic model

This module formalizes Section 6.3 of [conn2000trust]. At an iterate with model gradient $g$, the
Cauchy arc consists of the steps $s = -tg$ with $t \ge 0$ in the trust region $\|s\| \le \Delta$,
and the Cauchy point minimizes the model on this arc (6.3.3). For a quadratic model with Hessian
$H$, the Cauchy point gives the model decrease
$$m(0) - m(s^C) \ge \tfrac{1}{2} \|g\| \min\left\{ \frac{\|g\|}{\beta}, \nu \Delta \right\}, \qquad
  \beta = 1 + \|H\|, \quad \nu = \frac{\|g\|}{\|g\|_k},$$
where $\|\cdot\|_k$ is the trust-region norm (Theorem 6.3.1, Corollary 6.3.2). An Armijo
backtracking search along the arc gives a similar decrease (Theorem 6.3.3). Assumption AA.1 asks for
a fixed fraction of such a decrease (6.3.27), and Theorems 6.3.4 and 6.3.5 derive its basic
consequences. Each estimate compares the minimizer on the arc, or on the feasible set, with a
particular feasible step.

The module builds on the basic trust-region algorithm in
`NumlibSurface.ConnGouldToint.Chapter06.Section01`.

## Main definitions

* Equation (6.3.1), `ConnGouldToint.Chapter06.quadraticCurvatureBound`: the curvature bound
  $\beta = 1 + \|H\|$ of a quadratic model.
* Section 6.3.1, `ConnGouldToint.Chapter06.cauchyArc`: the steps $-tg$ with $t \ge 0$ in the trust
  region.
* Equation (6.3.3), `ConnGouldToint.Chapter06.IsCauchyPoint`: a minimizer of the model on the Cauchy
  arc.
* Equation (6.3.5), `ConnGouldToint.Chapter06.cauchyNormRatio`: the ratio $\|g\| / \|g\|_k$.
* Equation (6.3.17), `ConnGouldToint.Chapter06.approximateCauchyTime`: the trial times
  $\theta^j \Delta / \|g\|_k$ of the backtracking search.
* Assumption AA.1 and (6.3.27), `ConnGouldToint.Chapter06.HasSufficientModelDecrease`: the model
  decrease is at least $\kappa \|g\| \min\{\|g\| / \beta, \Delta\}$.
* Assumption AM.3 and (6.2.2), `ConnGouldToint.Chapter06.modelGradient`: the model gradient $g_k$ at
  the center.

## Main results

* Theorem 6.3.1, `ConnGouldToint.Chapter06.theorem_6_3_1`: the decrease of a quadratic model at a
  Cauchy point.
* Corollary 6.3.2, `ConnGouldToint.Chapter06.corollary_6_3_2`: the same bound written as
  $m(0) - m(s^C)$.
* Theorem 6.3.3, `ConnGouldToint.Chapter06.theorem_6_3_3`: the Armijo backtracking search terminates
  with a uniform model decrease.
* Theorem 6.3.4, `ConnGouldToint.Chapter06.theorem_6_3_4`: a step that satisfies AA.1 at a
  noncritical point is nonzero and decreases the model.
* Theorem 6.3.5, `ConnGouldToint.Chapter06.theorem_6_3_5`: a fixed fraction of the optimal model
  decrease satisfies AA.1 with a smaller constant.

## Conventions

* The model of Theorem 6.3.1 and Corollary 6.3.2 is the quadratic model
  `ConnGouldToint.Chapter06.quadraticModel`, evaluated at the step from the current iterate. The
  Cauchy arc is in these displacement coordinates.
* The trust-region norm $\|\cdot\|_k$ is a seminorm `p`. The Euclidean norm $\|\cdot\|$ is the norm
  of the inner product space.

## Deviations from the source

* **Theorem 6.3.3** (reading). The accepted step is taken at the first index at which the Armijo
  test holds. A sufficient step length bound guarantees that such an index exists, and the rejected
  predecessor gives the decrease bound. See `ConnGouldToint.Chapter06.theorem_6_3_3`.
-/

namespace ConnGouldToint.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (6.3.1)** of [conn2000trust], for quadratic models. For a quadratic model with
Hessian $H$, the **curvature bound** is $\beta = 1 + \|H\|$. -/
noncomputable def quadraticCurvatureBound (H : E →L[ℝ] E) : ℝ :=
  1 + ‖H‖

/-- **Section 6.3.1** of [conn2000trust], the Cauchy arc. For a seminorm $\|\cdot\|_k$ on $E$, a
gradient $g$ and a radius $\Delta$, the **Cauchy arc** is the set of steps
$$\{ s = -tg : t \ge 0, \ \|s\|_k \le \Delta \}.$$

The steps are displacements from the current iterate, which is the origin. -/
def cauchyArc (p : Seminorm ℝ E) (g : E) (Δ : ℝ) : Set E :=
  {s | ∃ t : ℝ, 0 ≤ t ∧ s = (-t) • g ∧ p s ≤ Δ}

/-- **Equation (6.3.3)** of [conn2000trust]. A step $s$ is a **Cauchy point** of the model $m$ for
the gradient $g$ and the radius $\Delta$ if $s$ lies on the Cauchy arc and minimizes $m$ over
the Cauchy arc. -/
def IsCauchyPoint (m : E → ℝ) (p : Seminorm ℝ E) (g : E) (Δ : ℝ) (s : E) : Prop :=
  IsMinOn m (cauchyArc p g Δ) s ∧ s ∈ cauchyArc p g Δ

/-- **Equation (6.3.5)** of [conn2000trust]. For a seminorm $\|\cdot\|_k$ and a gradient $g$, the
**norm ratio** is
$$\nu = \frac{\|g\|}{\|g\|_k}.$$

It is $0$ when $\|g\|_k = 0$, by Lean's convention for division by zero. -/
noncomputable def cauchyNormRatio (p : Seminorm ℝ E) (g : E) : ℝ :=
  ‖g‖ / p g

private theorem quadraticModel_cauchy (c : ℝ) (g : E) (H : E →L[ℝ] E) (t : ℝ) :
    quadraticModel c g H.toLinearMap ((-t) • g) =
      c - t * ‖g‖ ^ 2 + (1 / 2) * t ^ 2 * inner ℝ g (H g) := by
  simp only [quadraticModel, ContinuousLinearMap.coe_coe, map_smul,
    inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- **Theorem 6.3.1** of [conn2000trust]. Let $c \in \mathbb{R}$, $g \in E$, let $H$ be a bounded
linear operator on $E$, and let $\|\cdot\|_k$ be a norm on $E$. Let $\Delta \ge 0$, and let $s$
be a Cauchy point of the quadratic model $m(s) = c + \langle g, s \rangle + \frac{1}{2} \langle
s, Hs \rangle$. Then
$$c - m(s) \ge \tfrac{1}{2} \|g\| \min\left\{ \frac{\|g\|}{\beta}, \nu \Delta \right\},$$
where $\beta = 1 + \|H\|$ and $\nu = \|g\| / \|g\|_k$.

The norm is a seminorm `p` with `p v = 0 → v = 0`. -/
theorem theorem_6_3_1 (c : ℝ) (g : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : E}
    (hs : IsCauchyPoint (quadraticModel c g H.toLinearMap) p g Δ s) :
    c - quadraticModel c g H.toLinearMap s ≥
      (1 / 2) * ‖g‖ * min (‖g‖ / quadraticCurvatureBound H) (cauchyNormRatio p g * Δ) := by
  by_cases hg : g = 0
  · obtain ⟨t, _, rfl, _⟩ := hs.2
    simp [hg, quadraticModel]
  have hpg : 0 < p g := lt_of_le_of_ne (apply_nonneg p g) (fun h ↦ hg (hp g h.symm))
  let β := quadraticCurvatureBound H
  have hβ : 0 < β := by dsimp [β, quadraticCurvatureBound]; positivity
  let t := min (1 / β) (Δ / p g)
  have ht : 0 ≤ t := le_min (div_nonneg zero_le_one hβ.le) (div_nonneg hΔ hpg.le)
  have htΔ : t * p g ≤ Δ := (le_div_iff₀ hpg).1 (min_le_right _ _)
  have htβ : t * β ≤ 1 := (le_div_iff₀ hβ).1 (min_le_left _ _)
  have htrial : (-t) • g ∈ cauchyArc p g Δ := by
    refine ⟨t, ht, rfl, ?_⟩
    simpa only [map_smul_eq_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht] using htΔ
  have hmin := isMinOn_iff.1 hs.1 _ htrial
  rw [quadraticModel_cauchy] at hmin
  have hcurv : inner ℝ g (H g) ≤ β * ‖g‖ ^ 2 := calc
    inner ℝ g (H g) ≤ |inner ℝ g (H g)| := le_abs_self _
    _ ≤ ‖g‖ * ‖H g‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖H‖ * ‖g‖) := mul_le_mul_of_nonneg_left (H.le_opNorm g) (norm_nonneg g)
    _ = ‖H‖ * ‖g‖ ^ 2 := by ring
    _ ≤ β * ‖g‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [β, quadraticCurvatureBound]
      linarith
  have hquad : t ^ 2 * inner ℝ g (H g) ≤ t * ‖g‖ ^ 2 := calc
    _ ≤ t ^ 2 * (β * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    _ = (t * β) * (t * ‖g‖ ^ 2) := by ring
    _ ≤ 1 * (t * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_right htβ (mul_nonneg ht (sq_nonneg _))
    _ = _ := one_mul _
  have hlength : ‖g‖ * t = min (‖g‖ / β) (cauchyNormRatio p g * Δ) := by
    dsimp only [t]
    rw [mul_min_of_nonneg _ _ (norm_nonneg g)]
    simp only [cauchyNormRatio]
    congr 1 <;> ring
  change (1 / 2) * ‖g‖ * min (‖g‖ / β) (cauchyNormRatio p g * Δ) ≤
    c - quadraticModel c g H.toLinearMap s
  rw [← hlength]
  nlinarith only [hmin, hquad]

/-- **Corollary 6.3.2** of [conn2000trust]. Under the hypotheses of
`ConnGouldToint.Chapter06.theorem_6_3_1`,
$$m(0) - m(s) \ge \tfrac{1}{2} \|g\| \min\left\{ \frac{\|g\|}{1 + \|H\|}, \nu \Delta \right\}.$$

The model is written in displacement coordinates, so $m(0)$ is the model value at the current
iterate. -/
theorem corollary_6_3_2 (c : ℝ) (g : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : E}
    (hs : IsCauchyPoint (quadraticModel c g H.toLinearMap) p g Δ s) :
    quadraticModel c g H.toLinearMap 0 - quadraticModel c g H.toLinearMap s ≥
      (1 / 2) * ‖g‖ * min (‖g‖ / (1 + ‖H‖)) (cauchyNormRatio p g * Δ) := by
  simpa [quadraticModel, quadraticCurvatureBound] using theorem_6_3_1 c g H p hp hΔ hs

/-- **Equation (6.3.17)** of [conn2000trust]. For $\theta, \Delta \in \mathbb{R}$, a seminorm
$\|\cdot\|_k$ and a gradient $g$, the $j$-th **trial time** of the approximate Cauchy search is
$$t_j = \theta^j \frac{\Delta}{\|g\|_k}.$$
-/
noncomputable def approximateCauchyTime (θ Δ : ℝ) (p : Seminorm ℝ E) (g : E) (j : ℕ) : ℝ :=
  θ ^ j * (Δ / p g)

open Filter in
/-- **Theorem 6.3.3** of [conn2000trust]. Let $m : E \to \mathbb{R}$, $x, g \in E$ and a seminorm
$\|\cdot\|_k$ with $\|g\|_k > 0$. Let $\theta \in (0, 1)$, $\sigma \in (0, \frac{1}{2})$,
$\beta > 0$ and $\Delta > 0$, and suppose that
$$m(x - tg) \le m(x) - t \|g\|^2 + \frac{\beta t}{2} \, t \|g\|^2 \quad \text{for all } t \in
  [0, \Delta / \|g\|_k].$$
Let $t_j = \theta^j \Delta / \|g\|_k$. Then there is $j \in \mathbb{N}$ such that, with
$s = -t_j g$,

* $\|s\|_k \le \Delta$,
* $m(x + s) \le m(x) - \sigma t_j \|g\|^2$, the Armijo test, holds at $j$,
* the Armijo test fails at every $i < j$, and
* $m(x) - m(x + s) \ge \sigma \theta \|g\| \min\{ \|g\| / \beta, \nu \Delta \}$ with
  $\nu = \|g\| / \|g\|_k$.

**Reading.** The step is taken at the first index at which the Armijo test holds. A sufficient
step length bound guarantees that such an index exists, and the failure of the test at the
predecessor gives the decrease bound.

The quadratic upper estimate on the model follows from AM.1 and the bound on the model Hessian
along the feasible ray. -/
theorem theorem_6_3_3 {m : E → ℝ} {x g : E} (p : Seminorm ℝ E)
    {θ σ β Δ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hσ : σ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hβ : 0 < β) (hΔ : 0 < Δ) (hpg : 0 < p g)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) (Δ / p g),
      m (x + (-t) • g) ≤ m x - t * ‖g‖ ^ 2 + (β * t / 2) * (t * ‖g‖ ^ 2)) :
    ∃ j : ℕ,
      let t := approximateCauchyTime θ Δ p g
      let s := (-(t j)) • g
      p s ≤ Δ ∧
      m (x + s) ≤ m x - σ * (t j * ‖g‖ ^ 2) ∧
      (∀ i < j, m x - σ * (t i * ‖g‖ ^ 2) < m (x + (-(t i)) • g)) ∧
      σ * θ * ‖g‖ * min (‖g‖ / β) (cauchyNormRatio p g * Δ) ≤ m x - m (x + s) := by
  classical
  let t := approximateCauchyTime θ Δ p g
  let test (i : ℕ) := m (x + (-(t i)) • g) ≤ m x - σ * (t i * ‖g‖ ^ 2)
  have ht (i : ℕ) : 0 ≤ t i := mul_nonneg (pow_nonneg hθ.1.le _) (div_nonneg hΔ.le hpg.le)
  have htmax (i : ℕ) : t i ≤ Δ / p g :=
    mul_le_of_le_one_left (div_nonneg hΔ.le hpg.le) (pow_le_one₀ hθ.1.le hθ.2.le)
  have htcrit (i : ℕ) (h : t i ≤ 1 / β) : test i := by
    have hmul : β * t i ≤ 1 := by
      rw [mul_comm]
      exact (le_div_iff₀ hβ).mp h
    have hq := mul_le_mul_of_nonneg_right
      (show β * t i / 2 ≤ 1 - σ by linarith [hσ.2]) (mul_nonneg (ht i) (sq_nonneg ‖g‖))
    exact (hupper (t i) ⟨ht i, htmax i⟩).trans (by linarith)
  have hlim : Tendsto t atTop (nhds 0) := by
    change Tendsto (fun i : ℕ ↦ θ ^ i * (Δ / p g)) atTop (nhds 0)
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.1.le hθ.2).mul_const (Δ / p g)
  have hex : ∃ i, test i := by
    obtain ⟨i, hi⟩ := (hlim.eventually (gt_mem_nhds (one_div_pos.mpr hβ))).exists
    exact ⟨i, htcrit i hi.le⟩
  let j := Nat.find hex
  have hj : test j := Nat.find_spec hex
  have hfailed (i : ℕ) (hi : i < j) : ¬ test i := Nat.find_min hex hi
  have hlow : θ * min (1 / β) (Δ / p g) ≤ t j := by
    cases hji : j with
    | zero =>
      change _ ≤ t 0
      simp only [t, approximateCauchyTime, pow_zero, one_mul]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ.1.le).trans
        (mul_le_of_le_one_left (div_nonneg hΔ.le hpg.le) hθ.2.le)
    | succ i =>
      have hi : 1 / β < t i := lt_of_not_ge (fun h ↦ hfailed i (hji ▸ Nat.lt_succ_self i) (htcrit i h))
      rw [show t (i + 1) = θ * t i by simp [t, approximateCauchyTime, pow_succ]; ring]
      exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hi.le) hθ.1.le
  have hlength : ‖g‖ * min (1 / β) (Δ / p g) =
      min (‖g‖ / β) (cauchyNormRatio p g * Δ) := by
    rw [mul_min_of_nonneg _ _ (norm_nonneg g)]
    simp only [cauchyNormRatio]
    congr 1 <;> ring
  refine ⟨j, ?_, hj, fun i hi ↦ lt_of_not_ge (hfailed i hi), ?_⟩
  · change p ((-(t j)) • g) ≤ Δ
    simpa only [map_smul_eq_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (ht j)] using
      (le_div_iff₀ hpg).mp (htmax j)
  · rw [← hlength]
    have h := mul_le_mul_of_nonneg_left hlow (mul_nonneg hσ.1.le (sq_nonneg ‖g‖))
    change m (x + (-(t j)) • g) ≤ m x - σ * (t j * ‖g‖ ^ 2) at hj
    calc
      _ = (σ * ‖g‖ ^ 2) * (θ * min (1 / β) (Δ / p g)) := by ring
      _ ≤ _ := h.trans (by linarith only [hj])

/-- **Assumption AA.1** of [conn2000trust], with the benchmark (6.3.27). A step $s$ from $x$ gives
**sufficient model decrease** for the gradient $g$, the curvature bound $\beta$, the radius
$\Delta$ and the constant $\kappa$ if $\kappa \in (0, 1)$ and
$$m(x) - m(x + s) \ge \kappa \|g\| \min\left\{ \frac{\|g\|}{\beta}, \Delta \right\}.$$
-/
def HasSufficientModelDecrease (m : E → ℝ) (x s g : E) (β Δ κ : ℝ) : Prop :=
  κ ∈ Set.Ioo (0 : ℝ) 1 ∧ κ * ‖g‖ * min (‖g‖ / β) Δ ≤ m x - m (x + s)

variable [CompleteSpace E]

/-- **Assumption AM.3** of [conn2000trust] and **Equation (6.2.2)**. Let $E$ be a real Hilbert
space. The **model gradient** at the center $x$ is the gradient $g_k = \nabla m(x)$ of the model
$m$.

AM.3 requires it to equal the gradient of the objective at $x$. The gradient is Mathlib's
`gradient`. -/
noncomputable abbrev modelGradient (m : E → ℝ) (x : E) : E := gradient m x

/-- **Theorem 6.3.4** of [conn2000trust]. Let $E$ be a real Hilbert space, let
$f, m : E \to \mathbb{R}$ and $x, s \in E$, and let $\beta > 0$ and $\Delta > 0$. Suppose that
$\nabla m(x) = \nabla f(x) \neq 0$ (AM.3 at a noncritical point) and that $s$ gives sufficient
model decrease (AA.1) for the gradient $\nabla m(x)$. Then
$$m(x + s) < m(x) \quad \text{and} \quad s \neq 0.$$
-/
theorem theorem_6_3_4 {f m : E → ℝ} {x s : E} {β Δ κ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hmatch : modelGradient m x = gradient f x) (hg : gradient f x ≠ 0)
    (hdec : HasSufficientModelDecrease m x s (modelGradient m x) β Δ κ) :
    m (x + s) < m x ∧ s ≠ 0 := by
  have hgn : 0 < ‖modelGradient m x‖ := by
    rw [hmatch]
    exact norm_pos_iff.mpr hg
  have hpos : 0 < κ * ‖modelGradient m x‖ * min (‖modelGradient m x‖ / β) Δ :=
    mul_pos (mul_pos hdec.1.1 hgn) (lt_min (div_pos hgn hβ) hΔ)
  have hlt := sub_pos.mp (hpos.trans_le hdec.2)
  exact ⟨hlt, fun hz ↦ by simp [hz] at hlt⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Theorem 6.3.5** of [conn2000trust]. Let $E$ be a normed additive commutative group, let
$m : E \to \mathbb{R}$, $S \subseteq E$, and $x, s, g, u, v \in E$. Suppose that

* $u$ minimizes $m$ over $S$,
* $x + v \in S$, and $v$ gives sufficient model decrease (AA.1) with the constant $\kappa$, and
* $a \in (0, 1]$ and $a (m(x) - m(u)) \le m(x) - m(x + s)$.

Then $s$ gives sufficient model decrease (AA.1) with the constant $a \kappa$. -/
theorem theorem_6_3_5 {m : E → ℝ} {S : Set E} {x s g u v : E} {β Δ κ a : ℝ}
    (hopt : IsMinOn m S u) (hv : x + v ∈ S)
    (hdec : HasSufficientModelDecrease m x v g β Δ κ)
    (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (happrox : a * (m x - m u) ≤ m x - m (x + s)) :
    HasSufficientModelDecrease m x s g β Δ (a * κ) := by
  refine ⟨⟨mul_pos ha.1 hdec.1.1,
    (mul_le_of_le_one_left hdec.1.1.le ha.2).trans_lt hdec.1.2⟩, ?_⟩
  have hmin := isMinOn_iff.mp hopt _ hv
  calc
    _ = a * (κ * ‖g‖ * min (‖g‖ / β) Δ) := by ring
    _ ≤ a * (m x - m (x + v)) := mul_le_mul_of_nonneg_left hdec.2 ha.1.le
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sub_le_sub_left hmin _) ha.1.le).trans happrox

end ConnGouldToint.Chapter06
