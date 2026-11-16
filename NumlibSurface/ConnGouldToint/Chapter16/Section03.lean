/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.FischerBurmeister
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Conn, Gould and Toint, Section 16.3: Complementarity problems

Section 16.3 of [conn2000trust] treats the generalized complementarity problem: find $x$ such that
$$a(x) \ge 0, \qquad b(x) \ge 0, \qquad \langle a(x), b(x) \rangle = 0$$
for smooth maps $a, b : E \to \mathbb{R}^\iota$. The Fischer–Burmeister function $\phi(\alpha,
\beta) = \sqrt{\alpha^2 + \beta^2} - \alpha - \beta$ vanishes exactly when $\alpha \ge 0$,
$\beta \ge 0$ and $\alpha \beta = 0$. Hence the problem is the system of equations $\Phi(x) = 0$
with $\Phi_i(x) = \phi(a_i(x), b_i(x))$, and a trust-region method minimizes the least-squares merit
function $\frac{1}{2} \|\Phi(x)\|^2$. This module formalizes the residual and the merit function,
the linearization of the residual, the Gauss–Newton model, and Theorem 16.3.1, which characterizes
the solutions as the regular critical points of the merit function. The scalar residual is
`Numlib.Optimization.fischerBurmeister`.

## Main definitions

* Equation (16.3.1), `ConnGouldToint.Chapter16.IsComplementary`: the complementarity conditions.
* Equation (16.3.2), `ConnGouldToint.Chapter16.fischerBurmeister`: the scalar residual $\phi$.
* Equation (16.3.3), `ConnGouldToint.Chapter16.complementarityResidual`: the residual $\Phi$.
* Equation (16.3.4), `ConnGouldToint.Chapter16.complementarityLinearization`: the linearization of
  $\Phi$.
* Equations (16.3.5)–(16.3.6), `ConnGouldToint.Chapter16.complementarityCoefficient`: the diagonal
  coefficients of the linearization.
* Equation (16.3.7), `ConnGouldToint.Chapter16.complementarityMerit`: the merit function
  $\frac{1}{2} \|\Phi\|^2$.
* Equation (16.3.9), `ConnGouldToint.Chapter16.complementarityModel`: the Gauss–Newton model of the
  merit function.
* Theorem 16.3.1, `ConnGouldToint.Chapter16.HasRegularitySigns` and
  `ConnGouldToint.Chapter16.ComplementarityRegular`: the regularity condition.

## Main results

* Equation (16.3.3), `ConnGouldToint.Chapter16.complementarityResidual_eq_zero_iff`: $\Phi = 0$ if
  and only if the complementarity conditions hold.
* Equation (16.3.4), `ConnGouldToint.Chapter16.hasFDerivAt_complementarityResidual`: the
  linearization is the derivative of $\Phi$ where no pair of arguments vanishes.
* Equation (16.3.5), `ConnGouldToint.Chapter16.complementarityCoefficient_disk`: the coefficients
  lie in the disk (16.3.5).
* Equation (16.3.8), `ConnGouldToint.Chapter16.hasFDerivAt_complementarityMerit`: the derivative of
  the merit function.
* Equation (16.3.9), `ConnGouldToint.Chapter16.complementarityModel_expansion`: the expansion of the
  model.
* Theorem 16.3.1, `ConnGouldToint.Chapter16.theorem_16_3_1`: complementarity holds if and only if
  $x$ is regular and the merit function is stationary at $x$.

## Conventions

* The Jacobian of a map maps input directions to output directions. The gradient of $a_i$ is the
  continuous linear functional `fderiv ℝ (a · i) x`.
* At a pair $(\alpha, \beta) = (0, 0)$ the coefficients are $(-1, -1)$, the center of the disk
  (16.3.5).

## Deviations from the source

* **Equation (16.3.4)** (reading). The linearization maps a direction to the changes of the residual
  components. This transposes the printed matrix of column gradients and agrees with
  (16.3.8)–(16.3.9). See `ConnGouldToint.Chapter16.complementarityLinearization`.
* **Equation (16.3.8)** (generalization). The formula for the derivative of the merit function also
  holds where both arguments of a residual component vanish. See
  `ConnGouldToint.Chapter16.hasFDerivAt_complementarityMerit`.
-/

open scoped BigOperators

namespace ConnGouldToint.Chapter16

/-- **Equation (16.3.1)** of [conn2000trust]. For $a, b \in \mathbb{R}^\iota$, the pair is
**complementary** if
$$a_i \ge 0, \quad b_i \ge 0 \quad \text{for all } i, \qquad \sum_i a_i b_i = 0.$$
-/
def IsComplementary {ι : Type*} [Fintype ι] (a b : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧ ∑ i, a i * b i = 0

/-- **Equation (16.3.2)** of [conn2000trust]. The scalar complementarity residual is the
**Fischer–Burmeister function** $\phi(\alpha, \beta) = \sqrt{\alpha^2 + \beta^2} - \alpha -
\beta$. -/
noncomputable abbrev fischerBurmeister := Numlib.Optimization.fischerBurmeister

/-- **Equation (16.3.3)** of [conn2000trust]. For $a, b \in \mathbb{R}^\iota$, the **complementarity
residual** is the vector with components $\Phi_i = \phi(a_i, b_i)$. -/
noncomputable def complementarityResidual {ι : Type*} (a b : ι → ℝ) (i : ι) : ℝ :=
  fischerBurmeister (a i) (b i)

/-- **Equation (16.3.3)** of [conn2000trust]. For $a, b \in \mathbb{R}^\iota$, the residual $\Phi$
vanishes if and only if $a$ and $b$ are complementary. -/
theorem complementarityResidual_eq_zero_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    complementarityResidual a b = 0 ↔ IsComplementary a b := by
  constructor
  · intro h
    have hc (i : ι) : 0 ≤ a i ∧ 0 ≤ b i ∧ a i * b i = 0 :=
      Numlib.Optimization.fischerBurmeister_eq_zero_iff.mp (congrFun h i)
    exact ⟨fun i ↦ (hc i).1, fun i ↦ (hc i).2.1,
      Finset.sum_eq_zero fun i _ ↦ (hc i).2.2⟩
  · rintro ⟨ha, hb, hsum⟩
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_nonneg (ha i) (hb i))).mp hsum
    funext i
    exact Numlib.Optimization.fischerBurmeister_eq_zero_iff.mpr
      ⟨ha i, hb i, hprod i (Finset.mem_univ i)⟩

/-- **Equation (16.3.7)** of [conn2000trust]. For $a, b \in \mathbb{R}^\iota$, the **complementarity
merit** is $\frac{1}{2} \sum_i \Phi_i^2$. -/
noncomputable def complementarityMerit {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  (∑ i, complementarityResidual a b i ^ 2) / 2

/-- **Equations (16.3.5)–(16.3.6)** of [conn2000trust]. For $\alpha, \beta \in \mathbb{R}$, the
**diagonal coefficient** is
$$\frac{\alpha}{\sqrt{\alpha^2 + \beta^2}} - 1.$$
It is the partial derivative of $\phi$ with respect to its first argument where
$(\alpha, \beta) \neq (0, 0)$.

At the origin the Lean division gives the value $-1$. Then both coefficients are $-1$, the
center of the permitted disk (16.3.5). -/
noncomputable def complementarityCoefficient (a b : ℝ) : ℝ :=
  a / √(a ^ 2 + b ^ 2) - 1

private theorem radicand_pos {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + b ^ 2 := by
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg b)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero h)

/-- **Equation (16.3.5)** of [conn2000trust]. For all $\alpha, \beta \in \mathbb{R}$, the
coefficients $\xi = \alpha / \sqrt{\alpha^2 + \beta^2} - 1$ and
$\zeta = \beta / \sqrt{\alpha^2 + \beta^2} - 1$ satisfy $(\xi + 1)^2 + (\zeta + 1)^2 \le 1$. -/
theorem complementarityCoefficient_disk (a b : ℝ) :
    (complementarityCoefficient a b + 1) ^ 2 +
      (complementarityCoefficient b a + 1) ^ 2 ≤ 1 := by
  by_cases h : a ≠ 0 ∨ b ≠ 0
  · have hq := radicand_pos h
    unfold complementarityCoefficient
    rw [add_comm (b ^ 2), sub_add_cancel, sub_add_cancel, div_pow, div_pow, ← add_div,
      Real.sq_sqrt hq.le, div_self hq.ne']
  · push Not at h
    norm_num [complementarityCoefficient, h.1, h.2]

private theorem abs_fischerBurmeister_le (a b : ℝ) :
    |fischerBurmeister a b| ≤ 2 * (|a| + |b|) := by
  have hs : √(a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, by nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]⟩
  calc
    _ ≤ |√(a ^ 2 + b ^ 2) - a| + |b| := abs_sub _ _
    _ ≤ (√(a ^ 2 + b ^ 2) + |a|) + |b| := by
      have ht := abs_sub (√(a ^ 2 + b ^ 2)) a
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at ht
      linarith
    _ ≤ _ := by linarith

open Filter Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasFDerivAt_fischerBurmeister_of_ne_zero {a b : E → ℝ} {x : E}
    {A B : E →L[ℝ] ℝ} (ha : HasFDerivAt a A x) (hb : HasFDerivAt b B x)
    (h : a x ≠ 0 ∨ b x ≠ 0) :
    HasFDerivAt (fun y ↦ fischerBurmeister (a y) (b y))
      (complementarityCoefficient (a x) (b x) • A +
        complementarityCoefficient (b x) (a x) • B) x := by
  have hq := radicand_pos h
  have hs := (((ha.pow 2).add (hb.pow 2)).sqrt hq.ne').sub ha |>.sub hb
  convert hs using 1
  · rfl
  · ext v
    simp [complementarityCoefficient, add_comm (b x ^ 2)]
    ring

/-- **Equation (16.3.4)** of [conn2000trust]. For $a, b : E \to \mathbb{R}^\iota$ and $x \in E$, the
**linearization** of the residual maps a direction $s$ to the vector with components
$$\xi_i \, \nabla a_i(x) s + \zeta_i \, \nabla b_i(x) s,$$
where $\xi_i$ and $\zeta_i$ are the diagonal coefficients at $(a_i(x), b_i(x))$ and
$(b_i(x), a_i(x))$.

**Reading.** The source writes the linearization with the matrix of column gradients of $a$ and
$b$. With the Jacobian convention that maps input directions to output directions, this matrix
is transposed, and the diagonal weights act on the output of each Jacobian. This form agrees
with (16.3.8)–(16.3.9). -/
noncomputable def complementarityLinearization {ι : Type*} (a b : E → ι → ℝ) (x : E) :
    E →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    complementarityCoefficient (a x i) (b x i) • fderiv ℝ (a · i) x +
      complementarityCoefficient (b x i) (a x i) • fderiv ℝ (b · i) x

/-- **Equation (16.3.4)** of [conn2000trust], derivative of the residual. Let
$a, b : E \to \mathbb{R}^\iota$ have differentiable components at $x$, and suppose that
$(a_i(x), b_i(x)) \neq (0, 0)$ for every $i$. Then the linearization is the derivative of
$y \mapsto \Phi(a(y), b(y))$ at $x$. -/
theorem hasFDerivAt_complementarityResidual {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x)
    (h : ∀ i, a x i ≠ 0 ∨ b x i ≠ 0) :
    HasFDerivAt (fun y ↦ complementarityResidual (a y) (b y))
      (complementarityLinearization a b x) x :=
  hasFDerivAt_pi.2 fun i ↦
    hasFDerivAt_fischerBurmeister_of_ne_zero (ha i).hasFDerivAt (hb i).hasFDerivAt (h i)

private theorem hasFDerivAt_half_fischerBurmeister_sq {a b : E → ℝ} {x : E}
    {A B : E →L[ℝ] ℝ} (ha : HasFDerivAt a A x) (hb : HasFDerivAt b B x) :
    HasFDerivAt (fun y ↦ fischerBurmeister (a y) (b y) ^ 2 / 2)
      (fischerBurmeister (a x) (b x) •
        (complementarityCoefficient (a x) (b x) • A +
          complementarityCoefficient (b x) (a x) • B)) x := by
  by_cases h : a x ≠ 0 ∨ b x ≠ 0
  · have hs := hasFDerivAt_fischerBurmeister_of_ne_zero ha hb h
    have hd := (hs.pow 2).const_mul ((2 : ℝ)⁻¹)
    convert hd using 1
    · funext y
      ring
    · ext v
      simp
      ring
  · push Not at h
    have hzero : fischerBurmeister (a x) (b x) = 0 := by
      simp [Numlib.Optimization.fischerBurmeister, h.1, h.2]
    rw [hzero, zero_smul, hasFDerivAt_iff_isLittleO]
    have hA : a =O[𝓝 x] (· - x) := by simpa [h.1] using ha.isBigO_sub
    have hB : b =O[𝓝 x] (· - x) := by simpa [h.2] using hb.isBigO_sub
    let r (y : E) := fischerBurmeister (a y) (b y)
    have hr : r =O[𝓝 x] (· - x) := by
      apply IsBigO.trans _ (hA.norm_left.add hB.norm_left)
      apply IsBigO.of_bound 2
      filter_upwards with y
      change ‖r y‖ ≤ 2 * ‖‖a y‖ + ‖b y‖‖
      rw [Real.norm_eq_abs (r y), Real.norm_of_nonneg (by positivity), Real.norm_eq_abs (a y),
        Real.norm_eq_abs (b y)]
      exact abs_fischerBurmeister_le (a y) (b y)
    have hrcont : ContinuousAt r x := by
      change ContinuousAt (fun y ↦ √(a y ^ 2 + b y ^ 2) - a y - b y) x
      have hca := ha.continuousAt
      have hcb := hb.continuousAt
      fun_prop
    have hrsmall : r =o[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      apply (isLittleO_one_iff ℝ).2
      simpa [r, hzero] using hrcont.tendsto
    have hsq : (fun y ↦ r y ^ 2) =o[𝓝 x] (· - x) := by
      apply IsLittleO.of_norm_right
      simpa only [pow_two, mul_one] using hr.norm_right.mul_isLittleO hrsmall
    simpa [r, hzero, div_eq_mul_inv, mul_comm] using hsq.const_mul_left ((2 : ℝ)⁻¹)

/-- **Equation (16.3.8)** of [conn2000trust]. Let $a, b : E \to \mathbb{R}^\iota$ have
differentiable components at $x$. Then the derivative at $x$ of the merit function
$y \mapsto \frac{1}{2} \|\Phi(a(y), b(y))\|^2$ is
$$\sum_i \Phi_i \bigl(\xi_i \nabla a_i(x) + \zeta_i \nabla b_i(x)\bigr),$$
where $\Phi_i = \phi(a_i(x), b_i(x))$ and $\xi_i, \zeta_i$ are the diagonal coefficients.

**Generalization.** The formula also holds where $a_i(x) = b_i(x) = 0$. There $\Phi_i = 0$, so
the coefficient of that component does not matter.

The derivative is a continuous linear functional, as the Jacobian convention gives. -/
theorem hasFDerivAt_complementarityMerit {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x) :
    HasFDerivAt (fun y ↦ complementarityMerit (a y) (b y))
      (∑ i, complementarityResidual (a x) (b x) i •
        (complementarityCoefficient (a x i) (b x i) • fderiv ℝ (a · i) x +
          complementarityCoefficient (b x i) (a x i) • fderiv ℝ (b · i) x)) x := by
  simpa only [complementarityMerit, complementarityResidual, Finset.sum_div] using
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      hasFDerivAt_half_fischerBurmeister_sq (ha i).hasFDerivAt (hb i).hasFDerivAt)

/-- **Equation (16.3.9)** of [conn2000trust]. For $a, b : E \to \mathbb{R}^\iota$ and $x \in E$, the
**Gauss–Newton model** of the merit function is
$$m(s) = \tfrac{1}{2} \sum_i \bigl(\Phi_i + (\Lambda s)_i\bigr)^2,$$
where $\Phi_i = \phi(a_i(x), b_i(x))$ and $\Lambda$ is the linearization (16.3.4) at $x$. -/
noncomputable def complementarityModel {ι : Type*} [Fintype ι]
    (a b : E → ι → ℝ) (x s : E) : ℝ :=
  (∑ i, (complementarityResidual (a x) (b x) i +
    complementarityLinearization a b x s i) ^ 2) / 2

/-- **Equation (16.3.9)** of [conn2000trust], expansion. Let $a, b : E \to \mathbb{R}^\iota$ have
differentiable components at $x$. For every $s \in E$,
$$m(s) = \psi(x) + \nabla \psi(x) s + \tfrac{1}{2} \|\Lambda s\|^2,$$
where $\psi(y) = \frac{1}{2} \|\Phi(a(y), b(y))\|^2$ is the merit function and $\Lambda$ is the
linearization at $x$. -/
theorem complementarityModel_expansion {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x)
    (s : E) :
    complementarityModel a b x s = complementarityMerit (a x) (b x) +
      fderiv ℝ (fun y ↦ complementarityMerit (a y) (b y)) x s +
      (∑ i, complementarityLinearization a b x s i ^ 2) / 2 := by
  rw [(hasFDerivAt_complementarityMerit ha hb).fderiv]
  simp only [complementarityModel, complementarityMerit, Finset.sum_div,
    sum_apply, smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [complementarityLinearization, ContinuousLinearMap.pi_apply]
  ring

/-- A pair $(\alpha, \beta) \in \mathbb{R}^2$ is **componentwise complementary** if $\alpha \ge 0$,
$\beta \ge 0$ and $\alpha \beta = 0$. The indices with this property form the set $J_C$ of
Theorem 16.3.1. -/
def IsComplementaryComponent (a b : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ a * b = 0

/-- **Theorem 16.3.1** of [conn2000trust], sign conditions. For $a, b, v \in \mathbb{R}^\iota$, the
vector $v$ **has the regularity signs** if for every $i$:

* $v_i = 0$ if $(a_i, b_i)$ is componentwise complementary (the set $J_C$);
* $v_i > 0$ if $a_i > 0$ and $b_i > 0$ (the set $J_+$);
* $v_i < 0$ in all other cases (the set $J_-$). -/
def HasRegularitySigns {ι : Type*} (a b v : ι → ℝ) : Prop :=
  ∀ i, (IsComplementaryComponent (a i) (b i) → v i = 0) ∧
    (0 < a i → 0 < b i → 0 < v i) ∧
    (¬ IsComplementaryComponent (a i) (b i) → ¬ (0 < a i ∧ 0 < b i) → v i < 0)

/-- **Theorem 16.3.1** of [conn2000trust], regularity. Let $a, b : E \to \mathbb{R}^\iota$ and
$x \in E$. The point $x$ is **regular** if for all nonzero $u, v \in \mathbb{R}^\iota$ that have
the regularity signs at $(a(x), b(x))$,
$$\sum_i \bigl(u_i \nabla a_i(x) + v_i \nabla b_i(x)\bigr) \neq 0.$$

With Jacobians that map input directions to output directions, the condition uses their
transposes. It is written as a sum of the component derivative functionals. -/
def ComplementarityRegular {ι : Type*} [Fintype ι] (a b : E → ι → ℝ) (x : E) : Prop :=
  ∀ u v : ι → ℝ, u ≠ 0 → v ≠ 0 →
    HasRegularitySigns (a x) (b x) u → HasRegularitySigns (a x) (b x) v →
    (∑ i, (u i • fderiv ℝ (a · i) x + v i • fderiv ℝ (b · i) x)) ≠ 0

private theorem coefficient_neg_of_other_ne_zero {a b : ℝ} (hb : b ≠ 0) :
    complementarityCoefficient a b < 0 := by
  have hs := Real.sqrt_pos.2 (radicand_pos (Or.inr hb : a ≠ 0 ∨ b ≠ 0))
  have hlt : a < √(a ^ 2 + b ^ 2) := by
    by_cases ha : 0 ≤ a
    · exact (Real.lt_sqrt ha).2 (lt_add_of_pos_right _ (sq_pos_of_ne_zero hb))
    · linarith
  unfold complementarityCoefficient
  linarith [(div_lt_one hs).2 hlt]

private theorem coefficient_neg_of_neg {a b : ℝ} (ha : a < 0) :
    complementarityCoefficient a b < 0 := by
  unfold complementarityCoefficient
  have hs := Real.sqrt_pos.2 (radicand_pos (Or.inl ha.ne : a ≠ 0 ∨ b ≠ 0))
  linarith [div_neg_of_neg_of_pos ha hs]

private theorem weighted_coefficient_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < complementarityCoefficient a b * fischerBurmeister a b := by
  apply mul_pos_of_neg_of_neg (coefficient_neg_of_other_ne_zero hb.ne')
  have hs : √(a ^ 2 + b ^ 2) < a + b :=
    (Real.sqrt_lt (by positivity) (by positivity)).2 (by nlinarith [mul_pos ha hb])
  change √(a ^ 2 + b ^ 2) - a - b < 0
  linarith

private theorem weighted_coefficient_neg {a b : ℝ} (h : a < 0 ∨ b < 0) :
    complementarityCoefficient a b * fischerBurmeister a b < 0 := by
  apply mul_neg_of_neg_of_pos
  · exact h.elim coefficient_neg_of_neg (fun hb ↦ coefficient_neg_of_other_ne_zero hb.ne)
  · have hs₁ : a ≤ √(a ^ 2 + b ^ 2) := by
      by_cases ha : 0 ≤ a
      · exact (Real.le_sqrt ha (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg b))
      · exact (le_of_not_ge ha).trans (Real.sqrt_nonneg _)
    have hs₂ : b ≤ √(a ^ 2 + b ^ 2) := by
      by_cases hb : 0 ≤ b
      · exact (Real.le_sqrt hb (by positivity)).2 (le_add_of_nonneg_left (sq_nonneg a))
      · exact (le_of_not_ge hb).trans (Real.sqrt_nonneg _)
    change 0 < √(a ^ 2 + b ^ 2) - a - b
    rcases h with ha | hb <;> linarith

private theorem weighted_coefficients_signs {ι : Type*} (a b : ι → ℝ) :
    HasRegularitySigns a b
      (fun i ↦ complementarityCoefficient (a i) (b i) * complementarityResidual a b i) ∧
    HasRegularitySigns a b
      (fun i ↦ complementarityCoefficient (b i) (a i) * complementarityResidual a b i) := by
  have hneg {a b : ℝ} (hc : ¬ IsComplementaryComponent a b)
      (hp : ¬ (0 < a ∧ 0 < b)) : a < 0 ∨ b < 0 := by
    by_contra! h
    have ha : a = 0 ∨ b = 0 := by
      rcases eq_or_lt_of_le h.1 with ha | ha
      · exact Or.inl ha.symm
      · exact Or.inr (le_antisymm (le_of_not_gt (fun hb ↦ hp ⟨ha, hb⟩)) h.2)
    exact hc ⟨h.1, h.2, mul_eq_zero.2 ha⟩
  have hsymm (a b : ℝ) : fischerBurmeister a b = fischerBurmeister b a := by
    change √(a ^ 2 + b ^ 2) - a - b = √(b ^ 2 + a ^ 2) - b - a
    rw [add_comm (b ^ 2)]
    ring
  constructor
  · intro i
    exact ⟨fun hc ↦ mul_eq_zero.2
      (Or.inr (Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 hc)),
      weighted_coefficient_pos, fun hc hp ↦ weighted_coefficient_neg (hneg hc hp)⟩
  · intro i
    refine ⟨fun hc ↦ mul_eq_zero.2
      (Or.inr (Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 hc)), ?_, ?_⟩
    · intro ha hb
      simp only [complementarityResidual]
      rw [hsymm (a i) (b i)]
      exact weighted_coefficient_pos hb ha
    · intro hc hp
      simp only [complementarityResidual]
      rw [hsymm (a i) (b i)]
      exact weighted_coefficient_neg (Or.symm (hneg hc hp))

/-- **Theorem 16.3.1** of [conn2000trust]. Let $a, b : E \to \mathbb{R}^\iota$ have differentiable
components at $x$. Then $a(x)$ and $b(x)$ are complementary if and only if $x$ is regular and
the derivative of the merit function $y \mapsto \frac{1}{2} \|\Phi(a(y), b(y))\|^2$ at $x$ is
$0$.

The derivative is the functional of (16.3.8), which uses the transposes of the component
Jacobians. Regularity is `ConnGouldToint.Chapter16.ComplementarityRegular`. -/
theorem theorem_16_3_1 {ι : Type*} [Fintype ι] {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x) :
    IsComplementary (a x) (b x) ↔ ComplementarityRegular a b x ∧
      fderiv ℝ (fun y ↦ complementarityMerit (a y) (b y)) x = 0 := by
  have hd := (hasFDerivAt_complementarityMerit ha hb).fderiv
  constructor
  · intro hc
    have hz := complementarityResidual_eq_zero_iff.2 hc
    refine ⟨?_, by rw [hd, hz]; simp⟩
    intro u v hu _ hsu _
    exfalso
    apply hu
    funext i
    exact (hsu i).1 (Numlib.Optimization.fischerBurmeister_eq_zero_iff.1 (congrFun hz i))
  · rintro ⟨hregular, hcritical⟩
    by_contra hc
    let u (i : ι) := complementarityCoefficient (a x i) (b x i) *
      complementarityResidual (a x) (b x) i
    let v (i : ι) := complementarityCoefficient (b x i) (a x i) *
      complementarityResidual (a x) (b x) i
    have hs := weighted_coefficients_signs (a x) (b x)
    have hi : ∃ i, ¬ IsComplementaryComponent (a x i) (b x i) := by
      by_contra! h
      exact hc (complementarityResidual_eq_zero_iff.1
        (funext fun i ↦ Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 (h i)))
    obtain ⟨i, hi⟩ := hi
    have hne {w : ι → ℝ} (hw : HasRegularitySigns (a x) (b x) w) : w ≠ 0 := by
      intro h
      have hwi : w i = 0 := congrFun h i
      by_cases hp : 0 < a x i ∧ 0 < b x i
      · exact (ne_of_gt ((hw i).2.1 hp.1 hp.2)) hwi
      · exact (ne_of_lt ((hw i).2.2 hi hp)) hwi
    apply hregular u v (hne hs.1) (hne hs.2) hs.1 hs.2
    rw [hd] at hcritical
    simpa only [u, v, smul_add, smul_smul, mul_comm] using hcritical

end ConnGouldToint.Chapter16
