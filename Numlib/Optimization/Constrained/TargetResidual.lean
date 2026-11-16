/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.HalfNormSqDeriv
import Numlib.Optimization.Constrained
import Numlib.Optimization.Optimality.ConstrainedMeasure

/-!
# The target reformulation of an equality-constrained problem

Let $f : E \to \mathbb{R}$ and $c : E \to F$, where $F$ is a real inner product space (the space
$\mathbb{R}^m$ of the source), and let $t \in \mathbb{R}$ be a target. The two-phase methods of
[cartis2022evaluation], §7.2 and §14.3, minimize the norm of the residual
$r(x, t) = (c(x), f(x) - t)$, by (7.2.4)–(7.2.6):
$$\|r(x, t)\| = \sqrt{\|c(x)\|^2 + (f(x) - t)^2}, \qquad \mu_2(x, t) = \tfrac12 \|r(x, t)\|^2.$$
This file defines these functions and the multiplier estimate $y = -c(x) / (f(x) - t)$. It computes
the derivatives of $\mu_2(\cdot, t)$ up to order three, and it relates the derivatives, the Taylor
decrements and the Taylor measures of $\mu_2(\cdot, t)$ to those of the Lagrangian $\mathcal{L}(z,
y) = f(z) - \langle y, c(z) \rangle$, as in the proofs of Lemmas 7.2.1 and 14.3.5. It also proves
Theorem 7.1.1 and Lemma B.7.1 of [cartis2022evaluation].

## Main definitions

* `Constrained.targetResidual`: the residual norm $\|r(x, t)\|$.
* `Constrained.targetMerit`: the merit function $\mu_2(x, t) = \frac12 \|r(x, t)\|^2$.
* `Constrained.targetMultiplier`: the multiplier estimate $y = -c(x) / (f(x) - t)$ of (7.2.22) and
  (14.3.53).
* `Constrained.targetSublevel`: the set $\{x \in X : \|r(x, t)\| \le 1\}$.

## Main results

* `Constrained.fderiv_targetMerit`: $\nabla_x \mu_2 = (f - t) \nabla f + (Dc)^* c$; the diagonal
  second and third derivatives (14.3.38)–(14.3.39) are
  `Constrained.iteratedFDeriv_two_targetMerit_apply` and
  `Constrained.iteratedFDeriv_three_targetMerit_apply`.
* `Constrained.fderiv_targetMerit_eq_smul_lagrangian`: with $y$ the multiplier estimate, $\nabla_x
  \mu_2 = (f(x) - t) \nabla_x \mathcal{L}(x, y)$. Together with
  `Constrained.targetResidual_div_eq_sqrt`, which gives $\|r(x, t)\| / (f(x) - t) = \|(y, 1)\|$, and
  the corresponding identities between Taylor measures and criticality measures, this is the core of
  the proofs of Lemmas 7.2.1 and 14.3.5.
* `Constrained.taylorMeasure_lagrangian_two_le`, `Constrained.taylorMeasure_lagrangian_three_le`:
  the second- and third-order measure relations of the proof of Lemma 14.3.5, with the extra term
  $(\nabla f(x)[d])^2 / (2(f(x) - t))$.
* `Constrained.iteratedFDerivHolderOn_targetMerit_of_mem_Icc`: the derivatives of $\mu_2(\cdot, t)$
  have Hölder (or Lipschitz) constants that are uniform over an interval of targets, the core of
  Lemma 7.2.5.
* `neg_add_sqrt_sq_sub_sq_ge`: the inequality of Lemma B.7.1.
* `Constrained.isMinOn_of_isMinOn_sub_inner`: sufficiency of the Lagrangian, Theorem 7.1.1.

## Notation

* $\Delta T_{\phi, j}(d)$: the Taylor decrement $T_{\phi,j}(x, 0) - T_{\phi,j}(x, d)$ of order $j$
  of $\phi$ at $x$, which is `FormalMultilinearSeries.taylorDecrement` of `ftaylorSeries ℝ φ x`.
* $\varphi^\delta_{\phi, S, j}$: the Taylor measure `Optimization.taylorMeasure` of order $j$ of
  $\phi$ at $x$, the supremum of $\Delta T_{\phi, j}(d)$ over $\|d\| \le \delta$, $d \in S$.

## Implementation notes

* The pair $r(x, t)$ is never formed as an element of a product space, because the Mathlib product
  `F × ℝ` carries the sup norm. The Euclidean norm is defined directly.
* The Lagrangian $\mathcal{L}(x, y) = f(x) - \langle y, c(x) \rangle$ of the source is
  `Constrained.innerLagrangian f c y`, a reducible abbreviation of `fun z => f z - ⟪y, c z⟫`; the
  statements below are written in this form. Its multipliers enter with the sign opposite to that of
  `Constrained.lagrangian` (`Constrained.innerLagrangian_apply_eq_lagrangian`).
* On $T(x) = \ker \nabla c(x)$ the derivative of the Lagrangian is
  $\nabla_x \mathcal{L}(x, y)[d] = \nabla f(x)[d]$. The second- and third-order relations (14.3.43)
  and (14.3.46) therefore contain the extra term $(\nabla f(x)[d])^2 / (2(f(x) - t))$, and the
  statements below carry this term explicitly.
-/

open Set Metric Filter Finset
open scoped Topology RealInnerProductSpace Nat

/-! ### Lemma B.7.1 -/

/-- **Lemma B.7.1** of [cartis2022evaluation]. Let $0 \le \omega \le \varepsilon$, and let
$u, v \in \mathbb{R}$ with $u^2 + v^2 \le \omega^2$. Then
$$\varepsilon - \omega \le -u + \sqrt{\varepsilon^2 - v^2}.$$
That is, the minimum of $\psi(u, v) = -u + \sqrt{\varepsilon^2 - v^2}$ over the disc
$u^2 + v^2 \le \omega^2$ is $\varepsilon - \omega$, attained at $(\omega, 0)$.

The proof uses $u \le \sqrt{\omega^2 - v^2}$ and $\sqrt{\varepsilon^2 - v^2} - \sqrt{\omega^2 -
v^2} \ge \varepsilon - \omega$ instead of the Karush–Kuhn–Tucker conditions. -/
theorem neg_add_sqrt_sq_sub_sq_ge {ω ε u v : ℝ} (hω : 0 ≤ ω) (hωε : ω ≤ ε)
    (huv : u ^ 2 + v ^ 2 ≤ ω ^ 2) : ε - ω ≤ -u + √(ε ^ 2 - v ^ 2) := by
  set b := √(ω ^ 2 - v ^ 2) with hb
  have hvω : v ^ 2 ≤ ω ^ 2 := by nlinarith
  have hb2 : b ^ 2 = ω ^ 2 - v ^ 2 := Real.sq_sqrt (by linarith)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbω : b ≤ ω := by
    rw [hb, Real.sqrt_le_left hω]
    nlinarith
  have hub : u ≤ b := (le_abs_self u).trans (Real.abs_le_sqrt (by linarith))
  have hab : ε - ω + b ≤ √(ε ^ 2 - v ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

/-- The value in Lemma B.7.1 of [cartis2022evaluation] at the minimizer $(\omega, 0)$: for
$\varepsilon \ge 0$, $-\omega + \sqrt{\varepsilon^2 - 0^2} = \varepsilon - \omega$. -/
theorem neg_add_sqrt_sq_sub_zero_sq {ω ε : ℝ} (hε : 0 ≤ ε) :
    -ω + √(ε ^ 2 - 0 ^ 2) = ε - ω := by
  rw [zero_pow two_ne_zero, sub_zero, Real.sqrt_sq hε]
  ring

namespace Constrained

/-! ### Theorem 7.1.1 -/

/-- **Theorem 7.1.1** of [cartis2022evaluation] (sufficiency of the Lagrangian). Let $F$ be a real
inner product space, let $f : E \to \mathbb{R}$, $c : E \to F$, $S \subseteq E$, $x \in E$ and
$y \in F$. If $c(x) = 0$ and $x$ minimizes the Lagrangian
$z \mapsto f(z) - \langle y, c(z) \rangle$ over $S$, then $x$ minimizes $f$ over the feasible
part $\{z \in S : c(z) = 0\}$ of $S$.

The set $S$ need not be closed. -/
theorem isMinOn_of_isMinOn_sub_inner {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → ℝ} {c : E → F} {S : Set E} {x : E} {y : F}
    (hcx : c x = 0) (hmin : IsMinOn (fun z => f z - ⟪y, c z⟫) S x) :
    IsMinOn f {z ∈ S | c z = 0} x := by
  intro z hz
  have h := hmin hz.1
  simp only [mem_ofPred_eq, hcx, hz.2, inner_zero_right, sub_zero] at h
  exact h

/-! ### The residual and the merit function -/

section Defs

variable {E F : Type*} [NormedAddCommGroup F]

/-- The **target residual norm** of [cartis2022evaluation], (7.2.4):
$$\|r(x, t)\| = \sqrt{\|c(x)\|^2 + (f(x) - t)^2},$$
the Euclidean norm of the pair $r(x, t) = (c(x), f(x) - t)$. -/
noncomputable def targetResidual (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : ℝ :=
  √(‖c x‖ ^ 2 + (f x - t) ^ 2)

/-- The **target merit function** of [cartis2022evaluation], (7.2.5):
$$\mu_2(x, t) = \tfrac12 \|r(x, t)\|^2 = \tfrac12 (\|c(x)\|^2 + (f(x) - t)^2).$$
It is also the function $\mu(x, t)$ of (14.3.30). -/
noncomputable def targetMerit (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : ℝ :=
  (‖c x‖ ^ 2 + (f x - t) ^ 2) / 2

variable {f : E → ℝ} {c : E → F} {t t' : ℝ} {x x' : E}

/-- The target residual norm is $\|r(x, t)\| = \sqrt{\|c(x)\|^2 + (f(x) - t)^2}$. -/
theorem targetResidual_def :
    targetResidual f c t x = √(‖c x‖ ^ 2 + (f x - t) ^ 2) := rfl

/-- The target merit function is $\mu_2(x, t) = (\|c(x)\|^2 + (f(x) - t)^2) / 2$. -/
theorem targetMerit_def : targetMerit f c t x = (‖c x‖ ^ 2 + (f x - t) ^ 2) / 2 := rfl

/-- The target residual norm is nonnegative. -/
theorem targetResidual_nonneg : 0 ≤ targetResidual f c t x := Real.sqrt_nonneg _

/-- The square of the target residual norm is $\|r(x, t)\|^2 = \|c(x)\|^2 + (f(x) - t)^2$. -/
theorem targetResidual_sq : targetResidual f c t x ^ 2 = ‖c x‖ ^ 2 + (f x - t) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The merit function is half the square of the residual norm:
$\mu_2(x, t) = \frac12 \|r(x, t)\|^2$. -/
theorem targetMerit_eq : targetMerit f c t x = targetResidual f c t x ^ 2 / 2 := by
  rw [targetResidual_sq, targetMerit_def]

/-- The target merit function is nonnegative. -/
theorem targetMerit_nonneg : 0 ≤ targetMerit f c t x := by
  rw [targetMerit_eq]
  positivity

/-- The constraint violation is at most the residual norm: $\|c(x)\| \le \|r(x, t)\|$. -/
theorem norm_le_targetResidual : ‖c x‖ ≤ targetResidual f c t x :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (f x - t)])

/-- The distance to the target is at most the residual norm: $|f(x) - t| \le \|r(x, t)\|$. -/
theorem abs_sub_le_targetResidual : |f x - t| ≤ targetResidual f c t x :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖c x‖])

/-- The excess over the target is at most the residual norm: $f(x) - t \le \|r(x, t)\|$. -/
theorem sub_le_targetResidual : f x - t ≤ targetResidual f c t x :=
  (le_abs_self _).trans abs_sub_le_targetResidual

/-- The residual depends on $t$ only through $|f(x) - t|$: reflecting the target through $f(x)$ does
not change it, $\|r(x, 2 f(x) - t)\| = \|r(x, t)\|$. This is used in (7.2.18)–(7.2.19) of
[cartis2022evaluation]. -/
theorem targetResidual_two_mul_sub :
    targetResidual f c (2 * f x - t) x = targetResidual f c t x := by
  simp only [targetResidual_def]
  congr 1
  ring

/-- Let $\varepsilon \ge 0$ and $\|c(x)\| \le \varepsilon$. Resetting the target to
$t = f(x) - \sqrt{\varepsilon^2 - \|c(x)\|^2}$ gives the residual norm
$\|r(x, t)\| = \varepsilon$. This is the target update of (7.2.11) and (7.2.27) of
[cartis2022evaluation]. -/
theorem targetResidual_sub_sqrt {ε : ℝ} (hε : 0 ≤ ε) (hc : ‖c x‖ ≤ ε) :
    targetResidual f c (f x - √(ε ^ 2 - ‖c x‖ ^ 2)) x = ε := by
  have h : 0 ≤ ε ^ 2 - ‖c x‖ ^ 2 := by nlinarith [norm_nonneg (c x)]
  rw [targetResidual_def, sub_sub_cancel, Real.sq_sqrt h, add_sub_cancel, Real.sqrt_sq hε]

/-- At the target $t = f(x)$ the residual norm is the constraint violation:
$\|r(x, f(x))\| = \|c(x)\|$. -/
@[simp]
theorem targetResidual_self : targetResidual f c (f x) x = ‖c x‖ := by
  simp [targetResidual_def, Real.sqrt_sq (norm_nonneg _)]

/-- At the target $t = f(x)$ the merit function is $\Phi_2(x) = \frac12 \|c(x)\|^2$. -/
@[simp]
theorem targetMerit_self : targetMerit f c (f x) x = ‖c x‖ ^ 2 / 2 := by
  simp [targetMerit_def]

/-- Comparing merit values is comparing residual norms: $\mu_2(x, t) \le \mu_2(x', t')$ if and only
if $\|r(x, t)\| \le \|r(x', t')\|$. -/
theorem targetMerit_le_targetMerit_iff :
    targetMerit f c t x ≤ targetMerit f c t' x' ↔
      targetResidual f c t x ≤ targetResidual f c t' x' := by
  rw [targetMerit_eq, targetMerit_eq, div_le_div_iff_of_pos_right two_pos,
    pow_le_pow_iff_left₀ targetResidual_nonneg targetResidual_nonneg two_ne_zero]

/-- Comparing merit values is comparing residual norms, strict form: $\mu_2(x, t) < \mu_2(x', t')$
if and only if $\|r(x, t)\| < \|r(x', t')\|$. -/
theorem targetMerit_lt_targetMerit_iff :
    targetMerit f c t x < targetMerit f c t' x' ↔
      targetResidual f c t x < targetResidual f c t' x' := by
  rw [← not_le, targetMerit_le_targetMerit_iff, not_le]

/-- The merit function is affine in the target up to a quadratic term in $t$ alone:
$\mu_2(x, t) = \mu_2(x, 0) - t f(x) + t^2 / 2$. -/
theorem targetMerit_eq_sub : targetMerit f c t x = targetMerit f c 0 x - t * f x + t ^ 2 / 2 := by
  simp only [targetMerit_def]
  ring

/-- The **target sublevel set** $\{x \in X : \|r(x, t)\| \le 1\}$, on which the merit function
$\mu(\cdot, t)$ is controlled in Lemma 14.3.6(ii) of [cartis2022evaluation]. -/
def targetSublevel (f : E → ℝ) (c : E → F) (X : Set E) (t : ℝ) : Set E :=
  {x ∈ X | targetResidual f c t x ≤ 1}

/-- A point $x$ is in the target sublevel set if and only if $x \in X$ and $\|r(x, t)\| \le 1$. -/
theorem mem_targetSublevel {X : Set E} :
    x ∈ targetSublevel f c X t ↔ x ∈ X ∧ targetResidual f c t x ≤ 1 := Iff.rfl

end Defs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- The **multiplier estimate** $y = -c(x) / (f(x) - t)$ of [cartis2022evaluation], (7.2.22) and
(14.3.53).

It is meaningful only when $f(x) \neq t$. For $f(x) = t$ it has the value $0$, by the convention
$0^{-1} = 0$. -/
noncomputable def targetMultiplier (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : F :=
  -(f x - t)⁻¹ • c x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The multiplier estimate is $y = -(f(x) - t)^{-1} c(x)$. -/
theorem targetMultiplier_def {f : E → ℝ} {c : E → F} {t : ℝ} {x : E} :
    targetMultiplier f c t x = -(f x - t)⁻¹ • c x := rfl

/-! ### Derivatives of the merit function -/

section Deriv

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}

/-- If $f$ and $c$ are $C^n$ at $x$, then $\mu_2(\cdot, t)$ is $C^n$ at $x$. -/
theorem contDiffAt_targetMerit {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x)
    (hc : ContDiffAt ℝ n c x) : ContDiffAt ℝ n (targetMerit f c t) x := by
  have : targetMerit f c t = fun z => (‖c z‖ ^ 2 + (f z - t) ^ 2) / 2 := rfl
  rw [this]
  exact ((hc.norm_sq ℝ).add ((hf.sub contDiffAt_const).pow 2)).div_const _

/-- **The derivative of the merit function.** Let $f$ and $c$ have the derivatives $f'$ and $c'$ at
$x$. Then $\mu_2(\cdot, t)$ has the derivative
$$\nabla_x \mu_2(x, t) = (f(x) - t) f' + (c')^* c(x)$$
at $x$, where $(c')^* c(x)$ is the functional $d \mapsto \langle c(x), c' d \rangle$. This is
used in the proof of Lemma 7.2.1 and in (14.3.37) of [cartis2022evaluation]. -/
theorem hasFDerivAt_targetMerit {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F} (hf : HasFDerivAt f f' x)
    (hc : HasFDerivAt c c' x) :
    HasFDerivAt (targetMerit f c t) ((f x - t) • f' + (innerSL ℝ (c x)).comp c') x := by
  have h1 := hc.norm_sq
  have h2 := (hf.sub_const t).pow 2
  have h := (h1.add h2).const_smul (2⁻¹ : ℝ)
  have hfun : targetMerit f c t =
      (2⁻¹ : ℝ) • ((fun x => ‖c x‖ ^ 2) + fun x => (f x - t) ^ 2) := by
    funext z
    simp only [targetMerit_def, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hfun]
  refine h.congr_fderiv ?_
  ext d
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  simp
  ring

/-- **The derivative of the merit function.** Let $f$ and $c$ be differentiable at $x$. Then
$$\nabla_x \mu_2(x, t) = (f(x) - t) \nabla f(x) + (Dc(x))^* c(x),$$
where $(Dc(x))^* c(x)$ is the functional $d \mapsto \langle c(x), Dc(x)[d] \rangle$. This is
used in the proof of Lemma 7.2.1 and in (14.3.37) of [cartis2022evaluation]. -/
theorem fderiv_targetMerit (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    fderiv ℝ (targetMerit f c t) x =
      (f x - t) • fderiv ℝ f x + (innerSL ℝ (c x)).comp (fderiv ℝ c x) :=
  (hasFDerivAt_targetMerit hf.hasFDerivAt hc.hasFDerivAt).fderiv

/-- **The first-order Taylor decrement of the merit function.** Let $f$ and $c$ have the derivatives
$f'$ and $c'$ at $x$. Then for every direction $d$,
$$\Delta T_{\mu, 1}(d) = -\big((f(x) - t) f'(d) + \langle c(x), c'(d) \rangle\big).$$
-/
theorem taylorDecrement_one_targetMerit {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x) (d : E) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 1 d =
      -((f x - t) * f' d + ⟪c x, c' d⟫) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply, (hasFDerivAt_targetMerit hf hc).fderiv]
  simp

/-- Let $f$ and $c$ be differentiable at $x$, and let $f(x) = t$. Then the derivative of
$\mu_2(\cdot, t)$ at $x$ is the derivative of $\Phi_2 = \frac12 \|c\|^2$ at $x$. This is the
case $f(x_\varepsilon) = t_\varepsilon$ in the proof of Lemma 7.2.1 of [cartis2022evaluation]. -/
theorem fderiv_targetMerit_of_eq (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (ht : f x = t) :
    fderiv ℝ (targetMerit f c t) x = fderiv ℝ (fun z => ‖c z‖ ^ 2 / 2) x := by
  rw [fderiv_targetMerit hf hc, ht, sub_self, zero_smul, zero_add]
  have h : fderiv ℝ (fun z => ‖c z‖ ^ 2 / 2) x =
      (2⁻¹ : ℝ) • (2 • (innerSL ℝ (c x)).comp (fderiv ℝ c x)) := by
    have hfun : (fun z => ‖c z‖ ^ 2 / 2) = (2⁻¹ : ℝ) • fun z => ‖c z‖ ^ 2 := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact (hc.hasFDerivAt.norm_sq.const_smul (2⁻¹ : ℝ)).fderiv
  rw [h]
  ext d
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply]
  simp

/-- The dependence of the derivatives of $\mu_2(\cdot, t)$ on the target: let $j \ge 1$, and let $f$
and $c$ be $C^j$ at $x$. Then $\nabla^j \mu_2(x, t) = \nabla^j \mu_2(x, 0) - t \nabla^j f(x)$. -/
theorem iteratedFDeriv_targetMerit_eq_sub {j : ℕ} (hj : j ≠ 0) (hf : ContDiffAt ℝ j f x)
    (hc : ContDiffAt ℝ j c x) :
    iteratedFDeriv ℝ j (targetMerit f c t) x =
      iteratedFDeriv ℝ j (targetMerit f c 0) x - t • iteratedFDeriv ℝ j f x := by
  have hfun : targetMerit f c t =
      (targetMerit f c 0 + (-t) • f) + fun _ => t ^ 2 / 2 := by
    funext z
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, targetMerit_eq_sub, smul_eq_mul]
    ring
  have h0 : ContDiffAt ℝ j (targetMerit f c 0) x := contDiffAt_targetMerit hf hc
  have h1 : ContDiffAt ℝ j ((-t) • f) x := by
    change ContDiffAt ℝ j (fun y => (-t) • f y) x
    exact hf.const_smul _
  have h2 : ContDiffAt ℝ j (targetMerit f c 0 + (-t) • f) x := h0.add h1
  rw [hfun, iteratedFDeriv_add_apply h2 contDiffAt_const, iteratedFDeriv_add_apply h0 h1,
    iteratedFDeriv_const_smul_apply hf, neg_smul, ← sub_eq_add_neg]
  rw [iteratedFDeriv_const_of_ne hj, Pi.zero_apply, add_zero]

end Deriv

/-! ### The multiplier estimate and the Lagrangian -/

section Multiplier

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}

/-- **The derivative of the Lagrangian** $z \mapsto f(z) - \langle y, c(z) \rangle$ of
[cartis2022evaluation], (1.1.1). Let $f$ and $c$ have the derivatives $f'$ and $c'$ at $x$, and
let $y \in F$. Then the Lagrangian has the derivative $f' - (c')^* y$ at $x$, where $(c')^* y$
is the functional $d \mapsto \langle y, c' d \rangle$. -/
theorem hasFDerivAt_sub_inner {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F} (y : F) (hf : HasFDerivAt f f' x)
    (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun z => f z - ⟪y, c z⟫) (f' - (innerSL ℝ y).comp c') x :=
  hf.sub ((innerSL ℝ y).hasFDerivAt.comp x hc)

/-- **The multiplier identity.** Let $f$ and $c$ be differentiable at $x$, let $f(x) \neq t$, and
let $y = -c(x) / (f(x) - t)$ be the multiplier estimate. Then
$$\nabla_x \mu_2(x, t) = (f(x) - t) \nabla_x \mathcal{L}(x, y)$$
for the Lagrangian $\mathcal{L}(z, y) = f(z) - \langle y, c(z) \rangle$. This is (7.2.22) with
the proof of Lemma 7.2.1, and (14.3.53)–(14.3.54), of [cartis2022evaluation]. -/
theorem fderiv_targetMerit_eq_smul_lagrangian (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x ≠ t) :
    fderiv ℝ (targetMerit f c t) x =
      (f x - t) • fderiv ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x := by
  have hτ : f x - t ≠ 0 := sub_ne_zero.2 ht
  rw [fderiv_targetMerit hf hc,
    (hasFDerivAt_sub_inner (targetMultiplier f c t x) hf.hasFDerivAt hc.hasFDerivAt).fderiv]
  ext d
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, targetMultiplier_def, inner_smul_left]
  simp only [conj_trivial]
  field_simp
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The scaling of the approximate Karush–Kuhn–Tucker condition** (7.1.4), from the proof of Lemma
7.2.1 of [cartis2022evaluation]. Let $t < f(x)$ and let $y = -c(x) / (f(x) - t)$ be the
multiplier estimate. Then
$$\frac{\|r(x, t)\|}{f(x) - t} = \|(y, 1)\| = \sqrt{\|y\|^2 + 1}.$$
-/
theorem targetResidual_div_eq_sqrt (ht : t < f x) :
    targetResidual f c t x / (f x - t) = √(‖targetMultiplier f c t x‖ ^ 2 + 1) := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  have h : ‖targetMultiplier f c t x‖ ^ 2 + 1 = (‖c x‖ ^ 2 + (f x - t) ^ 2) / (f x - t) ^ 2 := by
    rw [targetMultiplier_def, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hτ.le]
    field_simp
  rw [h, Real.sqrt_div (by positivity), Real.sqrt_sq hτ.le, targetResidual_def]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For the multiplier estimate $y$, $\langle y, c(x) \rangle = -\|c(x)\|^2 / (f(x) - t)$. This is
the remark after the proof of Lemma 14.3.5 of [cartis2022evaluation].

For $f(x) = t$ both sides are $0$. -/
theorem inner_targetMultiplier :
    ⟪targetMultiplier f c t x, c x⟫ = -(‖c x‖ ^ 2 / (f x - t)) := by
  rw [targetMultiplier_def, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- If $t \le f(x)$, the multiplier estimate $y$ satisfies $\langle y, c(x) \rangle \le 0$. This is
the remark after the proof of Lemma 14.3.5 of [cartis2022evaluation]. -/
theorem inner_targetMultiplier_nonpos (ht : t ≤ f x) : ⟪targetMultiplier f c t x, c x⟫ ≤ 0 := by
  rw [inner_targetMultiplier, neg_nonpos]
  exact div_nonneg (sq_nonneg _) (sub_nonneg.2 ht)

/-- Let $f$ and $c$ be differentiable at $x$, let $f(x) \neq t$, and let $y$ be the multiplier
estimate. Then the first derivatives, as $1$-linear maps, satisfy $\nabla_x \mu_2(x, t) =
(f(x) - t) \nabla_x \mathcal{L}(x, y)$. -/
theorem iteratedFDeriv_one_targetMerit_eq_smul (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x ≠ t) :
    iteratedFDeriv ℝ 1 (targetMerit f c t) x =
      (f x - t) • iteratedFDeriv ℝ 1 (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x := by
  ext m
  rw [smul_apply, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
    fderiv_targetMerit_eq_smul_lagrangian hf hc ht, smul_apply]

/-- **First-order criticality measures of $\mu_2$ and of the Lagrangian**, from the proof of Lemma
7.2.1 of [cartis2022evaluation]. Let $f$ and $c$ be differentiable at $x$, let $t < f(x)$, and
let $y = -c(x) / (f(x) - t)$ be the multiplier estimate. Then for every set $T$ of admissible
displacements, the criticality measures (7.1.2) satisfy
$$\omega_{\mu_2}(x, t) = (f(x) - t)\, \omega_{\mathcal{L}}(x, y).$$

The criticality measure of a $j$-linear form $A$ over $T$ is `Optimization.formCriticality`, the
supremum of $-A[d]^j$ over $d \in T$ with $\|d\| \le 1$; here $j = 1$ and $A$ is the first
derivative. -/
theorem formCriticality_targetMerit_eq_mul (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : t < f x) (T : Set E) :
    Optimization.formCriticality (iteratedFDeriv ℝ 1 (targetMerit f c t) x) T =
      (f x - t) * Optimization.formCriticality
        (iteratedFDeriv ℝ 1 (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) T := by
  rw [iteratedFDeriv_one_targetMerit_eq_smul hf hc ht.ne',
    Optimization.formCriticality_smul _ (sub_nonneg.2 ht.le)]

/-- **First-order Taylor measures of $\mu_2$ and of the Lagrangian**, (14.3.53)–(14.3.54) and Lemma
14.3.5 for $j = 1$ of [cartis2022evaluation]. Let $f$ and $c$ be differentiable at $x$, let
$t < f(x)$, and let $y = -c(x) / (f(x) - t)$ be the multiplier estimate. Then for every radius
$\delta$ and every set $S$ of directions,
$$\varphi^\delta_{\mathcal{L}, S, 1}(x, y) = \frac{\varphi^\delta_{\mu, S, 1}(x, t)}{f(x) -
  t}.$$
-/
theorem taylorMeasure_lagrangian_one_eq (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : t < f x) (δ : ℝ) (S : Set E) :
    Optimization.taylorMeasure
        (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 1 δ S =
      (f x - t)⁻¹ * Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 1 δ S := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  rw [Optimization.taylorMeasure, Optimization.taylorMeasure,
    ← Optimization.decrementMeasure_const_mul (inv_nonneg.2 hτ.le)]
  congr 1
  funext d
  simp only [FormalMultilinearSeries.taylorDecrement_one_apply, ftaylorSeries,
    iteratedFDeriv_one_targetMerit_eq_smul hf hc ht.ne', smul_apply,
    smul_eq_mul]
  field_simp

end Multiplier

/-! ### Uniform Hölder constants over an interval of targets (Lemma 7.2.5) -/

section Holder

variable {f : E → ℝ} {c : E → F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] in
/-- Let $t_1 < t_2$ and $t \in \mathbb{R}$, and let $\theta = (t - t_1) / (t_2 - t_1)$. Then
$$\mu_2(\cdot, t) = (1 - \theta) \mu_2(\cdot, t_1) + \theta \mu_2(\cdot, t_2) + \tfrac12
  \big(t^2 - (1 - \theta) t_1^2 - \theta t_2^2\big).$$
For $t \in [t_1, t_2]$ this is a convex combination of $\mu_2(\cdot, t_1)$ and
$\mu_2(\cdot, t_2)$ plus a constant. -/
theorem targetMerit_eq_lineMap {t₁ t₂ t : ℝ} (h₁₂ : t₁ < t₂) :
    targetMerit f c t = fun x => (1 - (t - t₁) / (t₂ - t₁)) • targetMerit f c t₁ x +
      ((t - t₁) / (t₂ - t₁)) • targetMerit f c t₂ x +
      (t ^ 2 - (1 - (t - t₁) / (t₂ - t₁)) * t₁ ^ 2 - (t - t₁) / (t₂ - t₁) * t₂ ^ 2) / 2 := by
  have hd : t₂ - t₁ ≠ 0 := sub_ne_zero.2 h₁₂.ne'
  funext x
  rw [targetMerit_eq_sub (t := t), targetMerit_eq_sub (t := t₁), targetMerit_eq_sub (t := t₂)]
  simp only [smul_eq_mul]
  field_simp
  ring

omit [InnerProductSpace ℝ F] in
/-- **Uniform Hölder constants over an interval of targets**, the core of Lemma 7.2.5 of
[cartis2022evaluation]. Let $F$ be a normed additive commutative group, let $p \ge 1$,
$t_1 \le t \le t_2$ and $C \subseteq E$. For $i = 1, 2$, let $\mu_2(\cdot, t_i)$ be $C^p$ at
every point of $C$, and let its $p$-th derivative be Hölder continuous on $C$ with constant
$H_i$ and exponent $\beta$:
$$\|\nabla^p \mu_2(x, t_i) - \nabla^p \mu_2(z, t_i)\| \le H_i \|x - z\|^\beta \quad \text{for }
  x, z \in C.$$
Then the $p$-th derivative of $\mu_2(\cdot, t)$ is Hölder continuous on $C$ with constant
$\max\{H_1, H_2\}$ and exponent $\beta$.

The Hölder condition is `IteratedFDerivHolderOn`. The proof uses that $\mu_2$ is affine in $t$
up to an additive constant (`Constrained.targetMerit_eq_lineMap`); continuity in $t$ alone would
not give a uniform constant. -/
theorem iteratedFDerivHolderOn_targetMerit_of_mem_Icc {p : ℕ} {t₁ t₂ t H₁ H₂ β : ℝ} {C : Set E}
    (hp : p ≠ 0) (ht : t ∈ Icc t₁ t₂)
    (hμ₁ : ∀ x ∈ C, ContDiffAt ℝ p (targetMerit f c t₁) x)
    (hμ₂ : ∀ x ∈ C, ContDiffAt ℝ p (targetMerit f c t₂) x)
    (h₁ : IteratedFDerivHolderOn (targetMerit f c t₁) p H₁ β C)
    (h₂ : IteratedFDerivHolderOn (targetMerit f c t₂) p H₂ β C) :
    IteratedFDerivHolderOn (targetMerit f c t) p (max H₁ H₂) β C := by
  rcases ht.1.eq_or_lt with rfl | h₁t
  · exact h₁.mono_const (le_max_left _ _)
  have h₁₂ : t₁ < t₂ := h₁t.trans_le ht.2
  set w := (t - t₁) / (t₂ - t₁) with hw
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.2 h₁t.le) (sub_nonneg.2 h₁₂.le)
  have hw1 : w ≤ 1 := (div_le_one (sub_pos.2 h₁₂)).2 (by linarith [ht.2])
  rw [targetMerit_eq_lineMap h₁₂]
  refine (h₁.smul_add_smul_add_const hp hμ₁ hμ₂ h₂ (sub_nonneg.2 hw1) hw0 _).mono_const ?_
  calc (1 - w) * H₁ + w * H₂ ≤ (1 - w) * max H₁ H₂ + w * max H₁ H₂ := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max H₁ H₂ := by ring

end Holder

/-! ### Second- and third-order relations with the Lagrangian -/

section HigherOrder

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}

/-- **The diagonal second derivative of the merit function**, (14.3.38) of [cartis2022evaluation].
Let $f$ and $c$ be $C^2$ at $x$. Then for every direction $d$,
$$\nabla^2 \mu_2(x, t)[d]^2 = \|\nabla c(x)[d]\|^2 + \langle c(x), \nabla^2 c(x)[d]^2 \rangle +
  (\nabla f(x)[d])^2 + (f(x) - t) \nabla^2 f(x)[d]^2.$$
-/
theorem iteratedFDeriv_two_targetMerit_apply (hf : ContDiffAt ℝ 2 f x) (hc : ContDiffAt ℝ 2 c x)
    (d : E) :
    iteratedFDeriv ℝ 2 (targetMerit f c t) x (fun _ => d) =
      ‖fderiv ℝ c x d‖ ^ 2 + ⟪c x, iteratedFDeriv ℝ 2 c x (fun _ => d)⟫ +
        (fderiv ℝ f x d) ^ 2 + (f x - t) * iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  have hft : ContDiffAt ℝ 2 (fun z => f z - t) x := hf.sub contDiffAt_const
  have h1 : ContDiffAt ℝ 2 (fun z => ‖c z‖ ^ 2 / 2) x := (hc.norm_sq ℝ).div_const _
  have h2 : ContDiffAt ℝ 2 (fun z => ‖f z - t‖ ^ 2 / 2) x := (hft.norm_sq ℝ).div_const _
  have hfun : targetMerit f c t = (fun z => ‖c z‖ ^ 2 / 2) + fun z => ‖f z - t‖ ^ 2 / 2 := by
    funext z
    simp only [targetMerit_def, Pi.add_apply, Real.norm_eq_abs, sq_abs]
    ring
  rw [hfun, iteratedFDeriv_add_apply h1 h2, add_apply, iteratedFDeriv_two_half_norm_sq_apply hc,
    iteratedFDeriv_two_half_norm_sq_apply hft, iteratedFDeriv_sub_const_apply two_ne_zero hf,
    fderiv_sub_const, Real.norm_eq_abs, sq_abs, RCLike.inner_apply, conj_trivial]
  ring

/-- **The diagonal third derivative of the merit function**, (14.3.39) of [cartis2022evaluation].
Let $f$ and $c$ be $C^3$ at $x$. Then for every direction $d$,
$$\nabla^3 \mu_2(x, t)[d]^3 = 3 \langle \nabla^2 c(x)[d]^2, \nabla c(x)[d] \rangle + \langle
  c(x), \nabla^3 c(x)[d]^3 \rangle + 3 \nabla^2 f(x)[d]^2 \, \nabla f(x)[d] + (f(x) - t)
  \nabla^3 f(x)[d]^3.$$
-/
theorem iteratedFDeriv_three_targetMerit_apply (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (d : E) :
    iteratedFDeriv ℝ 3 (targetMerit f c t) x (fun _ => d) =
      3 * ⟪iteratedFDeriv ℝ 2 c x (fun _ => d), fderiv ℝ c x d⟫ +
        ⟪c x, iteratedFDeriv ℝ 3 c x (fun _ => d)⟫ +
        3 * iteratedFDeriv ℝ 2 f x (fun _ => d) * fderiv ℝ f x d +
        (f x - t) * iteratedFDeriv ℝ 3 f x (fun _ => d) := by
  have hft : ContDiffAt ℝ 3 (fun z => f z - t) x := hf.sub contDiffAt_const
  have h1 : ContDiffAt ℝ 3 (fun z => ‖c z‖ ^ 2 / 2) x := (hc.norm_sq ℝ).div_const _
  have h2 : ContDiffAt ℝ 3 (fun z => ‖f z - t‖ ^ 2 / 2) x := (hft.norm_sq ℝ).div_const _
  have hfun : targetMerit f c t = (fun z => ‖c z‖ ^ 2 / 2) + fun z => ‖f z - t‖ ^ 2 / 2 := by
    funext z
    simp only [targetMerit_def, Pi.add_apply, Real.norm_eq_abs, sq_abs]
    ring
  rw [hfun, iteratedFDeriv_add_apply h1 h2, add_apply, iteratedFDeriv_three_half_norm_sq_apply hc,
    iteratedFDeriv_three_half_norm_sq_apply hft,
    iteratedFDeriv_sub_const_apply (by norm_num) hf,
    iteratedFDeriv_sub_const_apply two_ne_zero (hf.of_le (by norm_num)),
    fderiv_sub_const, RCLike.inner_apply, RCLike.inner_apply, conj_trivial, conj_trivial,
    real_inner_comm (fderiv ℝ c x d)]
  ring

/-- The decomposition behind (14.3.55) and (14.3.58) of [cartis2022evaluation]. Let $n \ge 1$, let
$f$ and $c$ be $C^n$ at $x$, let $\tau = f(x) - t \neq 0$, let $y = -c(x) / \tau$, and let
$\mathcal{L}(z) = f(z) - \langle y, c(z) \rangle$. Then
$$\nabla^n \mu_2(x, t) = \tau \nabla^n \mathcal{L}(x) + \nabla^n \big(\tfrac12 \|c -
  c(x)\|^2\big)(x) + \nabla^n \big(\tfrac12 (f - f(x))^2\big)(x).$$

This follows from $\mu_2(z, t) = \tau \mathcal{L}(z) + \frac12 \|c(z) - c(x)\|^2 + \frac12
(f(z) - f(x))^2 + \text{const}$. -/
theorem iteratedFDeriv_targetMerit_eq_lagrangian {n : ℕ} (hn : n ≠ 0) (hf : ContDiffAt ℝ n f x)
    (hc : ContDiffAt ℝ n c x) (ht : f x ≠ t) :
    iteratedFDeriv ℝ n (targetMerit f c t) x =
      (f x - t) • iteratedFDeriv ℝ n (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x +
        iteratedFDeriv ℝ n (fun z => ‖c z - c x‖ ^ 2 / 2) x +
        iteratedFDeriv ℝ n (fun z => ‖f z - f x‖ ^ 2 / 2) x := by
  have hτ : f x - t ≠ 0 := sub_ne_zero.2 ht
  set ℓ : E → ℝ := fun z => f z - ⟪targetMultiplier f c t x, c z⟫ with hℓ
  set Gc : E → ℝ := fun z => ‖c z - c x‖ ^ 2 / 2 with hGc
  set Gf : E → ℝ := fun z => ‖f z - f x‖ ^ 2 / 2 with hGf
  have kℓ : ContDiffAt ℝ n ℓ x := hf.sub (contDiffAt_const.inner ℝ hc)
  have kc : ContDiffAt ℝ n Gc x := ((hc.sub contDiffAt_const).norm_sq ℝ).div_const _
  have kf : ContDiffAt ℝ n Gf x := ((hf.sub contDiffAt_const).norm_sq ℝ).div_const _
  have k₁ : ContDiffAt ℝ n ((f x - t) • ℓ) x := by
    change ContDiffAt ℝ n (fun z => (f x - t) • ℓ z) x
    exact kℓ.const_smul _
  have k₂ : ContDiffAt ℝ n ((f x - t) • ℓ + Gc) x := k₁.add kc
  have k₃ : ContDiffAt ℝ n ((f x - t) • ℓ + Gc + Gf) x := k₂.add kf
  have hfun : targetMerit f c t = ((f x - t) • ℓ + Gc + Gf) +
      fun _ => (f x - t) ^ 2 / 2 - (f x - t) * f x - ‖c x‖ ^ 2 / 2 := by
    funext z
    simp only [targetMerit_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hℓ, hGc, hGf,
      targetMultiplier_def, real_inner_smul_left, norm_sub_sq_real, Real.norm_eq_abs, sq_abs,
      real_inner_comm (c z)]
    field_simp
    ring
  rw [hfun, iteratedFDeriv_add_apply k₃ contDiffAt_const, iteratedFDeriv_const_of_ne hn,
    Pi.zero_apply, add_zero, iteratedFDeriv_add_apply k₂ kf, iteratedFDeriv_add_apply k₁ kc,
    iteratedFDeriv_const_smul_apply kℓ]

variable {d : E}

/-- (14.3.55) of [cartis2022evaluation] in decrement form. Let $f$ and $c$ be $C^2$ at $x$, let
$\tau = f(x) - t \neq 0$, let $y = -c(x) / \tau$ and $\mathcal{L}(z) = f(z) - \langle y, c(z)
\rangle$, and let $d$ satisfy $\nabla c(x)[d] = 0$. Then the second-order Taylor decrements
satisfy
$$\Delta T_{\mu, 2}(d) = \tau \, \Delta T_{\mathcal{L}, 2}(d) - \tfrac12 (\nabla f(x)[d])^2.$$
-/
theorem taylorDecrement_two_targetMerit (hf : ContDiffAt ℝ 2 f x) (hc : ContDiffAt ℝ 2 c x)
    (ht : f x ≠ t) (hd : fderiv ℝ c x d = 0) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 2 d =
      (f x - t) * FormalMultilinearSeries.taylorDecrement
          (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 2 d -
        (fderiv ℝ f x d) ^ 2 / 2 := by
  have hc1 : ContDiffAt ℝ 1 c x := hc.of_le (by norm_num)
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hcx : ContDiffAt ℝ 2 (fun z => c z - c x) x := hc.sub contDiffAt_const
  have hfx : ContDiffAt ℝ 2 (fun z => f z - f x) x := hf.sub contDiffAt_const
  simp only [FormalMultilinearSeries.taylorDecrement_two, ftaylorSeries]
  rw [iteratedFDeriv_targetMerit_eq_lagrangian one_ne_zero hf1 hc1 ht,
    iteratedFDeriv_targetMerit_eq_lagrangian two_ne_zero hf hc ht]
  simp only [add_apply, smul_apply, smul_eq_mul, iteratedFDeriv_one_apply]
  rw [fderiv_half_norm_sq_apply (hcx.differentiableAt (by norm_num)),
    fderiv_half_norm_sq_apply (hfx.differentiableAt (by norm_num)),
    iteratedFDeriv_two_half_norm_sq_apply hcx, iteratedFDeriv_two_half_norm_sq_apply hfx]
  simp only [sub_self, inner_zero_left, fderiv_sub_const, hd, norm_zero, Real.norm_eq_abs,
    sq_abs]
  ring

/-- (14.3.58) of [cartis2022evaluation] in decrement form. Let $f$ and $c$ be $C^3$ at $x$, let
$\tau = f(x) - t \neq 0$, let $y = -c(x) / \tau$ and $\mathcal{L}(z) = f(z) - \langle y, c(z)
\rangle$, and let $d$ satisfy $\nabla c(x)[d] = 0$. Then the third-order Taylor decrements
satisfy
$$\Delta T_{\mu, 3}(d) = \tau \, \Delta T_{\mathcal{L}, 3}(d) - \tfrac12 (\nabla f(x)[d])^2 -
  \tfrac12 \nabla f(x)[d] \, \nabla^2 f(x)[d]^2.$$
-/
theorem taylorDecrement_three_targetMerit (hf : ContDiffAt ℝ 3 f x) (hc : ContDiffAt ℝ 3 c x)
    (ht : f x ≠ t) (hd : fderiv ℝ c x d = 0) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 3 d =
      (f x - t) * FormalMultilinearSeries.taylorDecrement
          (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 3 d -
        (fderiv ℝ f x d) ^ 2 / 2 -
        fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) / 2 := by
  have hc1 : ContDiffAt ℝ 1 c x := hc.of_le (by norm_num)
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 c x := hc.of_le (by norm_num)
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hcx : ContDiffAt ℝ 3 (fun z => c z - c x) x := hc.sub contDiffAt_const
  have hfx : ContDiffAt ℝ 3 (fun z => f z - f x) x := hf.sub contDiffAt_const
  simp only [FormalMultilinearSeries.taylorDecrement_three, ftaylorSeries]
  rw [iteratedFDeriv_targetMerit_eq_lagrangian one_ne_zero hf1 hc1 ht,
    iteratedFDeriv_targetMerit_eq_lagrangian two_ne_zero hf2 hc2 ht,
    iteratedFDeriv_targetMerit_eq_lagrangian (by norm_num) hf hc ht]
  simp only [add_apply, smul_apply, smul_eq_mul, iteratedFDeriv_one_apply]
  rw [fderiv_half_norm_sq_apply (hcx.differentiableAt (by norm_num)),
    fderiv_half_norm_sq_apply (hfx.differentiableAt (by norm_num)),
    iteratedFDeriv_two_half_norm_sq_apply (hcx.of_le (by norm_num)),
    iteratedFDeriv_two_half_norm_sq_apply (hfx.of_le (by norm_num)),
    iteratedFDeriv_three_half_norm_sq_apply hcx, iteratedFDeriv_three_half_norm_sq_apply hfx,
    iteratedFDeriv_sub_const_apply two_ne_zero hf2]
  simp only [sub_self, inner_zero_left, fderiv_sub_const, hd, norm_zero, inner_zero_left,
    Real.norm_eq_abs, sq_abs, RCLike.inner_apply, conj_trivial]
  ring

end HigherOrder

/-! ### Measure relations between $\mu_2$ and the Lagrangian (Lemma 14.3.5) -/

section MeasureRelations

open Optimization

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E} {δ : ℝ} {S : Set E}

/-- **Second-order measure relation**, (14.3.43) of [cartis2022evaluation]. Let $f$ and $c$ be $C^2$
at $x$, let $\tau = f(x) - t > 0$, let $y = -c(x) / \tau$ and $\mathcal{L}(z) = f(z) - \langle
y, c(z) \rangle$. Let $0 \in S$, $\delta \ge 0$, and $T = S \cap \ker \nabla c(x)$. Suppose that
$|\nabla f(x)[d]| \le G$ for every $d \in T$ with $\|d\| \le \delta$; for example
$G = \|\nabla f(x)\| \delta$. Then
$$\varphi^\delta_{\mathcal{L}, T, 2}(x) \le \frac{\varphi^\delta_{\mu, S, 2}(x, t) + G^2 /
  2}{\tau}.$$

On $T$, $\Delta T_{\mathcal{L}, 2}(d) = (\Delta T_{\mu, 2}(d) + \frac12 (\nabla f(x)[d])^2) /
\tau$ by (14.3.55). Since $\nabla \mathcal{L}(x)[d] = \nabla f(x)[d]$ on $T$, the extra term is
not controlled by $\varphi^\delta_{\mathcal{L}, 1}$. -/
theorem taylorMeasure_lagrangian_two_le (hf : ContDiffAt ℝ 2 f x) (hc : ContDiffAt ℝ 2 c x)
    (ht : t < f x) (hδ : 0 ≤ δ) (hS : (0 : E) ∈ S) {G : ℝ}
    (hG : ∀ d ∈ closedBall (0 : E) δ ∩ (S ∩ {d | fderiv ℝ c x d = 0}), |fderiv ℝ f x d| ≤ G) :
    taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 2 δ
        (S ∩ {d | fderiv ℝ c x d = 0}) ≤
      (f x - t)⁻¹ * (taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2 δ S + G ^ 2 / 2) := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  rw [taylorMeasure]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩ fun d hd => ?_
  have hdec := taylorDecrement_two_targetMerit hf hc ht.ne' hd.2.2
  have hμ := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2
    (S := S) ⟨hd.1, hd.2.1⟩
  have hG' : (fderiv ℝ f x d) ^ 2 ≤ G ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hG d hd) 2
  rw [le_inv_mul_iff₀ hτ]
  linarith

/-- **Second-order measure relation on $\ker \nabla f(x)$**, (14.3.44) of [cartis2022evaluation].
Let $f$ and $c$ be $C^2$ at $x$, let $\tau = f(x) - t > 0$, let $y = -c(x) / \tau$ and
$\mathcal{L}(z) = f(z) - \langle y, c(z) \rangle$. Let $0 \in S$, $\delta \ge 0$, and $M = S
\cap \ker \nabla c(x) \cap \ker \nabla f(x)$. Then
$$\varphi^\delta_{\mathcal{L}, M, 2}(x) \le \frac{\varphi^\delta_{\mu, S, 2}(x, t)}{\tau}.$$
-/
theorem taylorMeasure_lagrangian_two_le_of_ker (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : t < f x) (hδ : 0 ≤ δ) (hS : (0 : E) ∈ S) :
    taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 2 δ
        (S ∩ {d | fderiv ℝ c x d = 0} ∩ {d | fderiv ℝ f x d = 0}) ≤
      (f x - t)⁻¹ * taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2 δ S := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  rw [taylorMeasure]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, ⟨hS, by simp⟩, by simp⟩ fun d hd => ?_
  have hdec := taylorDecrement_two_targetMerit hf hc ht.ne' hd.2.1.2
  have hμ := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2
    (S := S) ⟨hd.1, hd.2.1.1⟩
  have hfd : fderiv ℝ f x d = 0 := hd.2.2
  rw [hfd] at hdec
  rw [le_inv_mul_iff₀ hτ]
  linarith

/-- **Third-order measure relation**, (14.3.46) of [cartis2022evaluation]. Let $f$ and $c$ be $C^3$
at $x$, let $\tau = f(x) - t > 0$, let $y = -c(x) / \tau$ and $\mathcal{L}(z) = f(z) - \langle
y, c(z) \rangle$. Let $0 \in S$, $\delta \ge 0$, and $T = S \cap \ker \nabla c(x)$. Suppose that
$|\nabla f(x)[d]| \le G$ and $|\nabla^2 f(x)[d]^2| \le H$ for every $d \in T$ with
$\|d\| \le \delta$. Then
$$\varphi^\delta_{\mathcal{L}, T, 3}(x) \le \frac{\varphi^\delta_{\mu, S, 3}(x, t) + (G + H) G /
  2}{\tau}.$$

On $T$, $\Delta T_{\mathcal{L}, 3}(d) = (\Delta T_{\mu, 3}(d) + \frac12 (\nabla f(x)[d])^2 +
\frac12 \nabla f(x)[d] \, \nabla^2 f(x)[d]^2) / \tau$ by (14.3.58). -/
theorem taylorMeasure_lagrangian_three_le (hf : ContDiffAt ℝ 3 f x) (hc : ContDiffAt ℝ 3 c x)
    (ht : t < f x) (hδ : 0 ≤ δ) (hS : (0 : E) ∈ S) {G H : ℝ}
    (hG : ∀ d ∈ closedBall (0 : E) δ ∩ (S ∩ {d | fderiv ℝ c x d = 0}), |fderiv ℝ f x d| ≤ G)
    (hH : ∀ d ∈ closedBall (0 : E) δ ∩ (S ∩ {d | fderiv ℝ c x d = 0}),
      |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ H) :
    taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 3 δ
        (S ∩ {d | fderiv ℝ c x d = 0}) ≤
      (f x - t)⁻¹ *
        (taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3 δ S + (G + H) * G / 2) := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  rw [taylorMeasure]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩ fun d hd => ?_
  have hdec := taylorDecrement_three_targetMerit hf hc ht.ne' hd.2.2
  have hμ := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3
    (S := S) ⟨hd.1, hd.2.1⟩
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG d hd)
  have hG' : (fderiv ℝ f x d) ^ 2 ≤ G ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hG d hd) 2
  have hGH : fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) ≤ G * H := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul (hG d hd) (hH d hd) (abs_nonneg _) hG0
  rw [le_inv_mul_iff₀ hτ]
  nlinarith

/-- **Third-order measure relation on $\ker \nabla f(x)$**, (14.3.47) of [cartis2022evaluation]. Let
$f$ and $c$ be $C^3$ at $x$, let $\tau = f(x) - t > 0$, let $y = -c(x) / \tau$ and
$\mathcal{L}(z) = f(z) - \langle y, c(z) \rangle$. Let $0 \in S$, $\delta \ge 0$, and $M = S
\cap \ker \nabla c(x) \cap \ker \nabla f(x)$. Then
$$\varphi^\delta_{\mathcal{L}, M, 3}(x) \le \frac{\varphi^\delta_{\mu, S, 3}(x, t)}{\tau}.$$
-/
theorem taylorMeasure_lagrangian_three_le_of_ker (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : t < f x) (hδ : 0 ≤ δ) (hS : (0 : E) ∈ S) :
    taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪targetMultiplier f c t x, c z⟫) x) 3 δ
        (S ∩ {d | fderiv ℝ c x d = 0} ∩ {d | fderiv ℝ f x d = 0}) ≤
      (f x - t)⁻¹ * taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3 δ S := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  rw [taylorMeasure]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, ⟨hS, by simp⟩, by simp⟩ fun d hd => ?_
  have hdec := taylorDecrement_three_targetMerit hf hc ht.ne' hd.2.1.2
  have hμ := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3
    (S := S) ⟨hd.1, hd.2.1.1⟩
  have hfd : fderiv ℝ f x d = 0 := hd.2.2
  rw [hfd] at hdec
  rw [le_inv_mul_iff₀ hτ]
  linarith

end MeasureRelations

end Constrained
