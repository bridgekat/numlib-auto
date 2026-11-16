/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.MeasureDominated
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Powers of the norm of a residual

Let $E$ and $F$ be real inner product spaces, let $r : E \to F$ be a residual map (in the book,
$r : \mathbb{R}^n \to \mathbb{R}^m$), and let $\ell$ be a real exponent. This file studies the
objective
$$\Phi_\ell(x) = \frac{1}{\ell} \|r(x)\|^\ell$$
of (5.1.3) in [cartis2022evaluation]; the case $\ell = 2$ is nonlinear least squares. Write $J(x)$
for the derivative of $r$ at $x$ and $J(x)^*$ for its adjoint. The file proves that $\Phi_\ell$ is
as smooth as $r$ (Lemma 5.1.1), computes the gradient $\nabla \Phi_\ell(x) = \|r(x)\|^{\ell-2}
J(x)^* r(x)$, and shows that the scaled gradient norm $\psi_{\ell,1}(x) = \|\nabla \Phi_\ell(x)\| /
\|r(x)\|^{\ell-1}$ equals $\|J(x)^* r(x)\| / \|r(x)\|$ for every $\ell > 1$ (5.1.63). A lower bound
$s_0$ on $J(x)^*$ gives $\|\nabla \Phi_\ell(x)\| \ge s_0 \|r(x)\|^{\ell-1}$ (5.1.64), and then
$\Phi_\ell$ is measure dominated of level $\ell / (\ell - 1)$ (5.3.3).

The last part proves the cascading-differences inequality of Lemma 5.1.3 and the decrease of the
potential $\|r\|^{1/2^i}$ on a successful iteration that Lemma 5.1.4 derives from it.

## Main definitions

* `Optimization.residualPow`: the objective $\Phi_\ell(x) = \|r(x)\|^\ell / \ell$ of (5.1.3).

## Main results

* `Optimization.contDiff_residualPow`: Lemma 5.1.1, $\Phi_\ell$ is $C^p$ when $r$ is $C^p$, if
  $\ell$ is an even integer or $\ell \ge 2p$.
* `Optimization.gradient_residualPow`: for $\ell > 1$, $\nabla \Phi_\ell(x) = \|r(x)\|^{\ell-2}
  J(x)^* r(x)$.
* `Optimization.norm_fderiv_residualPow`: for $\ell > 1$, $\|\nabla \Phi_\ell(x)\| =
  \|r(x)\|^{\ell-2} \|J(x)^* r(x)\|$.
* `Optimization.norm_fderiv_residualPow_div`, `Optimization.norm_fderiv_residualPow_div_eq_two`:
  (5.1.63), for $r(x) \neq 0$ and $\ell > 1$, $\|\nabla \Phi_\ell(x)\| / \|r(x)\|^{\ell-1} =
  \|\nabla \Phi_2(x)\| / \|r(x)\| = \|J(x)^* r(x)\| / \|r(x)\|$.
* `Optimization.norm_fderiv_residualPow_ge`: (5.1.64) and (5.3.2), if $s_0 \|v\| \le \|J(x)^* v\|$
  for all $v$, then $\|\nabla \Phi_\ell(x)\| \ge s_0 \|r(x)\|^{\ell-1}$.
* `Optimization.residualPow_le_of_norm_fderiv_ge`, `Optimization.isMeasureDominated_residualPow`:
  (5.3.3), under this bound $\Phi_\ell$ is measure dominated of level $\ell / (\ell - 1)$ for the
  measure $\|\nabla \Phi_\ell\|$.
* `Optimization.rpow_inv_two_pow_sub_ge`: Lemma 5.1.3 (cascading differences).
* `Optimization.rpow_inv_two_pow_sub_ge_min`: the decrease of the potential $\|r\|^{1/2^i}$ on a
  successful iteration, from Lemma 5.1.4, (5.1.20) and (5.1.27), and display (6.3.3).

## Implementation notes

* The derivative of $\Phi_\ell$ is the Fréchet derivative
  `fderiv ℝ (Optimization.residualPow r ℓ) x`, a continuous linear functional on $E$. Its operator
  norm is the norm of the gradient $\nabla \Phi_\ell(x)$, so the gradient vector itself does not
  appear.
* The adjoint $J(x)^*$ is `ContinuousLinearMap.adjoint (fderiv ℝ r x)`. The results that use it
  assume that $E$ and $F$ are complete.
* The potential decrease `Optimization.rpow_inv_two_pow_sub_ge_min` is stated for real numbers, so
  that both the unconstrained first-order measure $\|\nabla \Phi_\ell\|$ and the constrained measure
  $\omega_{\Phi_\ell, \mathcal{C}, 1}$ are instances of it.
-/

open scoped InnerProductSpace

namespace Optimization

section Def

variable {E F : Type*} [NormedAddCommGroup F]

/-- The objective $\Phi_\ell(x) = \|r(x)\|^\ell / \ell$ of a map $r : E \to F$ into a normed group,
with a real exponent $\ell$. This is (5.1.3) of [cartis2022evaluation].

The book uses $\ell \ge 1$, and the results below assume $\ell > 1$ or $\ell \ge 2p$. For the
degenerate exponent $\ell = 0$, division by zero gives $\Phi_0 = 0$. For $\ell < 0$ the function
is not a meaningful objective. -/
noncomputable def residualPow (r : E → F) (ℓ : ℝ) (x : E) : ℝ :=
  ‖r x‖ ^ ℓ / ℓ

/-- The defining formula $\Phi_\ell(x) = \|r(x)\|^\ell / \ell$, with the real power $\|r(x)\|^\ell$.
-/
theorem residualPow_def (r : E → F) (ℓ : ℝ) (x : E) : residualPow r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  rfl

/-- For a natural exponent $n$, $\Phi_n(x) = \|r(x)\|^n / n$ with the natural power $\|r(x)\|^n$. -/
@[simp]
theorem residualPow_natCast (r : E → F) (n : ℕ) (x : E) :
    residualPow r n x = ‖r x‖ ^ n / n := by
  simp [residualPow, Real.rpow_natCast]

/-- If $\ell \ge 0$, then $\Phi_\ell(x) \ge 0$ for every $x$. -/
theorem residualPow_nonneg (r : E → F) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : E) : 0 ≤ residualPow r ℓ x :=
  div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hℓ

end Def

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- Let $p$ be a natural number and let $r : E \to F$ be $p$ times continuously differentiable. If
$\ell$ is an even natural number $2m$, or $\ell$ is a real number with $\ell \ge 2p$, then
$\Phi_\ell$ is $p$ times continuously differentiable. This is Lemma 5.1.1 of
[cartis2022evaluation].

The book assumes the strict inequality $\ell > 2p$. Its proof writes
$\Phi_\ell = (\|r\|^2)^{\ell/2} / \ell$ and needs only that $t \mapsto t^{\ell/2}$ is $C^p$,
which holds for $\ell / 2 \ge p$ by `Real.contDiff_rpow_const_of_le`; so the statement here is
slightly stronger. The book also remarks that $\ell > p$ suffices; that remark is not proved
there and is not formalized. -/
theorem contDiff_residualPow {r : E → F} {p : ℕ} {ℓ : ℝ} (hr : ContDiff ℝ p r)
    (hℓ : (∃ m : ℕ, ℓ = 2 * m) ∨ 2 * (p : ℝ) ≤ ℓ) : ContDiff ℝ p (residualPow r ℓ) := by
  have hsq : ContDiff ℝ p fun x => ‖r x‖ ^ 2 := hr.norm_sq ℝ
  rcases hℓ with ⟨m, rfl⟩ | hℓ
  · have : residualPow r (2 * m) = fun x => (‖r x‖ ^ 2) ^ m / (2 * m) := by
      funext x
      rw [residualPow, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_mul]
    rw [this]
    exact (hsq.pow m).div_const _
  · have : residualPow r ℓ = fun x => (‖r x‖ ^ 2) ^ (ℓ / 2) / ℓ := by
      funext x
      rw [residualPow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 2
      push_cast
      ring
    rw [this]
    exact ((Real.contDiff_rpow_const_of_le (by linarith)).comp hsq).div_const _

/-- Let $\ell > 1$ and let $r$ have the derivative $r'$ at $x$. Then $\Phi_\ell$ has at $x$ the
derivative
$$h \mapsto \|r(x)\|^{\ell-2} \langle r(x), r' h \rangle.$$
-/
theorem hasFDerivAt_residualPow {r : E → F} {r' : E →L[ℝ] F} {x : E} {ℓ : ℝ}
    (hr : HasFDerivAt r r' x) (hℓ : 1 < ℓ) :
    HasFDerivAt (residualPow r ℓ) (‖r x‖ ^ (ℓ - 2) • (innerSL ℝ (r x)).comp r') x := by
  have h := ((hasFDerivAt_norm_rpow (r x) hℓ).comp x hr).mul_const ℓ⁻¹
  have hℓ0 : ℓ ≠ 0 := by positivity
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp
  · simp [residualPow, div_eq_mul_inv]

/-- **Gradient of $\Phi_\ell$.** Let $\ell > 1$ and let $r$ be differentiable at $x$, with
derivative $J(x)$. Then the derivative of $\Phi_\ell$ at $x$ is
$$D\Phi_\ell(x) h = \|r(x)\|^{\ell-2} \langle r(x), J(x) h \rangle,$$
that is, $\nabla \Phi_\ell(x) = \|r(x)\|^{\ell-2} J(x)^* r(x)$. This is the gradient formula
behind (5.1.63) of [cartis2022evaluation].

The statement is the equality of the two continuous linear functionals; it needs no completeness
of $E$ or $F$. -/
theorem gradient_residualPow {r : E → F} {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x)
    (hℓ : 1 < ℓ) :
    fderiv ℝ (residualPow r ℓ) x = ‖r x‖ ^ (ℓ - 2) • (innerSL ℝ (r x)).comp (fderiv ℝ r x) :=
  (hasFDerivAt_residualPow hr.hasFDerivAt hℓ).fderiv

/-- If $\ell > 1$ and $r$ is differentiable at $x$, then $\Phi_\ell$ is differentiable at $x$. -/
theorem differentiableAt_residualPow {r : E → F} {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x)
    (hℓ : 1 < ℓ) : DifferentiableAt ℝ (residualPow r ℓ) x :=
  (hasFDerivAt_residualPow hr.hasFDerivAt hℓ).differentiableAt

/-- Let $E$ and $F$ be complete real inner product spaces, let $A : E \to F$ be a continuous linear
map and let $v \in F$. Then the functional $u \mapsto \langle v, A u \rangle$ is
$u \mapsto \langle A^* v, u \rangle$, and its norm is $\|A^* v\|$. -/
theorem norm_innerSL_comp [CompleteSpace E] [CompleteSpace F] (A : E →L[ℝ] F) (v : F) :
    ‖(innerSL ℝ v).comp A‖ = ‖(ContinuousLinearMap.adjoint A) v‖ := by
  have : (innerSL ℝ v).comp A = innerSL ℝ ((ContinuousLinearMap.adjoint A) v) := by
    ext u
    simp [ContinuousLinearMap.adjoint_inner_left]
  rw [this, innerSL_apply_norm]

/-- Let $E$ and $F$ be complete, let $\ell > 1$ and let $r$ be differentiable at $x$. Then the norm
of the gradient of $\Phi_\ell$ is
$$\|\nabla \Phi_\ell(x)\| = \|r(x)\|^{\ell-2} \, \|J(x)^* r(x)\|.$$
-/
theorem norm_fderiv_residualPow [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E} {ℓ : ℝ}
    (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ =
      ‖r x‖ ^ (ℓ - 2) * ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ := by
  rw [gradient_residualPow hr hℓ, norm_smul, norm_innerSL_comp, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-- Let $E$ and $F$ be complete, let $\ell > 1$, let $r$ be differentiable at $x$, and let
$r(x) \neq 0$. Then the scaled gradient norm $\psi_{\ell,1}(x)$ does not depend on $\ell$:
$$\psi_{\ell,1}(x) = \frac{\|\nabla \Phi_\ell(x)\|}{\|r(x)\|^{\ell-1}} = \frac{\|J(x)^*
  r(x)\|}{\|r(x)\|}.$$
This is the outer equality of (5.1.63) of [cartis2022evaluation]; for $\ell = 2$ the left side
is $\|\nabla \Phi_2(x)\| / \|r(x)\|$. -/
theorem norm_fderiv_residualPow_div [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E}
    {ℓ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) (hrx : r x ≠ 0) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) =
      ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ / ‖r x‖ := by
  have hpos : 0 < ‖r x‖ := norm_pos_iff.2 hrx
  rw [norm_fderiv_residualPow hr hℓ, show ℓ - 1 = (ℓ - 2) + 1 by ring,
    Real.rpow_add_one hpos.ne']
  have : 0 < ‖r x‖ ^ (ℓ - 2) := Real.rpow_pos_of_pos hpos _
  field_simp

/-- Let $E$ and $F$ be complete, let $\ell > 1$, let $r$ be differentiable at $x$, and let
$r(x) \neq 0$. Then the scaled gradient norm of $\Phi_\ell$ equals that of the least-squares
objective $\Phi_2$:
$$\frac{\|\nabla \Phi_\ell(x)\|}{\|r(x)\|^{\ell-1}} = \frac{\|\nabla \Phi_2(x)\|}{\|r(x)\|}.$$
This is the middle equality of (5.1.63) of [cartis2022evaluation]. -/
theorem norm_fderiv_residualPow_div_eq_two [CompleteSpace E] [CompleteSpace F] {r : E → F}
    {x : E} {ℓ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ) (hrx : r x ≠ 0) :
    ‖fderiv ℝ (residualPow r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) =
      ‖fderiv ℝ (residualPow r 2) x‖ / ‖r x‖ := by
  rw [norm_fderiv_residualPow_div hr hℓ hrx]
  have := norm_fderiv_residualPow_div hr one_lt_two hrx
  norm_num at this
  rw [this]

/-- Let $E$ and $F$ be complete, let $\ell > 1$, and let $r$ be differentiable at $x$. Let $s_0$ be
a real number with $s_0 \|v\| \le \|J(x)^* v\|$ for all $v \in F$; in finite dimension, this
holds when $s_0$ is at most the smallest singular value of $J(x)^*$. Then
$$s_0 \|r(x)\|^{\ell-1} \le \|\nabla \Phi_\ell(x)\|,$$
so that $\psi_{\ell,1}(x) \ge s_0$ when $r(x) \neq 0$, which is condition (5.1.62). This is
(5.1.64) and (5.3.2) of [cartis2022evaluation]. -/
theorem norm_fderiv_residualPow_ge [CompleteSpace E] [CompleteSpace F] {r : E → F} {x : E}
    {ℓ s₀ : ℝ} (hr : DifferentiableAt ℝ r x) (hℓ : 1 < ℓ)
    (hs : ∀ v, s₀ * ‖v‖ ≤ ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) v‖) :
    s₀ * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖ := by
  rw [norm_fderiv_residualPow hr hℓ]
  rcases eq_or_ne (r x) 0 with h0 | h0
  · rw [h0, norm_zero, Real.zero_rpow (by linarith), mul_zero]
    positivity
  · have hpos : 0 < ‖r x‖ := norm_pos_iff.2 h0
    rw [show ℓ - 1 = (ℓ - 2) + 1 by ring, Real.rpow_add_one hpos.ne']
    have := mul_le_mul_of_nonneg_left (hs (r x)) (Real.rpow_nonneg hpos.le (ℓ - 2))
    linarith

omit [InnerProductSpace ℝ F] in
/-- Let $F$ be a normed group, let $\ell > 1$ and $\psi_{\min} > 0$, and suppose that $\|\nabla
\Phi_\ell(x)\| \ge \psi_{\min} \|r(x)\|^{\ell-1}$. Then
$$\Phi_\ell(x) \le \frac{\psi_{\min}^{-\ell/(\ell-1)}}{\ell} \, \|\nabla
  \Phi_\ell(x)\|^{\ell/(\ell-1)}.$$
This is (5.3.3) of [cartis2022evaluation]. -/
theorem residualPow_le_of_norm_fderiv_ge {r : E → F} {x : E} {ℓ ψmin : ℝ} (hℓ : 1 < ℓ)
    (hψ : 0 < ψmin) (h : ψmin * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖) :
    residualPow r ℓ x ≤
      ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ * ‖fderiv ℝ (residualPow r ℓ) x‖ ^ (ℓ / (ℓ - 1)) := by
  set G := ‖fderiv ℝ (residualPow r ℓ) x‖
  have hℓ1 : 0 < ℓ - 1 := by linarith
  have ha : 0 ≤ ‖r x‖ ^ (ℓ - 1) := Real.rpow_nonneg (norm_nonneg _) _
  have hle : ‖r x‖ ^ (ℓ - 1) ≤ G / ψmin := by rw [le_div_iff₀ hψ]; linarith
  have hpow : ‖r x‖ ^ ℓ ≤ (G / ψmin) ^ (ℓ / (ℓ - 1)) := by
    calc ‖r x‖ ^ ℓ = (‖r x‖ ^ (ℓ - 1)) ^ (ℓ / (ℓ - 1)) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hℓ1.ne']
      _ ≤ _ := Real.rpow_le_rpow ha hle (by positivity)
  rw [Real.div_rpow (norm_nonneg _) hψ.le] at hpow
  rw [residualPow, div_le_iff₀ (by linarith)]
  calc ‖r x‖ ^ ℓ ≤ G ^ (ℓ / (ℓ - 1)) / ψmin ^ (ℓ / (ℓ - 1)) := hpow
    _ = _ := by
      have : 0 < ψmin ^ (ℓ / (ℓ - 1)) := Real.rpow_pos_of_pos hψ _
      rw [Real.rpow_neg hψ.le]
      field_simp

omit [InnerProductSpace ℝ F] in
/-- **Measure domination of $\Phi_\ell$.** Let $F$ be a normed group, let $\ell > 1$ and
$\psi_{\min} > 0$, and let $A \subseteq E$ be a set with $\|\nabla \Phi_\ell(x)\| \ge
\psi_{\min} \|r(x)\|^{\ell-1}$ for all $x \in A$. Then $\Phi_\ell$ is measure dominated on $A$
(`Optimization.IsMeasureDominated`) for the measure $\psi = \|\nabla \Phi_\ell\|$, with value
$f_* = 0$, level $\ell / (\ell - 1)$ and constant $\kappa_\psi = \psi_{\min}^{-\ell/(\ell-1)} /
\ell$: for $x \in A$,
$$0 \le \Phi_\ell(x) \le \kappa_\psi \|\nabla \Phi_\ell(x)\|^{\ell/(\ell-1)}.$$
This is (5.3.3) of [cartis2022evaluation].

The hypothesis holds, for example, under condition (5.1.62), by
`Optimization.norm_fderiv_residualPow_ge`. -/
theorem isMeasureDominated_residualPow {r : E → F} {ℓ ψmin : ℝ} {A : Set E} (hℓ : 1 < ℓ)
    (hψ : 0 < ψmin)
    (h : ∀ x ∈ A, ψmin * ‖r x‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (residualPow r ℓ) x‖) :
    IsMeasureDominated (residualPow r ℓ) (fun x => ‖fderiv ℝ (residualPow r ℓ) x‖) 0
      (ℓ / (ℓ - 1)) (ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ) A := fun x hx =>
  ⟨residualPow_nonneg r (by linarith) x,
    by rw [sub_zero]; exact residualPow_le_of_norm_fderiv_ge hℓ hψ (h x hx)⟩

end Calculus

/-! ### Cascading differences -/

section Cascade

/-- For real numbers $0 \le b \le a$ and a natural number $n$,
$$a^{n+1} - b^{n+1} \le (n+1) \, a^n (a - b).$$
-/
theorem pow_succ_sub_pow_succ_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := by
  have ha : 0 ≤ a := hb.trans hba
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left ih ha
    have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hba (n + 1)) (sub_nonneg.2 hba)
    calc _ ≤ a * ((n + 1) * a ^ n * (a - b)) + a ^ (n + 1) * (a - b) := add_le_add h1 h2
      _ = _ := by push_cast; ring

/-- Concavity of $t \mapsto t^\alpha$ for $\alpha \in [0, 1]$: if $a > 0$ and $b \ge 0$, then
$$\alpha \, a^{\alpha-1} (a - b) \le a^\alpha - b^\alpha.$$
-/
theorem mul_rpow_sub_one_mul_le_rpow_sub {a b α : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : α * a ^ (α - 1) * (a - b) ≤ a ^ α - b ^ α := by
  have h := rpow_one_add_le_one_add_mul_self (s := b / a - 1)
    (by have := div_nonneg hb ha.le; linarith) hα0 hα1
  rw [add_sub_cancel, Real.div_rpow hb ha.le, div_le_iff₀ (Real.rpow_pos_of_pos ha α)] at h
  rw [Real.rpow_sub_one ha.ne']
  have : (1 + α * (b / a - 1)) * a ^ α = a ^ α - α * (a ^ α / a) * (a - b) := by
    field_simp
    ring
  linarith

/-- The **cascading-differences inequality**. Let $0 \le b \le a$ be real numbers, and let $i$ and
$\ell \ge 1$ be natural numbers. Then
$$a^{1/2^i} - b^{1/2^i} \ge \frac{a^\ell - b^\ell}{2^i \, \ell \, a^{(2^i - 1)/2^i + \ell -
  1}}.$$
This is Lemma 5.1.3 of [cartis2022evaluation]. -/
theorem rpow_inv_two_pow_sub_ge {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (i : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * a ^ (((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  rcases (hb.trans hba).lt_or_eq with ha | ha
  · obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
    set α : ℝ := 1 / 2 ^ i with hαdef
    have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have hα0 : 0 ≤ α := by positivity
    have hα1 : α ≤ 1 := by
      rw [hαdef, div_le_one h2]; exact one_le_pow₀ (by norm_num)
    have hα2 : α * 2 ^ i = 1 := by rw [hαdef]; field_simp
    have hexp : ((2 : ℝ) ^ i - 1) / 2 ^ i + ((n + 1 : ℕ) : ℝ) - 1 = (1 - α) + n := by
      rw [hαdef]; push_cast; field_simp; ring
    rw [hexp, Real.rpow_add ha, Real.rpow_natCast]
    have hAB : a ^ (α - 1) * a ^ (1 - α) = 1 := by
      rw [← Real.rpow_add ha]; simp
    have hB : 0 < a ^ (1 - α) := Real.rpow_pos_of_pos ha _
    have hD : 0 < 2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n) := by positivity
    rw [div_le_iff₀ hD]
    calc a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := pow_succ_sub_pow_succ_le hb hba n
      _ = α * a ^ (α - 1) * (a - b) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) := by
        have : α * a ^ (α - 1) * (a - b) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) =
            (α * 2 ^ i) * (a ^ (α - 1) * a ^ (1 - α)) * ((n + 1) * a ^ n * (a - b)) := by
          push_cast; ring
        rw [this, hα2, hAB, one_mul, one_mul]
      _ ≤ (a ^ α - b ^ α) * (2 ^ i * ((n + 1 : ℕ) : ℝ) * (a ^ (1 - α) * a ^ n)) :=
        mul_le_mul_of_nonneg_right (mul_rpow_sub_one_mul_le_rpow_sub ha hb hα0 hα1) hD.le
  · have hb0 : b = 0 := le_antisymm (ha ▸ hba) hb
    subst hb0
    rw [← ha]
    simp [zero_pow (by omega : ℓ ≠ 0)]

/-- **Decrease of the potential $\|r\|^{1/2^i}$** on a successful iteration that does not terminate.
Let $p \ge 1$, $\ell \ge 1$ and $i$ be natural numbers with
$$\iota_1 = \frac{2^i - 1}{2^i} - \frac{\ell - 1}{p} \ge 0,$$
as in (5.1.21). Let $\beta \in (0, 1)$ and $\kappa_1, \varepsilon_0, \varepsilon_1 > 0$. Let
$a, b, R, \omega$ be real numbers with $\varepsilon_0 < b \le a \le R$,
$\omega > \varepsilon_1 b^{\ell-1}$ and $a^\ell - b^\ell \ge \ell \kappa_1 \omega^{(p+1)/p}$.
Then
$$a^{1/2^i} - b^{1/2^i} \ge \frac{\min(\kappa_{r0}, \kappa_{r1}) \min(\varepsilon_0^{1/2^i},
  \varepsilon_1^{(p+1)/p})}{\max(1, R^{\iota_1})},$$
where $\kappa_{r0} = 1 - \beta^{1/2^i}$ and $\kappa_{r1} = \kappa_1 \beta^{(\ell-1)(p+1)/p} /
2^i$. This bound comes from Lemma 5.1.4 of [cartis2022evaluation], with (5.1.20), (5.1.27) and
(5.1.28), and from display (6.3.3) for the algorithm ARpLE-CC.

In the application, $a = \|r(x_k)\|$, $b = \|r(x_{k+1})\|$ and $R = \|r(x_0)\|$. The number
$\omega$ is the first-order measure of $\Phi_\ell$ at $x_{k+1}$, which fails the termination
test, and the hypothesis on $a^\ell - b^\ell$ is the decrease of Lemmas 4.1.4 and 6.2.4 for
$\Phi_\ell$. The theorem is not a numbered item of the book: it combines the two cases (5.1.20)
and (5.1.27) of Lemma 5.1.4, and bounds the quantities that depend on $\varepsilon$ as in the
proofs of Theorems 5.1.7 and 6.3.1. -/
theorem rpow_inv_two_pow_sub_ge_min {p ℓ i : ℕ} (hp : 1 ≤ p) (hℓ : 1 ≤ ℓ)
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β κ₁ ε₀ ε₁ R a b ω : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ₁ : 0 < κ₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hRa : a ≤ R)
    (hba : b ≤ a) (hb : ε₀ < b) (hω : ε₁ * b ^ (ℓ - 1) < ω)
    (hdec : ℓ * κ₁ * ω ^ (((p : ℝ) + 1) / p) ≤ a ^ ℓ - b ^ ℓ) :
    min (1 - β ^ (1 / 2 ^ i : ℝ)) (κ₁ * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i) *
        min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) /
        max 1 (R ^ (((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  set α : ℝ := 1 / 2 ^ i with hαdef
  set ν : ℝ := ((p : ℝ) + 1) / p with hνdef
  set ι : ℝ := ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p with hιdef
  set κr0 := 1 - β ^ α
  set κr1 := κ₁ * β ^ (((ℓ : ℝ) - 1) * ν) / 2 ^ i
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hb0 : 0 < b := hε₀.trans hb
  have ha : 0 < a := hb0.trans_le hba
  have hα0 : 0 < α := by positivity
  have hν0 : 0 < ν := by positivity
  have hℓ1 : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hκr0 : 0 < κr0 := by
    have : β ^ α < 1 := Real.rpow_lt_one hβ0.le hβ1 hα0
    linarith
  have hκr1 : 0 < κr1 := by positivity
  have hM : 1 ≤ max 1 (R ^ ι) := le_max_left _ _
  have hMpos : 0 < max 1 (R ^ ι) := one_pos.trans_le hM
  have hEps : 0 ≤ min (ε₀ ^ α) (ε₁ ^ ν) := le_min (by positivity) (by positivity)
  have hK : 0 ≤ min κr0 κr1 := le_min hκr0.le hκr1.le
  rcases le_or_gt b (β * a) with hcase | hcase
  · -- (5.1.26)–(5.1.27): the residual drops by the factor `β`
    have hbα : b ^ α ≤ β ^ α * a ^ α := by
      rw [← Real.mul_rpow hβ0.le ha.le]
      exact Real.rpow_le_rpow hb0.le hcase hα0.le
    have hba' : b ^ α ≤ a ^ α := Real.rpow_le_rpow hb0.le hba hα0.le
    have hε : ε₀ ^ α ≤ b ^ α := Real.rpow_le_rpow hε₀.le hb.le hα0.le
    calc min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) / max 1 (R ^ ι)
        ≤ min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) := div_le_self (mul_nonneg hK hEps) hM
      _ ≤ κr0 * ε₀ ^ α := mul_le_mul (min_le_left _ _) (min_le_left _ _) hEps hκr0.le
      _ ≤ κr0 * b ^ α := mul_le_mul_of_nonneg_left hε hκr0.le
      _ ≤ κr0 * a ^ α := mul_le_mul_of_nonneg_left hba' hκr0.le
      _ ≤ a ^ α - b ^ α := by
        have : κr0 * a ^ α = a ^ α - β ^ α * a ^ α := by ring
        linarith
  · -- (5.1.19)–(5.1.20): Lemma 5.1.3 and the decrease
    have hcasc := rpow_inv_two_pow_sub_ge hb0.le hba i hℓ
    -- the exponent of `a` splits as `(ℓ - 1) ν + ι`
    have hsplit : ((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1 = ((ℓ : ℝ) - 1) * ν + ι := by
      rw [hνdef, hιdef]; field_simp; ring
    rw [hsplit, Real.rpow_add ha] at hcasc
    have hA : 0 < a ^ (((ℓ : ℝ) - 1) * ν) := Real.rpow_pos_of_pos ha _
    have hI : 0 < a ^ ι := Real.rpow_pos_of_pos ha _
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    -- lower bound on `ω^ν`
    have hω0 : 0 ≤ ε₁ * b ^ (ℓ - 1) := by positivity
    have hων : ε₁ ^ ν * β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν) ≤ ω ^ ν := by
      have e1 : (ε₁ * b ^ (ℓ - 1)) ^ ν = ε₁ ^ ν * b ^ (((ℓ : ℝ) - 1) * ν) := by
        rw [Real.mul_rpow hε₁.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hb0.le, Nat.cast_sub hℓ, Nat.cast_one]
      have e2 : β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν) =
          (β * a) ^ (((ℓ : ℝ) - 1) * ν) := (Real.mul_rpow hβ0.le ha.le).symm
      have h1 : (β * a) ^ (((ℓ : ℝ) - 1) * ν) ≤ b ^ (((ℓ : ℝ) - 1) * ν) :=
        Real.rpow_le_rpow (by positivity) hcase.le (by positivity)
      have h2' : (ε₁ * b ^ (ℓ - 1)) ^ ν ≤ ω ^ ν := Real.rpow_le_rpow hω0 hω.le hν0.le
      rw [e1] at h2'
      rw [mul_assoc, e2]
      exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2'
    have hIR : a ^ ι ≤ max 1 (R ^ ι) :=
      (Real.rpow_le_rpow ha.le hRa hι).trans (le_max_right _ _)
    calc min κr0 κr1 * min (ε₀ ^ α) (ε₁ ^ ν) / max 1 (R ^ ι)
        ≤ κr1 * ε₁ ^ ν / a ^ ι := by
          apply div_le_div₀ (by positivity)
            (mul_le_mul (min_le_right _ _) (min_le_right _ _) hEps hκr1.le) hI hIR
      _ = ℓ * κ₁ * (ε₁ ^ ν * β ^ (((ℓ : ℝ) - 1) * ν) * a ^ (((ℓ : ℝ) - 1) * ν)) /
            (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          simp only [κr1]
          field_simp
      _ ≤ ℓ * κ₁ * ω ^ ν / (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          gcongr
      _ ≤ (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * (a ^ (((ℓ : ℝ) - 1) * ν) * a ^ ι)) := by
          gcongr
      _ ≤ _ := hcasc

end Cascade

end Optimization
