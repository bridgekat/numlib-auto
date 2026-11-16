/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Nonlinear.QuasiNewton

/-!
# Local convergence of Broyden's method: the Dennis–Moré theory

Let $F : \mathbb{R}^n \to \mathbb{R}^n$ have a root $z$, near which the Jacobian $J$ is Lipschitz
and $J(z)$ is invertible. Broyden's method computes $x_{k+1} = x_k - Q_k^{-1} F(x_k)$ and updates
the Jacobian approximation by $Q_{k+1} = Q_k + ((y_k - Q_k s_k) s_k^T)/(s_k^T s_k)$, with
$s_k = x_{k+1} - x_k$ and $y_k = F(x_{k+1}) - F(x_k)$. This module proves that Broyden's method
converges locally and superlinearly: if $x_0$ is close to $z$ and $Q_0$ is close to $J(z)$, then
every $Q_k$ is invertible, $\|x_k - z\| \le \varepsilon/2^k$, and
$\|x_{k+1} - z\| \le c_k \|x_k - z\|$ with $c_k \to 0$. This is Property 7.2 of
[quarteroni2000numerical], the theorem of [dennis1974characterization], and Theorem 8.2.2 of
[dennis1996numerical]. The iteration is `Broyden.iterate` of `Numlib.Nonlinear.QuasiNewton`, on
`EuclideanSpace ℝ n`.

The module does not claim that $Q_k \to J(z)$. This fails in general (Example 7.3 of
[quarteroni2000numerical]).

## Main definitions

* `Broyden.LipschitzJacobianRoot`: the standing hypotheses: $F$ is differentiable on a convex set
  $D$, and its Jacobian is Lipschitz at the root $z \in D$.
* `Broyden.dennisMoreQuotient`: the quotient $\eta_k = \|(Q_k - J(z)) s_k\| / \|s_k\|$.

## Main results

* `Matrix.sq_norm_mulVec_div_le_frobenius`: the Dennis–Moré inequality $\|A s\|^2/\|s\|^2 \le 2
  \|A\|_F (\|A\|_F - \|A (I - P)\|_F)$ for the projector $P$ onto $s$.
* `Matrix.sq_norm_sub_mulVec_div_le_broydenUpdate`: the Dennis–Moré inequality for Broyden's update.
* `Broyden.norm_step_x_sub_le`: one Broyden step from an operator $Q$ with
  $3\beta \|Q - J(z)\| \le 1$ is well defined, and $\|x_+ - z\| \le (3\beta/2)(\|Q - J(z)\| +
  (L/2)\|x - z\|)\|x - z\|$.
* `Broyden.frobenius_norm_symm_iterate_succ_sub_le`: bounded deterioration of the Jacobian
  approximations in the Frobenius norm.
* `Broyden.norm_iterate_sub_le_and_frobenius_norm_le`: local linear convergence,
  $\|x_k - z\| \le \varepsilon/2^k$.
* `Broyden.tendsto_dennisMoreQuotient`: the Dennis–Moré condition $\eta_k \to 0$.
* `Broyden.norm_iterate_succ_sub_le_mul`: the superlinear step bound $\|x_{k+1} - z\| \le
  4\beta(\eta_k + L\|x_k - z\|)\|x_k - z\|$.
* `Broyden.superlinear_of_le`: local superlinear convergence, quantitative form.
* `Broyden.exists_superlinear`: local superlinear convergence, existential form.

## Proof outline

The proof has three layers.

The first layer is the Frobenius geometry of the update. Let $P = s s^T/(s^T s)$ be the projector
onto the step. The Pythagoras identity $\|A (I - P)\|_F^2 + \|A P\|_F^2 = \|A\|_F^2$
(`Matrix.frobenius_norm_sq_mul_one_sub_add_sq_mul`) and the bound $\|A s\| \le \|A P\|_F \|s\|$ give
the Dennis–Moré inequality. For Broyden's update $Q_+$ with the errors $E = Q - J$ and
$E_+ = Q_+ - J$, it gives
$$\frac{\|E s\|^2}{\|s\|^2} \le 2 \|E\|_F \Bigl(\|E\|_F - \|E_+\|_F + \frac{\|y - J
  s\|}{\|s\|}\Bigr).$$
So the update cannot decrease the Frobenius error much unless the error along the step is small.

The second layer is bounded deterioration and linear convergence, the two-sequence induction of
Theorem 8.2.2 of [dennis1996numerical]. Let $\|J(z)^{-1}\| \le \beta$. One step from a $Q$ within
$1/(3\beta)$ of $J(z)$ is well defined and satisfies $\|x_+ - z\| \le (3\beta/2)(\|Q - J(z)\| +
(L/2)\|x - z\|)\|x - z\|$. Along the iteration, the matrices $M_k$ of $Q_k$ satisfy $\|M_{k+1} -
J(z)\|_F \le \|M_k - J(z)\|_F + (L/2)(\|x_{k+1} - z\| + \|x_k - z\|)$, by
`Matrix.frobenius_norm_broydenUpdate_sub_le_add`. Under the thresholds $12 \beta \delta \le 1$ and
$3 L \varepsilon \le 2\delta$, induction gives $\|x_k - z\| \le \varepsilon/2^k$ and
$\|M_k - J(z)\|_F \le 2\delta$.

The third layer is the Dennis–Moré condition and superlinear convergence. The sum of the Dennis–Moré
inequalities along the iteration telescopes the Frobenius errors. So the quotients $\eta_k$ are
square-summable and tend to $0$. The secant equation $Q_k s_k = -F(x_k)$ then gives $\|x_{k+1} - z\|
\le 4\beta(\eta_k + L\|x_k - z\|)\|x_k - z\|$. This is superlinear convergence with the explicit
factors $c_k = 4\beta(\eta_k + L\varepsilon/2^k) \to 0$.

## Implementation notes

* The Jacobian is a matrix-valued function `J : E → Matrix n n ℝ`, because the deterioration
  estimate is in the Frobenius norm. The operators $Q_k$ of `Broyden.iterate` are read back as
  matrices through `Matrix.toEuclideanCLM.symm` (`Broyden.symm_iterate_succ_Q`). The operator norm
  and the Frobenius norm are compared by `Matrix.norm_toEuclideanCLM_le_frobenius_norm` and
  `Matrix.frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM`.
* The invertibility of $J(z)$ is a continuous linear equivalence `e` whose underlying map is $J(z)$,
  and $\beta$ bounds the norm of its inverse.
* `Broyden.superlinear_of_le` takes the hypothesis on $Q_0$ in the Frobenius norm.
  `Broyden.exists_superlinear`, the existential form of the source, takes it in the operator norm.
-/

open scoped InnerProductSpace
open Filter Topology WithLp

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **The projected part of $A$ sees $A s$.** Let $A \in \mathbb{R}^{n \times n}$ and
$s \in \mathbb{R}^n$ with $s \neq 0$, and let $P = s s^T/(s^T s)$. Then
$$\|A s\|_2 \le \|A P\|_F \|s\|_2,$$
because $(A P) s = A s$. -/
theorem norm_mulVec_le_frobenius_norm_mul_proj (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖toLp 2 (A *ᵥ s)‖ ≤ ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ * ‖toLp 2 s‖ := by
  have h := frobenius_norm_mulVec_le (A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)) s
  rwa [← mulVec_mulVec, smul_vecMulVec_mulVec_self hs] at h

/-- **The Dennis–Moré inequality for the projection off a line.** Let
$A \in \mathbb{R}^{n \times n}$ and $s \in \mathbb{R}^n$ with $s \neq 0$, and let
$P = s s^T/(s^T s)$. Then
$$\frac{\|A s\|_2^2}{\|s\|_2^2} \le 2 \|A\|_F \bigl(\|A\|_F - \|A (I - P)\|_F\bigr).$$
This is the quantitative form of the fact that the update cannot decrease the Frobenius error
along $s$ without a cost. It is behind the superlinear convergence of Broyden's method (proof of
Theorem 8.2.2 of [dennis1996numerical]).

By the Pythagoras identity, $\|A s\|^2/\|s\|^2 \le \|A P\|_F^2 = \|A\|_F^2 - \|A (I - P)\|_F^2 =
(\|A\|_F - \|A (I - P)\|_F)(\|A\|_F + \|A (I - P)\|_F)$, and $\|A (I - P)\|_F \le \|A\|_F$. -/
theorem sq_norm_mulVec_div_le_frobenius (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖toLp 2 (A *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2
      ≤ 2 * ‖A‖ * (‖A‖ - ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖) := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hpyth := frobenius_norm_sq_mul_one_sub_add_sq_mul A hs
  have hproj := norm_mulVec_le_frobenius_norm_mul_proj A hs
  have hle := frobenius_norm_mul_one_sub_le A hs
  set a := ‖A‖
  set c := ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖
  set b := ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖
  have hq : ‖toLp 2 (A *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2 ≤ b ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ ‖toLp 2 (A *ᵥ s)‖ := norm_nonneg _
    calc ‖toLp 2 (A *ᵥ s)‖ ^ 2 ≤ (b * ‖toLp 2 s‖) ^ 2 := pow_le_pow_left₀ h0 hproj 2
      _ = b ^ 2 * ‖toLp 2 s‖ ^ 2 := by ring
  nlinarith

/-- **The Dennis–Moré inequality for Broyden's update** (proof of Theorem 8.2.2 of
[dennis1996numerical]). Let $Q, J \in \mathbb{R}^{n \times n}$ and $s, y \in \mathbb{R}^n$ with
$s \neq 0$. Let $Q_+ = Q + ((y - Q s) s^T)/(s^T s)$ be Broyden's update, and let $E = Q - J$ and
$E_+ = Q_+ - J$ be the errors before and after the update. Then
$$\frac{\|E s\|_2^2}{\|s\|_2^2} \le 2 \|E\|_F \Bigl(\|E\|_F - \|E_+\|_F + \frac{\|y - J
  s\|_2}{\|s\|_2}\Bigr).$$

The proof uses $E_+ = E (I - P) + ((y - J s) s^T)/(s^T s)$, so $\|E_+\|_F \le \|E (I - P)\|_F +
\|y - J s\|/\|s\|$, and `Matrix.sq_norm_mulVec_div_le_frobenius`. Along Broyden's iteration,
$\|y - J s\|/\|s\|$ is $O(\|x - z\|)$ and the Frobenius errors are bounded. So the sum of these
inequalities forces $\|E_k s_k\|/\|s_k\| \to 0$, the Dennis–Moré condition for superlinear
convergence. -/
theorem sq_norm_sub_mulVec_div_le_broydenUpdate (Q J : Matrix n n ℝ) {s y : n → ℝ}
    (hs : s ≠ 0) :
    ‖toLp 2 ((Q - J) *ᵥ s)‖ ^ 2 / ‖toLp 2 s‖ ^ 2
      ≤ 2 * ‖Q - J‖ * (‖Q - J‖ - ‖broydenUpdate Q s y - J‖
          + ‖toLp 2 (y - J *ᵥ s)‖ / ‖toLp 2 s‖) := by
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  set w : n → ℝ := y - J *ᵥ s with hw
  have h1 : ‖broydenUpdate Q s y - J‖ ≤ ‖(Q - J) * (1 - P)‖ + ‖toLp 2 w‖ / ‖toLp 2 s‖ := by
    rw [broydenUpdate_sub_eq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (frobenius_norm_smul_vecMulVec_le _ _))
  have h2 := sq_norm_mulVec_div_le_frobenius (Q - J) hs
  have h3 : 0 ≤ ‖Q - J‖ := norm_nonneg _
  refine h2.trans ?_
  rw [← hPdef]
  nlinarith

end Frobenius

end Matrix

namespace Broyden

open Matrix Metric

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "E" => EuclideanSpace ℝ n

/-- **The standing hypotheses of the local convergence theory** (Theorem 8.2.2 of
[dennis1996numerical], Theorem 7.1 of [quarteroni2000numerical]). Let
$F : \mathbb{R}^n \to \mathbb{R}^n$, $J : \mathbb{R}^n \to \mathbb{R}^{n \times n}$,
$D \subseteq \mathbb{R}^n$, $z \in \mathbb{R}^n$ and $L \in \mathbb{R}$. The hypotheses are: $D$
is convex; $F$ is differentiable at every $w \in D$ with Jacobian matrix $J(w)$; $z \in D$ and
$F(z) = 0$; the Jacobian is Lipschitz at $z$ on $D$ with constant $L \ge 0$, that is,
$$\|J(w) - J(z)\| \le L \|w - z\| \quad \text{for } w \in D,$$
in the Euclidean operator norm. -/
structure LipschitzJacobianRoot (F : E → E) (J : E → Matrix n n ℝ) (D : Set E) (z : E)
    (L : ℝ) : Prop where
  /-- The set $D$ is convex. -/
  convex : Convex ℝ D
  /-- The map $F$ has the Jacobian matrix $J(w)$ at every $w \in D$. -/
  hasFDerivAt : ∀ w ∈ D, HasFDerivAt F (toEuclideanCLM (𝕜 := ℝ) (J w)) w
  /-- The point $z$ is a root: $F(z) = 0$. -/
  root : F z = 0
  /-- The root $z$ lies in $D$. -/
  mem : z ∈ D
  /-- The Jacobian is Lipschitz at $z$ on $D$: $\|J(w) - J(z)\| \le L \|w - z\|$ for $w \in D$, in
  the operator norm. -/
  lipschitz : ∀ w ∈ D,
    ‖toEuclideanCLM (𝕜 := ℝ) (J w) - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ L * ‖w - z‖
  /-- The Lipschitz constant is nonnegative. This is automatic unless $D = \{z\}$. -/
  nonneg : 0 ≤ L

-- the local notation `E` must not be used in `variable` lines (it elaborates to `sorry` there)
variable {F : EuclideanSpace ℝ n → EuclideanSpace ℝ n} {J : EuclideanSpace ℝ n → Matrix n n ℝ}
  {D : Set (EuclideanSpace ℝ n)} {z : EuclideanSpace ℝ n} {L : ℝ}

/-- **The quadratic remainder at the root.** Under `Broyden.LipschitzJacobianRoot`, for every
$x \in D$,
$$\|F(x) - J(z)(x - z)\| \le \frac{L}{2} \|x - z\|^2.$$
This is the mean value inequality with three points, with $z$ as the base point. -/
theorem LipschitzJacobianRoot.norm_sub_apply_le (h : LipschitzJacobianRoot F J D z L) {x : E}
    (hx : x ∈ D) : ‖F x - toEuclideanCLM (𝕜 := ℝ) (J z) (x - z)‖ ≤ L / 2 * ‖x - z‖ ^ 2 := by
  have hmv := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add h.convex h.hasFDerivAt
    (x := z) (y := x) h.mem hx h.lipschitz
  rw [h.root, sub_zero, sub_self, norm_zero, zero_add] at hmv
  linarith [sq ‖x - z‖]

/-- **The secant remainder.** Under `Broyden.LipschitzJacobianRoot`, for all $x, y \in D$,
$$\|F(y) - F(x) - J(z)(y - x)\| \le \frac{L}{2} \bigl(\|x - z\| + \|y - z\|\bigr) \|y - x\|.$$
-/
theorem LipschitzJacobianRoot.norm_sub_sub_apply_le (h : LipschitzJacobianRoot F J D z L)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖F y - F x - toEuclideanCLM (𝕜 := ℝ) (J z) (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ :=
  Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add h.convex h.hasFDerivAt hx hy
    h.lipschitz

/-- **One Broyden step near the root** (proof of Theorem 8.2.2 of [dennis1996numerical]). Assume
`Broyden.LipschitzJacobianRoot`, let $J(z)$ be invertible with $\|J(z)^{-1}\| \le \beta$, and
let $x \in D$. Let $Q$ be an operator on $\mathbb{R}^n$ with $3 \beta \|Q - J(z)\| \le 1$, in
the operator norm. Then $Q$ is invertible with $\|Q^{-1}\| \le 3\beta/2$, and the point
$x_+ = x - Q^{-1} F(x)$ of `Broyden.step` satisfies
$$\|x_+ - z\| \le \frac{3\beta}{2} \Bigl(\|Q - J(z)\| + \frac{L}{2} \|x - z\|\Bigr) \|x - z\|.$$

The invertibility of $Q$ is the perturbation theorem
`ContinuousLinearEquiv.exists_symm_norm_le_of_add`. The bound follows from $x_+ - z =
Q^{-1}\bigl((Q - J(z))(x - z) - (F(x) - J(z)(x - z))\bigr)$. -/
theorem norm_step_x_sub_le (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {x : E} (hx : x ∈ D) {Q : E →L[ℝ] E}
    (hQ : 3 * (β * ‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖) ≤ 1) :
    (∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = Q ∧ ‖(e'.symm : E →L[ℝ] E)‖ ≤ 3 * β / 2) ∧
      ‖(step F ⟨x, Q⟩).x - z‖
        ≤ 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) * ‖x - z‖ := by
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  set t : E →L[ℝ] E := Q - Js with ht
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hes : ‖(e.symm : E →L[ℝ] E)‖ * ‖t‖ ≤ β * ‖t‖ := mul_le_mul_of_nonneg_right hβ ht0
  have hlt : ‖(e.symm : E →L[ℝ] E)‖ * ‖t‖ < 1 := by linarith
  obtain ⟨e', he', he'inv, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add e t hlt
  have he'Q : (e' : E →L[ℝ] E) = Q := by rw [he', he, ht]; abel
  have hinv : ‖(e'.symm : E →L[ℝ] E)‖ ≤ 3 * β / 2 := by
    refine he'inv.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (e.symm : E →L[ℝ] E)]
  refine ⟨⟨e', he'Q, hinv⟩, ?_⟩
  have hstep : (step F ⟨x, Q⟩).x - z = e'.symm (Q (x - z) - F x) := by
    rw [step_x]
    change x - Q.inverse (F x) - z = e'.symm (Q (x - z) - F x)
    rw [← he'Q, ContinuousLinearMap.inverse_equiv, map_sub]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hmv := h.norm_sub_apply_le hx
  have hdecomp : Q (x - z) - F x = t (x - z) - (F x - Js (x - z)) := by
    rw [ht, _root_.sub_apply]
    abel
  calc ‖(step F ⟨x, Q⟩).x - z‖ = ‖e'.symm (Q (x - z) - F x)‖ := by rw [hstep]
    _ ≤ ‖(e'.symm : E →L[ℝ] E)‖ * ‖Q (x - z) - F x‖ := (e'.symm : E →L[ℝ] E).le_opNorm _
    _ ≤ 3 * β / 2 * (‖t‖ * ‖x - z‖ + L / 2 * ‖x - z‖ ^ 2) := by
        refine mul_le_mul hinv ?_ (norm_nonneg _) (by positivity)
        rw [hdecomp]
        exact (norm_sub_le _ _).trans (add_le_add (t.le_opNorm _) hmv)
    _ = 3 * β / 2 * (‖t‖ + L / 2 * ‖x - z‖) * ‖x - z‖ := by ring

/-! ### The iteration: bounded deterioration and linear convergence -/

section Iteration

open scoped Matrix.Norms.Frobenius

/-- **The matrix recurrence of Broyden's iteration.** For every $F$, $x_0$ and $Q_0$, let $M_k$ be
the matrix of the operator $Q_k$ of `Broyden.iterate`. Then $M_{k+1}$ is Broyden's update of
$M_k$ with the secant pair $s_k = x_{k+1} - x_k$ and $y_k = F(x_{k+1}) - F(x_k)$:
$$M_{k+1} = M_k + \frac{(y_k - M_k s_k) s_k^T}{s_k^T s_k}.$$

This is `Broyden.step_Q`, read through `Matrix.toEuclideanCLM_broydenUpdate`. -/
theorem symm_iterate_succ_Q (F : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) :
    (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q
      = broydenUpdate ((toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q)
          (ofLp ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x))
          (ofLp (F (iterate F x₀ Q₀ (k + 1)).x - F (iterate F x₀ Q₀ k).x)) := by
  rw [StarAlgEquiv.symm_apply_eq, toEuclideanCLM_broydenUpdate, StarAlgEquiv.apply_symm_apply,
    toLp_ofLp, toLp_ofLp, iterate_succ, step_Q]

/-- For every matrix $M$, the operator $Q_k - M$ is the operator of the matrix $M_k - M$, where
$M_k$ is the matrix of $Q_k$. -/
theorem iterate_Q_sub_eq (F : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) (M : Matrix n n ℝ) :
    (iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) M
      = toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - M) := by
  rw [map_sub, StarAlgEquiv.apply_symm_apply]

/-- **Bounded deterioration along Broyden's iteration** (Lemma 8.2.1 of [dennis1996numerical], at
every step). Assume `Broyden.LipschitzJacobianRoot`, and let $x_k, x_{k+1} \in D$. Then, in the
Frobenius norm,
$$\|M_{k+1} - J(z)\|_F \le \|M_k - J(z)\|_F + \frac{L}{2} \bigl(\|x_{k+1} - z\| + \|x_k -
  z\|\bigr).$$

A zero step $x_{k+1} = x_k$ leaves $M_k$ unchanged. -/
theorem frobenius_norm_symm_iterate_succ_sub_le (h : LipschitzJacobianRoot F J D z L)
    {x₀ : E} {Q₀ : E →L[ℝ] E} {k : ℕ} (hk : (iterate F x₀ Q₀ k).x ∈ D)
    (hk1 : (iterate F x₀ Q₀ (k + 1)).x ∈ D) :
    ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q - J z‖
      ≤ ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        + L / 2 * (‖(iterate F x₀ Q₀ (k + 1)).x - z‖ + ‖(iterate F x₀ Q₀ k).x - z‖) := by
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q with hM
  rw [symm_iterate_succ_Q, ← hx, ← hx', ← hM]
  have hpos : 0 ≤ L / 2 * (‖x' - z‖ + ‖x - z‖) := by
    have := h.nonneg
    positivity
  by_cases hs : ofLp (x' - x) = 0
  · rw [hs, Matrix.broydenUpdate_zero_left]
    linarith
  · have hxs : x + toLp 2 (ofLp (x' - x)) ∈ D := by
      rwa [toLp_ofLp, add_sub_cancel]
    have := frobenius_norm_broydenUpdate_sub_le_add h.convex h.hasFDerivAt h.lipschitz hk hs hxs M
    simpa only [toLp_ofLp, add_sub_cancel] using this

/-- **The two-sequence induction of Theorem 8.2.2** of [dennis1996numerical], local linear
convergence of Broyden's method. Assume `Broyden.LipschitzJacobianRoot`, and let $J(z)$ be
invertible with $\|J(z)^{-1}\| \le \beta$. Let $\varepsilon \ge 0$ and $\delta$ satisfy
$12 \beta \delta \le 1$, $3 L \varepsilon \le 2\delta$ and $\bar B(z, \varepsilon) \subseteq D$.
Let $\|x_0 - z\| \le \varepsilon$, and let the matrix $M_0$ of $Q_0$ satisfy
$\|M_0 - J(z)\|_F \le \delta$. Then for every $k$,
$$\|x_k - z\| \le \frac{\varepsilon}{2^k} \quad \text{and} \quad \|M_k - J(z)\|_F \le \delta +
  \frac{3L}{2} \varepsilon \Bigl(1 - \frac{1}{2^k}\Bigr),$$
and in particular $\|M_k - J(z)\|_F \le 2\delta$.

The thresholds give $3 \beta L \varepsilon \le 1/6$. The step estimate
`Broyden.norm_step_x_sub_le` halves the error, because
$(3\beta/2)(2\delta + L\varepsilon/2) \le 1/2$. The bounded deterioration adds at most
$(L/2)(3/2)\varepsilon/2^k$ to the Frobenius error, and the sum of these terms stays below
$\delta$. -/
theorem norm_iterate_sub_le_and_frobenius_norm_le (h : LipschitzJacobianRoot F J D z L)
    (e : E ≃L[ℝ] E) (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε)
    (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) (k : ℕ) :
    ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k ∧
      ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        ≤ δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ k) := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  have hL0 : 0 ≤ L := h.nonneg
  induction k with
  | zero => simpa using ⟨hx₀, hQ₀⟩
  | succ k ih =>
    obtain ⟨ihx, ihM⟩ := ih
    set x : E := (iterate F x₀ Q₀ k).x with hx
    set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
    set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm Q with hM
    have haε : ε / 2 ^ k ≤ ε := div_le_self hε (one_le_pow₀ (by norm_num))
    have hsucc : ε / 2 ^ (k + 1) = ε / 2 ^ k / 2 := by rw [pow_succ, div_div]
    have h2k : (1 : ℝ) / 2 ^ (k + 1) = 1 / 2 ^ k / 2 := by rw [pow_succ, div_div]
    have hxD : x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      exact ihx.trans haε)
    -- the operator error is at most the Frobenius error, at most `2δ`
    have hM2 : ‖M - J z‖ ≤ 2 * δ := by
      have : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
        have h1 : 0 ≤ 3 * L / 2 * ε := by positivity
        have h2 : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
        nlinarith
      linarith
    have hQJ : ‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ 2 * δ := by
      rw [hQ, iterate_Q_sub_eq, ← hQ, ← hM]
      exact (norm_toEuclideanCLM_le_frobenius_norm _).trans hM2
    -- one step
    obtain ⟨-, hstep⟩ := norm_step_x_sub_le h e he hβ hxD (Q := Q) (by nlinarith)
    have hxk1 : (iterate F x₀ Q₀ (k + 1)).x = (step F ⟨x, Q⟩).x := by
      rw [iterate_succ]
    have hx' : ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ ε / 2 ^ (k + 1) := by
      rw [hxk1, hsucc]
      refine hstep.trans ?_
      have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
      have hcoef : 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) ≤ 1 / 2 := by
        have h1 : ‖x - z‖ ≤ ε := ihx.trans haε
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hβ0 hL0)]
      calc 3 * β / 2 * (‖Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ + L / 2 * ‖x - z‖) * ‖x - z‖
          ≤ 1 / 2 * ‖x - z‖ := mul_le_mul_of_nonneg_right hcoef hxz
        _ ≤ 1 / 2 * (ε / 2 ^ k) := mul_le_mul_of_nonneg_left ihx (by norm_num)
        _ = ε / 2 ^ k / 2 := by ring
    refine ⟨hx', ?_⟩
    -- bounded deterioration
    have hx'D : (iterate F x₀ Q₀ (k + 1)).x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      refine hx'.trans ?_
      rw [hsucc]
      linarith)
    have hdet := frobenius_norm_symm_iterate_succ_sub_le h hxD hx'D
    rw [← hx, ← hQ, ← hM] at hdet
    refine hdet.trans ?_
    rw [hsucc] at hx'
    have hrest : L / 2 * (‖(iterate F x₀ Q₀ (k + 1)).x - z‖ + ‖x - z‖)
        ≤ L / 2 * (ε / 2 ^ k / 2 + ε / 2 ^ k) :=
      mul_le_mul_of_nonneg_left (add_le_add hx' ihx) (by positivity)
    have hgeom : δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ k) + L / 2 * (ε / 2 ^ k / 2 + ε / 2 ^ k)
        = δ + 3 * L / 2 * ε * (1 - 1 / 2 ^ (k + 1)) := by
      rw [h2k]
      field_simp
      ring
    linarith

end Iteration

/-! ### The Dennis–Moré condition and superlinear convergence -/

section Superlinear

open scoped Matrix.Norms.Frobenius

/-- **The Dennis–Moré inequality along Broyden's iteration.** Assume
`Broyden.LipschitzJacobianRoot`, and let $x_k, x_{k+1} \in D$. Let $s_k = x_{k+1} - x_k$ and
$\eta_k = \|(Q_k - J(z)) s_k\|/\|s_k\|$, the relative error of the Jacobian approximation along
the step. Then
$$\eta_k^2 \le 2 \|M_k - J(z)\|_F \Bigl(\|M_k - J(z)\|_F - \|M_{k+1} - J(z)\|_F + \frac{L}{2}
  \bigl(\|x_k - z\| + \|x_{k+1} - z\|\bigr)\Bigr).$$

This is `Matrix.sq_norm_sub_mulVec_div_le_broydenUpdate`, with the secant remainder bounded by
the mean value inequality. A zero step gives $\eta_k = 0$ and $M_{k+1} = M_k$. -/
theorem sq_norm_iterate_sub_apply_div_le (h : LipschitzJacobianRoot F J D z L) {x₀ : E}
    {Q₀ : E →L[ℝ] E} {k : ℕ} (hk : (iterate F x₀ Q₀ k).x ∈ D)
    (hk1 : (iterate F x₀ Q₀ (k + 1)).x ∈ D) :
    (‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
        ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
        / ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖) ^ 2
      ≤ 2 * ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
        * (‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q - J z‖
            - ‖(toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q - J z‖
            + L / 2 * (‖(iterate F x₀ Q₀ k).x - z‖ + ‖(iterate F x₀ Q₀ (k + 1)).x - z‖)) := by
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
  set M : Matrix n n ℝ := (toEuclideanCLM (𝕜 := ℝ)).symm Q with hM
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  have hM' : (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ (k + 1)).Q
      = broydenUpdate M (ofLp (x' - x)) (ofLp (F x' - F x)) := symm_iterate_succ_Q F x₀ Q₀ k
  rw [hM']
  have hL0 := h.nonneg
  by_cases hs : x' - x = 0
  · have hs0 : ofLp (x' - x) = 0 := by rw [hs]; rfl
    rw [hs0, hs, broydenUpdate_zero_left, map_zero, norm_zero, div_zero, sub_self, zero_add,
      zero_pow two_ne_zero]
    positivity
  · have hs' : ofLp (x' - x) ≠ 0 := fun h0 => hs (by simpa using congrArg (toLp 2) h0)
    have key := sq_norm_sub_mulVec_div_le_broydenUpdate M (J z) (y := ofLp (F x' - F x)) hs'
    have e1 : toLp 2 ((M - J z) *ᵥ ofLp (x' - x)) = (Q - Js) (x' - x) := by
      rw [← toEuclideanCLM_toLp, toLp_ofLp]
      congr 1
      rw [map_sub, hM, StarAlgEquiv.apply_symm_apply]
    have e3 : toLp 2 (ofLp (F x' - F x) - J z *ᵥ ofLp (x' - x)) = F x' - F x - Js (x' - x) := by
      rw [toLp_sub, toLp_ofLp, ← toEuclideanCLM_toLp, toLp_ofLp]
    rw [e1, toLp_ofLp, e3] at key
    rw [div_pow]
    refine key.trans ?_
    have hmv := h.norm_sub_sub_apply_le hk hk1
    have hs0 : 0 < ‖x' - x‖ := norm_pos_iff.2 hs
    have hq : ‖F x' - F x - Js (x' - x)‖ / ‖x' - x‖ ≤ L / 2 * (‖x - z‖ + ‖x' - z‖) := by
      rw [div_le_iff₀ hs0]
      exact hmv
    gcongr

/-- The **Dennis–Moré quotient** $\eta_k = \|(Q_k - J(z)) s_k\|/\|s_k\|$ of Broyden's iteration,
with $s_k = x_{k+1} - x_k$. For $s_k = 0$ its value is $0$, because division by zero gives $0$
in Lean. -/
noncomputable def dennisMoreQuotient (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) : ℝ :=
  ‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
      ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
    / ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖

/-- The Dennis–Moré quotient is nonnegative: $\eta_k \ge 0$. -/
theorem dennisMoreQuotient_nonneg (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) : 0 ≤ dennisMoreQuotient F J z x₀ Q₀ k :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- For every $k$, $\|(Q_k - J(z)) s_k\| \le \eta_k \|s_k\|$. In fact equality holds, also for
$s_k = 0$, where both sides are $0$. -/
theorem norm_sub_apply_le_dennisMoreQuotient_mul (F : E → E) (J : E → Matrix n n ℝ) (z x₀ : E)
    (Q₀ : E →L[ℝ] E) (k : ℕ) :
    ‖((iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z))
        ((iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x)‖
      ≤ dennisMoreQuotient F J z x₀ Q₀ k
        * ‖(iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x‖ := by
  rw [dennisMoreQuotient]
  by_cases hs : (iterate F x₀ Q₀ (k + 1)).x - (iterate F x₀ Q₀ k).x = 0
  · rw [hs, map_zero, norm_zero, div_zero, zero_mul]
  · rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hs)]

/-- **The Dennis–Moré condition holds along Broyden's iteration** (proof of Theorem 8.2.2 of
[dennis1996numerical]). Under the hypotheses of
`Broyden.norm_iterate_sub_le_and_frobenius_norm_le`, the Dennis–Moré quotient tends to $0$:
$$\eta_k = \frac{\|(Q_k - J(z)) s_k\|}{\|s_k\|} \to 0.$$

The sum of the inequalities `Broyden.sq_norm_iterate_sub_apply_div_le` telescopes the Frobenius
errors. Their total variation is at most $\|M_0 - J(z)\|_F + (L/2) \sum_k (\|x_k - z\| +
\|x_{k+1} - z\|) \le \delta + 2 L \varepsilon$, so $\sum_k \eta_k^2 \le 4\delta(\delta + 2 L
\varepsilon) < \infty$. -/
theorem tendsto_dennisMoreQuotient (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) :
    Tendsto (dennisMoreQuotient F J z x₀ Q₀) atTop (𝓝 0) := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hQ₀
  set η := dennisMoreQuotient F J z x₀ Q₀ with hη
  set xs : ℕ → E := fun k => (iterate F x₀ Q₀ k).x with hxs
  set Ms : ℕ → Matrix n n ℝ := fun k => (toEuclideanCLM (𝕜 := ℝ)).symm (iterate F x₀ Q₀ k).Q
    with hMs
  have hpow : ∀ k, ε / 2 ^ k = ε * (1 / 2 : ℝ) ^ k := fun k => by
    rw [_root_.one_div_pow, div_eq_mul_one_div]
  have hxk : ∀ k, xs k ∈ D := fun k => hball (by
    rw [mem_closedBall, dist_eq_norm]
    exact (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num))))
  have hM2 : ∀ k, ‖Ms k - J z‖ ≤ 2 * δ := fun k => by
    have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
      have : 0 ≤ 3 * L / 2 * ε := by positivity
      have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
      nlinarith
    linarith [(hinv k).2]
  -- the bracket of the Dennis–Moré inequality, nonnegative by bounded deterioration
  set b : ℕ → ℝ := fun k => ‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖
    + L / 2 * (‖xs k - z‖ + ‖xs (k + 1) - z‖) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    have := frobenius_norm_symm_iterate_succ_sub_le h (hxk k) (hxk (k + 1))
    simp only [hb]
    linarith
  have hη2 : ∀ k, η k ^ 2 ≤ 4 * δ * b k := fun k => by
    have h1 := sq_norm_iterate_sub_apply_div_le h (hxk k) (hxk (k + 1))
    have h2 : 2 * ‖Ms k - J z‖ * b k ≤ 4 * δ * b k := by
      have := hM2 k
      have := hb0 k
      nlinarith
    exact h1.trans h2
  -- the partial sums of the bracket telescope
  have hsum : ∀ N, ∑ k ∈ Finset.range N, b k ≤ δ + 2 * L * ε := fun N => by
    have htel : ∑ k ∈ Finset.range N, (‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖)
        = ‖Ms 0 - J z‖ - ‖Ms N - J z‖ := Finset.sum_range_sub' (fun k => ‖Ms k - J z‖) N
    have hgeo : ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖) ≤ 4 * ε := by
      calc ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖)
          ≤ ∑ k ∈ Finset.range N, 2 * ε * (1 / 2 : ℝ) ^ k := by
            refine Finset.sum_le_sum fun k _ => ?_
            have h1 := (hinv k).1
            have h2 := (hinv (k + 1)).1
            rw [hpow] at h1 h2
            have h3 : ε * (1 / 2 : ℝ) ^ (k + 1) ≤ ε * (1 / 2 : ℝ) ^ k := by
              rw [pow_succ]
              have : 0 ≤ ε * (1 / 2 : ℝ) ^ k := by positivity
              linarith
            linarith
        _ = 2 * ε * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * ε * 2 := by gcongr; exact sum_geometric_two_le N
        _ = 4 * ε := by ring
    have hM0 : ‖Ms 0 - J z‖ ≤ δ := hQ₀
    have hMN : 0 ≤ ‖Ms N - J z‖ := norm_nonneg _
    calc ∑ k ∈ Finset.range N, b k
        = ∑ k ∈ Finset.range N, (‖Ms k - J z‖ - ‖Ms (k + 1) - J z‖)
          + L / 2 * ∑ k ∈ Finset.range N, (‖xs k - z‖ + ‖xs (k + 1) - z‖) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ δ + L / 2 * (4 * ε) := by
          rw [htel]
          gcongr
          linarith
      _ = δ + 2 * L * ε := by ring
  have hsum2 : ∀ N, ∑ k ∈ Finset.range N, η k ^ 2 ≤ 4 * δ * (δ + 2 * L * ε) := fun N =>
    (Finset.sum_le_sum fun k _ => hη2 k).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum N) (by positivity))
  have hsumm : Summable fun k => η k ^ 2 :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hsum2
  have h0 := hsumm.tendsto_atTop_zero.sqrt
  rw [Real.sqrt_zero] at h0
  exact h0.congr fun k => Real.sqrt_sq (dennisMoreQuotient_nonneg F J z x₀ Q₀ k)

/-- **The superlinear step bound** (Lemma 8.2.3 and Theorem 8.2.4 of [dennis1996numerical], the "if"
half of the Dennis–Moré characterization in a quantitative form). Under the hypotheses of
`Broyden.norm_iterate_sub_le_and_frobenius_norm_le`, for every $k$,
$$\|x_{k+1} - z\| \le 4\beta \bigl(\eta_k + L \|x_k - z\|\bigr) \|x_k - z\|.$$

From $Q_k s_k = -F(x_k)$ follows $F(x_{k+1}) = (F(x_{k+1}) - F(x_k) - J(z) s_k) - (Q_k - J(z))
s_k$. So $\|F(x_{k+1})\| \le (\eta_k + L\|x_k - z\|)\|s_k\|$ with $\|s_k\| \le 2\|x_k - z\|$.
Also $\|x_{k+1} - z\| \le \beta \|J(z)(x_{k+1} - z)\| \le \beta(\|F(x_{k+1})\| +
(L/2)\|x_{k+1} - z\|^2)$ and $\beta L \|x_{k+1} - z\| \le 1/3$. -/
theorem norm_iterate_succ_sub_le_mul (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) (k : ℕ) :
    ‖(iterate F x₀ Q₀ (k + 1)).x - z‖
      ≤ 4 * β * (dennisMoreQuotient F J z x₀ Q₀ k + L * ‖(iterate F x₀ Q₀ k).x - z‖)
        * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  set x : E := (iterate F x₀ Q₀ k).x with hx
  set x' : E := (iterate F x₀ Q₀ (k + 1)).x with hx'
  set Q : E →L[ℝ] E := (iterate F x₀ Q₀ k).Q with hQ
  set Js : E →L[ℝ] E := toEuclideanCLM (𝕜 := ℝ) (J z) with hJs
  set η : ℝ := dennisMoreQuotient F J z x₀ Q₀ k with hηdef
  have hη0 : 0 ≤ η := dennisMoreQuotient_nonneg F J z x₀ Q₀ k
  have hηs : ‖(Q - Js) (x' - x)‖ ≤ η * ‖x' - x‖ :=
    norm_sub_apply_le_dennisMoreQuotient_mul F J z x₀ Q₀ k
  have hxε : ‖x - z‖ ≤ ε := (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num)))
  have hx'ε : ‖x' - z‖ ≤ ε := (hinv (k + 1)).1.trans (div_le_self hε (one_le_pow₀ (by norm_num)))
  have hxD : x ∈ D := hball (by rw [mem_closedBall, dist_eq_norm]; exact hxε)
  have hx'D : x' ∈ D := hball (by rw [mem_closedBall, dist_eq_norm]; exact hx'ε)
  -- the operator error is at most `2δ`, so the step lemma applies
  have hQJ : ‖Q - Js‖ ≤ 2 * δ := by
    have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
      have : 0 ≤ 3 * L / 2 * ε := by positivity
      have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
      nlinarith
    rw [hQ, hJs, iterate_Q_sub_eq]
    exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (by linarith [(hinv k).2])
  obtain ⟨⟨e', he'Q, -⟩, hstep⟩ := norm_step_x_sub_le h e he hβ hxD (Q := Q) (by nlinarith)
  have hxk1 : x' = (step F ⟨x, Q⟩).x := by rw [hx', iterate_succ]
  -- `‖x' - z‖ ≤ ‖x - z‖ / 2`
  have hhalf : ‖x' - z‖ ≤ ‖x - z‖ / 2 := by
    rw [hxk1]
    refine hstep.trans ?_
    have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
    have hcoef : 3 * β / 2 * (‖Q - Js‖ + L / 2 * ‖x - z‖) ≤ 1 / 2 := by
      have h1 : β * ‖Q - Js‖ ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hQJ hβ0
      have h2 : β * L * ‖x - z‖ ≤ β * L * ε := mul_le_mul_of_nonneg_left hxε (mul_nonneg hβ0 hL0)
      have h3 : β * (3 * L * ε) ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hLε hβ0
      linarith
    calc 3 * β / 2 * (‖Q - Js‖ + L / 2 * ‖x - z‖) * ‖x - z‖
        ≤ 1 / 2 * ‖x - z‖ := mul_le_mul_of_nonneg_right hcoef hxz
      _ = ‖x - z‖ / 2 := by ring
  -- the secant equation of the step: `Q s = -F x`
  have hsec : Q (x' - x) = -F x := by
    rw [hxk1]
    exact apply_step_x_sub F ⟨x, Q⟩ e' he'Q
  -- the residual at `x'`
  have hFx' : F x' = (F x' - F x - Js (x' - x)) - (Q - Js) (x' - x) := by
    rw [_root_.sub_apply, hsec]
    abel
  have hmv := h.norm_sub_sub_apply_le hxD hx'D
  have hs : ‖x' - x‖ ≤ 2 * ‖x - z‖ := by
    have : x' - x = (x' - z) - (x - z) := by abel
    rw [this]
    linarith [norm_sub_le (x' - z) (x - z), norm_nonneg (x - z)]
  have hFbound : ‖F x'‖ ≤ (η + L * ‖x - z‖) * (2 * ‖x - z‖) := by
    rw [hFx']
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖F x' - F x - Js (x' - x)‖ ≤ L * ‖x - z‖ * ‖x' - x‖ := by
      refine hmv.trans ?_
      have : L / 2 * (‖x - z‖ + ‖x' - z‖) ≤ L * ‖x - z‖ := by
        linarith [mul_le_mul_of_nonneg_left hhalf hL0, mul_nonneg hL0 (norm_nonneg (x - z))]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hxz : 0 ≤ ‖x - z‖ := norm_nonneg _
    linarith [mul_le_mul_of_nonneg_left hs (add_nonneg hη0 (mul_nonneg hL0 hxz))]
  -- the lower bound `‖x' - z‖ ≤ β (‖F x'‖ + (L / 2) ‖x' - z‖²)`
  have hlow : ‖x' - z‖ ≤ β * (‖F x'‖ + L / 2 * ‖x' - z‖ ^ 2) := by
    have h2 : e (x' - z) = Js (x' - z) := by rw [← he]; rfl
    have h3 : Js (x' - z) = F x' - (F x' - Js (x' - z)) := by abel
    have h4 := h.norm_sub_apply_le hx'D
    calc ‖x' - z‖ = ‖(e.symm : E →L[ℝ] E) (e (x' - z))‖ := by simp
      _ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖e (x' - z)‖ := (e.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ β * ‖e (x' - z)‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
      _ ≤ β * (‖F x'‖ + L / 2 * ‖x' - z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hβ0
          rw [h2, h3]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl h4)
  -- `β L ‖x' - z‖ ≤ 1 / 3`
  have hβL : 3 * (β * L * ‖x' - z‖) ≤ 1 := by
    have h1 : β * L * ‖x' - z‖ ≤ β * L * ε := mul_le_mul_of_nonneg_left hx'ε (by positivity)
    have h2 : β * (3 * L * ε) ≤ β * (2 * δ) := mul_le_mul_of_nonneg_left hLε hβ0
    linarith
  have hx'z : 0 ≤ ‖x' - z‖ := norm_nonneg _
  -- `(5 / 6) ‖x' - z‖ ≤ β ‖F x'‖`
  have h56 : 5 / 6 * ‖x' - z‖ ≤ β * ‖F x'‖ := by
    have h1 : β * L * ‖x' - z‖ * ‖x' - z‖ ≤ 1 / 3 * ‖x' - z‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hx'z
    linarith
  calc ‖x' - z‖ ≤ 6 / 5 * (β * ‖F x'‖) := by linarith
    _ ≤ 6 / 5 * (β * ((η + L * ‖x - z‖) * (2 * ‖x - z‖))) := by gcongr
    _ ≤ 4 * β * (η + L * ‖x - z‖) * ‖x - z‖ := by
        have : 0 ≤ β * ((η + L * ‖x - z‖) * ‖x - z‖) := by positivity
        linarith

end Superlinear

/-! ### The convergence theorem -/

section Main

open scoped Matrix.Norms.Frobenius

/-- For every $\varepsilon \in \mathbb{R}$, $\varepsilon/2^k \to 0$ as $k \to \infty$. -/
theorem tendsto_div_two_pow (ε : ℝ) : Tendsto (fun k : ℕ => ε / 2 ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **Local superlinear convergence of Broyden's method, quantitative form**
([dennis1974characterization]; Theorem 8.2.2 of [dennis1996numerical]; Property 7.2 of
[quarteroni2000numerical]). Assume `Broyden.LipschitzJacobianRoot`, and let $J(z)$ be invertible
with $\|J(z)^{-1}\| \le \beta$. Let $\varepsilon \ge 0$ and $\delta$ satisfy
$12 \beta \delta \le 1$, $3 L \varepsilon \le 2\delta$ and $\bar B(z, \varepsilon) \subseteq D$.
Let $\|x_0 - z\| \le \varepsilon$, and let the matrix $M_0$ of $Q_0$ satisfy
$\|M_0 - J(z)\|_F \le \delta$. Then Broyden's iteration from $(x_0, Q_0)$ has the following
properties:
* every $Q_k$ is invertible, so the iteration is well defined;
* $\|x_k - z\| \le \varepsilon/2^k$ for every $k$, and $x_k \to z$;
* there is a sequence $c_k \to 0$ with $\|x_{k+1} - z\| \le c_k \|x_k - z\|$ for every $k$.

The proof takes $c_k = 4\beta(\eta_k + L\varepsilon/2^k)$, where $\eta_k \to 0$ is the
Dennis–Moré quotient (`Broyden.tendsto_dennisMoreQuotient`). -/
theorem superlinear_of_le (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) {ε δ : ℝ} (hε : 0 ≤ ε) (hβδ : 12 * β * δ ≤ 1)
    (hLε : 3 * L * ε ≤ 2 * δ) (hball : closedBall z ε ⊆ D) {x₀ : E} {Q₀ : E →L[ℝ] E}
    (hx₀ : ‖x₀ - z‖ ≤ ε) (hQ₀ : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ) :
    (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q) ∧
      (∀ k, ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k) ∧
      Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) ∧
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ k, ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ c k * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hinv := norm_iterate_sub_le_and_frobenius_norm_le h e he hβ hε hβδ hLε hball hx₀ hQ₀
  have hL0 := h.nonneg
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hβ
  -- every `Q_k` is invertible
  have hunit : ∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q := fun k => by
    have hxD : (iterate F x₀ Q₀ k).x ∈ D := hball (by
      rw [mem_closedBall, dist_eq_norm]
      exact (hinv k).1.trans (div_le_self hε (one_le_pow₀ (by norm_num))))
    have hQJ : ‖(iterate F x₀ Q₀ k).Q - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ 2 * δ := by
      have h1 : 3 * L / 2 * ε * (1 - 1 / 2 ^ k) ≤ 3 * L / 2 * ε := by
        have : 0 ≤ 3 * L / 2 * ε := by positivity
        have : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
        nlinarith
      rw [iterate_Q_sub_eq]
      exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (by linarith [(hinv k).2])
    obtain ⟨⟨e', he', -⟩, -⟩ := norm_step_x_sub_le h e he hβ hxD (Q := (iterate F x₀ Q₀ k).Q)
      (by nlinarith)
    exact ⟨e', he'⟩
  -- convergence
  have hlim : Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hinv k).1) (tendsto_div_two_pow ε)
  refine ⟨hunit, fun k => (hinv k).1, hlim,
    ⟨fun k => 4 * β * (dennisMoreQuotient F J z x₀ Q₀ k + L * (ε / 2 ^ k)), ?_, fun k => ?_⟩⟩
  · have h1 := tendsto_dennisMoreQuotient h e he hβ hε hβδ hLε hball hx₀ hQ₀
    have h2 := ((h1.add ((tendsto_div_two_pow ε).const_mul L)).const_mul (4 * β))
    simpa using h2
  · refine (norm_iterate_succ_sub_le_mul h e he hβ hε hβδ hLε hball hx₀ hQ₀ k).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (norm_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hinv k).1 hL0)

/-- **Local superlinear convergence of Broyden's method**, existential form
([dennis1974characterization]; Theorem 8.2.2 of [dennis1996numerical]; Property 7.2 of
[quarteroni2000numerical]). Assume `Broyden.LipschitzJacobianRoot`, let $J(z)$ be invertible
with $\|J(z)^{-1}\| \le \beta$ and $\beta > 0$, and let $R > 0$ with $B(z, R) \subseteq D$. Then
there are $\varepsilon > 0$ and $\gamma > 0$ such that for every $x_0$ with
$\|x_0 - z\| \le \varepsilon$ and every operator $Q_0$ with $\|Q_0 - J(z)\| \le \gamma$ in the
operator norm, Broyden's iteration from $(x_0, Q_0)$ has the following properties:
* every $Q_k$ is invertible, so the iteration is well defined;
* $\|x_k - z\| \le \varepsilon/2^k$ for every $k$, and $x_k \to z$;
* there is a sequence $c_k \to 0$ with $\|x_{k+1} - z\| \le c_k \|x_k - z\|$ for every $k$.

The proof takes $\delta = 1/(12\beta)$, $\varepsilon = \min\{R/2, 2\delta/(3(L + 1))\}$ and
$\gamma = \delta/(\sqrt{n} + 1)$. The choice of $\gamma$ converts the hypothesis in the operator
norm to the hypothesis in the Frobenius norm of `Broyden.superlinear_of_le`. -/
theorem exists_superlinear (h : LipschitzJacobianRoot F J D z L) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = toEuclideanCLM (𝕜 := ℝ) (J z)) {β : ℝ}
    (hβ : ‖(e.symm : E →L[ℝ] E)‖ ≤ β) (hβ0 : 0 < β) {R : ℝ} (hR : 0 < R)
    (hRD : ball z R ⊆ D) :
    ∃ ε > 0, ∃ γ > 0, ∀ (x₀ : E) (Q₀ : E →L[ℝ] E), ‖x₀ - z‖ ≤ ε →
      ‖Q₀ - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ γ →
      (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = (iterate F x₀ Q₀ k).Q) ∧
        (∀ k, ‖(iterate F x₀ Q₀ k).x - z‖ ≤ ε / 2 ^ k) ∧
        Tendsto (fun k => (iterate F x₀ Q₀ k).x) atTop (𝓝 z) ∧
        ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
          ∀ k, ‖(iterate F x₀ Q₀ (k + 1)).x - z‖ ≤ c k * ‖(iterate F x₀ Q₀ k).x - z‖ := by
  have hL0 := h.nonneg
  set δ : ℝ := 1 / (12 * β) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := min (R / 2) (2 * δ / (3 * (L + 1))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  set c : ℝ := √(Fintype.card n : ℝ) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set γ : ℝ := δ / (c + 1) with hγ
  have hγ0 : 0 < γ := by positivity
  refine ⟨ε, hε0, γ, hγ0, fun x₀ Q₀ hx₀ hQ₀ => ?_⟩
  have hβδ : 12 * β * δ ≤ 1 := by
    rw [hδ, mul_one_div, div_self (by positivity)]
  have hLε : 3 * L * ε ≤ 2 * δ := by
    have h1 : ε ≤ 2 * δ / (3 * (L + 1)) := min_le_right _ _
    have h2 : 3 * L * ε ≤ 3 * L * (2 * δ / (3 * (L + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hball : closedBall z ε ⊆ D := by
    refine (closedBall_subset_ball ?_).trans hRD
    have := min_le_left (R / 2) (2 * δ / (3 * (L + 1)))
    linarith
  have hQ₀' : ‖(toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z‖ ≤ δ := by
    have h1 := frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM
      ((toEuclideanCLM (𝕜 := ℝ)).symm Q₀ - J z)
    rw [map_sub, StarAlgEquiv.apply_symm_apply] at h1
    refine h1.trans ?_
    calc c * ‖Q₀ - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ c * γ :=
          mul_le_mul_of_nonneg_left hQ₀ hc0
      _ = δ * (c / (c + 1)) := by rw [hγ]; ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hδ0.le
      _ = δ := mul_one δ
  exact superlinear_of_le h e he hβ hε0.le hβδ hLε hball hx₀ hQ₀'

end Main

end Broyden
