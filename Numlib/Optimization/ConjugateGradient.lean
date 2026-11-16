/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG

/-!
# Nonlinear conjugate gradient methods

This file defines the nonlinear conjugate gradient methods of unconstrained optimization, as in
Remark 7.2 of [quarteroni2000numerical] and §5.2 of [nocedal2006numerical]. Let $E$ be a real inner
product space and let $g : E \to E$ be the gradient of the objective $f$. From a starting point
$x_0$ the method sets $d_0 = -g(x_0)$ and
$$x_{k+1} = x_k + \alpha_k d_k, \qquad d_{k+1} = -g(x_{k+1}) + \beta_{k+1} d_k.$$
The step length $\alpha_k$ comes from a line search. The coefficient $\beta_{k+1}$ is a formula in
the two consecutive gradients $g_k = g(x_k)$ and $g_{k+1}$: the Fletcher–Reeves coefficient
$\|g_{k+1}\|^2 / \|g_k\|^2$ or the Polak–Ribière coefficient $\langle g_{k+1}, g_{k+1} - g_k \rangle
/ \|g_k\|^2$.

The main result is that on the quadratic $f(x) = \frac12 \langle Ax, x \rangle - \langle b, x
\rangle$ with $A$ symmetric and coercive, with exact line searches, both choices of $\beta$ give
exactly the iterates of the linear conjugate gradient method of `Numlib.Krylov.CG`. The points
agree, the gradients are the negated residuals, and the search directions agree. Therefore all
results proved for linear conjugate gradients (finite termination, the expanding subspace property,
the rate in $\sqrt{\kappa}$) apply to these methods on a quadratic.

## Main definitions

* `NonlinearCG.State`: the current point, its gradient and the current search direction.
* `NonlinearCG.betaFletcherReeves`, `NonlinearCG.betaPolakRibiere`: the two choices of the
  coefficient $\beta$.
* `NonlinearCG.init`, `NonlinearCG.step`, `NonlinearCG.iterate`: the iteration, with the step length
  given by a rule $\alpha$ that maps a state to a real number.
* `NonlinearCG.exactStep`: the exact line search $\alpha = -\langle g, d \rangle / \langle Ad, d
  \rangle$ along the current direction for a quadratic with Hessian $A$, as in (7.36) of
  [quarteroni2000numerical].

## Main results

* `NonlinearCG.iterate_eq_CG_iterate_of_quadratic`: on a quadratic with symmetric coercive Hessian,
  with exact line searches, any coefficient rule that agrees with the linear conjugate gradient
  coefficient on the residuals gives the linear conjugate gradient iterates.
* `NonlinearCG.iterate_fletcherReeves_eq_CG_iterate`: the Fletcher–Reeves method with exact line
  searches on such a quadratic is the linear conjugate gradient method.
* `NonlinearCG.iterate_polakRibiere_eq_CG_iterate`: the Polak–Ribière method with exact line
  searches on such a quadratic is the linear conjugate gradient method.

## Proof outline

The agreement theorem is proved by induction on $k$. The exact step equals the linear conjugate
gradient step length because $\langle p_k, r_k \rangle = \|r_k\|^2$. The Fletcher–Reeves coefficient
is the linear coefficient by definition, and the Polak–Ribière coefficient equals it because
consecutive residuals are orthogonal. No invariant of linear conjugate gradients is proved again.

## Implementation notes

* The linear theory is not repeated here. Exact steps along a direction, steepest descent and the
  Kantorovich inequality are in `Numlib.Projection.OneDimensional`, and conjugate directions are in
  `Numlib.Projection.ConjugateDirection`.
* The method is stated on a real inner product space, with the gradient given as data $g : E \to E$,
  as in `Numlib.Analysis.Convex.Gateaux`. The gradient of the quadratic is $Ax - b$ by
  `hasGradientAt_energyFunctional`.
* The step length is a rule `α : NonlinearCG.State E → ℝ`, so that exact line searches, Armijo–Wolfe
  searches and the quadratic case are all instances.
* The divisions in $\beta$ and in the exact step use the Lean convention $x / 0 = 0$. The
  coefficients of `CG.iterate` use the same convention, so the agreement with linear conjugate
  gradients holds at every step, also after the residual becomes zero.
-/

variable {E : Type*} [NormedAddCommGroup E]

namespace NonlinearCG

/-- A **state** of a nonlinear conjugate gradient iteration consists of the current point $x$, the
gradient $g$ at that point, and the current search direction $d$. -/
@[ext]
structure State (E : Type*) where
  /-- The current point $x_k$. -/
  x : E
  /-- The gradient $g_k = \nabla f(x_k)$ at the current point. -/
  g : E
  /-- The current search direction $d_k$. -/
  d : E

/-- The **initial state** at $x_0$ for the gradient $g$ is the point $x_0$, the gradient $g(x_0)$,
and the steepest descent direction $d_0 = -g(x_0)$.

This corresponds to the choice $\beta_1 = 0$ in the indexing of [quarteroni2000numerical]. -/
def init (g : E → E) (x₀ : E) : State E := { x := x₀, g := g x₀, d := -g x₀ }

section Init

variable (g : E → E) (x₀ : E)

/-- The point of the initial state is $x_0$. -/
@[simp] theorem init_x : (init g x₀).x = x₀ := rfl

/-- The gradient of the initial state is $g(x_0)$. -/
@[simp] theorem init_g : (init g x₀).g = g x₀ := rfl

/-- The direction of the initial state is $-g(x_0)$. -/
@[simp] theorem init_d : (init g x₀).d = -g x₀ := rfl

end Init

variable [InnerProductSpace ℝ E]

/-- The **Fletcher–Reeves coefficient** of two consecutive gradients $g_{\mathrm{old}}$ and
$g_{\mathrm{new}}$ is
$$\beta = \frac{\|g_{\mathrm{new}}\|^2}{\|g_{\mathrm{old}}\|^2}.$$
This is Remark 7.2 of [quarteroni2000numerical].

The value is $0$ when $g_{\mathrm{old}} = 0$. -/
noncomputable def betaFletcherReeves (gOld gNew : E) : ℝ := ‖gNew‖ ^ 2 / ‖gOld‖ ^ 2

/-- The **Polak–Ribière coefficient** of two consecutive gradients $g_{\mathrm{old}}$ and
$g_{\mathrm{new}}$ is
$$\beta = \frac{\langle g_{\mathrm{new}}, g_{\mathrm{new}} - g_{\mathrm{old}}
  \rangle}{\|g_{\mathrm{old}}\|^2}.$$
This is Remark 7.2 of [quarteroni2000numerical].

The value is $0$ when $g_{\mathrm{old}} = 0$. -/
noncomputable def betaPolakRibiere (gOld gNew : E) : ℝ := inner ℝ gNew (gNew - gOld) / ‖gOld‖ ^ 2

/-- One **step** of nonlinear conjugate gradients, for the gradient $g : E \to E$, the coefficient
rule $\beta(g_{\mathrm{old}}, g_{\mathrm{new}})$ and the step length rule $\alpha$, maps a state
$(x, g_x, d)$ to the state $(x', g', d')$ with
$$x' = x + \alpha(s)\, d, \qquad g' = g(x'), \qquad d' = -g' + \beta(g_x, g')\, d,$$
where $s$ is the old state. -/
noncomputable def step (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (s : State E) : State E :=
  let x' := s.x + α s • s.d
  let g' := g x'
  { x := x', g := g', d := -g' + β s.g g' • s.d }

/-- The $k$-th state of nonlinear conjugate gradients from $x_0$: the step `NonlinearCG.step`
applied $k$ times to the initial state `NonlinearCG.init`. -/
noncomputable def iterate (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (x₀ : E) (k : ℕ) :
    State E :=
  (step g β α)^[k] (init g x₀)

section General

variable (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (x₀ : E)

/-- State $0$ of the iteration is the initial state. -/
@[simp] theorem iterate_zero : iterate g β α x₀ 0 = init g x₀ := rfl

/-- The recurrence: state $k + 1$ of the iteration is one step `NonlinearCG.step` applied to state
$k$. -/
theorem iterate_succ (k : ℕ) : iterate g β α x₀ (k + 1) = step g β α (iterate g β α x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The point of the new state is $x' = x + \alpha(s)\, d$. -/
theorem step_x (s : State E) : (step g β α s).x = s.x + α s • s.d := rfl

/-- The gradient of the new state is $g(x + \alpha(s)\, d)$, the gradient at the new point. -/
theorem step_g (s : State E) : (step g β α s).g = g (s.x + α s • s.d) := rfl

/-- The direction of the new state is $d' = -g' + \beta(g_x, g')\, d$, where $g'$ is the gradient of
the new state and $g_x$ the gradient of the old state. -/
theorem step_d (s : State E) :
    (step g β α s).d = -(step g β α s).g + β s.g (step g β α s).g • s.d := rfl

/-- For every $k$, the gradient stored in state $k$ is the gradient $g(x_k)$ at the point $x_k$ of
state $k$. -/
theorem iterate_g (k : ℕ) : (iterate g β α x₀ k).g = g (iterate g β α x₀ k).x := by
  cases k with
  | zero => rfl
  | succ k => rw [iterate_succ, step_g, step_x]

end General

/-! ### The quadratic case -/

/-- The **exact line search** along the current direction for a quadratic objective with Hessian
$A$: for a state with gradient $g$ and direction $d$,
$$\alpha = -\frac{\langle g, d \rangle}{\langle Ad, d \rangle}.$$
If $A$ is symmetric and $\langle Ad, d \rangle > 0$, this is the minimizer of
$t \mapsto f(x + t d)$, as in (7.36) of [quarteroni2000numerical]. For $f(x) = \frac12 \langle
Ax, x \rangle - \langle b, x \rangle$, with $g = Ax - b = -r$, it is
$\langle d, r \rangle / \langle d, Ad \rangle$.

The value is $0$ when $\langle Ad, d \rangle = 0$. -/
noncomputable def exactStep (A : E →ₗ[ℝ] E) (s : State E) : ℝ :=
  -inner ℝ s.g s.d / inner ℝ (A s.d) s.d

section Quadratic

variable (β : E → E → ℝ) {A : E →ₗ[ℝ] E} (hA : A.IsSymmetricCoercive) (b x₀ : E)
include hA

/-- Let $A$ be a symmetric coercive linear operator on $E$, let $b, x_0 \in E$, and let
$(x_k, r_k, p_k)$ be the states of the linear conjugate gradient method for $Ax = b$ from $x_0$.
Let $\beta$ be a coefficient rule with $\beta(-r_k, -r_{k+1}) = \beta^{\mathrm{CG}}_k$ for every
$k$, where $\beta^{\mathrm{CG}}_k$ is the linear conjugate gradient coefficient `CG.beta`. Then
for every $k$, the state $k$ of nonlinear conjugate gradients for the gradient $g(x) = Ax - b$,
with the coefficient rule $\beta$ and exact line searches, is $(x_k, -r_k, p_k)$.

The linear states are `CG.iterate`, and the exact line search is `NonlinearCG.exactStep`. The
exact step equals `CG.alpha` because $\langle p_k, r_k \rangle = \|r_k\|^2$
(`CG.inner_residual_direction_eq`). The proof is an induction on $k$. -/
theorem iterate_eq_CG_iterate_of_quadratic
    (hβ : ∀ k, β (-(CG.iterate A b x₀ k).r) (-(CG.iterate A b x₀ (k + 1)).r)
      = CG.beta A (CG.iterate A b x₀ k)) (k : ℕ) :
    iterate (fun x => A x - b) β (exactStep A) x₀ k
      = ⟨(CG.iterate A b x₀ k).x, -(CG.iterate A b x₀ k).r, (CG.iterate A b x₀ k).p⟩ := by
  induction k with
  | zero =>
    ext <;> simp [init, CG.init]
  | succ k ih =>
    have hα : exactStep A (iterate (fun x => A x - b) β (exactStep A) x₀ k)
        = CG.alpha A (CG.iterate A b x₀ k) := by
      rw [ih, exactStep, CG.alpha]
      simp only [inner_neg_left, neg_neg]
      rw [CG.inner_residual_direction_eq b x₀ hA le_rfl, real_inner_self_eq_norm_sq]
      rfl
    rw [iterate_succ]
    ext
    · rw [step_x, hα, ih, CG.iterate_succ_x]
    · rw [step_g, hα, ih]
      dsimp only
      rw [← CG.iterate_succ_x, ← neg_sub, ← CG.residual_eq A b x₀ (k + 1)]
    · rw [step_d, step_g, hα, ih]
      dsimp only
      rw [← CG.iterate_succ_x, ← neg_sub, ← CG.residual_eq A b x₀ (k + 1), hβ, neg_neg,
        CG.iterate_succ_p]

omit hA in
/-- Let $A$ be a linear operator on $E$, let $b, x_0 \in E$, and let $r_k$ be the residuals of the
linear conjugate gradient method for $Ax = b$ from $x_0$. Then for every $k$, the
Fletcher–Reeves coefficient of $-r_k$ and $-r_{k+1}$ is the linear conjugate gradient
coefficient:
$$\beta^{\mathrm{FR}}(-r_k, -r_{k+1}) = \frac{\|r_{k+1}\|^2}{\|r_k\|^2} =
  \beta^{\mathrm{CG}}_k.$$

The linear coefficient is `CG.beta`. No hypothesis on $A$ is needed. -/
theorem betaFletcherReeves_neg_residual (k : ℕ) :
    betaFletcherReeves (-(CG.iterate A b x₀ k).r) (-(CG.iterate A b x₀ (k + 1)).r)
      = CG.beta A (CG.iterate A b x₀ k) := by
  rw [betaFletcherReeves, CG.beta_iterate, norm_neg, norm_neg, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

omit hA in
/-- Let $g_{\mathrm{old}}, g_{\mathrm{new}} \in E$ with $\langle g_{\mathrm{new}}, g_{\mathrm{old}}
\rangle = 0$. Then the Polak–Ribière coefficient of $g_{\mathrm{old}}$ and $g_{\mathrm{new}}$
equals their Fletcher–Reeves coefficient. -/
theorem betaPolakRibiere_eq_betaFletcherReeves {gOld gNew : E} (h : inner ℝ gNew gOld = 0) :
    betaPolakRibiere gOld gNew = betaFletcherReeves gOld gNew := by
  rw [betaPolakRibiere, betaFletcherReeves, inner_sub_right, h, sub_zero,
    real_inner_self_eq_norm_sq]

/-- Let $A$ be a symmetric coercive linear operator on $E$, let $b, x_0 \in E$, and let $r_k$ be the
residuals of the linear conjugate gradient method for $Ax = b$ from $x_0$. Then for every $k$,
the Polak–Ribière coefficient of $-r_k$ and $-r_{k+1}$ is the linear conjugate gradient
coefficient `CG.beta`.

The proof uses that consecutive residuals are orthogonal (`CG.inner_residual_eq_zero`), so that
the coefficient reduces to Fletcher–Reeves by
`NonlinearCG.betaPolakRibiere_eq_betaFletcherReeves`. -/
theorem betaPolakRibiere_neg_residual (k : ℕ) :
    betaPolakRibiere (-(CG.iterate A b x₀ k).r) (-(CG.iterate A b x₀ (k + 1)).r)
      = CG.beta A (CG.iterate A b x₀ k) := by
  rw [betaPolakRibiere_eq_betaFletcherReeves, betaFletcherReeves_neg_residual b x₀]
  rw [inner_neg_left, inner_neg_right, neg_neg]
  exact CG.inner_residual_eq_zero b x₀ hA (Nat.succ_ne_self k)

/-- Let $A$ be a symmetric coercive linear operator on $E$ and let $b, x_0 \in E$. Consider the
quadratic $f(x) = \frac12 \langle Ax, x \rangle - \langle b, x \rangle$, whose gradient is
$g(x) = Ax - b$. Then for every $k$, the state $k$ of the Fletcher–Reeves method with exact line
searches is $(x_k, -r_k, p_k)$, where $(x_k, r_k, p_k)$ is the state $k$ of the linear conjugate
gradient method for $Ax = b$ from $x_0$. That is, the points are the linear conjugate gradient
iterates, the gradients are the negated residuals, and the directions are the linear conjugate
gradient directions. This is the content of §7.2.4 and Remark 7.2 of [quarteroni2000numerical].

The gradient of the quadratic is given by `hasGradientAt_energyFunctional`. The linear states
are `CG.iterate`. The proof applies `NonlinearCG.iterate_eq_CG_iterate_of_quadratic` with
`NonlinearCG.betaFletcherReeves_neg_residual`. -/
theorem iterate_fletcherReeves_eq_CG_iterate (k : ℕ) :
    iterate (fun x => A x - b) betaFletcherReeves (exactStep A) x₀ k
      = ⟨(CG.iterate A b x₀ k).x, -(CG.iterate A b x₀ k).r, (CG.iterate A b x₀ k).p⟩ :=
  iterate_eq_CG_iterate_of_quadratic betaFletcherReeves hA b x₀
    (betaFletcherReeves_neg_residual b x₀) k

/-- Let $A$ be a symmetric coercive linear operator on $E$ and let $b, x_0 \in E$. Then for every
$k$, the state $k$ of the Polak–Ribière method with exact line searches for the gradient
$g(x) = Ax - b$ is $(x_k, -r_k, p_k)$, where $(x_k, r_k, p_k)$ is the state $k$ of the linear
conjugate gradient method for $Ax = b$ from $x_0$. This is the content of §7.2.4 and Remark 7.2
of [quarteroni2000numerical].

The linear states are `CG.iterate`. The proof applies
`NonlinearCG.iterate_eq_CG_iterate_of_quadratic` with
`NonlinearCG.betaPolakRibiere_neg_residual`. -/
theorem iterate_polakRibiere_eq_CG_iterate (k : ℕ) :
    iterate (fun x => A x - b) betaPolakRibiere (exactStep A) x₀ k
      = ⟨(CG.iterate A b x₀ k).x, -(CG.iterate A b x₀ k).r, (CG.iterate A b x₀ k).p⟩ :=
  iterate_eq_CG_iterate_of_quadratic betaPolakRibiere hA b x₀
    (betaPolakRibiere_neg_residual hA b x₀) k

end Quadratic

end NonlinearCG
