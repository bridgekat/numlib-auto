import Numlib.Krylov.CG

/-!
# Nonlinear conjugate gradient methods

The nonlinear conjugate gradient methods of unconstrained optimization
([quarteroni2000numerical] Remark 7.2; Nocedal–Wright, *Numerical Optimization*, §5.2): from the
gradient `g : E → E` of the objective, the iteration `x_{k+1} = x_k + α_k d_k`,
`d_{k+1} = -g(x_{k+1}) + β_{k+1} d_k`, `d_0 = -g(x_0)`, where the step length `α_k` comes from a
line search and `β` is a formula in the two consecutive gradients — Fletcher–Reeves
`‖g_{k+1}‖² / ‖g_k‖²` or Polak–Ribière `⟪g_{k+1}, g_{k+1} - g_k⟫ / ‖g_k‖²`.

## Main definitions

* `NonlinearCG.State`: the current point, its gradient and the current search direction;
* `NonlinearCG.betaFletcherReeves`, `NonlinearCG.betaPolakRibiere`: the two choices of `β`;
* `NonlinearCG.step g β α`, `NonlinearCG.init g x₀`, `NonlinearCG.iterate g β α x₀`: the
  iteration, with the step length an oracle `α : State E → ℝ` so that exact line searches,
  Armijo–Wolfe searches and the quadratic case are all instances;
* `NonlinearCG.exactStep A`: the exact line search along the current direction for a quadratic
  with Hessian `A`, `α = -⟪g, d⟫ / ⟪A d, d⟫` ([quarteroni2000numerical] (7.36)).

## Main statements

* `NonlinearCG.iterate_eq_CG_iterate_of_quadratic`, with its two instances
  `NonlinearCG.iterate_fletcherReeves_eq_CG_iterate` and
  `NonlinearCG.iterate_polakRibiere_eq_CG_iterate`: on the quadratic `½ ⟪A x, x⟫ - ⟪b, x⟫` with
  symmetric coercive `A` — whose gradient is `A x - b`, `hasGradientAt_energyFunctional` in
  `Numlib/Analysis/InnerProductSpace/Energy` — and with exact line searches, both choices of `β`
  reproduce the linear conjugate gradient iterates of `Numlib/Krylov/CG` exactly: the points, the
  negated residuals as gradients, and the directions. Everything proved there (finite termination,
  the expanding subspace property, the `√κ` rate) therefore applies.

## Design

The linear theory is not repeated: exact steps along a direction, steepest descent and
Kantorovich's inequality are `Numlib/Projection/OneDimensional`, conjugate directions are
`Numlib/Projection/ConjugateDirection`, and the agreement theorem reduces the nonlinear recurrence
to `CG.iterate` by induction rather than re-proving any CG invariant. The method is stated on a
real inner product space with the gradient as data, following `Numlib/Analysis/Convex/Gateaux`;
the divisions in `β` and in the exact step follow Lean's convention `x / 0 = 0`, under which the
agreement with CG (whose coefficients use the same convention) holds at every step, including past
the point where the residual vanishes.
-/

variable {E : Type*} [NormedAddCommGroup E]

namespace NonlinearCG

/-- State of a nonlinear conjugate gradient iteration: the current point `x`, its gradient `g`
and the current search direction `d`. -/
@[ext]
structure State (E : Type*) where
  /-- The current point `x_k`. -/
  x : E
  /-- The gradient `g_k = ∇f(x_k)` at the current point. -/
  g : E
  /-- The current search direction `d_k`. -/
  d : E

/-- The initial state at `x₀`: the direction is the steepest descent direction `-g x₀`
(the book's `β₁ = 0`). -/
def init (g : E → E) (x₀ : E) : State E := { x := x₀, g := g x₀, d := -g x₀ }

section Init

variable (g : E → E) (x₀ : E)

@[simp] theorem init_x : (init g x₀).x = x₀ := rfl

@[simp] theorem init_g : (init g x₀).g = g x₀ := rfl

@[simp] theorem init_d : (init g x₀).d = -g x₀ := rfl

end Init

variable [InnerProductSpace ℝ E]

/-- The Fletcher–Reeves coefficient `β = ‖g_{new}‖² / ‖g_{old}‖²`
([quarteroni2000numerical] Remark 7.2). -/
noncomputable def betaFletcherReeves (gOld gNew : E) : ℝ := ‖gNew‖ ^ 2 / ‖gOld‖ ^ 2

/-- The Polak–Ribière coefficient `β = ⟪g_{new}, g_{new} - g_{old}⟫ / ‖g_{old}‖²`
([quarteroni2000numerical] Remark 7.2). -/
noncomputable def betaPolakRibiere (gOld gNew : E) : ℝ := inner ℝ gNew (gNew - gOld) / ‖gOld‖ ^ 2

/-- One step of nonlinear conjugate gradients with gradient `g`, direction coefficient `β` and
step-length rule `α`: `x' = x + α s • d`, `g' = g x'`, `d' = -g' + β g g' • d`. -/
noncomputable def step (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (s : State E) : State E :=
  let x' := s.x + α s • s.d
  let g' := g x'
  { x := x', g := g', d := -g' + β s.g g' • s.d }

/-- The `k`-th state of nonlinear conjugate gradients from `x₀`. -/
noncomputable def iterate (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (x₀ : E) (k : ℕ) :
    State E :=
  (step g β α)^[k] (init g x₀)

section General

variable (g : E → E) (β : E → E → ℝ) (α : State E → ℝ) (x₀ : E)

@[simp] theorem iterate_zero : iterate g β α x₀ 0 = init g x₀ := rfl

/-- The recurrence: state `k + 1` is one `step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) : iterate g β α x₀ (k + 1) = step g β α (iterate g β α x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The point update `x' = x + α s • d`. -/
theorem step_x (s : State E) : (step g β α s).x = s.x + α s • s.d := rfl

/-- The gradient is evaluated at the new point. -/
theorem step_g (s : State E) : (step g β α s).g = g (s.x + α s • s.d) := rfl

/-- The direction update `d' = -g' + β g g' • d`. -/
theorem step_d (s : State E) :
    (step g β α s).d = -(step g β α s).g + β s.g (step g β α s).g • s.d := rfl

/-- The gradient field of every state is the gradient at its point. -/
theorem iterate_g (k : ℕ) : (iterate g β α x₀ k).g = g (iterate g β α x₀ k).x := by
  cases k with
  | zero => rfl
  | succ k => rw [iterate_succ, step_g, step_x]

end General

/-! ### The quadratic case -/

/-- The exact line search along the current direction for a quadratic objective with Hessian `A`:
`α = -⟪g, d⟫ / ⟪A d, d⟫`, the minimizer of `α ↦ f(x + α d)` ([quarteroni2000numerical] (7.36));
for `f = ½ ⟪A x, x⟫ - ⟪b, x⟫` with `g = A x - b = -r` this is `⟪d, r⟫ / ⟪d, A d⟫`. -/
noncomputable def exactStep (A : E →ₗ[ℝ] E) (s : State E) : ℝ :=
  -inner ℝ s.g s.d / inner ℝ (A s.d) s.d

section Quadratic

variable (β : E → E → ℝ) {A : E →ₗ[ℝ] E} (hA : A.IsSymmetricCoercive) (b x₀ : E)
include hA

/-- The engine of the agreement with linear conjugate gradients: on the quadratic with gradient
`g x = A x - b`, with exact line searches and any coefficient rule `β` that agrees with the CG
coefficient on the CG residuals, the nonlinear CG state at step `k` is the CG state at step `k`
with the residual negated. The exact step is `CG.alpha` because `⟪p_k, r_k⟫ = ‖r_k‖²`
(`CG.inner_residual_direction_eq`). -/
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
/-- Fletcher–Reeves is exactly the CG coefficient `β = ‖r_{k+1}‖² / ‖r_k‖²`. -/
theorem betaFletcherReeves_neg_residual (k : ℕ) :
    betaFletcherReeves (-(CG.iterate A b x₀ k).r) (-(CG.iterate A b x₀ (k + 1)).r)
      = CG.beta A (CG.iterate A b x₀ k) := by
  rw [betaFletcherReeves, CG.beta_iterate, norm_neg, norm_neg, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

omit hA in
/-- On mutually orthogonal consecutive gradients Polak–Ribière reduces to Fletcher–Reeves. -/
theorem betaPolakRibiere_eq_betaFletcherReeves {gOld gNew : E} (h : inner ℝ gNew gOld = 0) :
    betaPolakRibiere gOld gNew = betaFletcherReeves gOld gNew := by
  rw [betaPolakRibiere, betaFletcherReeves, inner_sub_right, h, sub_zero,
    real_inner_self_eq_norm_sq]

/-- Polak–Ribière is the CG coefficient on the CG residuals, because consecutive residuals are
orthogonal (`CG.inner_residual_eq_zero`). -/
theorem betaPolakRibiere_neg_residual (k : ℕ) :
    betaPolakRibiere (-(CG.iterate A b x₀ k).r) (-(CG.iterate A b x₀ (k + 1)).r)
      = CG.beta A (CG.iterate A b x₀ k) := by
  rw [betaPolakRibiere_eq_betaFletcherReeves, betaFletcherReeves_neg_residual b x₀]
  rw [inner_neg_left, inner_neg_right, neg_neg]
  exact CG.inner_residual_eq_zero b x₀ hA (Nat.succ_ne_self k)

/-- [quarteroni2000numerical] §7.2.4 and Remark 7.2: on the quadratic `½ ⟪A x, x⟫ - ⟪b, x⟫` with
symmetric coercive `A`, whose gradient is `A x - b` (`hasGradientAt_energyFunctional`), the
Fletcher–Reeves method with exact line searches is the linear conjugate gradient method: the
points are the CG iterates, the gradients the negated CG residuals, the directions the CG
directions. -/
theorem iterate_fletcherReeves_eq_CG_iterate (k : ℕ) :
    iterate (fun x => A x - b) betaFletcherReeves (exactStep A) x₀ k
      = ⟨(CG.iterate A b x₀ k).x, -(CG.iterate A b x₀ k).r, (CG.iterate A b x₀ k).p⟩ :=
  iterate_eq_CG_iterate_of_quadratic betaFletcherReeves hA b x₀
    (betaFletcherReeves_neg_residual b x₀) k

/-- [quarteroni2000numerical] §7.2.4 and Remark 7.2: the Polak–Ribière method with exact line
searches is the linear conjugate gradient method on a quadratic, as
`iterate_fletcherReeves_eq_CG_iterate`. -/
theorem iterate_polakRibiere_eq_CG_iterate (k : ℕ) :
    iterate (fun x => A x - b) betaPolakRibiere (exactStep A) x₀ k
      = ⟨(CG.iterate A b x₀ k).x, -(CG.iterate A b x₀ k).r, (CG.iterate A b x₀ k).p⟩ :=
  iterate_eq_CG_iterate_of_quadratic betaPolakRibiere hA b x₀
    (betaPolakRibiere_neg_residual hA b x₀) k

end Quadratic

end NonlinearCG
