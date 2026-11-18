import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Primal-dual logarithmic barrier equations

For componentwise inequalities $c(x)\leq 0$, a feasible slack satisfies $c(x)+z=0$
and $z\geq0$. The logarithmic barrier instead requires $z>0$.
Its slack stationarity condition is $y_i=\mu/z_i$, equivalent for $\mu>0$ to
$y_i z_i=\mu$ with $y,z\geq0$.
For a Newton step the diagonal multiplier block eliminates the slack increment.

## Main definitions

* `Optimization.logBarrierLagrangian`: the Lagrangian with the logarithmic slack penalty.

## Main results

* `Optimization.exists_nonneg_slack_iff`: nonpositive inequalities are equivalent to
  slack feasibility.
* `Optimization.hasDerivAt_logBarrierLagrangian_slack`: the derivative in a slack coordinate.
* `Optimization.barrier_slackStationary_iff`: reciprocal stationarity and complementarity agree.
* `Optimization.barrierNewton_eq_iff_reduced`: slack elimination and recovery in the
  Newton equations.
-/

namespace Optimization

open Matrix

variable {n m : Type*}

/-- A real constraint vector $c$ is componentwise nonpositive if and only if it admits
a nonnegative slack $z$ with $c+z=0$. -/
theorem exists_nonneg_slack_iff (c : m → ℝ) :
    (∃ z : m → ℝ, 0 ≤ z ∧ c + z = 0) ↔ c ≤ 0 := by
  constructor
  · rintro ⟨z, hz, heq⟩ i
    have hi : c i + z i = 0 := congrFun heq i
    exact le_of_add_le_add_right (show c i + z i ≤ 0 + z i by rw [hi, zero_add]; exact hz i)
  · intro hc
    exact ⟨-c, fun i ↦ neg_nonneg.mpr (hc i), add_neg_cancel c⟩

variable [Fintype m]

/-- For an objective value $f$, constraint vector $c$, multiplier $y$, slack $z$ and parameter
$\mu$, the **logarithmic barrier Lagrangian** is $f+y^T(c+z)-\mu\sum_i\log z_i$.
Its barrier domain consists of $z_i>0$; the real-valued expression itself is total. -/
noncomputable def logBarrierLagrangian (f μ : ℝ) (c y z : m → ℝ) : ℝ :=
  f + y ⬝ᵥ (c + z) - μ * ∑ i, Real.log (z i)

/-- The logarithmic barrier Lagrangian evaluates to the objective plus the multiplier pairing
minus the sum of logarithmic penalties. -/
theorem logBarrierLagrangian_apply (f μ : ℝ) (c y z : m → ℝ) :
    logBarrierLagrangian f μ c y z = f + y ⬝ᵥ (c + z) - μ * ∑ i, Real.log (z i) :=
  rfl

/-- At a positive slack coordinate $z_i$, the derivative of the logarithmic barrier
Lagrangian with respect to that coordinate, holding all other coordinates fixed,
is $y_i-\mu/z_i$. -/
theorem hasDerivAt_logBarrierLagrangian_slack [DecidableEq m]
    (f μ : ℝ) (c y z : m → ℝ) (i : m) (hz : 0 < z i) :
    HasDerivAt (fun t ↦ logBarrierLagrangian f μ c y (Function.update z i t))
      (y i - μ / z i) (z i) := by
  have hlinear : ∀ j : m, HasDerivAt (fun t ↦ y j * (c j + Function.update z i t j))
      (if j = i then y i else 0) (z i) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using (((hasDerivAt_id (z i)).const_add (c i)).const_mul (y i))
    · simpa [Function.update_of_ne hj, hj] using hasDerivAt_const (z i) (y j * (c j + z j))
  have hlog : ∀ j : m, HasDerivAt (fun t ↦ Real.log (Function.update z i t j))
      (if j = i then (z i)⁻¹ else 0) (z i) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using Real.hasDerivAt_log hz.ne'
    · simpa [Function.update_of_ne hj, hj] using hasDerivAt_const (z i) (Real.log (z j))
  have hd := ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hlinear j)).const_add f).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hlog j)).const_mul μ)
  change HasDerivAt
    ((fun t ↦ f + ∑ j, y j * (c j + Function.update z i t j)) -
      (fun t ↦ μ * ∑ j, Real.log (Function.update z i t j))) (y i - μ / z i) (z i)
  simpa [div_eq_mul_inv] using hd

/-- Along a real primal path, suppose the objective and each constraint have derivatives
$f'$ and $c'_i$ at $t_0$. With fixed multiplier $y$ and slack $z$, the derivative of the
logarithmic barrier Lagrangian is $f'+y^Tc'$. -/
theorem hasDerivAt_logBarrierLagrangian_primal (f : ℝ → ℝ) (c : ℝ → m → ℝ)
    (μ : ℝ) (y z : m → ℝ) {t₀ f' : ℝ} {c' : m → ℝ}
    (hf : HasDerivAt f f' t₀) (hc : ∀ i, HasDerivAt (fun t ↦ c t i) (c' i) t₀) :
    HasDerivAt (fun t ↦ logBarrierLagrangian (f t) μ (c t) y z) (f' + y ⬝ᵥ c') t₀ := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ ((hc i).add_const (z i)).const_mul (y i))
  change HasDerivAt (fun t ↦ (f + fun t' ↦ ∑ i, y i * (c t' i + z i)) t -
    μ * ∑ i, Real.log (z i)) (f' + y ⬝ᵥ c') t₀
  exact (hf.add hsum).sub_const _

omit [Fintype m] in
/-- The derivative of the scalar complementarity residual $(y+t\,dy)(z+t\,dz)-\mu$
at $t=0$ is $z\,dy+y\,dz$. -/
theorem hasDerivAt_perturbedComplementarity (μ y z dy dz : ℝ) :
    HasDerivAt (fun t ↦ (y + t * dy) * (z + t * dz) - μ) (z * dy + y * dz) 0 := by
  have hy := ((hasDerivAt_id (0 : ℝ)).mul_const dy).const_add y
  have hz := ((hasDerivAt_id (0 : ℝ)).mul_const dz).const_add z
  convert (hy.mul hz).sub_const μ using 1 <;> simp [mul_comm]

omit [Fintype m] in
/-- For $\mu>0$, slack stationarity $y_i=\mu/z_i$ with $z_i>0$ for every $i$
is equivalent to $y,z\geq0$ and $y_i z_i=\mu$ for every $i$. -/
theorem barrier_slackStationary_iff {μ : ℝ} (hμ : 0 < μ) (y z : m → ℝ) :
    ((∀ i, 0 < z i) ∧ ∀ i, y i = μ / z i) ↔
      0 ≤ y ∧ 0 ≤ z ∧ ∀ i, y i * z i = μ := by
  constructor
  · rintro ⟨hz, hy⟩
    exact ⟨fun i ↦ (hy i) ▸ div_nonneg hμ.le (hz i).le, fun i ↦ (hz i).le,
      fun i ↦ (eq_div_iff (hz i).ne').mp (hy i)⟩
  · rintro ⟨hy, hz, hprod⟩
    have hz' (i : m) : 0 < z i := by
      refine lt_of_le_of_ne (hz i) ?_
      intro hzero
      have h := hprod i
      rw [← hzero, mul_zero] at h
      exact hμ.ne' h.symm
    exact ⟨hz', fun i ↦ (eq_div_iff (hz' i).ne').mpr (hprod i)⟩

variable [Fintype n] [DecidableEq m]

/-- For $H\in\mathbb R^{n\times n}$, $B\in\mathbb R^{m\times n}$, slack $z$ and
nonzero multiplier entries $y_i$, let $D=\operatorname{diag}(z_i/y_i)$.
The three Newton equations with right-hand sides $a,b,s$ are equivalent to
the original first equation, the reduced equation $B\,dx-D\,dy=b-(s_i/y_i)_i$,
and the recovery formula $dz=(s_i/y_i)_i-D\,dy$. -/
theorem barrierNewton_eq_iff_reduced (H : Matrix n n ℝ) (B : Matrix m n ℝ)
    (y z : m → ℝ) (hy : ∀ i, y i ≠ 0) (a : n → ℝ) (b s : m → ℝ)
    (dx : n → ℝ) (dy dz : m → ℝ) :
    (H *ᵥ dx + Bᵀ *ᵥ dy = a ∧ B *ᵥ dx + dz = b ∧
      diagonal z *ᵥ dy + diagonal y *ᵥ dz = s) ↔
    (H *ᵥ dx + Bᵀ *ᵥ dy = a ∧
      B *ᵥ dx - diagonal (fun i ↦ z i / y i) *ᵥ dy = b - (fun i ↦ s i / y i) ∧
      dz = (fun i ↦ s i / y i) - diagonal (fun i ↦ z i / y i) *ᵥ dy) := by
  have hrecover :
      diagonal z *ᵥ dy + diagonal y *ᵥ dz = s ↔
        dz = (fun i ↦ s i / y i) - diagonal (fun i ↦ z i / y i) *ᵥ dy := by
    rw [funext_iff, funext_iff]
    simp only [Pi.add_apply, Pi.sub_apply, mulVec_diagonal]
    apply forall_congr'
    intro i
    constructor <;> intro hi
    · field_simp [hy i]
      linear_combination hi
    · field_simp [hy i] at hi
      linear_combination hi
  rw [hrecover]
  constructor
  · rintro ⟨htop, hmid, hthird⟩
    refine ⟨htop, ?_, hthird⟩
    rw [hthird] at hmid
    exact eq_sub_of_add_eq (by simpa only [sub_eq_add_neg, add_left_comm, add_comm, add_assoc]
      using hmid)
  · rintro ⟨htop, hmid, hthird⟩
    refine ⟨htop, ?_, hthird⟩
    rw [hthird]
    calc
      _ = (B *ᵥ dx - diagonal (fun i ↦ z i / y i) *ᵥ dy) + (fun i ↦ s i / y i) := by abel
      _ = b := by rw [hmid, sub_add_cancel]

omit [Fintype m] in
/-- If $y$ and $z$ are nonnegative, the diagonal matrix with entries $z_i/y_i$ is
positive semidefinite, with totalized value zero when $y_i=0$. -/
theorem barrierSchurDiagonal_posSemidef (y z : m → ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (diagonal (fun i ↦ z i / y i)).PosSemidef :=
  posSemidef_diagonal_iff.mpr (fun i ↦ div_nonneg (hz i) (hy i))

omit [Fintype m] [DecidableEq m] in
/-- Let $f$ be convex on the real coordinate space. If every restriction
$t\mapsto f(x+tv)$ is differentiable and its second derivative at zero equals
$v^THv$ for a symmetric matrix $H$, then $H$ is positive semidefinite. -/
theorem posSemidef_of_convex_lineCurvature (f : (n → ℝ) → ℝ) (x : n → ℝ)
    (H : Matrix n n ℝ) (hsymm : H.IsSymm) (hf : ConvexOn ℝ Set.univ f)
    (hd : ∀ v, Differentiable ℝ (fun t : ℝ ↦ f (x + t • v)))
    (hdd : ∀ v, HasDerivAt (deriv (fun t : ℝ ↦ f (x + t • v))) (v ⬝ᵥ (H *ᵥ v)) 0) :
    H.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hsymm) fun v ↦ ?_
  have hline (t : ℝ) : AffineMap.lineMap x (x + v) t = x + t • v := by
    rw [AffineMap.lineMap_apply_module]
    module
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ ↦ f (x + t • v)) := by
    simpa [Function.comp_def, hline] using hf.comp_affineMap (AffineMap.lineMap x (x + v))
  have hmono := hconv.monotoneOn_deriv (fun t _ ↦ hd v t)
  rw [monotoneOn_univ] at hmono
  simpa [(hdd v).deriv] using hmono.deriv_nonneg (x := 0)

omit [Fintype n] [DecidableEq m] in
/-- If the objective curvature $H$ and all constraint curvature matrices $H_i$ are positive
semidefinite, then $H+\sum_i y_i H_i$ is positive semidefinite for nonnegative $y$. -/
theorem lagrangianHessian_posSemidef (H : Matrix n n ℝ) (Hc : m → Matrix n n ℝ)
    (y : m → ℝ) (hy : 0 ≤ y) (hH : H.PosSemidef) (hHc : ∀ i, (Hc i).PosSemidef) :
    (H + ∑ i, y i • Hc i).PosSemidef :=
  hH.add <| posSemidef_sum _ fun i _ ↦ (hHc i).smul (hy i)

omit [Fintype n] [DecidableEq m] in
/-- If the objective curvature $H$ is positive definite and all constraint curvature
matrices $H_i$ are positive semidefinite, then $H+\sum_i y_i H_i$ is positive definite
for nonnegative $y$. -/
theorem lagrangianHessian_posDef (H : Matrix n n ℝ) (Hc : m → Matrix n n ℝ)
    (y : m → ℝ) (hy : 0 ≤ y) (hH : H.PosDef) (hHc : ∀ i, (Hc i).PosSemidef) :
    (H + ∑ i, y i • Hc i).PosDef :=
  hH.add_posSemidef <| posSemidef_sum _ fun i _ ↦ (hHc i).smul (hy i)

end Optimization
