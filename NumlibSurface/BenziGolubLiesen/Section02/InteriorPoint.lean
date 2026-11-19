import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Data.Matrix.Block
import Numlib.Optimization.PrimalDualBarrierNewton
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 2.3: Saddle point systems from interior point methods

The logarithmic barrier in [benzi2005numerical] replaces the inequalities $c(x)\leq 0$
by equalities $c(x)+z=0$ with $z>0$. Its slack derivatives give the perturbed
complementarity equations $y_i z_i=\mu$. Eliminating the slack increment gives a
saddle-point Newton system with a diagonal dual block. The proofs specialize
`Numlib.Optimization.PrimalDualBarrierNewton`.

## Main definitions

* Equation (2.27), `BenziGolubLiesen.barrierObjective`: the log-penalized objective.
* Equation (2.28), `BenziGolubLiesen.barrierFeasibleSet`: positive feasible slacks.

## Main results

* Equation (2.31), `BenziGolubLiesen.barrierLagrangian_slackStationary_iff`: slack stationarity.
* Equations (2.29)–(2.35), `BenziGolubLiesen.barrierStationarity_iff_complementarity`: equivalence.
* Equations (2.36)–(2.37), `BenziGolubLiesen.barrierNewton_iff_reduced`: elimination and recovery.
* After (2.37), `BenziGolubLiesen.lagrangianHessian_posSemidef_of_convex`: nonnegative curvature.
* After (2.37), `BenziGolubLiesen.barrierReducedDiagonal_posSemidef`: the nonnegative
  diagonal block.

## Deviations from the source

* **Paragraph after (2.37)** (correction). Positive definiteness of the objective Hessian
  at the current point suffices; strict convexity alone does not. See
  `BenziGolubLiesen.strictConvex_hessian_not_posDef_example`.

## Not formalized

* **(2.29)–(2.36).** The Newton reduction takes evaluated derivative matrices as inputs, rather than
  constructing the full Fréchet derivative of a nonlinear residual on a product space.
* **Paragraph before (2.36).** Convergence as $\mu\to0$ needs hypotheses and a
  path-following scheme.
* **Paragraph after (2.37).** The LP/QP comparison needs a specified formulation of the bounds.
-/

namespace BenziGolubLiesen

open Matrix Optimization

variable {X n m : Type*}

/-- **Equations (2.25)–(2.28)** of [benzi2005numerical], introduction of slacks.
For a constraint vector $c(x)$, $c(x)\le 0$ if and only if $c(x)+z=0$ for some $z\ge 0$. -/
theorem inequalities_iff_exists_slack (c : X → m → ℝ) (x : X) :
    c x ≤ 0 ↔ ∃ z : m → ℝ, 0 ≤ z ∧ c x + z = 0 :=
  (exists_nonneg_slack_iff (c x)).symm

/-- **Equation (2.28)** of [benzi2005numerical]. The **barrier feasible set** of $c$
is the set of pairs $(x,z)$ with $c(x)+z=0$ and $z_i>0$ for every $i$. -/
def barrierFeasibleSet (c : X → m → ℝ) : Set (X × (m → ℝ)) :=
  {point | c point.1 + point.2 = 0 ∧ ∀ i, 0 < point.2 i}

/-- Membership in the barrier feasible set is slack equality and strict positivity. -/
@[simp] theorem mem_barrierFeasibleSet (c : X → m → ℝ) (x : X) (z : m → ℝ) :
    (x, z) ∈ barrierFeasibleSet c ↔ c x + z = 0 ∧ ∀ i, 0 < z i :=
  Iff.rfl

variable [Fintype m]

/-- **Equation (2.27)** of [benzi2005numerical]. The **logarithmic barrier objective** at
$(x,z)$ is $f(x)-\mu\sum_i\log z_i$. The expression is total, and the optimization problem
uses it on the domain of `BenziGolubLiesen.barrierFeasibleSet`. -/
noncomputable def barrierObjective (f : X → ℝ) (μ : ℝ) (point : X × (m → ℝ)) : ℝ :=
  f point.1 - μ * ∑ i, Real.log (point.2 i)

/-- The barrier objective evaluates to the objective value minus the weighted log sum. -/
@[simp] theorem barrierObjective_apply (f : X → ℝ) (μ : ℝ) (x : X) (z : m → ℝ) :
    barrierObjective f μ (x, z) = f x - μ * ∑ i, Real.log (z i) :=
  rfl

/-- **Equation (2.31)** of [benzi2005numerical]. At a positive slack vector $z$, all
slack coordinate derivatives of the Lagrangian vanish if and only if $y_i=\mu/z_i$
for every $i$. -/
theorem barrierLagrangian_slackStationary_iff [DecidableEq m]
    (f μ : ℝ) (c y z : m → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ i, deriv (fun t ↦ logBarrierLagrangian f μ c y (Function.update z i t)) (z i) = 0) ↔
      ∀ i, y i = μ / z i := by
  apply forall_congr'
  intro i
  rw [(hasDerivAt_logBarrierLagrangian_slack f μ c y z i (hz i)).deriv, sub_eq_zero]

variable [Fintype n]

omit [Fintype n] in
/-- **Equations (2.29)–(2.35)** of [benzi2005numerical]. Given a gradient vector $g$,
constraint Jacobian $B$, constraint value $c$, and $\mu>0$, the system
$g+B^Ty=0$, $c+z=0$, $y_i=\mu/z_i$ and $z_i>0$ is equivalent to
$g+B^Ty=0$, $c+z=0$, $y,z\ge0$ and $y_i z_i=\mu$. -/
theorem barrierStationarity_iff_complementarity (g : n → ℝ) (B : Matrix m n ℝ)
    (c y z : m → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    (g + Bᵀ *ᵥ y = 0 ∧ c + z = 0 ∧ (∀ i, 0 < z i) ∧ ∀ i, y i = μ / z i) ↔
      (g + Bᵀ *ᵥ y = 0 ∧ c + z = 0 ∧ 0 ≤ y ∧ 0 ≤ z ∧ ∀ i, y i * z i = μ) := by
  rw [barrier_slackStationary_iff hμ y z]

/-- **Equations (2.36)–(2.37)** of [benzi2005numerical]. Let $H$ be the Lagrangian Hessian,
$B$ the constraint Jacobian, $g$ the objective gradient, and $c$ the constraint value.
Let $y,z$ be multiplier and slack vectors with every $y_i\ne0$, and let
$D=\operatorname{diag}(z_i/y_i)$. The three Newton rows in $(dx,dy,dz)$ hold if and only if
$(dx,-dy)$ solves the reduced system with matrix $\left[\begin{smallmatrix}-H&B^T\\ B&D
\end{smallmatrix}\right]$ and residual $(g+B^Ty,-c-(\mu/y_i)_i)$, and
$dz=(\mu/y_i)_i-z-D\,dy$. -/
theorem barrierNewton_iff_reduced [DecidableEq m] (H : Matrix n n ℝ) (B : Matrix m n ℝ)
    (g : n → ℝ) (c y z : m → ℝ) (μ : ℝ) (hy : ∀ i, y i ≠ 0)
    (dx : n → ℝ) (dy dz : m → ℝ) :
    (H *ᵥ dx + Bᵀ *ᵥ dy = -(g + Bᵀ *ᵥ y) ∧ B *ᵥ dx + dz = -c - z ∧
      diagonal z *ᵥ dy + diagonal y *ᵥ dz = (fun i ↦ μ - y i * z i)) ↔
    (saddlePointMatrix (-H) B B (-diagonal (fun i ↦ z i / y i)) *ᵥ Sum.elim dx (-dy) =
      Sum.elim (g + Bᵀ *ᵥ y) (-c - fun i ↦ μ / y i) ∧
      dz = (fun i ↦ μ / y i) - z - diagonal (fun i ↦ z i / y i) *ᵥ dy) := by
  have hscale : (fun i ↦ (μ - y i * z i) / y i) = (fun i ↦ μ / y i) - z := by
    funext i
    change (μ - y i * z i) / y i = μ / y i - z i
    field_simp [hy i]
  rw [barrierNewton_eq_iff_reduced H B y z hy, hscale]
  simp only [saddlePointMatrix, neg_neg, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Sum.elim_eq_iff, neg_mulVec, mulVec_neg, ← neg_add, neg_eq_iff_eq_neg]
  rw [← sub_eq_add_neg]
  have hmid : -c - z - ((fun i ↦ μ / y i) - z) = -c - (fun i ↦ μ / y i) := by abel
  rw [hmid, and_assoc]

/-- **Section 2.3** of [benzi2005numerical], paragraph after (2.37).
Let $f$ and each $c_i$ be convex functions on the real coordinate space. Suppose their
restrictions to lines through $x$ are differentiable and the second derivatives at
$x$ along $v$ are $v^T H_f v$ and $v^T H_i v$ for symmetric matrices $H_f,H_i$.
For nonnegative multipliers $y$, the Lagrangian Hessian $H_f+\sum_i y_i H_i$ is
positive semidefinite.

**Correction.** Proves semidefiniteness from nonnegative multipliers and line curvatures, correcting
the printed strict-convexity implication.
-/
theorem lagrangianHessian_posSemidef_of_convex
    (f : (n → ℝ) → ℝ) (c : m → (n → ℝ) → ℝ) (x : n → ℝ)
    (Hf : Matrix n n ℝ) (Hc : m → Matrix n n ℝ) (y : m → ℝ) (hy : 0 ≤ y)
    (hsf : Hf.IsSymm) (hsc : ∀ i, (Hc i).IsSymm)
    (hf : ConvexOn ℝ Set.univ f) (hc : ∀ i, ConvexOn ℝ Set.univ (c i))
    (hdf : ∀ v, Differentiable ℝ (fun t : ℝ ↦ f (x + t • v)))
    (hdc : ∀ i v, Differentiable ℝ (fun t : ℝ ↦ c i (x + t • v)))
    (hddf : ∀ v, HasDerivAt (deriv (fun t : ℝ ↦ f (x + t • v))) (v ⬝ᵥ (Hf *ᵥ v)) 0)
    (hddc : ∀ i v, HasDerivAt (deriv (fun t : ℝ ↦ c i (x + t • v))) (v ⬝ᵥ (Hc i *ᵥ v)) 0) :
    (Hf + ∑ i, y i • Hc i).PosSemidef :=
  lagrangianHessian_posSemidef Hf Hc y hy
    (posSemidef_of_convex_lineCurvature f x Hf hsf hf hdf hddf)
    (fun i ↦ posSemidef_of_convex_lineCurvature (c i) x (Hc i) (hsc i) (hc i) (hdc i) (hddc i))

omit [Fintype n] [Fintype m] in
/-- **Section 2.3** of [benzi2005numerical], paragraph after (2.37).
For componentwise nonnegative slack $z$ and multiplier $y$, the diagonal block with
entries $z_i/y_i$ is positive semidefinite. At a zero multiplier the totalized
quotient is zero; the reduction itself requires nonzero multiplier entries. -/
theorem barrierReducedDiagonal_posSemidef [DecidableEq m] (y z : m → ℝ)
    (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (diagonal (fun i ↦ z i / y i)).PosSemidef :=
  barrierSchurDiagonal_posSemidef y z hy hz

/-- **Section 2.3** of [benzi2005numerical], paragraph after (2.37). The scalar objective
$f(t)=t^4$ is strictly convex on $\mathbb R$, but its Hessian at zero is zero.

**Correction.** The text infers positive definiteness of the Lagrangian Hessian from
strict convexity of the objective. With no constraints, this example disproves the
inference. Positive definiteness of the objective Hessian at the current point, together
with semidefinite constraint Hessians and nonnegative multipliers, suffices by
`Optimization.lagrangianHessian_posDef`. -/
theorem strictConvex_hessian_not_posDef_example :
    StrictConvexOn ℝ Set.univ (fun t : ℝ ↦ t ^ 4) ∧ deriv (deriv (fun t : ℝ ↦ t ^ 4)) 0 = 0 := by
  refine ⟨Even.strictConvexOn_pow (by decide : Even 4) (by decide), ?_⟩
  have hderiv : deriv (fun t : ℝ ↦ t ^ 4) = fun t ↦ 4 * t ^ 3 := by
    funext t
    rw [deriv_pow_field]
    norm_num
  rw [hderiv, deriv_const_mul_field, deriv_pow_field]
  norm_num

end BenziGolubLiesen
