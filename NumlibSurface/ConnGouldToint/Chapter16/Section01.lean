/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumlibSurface.ConnGouldToint.Chapter06.Section03

/-!
# Conn, Gould and Toint, Section 16.1: Nonlinear equations and nonlinear least squares

Section 16.1 of [conn2000trust] solves a system of nonlinear equations $c(x) = 0$, with
$c : E \to \mathbb{R}^m$, by minimizing the least-squares objective $f(x) = \frac{1}{2} \|c(x)\|^2$
with a trust-region method. The Hessian of $f$ is
$$\nabla^2 f(x) = \sum_i c_i(x) \nabla^2 c_i(x) + J(x)^T J(x),$$
where $J(x)$ is the Jacobian of $c$. Models of $f$ come from models of the residual $c$: the affine
Gauss–Newton residual $c(x) + J(x) s$, and a quadratic residual that adds the component Hessians.
This module formalizes the objective and the models, the uniform Hessian bound of Theorem 16.1.1,
the transfer of model assumptions from residual models to least-squares models in Theorem 16.1.2,
the vanishing Gauss–Newton Hessian error of Theorem 16.1.3, and the parts of Theorem 16.1.4 on
positive definiteness at a root and on roots of the models. The run of the counterexample is a run
of the basic trust-region algorithm of `NumlibSurface.ConnGouldToint.Chapter06.Section01`.

## Main definitions

* Equation (16.1.4), `ConnGouldToint.Chapter16.leastSquaresObjective`: the objective
  $\frac{1}{2} \|c(x)\|^2$.
* Equation (16.1.6), `ConnGouldToint.Chapter16.gaussNewtonResidual`: the affine residual
  $c_0 + A s$.
* Equation (16.1.7), `ConnGouldToint.Chapter16.newtonLeastSquaresModel`: the Newton model of the
  least-squares objective.
* Equation (16.1.8), `ConnGouldToint.Chapter16.quadraticResidual`: the quadratic residual model.

## Main results

* Equation (16.1.5), `ConnGouldToint.Chapter16.leastSquares_hessian_apply`: the formula for the
  Hessian of $f$.
* Equation (16.1.5), `ConnGouldToint.Chapter16.leastSquares_hessian_sub`: the Hessian error of a
  residual model that agrees to first order.
* Theorem 16.1.1, `ConnGouldToint.Chapter16.theorem_16_1_1`: bounded residual derivatives give a
  nonnegative $C^2$ objective with bounded Hessian.
* Theorem 16.1.2, `ConnGouldToint.Chapter16.theorem_16_1_2`: residual models with uniform bounds on
  the model regions give least-squares models with the same properties.
* `ConnGouldToint.Chapter16.theorem_16_1_2_unbounded_radii_counterexample`: bounds at the centers
  alone do not bound the Hessians of the least-squares models.
* Theorem 16.1.3, `ConnGouldToint.Chapter16.theorem_16_1_3`: the Gauss–Newton Hessian error tends to
  zero along a sequence with vanishing residuals.
* Equation (16.1.9), `ConnGouldToint.Chapter16.theorem_16_1_3_of_tendsto_root`: the same along a
  sequence that converges to a root.
* Theorem 16.1.4, `ConnGouldToint.Chapter16.theorem_16_1_4_root_hessian_iff`: at a root,
  $\nabla^2 f$ is positive definite if and only if $J$ is injective.
* `ConnGouldToint.Chapter16.theorem_16_1_4_surjective_counterexample`: a surjective Jacobian does
  not give positive definiteness.
* Theorem 16.1.4, `ConnGouldToint.Chapter16.theorem_16_1_4_eventually_model_root`: near a regular
  root, the residual models eventually have roots in balls of fixed radius.
* `ConnGouldToint.Chapter16.theorem_16_1_4_exact_model_counterexample`: with exact models, a run can
  alternate between two roots.

## Conventions

* The residual takes values in `EuclideanSpace ℝ ι` for a finite index type $\iota$, and $c_i$ is
  the component `fun y ↦ c y i`.
* The Hessian $\nabla^2 f(x)$ is `iteratedFDeriv ℝ 2 f x`, a continuous bilinear form on $E$, and
  the Jacobian $J(x)$ is `fderiv ℝ c x`.

## Deviations from the source

* **Explicit global bounds.** Theorem 16.1.1 states the differentiability and Hessian bounds
  explicitly on the whole space. See `ConnGouldToint.Chapter16.theorem_16_1_1`.
* **Correction.** Theorem 16.1.2 explicitly bounds model values and Jacobians on the model domains,
  with a counterexample for unbounded radii. See `ConnGouldToint.Chapter16.theorem_16_1_2`,
  `ConnGouldToint.Chapter16.theorem_16_1_2_unbounded_radii_counterexample`.
* **Generalization and scope.** Theorem 16.1.3 gives the Hessian limit from residual convergence and
  a Hessian bound, independently of a BTR run. See `ConnGouldToint.Chapter16.theorem_16_1_3`,
  `ConnGouldToint.Chapter16.theorem_16_1_3_of_tendsto_root`.
* **Correction.** Theorem 16.1.4 requires injectivity for positive definiteness at a root. A
  full-row-rank counterexample verifies the distinction. See
  `ConnGouldToint.Chapter16.theorem_16_1_4_root_hessian_iff`,
  `ConnGouldToint.Chapter16.theorem_16_1_4_surjective_counterexample`.
* **Restricted conclusion and counterexample.** Theorem 16.1.4 proves eventual model roots
  conditional on convergence and local regularity, and includes an exact-model counterexample to
  convergence of the whole run. See `ConnGouldToint.Chapter16.theorem_16_1_4_eventually_model_root`,
  `ConnGouldToint.Chapter16.theorem_16_1_4_exact_model_counterexample`.
* **Theorem 16.1.2** (correction). The bounds on the model residuals and their Jacobians hold
  throughout the model regions, not only at the centers. See
  `ConnGouldToint.Chapter16.theorem_16_1_2_unbounded_radii_counterexample`.
* **Theorem 16.1.4** (reading). At a root, positive definiteness of $\nabla^2 f$ is equivalent to
  injectivity of the Jacobian; a surjective Jacobian is not enough. See
  `ConnGouldToint.Chapter16.theorem_16_1_4_surjective_counterexample`.
* **Theorem 16.1.4** (correction). Exact residual models do not force convergence of the iterates to
  one regular root. The model-root result assumes convergence of the iterates and a trust region
  that contains a ball of fixed positive radius. See
  `ConnGouldToint.Chapter16.theorem_16_1_4_exact_model_counterexample`.
-/

open scoped BigOperators NNReal

namespace ConnGouldToint.Chapter16

variable {E F ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Equation (16.1.4)** of [conn2000trust]. For a residual $c : E \to F$ with values in a real
inner product space, the **least-squares objective** is $f(x) = \frac{1}{2} \|c(x)\|^2$. -/
noncomputable def leastSquaresObjective (c : E → F) (x : E) : ℝ :=
  ‖c x‖ ^ 2 / 2

/-- **Equation (16.1.6)** of [conn2000trust]. For $c_0 \in F$ and a continuous linear map
$A : E \to F$, the **Gauss–Newton residual** is the affine model $s \mapsto c_0 + A s$ of the
residual, in the step $s$. -/
def gaussNewtonResidual (c₀ : F) (A : E →L[ℝ] F) (s : E) : F :=
  c₀ + A s

/-- **Equation (16.1.7)** of [conn2000trust]. Let $c_0 \in \mathbb{R}^\iota$, let
$A : E \to \mathbb{R}^\iota$ be continuous linear, and let $H_i$ be continuous bilinear forms on
$E$. The **Newton least-squares model** is
$$m(s) = \tfrac{1}{2} \|c_0\|^2 + \langle c_0, A s \rangle + \tfrac{1}{2} \|A s\|^2 +
  \tfrac{1}{2} \sum_i (c_0)_i H_i(s, s).$$

With $c_0 = c(x)$, $A = J(x)$ and $H_i = \nabla^2 c_i(x)$, this is the second-order Taylor model
of $f$ at $x$. -/
noncomputable def newtonLeastSquaresModel [Fintype ι] (c₀ : EuclideanSpace ℝ ι)
    (A : E →L[ℝ] EuclideanSpace ℝ ι) (H : ι → E [×2]→L[ℝ] ℝ) (s : E) : ℝ :=
  ‖c₀‖ ^ 2 / 2 + inner ℝ c₀ (A s) + ‖A s‖ ^ 2 / 2 +
    (∑ i : ι, c₀ i * H i (fun _ ↦ s)) / 2

/-- **Equation (16.1.8)** of [conn2000trust]. Let $c_0 \in \mathbb{R}^\iota$, let
$A : E \to \mathbb{R}^\iota$ be continuous linear, and let $H_i$ be continuous bilinear forms on
$E$. The **quadratic residual model** has the components
$$(c_0)_i + (A s)_i + \tfrac{1}{2} H_i(s, s).$$
-/
noncomputable def quadraticResidual [Fintype ι] (c₀ : EuclideanSpace ℝ ι)
    (A : E →L[ℝ] EuclideanSpace ℝ ι) (H : ι → E [×2]→L[ℝ] ℝ) (s : E) :
    EuclideanSpace ℝ ι :=
  c₀ + A s + (1 / 2 : ℝ) • WithLp.toLp 2 (fun i ↦ H i (fun _ ↦ s))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem leastSquaresObjective_eq_sum [Fintype ι] (c : E → EuclideanSpace ℝ ι) :
    leastSquaresObjective c = fun x ↦ ∑ i : ι, c x i ^ 2 / 2 := by
  funext x
  unfold leastSquaresObjective
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
  simp [Real.norm_eq_abs, sq_abs]

private theorem fderiv_residual_component [Finite ι] {c : E → EuclideanSpace ℝ ι}
    {x : E} (hc : DifferentiableAt ℝ c x) (i : ι) :
    fderiv ℝ (fun y ↦ c y i) x = (PiLp.proj _ _ i).comp (fderiv ℝ c x) := by
  have := Fintype.ofFinite ι
  let p : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  exact (p.hasFDerivAt.comp x hc.hasFDerivAt).fderiv

private theorem norm_iteratedFDeriv_two_half_sq_le {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    {K : ℝ} (hK : 0 ≤ K)
    (h₀ : ‖u x‖ ≤ K) (h₁ : ‖fderiv ℝ u x‖ ≤ K)
    (h₂ : ‖iteratedFDeriv ℝ 2 u x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ u y ^ 2 / 2) x‖ ≤ 2 * K ^ 2 := by
  have hu' : ContDiffWithinAt ℝ 2 u Set.univ x := hu.contDiffWithinAt
  obtain ⟨s, hs, hx, hus⟩ := hu'.contDiffOn' le_rfl (by norm_num)
  have huOn : ContDiffOn ℝ 2 u s := by simpa using hus
  have h := norm_iteratedFDerivWithin_mul_le huOn huOn (hs.uniqueDiffOn) hx (n := 2)
    (by norm_num)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] at h
  norm_num at h
  change _ ≤ |u x| * ‖iteratedFDeriv ℝ 2 u x‖ +
    2 * ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
    ‖iteratedFDeriv ℝ 2 u x‖ * ‖iteratedFDeriv ℝ 0 u x‖ at h
  rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one, ← Real.norm_eq_abs] at h
  have hb : ‖iteratedFDeriv ℝ 2 (fun y ↦ u y * u y) x‖ ≤ 4 * K ^ 2 := by
    have h02 := mul_le_mul h₀ h₂ (norm_nonneg _) hK
    have h11 := mul_le_mul h₁ h₁ (norm_nonneg _) hK
    nlinarith
  have heq : (fun y ↦ u y ^ 2 / 2) = (1 / 2 : ℝ) • (fun y ↦ u y * u y) := by
    funext y
    simp [Pi.smul_apply, div_eq_mul_inv, pow_two, mul_comm]
  rw [heq, iteratedFDeriv_const_smul_apply (hu.mul hu), norm_smul]
  norm_num [Real.norm_eq_abs]
  linarith

private theorem norm_leastSquares_hessian_le [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    {x : E} (hc : ContDiffAt ℝ 2 c x) {K : ℝ} (hK : 0 ≤ K)
    (hval : ‖c x‖ ≤ K) (hjac : ‖fderiv ℝ c x‖ ≤ K)
    (hhess : ∀ i, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) x‖ ≤ 2 * (Fintype.card ι : ℝ) * K ^ 2 := by
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  have hp (i : ι) : ‖p i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [p] using PiLp.norm_apply_le z i
  have hci (i : ι) : ContDiffAt ℝ 2 (fun y ↦ c y i) x :=
    (p i).contDiff.contDiffAt.comp x hc
  have hi (i : ι) : ‖fderiv ℝ (fun y ↦ c y i) x‖ ≤ K := by
    rw [fderiv_residual_component (hc.differentiableAt (by norm_num))]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))).trans (by simpa using hjac)
  rw [leastSquaresObjective_eq_sum,
    iteratedFDeriv_fun_sum_apply fun i _ ↦ ((hci i).pow 2).div_const 2]
  refine (norm_sum_le _ _).trans ?_
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) fun i _ ↦
    norm_iteratedFDeriv_two_half_sq_le (hci i) hK
      ((PiLp.norm_apply_le (c x) i).trans hval) (hi i) (hhess i)
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **Theorem 16.1.1** of [conn2000trust]. Let $c : E \to \mathbb{R}^\iota$ be twice continuously
differentiable, and let $K > 0$ be such that
$$\|c(x)\| \le K, \qquad \|J(x)\| \le K, \qquad \|\nabla^2 c_i(x)\| \le K$$
for all $x \in E$ and all $i$. Then the least-squares objective $f = \frac{1}{2} \|c\|^2$ is
twice continuously differentiable, $f(x) \ge 0$ for all $x$, and there is $C > 0$ with
$\|\nabla^2 f(x)\| \le C$ for all $x$.

The proof gives $C = 2 |\iota| K^2 + 1$, where $|\iota|$ is the number of residual components.

**Reading.** The result uses global scalar bounds on the residual, its Jacobian and component
Hessians. It gives global twice continuous differentiability, nonnegativity and a uniform Hessian
bound.
-/
theorem theorem_16_1_1 [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    (hc : ContDiff ℝ 2 c) {K : ℝ} (hK : 0 < K)
    (hval : ∀ x, ‖c x‖ ≤ K) (hjac : ∀ x, ‖fderiv ℝ c x‖ ≤ K)
    (hhess : ∀ i x, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) x‖ ≤ K) :
    ContDiff ℝ 2 (leastSquaresObjective c) ∧
      (∀ x, 0 ≤ leastSquaresObjective c x) ∧
      ∃ C > 0, ∀ x, ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) x‖ ≤ C := by
  refine ⟨(hc.norm_sq ℝ).div_const 2, fun x ↦ by unfold leastSquaresObjective; positivity,
    2 * (Fintype.card ι : ℝ) * K ^ 2 + 1, by positivity, fun x ↦ ?_⟩
  exact (norm_leastSquares_hessian_le hc.contDiffAt hK.le (hval x) (hjac x)
    (fun i ↦ hhess i x)).trans (le_add_of_nonneg_right zero_le_one)

private theorem fderiv_half_sq {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y ↦ u y ^ 2 / 2) x = u x • fderiv ℝ u x := by
  rw [show (fun y ↦ u y ^ 2 / 2) = (fun y ↦ u y ^ 2 * (2 : ℝ)⁻¹) by simp [div_eq_mul_inv]]
  have h := ((hu.hasFDerivAt.pow 2).mul_const (2 : ℝ)⁻¹).fderiv
  rw [h]
  ext v
  simp only [smul_apply, smul_eq_mul]
  ring

open Filter Topology in
private theorem hessian_half_sq_apply {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y ↦ u y ^ 2 / 2) x v =
      u x * iteratedFDeriv ℝ 2 u x v + fderiv ℝ u x (v 0) * fderiv ℝ u x (v 1) := by
  have hd := hu.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y ↦ u y ^ 2 / 2) =ᶠ[𝓝 x] fun y ↦ u y • fderiv ℝ u y :=
    (hu.eventually (by norm_num)).mono fun _ hy ↦ fderiv_half_sq (hy.differentiableAt (by norm_num))
  rw [iteratedFDeriv_two_apply, heq.fderiv_eq,
    (hd.hasFDerivAt.fun_smul hdd.hasFDerivAt).fderiv, iteratedFDeriv_two_apply]
  simp

/-- **Equation (16.1.5)** of [conn2000trust]. Let $c : E \to \mathbb{R}^\iota$ be twice continuously
differentiable at $x$. For all directions $v_0, v_1 \in E$,
$$\nabla^2 f(x)(v_0, v_1) = \sum_i \bigl( c_i(x) \nabla^2 c_i(x)(v_0, v_1) + (J(x) v_0)_i (J(x)
  v_1)_i \bigr),$$
where $f = \frac{1}{2} \|c\|^2$. -/
theorem leastSquares_hessian_apply [Fintype ι] {c : E → EuclideanSpace ℝ ι} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (leastSquaresObjective c) x v =
      ∑ i : ι, (c x i * iteratedFDeriv ℝ 2 (fun y ↦ c y i) x v +
        fderiv ℝ c x (v 0) i * fderiv ℝ c x (v 1) i) := by
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  have hci (i : ι) : ContDiffAt ℝ 2 (fun y ↦ c y i) x :=
    (p i).contDiff.contDiffAt.comp x hc
  rw [leastSquaresObjective_eq_sum,
    iteratedFDeriv_fun_sum_apply (fun i _ ↦ ((hci i).pow 2).div_const 2), sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hessian_half_sq_apply (hci i),
    fderiv_residual_component (hc.differentiableAt (by norm_num))]
  rfl

/-- **Equation (16.1.5)** of [conn2000trust], Hessian error of a model. Let
$c, m : E \to \mathbb{R}^\iota$ be twice continuously differentiable at $x$, with $m(x) = c(x)$
and $J_m(x) = J_c(x)$. Then
$$\nabla^2 f_c(x) - \nabla^2 f_m(x) = \sum_i c_i(x) \bigl( \nabla^2 c_i(x) - \nabla^2 m_i(x)
  \bigr),$$
where $f_c = \frac{1}{2} \|c\|^2$ and $f_m = \frac{1}{2} \|m\|^2$. -/
theorem leastSquares_hessian_sub [Fintype ι] {c m : E → EuclideanSpace ℝ ι} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (hm : ContDiffAt ℝ 2 m x) (hval : m x = c x)
    (hjac : fderiv ℝ m x = fderiv ℝ c x) :
    iteratedFDeriv ℝ 2 (leastSquaresObjective c) x -
        iteratedFDeriv ℝ 2 (leastSquaresObjective m) x =
      ∑ i : ι, c x i • (iteratedFDeriv ℝ 2 (fun y ↦ c y i) x -
        iteratedFDeriv ℝ 2 (fun y ↦ m y i) x) := by
  ext v
  rw [sub_apply, leastSquares_hessian_apply hc, leastSquares_hessian_apply hm,
    ← Finset.sum_sub_distrib, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_apply, sub_apply, hval, hjac]
  change _ = c x i * _
  ring

private theorem fderiv_leastSquaresObjective {c : E → F} {x : E}
    (hc : DifferentiableAt ℝ c x) :
    fderiv ℝ (leastSquaresObjective c) x = (innerSL ℝ (c x)).comp (fderiv ℝ c x) := by
  have h := (hc.hasFDerivAt.norm_sq.const_smul ((2 : ℝ)⁻¹)).fderiv
  have heq : (2 : ℝ)⁻¹ • (fun y ↦ ‖c y‖ ^ 2) = leastSquaresObjective c := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, leastSquaresObjective, div_eq_mul_inv, mul_comm]
  rw [← heq, h]
  ext v
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  ring

open Filter Topology in
/-- **Theorem 16.1.2** of [conn2000trust]. Let $c : E \to \mathbb{R}^\iota$, let $x_k \in E$, let
$B_k \subseteq E$ be model regions with $x_k \in B_k$, and let $m_k : E \to \mathbb{R}^\iota$ be
residual models. Suppose that $c$ is twice continuously differentiable at each $x_k$, that $m_k$
is twice continuously differentiable at each point of $B_k$, and that $m_k(x_k) = c(x_k)$ and
$J_{m_k}(x_k) = J_c(x_k)$. Let $K \ge 0$ and suppose that
$$\|m_k(y)\| \le K, \qquad \|J_{m_k}(y)\| \le K, \qquad \|\nabla^2 (m_k)_i(y)\| \le K$$
for all $k$, all $y \in B_k$ and all $i$. Let $f = \frac{1}{2} \|c\|^2$ and
$f_k = \frac{1}{2} \|m_k\|^2$. Then:

* $f_k$ is twice continuously differentiable at each point of $B_k$;
* $f_k(x_k) = f(x_k)$ and $\nabla f_k(x_k) = \nabla f(x_k)$;
* $\|\nabla^2 f_k(y)\| \le 2 |\iota| K^2$ for all $y \in B_k$;
* suppose that $\|\nabla f(x_k)\| \to 0$ implies $\|\nabla^2 c_i(x_k) - \nabla^2 (m_k)_i(x_k)\|
  \to 0$ for every $i$. If $\|\nabla f(x_k)\| \to 0$, then
  $\|\nabla^2 f(x_k) - \nabla^2 f_k(x_k)\| \to 0$.

**Correction.** The bounds on the values and the Jacobians of the residual models must hold
throughout the model regions. Bounds only at the centers do not control the Hessians of the
least-squares models in unbounded trust regions; see
`ConnGouldToint.Chapter16.theorem_16_1_2_unbounded_radii_counterexample`.

In the last item, the stationarity test of assumption AM.5e uses the full residual vector, so it
is exactly the test $\|\nabla f(x_k)\| \to 0$ on the least-squares gradient.

**Correction.** The residual models need uniform bounds on their values and Jacobians on the actual
model domains. The counterexample has exact first-order agreement at zero and bounded residual-model
curvature, yet the objective-model curvature is unbounded on growing balls.
-/
theorem theorem_16_1_2 [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    {m : ℕ → E → EuclideanSpace ℝ ι} {x : ℕ → E} {B : ℕ → Set E}
    (hc : ∀ k, ContDiffAt ℝ 2 c (x k)) (hx : ∀ k, x k ∈ B k)
    (hm : ∀ k y, y ∈ B k → ContDiffAt ℝ 2 (m k) y)
    (hval : ∀ k, m k (x k) = c (x k))
    (hjac : ∀ k, fderiv ℝ (m k) (x k) = fderiv ℝ c (x k))
    {K : ℝ} (hK : 0 ≤ K)
    (hboundVal : ∀ k y, y ∈ B k → ‖m k y‖ ≤ K)
    (hboundJac : ∀ k y, y ∈ B k → ‖fderiv ℝ (m k) y‖ ≤ K)
    (hboundHess : ∀ k y, y ∈ B k →
      ∀ i, ‖iteratedFDeriv ℝ 2 (fun z ↦ m k z i) y‖ ≤ K) :
    (∀ k y, y ∈ B k → ContDiffAt ℝ 2 (leastSquaresObjective (m k)) y) ∧
    (∀ k, leastSquaresObjective (m k) (x k) = leastSquaresObjective c (x k)) ∧
    (∀ k, fderiv ℝ (leastSquaresObjective (m k)) (x k) =
      fderiv ℝ (leastSquaresObjective c) (x k)) ∧
    (∀ k y, y ∈ B k → ‖iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) y‖ ≤
      2 * (Fintype.card ι : ℝ) * K ^ 2) ∧
    ((Tendsto (fun k ↦ ‖fderiv ℝ (leastSquaresObjective c) (x k)‖) atTop (𝓝 0) →
      ∀ i, Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k) -
        iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k)‖) atTop (𝓝 0)) →
      Tendsto (fun k ↦ ‖fderiv ℝ (leastSquaresObjective c) (x k)‖) atTop (𝓝 0) →
      Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
        iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) (x k)‖) atTop (𝓝 0)) := by
  refine ⟨fun k y hy ↦ ((hm k y hy).norm_sq ℝ).div_const 2,
    fun k ↦ by simp only [leastSquaresObjective, hval k], ?_,
    fun k y hy ↦ norm_leastSquares_hessian_le (hm k y hy) hK
      (hboundVal k y hy) (hboundJac k y hy) (hboundHess k y hy), ?_⟩
  · intro k
    rw [fderiv_leastSquaresObjective ((hm k (x k) (hx k)).differentiableAt (by norm_num)),
      fderiv_leastSquaresObjective ((hc k).differentiableAt (by norm_num)), hval, hjac]
  · intro ham5 hgrad
    let gap (i : ι) (k : ℕ) := iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k) -
      iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k)
    have ht : Tendsto (fun k ↦ ∑ i : ι, K * ‖gap i k‖) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun i _ ↦ (ham5 hgrad i).const_mul K
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) ht
    rw [leastSquares_hessian_sub (hc k) (hm k (x k) (hx k)) (hval k) (hjac k)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    change ‖c (x k) i • gap i k‖ ≤ K * ‖gap i k‖
    rw [norm_smul]
    have hv := hboundVal k (x k) (hx k)
    rw [hval] at hv
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le _ i).trans hv) (norm_nonneg _)

open Filter Topology in
/-- **Theorem 16.1.3** of [conn2000trust]. Let $c : E \to \mathbb{R}^\iota$ be twice continuously
differentiable, let $(x_k)$ be a sequence with $c(x_k) \to 0$, and let $K$ be such that
$\|\nabla^2 c_i(x_k)\| \le K$ for all $i$ and $k$. Let $f_k = \frac{1}{2} \|c(x_k) +
J(x_k)(\cdot - x_k)\|^2$ be the Gauss–Newton model at $x_k$. Then
$$\|\nabla^2 f(x_k) - \nabla^2 f_k(x_k)\| \to 0.$$

The result applies to a subsequence that approaches a root, as in (16.1.9). To conclude the
full-sequence form of assumption AM.5 by this argument, the residuals must tend to zero along
the whole sequence. The Gauss–Newton residual is `ConnGouldToint.Chapter16.gaussNewtonResidual`.

**Generalization.** For the Hessian difference it suffices that the residual tend to zero along the
sequence and that residual Hessians be uniformly bounded there. A root-convergent version recovers
the displayed limit without requiring a BTR run.
-/
theorem theorem_16_1_3 [Fintype ι] {c : E → EuclideanSpace ℝ ι} (hc : ContDiff ℝ 2 c)
    {x : ℕ → E} (hres : Tendsto (fun k ↦ c (x k)) atTop (𝓝 0)) {K : ℝ}
    (hhess : ∀ i k, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k)‖ ≤ K) :
    Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
      iteratedFDeriv ℝ 2 (leastSquaresObjective
        (fun y ↦ gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k))) (x k)‖)
      atTop (𝓝 0) := by
  let m (k : ℕ) (y : E) :=
    gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k)
  have hm (k : ℕ) : ContDiff ℝ 2 (m k) :=
    contDiff_const.add ((fderiv ℝ c (x k)).contDiff.comp (contDiff_id.sub contDiff_const))
  have hmval (k : ℕ) : m k (x k) = c (x k) := by
    simp [m, gaussNewtonResidual]
  have hmjac (k : ℕ) (y : E) : fderiv ℝ (m k) y = fderiv ℝ c (x k) := by
    have h := ((fderiv ℝ c (x k)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const (x k))).const_add (c (x k))
    simpa [m, gaussNewtonResidual] using h.fderiv
  have hmhess (k : ℕ) (i : ι) : iteratedFDeriv ℝ 2 (fun y ↦ m k y i) (x k) = 0 := by
    have hfun : fderiv ℝ (fun y ↦ m k y i) =
        fun _ ↦ (PiLp.proj _ _ i).comp (fderiv ℝ c (x k)) := by
      funext y
      rw [fderiv_residual_component ((hm k).differentiable (by norm_num) y), hmjac]
    ext v
    rw [iteratedFDeriv_two_apply, hfun]
    simp
  change Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
    iteratedFDeriv ℝ 2 (leastSquaresObjective (m k)) (x k)‖) atTop (𝓝 0)
  have ht : Tendsto (fun k ↦ (Fintype.card ι : ℝ) * (‖c (x k)‖ * K)) atTop (𝓝 0) := by
    simpa using (hres.norm.mul_const K).const_mul (Fintype.card ι : ℝ)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) ht
  rw [leastSquares_hessian_sub hc.contDiffAt (hm k).contDiffAt (hmval k) (hmjac k (x k))]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : ι, ‖c (x k)‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [hmhess, sub_zero, norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le (c (x k)) i) (hhess i k)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

open Filter Topology in
/-- **Equation (16.1.9)** of [conn2000trust]. Let $c : E \to \mathbb{R}^\iota$ be twice continuously
differentiable, let $x_k \to x_*$ with $c(x_*) = 0$, and let $K$ be such that
$\|\nabla^2 c_i(x_k)\| \le K$ for all $i$ and $k$. Then the Hessian error
$\|\nabla^2 f(x_k) - \nabla^2 f_k(x_k)\|$ of the Gauss–Newton models $f_k$ tends to $0$.

This follows from `ConnGouldToint.Chapter16.theorem_16_1_3`, because $c(x_k) \to c(x_*) = 0$.

**Generalization.** For the Hessian difference it suffices that the residual tend to zero along the
sequence and that residual Hessians be uniformly bounded there. A root-convergent version recovers
the displayed limit without requiring a BTR run.
-/
theorem theorem_16_1_3_of_tendsto_root [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    (hc : ContDiff ℝ 2 c) {x : ℕ → E} {xStar : E}
    (hx : Tendsto x atTop (𝓝 xStar)) (hroot : c xStar = 0) {K : ℝ}
    (hhess : ∀ i k, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) (x k)‖ ≤ K) :
    Tendsto (fun k ↦ ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) (x k) -
      iteratedFDeriv ℝ 2 (leastSquaresObjective
        (fun y ↦ gaussNewtonResidual (c (x k)) (fderiv ℝ c (x k)) (y - x k))) (x k)‖)
      atTop (𝓝 0) := by
  apply theorem_16_1_3 hc _ hhess
  rw [← hroot]
  exact hc.continuous.continuousAt.tendsto.comp hx

/-- Bounds on the residual models at the centers alone do not bound the Hessians of the
least-squares models, which shows the correction in Theorem 16.1.2 of [conn2000trust]. On
$\mathbb{R}$, the residual $c = 0$ and the model residual $m(t) = t^2$ agree to first order at
the center $0$, and $|m''(t)| \le 2$ for all $t$. But no $K$ bounds the Hessian of
$\frac{1}{2} m^2$ on all the balls $[-k, k]$, $k \in \mathbb{N}$.

**Correction.** The residual models need uniform bounds on their values and Jacobians on the actual
model domains. The counterexample has exact first-order agreement at zero and bounded residual-model
curvature, yet the objective-model curvature is unbounded on growing balls.
-/
theorem theorem_16_1_2_unbounded_radii_counterexample :
    (fun t : ℝ ↦ t ^ 2) 0 = (fun _ : ℝ ↦ (0 : ℝ)) 0 ∧
    fderiv ℝ (fun t : ℝ ↦ t ^ 2) 0 = fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0 ∧
    (∀ t : ℝ, ‖iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2) t‖ ≤ 2) ∧
    ¬ ∃ K : ℝ, ∀ (k : ℕ) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) k →
      ‖iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2)) t‖ ≤ K := by
  have hsq : ContDiff ℝ 2 (fun y : ℝ ↦ y ^ 2) := contDiff_id.pow 2
  have hderiv (t : ℝ) : fderiv ℝ (fun y : ℝ ↦ y ^ 2) t =
      (2 * t) • ContinuousLinearMap.id ℝ ℝ := by
    have h := ((hasFDerivAt_id (𝕜 := ℝ) t).pow 2).fderiv
    change fderiv ℝ (fun y : ℝ ↦ y ^ 2) t = _ at h
    rw [h]
    congr 1
    simp [two_mul]
  have hid (t : ℝ) (v : Fin 2 → ℝ) : iteratedFDeriv ℝ 2 id t v = 0 := by
    have hf : fderiv ℝ (id : ℝ → ℝ) = fun _ ↦ ContinuousLinearMap.id ℝ ℝ :=
      funext fun y ↦ (hasFDerivAt_id y).fderiv
    rw [iteratedFDeriv_two_apply, hf]
    simp
  have hess (t : ℝ) (v : Fin 2 → ℝ) :
      iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2) t v = 2 * v 0 * v 1 := by
    have heq : (fun y : ℝ ↦ y ^ 2) = (2 : ℝ) • (fun y : ℝ ↦ y ^ 2 / 2) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hhalf := hessian_half_sq_apply (x := t) (u := id) contDiff_id.contDiffAt v
    change iteratedFDeriv ℝ 2 (fun y : ℝ ↦ y ^ 2 / 2) t v = _ at hhalf
    rw [heq, iteratedFDeriv_const_smul_apply ((hsq.div_const 2).contDiffAt),
      smul_apply, hhalf, hid]
    rw [(hasFDerivAt_id (𝕜 := ℝ) t).fderiv]
    simp [mul_assoc]
  refine ⟨by simp, by simp [hderiv], fun t ↦ ?_, ?_⟩
  · apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
    intro v
    rw [hess, Fin.prod_univ_two]
    simp [norm_mul, mul_assoc]
  · rintro ⟨K, hK⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (max K 1)
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk₁ : (1 : ℝ) < k := (le_max_right K 1).trans_lt hk
    have hball : (k : ℝ) ∈ Metric.closedBall (0 : ℝ) k := by
      simp [Metric.mem_closedBall]
    let v : Fin 2 → ℝ := fun _ ↦ 1
    have hl := (iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2))
      (k : ℝ)).le_opNorm v
    have hval : iteratedFDeriv ℝ 2 (leastSquaresObjective (fun y : ℝ ↦ y ^ 2))
        (k : ℝ) v = 6 * (k : ℝ) ^ 2 := by
      have heq : leastSquaresObjective (fun y : ℝ ↦ y ^ 2) =
          (fun y : ℝ ↦ (y ^ 2) ^ 2 / 2) := by
        funext y
        simp [leastSquaresObjective, Real.norm_eq_abs]
      rw [heq, hessian_half_sq_apply hsq.contDiffAt, hess, hderiv]
      simp [v]
      ring
    rw [hval] at hl
    have hle : 6 * (k : ℝ) ^ 2 ≤ K := by
      simpa [v, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 6 * (k : ℝ) ^ 2)]
        using hl.trans (by simpa [v] using hK k k hball)
    have hlt := (le_max_left K 1).trans_lt hk
    nlinarith [mul_nonneg (sub_nonneg.mpr hk₁.le) hk₀]

/-- **Theorem 16.1.4** of [conn2000trust], positive definiteness at a root. Let
$c : E \to \mathbb{R}^\iota$ be twice continuously differentiable at $x$, with $c(x) = 0$. Then
$\nabla^2 f(x)(v, v) > 0$ for all $v \neq 0$ if and only if the Jacobian $J(x)$ is injective.

**Reading.** The theorem assumes that the Hessian of $f$ at the root is positive definite. At a
root this assumption is exactly injectivity of $J(x)$. A surjective Jacobian, of full row rank,
does not suffice; see `ConnGouldToint.Chapter16.theorem_16_1_4_surjective_counterexample`.

**Correction.** At a root the least-squares Hessian is positive definite exactly when the Jacobian
is injective. Full row rank alone, illustrated by a surjective map with a nontrivial kernel, is
insufficient.
-/
theorem theorem_16_1_4_root_hessian_iff [Fintype ι] {c : E → EuclideanSpace ℝ ι} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (hroot : c x = 0) :
    (∀ v : E, v ≠ 0 → 0 < iteratedFDeriv ℝ 2 (leastSquaresObjective c) x (fun _ ↦ v)) ↔
      Function.Injective (fderiv ℝ c x) := by
  have hdiag (v : E) :
      iteratedFDeriv ℝ 2 (leastSquaresObjective c) x (fun _ ↦ v) = ‖fderiv ℝ c x v‖ ^ 2 := by
    rw [leastSquares_hessian_apply hc, hroot, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp [Real.norm_eq_abs, sq]
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h v hv
    by_contra hne
    simpa [hdiag v, hv] using h v hne
  · intro h v hv
    rw [hdiag]
    exact pow_pos (norm_pos_iff.mpr fun hz ↦ hv (h v hz)) 2

/-- A surjective Jacobian at a root does not make the least-squares Hessian positive definite, which
supports the reading of Theorem 16.1.4 of [conn2000trust]. The residual
$c : \mathbb{R}^2 \to \mathbb{R}^1$, $c(x) = x_1$, is twice continuously differentiable,
$c(0) = 0$ and $J(0)$ is surjective, but $\nabla^2 f(0)(v, v) = 0$ for $v = (0, 1)$.

**Correction.** At a root the least-squares Hessian is positive definite exactly when the Jacobian
is injective. Full row rank alone, illustrated by a surjective map with a nontrivial kernel, is
insufficient.
-/
theorem theorem_16_1_4_surjective_counterexample :
    ∃ c : ℝ × ℝ → EuclideanSpace ℝ (Fin 1), ContDiff ℝ 2 c ∧ c 0 = 0 ∧
      Function.Surjective (fderiv ℝ c 0) ∧
      ¬ (∀ v : ℝ × ℝ, v ≠ 0 →
        0 < iteratedFDeriv ℝ 2 (leastSquaresObjective c) 0 (fun _ ↦ v)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  let A : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (e : (Fin 1 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
      (ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hA : fderiv ℝ (A : ℝ × ℝ → EuclideanSpace ℝ (Fin 1)) 0 = A := A.fderiv
  refine ⟨A, A.contDiff, A.map_zero, ?_, ?_⟩
  · rw [hA]
    intro y
    refine ⟨(e.symm y 0, 0), ?_⟩
    apply e.symm.injective
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    funext i
    fin_cases i
    rfl
  · rw [theorem_16_1_4_root_hessian_iff A.contDiff.contDiffAt A.map_zero, hA]
    intro h
    have hz : A (0, 1) = A (0, 0) := rfl
    have heq := congrArg Prod.snd (h hz)
    norm_num at heq

open Filter Topology in
/-- **Theorem 16.1.4** of [conn2000trust], roots of the models. Let $E$ be a Banach space and
$c : E \to \mathbb{R}^\iota$. Let $x_k \to x_*$, where $c$ is continuously differentiable at
$x_*$, $c(x_*) = 0$, and $J(x_*)$ is a continuous linear isomorphism $E \to \mathbb{R}^\iota$.
Let $R > 0$ and $L \ge 0$. Suppose that each residual model $m_k$ is differentiable on the
closed ball $B(x_k, R)$, that
$$\|J_{m_k}(y) - J_{m_k}(x_k)\| \le L \|y - x_k\| \quad \text{for all } y \in B(x_k, R),$$
and that $m_k(x_k) = c(x_k)$ and $J_{m_k}(x_k) = J_c(x_k)$. Then for all sufficiently large $k$
there is $y \in B(x_k, R)$ with $m_k(y) = 0$.

**Correction.** Exact models alone do not force the iterates to converge to a regular root; see
`ConnGouldToint.Chapter16.theorem_16_1_4_exact_model_counterexample`. Here the convergence
$x_k \to x_*$ is a hypothesis, and the trust region must contain a ball of fixed radius $R$.

A uniform bound on the second derivatives of the models gives the Lipschitz bound by the mean
value theorem.

**Correction.** The eventual model-root conclusion assumes convergence, an invertible Jacobian and
uniform local derivative control on a fixed-radius ball. The exact-model example has successful
sufficient-decrease steps with distinct subsequential limits, refuting the unrestricted convergence
claim.
-/
theorem theorem_16_1_4_eventually_model_root [CompleteSpace E] [Fintype ι]
    {c : E → EuclideanSpace ℝ ι} {m : ℕ → E → EuclideanSpace ℝ ι}
    {x : ℕ → E} {xStar : E} (hx : Tendsto x atTop (𝓝 xStar))
    (hc : ContDiffAt ℝ 1 c xStar) (hroot : c xStar = 0)
    (e : E ≃L[ℝ] EuclideanSpace ℝ ι) (he : (e : E →L[ℝ] EuclideanSpace ℝ ι) =
      fderiv ℝ c xStar) {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hmodel : ∀ k y, y ∈ Metric.closedBall (x k) R → DifferentiableAt ℝ (m k) y)
    (hlip : ∀ k y, y ∈ Metric.closedBall (x k) R →
      ‖fderiv ℝ (m k) y - fderiv ℝ (m k) (x k)‖ ≤ L * ‖y - x k‖)
    (hval : ∀ k, m k (x k) = c (x k))
    (hjac : ∀ k, fderiv ℝ (m k) (x k) = fderiv ℝ c (x k)) :
    ∀ᶠ k in atTop, ∃ y ∈ Metric.closedBall (x k) R, m k y = 0 := by
  let A : E →L[ℝ] EuclideanSpace ℝ ι := e
  let inv : A.NonlinearRightInverse := {
    toFun := e.symm
    nnnorm := ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] E)‖₊ + 1
    bound' := fun y ↦ (ContinuousLinearMap.le_opNorm
      (e.symm : EuclideanSpace ℝ ι →L[ℝ] E) y).trans (by
        push_cast
        gcongr
        linarith)
    right_inv' := e.apply_symm_apply }
  let C : ℝ≥0 := inv.nnnorm⁻¹ / 2
  have hi : 0 < (inv.nnnorm : ℝ) := by
    change 0 < ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] E)‖ + 1
    positivity
  have hC : 0 < (C : ℝ) := by
    change 0 < (↑(inv.nnnorm⁻¹ / 2) : ℝ)
    push_cast
    positivity
  have hgap : 0 < (inv.nnnorm : ℝ)⁻¹ - C := by
    change 0 < (inv.nnnorm : ℝ)⁻¹ - ↑(inv.nnnorm⁻¹ / 2)
    push_cast
    linarith [inv_pos.mpr hi]
  let r := min R ((C : ℝ) / (2 * (L + 1)))
  have hr : 0 < r := lt_min hR (div_pos hC (by positivity))
  have hrR : r ≤ R := min_le_left _ _
  have hLr : L * r ≤ (C : ℝ) / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp
      (min_le_right R ((C : ℝ) / (2 * (L + 1))))
    nlinarith
  have hA : Tendsto (fun k ↦ fderiv ℝ c (x k)) atTop (𝓝 A) := by
    change Tendsto _ _ (𝓝 (e : E →L[ℝ] EuclideanSpace ℝ ι))
    rw [he]
    exact (hc.continuousAt_fderiv (by norm_num)).tendsto.comp hx
  have hsmallA := hA.eventually (Metric.ball_mem_nhds A (half_pos hC))
  have hsmallC : Tendsto (fun k ↦ c (x k)) atTop (𝓝 0) := by
    rw [← hroot]
    exact hc.continuousAt.tendsto.comp hx
  filter_upwards [hsmallA, hsmallC.eventually (Metric.ball_mem_nhds 0 (mul_pos hgap hr))]
    with k hkA hkC
  have hsub := Metric.closedBall_subset_closedBall hrR (x := x k)
  have hclose (y : E) (hy : y ∈ Metric.closedBall (x k) r) :
      ‖fderiv ℝ (m k) y - A‖ ≤ (C : ℝ) := by
    have hy' : ‖y - x k‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hcenter : ‖fderiv ℝ (m k) (x k) - A‖ ≤ (C : ℝ) / 2 := by
      rw [hjac k]
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hkA).le
    calc
      _ ≤ ‖fderiv ℝ (m k) y - fderiv ℝ (m k) (x k)‖ +
          ‖fderiv ℝ (m k) (x k) - A‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * r + (C : ℝ) / 2 :=
        add_le_add ((hlip k y (hsub hy)).trans (mul_le_mul_of_nonneg_left hy' hL)) hcenter
      _ ≤ _ := by linarith
  have happ : ApproximatesLinearOn (m k) A (Metric.closedBall (x k) r) C := by
    intro y hy z hz
    have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw ↦ ((hmodel k w (hsub hw)).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt)
      hclose (convex_closedBall (x k) r) hz hy
    simpa [map_sub, sub_sub_sub_comm] using h
  have hzero : (0 : EuclideanSpace ℝ ι) ∈
      Metric.closedBall (m k (x k)) (((inv.nnnorm : ℝ)⁻¹ - C) * r) := by
    rw [Metric.mem_closedBall, hval k, dist_comm]
    exact (Metric.mem_ball.mp hkC).le
  obtain ⟨y, hy, hmy⟩ :=
    happ.surjOn_closedBall_of_nonlinearRightInverse inv hr.le Set.Subset.rfl hzero
  exact ⟨y, hsub hy, hmy⟩

open Filter Topology Chapter06 in
/-- Exact models do not force a trust-region run to converge to a particular regular root, which
shows the correction in Theorem 16.1.4 of [conn2000trust]. The residual $\sin$ is twice
continuously differentiable, $\sin 0 = 0$, $\sin' 0 = 1$, and $|\sin|$, $|\sin'|$ and $|\sin''|$
are bounded by $1$. There is a run of the basic trust-region algorithm for
$f = \frac{1}{2} \sin^2$ with the parameters (6.1.6) such that every model is $f$ itself, every
iteration is successful, every step satisfies assumption AA.1 with $\kappa = 1/4$ for every
$\beta \ge 1$, and
$$x_{2k} \to 0, \qquad x_{2k+1} \to \pi.$$

The run is a `ConnGouldToint.Chapter06.BTRRun` with `ConnGouldToint.Chapter06.defaultBTRParams`,
and AA.1 is `ConnGouldToint.Chapter06.HasSufficientModelDecrease`. In the construction the
radius is fixed at $\pi$, the iterates alternate between the two branches of the inverse sine,
and the residual is halved at each accepted step.

**Correction.** The eventual model-root conclusion assumes convergence, an invertible Jacobian and
uniform local derivative control on a fixed-radius ball. The exact-model example has successful
sufficient-decrease steps with distinct subsequential limits, refuting the unrestricted convergence
claim.
-/
theorem theorem_16_1_4_exact_model_counterexample :
    ContDiff ℝ 2 Real.sin ∧ (Real.sin 0 = 0 ∧ deriv Real.sin 0 = 1) ∧
    (∀ z : ℝ, |Real.sin z| ≤ 1 ∧ |deriv Real.sin z| ≤ 1 ∧
      |deriv (deriv Real.sin) z| ≤ 1) ∧
    ∃ run : BTRRun (leastSquaresObjective Real.sin) defaultBTRParams (fun _ _ _ _ ↦ True),
      (∀ k, run.model k = leastSquaresObjective Real.sin) ∧
      (∀ k, k ∈ run.successful) ∧
      (∀ k β, 1 ≤ β → HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
        (gradient (leastSquaresObjective Real.sin) (run.x k)) β (run.Δ k) (1 / 4)) ∧
      Tendsto (fun k ↦ run.x (2 * k)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ run.x (2 * k + 1)) atTop (𝓝 Real.pi) := by
  refine ⟨Real.contDiff_sin, ⟨Real.sin_zero, by simp⟩, ?_, ?_⟩
  · intro z
    simpa only [Real.deriv_sin, Real.deriv_cos, abs_neg] using
      ⟨Real.abs_sin_le_one z, Real.abs_cos_le_one z, Real.abs_sin_le_one z⟩
  let r (k : ℕ) : ℝ := (1 / 2) ^ (k + 1)
  let a (k : ℕ) := Real.arcsin (r k)
  let x (k : ℕ) := if k % 2 = 0 then a k else Real.pi - a k
  let s (k : ℕ) := x (k + 1) - x k
  let f := leastSquaresObjective Real.sin
  have hnext (k : ℕ) : x k + s k = x (k + 1) := by simp [s]
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hr₁ (k : ℕ) : r k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hsin (k : ℕ) : Real.sin (x k) = r k := by
    have h := Real.sin_arcsin (show -1 ≤ r k by linarith [hr k]) (hr₁ k)
    simp only [x]
    split <;> simp_all [a, Real.sin_pi_sub]
  have hxrange (k : ℕ) : x k ∈ Set.Icc (0 : ℝ) Real.pi := by
    have ha₀ : 0 ≤ a k := (Real.arcsin_nonneg.mpr (hr k).le)
    have haπ : a k ≤ Real.pi := (Real.arcsin_le_pi_div_two _).trans (by linarith [Real.pi_pos])
    simp only [x]
    split <;> exact ⟨by linarith, by linarith⟩
  have hdec (k : ℕ) : f (x k) - f (x k + s k) = (3 / 8) * r k ^ 2 := by
    have hrec : r (k + 1) = r k * (1 / 2) := by simp only [r, pow_succ _ (k + 1)]
    simp only [f, leastSquaresObjective, hnext, hsin]
    rw [Real.norm_of_nonneg (hr k).le, Real.norm_of_nonneg (hr (k + 1)).le, hrec]
    ring
  have hpos (k : ℕ) : 0 < f (x k) - f (x k + s k) := by
    rw [hdec]
    positivity
  have hratio (k : ℕ) : btrRatio f f (x k) (s k) = 1 := by
    unfold btrRatio Optimization.reductionRatio
    exact div_self (hpos k).ne'
  let run : BTRRun f defaultBTRParams (fun _ _ _ _ ↦ True) := {
    x := x
    s := s
    Δ := fun _ ↦ Real.pi
    p := fun _ ↦ normSeminorm ℝ ℝ
    norm_separates := fun _ _ h ↦ norm_eq_zero.mp h
    model := fun _ ↦ f
    delta_initial_pos := Real.pi_pos
    feasible := fun k ↦ by
      rw [mem_trustRegion, hnext]
      change |x (k + 1) - x k| ≤ Real.pi
      exact abs_le.mpr ⟨by linarith [(hxrange (k + 1)).1, (hxrange k).2],
        by linarith [(hxrange (k + 1)).2, (hxrange k).1]⟩
    sufficient_decrease := fun _ ↦ trivial
    predicted_pos := hpos
    iterate_update := fun k ↦ by
      unfold Optimization.acceptStep
      change x (k + 1) = if defaultBTRParams.η₁ ≤ btrRatio f f (x k) (s k)
        then x k + s k else x k
      rw [hratio k, ite_eq_left (defaultBTRParams.eta₁_le_eta₂.trans
        defaultBTRParams.eta₂_lt_one.le), hnext]
    radius_update := fun k ↦ by
      rw [hratio]
      exact ⟨fun _ ↦ le_rfl, by norm_num [defaultBTRParams], by norm_num [defaultBTRParams]⟩ }
  have ha : Tendsto a atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)).comp
      (tendsto_add_atTop_nat 1)
    simpa [a, r, Function.comp_def] using Real.continuous_arcsin.continuousAt.tendsto.comp ht
  refine ⟨run, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    change defaultBTRParams.η₁ ≤ btrRatio f f (x k) (s k)
    rw [hratio]
    exact (defaultBTRParams.eta₁_le_eta₂.trans defaultBTRParams.eta₂_lt_one.le)
  · intro k β hβ
    change HasSufficientModelDecrease f (x k) (s k) (gradient f (x k)) β Real.pi (1 / 4)
    have hgrad : ‖gradient f (x k)‖ ≤ r k := by
      have hfun : f = fun y ↦ Real.sin y ^ 2 / 2 := by
        funext y
        simp [f, leastSquaresObjective, Real.norm_eq_abs, sq_abs]
      have hd := (((Real.hasDerivAt_sin (x k)).pow 2).div_const 2).deriv
      change deriv (fun y ↦ Real.sin y ^ 2 / 2) (x k) = _ at hd
      rw [hfun, gradient_eq_deriv', hd]
      simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, Real.norm_eq_abs, hsin]
      have heq : (2 * r k * Real.cos (x k)) / 2 = r k * Real.cos (x k) := by ring
      rw [heq, abs_mul, abs_of_pos (hr k)]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x k)) (hr k).le
    refine ⟨by norm_num, ?_⟩
    rw [hdec]
    have hquot : ‖gradient f (x k)‖ / β ≤ ‖gradient f (x k)‖ := by
      rw [div_le_iff₀ (zero_lt_one.trans_le hβ)]
      exact le_mul_of_one_le_right (norm_nonneg _) hβ
    calc
      _ ≤ (1 / 4 : ℝ) * ‖gradient f (x k)‖ * ‖gradient f (x k)‖ :=
        mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hquot) (by positivity)
      _ ≤ (1 / 4 : ℝ) * r k * r k := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (r k)]
  · change Tendsto (fun k ↦ x (2 * k)) atTop (𝓝 0)
    have hidx : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ by change k ≤ _; omega) tendsto_id
    simpa [x, Function.comp_def] using ha.comp hidx
  · change Tendsto (fun k ↦ x (2 * k + 1)) atTop (𝓝 Real.pi)
    have hidx : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ by change k ≤ _; omega) tendsto_id
    simpa [x, Function.comp_def] using (ha.comp hidx).const_sub Real.pi

end ConnGouldToint.Chapter16
