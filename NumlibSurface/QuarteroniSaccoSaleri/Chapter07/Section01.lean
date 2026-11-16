/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Nonlinear.DennisMore
import Numlib.Nonlinear.DifferenceJacobian
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Newton
import Numlib.Nonlinear.QuasiNewton
import Numlib.Stationary.ConsistentlyOrdered
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 7.1: Solution of Systems of Nonlinear Equations

This module formalizes Section 7.1 of [quarteroni2000numerical], on methods for a system $F(x) = 0$
with $F : \mathbb{R}^n \to \mathbb{R}^n$. Newton's method (7.4) solves
$J_F(x^{(k)}) \delta x^{(k)} = -F(x^{(k)})$ at each step, and converges quadratically near a root
$x^*$ where $J_F(x^*)$ is invertible and $J_F$ is Lipschitz (Theorem 7.1). The variants of Newton's
method in the section are: the Newton–SOR method (7.7)–(7.8), which solves the Newton system by $m$
steps of SOR (Exercise 7.1); the difference-Jacobian method (7.9)–(7.10), which converges linearly
for small increments and quadratically for increments of the size of the error (Property 7.1); and
Broyden's method (7.11)–(7.14), whose rank-one update is characterized by the secant condition and a
least-change property, and which converges superlinearly (Property 7.2).

The last part treats the fixed-point iteration $x^{(k+1)} = G(x^{(k)})$ (7.17): contractive maps
(Definition 7.1), the contraction-mapping theorem (Theorem 7.2), local convergence when
$\rho(J_G(x^*)) < 1$ (Property 7.3), the two iteration functions of Example 7.4, and Newton's method
as a fixed-point iteration (Remark 7.1). The proofs specialize `Numlib.Nonlinear.Newton`,
`Numlib.Nonlinear.DifferenceJacobian`, `Numlib.Nonlinear.QuasiNewton`,
`Numlib.Nonlinear.DennisMore`, `Numlib.Nonlinear.FixedPoint`, and `Numlib.Stationary.Basic` for the
inner SOR iteration.

## Main definitions

* Section 7.1.2, `QuarteroniSaccoSaleri.Chapter07.newtonSORStep` and
  `QuarteroniSaccoSaleri.Chapter07.newtonSORIterate`: the $m$-step Newton–SOR method.
* Equation (7.10), `QuarteroniSaccoSaleri.Chapter07.equation_7_10`: Newton's method with the
  difference Jacobian.
* Definition 7.1, `QuarteroniSaccoSaleri.Chapter07.definition_7_1`: a contractive map on a set.
* Section 7.1, `QuarteroniSaccoSaleri.Chapter07.jacobianMatrix`: the Jacobian matrix $J_F(x)$.
* Example 7.4, `QuarteroniSaccoSaleri.Chapter07.example_7_4_F`,
  `QuarteroniSaccoSaleri.Chapter07.example_7_4_G₁` and
  `QuarteroniSaccoSaleri.Chapter07.example_7_4_G₂`: the system and its two iteration functions
  (7.18).

## Main results

* Equation (7.4), `QuarteroniSaccoSaleri.Chapter07.equation_7_4`: the Newton increment solves the
  Newton system.
* Theorem 7.1, `QuarteroniSaccoSaleri.Chapter07.theorem_7_1`: local quadratic convergence of
  Newton's method.
* Exercise 7.1, `QuarteroniSaccoSaleri.Chapter07.exercise_7_1`: the closed form (7.8) of the
  $m$-step Newton–SOR iterate.
* Equation (7.9), `QuarteroniSaccoSaleri.Chapter07.equation_7_9`: the entries and columns of the
  difference Jacobian.
* Property 7.1, `QuarteroniSaccoSaleri.Chapter07.property_7_1`: linear convergence of the
  difference-Jacobian method for small increments.
* Property 7.1, `QuarteroniSaccoSaleri.Chapter07.property_7_1_quadratic` and
  `QuarteroniSaccoSaleri.Chapter07.property_7_1_residual`: quadratic convergence when the increments
  are bounded by the error or by the residual.
* Equation (7.11), `QuarteroniSaccoSaleri.Chapter07.equation_7_11`: the Broyden step solves
  $Q_k \delta x = -F(x^{(k)})$.
* Equation (7.12), `QuarteroniSaccoSaleri.Chapter07.equation_7_12`: the updated matrix satisfies the
  secant condition.
* Equation (7.14), `QuarteroniSaccoSaleri.Chapter07.equation_7_14`: Broyden's update in matrix form.
* Section 7.1.4, `QuarteroniSaccoSaleri.Chapter07.broydenUpdate_leastChange`: Broyden's update is
  the unique operator that satisfies the secant condition and agrees with $Q_{k-1}$ on the
  orthogonal complement of $\delta x^{(k)}$.
* Property 7.2, `QuarteroniSaccoSaleri.Chapter07.property_7_2`: local superlinear convergence of
  Broyden's method.
* Theorem 7.2, `QuarteroniSaccoSaleri.Chapter07.theorem_7_2`: a contractive self-map of a nonempty
  closed set has a unique fixed point there.
* Theorem 7.2, `QuarteroniSaccoSaleri.Chapter07.theorem_7_2_tendsto`: the fixed-point iterates
  converge, with an a priori error estimate.
* Property 7.3, `QuarteroniSaccoSaleri.Chapter07.property_7_3`: if $\rho(J_G(x^*)) < 1$, the
  fixed-point iteration converges locally.
* Property 7.3, `QuarteroniSaccoSaleri.Chapter07.property_7_3_norm`: if $\|J_G(x^*)\| < q < 1$, the
  convergence is geometric with ratio $q$.
* Example 7.4, `QuarteroniSaccoSaleri.Chapter07.example_7_4_fixedPoint` and
  `QuarteroniSaccoSaleri.Chapter07.example_7_4_spectralRadius`: the two solutions are fixed points
  of $G_1$ and $G_2$, where the Jacobians have spectral radii $0$ and $\sqrt{2/3}$.
* Remark 7.1, `QuarteroniSaccoSaleri.Chapter07.remark_7_1`: Newton's method is the fixed-point
  iteration of $G_N(x) = x - J_F(x)^{-1} F(x)$ and a preconditioned Richardson iteration.

## Conventions

* Newton's iteration is the backbone's `Newton.iterate F F' x₀`, with the inverse
  `ContinuousLinearMap.inverse`, whose value at a noninvertible operator is $0$. So the clause "the
  sequence is uniquely defined" is the statement that every $F'(x^{(k)})$ is invertible.
* The difference-Jacobian iteration (7.10) is `QuarteroniSaccoSaleri.Chapter07.equation_7_10`,
  Broyden's method is `Broyden.step` and `Broyden.iterate`, and the fixed-point iteration (7.17) is
  `G^[k] x₀`, which needs no definition of its own.
* Theorem 7.1 is stated on any finite-dimensional real normed space, because the source allows "any
  vector norm" with the induced matrix norm. The results that need coordinates are stated on
  `EuclideanSpace ℝ (Fin n)`. The Jacobian matrix $J_F(x)$ is
  `QuarteroniSaccoSaleri.Chapter07.jacobianMatrix F x`, the matrix of `fderiv ℝ F x` in the standard
  basis.
* Spectral radii are `Matrix.complexSpectralRadius`, as in Chapter 4.

## Implementation notes

* Definition 7.1 does not require the contraction constant $\alpha$ to be nonnegative, as in the
  source. A negative $\alpha$ forces the set to have at most one point, and is the same as
  $\alpha = 0$. The a priori estimate of the proof of Theorem 7.2 is stated for $\alpha \ge 0$.

## Deviations from the source

* **Property 7.1** (reading). The source states the property in the norm $\|\cdot\|_1$. Here it is
  stated in the Euclidean norm, where the error of the difference Jacobian carries a factor
  $\sqrt{n}$ that changes no conclusion. See `QuarteroniSaccoSaleri.Chapter07.property_7_1`.
* **Property 7.1, "or, equivalently" clause** (reading). The clause is used in one direction: a
  bound of the increments by the residual implies quadratic convergence. See
  `QuarteroniSaccoSaleri.Chapter07.property_7_1_residual`.
* **Property 7.2** (reading). The source states the property without proof. It is stated on
  $\mathbb{R}^n$ with the hypotheses of Theorem 7.1, and the proof gives the constants $c_k$ of
  (7.15) explicitly. See `QuarteroniSaccoSaleri.Chapter07.property_7_2`.
* **Theorem 7.2** (correction). The source omits $D_0 \neq \emptyset$. The empty set satisfies the
  other hypotheses and has no fixed point. See `QuarteroniSaccoSaleri.Chapter07.theorem_7_2`.
* **Remark 7.1** (correction). The source writes Newton's method as $(I - J_{G_N}(x^{(k)})) \delta
  x^{(k)} = -r^{(k)}$. The matrix that makes the identity true is $J_F(x^{(k)})$. See
  `QuarteroniSaccoSaleri.Chapter07.remark_7_1`.

## Not formalized

* **Examples 7.1–7.3.** They are numerical computations.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped ENNReal InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Newton's method (7.4) and Theorem 7.1 -/

/-- **Equation (7.4)** of [quarteroni2000numerical], Newton's method for $F(x) = 0$. At each step,
Newton's method solves $J_F(x^{(k)}) \delta x^{(k)} = -F(x^{(k)})$ and sets
$x^{(k+1)} = x^{(k)} + \delta x^{(k)}$. Let $E$ be a real normed space, let $F : E \to E$, and
let $F'(x)$ be a continuous linear map for each $x$. Let $x^{(k)}$ be the Newton iterates from
$x^{(0)}$, and suppose that $F'(x^{(k)})$ is invertible. Then the increment
$\delta x^{(k)} = x^{(k+1)} - x^{(k)}$ satisfies
$$F'(x^{(k)}) \delta x^{(k)} = -F(x^{(k)}), \qquad x^{(k+1)} = x^{(k)} + \delta x^{(k)}.$$

The iterates are `Newton.iterate F F' x₀`, and $F'(x)$ stands for $J_F(x)$. Invertibility is a
continuous linear equivalence `e` whose underlying map is $F'(x^{(k)})$. -/
theorem equation_7_4 (F : E → E) (F' : E → E →L[ℝ] E) (x₀ : E) (k : ℕ) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = F' (Newton.iterate F F' x₀ k)) :
    F' (Newton.iterate F F' x₀ k) (Newton.iterate F F' x₀ (k + 1) - Newton.iterate F F' x₀ k)
        = -F (Newton.iterate F F' x₀ k) ∧
      Newton.iterate F F' x₀ (k + 1)
        = Newton.iterate F F' x₀ k
          + (Newton.iterate F F' x₀ (k + 1) - Newton.iterate F F' x₀ k) := by
  refine ⟨?_, by abel⟩
  have hinv : (F' (Newton.iterate F F' x₀ k)).inverse = (e.symm : E →L[ℝ] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  rw [Newton.iterate_succ, Newton.step, hinv, sub_sub_cancel_left, map_neg, ← he]
  simp

/-- **Theorem 7.1** of [quarteroni2000numerical] (local convergence of Newton's method). Let $E$ be
a finite-dimensional real normed space and $F : E \to E$ with $F(x^*) = 0$. Let $R, C, L > 0$.
Suppose that $F$ has the derivative $F'(x)$ at every $x$ in the ball $B(x^*; R)$, that $F'(x^*)$
is invertible with $\|F'(x^*)^{-1}\| \le C$, and that
$$\|F'(x) - F'(y)\| \le L \|x - y\| \qquad \text{for all } x, y \in B(x^*; R).$$
Then there is $r > 0$ such that for every $x^{(0)} \in B(x^*; r)$ the sequence (7.4) is uniquely
defined, that is, every $F'(x^{(k)})$ is invertible, it converges to $x^*$, and it satisfies
(7.5):
$$\|x^{(k+1)} - x^*\| \le C L \|x^{(k)} - x^*\|^2 \qquad \text{for all } k.$$

The source assumes $F \in C^1$ on a convex open set that contains $x^*$; here $F$ is
differentiable with derivative $F'$ on the ball $B(x^*; R)$, and the Lipschitz condition makes
$F'$ continuous there. The norm of $E$ is any norm, and the operator norm is the induced matrix
norm. The proof takes the radius $r = \min(R, 1/(2CL))$ of the source and specializes
`Newton.forall_norm_iterate_succ_sub_le_of_mem_ball`. -/
theorem theorem_7_1 [FiniteDimensional ℝ E] {F : E → E} {F' : E → E →L[ℝ] E} {xstar : E}
    (hstar : F xstar = 0) (e : E ≃L[ℝ] E) (he : (e : E →L[ℝ] E) = F' xstar) {R C L : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hL : 0 < L) (hCe : ‖(e.symm : E →L[ℝ] E)‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ r > 0, ∀ x₀ ∈ ball xstar r,
      (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = F' (Newton.iterate F F' x₀ k)) ∧
      Tendsto (Newton.iterate F F' x₀) atTop (𝓝 xstar) ∧
      ∀ k, ‖Newton.iterate F F' x₀ (k + 1) - xstar‖
        ≤ C * L * ‖Newton.iterate F F' x₀ k - xstar‖ ^ 2 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨min R (1 / (2 * C * L)), lt_min hR (by positivity), fun x₀ hx₀ => ?_⟩
  have h := fun k => Newton.forall_norm_iterate_succ_sub_le_of_mem_ball hstar e he hCe hF hLip
    hx₀ k
  refine ⟨fun k => ⟨(h k).2.1.choose, (h k).2.1.choose_spec.1⟩, ?_, fun k => (h k).2.2.1⟩
  exact tendsto_of_eventually_norm_sub_succ_le (by norm_num : (1 / 2 : ℝ) < 1)
    (Eventually.of_forall fun k => by linarith [(h k).2.2.2])

/-! ### The Newton–SOR method (7.7)–(7.8) and Exercise 7.1 -/

section NewtonSOR

variable {n : ℕ}

/-- **Section 7.1.2** of [quarteroni2000numerical], one outer step of the $m$-step Newton–SOR
method. Let $F : \mathbb{R}^n \to \mathbb{R}^n$, let $J(x) \in \mathbb{R}^{n \times n}$ stand
for $J_F(x)$, and let $\omega \in \mathbb{R}$. Write $J(x) = D - E - F$ as in (7.6), with $D$
the diagonal part and $-E$, $-F$ the strictly lower and strictly upper parts. The SOR iteration
(7.7) for the linear system $J(x) \delta = -F(x)$, from $\delta_0 = 0$, is
$$\delta_{r+1} = M \delta_r - \omega (D - \omega E)^{-1} F(x), \qquad M = (D - \omega E)^{-1}
  ((1 - \omega) D + \omega F).$$
The outer step maps $x$ to $x + \delta_m$.

The matrix $M$ is `Matrix.sorIterationMatrix (J x) ω`, and $D - \omega E$ is
`diagPart (J x) + ω • strictLower (J x)`. The inner iteration is
`QuarteroniSaccoSaleri.Chapter04.affineStep`. The method is stated on `Fin n → ℝ`, because the
splitting is a matrix operation. Matrix inverses are those of Mathlib, which are $0$ for a
singular matrix. -/
noncomputable def newtonSORStep (F : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (m : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  x + (Chapter04.affineStep (sorIterationMatrix (J x) ω)
    (-(ω • ((diagPart (J x) + ω • strictLower (J x))⁻¹ *ᵥ F x))))^[m] 0

/-- **Section 7.1.2** of [quarteroni2000numerical], the iterates $x^{(k)}$ of the $m$-step
Newton–SOR method from $x^{(0)}$: at every outer step, $m$ sweeps of SOR on the Newton system.
The one-step Newton–SOR method is the case $m = 1$. -/
noncomputable def newtonSORIterate (F : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ) :
    Fin n → ℝ :=
  (newtonSORStep F J ω m)^[k] x₀

/-- Let $A \in \mathbb{R}^{n \times n}$ have a nonsingular diagonal part, and let $\omega \neq 0$.
Then the SOR matrix $(D - \omega E)^{-1}((1 - \omega) D + \omega F)$ of (7.7) is the iteration
operator of the backbone's SOR splitting `Matrix.sorSplitting` of $A$. -/
theorem sorIterationMatrix_eq_sorSplitting_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    sorIterationMatrix A ω = (sorSplitting A h hω).iterationOperator :=
  (sorSplitting_iterationOperator_eq A h hω).symm

/-- Let $B \in \mathbb{R}^{n \times n}$ and $f \in \mathbb{R}^n$. Then $m$ steps of the linear
iteration $\delta \mapsto B \delta + f$ from $\delta = 0$ give
$$\delta_m = (B^{m-1} + \cdots + B + I) f.$$

This is `QuarteroniSaccoSaleri.Chapter04.affineStep` transported to the backbone's
`Stationary.step_iterate_eq_pow_add_sum`. -/
theorem affineStep_iterate_zero (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) (m : ℕ) :
    (Chapter04.affineStep B f)^[m] 0 = (∑ j ∈ Finset.range m, B ^ j) *ᵥ f := by
  apply toLp_injective 2
  rw [Chapter04.toLp_affineStep_iterate, Stationary.step_iterate_eq_pow_add_sum, toLp_zero,
    map_zero, zero_add, sum_mulVec, toLp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_pow, toEuclideanCLM_toLp]

/-- **Exercise 7.1** of [quarteroni2000numerical], which the source cites for (7.8). Let
$F : \mathbb{R}^n \to \mathbb{R}^n$, let $J(x) \in \mathbb{R}^{n \times n}$, let
$\omega \in \mathbb{R}$ and $m \in \mathbb{N}$. The $m$-step Newton–SOR iterates satisfy
$$x^{(k+1)} = x^{(k)} - \omega (M_k^{m-1} + \cdots + M_k + I) (D_k - \omega E_k)^{-1}
  F(x^{(k)}),$$
where $M_k$ is the SOR matrix and $D_k - \omega E_k$ is the lower triangular part of the
splitting of $J(x^{(k)})$.

The identity is algebraic. It needs neither a nonsingular $D_k$ nor $\omega \neq 0$, since the
inverses of Mathlib are $0$ at singular matrices. The matrix $M_k$ is `Matrix.sorIterationMatrix`
of $J(x^{(k)})$ and $\omega$, and $D_k - \omega E_k$ is $D_k + \omega$ times the strictly lower
part of $J(x^{(k)})$. The proof uses `Stationary.step_iterate_eq_pow_add_sum` and
$\delta_0 = 0$. -/
theorem exercise_7_1 (F : (Fin n → ℝ) → Fin n → ℝ) (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ω : ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ) :
    newtonSORIterate F J ω m x₀ (k + 1)
      = newtonSORIterate F J ω m x₀ k
        - ω • ((∑ j ∈ Finset.range m, sorIterationMatrix (J (newtonSORIterate F J ω m x₀ k)) ω ^ j)
          *ᵥ ((diagPart (J (newtonSORIterate F J ω m x₀ k))
            + ω • strictLower (J (newtonSORIterate F J ω m x₀ k)))⁻¹
              *ᵥ F (newtonSORIterate F J ω m x₀ k))) := by
  rw [newtonSORIterate, Function.iterate_succ_apply', ← newtonSORIterate, newtonSORStep,
    affineStep_iterate_zero, mulVec_neg, mulVec_smul, sub_eq_add_neg]

end NewtonSOR

/-! ### Difference approximations of the Jacobian, (7.9)–(7.10) and Property 7.1 -/

section DifferenceJacobian

variable {n : ℕ}

/-- **Equation (7.9)** of [quarteroni2000numerical], the difference Jacobian. Let
$F : \mathbb{R}^n \to \mathbb{R}^n$, $x \in \mathbb{R}^n$ and increments $h \in \mathbb{R}^n$.
The difference Jacobian $J_h$ of $F$ at $x$ has the entries
$$(J_h)_{ij} = \frac{F_i(x + h_j e_j) - F_i(x)}{h_j},$$
and its column $j$, the image of the basis vector $e_j$, is the forward difference
$(F(x + h_j e_j) - F(x)) / h_j$ of $F$ along $e_j$.

The difference Jacobian is `Matrix.differenceJacobian`. An increment $h_j = 0$ gives the column
$0$. -/
theorem equation_7_9 (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (h : Fin n → ℝ) (i j : Fin n) :
    differenceJacobian F x h i j = (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j ∧
      toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) (EuclideanSpace.single j 1)
        = (h j)⁻¹ • (F (x + h j • EuclideanSpace.single j 1) - F x) :=
  ⟨differenceJacobian_apply F x h i j, toEuclideanCLM_differenceJacobian_single F x h j⟩

/-- **Equation (7.10)** of [quarteroni2000numerical], Newton's method with the difference Jacobian:
$$x^{(k+1)} = x^{(k)} - (J_h^{(k)})^{-1} F(x^{(k)}),$$
where $J_h^{(k)}$ is the difference Jacobian (7.9) at $x^{(k)}$ with the increments $h^{(k)}$ of
step $k$.

The inverse is `ContinuousLinearMap.inverse`, whose value at a noninvertible operator is $0$. So
the invertibility of every $J_h^{(k)}$ is a conclusion of Property 7.1, not a hypothesis. -/
noncomputable def equation_7_10 (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → Fin n → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 => equation_7_10 F h x₀ k
      - (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))).inverse
          (F (equation_7_10 F h x₀ k))

/-- The recurrence of (7.10): $x^{(k+1)} = x^{(k)} - (J_h^{(k)})^{-1} F(x^{(k)})$. -/
theorem equation_7_10_succ (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → Fin n → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    equation_7_10 F h x₀ (k + 1) = equation_7_10 F h x₀ k
      - (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))).inverse
          (F (equation_7_10 F h x₀ k)) :=
  rfl

variable {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- Under the hypotheses of Theorem 7.1 on $B(x^*; R)$, the difference Jacobian at a point of
$B(x^*; R/2)$ with increments $0 < |h_j| \le \eta < R/2$ is within $\sqrt{n} (L/2) \eta$ of the
derivative. -/
private theorem norm_differenceJacobian_sub_le {R L : ℝ}
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ ball xstar (R / 2)) {h : Fin n → ℝ} {η : ℝ}
    (hη : η < R / 2)
    (hh : ∀ j, 0 < |h j| ∧ |h j| ≤ η) :
    ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F z h) - F' z‖
      ≤ √(Fintype.card (Fin n) : ℝ) * (L / 2) * η := by
  have hsub : ball z (R / 2) ⊆ ball xstar R := by
    intro y hy
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle y z xstar]
  have hR2 : 0 < R / 2 := lt_of_le_of_lt dist_nonneg (mem_ball.1 hz)
  exact opNorm_toEuclideanCLM_differenceJacobian_sub_le (fun y hy => hF y (hsub hy))
    (fun y hy => hLip y (hsub hy) z (hsub (mem_ball_self hR2)))
    (fun j => ⟨abs_pos.1 (hh j).1, lt_of_le_of_lt (hh j).2 hη⟩) fun j => (hh j).2

/-- Under the hypotheses of Property 7.1, there are $\varepsilon \le R/2$ and $\eta < R/2$ such that
for all increments $0 < |h_j^{(k)}| \le \eta$ and every $x^{(0)} \in B(x^*; \varepsilon)$ the
iterates of (7.10) stay in $B(x^*; \varepsilon)$, every $J_h^{(k)}$ is invertible with
$\|(J_h^{(k)})^{-1}\| \le 2C$, the error halves at every step, and the iterates converge to
$x^*$. -/
private theorem property_7_1_core {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ε ≤ R / 2 ∧ ∃ η > 0, η < R / 2 ∧ ∀ h : ℕ → Fin n → ℝ,
      (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) → ∀ x₀ ∈ ball xstar ε,
      (∀ k, equation_7_10 F h x₀ k ∈ ball xstar ε) ∧
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k)) ∧
        ‖(e'.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 2 * C) ∧
      (∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖ ≤ ‖equation_7_10 F h x₀ k - xstar‖ / 2) ∧
      Tendsto (equation_7_10 F h x₀) atTop (𝓝 xstar) := by
  have hF2 : ∀ x ∈ ball xstar (R / 2), HasFDerivAt F (F' x) x := fun x hx =>
    hF x (ball_subset_ball (by linarith) hx)
  have hLip2 : ∀ x ∈ ball xstar (R / 2), ∀ y ∈ ball xstar (R / 2), ‖F' x - F' y‖ ≤ L * ‖x - y‖ :=
    fun x hx y hy =>
      hLip x (ball_subset_ball (by linarith) hx) y (ball_subset_ball (by linarith) hy)
  obtain ⟨δ, hδ, hδR, η₀, hη₀, hmain⟩ :=
    Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le_of_mem hstar e he
      (by positivity : 0 < R / 2) hF2 hLip2
  set c : ℝ := √(Fintype.card (Fin n) : ℝ) * (L / 2) with hc
  set η : ℝ := min (R / 4) (η₀ / (|c| + 1)) with hηdef
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηR : η < R / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηc : c * η ≤ η₀ := by
    calc c * η ≤ |c| * η := mul_le_mul_of_nonneg_right (le_abs_self c) hηpos.le
      _ ≤ |c| * (η₀ / (|c| + 1)) := by gcongr; exact min_le_right _ _
      _ ≤ η₀ := by
          rw [mul_div_assoc']
          exact (div_le_iff₀ (by positivity)).2 (by nlinarith [abs_nonneg c])
  refine ⟨δ, hδ, hδR, η, hηpos, hηR, fun h hh x₀ hx₀ => ?_⟩
  have hB : ∀ k, ∀ z ∈ ball xstar δ,
      ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F z (h k)) - F' z‖ ≤ η₀ := fun k z hz =>
    (norm_differenceJacobian_sub_le hF hLip (ball_subset_ball hδR hz) hηR (hh k)).trans hηc
  obtain ⟨hmem, hinv, hhalf, hlim⟩ := hmain (fun k z => toEuclideanCLM (𝕜 := ℝ)
    (differenceJacobian F z (h k))) (equation_7_10 F h x₀) hx₀ hB (equation_7_10_succ F h x₀)
  refine ⟨hmem, fun k => ?_, hhalf, hlim⟩
  obtain ⟨e', he', hn⟩ := hinv k
  exact ⟨e', he', hn.trans (by linarith)⟩

/-- **Property 7.1** of [quarteroni2000numerical], first part. Let
$F : \mathbb{R}^n \to \mathbb{R}^n$ with $F(x^*) = 0$, and let $R > 0$. Suppose that $F$ has the
derivative $F'(x)$ at every $x \in B(x^*; R)$, that $F'(x^*)$ is invertible with
$\|F'(x^*)^{-1}\| \le C$, and that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for $x, y \in B(x^*; R)$.
Then there are $\varepsilon > 0$ and $\eta > 0$ with the following property. For every sequence
of increments with $0 < |h_j^{(k)}| \le \eta$ for all $k$ and $j$, and every
$x^{(0)} \in B(x^*; \varepsilon)$, the sequence (7.10):

* is well defined, that is, every $J_h^{(k)}$ is invertible;
* satisfies $\|x^{(k+1)} - x^*\| \le \|x^{(k)} - x^*\| / 2$ for all $k$;
* converges to $x^*$, with order $1$.

**Reading.** The source states the property in the norm $\|\cdot\|_1$. Here the norm is the
Euclidean norm, where the error of the difference Jacobian carries a factor $\sqrt{n}$; this
changes only the constants.

The source states the result without proof. The order is `ConvergesWithOrder`. The proof
specializes `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le` with the error
bound `Matrix.opNorm_toEuclideanCLM_differenceJacobian_sub_le` of the difference Jacobian. -/
theorem property_7_1 {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε,
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))) ∧
      (∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖ ≤ ‖equation_7_10 F h x₀ k - xstar‖ / 2) ∧
      Tendsto (equation_7_10 F h x₀) atTop (𝓝 xstar) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 1 := by
  obtain ⟨ε, hε, -, η, hη, -, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨ε, hε, η, hη, fun h hh x₀ hx₀ => ?_⟩
  obtain ⟨-, hinv, hhalf, hlim⟩ := hcore h hh x₀ hx₀
  refine ⟨fun k => ⟨(hinv k).choose, (hinv k).choose_spec.1⟩, hhalf, hlim, ?_⟩
  exact convergesWithOrder_one_of_eventually_norm_sub_succ_le (C := 1 / 2) (by norm_num)
    (by norm_num) (Eventually.of_forall fun k => by linarith [hhalf k])

/-- **Property 7.1** of [quarteroni2000numerical], second part. Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter07.property_7_1`, there are $\varepsilon > 0$ and $\eta > 0$ with
the following property. For every sequence of increments with $0 < |h_j^{(k)}| \le \eta$, every
$x^{(0)} \in B(x^*; \varepsilon)$ and every $C'$ with $|h_j^{(k)}| \le C' \|x^{(k)} - x^*\|$ for
all $k$ and $j$, there is $K$ with
$$\|x^{(k+1)} - x^*\| \le K \|x^{(k)} - x^*\|^2 \qquad \text{for all } k,$$
and the sequence (7.10) converges to $x^*$ with order $2$.

**Reading.** The norm is the Euclidean norm instead of $\|\cdot\|_1$, as in the first part.

The proof gives $K = 2C (\sqrt{n} (L/2) C' + L/2)$. It specializes
`Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul` with the error
$\sqrt{n} (L/2) C' \|x^{(k)} - x^*\|$ of the derivative. -/
theorem property_7_1_quadratic {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε, ∀ C' : ℝ, (∀ k j, |h k j| ≤ C' * ‖equation_7_10 F h x₀ k - xstar‖) →
      (∃ K, ∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖
        ≤ K * ‖equation_7_10 F h x₀ k - xstar‖ ^ 2) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 2 := by
  obtain ⟨ε, hε, hεR, η, hη, hηR, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨ε, hε, η, hη, fun h hh x₀ hx₀ C' hC' => ?_⟩
  obtain ⟨hmem, hinv, -, hlim⟩ := hcore h hh x₀ hx₀
  set c : ℝ := √(Fintype.card (Fin n) : ℝ) * (L / 2) with hc
  have hx2 : ∀ k, equation_7_10 F h x₀ k ∈ ball xstar (R / 2) := fun k =>
    ball_subset_ball hεR (hmem k)
  have hxR : ∀ k, equation_7_10 F h x₀ k ∈ ball xstar R := fun k =>
    ball_subset_ball (by linarith) (hx2 k)
  -- the derivative error is first order in the error
  have hCk : ∀ k, ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))
      - F' (equation_7_10 F h x₀ k)‖ ≤ |c| * |C'| * ‖equation_7_10 F h x₀ k - xstar‖ := by
    intro k
    set η' : ℝ := min η (|C'| * ‖equation_7_10 F h x₀ k - xstar‖) with hη'
    have hη'R : η' < R / 2 := lt_of_le_of_lt (min_le_left _ _) hηR
    have hhk : ∀ j, 0 < |h k j| ∧ |h k j| ≤ η' := fun j =>
      ⟨(hh k j).1, le_min (hh k j).2 ((hC' k j).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C') (norm_nonneg _)))⟩
    have hη'0 : 0 ≤ η' := le_min hη.le (by positivity)
    calc ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))
          - F' (equation_7_10 F h x₀ k)‖
        ≤ c * η' := norm_differenceJacobian_sub_le hF hLip (hx2 k) hη'R hhk
      _ ≤ |c| * η' := mul_le_mul_of_nonneg_right (le_abs_self c) hη'0
      _ ≤ |c| * (|C'| * ‖equation_7_10 F h x₀ k - xstar‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg c)
      _ = |c| * |C'| * ‖equation_7_10 F h x₀ k - xstar‖ := by ring
  have hK := fun k => Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul hstar hF hLip hxR hinv
    (equation_7_10_succ F h x₀) hCk k
  refine ⟨⟨2 * C * (|c| * |C'| + L / 2), hK⟩, hlim, max (2 * C * (|c| * |C'| + L / 2)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), Eventually.of_forall fun k => ?_⟩
  rw [Real.rpow_two]
  exact (hK k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- **Property 7.1** of [quarteroni2000numerical], the "or, equivalently" clause. Under the
hypotheses of `QuarteroniSaccoSaleri.Chapter07.property_7_1`, there are $\varepsilon > 0$ and
$\eta > 0$ with the following property. For every sequence of increments with
$0 < |h_j^{(k)}| \le \eta$, every $x^{(0)} \in B(x^*; \varepsilon)$ and every $c$ with
$|h_j^{(k)}| \le c \|F(x^{(k)})\|$ for all $k$ and $j$, there is $K$ with
$\|x^{(k+1)} - x^*\| \le K \|x^{(k)} - x^*\|^2$ for all $k$, and the sequence (7.10) converges
to $x^*$ with order $2$.

**Reading.** The source says that the condition on the increments can, equivalently, be stated
with $\|F(x^{(k)})\|$. Only the direction that the conclusion needs is proved: by the mean value
inequality, $F$ is Lipschitz on $B(x^*; R)$ with constant $\|F'(x^*)\| + |L| R$, and
$F(x^*) = 0$, so $\|F(x^{(k)})\| \le (\|F'(x^*)\| + |L| R) \|x^{(k)} - x^*\|$.

The second part then applies with $C' = c (\|F'(x^*)\| + |L| R)$. The constant is written with
$|L|$ because no sign of $L$ is assumed. -/
theorem property_7_1_residual {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε, ∀ c : ℝ, (∀ k j, |h k j| ≤ c * ‖F (equation_7_10 F h x₀ k)‖) →
      (∃ K, ∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖
        ≤ K * ‖equation_7_10 F h x₀ k - xstar‖ ^ 2) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 2 := by
  obtain ⟨ε, hε, η, hη, hquad⟩ := property_7_1_quadratic hstar e he hR hCe hF hLip
  -- the iterates stay in `B(x*; ε) ⊆ B(x*; R)`
  obtain ⟨ε', hε', hε'R, η', hη', -, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨min ε ε', lt_min hε hε', min η η', lt_min hη hη', fun h hh x₀ hx₀ c hc => ?_⟩
  have hhη : ∀ k j, 0 < |h k j| ∧ |h k j| ≤ η := fun k j =>
    ⟨(hh k j).1, (hh k j).2.trans (min_le_left _ _)⟩
  have hhη' : ∀ k j, 0 < |h k j| ∧ |h k j| ≤ η' := fun k j =>
    ⟨(hh k j).1, (hh k j).2.trans (min_le_right _ _)⟩
  obtain ⟨hmem, -, -, -⟩ := hcore h hhη' x₀ (ball_subset_ball (min_le_right _ _) hx₀)
  -- `F` is Lipschitz on the ball with constant `‖F'(x*)‖ + |L| R`
  have hFlip : ∀ z ∈ ball xstar R, ‖F z‖ ≤ (‖F' xstar‖ + |L| * R) * ‖z - xstar‖ := by
    intro z hz
    have hbound : ∀ y ∈ ball xstar R, ‖F' y‖ ≤ ‖F' xstar‖ + |L| * R := fun y hy => by
      have h1 := hLip y hy xstar (mem_ball_self hR)
      have h2 : ‖y - xstar‖ ≤ R := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
      have h3 : L * ‖y - xstar‖ ≤ |L| * R :=
        (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg L))
      calc ‖F' y‖ = ‖F' xstar + (F' y - F' xstar)‖ := by congr 1; abel
        _ ≤ ‖F' xstar‖ + ‖F' y - F' xstar‖ := norm_add_le _ _
        _ ≤ ‖F' xstar‖ + |L| * R := by linarith
    have := (convex_ball xstar R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hF y hy).hasFDerivWithinAt) hbound (mem_ball_self hR) hz
    rwa [hstar, sub_zero] at this
  refine hquad h hhη x₀ (ball_subset_ball (min_le_left _ _) hx₀) (c * (‖F' xstar‖ + |L| * R))
    fun k j => ?_
  have hz := hFlip _ (ball_subset_ball (by linarith) (hmem k))
  have hc0 : 0 ≤ c := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := (hh k j).1
    have h2 := hc k j
    have h3 := norm_nonneg (F (equation_7_10 F h x₀ k))
    nlinarith
  calc |h k j| ≤ c * ‖F (equation_7_10 F h x₀ k)‖ := hc k j
    _ ≤ c * ((‖F' xstar‖ + |L| * R) * ‖equation_7_10 F h x₀ k - xstar‖) :=
        mul_le_mul_of_nonneg_left hz hc0
    _ = c * (‖F' xstar‖ + |L| * R) * ‖equation_7_10 F h x₀ k - xstar‖ := by ring

end DifferenceJacobian

/-! ### Broyden's method (7.11)–(7.14) -/

section Broyden

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Equation (7.11)** of [quarteroni2000numerical]. One step of Broyden's method solves
$Q_k \delta x^{(k+1)} = -F(x^{(k)})$ and sets $x^{(k+1)} = x^{(k)} + \delta x^{(k+1)}$. Let $H$
be a real inner product space and $F : H \to H$, and let $(x^{(k)}, Q_k)$ be a state of
Broyden's method with $Q_k$ invertible. Then the next iterate satisfies
$$Q_k (x^{(k+1)} - x^{(k)}) = -F(x^{(k)}), \qquad x^{(k+1)} = x^{(k)} + (x^{(k+1)} - x^{(k)}).$$

The state is `Broyden.State` and the step is `Broyden.step`. The proof is
`Broyden.apply_step_x_sub`. -/
theorem equation_7_11 (F : H → H) (σ : Broyden.State H) (e : H ≃L[ℝ] H)
    (he : (e : H →L[ℝ] H) = σ.Q) :
    σ.Q ((Broyden.step F σ).x - σ.x) = -F σ.x ∧
      (Broyden.step F σ).x = σ.x + ((Broyden.step F σ).x - σ.x) :=
  ⟨Broyden.apply_step_x_sub F σ e he, by abel⟩

/-- **Equation (7.12)** of [quarteroni2000numerical] with $j = 1$, the secant condition. Let $H$ be
a real inner product space and $F : H \to H$. If a step of Broyden's method from
$(x^{(k)}, Q_k)$ gives $x^{(k+1)} \neq x^{(k)}$, then the updated matrix satisfies
$$Q_{k+1} (x^{(k+1)} - x^{(k)}) = F(x^{(k+1)}) - F(x^{(k)}).$$

The proof is `Broyden.step_Q_apply_sub`, from `Broyden.update_apply_self`. -/
theorem equation_7_12 (F : H → H) (σ : Broyden.State H) (h : (Broyden.step F σ).x ≠ σ.x) :
    (Broyden.step F σ).Q ((Broyden.step F σ).x - σ.x) = F (Broyden.step F σ).x - F σ.x :=
  Broyden.step_Q_apply_sub F σ h

/-- **Equation (7.14)** of [quarteroni2000numerical], Broyden's update in matrix form. Let
$Q \in \mathbb{R}^{n \times n}$ and $s, y \in \mathbb{R}^n$. Then
$$\mathrm{broydenUpdate}(Q, s, y) = Q + \frac{(y - Q s) s^T}{s^T s},$$
and on $\mathbb{R}^n$ with the Euclidean inner product this matrix is the operator update
`Broyden.update` of the backbone.

In the notation of the source, $Q_k = \mathrm{broydenUpdate}(Q_{k-1}, \delta x^{(k)}, b^{(k)})$.
The matrix update is `Matrix.broydenUpdate`. If $s = 0$, the coefficient $1 / (s^T s)$ is $0$
and the update returns $Q$. The second part is `Matrix.toEuclideanCLM_broydenUpdate`. -/
theorem equation_7_14 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    broydenUpdate Q s y = Q + (1 / (s ⬝ᵥ s)) • vecMulVec (y - Q *ᵥ s) s ∧
      toEuclideanCLM (𝕜 := ℝ) (broydenUpdate Q s y)
        = Broyden.update (toEuclideanCLM (𝕜 := ℝ) Q) (toLp 2 s) (toLp 2 y) :=
  ⟨rfl, toEuclideanCLM_broydenUpdate Q s y⟩

/-- **Section 7.1.4** of [quarteroni2000numerical], the characterization behind (7.14). Let $H$ be a
real inner product space, let $Q : H \to H$ be a continuous linear map, let $s \neq 0$ and
$b \in H$, and let $Q_+$ be Broyden's update of $Q$ with $s = \delta x^{(k)}$ and $b = b^{(k)}$.
Then:

* $Q_+ s = b$, the secant condition (7.12) with $j = 1$;
* $(Q_+ - Q) v = 0$ for every $v$ orthogonal to $s$;
* every continuous linear map $Q'$ with $Q' s = b$ and $(Q' - Q) v = 0$ for every $v$ orthogonal
  to $s$ is equal to $Q_+$.

The second property gives the smallest possible value of the quantity that the source minimizes.
Uniqueness holds because an operator is determined by its values on the span of $s$ and on the
orthogonal complement of $s$. The proof uses `Broyden.update_apply_self` and
`Broyden.update_sub_apply_of_inner_eq_zero`. -/
theorem broydenUpdate_leastChange (Q : H →L[ℝ] H) {s : H} (hs : s ≠ 0) (b : H) :
    Broyden.update Q s b s = b ∧
      (∀ v, ⟪s, v⟫_ℝ = 0 → (Broyden.update Q s b - Q) v = 0) ∧
      ∀ Q' : H →L[ℝ] H, Q' s = b → (∀ v, ⟪s, v⟫_ℝ = 0 → (Q' - Q) v = 0) →
        Q' = Broyden.update Q s b := by
  refine ⟨Broyden.update_apply_self Q hs b, fun v hv =>
    Broyden.update_sub_apply_of_inner_eq_zero Q s b hv, fun Q' hQ's hQ' => ?_⟩
  ext v
  set α : ℝ := ⟪s, v⟫_ℝ / ⟪s, s⟫_ℝ with hα
  have hss : ⟪s, s⟫_ℝ ≠ 0 := inner_self_ne_zero.2 hs
  have hw : ⟪s, v - α • s⟫_ℝ = 0 := by
    rw [inner_sub_right, inner_smul_right, hα, div_mul_cancel₀ _ hss, sub_self]
  have hv : v = α • s + (v - α • s) := by abel
  have h1 : Q' (v - α • s) = Q (v - α • s) := by
    have := hQ' _ hw
    rwa [_root_.sub_apply, sub_eq_zero] at this
  have h2 : Broyden.update Q s b (v - α • s) = Q (v - α • s) := by
    have := Broyden.update_sub_apply_of_inner_eq_zero Q s b hw
    rwa [_root_.sub_apply, sub_eq_zero] at this
  rw [hv, map_add, map_add, map_smul, map_smul, hQ's, Broyden.update_apply_self Q hs b, h1, h2]

/-- **Property 7.2** of [quarteroni2000numerical] (local superlinear convergence of Broyden's
method). Let $F : \mathbb{R}^n \to \mathbb{R}^n$ with $F(x^*) = 0$, and let $R, C, L > 0$.
Suppose that $F$ has the derivative $F'(x)$ at every $x \in B(x^*; R)$, that $F'(x^*)$ is
invertible with $\|F'(x^*)^{-1}\| \le C$, and that $\|F'(x) - F'(y)\| \le L \|x - y\|$ for
$x, y \in B(x^*; R)$. Then there are $\varepsilon > 0$ and $\gamma > 0$ such that for every
$x^{(0)}$ with $\|x^{(0)} - x^*\| \le \varepsilon$ and every $Q_0$ with
$\|Q_0 - F'(x^*)\| \le \gamma$, Broyden's method (7.11)–(7.14) from $(x^{(0)}, Q_0)$:

* is well defined, that is, every $Q_k$ is invertible;
* satisfies $\|x^{(k)} - x^*\| \le \varepsilon / 2^k$ for all $k$;
* converges to $x^*$;
* converges superlinearly, (7.15): there is a sequence $c_k \to 0$ with
  $\|x^{(k+1)} - x^*\| \le c_k \|x^{(k)} - x^*\|$ for all $k$.

**Reading.** The source states the property without proof. Here it has the hypotheses of Theorem
7.1 on $\mathbb{R}^n$, with the Jacobian read as the matrix of $F'$.

The proof gives $c_k = 4C (\eta_k + L \varepsilon / 2^k)$, where $\eta_k = \|(Q_k - F'(x^*))
\delta x^{(k+1)}\| / \|\delta x^{(k+1)}\| \to 0$ is the Dennis–Moré quotient. It is the
Dennis–Moré theory, Theorem 8.2.2 of Dennis and Schnabel, as the backbone's
`Broyden.exists_superlinear`. -/
theorem property_7_2 {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {xstar : EuclideanSpace ℝ (Fin n)} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) {R C L : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hL : 0 < L)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ γ > 0, ∀ (x₀ : EuclideanSpace ℝ (Fin n))
      (Q₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ‖x₀ - xstar‖ ≤ ε → ‖Q₀ - F' xstar‖ ≤ γ →
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
          (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            = (Broyden.iterate F x₀ Q₀ k).Q) ∧
        (∀ k, ‖(Broyden.iterate F x₀ Q₀ k).x - xstar‖ ≤ ε / 2 ^ k) ∧
        Tendsto (fun k => (Broyden.iterate F x₀ Q₀ k).x) atTop (𝓝 xstar) ∧
        ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
          ∀ k, ‖(Broyden.iterate F x₀ Q₀ (k + 1)).x - xstar‖
            ≤ c k * ‖(Broyden.iterate F x₀ Q₀ k).x - xstar‖ := by
  set J : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun w => (toEuclideanCLM (𝕜 := ℝ)).symm (F' w) with hJ
  have hJw : ∀ w, toEuclideanCLM (𝕜 := ℝ) (J w) = F' w := fun w => by
    rw [hJ, StarAlgEquiv.apply_symm_apply]
  have h : Broyden.LipschitzJacobianRoot F J (ball xstar R) xstar L :=
    { convex := convex_ball xstar R
      hasFDerivAt := fun w hw => by rw [hJw]; exact hF w hw
      root := hstar
      mem := mem_ball_self hR
      lipschitz := fun w hw => by rw [hJw, hJw]; exact hLip w hw xstar (mem_ball_self hR)
      nonneg := hL.le }
  obtain ⟨ε, hε, γ, hγ, H⟩ := Broyden.exists_superlinear h e (by rw [hJw]; exact he) hCe hC hR
    subset_rfl
  refine ⟨ε, hε, γ, hγ, fun x₀ Q₀ hx₀ hQ₀ => H x₀ Q₀ hx₀ ?_⟩
  rwa [hJw]

end Broyden

/-! ### Fixed-point methods: Definition 7.1, Theorem 7.2, Property 7.3 -/

/-- **Definition 7.1** of [quarteroni2000numerical]. Let $E$ be a real normed space. A map
$G : E \to E$ is **contractive** on a set $D_0 \subseteq E$ if there is a constant $\alpha < 1$
with
$$\|G(x) - G(y)\| \le \alpha \|x - y\| \qquad \text{for all } x, y \in D_0.$$

The "suitable vector norm" of the source is the norm of $E$, so a different norm is a different
space $E$. As in the source, $\alpha \ge 0$ is not required. A negative $\alpha$ forces $D_0$ to
have at most one point, and is the same as $\alpha = 0$, by
`QuarteroniSaccoSaleri.Chapter07.definition_7_1_iff`. -/
def definition_7_1 (G : E → E) (D₀ : Set E) : Prop :=
  ∃ α < 1, ∀ x ∈ D₀, ∀ y ∈ D₀, ‖G x - G y‖ ≤ α * ‖x - y‖

omit [NormedSpace ℝ E] in
/-- A map $G$ is contractive on $D_0$ in the sense of Definition 7.1 if and only if it is Lipschitz
on $D_0$, in the sense of Mathlib's `LipschitzOnWith`, with a constant $K \in [0, 1)$. A
negative constant $\alpha$ is replaced by $\max(\alpha, 0)$. -/
theorem definition_7_1_iff (G : E → E) (D₀ : Set E) :
    definition_7_1 G D₀ ↔ ∃ K : NNReal, K < 1 ∧ LipschitzOnWith K G D₀ := by
  constructor
  · rintro ⟨α, hα, hG⟩
    refine ⟨(max α 0).toNNReal, ?_, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_max_right _ _), NNReal.coe_one]
      exact max_lt hα one_pos
    · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact (hG x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rintro ⟨K, hK, hG⟩
    refine ⟨K, by exact_mod_cast hK, fun x hx y hy => ?_⟩
    have := hG.dist_le_mul x hx y hy
    rwa [dist_eq_norm, dist_eq_norm] at this

omit [NormedSpace ℝ E] in
/-- **Theorem 7.2** of [quarteroni2000numerical] (contraction-mapping theorem). Let $E$ be a
complete normed space, let $D_0 \subseteq E$ be closed and nonempty, and let $G : E \to E$ be
contractive on $D_0$ with $G(x) \in D_0$ for all $x \in D_0$. Then $G$ has exactly one fixed
point in $D_0$.

**Correction.** The source omits the hypothesis $D_0 \neq \emptyset$. The empty set satisfies
all other hypotheses and has no fixed point.

The source states the theorem on $\mathbb{R}^n$, which is complete. The proof specializes
`exists_unique_fixedPoint_of_mapsTo`. -/
theorem theorem_7_2 [CompleteSpace E] {G : E → E} {D₀ : Set E} (hG : definition_7_1 G D₀)
    (hD : IsClosed D₀) (hne : D₀.Nonempty) (hmaps : MapsTo G D₀ D₀) :
    ∃! x, x ∈ D₀ ∧ G x = x := by
  obtain ⟨α, hα, hG⟩ := hG
  refine exists_unique_fixedPoint_of_mapsTo hD hne hmaps (K := max α 0) (le_max_right _ _)
    (max_lt hα one_pos) fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact (hG x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

omit [NormedSpace ℝ E] in
/-- **Theorem 7.2** of [quarteroni2000numerical], the content of the existence proof. Let $E$ be a
complete normed space, let $D_0 \subseteq E$ be closed, let $0 \le \alpha < 1$, and let
$G : E \to E$ map $D_0$ into itself with $\|G(x) - G(y)\| \le \alpha \|x - y\|$ for all
$x, y \in D_0$. Let $x^* \in D_0$ be a fixed point of $G$, and let $x^{(0)} \in D_0$. Then the
fixed-point iterates (7.17) $x^{(k)} = G^k(x^{(0)})$ satisfy the a priori estimate
$$\|x^{(k)} - x^*\| \le \frac{\alpha^k}{1 - \alpha} \|x^{(1)} - x^{(0)}\| \qquad \text{for all }
  k,$$
and converge to $x^*$.

The estimate is the limit, as $p \to \infty$, of the Cauchy estimate $\|x^{(k+p)} - x^{(k)}\|
\le \alpha^k / (1 - \alpha) \, \|x^{(1)} - x^{(0)}\|$ of the proof in the source. The proof
specializes `dist_iterate_le_of_mapsTo`. -/
theorem theorem_7_2_tendsto [CompleteSpace E] {G : E → E} {D₀ : Set E} {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1) (hG : ∀ x ∈ D₀, ∀ y ∈ D₀, ‖G x - G y‖ ≤ α * ‖x - y‖) (hD : IsClosed D₀)
    (hmaps : MapsTo G D₀ D₀) {xstar : E} (hstar : xstar ∈ D₀) (hfix : G xstar = xstar) {x₀ : E}
    (hx₀ : x₀ ∈ D₀) :
    (∀ k, ‖G^[k] x₀ - xstar‖ ≤ α ^ k / (1 - α) * ‖G x₀ - x₀‖) ∧
      Tendsto (fun k => G^[k] x₀) atTop (𝓝 xstar) := by
  have hG' : ∀ x ∈ D₀, ∀ y ∈ D₀, dist (G x) (G y) ≤ α * dist x y := fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm]; exact hG x hx y hy
  have hbound : ∀ k, ‖G^[k] x₀ - xstar‖ ≤ α ^ k / (1 - α) * ‖G x₀ - x₀‖ := fun k => by
    have := dist_iterate_le_of_mapsTo hD hmaps hα0 hα hG' hstar hfix hx₀ k
    rwa [dist_eq_norm, dist_eq_norm] at this
  refine ⟨hbound, ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound ?_)
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα).div_const (1 - α)).mul_const
    ‖G x₀ - x₀‖
  simpa using h

section Jacobian

variable {n : ℕ}

/-- **Section 7.1** of [quarteroni2000numerical], the **Jacobian matrix** $J_F(x)$ of
$F : \mathbb{R}^n \to \mathbb{R}^n$ at $x$, with entries
$$(J_F(x))_{ij} = \frac{\partial F_i}{\partial x_j}(x).$$

It is defined as the matrix of the Fréchet derivative `fderiv ℝ F x` in the standard basis of
`EuclideanSpace ℝ (Fin n)`. If $F$ is not differentiable at $x$, the derivative is $0$ and so is
the matrix. -/
noncomputable def jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ F x : _ →ₗ[ℝ] _)

/-- The entries of the Jacobian matrix are the partial derivatives: $(J_F(x))_{ij}$ is the component
$i$ of the derivative of $F$ at $x$ in the direction of the basis vector $e_j$. -/
theorem jacobianMatrix_apply (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    jacobianMatrix F x i j = fderiv ℝ F x (EuclideanSpace.single j 1) i := by
  rw [jacobianMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  rfl

/-- The Jacobian matrix $J_F(x)$ acts on $\mathbb{R}^n$ as the derivative `fderiv ℝ F x`, as a
linear map. -/
theorem toEuclideanLin_jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (jacobianMatrix F x) = (fderiv ℝ F x : _ →ₗ[ℝ] _) := by
  rw [jacobianMatrix, toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]

/-- The Jacobian matrix $J_F(x)$ acts on $\mathbb{R}^n$ as the derivative `fderiv ℝ F x`, as a
continuous linear map. -/
theorem toEuclideanCLM_jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanCLM (𝕜 := ℝ) (jacobianMatrix F x) = fderiv ℝ F x := by
  apply ContinuousLinearMap.coe_injective
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_jacobianMatrix]

/-- **Property 7.3** of [quarteroni2000numerical]. Let $D \subseteq \mathbb{R}^n$, and let
$G : \mathbb{R}^n \to \mathbb{R}^n$ have a fixed point $x^*$ in the interior of $D$. Suppose
that $G$ is continuously differentiable in a neighbourhood of $x^*$ and that
$\rho(J_G(x^*)) < 1$. Then there is a neighbourhood $S \subseteq D$ of $x^*$ such that for every
$x^{(0)} \in S$ the iterates $x^{(k)} = G^k(x^{(0)})$ of (7.17) all lie in $D$ and converge to
$x^*$.

The source cites Ortega and Rheinboldt for the proof. In finite dimension, $\rho(J) < 1$ gives
$\|J^m\| < 1$ for some $m$, by
`Matrix.exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one`, and
Ostrowski's theorem for $G^m$ gives the result, by
`tendsto_iterate_of_exists_norm_pow_fderiv_lt_one` and
`exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one`. The spectral radius is
`Matrix.complexSpectralRadius`. -/
theorem property_7_3 {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D : Set (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hint : xstar ∈ interior D) (hfix : G xstar = xstar) (hG : ContDiffAt ℝ 1 G xstar)
    (hρ : complexSpectralRadius (jacobianMatrix G xstar) < 1) :
    ∃ S ∈ 𝓝 xstar, S ⊆ D ∧ ∀ x₀ ∈ S,
      (∀ k, G^[k] x₀ ∈ D) ∧ Tendsto (fun k => G^[k] x₀) atTop (𝓝 xstar) := by
  have hd : HasFDerivAt G (fderiv ℝ G xstar) xstar :=
    (hG.differentiableAt one_ne_zero).hasFDerivAt
  have hpow : ∃ m : ℕ, ‖fderiv ℝ G xstar ^ m‖ < 1 :=
    exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one hρ
      (toEuclideanLin_jacobianMatrix G xstar).symm
  obtain ⟨S, hS, hSD, hSin⟩ := exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one hfix
    hd hpow (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_exists_norm_pow_fderiv_lt_one hfix hd hpow
  refine ⟨S ∩ ball xstar δ, inter_mem hS (ball_mem_nhds xstar hδ), inter_subset_left.trans hSD,
    fun x₀ hx₀ => ⟨hSin x₀ hx₀.1, hconv x₀ hx₀.2⟩⟩

/-- **Property 7.3** of [quarteroni2000numerical], the remark after it. Let
$D \subseteq \mathbb{R}^n$, and let $G : \mathbb{R}^n \to \mathbb{R}^n$ have a fixed point $x^*$
in the interior of $D$ and be differentiable at $x^*$. Let $\|J_G(x^*)\| < q < 1$ in the
spectral norm. Then there is a neighbourhood $S \subseteq D$ of $x^*$ such that for every
$x^{(0)} \in S$ and every $k$, $x^{(k)} = G^k(x^{(0)}) \in D$ and
$$\|x^{(k)} - x^*\| \le q^k \|x^{(0)} - x^*\|.$$

The source says that it suffices that $\|J_G(x^*)\| < 1$ in some induced matrix norm; here the
norm is the spectral norm, the norm of `Matrix.toEuclideanCLM` applied to $J_G(x^*)$. The proof
specializes `exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one`, the case $m = 1$ of
Ostrowski's theorem. -/
theorem property_7_3_norm {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D : Set (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hint : xstar ∈ interior D) (hfix : G xstar = xstar) (hG : DifferentiableAt ℝ G xstar)
    {q : ℝ} (hq : ‖toEuclideanCLM (𝕜 := ℝ) (jacobianMatrix G xstar)‖ < q) (hq1 : q < 1) :
    ∃ S ∈ 𝓝 xstar, S ⊆ D ∧ ∀ x₀ ∈ S, ∀ k, G^[k] x₀ ∈ D ∧
      ‖G^[k] x₀ - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖ := by
  rw [toEuclideanCLM_jacobianMatrix] at hq
  obtain ⟨ρ, hρ, hρD⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨δ, hδ, hball⟩ :=
    exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hfix hG.hasFDerivAt hq hq1
  refine ⟨ball xstar (min ρ δ), ball_mem_nhds xstar (lt_min hρ hδ),
    (ball_subset_ball (min_le_left _ _)).trans hρD, fun x₀ hx₀ k => ?_⟩
  have h := hball x₀ (ball_subset_ball (min_le_right _ _) hx₀) k
  refine ⟨hρD ?_, h.2⟩
  have hk : ‖G^[k] x₀ - xstar‖ ≤ ‖x₀ - xstar‖ := by
    calc ‖G^[k] x₀ - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖ := h.2
      _ ≤ 1 * ‖x₀ - xstar‖ := by
          gcongr
          exact pow_le_one₀ (le_trans (norm_nonneg _) hq.le) hq1.le
      _ = ‖x₀ - xstar‖ := one_mul _
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hk (lt_of_lt_of_le (mem_ball.1 hx₀) (min_le_left _ _))

end Jacobian

/-! ### Example 7.4 and Remark 7.1 -/

section Example74

/-- **Example 7.4** of [quarteroni2000numerical], the system $F(x) = 0$ with
$$F(x) = (x_1^2 + x_2^2 - 1, \ 2 x_1 + x_2 - 1).$$

The components $x_1, x_2$ of the source are `x 0` and `x 1`. -/
noncomputable def example_7_4_F (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[x 0 ^ 2 + x 1 ^ 2 - 1, 2 * x 0 + x 1 - 1]

/-- **Example 7.4** of [quarteroni2000numerical], the first iteration function of (7.18),
$$G_1(x) = \left( \frac{1 - x_2}{2}, \ \sqrt{1 - x_1^2} \right).$$

The square root is `Real.sqrt`, whose value at a negative number is $0$. -/
noncomputable def example_7_4_G₁ (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(1 - x 1) / 2, √(1 - x 0 ^ 2)]

/-- **Example 7.4** of [quarteroni2000numerical], the second iteration function of (7.18),
$$G_2(x) = \left( \frac{1 - x_2}{2}, \ -\sqrt{1 - x_1^2} \right).$$

The square root is `Real.sqrt`, whose value at a negative number is $0$. -/
noncomputable def example_7_4_G₂ (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(1 - x 1) / 2, -√(1 - x 0 ^ 2)]

/-- **Example 7.4** of [quarteroni2000numerical], the algebraic part. The points $x_1^* = (0, 1)$
and $x_2^* = (4/5, -3/5)$ solve the system $F(x) = 0$, and they are fixed points of $G_1$ and
$G_2$ respectively: $G_1(x_1^*) = x_1^*$ and $G_2(x_2^*) = x_2^*$. -/
theorem example_7_4_fixedPoint :
    example_7_4_F !₂[0, 1] = 0 ∧ example_7_4_F !₂[4 / 5, -3 / 5] = 0 ∧
      example_7_4_G₁ !₂[0, 1] = !₂[0, 1] ∧
      example_7_4_G₂ !₂[4 / 5, -3 / 5] = !₂[4 / 5, -3 / 5] := by
  have h35 : √(1 - (4 / 5 : ℝ) ^ 2) = 3 / 5 := by
    rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [example_7_4_F, example_7_4_G₁, example_7_4_G₂, h35] <;> norm_num

/-- The Jacobian matrix of a map $\mathbb{R}^2 \to \mathbb{R}^2$ has as rows the derivatives of its
two scalar components, applied to the two basis vectors. -/
private theorem jacobianMatrix_pair {g₀ g₁ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {L₀ L₁ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (h₀ : HasFDerivAt g₀ L₀ p) (h₁ : HasFDerivAt g₁ L₁ p) :
    jacobianMatrix (fun x => !₂[g₀ x, g₁ x]) p
      = !![L₀ (EuclideanSpace.single 0 1), L₀ (EuclideanSpace.single 1 1);
           L₁ (EuclideanSpace.single 0 1), L₁ (EuclideanSpace.single 1 1)] := by
  have hpi : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ![g₀ x, g₁ x])
      (ContinuousLinearMap.pi ![L₀, L₁]) p := by
    refine hasFDerivAt_pi'' fun i => ?_
    fin_cases i
    · simpa using h₀
    · simpa using h₁
  have hd : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => !₂[g₀ x, g₁ x])
      (((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        (ContinuousLinearMap.pi ![L₀, L₁])) p :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.hasFDerivAt).comp p hpi
  ext i j
  rw [jacobianMatrix_apply, hd.fderiv]
  fin_cases i <;> fin_cases j <;> simp

/-- **Example 7.4** of [quarteroni2000numerical], the analytic part. The Jacobian matrices of the
two iteration functions at their fixed points are
$$J_{G_1}(x_1^*) = \begin{bmatrix} 0 & -1/2 \\ 0 & 0 \end{bmatrix}, \qquad J_{G_2}(x_2^*) =
  \begin{bmatrix} 0 & -1/2 \\ 4/3 & 0 \end{bmatrix},$$
with spectral radii $\rho(J_{G_1}(x_1^*)) = 0$ and $\rho(J_{G_2}(x_2^*)) = \sqrt{2/3} < 1$.

So Property 7.3 applies to both iteration functions, and both converge locally. The spectral
radius is `Matrix.complexSpectralRadius`, a value in $[0, \infty]$. -/
theorem example_7_4_spectralRadius :
    jacobianMatrix example_7_4_G₁ !₂[0, 1] = !![0, -(1 / 2); 0, 0] ∧
      jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)] = !![0, -(1 / 2); 4 / 3, 0] ∧
      complexSpectralRadius (jacobianMatrix example_7_4_G₁ !₂[0, 1]) = 0 ∧
      complexSpectralRadius (jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)])
        = ENNReal.ofReal (√(2 / 3)) ∧
      complexSpectralRadius (jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)]) < 1 := by
  have h35 : √(1 - (4 / 5 : ℝ) ^ 2) = 3 / 5 := by
    rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h0A : (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 0 = 0 := rfl
  have h0B : (!₂[(4 / 5 : ℝ), -(3 / 5)] : EuclideanSpace ℝ (Fin 2)) 0 = 4 / 5 := rfl
  -- the first component of both iteration functions
  have hA0 : ∀ p : EuclideanSpace ℝ (Fin 2),
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => (1 - x 1) / 2)
        ((2 : ℝ)⁻¹ • (-(EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)))) p := fun p =>
    (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).const_sub 1).mul_const
      (2 : ℝ)⁻¹
  -- the second component of `G₁` at `(0, 1)`
  have hA1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => √(1 - x 0 ^ 2))
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) !₂[0, 1] := by
    have hu := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
      (x := (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)))).pow 2).const_sub 1
    have hne : (1 : ℝ) - (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 ≠ 0 := by
      rw [h0A]; norm_num
    refine (hu.sqrt hne).congr_fderiv ?_
    ext v
    simp
  -- the second component of `G₂` at `(4/5, -3/5)`
  have hB1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => -√(1 - x 0 ^ 2))
      ((4 / 3 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) !₂[4 / 5, -(3 / 5)] := by
    have hu := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
      (x := (!₂[(4 / 5 : ℝ), -(3 / 5)] : EuclideanSpace ℝ (Fin 2)))).pow 2).const_sub 1
    have hne : (1 : ℝ) - (!₂[(4 / 5 : ℝ), -(3 / 5)] : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 ≠ 0 := by
      rw [h0B]; norm_num
    refine ((hu.sqrt hne).neg).congr_fderiv ?_
    ext v
    simp only [_root_.neg_apply, _root_.smul_apply, EuclideanSpace.coe_proj, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat, Matrix.cons_val_zero, h35]
    ring
  have hJ1 : jacobianMatrix example_7_4_G₁ !₂[0, 1] = !![0, -(1 / 2); 0, 0] := by
    rw [show example_7_4_G₁ = fun x : EuclideanSpace ℝ (Fin 2) =>
        !₂[(1 - x 1) / 2, √(1 - x 0 ^ 2)] from rfl, jacobianMatrix_pair (hA0 _) hA1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hJ2 : jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)] = !![0, -(1 / 2); 4 / 3, 0] := by
    rw [show example_7_4_G₂ = fun x : EuclideanSpace ℝ (Fin 2) =>
        !₂[(1 - x 1) / 2, -√(1 - x 0 ^ 2)] from rfl, jacobianMatrix_pair (hA0 _) hB1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  -- the square of the spectral radius of the second Jacobian, from `J² = -(2/3) I`
  have hsq2 : complexSpectralRadius (jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)]) ^ 2
      = ENNReal.ofReal (2 / 3 : ℝ) := by
    rw [hJ2]
    have hsq : (!![0, -(1 / 2); 4 / 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2
        = (-(2 / 3) : ℝ) • 1 := by
      rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    have h := Matrix.complexSpectralRadius_pow
      (!![0, -(1 / 2); 4 / 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) (by norm_num : 2 ≠ 0)
    rw [hsq, Matrix.complexSpectralRadius_smul, Matrix.complexSpectralRadius_one, mul_one] at h
    rw [← h, nnnorm_neg, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hsq2rho : complexSpectralRadius (jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)])
      = ENNReal.ofReal (√(2 / 3)) := by
    have hinj : ∀ a b : ENNReal, a ^ 2 = b ^ 2 → a = b := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hab (ne_of_lt ((ENNReal.pow_lt_pow_left_iff (by norm_num)).2 hlt))
      · exact absurd hab.symm (ne_of_lt ((ENNReal.pow_lt_pow_left_iff (by norm_num)).2 hlt))
    refine hinj _ _ ?_
    rw [hsq2, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  refine ⟨hJ1, hJ2, ?_, hsq2rho, ?_⟩
  · rw [hJ1]
    have hsq : (!![0, -(1 / 2); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by
      rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h := Matrix.complexSpectralRadius_pow (!![0, -(1 / 2); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      (two_ne_zero)
    rw [hsq, Matrix.complexSpectralRadius_zero] at h
    exact (pow_eq_zero_iff two_ne_zero).1 h.symm
  · by_contra hc
    rw [not_lt] at hc
    have h1 : (1 : ENNReal) ≤ complexSpectralRadius
        (jacobianMatrix example_7_4_G₂ !₂[4 / 5, -(3 / 5)]) ^ 2 := by
      calc (1 : ENNReal) = 1 ^ 2 := (one_pow 2).symm
        _ ≤ _ := ENNReal.pow_le_pow_left hc
    rw [hsq2] at h1
    have h2 : ENNReal.ofReal (2 / 3 : ℝ) < 1 := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
        ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
      norm_num
    exact absurd h1 (not_le.2 h2)

end Example74

/-- **Remark 7.1** of [quarteroni2000numerical]. Let $E$ be a real normed space, let $F : E \to E$,
and let $F'(x)$ be invertible. Let $G_N(x) = x - F'(x)^{-1} F(x)$ be the iteration function
(7.19) of Newton's method, and let $\alpha \in \mathbb{R}$. Then:

* the Newton step `Newton.step F F'` at $x$ is $G_N(x)$;
* $G_N(x) = x$ if and only if $F(x) = 0$;
* with the residual $r = F(x)$, the Newton increment satisfies $F'(x) (G_N(x) - x) = -r$, which
  is the preconditioned stationary Richardson step with preconditioner $F'(x)$;
* the damped step $x_+ = x - \alpha F'(x)^{-1} F(x)$ satisfies $F'(x) (x_+ - x) = -\alpha r$,
  which is the accelerated Richardson step.

**Correction.** The source prints the preconditioner as $I - J_{G_N}(x^{(k)})$. This is wrong:
$J_{G_N}(x) = -(D(J_F^{-1})(x) \, \cdot) F(x)$, so $I - J_{G_N}(x) \neq J_F(x)$ in general. At a
root, for example, $I - J_{G_N}$ is $I$, while $J_F$ need not be $I$. The matrix that makes the
identity true is $J_F(x^{(k)})$.

The damped step is the one of Section 7.2.6. The derivative $F'(x)$ stands for $J_F(x)$. -/
theorem remark_7_1 (F : E → E) (F' : E → E →L[ℝ] E) (x : E) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = F' x) (α : ℝ) :
    Newton.step F F' x = x - (F' x).inverse (F x) ∧
      (Newton.step F F' x = x ↔ F x = 0) ∧
      F' x (Newton.step F F' x - x) = -F x ∧
      F' x ((x - α • (F' x).inverse (F x)) - x) = -(α • F x) := by
  have hinv : (F' x).inverse = (e.symm : E →L[ℝ] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  refine ⟨rfl, ⟨fun h => ?_, fun h => Newton.step_eq_self_of_eq_zero F F' h⟩, ?_, ?_⟩
  · rw [Newton.step, hinv, sub_eq_self] at h
    have := congrArg e h
    rwa [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
  · rw [Newton.step, hinv, sub_sub_cancel_left, map_neg, ← he]
    simp
  · rw [hinv, sub_sub_cancel_left, map_neg, map_smul, ← he]
    simp

end QuarteroniSaccoSaleri.Chapter07
