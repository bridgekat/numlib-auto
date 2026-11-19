/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.ODE.LinearSystem
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section09

/-!
# Quarteroni, Sacco and Saleri, Section 11.10: Stiff Problems

This module formalizes the stiffness quotient (11.86) of Section 11.10 of [quarteroni2000numerical].
For a linear system $y' = Ay + \varphi(t)$ with constant coefficients whose eigenvalues satisfy
$\sigma \le \operatorname{Re} \lambda_j \le \tau < 0$, the stiffness quotient is
$r_s = \sigma / \tau$. The source calls the system stiff when all eigenvalues have negative real
part and $r_s \gg 1$, which is not a definition. The module proves that $r_s \ge 1$ in that case.

The quotient is `ODE.stiffnessQuotient` of `Numlib.Analysis.ODE.LinearSystem`, applied to the
complexified matrix.

## Main definitions

* Equation (11.86), `QuarteroniSaccoSaleri.Chapter11.stiffnessQuotient`: the stiffness quotient
  $r_s = \sigma / \tau$ of a real matrix.

## Main results

* Equation (11.86), `QuarteroniSaccoSaleri.Chapter11.stiffnessQuotient_eq`: $r_s$ is the least real
  part of an eigenvalue divided by the greatest one.
* Equation (11.86), `QuarteroniSaccoSaleri.Chapter11.one_le_stiffnessQuotient`: $r_s \ge 1$ when
  every eigenvalue has negative real part.

## Deviations from the source

* **Equation (11.86)** (reading). `stiffnessQuotient` takes $\sigma$ and $\tau$ to be the
  infimum and supremum of the real parts of the complex spectrum. The text describes them as
  bounds. `one_le_stiffnessQuotient` assumes a nonempty spectrum with strictly negative real
  parts and permits repeated eigenvalues.

## Not formalized

* **Definition 11.14**, Lambert's characterization of stiffness by the behaviour of methods with
  bounded regions of absolute stability. It is informal.
* The decomposition of the solution into a transient and a steady state, the constraint
  $L \ge \max_i |\lambda_i|$ on the fixed-point iteration, and the counterexample with a matrix
  $A(t)$ in the discussion of linearization. They are unnumbered prose.
-/

open Set Matrix

namespace QuarteroniSaccoSaleri.Chapter11

variable {n : ℕ}

/-- **Equation (11.86)** of [quarteroni2000numerical]. The **stiffness quotient** of
$A \in \mathbb{R}^{n \times n}$ is
$$r_s = \frac{\sigma}{\tau}, \qquad \sigma = \min_j \operatorname{Re} \lambda_j, \quad \tau =
  \max_j \operatorname{Re} \lambda_j,$$
where $\lambda_j$ runs over the complex eigenvalues of $A$.

The definition is `ODE.stiffnessQuotient` of the complexified matrix, with the infimum and the
supremum of the real parts of the spectrum. If $A$ has no eigenvalue ($n = 0$), both are $0$ and
$r_s = 0$; if $\tau = 0$, then $r_s = 0$, because Lean sets $x / 0 = 0$.

**Reading.** Takes the real-part infimum and supremum of the complex spectrum for the two
bounds. The lower-bound theorem uses a nonempty, strictly negative real-part spectrum without
assuming distinct eigenvalues. -/
noncomputable def stiffnessQuotient (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ODE.stiffnessQuotient (A.map ((↑) : ℝ → ℂ))

/-- **Equation (11.86)** of [quarteroni2000numerical], unfolded. For
$A \in \mathbb{R}^{n \times n}$,
$$r_s = \frac{\inf \{\operatorname{Re} \lambda : \lambda \in \sigma(A)\}}{\sup
  \{\operatorname{Re} \lambda : \lambda \in \sigma(A)\}},$$
where $\sigma(A) \subseteq \mathbb{C}$ is the spectrum of $A$ over $\mathbb{C}$.

**Reading.** Takes the real-part infimum and supremum of the complex spectrum for the two
bounds. The lower-bound theorem uses a nonempty, strictly negative real-part spectrum without
assuming distinct eigenvalues. -/
theorem stiffnessQuotient_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    stiffnessQuotient A =
      sInf (Complex.re '' spectrum ℂ (A.map ((↑) : ℝ → ℂ))) /
        sSup (Complex.re '' spectrum ℂ (A.map ((↑) : ℝ → ℂ))) :=
  rfl

/-- **Equation (11.86)** of [quarteroni2000numerical], the quotient is at least one. Let
$A \in \mathbb{R}^{n \times n}$ have at least one eigenvalue, and let every eigenvalue of $A$
have negative real part. Then $r_s \ge 1$.

The proof specializes `ODE.one_le_stiffnessQuotient`: $\sigma \le \tau < 0$ gives
$\sigma / \tau \ge 1$.

**Reading.** Takes the real-part infimum and supremum of the complex spectrum for the two
bounds. The lower-bound theorem uses a nonempty, strictly negative real-part spectrum without
assuming distinct eigenvalues. -/
theorem one_le_stiffnessQuotient (A : Matrix (Fin n) (Fin n) ℝ)
    (hne : (spectrum ℂ (A.map ((↑) : ℝ → ℂ))).Nonempty)
    (hneg : ∀ μ ∈ spectrum ℂ (A.map ((↑) : ℝ → ℂ)), μ.re < 0) : 1 ≤ stiffnessQuotient A :=
  ODE.one_le_stiffnessQuotient _ hne hneg

end QuarteroniSaccoSaleri.Chapter11
