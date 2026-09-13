import Numlib.Analysis.ODE.LinearSystem
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section09

/-!
# Quarteroni–Sacco–Saleri §11.10: stiff problems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.10.

The stiffness quotient (11.86): for a linear system `y' = A y + φ(t)` with constant coefficients
whose eigenvalues satisfy `σ ≤ Re λⱼ ≤ τ < 0`, `r_s = σ / τ`; the system is called stiff when the
eigenvalues all have negative real parts and `r_s ≫ 1`, which is not a definition. Definition
11.14 (Lambert's characterization of stiffness by the behaviour of methods with bounded
stability regions) is informal and gets no node; the decomposition of the solution into transient
and steady state, the fixed-point constraint `L ≥ max |λᵢ|` and the `A(t)` counterexample of the
linearization discussion are unnumbered prose. The quotient is `ODE.stiffnessQuotient` of
`Numlib/Analysis/ODE/LinearSystem` on the complexified matrix.

## Main definitions

* `stiffnessQuotient A` — `r_s = σ / τ` for a real matrix `A`.

## Main results

* `stiffnessQuotient_eq` — `r_s = (min Re λ) / (max Re λ)` over the spectrum.
* `one_le_stiffnessQuotient` — `r_s ≥ 1` when every eigenvalue has negative real part.
-/

open Set Matrix

namespace QuarteroniSaccoSaleri.Chapter11

variable {n : ℕ}

/-- **The stiffness quotient (11.86)** `r_s = σ / τ` of a real matrix `A`, where
`σ ≤ Re λⱼ ≤ τ` are the least and the greatest real parts of the (complex) eigenvalues of `A`;
`ODE.stiffnessQuotient` of the complexified matrix. -/
noncomputable def stiffnessQuotient (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ODE.stiffnessQuotient (A.map ((↑) : ℝ → ℂ))

/-- `r_s = σ / τ` with `σ = min_j Re λⱼ` and `τ = max_j Re λⱼ`, the extrema of the real parts of
the spectrum of `A` over `ℂ`. -/
theorem stiffnessQuotient_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    stiffnessQuotient A =
      sInf (Complex.re '' spectrum ℂ (A.map ((↑) : ℝ → ℂ))) /
        sSup (Complex.re '' spectrum ℂ (A.map ((↑) : ℝ → ℂ))) :=
  rfl

/-- If `A` has an eigenvalue and every eigenvalue has negative real part, then `r_s ≥ 1`;
`ODE.one_le_stiffnessQuotient`. -/
theorem one_le_stiffnessQuotient (A : Matrix (Fin n) (Fin n) ℝ)
    (hne : (spectrum ℂ (A.map ((↑) : ℝ → ℂ))).Nonempty)
    (hneg : ∀ μ ∈ spectrum ℂ (A.map ((↑) : ℝ → ℂ)), μ.re < 0) : 1 ≤ stiffnessQuotient A :=
  ODE.one_le_stiffnessQuotient _ hne hneg

end QuarteroniSaccoSaleri.Chapter11
