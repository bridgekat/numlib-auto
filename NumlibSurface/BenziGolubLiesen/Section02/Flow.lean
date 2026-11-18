import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Numlib.Optimization.AffineQuadraticKKT

/-!
# Benzi, Golub and Liesen, Section 2.1: Incompressible flow problems

The Stokes variational formulation in [benzi2005numerical] minimizes the Dirichlet
energy minus the work of the load over divergence-free velocities. In the weak
equations the pressure enforces the divergence constraint. The corresponding
algebraic statement follows from `Numlib.Optimization.AffineQuadraticKKT`.
The rotation contribution in two dimensions is skew and has zero quadratic energy.

## Main definitions

* Equations (2.13)–(2.14), `BenziGolubLiesen.stokesEnergy`: the energy built from the
  Dirichlet form.
* After (2.17), `BenziGolubLiesen.rotationBlock₂`: the two-dimensional rotation matrix.

## Main results

* After (2.14), `BenziGolubLiesen.stokes_minimizer_iff_weak_equations`: pressure as multiplier.
* After (2.14), `BenziGolubLiesen.stokes_minimizer_iff_discrete_pressure`: the finite
  pressure vector.
* Before Figure 2.1, `BenziGolubLiesen.convective_eq_gradient_sub_cross`: the Jacobian identity.
* After (2.17), `BenziGolubLiesen.rotationBlock₂_energy_zero`: the rotation does no work.

## Deviations from the source

* **Stokes variational interpretation** (reading). The equivalence concerns the weak algebraic
  equations, with an algebraic pressure functional, not equivalence of Sobolev or strong PDEs.

## Not formalized

* **(2.1)–(2.12).** Strong boundary-value PDEs, estimates for Picard convergence, and the properties
  of conservative discretizations need a specified spatial domain and discretization.
* **(2.13)–(2.14).** Strong PDE recovery and pressure solvability in the continuous pressure space
  require integration by parts with traces and an appropriate divergence inf-sup theorem.
* **(2.15)–(2.17).** The comparison of the linearized boundary-value problems requires a
  differentiable vector-field and boundary-condition setting; the identity is pointwise
  in a Jacobian.
* **(2.18)–(2.20).** The Darcy mixed boundary problem and mesh-independent stability require
  trace and approximation results for the chosen mixed spaces and mesh family.
* **Final paragraph.** The time-stepping applications require a concrete time and space scheme.
-/

namespace BenziGolubLiesen

open Matrix

variable {V Q : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Q] [Module ℝ Q]

/-- **Equation (2.13)** of [benzi2005numerical]. For a bilinear Dirichlet form $a$ on the space
of admissible velocities and a linear load $\ell$, the **Stokes energy** is $J(u)=a(u,u)/2-\ell(u)$.
In the Stokes model $a(u,v)=\int_\Omega \nabla u:\nabla v$ and
$\ell(v)=\int_\Omega f\cdot v$. The form and load are taken as parameters. -/
noncomputable abbrev stokesEnergy (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (load : Module.Dual ℝ V) :
    V → ℝ :=
  LinearMap.quadraticEnergy a load

/-- **Section 2.1** of [benzi2005numerical], the variational interpretation after (2.14).
Let $V,Q$ be real vector spaces, $a$ a symmetric nonnegative bilinear form on $V$,
$D:V\to Q$ the divergence map and $\ell$ the load. A velocity $u$ minimizes the Stokes
energy among divergence-free velocities if and only if $Du=0$ and there is a pressure
functional $p$ on $Q$ such that $a(u,v)-p(Dv)=\ell(v)$ for all $v\in V$.

**Reading.** The printed interpretation of the strong equations (2.10)–(2.12) is expressed
as its weak algebraic counterpart. The pressure is a linear functional on the divergence
space, without a claim that it is represented by a function in a Sobolev or Lebesgue space. -/
theorem stokes_minimizer_iff_weak_equations (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (load : Module.Dual ℝ V) (D : V →ₗ[ℝ] Q) (u : V)
    (hsymm : ∀ u v, a u v = a v u) (hnonneg : ∀ v, 0 ≤ a v v) :
    (D u = 0 ∧ IsMinOn (stokesEnergy a load) {v | D v = 0} u) ↔
      (D u = 0 ∧ ∃ pressure : Module.Dual ℝ Q, ∀ v, a u v - pressure (D v) = load v) := by
  apply and_congr_right
  intro hu
  rw [LinearMap.isMinOn_quadraticEnergy_iff_exists_dual a load D hsymm hnonneg hu]
  constructor
  · rintro ⟨pressure, hp⟩
    exact ⟨-pressure, fun v ↦ by simpa [sub_eq_add_neg] using hp v⟩
  · rintro ⟨pressure, hp⟩
    exact ⟨-pressure, fun v ↦ by simpa [sub_eq_add_neg] using hp v⟩

/-- **Section 2.1** of [benzi2005numerical], the discrete pressure. Let the symmetric
nonnegative discrete Dirichlet form be $a$ and let $B$ be the negative discrete divergence
operator with finitely many pressure coordinates. A velocity $u$ minimizes the Stokes
energy over $Bv=0$ if and only if $Bu=0$ and some pressure vector $p$ satisfies
$a(u,v)+p^TBv=\ell(v)$ for every test velocity $v$. -/
theorem stokes_minimizer_iff_discrete_pressure {m : Type*} [Fintype m]
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (load : Module.Dual ℝ V) (B : V →ₗ[ℝ] (m → ℝ))
    (u : V) (hsymm : ∀ u v, a u v = a v u) (hnonneg : ∀ v, 0 ≤ a v v) :
    (B u = 0 ∧ IsMinOn (stokesEnergy a load) {v | B v = 0} u) ↔
      (B u = 0 ∧ ∃ p : m → ℝ, ∀ v, a u v + p ⬝ᵥ B v = load v) := by
  classical
  apply and_congr_right
  intro hu
  rw [LinearMap.isMinOn_quadraticEnergy_iff_exists_dual a load B hsymm hnonneg hu]
  exact (dotProductEquiv ℝ m).surjective.exists

/-- **Section 2.1** of [benzi2005numerical], before Figure 2.1. For a velocity Jacobian $J$
with $J_{ij}=\partial_j u_i$, the **curl** in three coordinates is
$(J_{32}-J_{23},J_{13}-J_{31},J_{21}-J_{12})$ (mathematical indices starting at one). -/
def curlOfJacobian (J : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![J 2 1 - J 1 2, J 0 2 - J 2 0, J 1 0 - J 0 1]

/-- **Section 2.1** of [benzi2005numerical], before Figure 2.1. At a velocity $u$ with
Jacobian $J$, the convective derivative $Ju$ is $J^T u-u\times\operatorname{curl}(J)$.
The term $J^T u$ is the gradient of $\|u\|_2^2/2$. The formal statement is pointwise
in the value and Jacobian, and does not require a choice of domain for the field. -/
theorem convective_eq_gradient_sub_cross (J : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) :
    J *ᵥ u = Jᵀ *ᵥ u - crossProduct u (curlOfJacobian J) := by
  funext i
  fin_cases i <;>
    simp [curlOfJacobian, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- **Section 2.1** of [benzi2005numerical], after (2.17). For a scalar vorticity $w$,
the **two-dimensional rotation block** is $\begin{bmatrix}0&w\\-w&0\end{bmatrix}$. -/
def rotationBlock₂ (w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, w; -w, 0]

/-- **Section 2.1** of [benzi2005numerical], rotation form. For every scalar vorticity
$w$ and velocity vector $u\in\mathbb R^2$, the rotation block contributes no quadratic
energy: $u^T\begin{bmatrix}0&w\\-w&0\end{bmatrix}u=0$. -/
theorem rotationBlock₂_energy_zero (w : ℝ) (u : Fin 2 → ℝ) :
    u ⬝ᵥ (rotationBlock₂ w *ᵥ u) = 0 := by
  simp [rotationBlock₂, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- **Section 2.1** of [benzi2005numerical], irrotational wind. The two-dimensional
rotation block vanishes at zero vorticity. -/
@[simp] theorem rotationBlock₂_zero : rotationBlock₂ 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationBlock₂]

end BenziGolubLiesen
