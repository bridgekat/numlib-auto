/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Numlib.LinearAlgebra.Matrix.Assembly
import Numlib.Variational.Galerkin

/-!
# Saad, Section 2.3: The finite element method

This module formalizes the algebraic half of §2.3 of [saad2003iterative], the finite element method.
Let $\phi_1, \dots, \phi_n$ be a basis of a finite-dimensional space $V_h$. With
$u = \sum_j \xi_j \phi_j$, the Galerkin condition (2.43), $a(u, v) = (f, v)$ for every $v \in V_h$,
is the linear system $A\xi = b$ of (2.44), with the stiffness matrix
$\alpha_{ij} = a(\phi_j, \phi_i)$ and the load vector $\beta_i = (f, \phi_i)$. The module proves
this, the symmetry and the positive definiteness of the stiffness matrix, the singularity of the
pure Neumann system, the assembly $A = \sum_e P_e A_{K_e} P_e^T$ of (2.45), the unassembled
matrix–vector product (2.46), and Example 2.1. The proofs specialize `Numlib.Variational.Galerkin`
and `Numlib.LinearAlgebra.Matrix.Assembly`. It also defines the energy form $a(u, v) = \int_\Omega
\nabla u \cdot \nabla v \, dx$ and proves that it is bilinear and symmetric.

The analytic and geometric half of the section is not formalized, because Mathlib lacks the boundary
theory that it needs. Every statement below takes as a hypothesis what the missing geometry would
supply. Section 2.3 proves nothing with Sobolev theory (it has no Céa lemma, no Lax–Milgram theorem,
no interpolation estimate and no convergence result), so the missing theory would be needed only to
state (2.41) and to build $V_h$, not to run an argument.

## Main definitions

* §2.3, `SaadSparse.Chapter02.energyForm`: the energy form $a(u, v) = \int_\Omega \nabla u \cdot
  \nabla v \, dx$.
* Equation (2.44), `SaadSparse.Chapter02.stiffnessMatrix` and `SaadSparse.Chapter02.loadVector`: the
  stiffness matrix $\alpha_{ij} = a(\phi_j, \phi_i)$ and the load vector $\beta_i = \ell(\phi_i)$.
* Equation (2.45), `SaadSparse.Chapter02.elementMatrix`: the $3 \times 3$ element stiffness matrix
  $A_{K_e}$.
* Example 2.1, `SaadSparse.Chapter02.mesh_2_8`: the element node lists of the mesh of Figure 2.8.

## Main results

* §2.3, `SaadSparse.Chapter02.energyForm_symm` and `SaadSparse.Chapter02.energyForm_bilinear`: the
  energy form is symmetric and linear in its first argument.
* Equation (2.44), `SaadSparse.Chapter02.equation_2_44`: the Galerkin condition for
  $u = \sum_j \xi_j \phi_j$ is the linear system $A\xi = b$.
* §2.3, `SaadSparse.Chapter02.stiffness_isSymm` and `SaadSparse.Chapter02.stiffness_posDef`: the
  stiffness matrix is symmetric when $a$ is, and positive definite when $a$ is also coercive and the
  $\phi_j$ are linearly independent.
* §2.3, `SaadSparse.Chapter02.neumann_not_isUnit`: with Neumann conditions on the whole boundary the
  stiffness matrix is singular.
* Equation (2.45), `SaadSparse.Chapter02.equation_2_45`: the assembly
  $A = \sum_e P_e A_{K_e} P_e^T$.
* Equation (2.46), `SaadSparse.Chapter02.equation_2_46`: the unassembled product
  $Ax = \sum_e P_e A_{K_e} (P_e^T x)$.
* Example 2.1, `SaadSparse.Chapter02.example_2_1`: the assembly on the mesh of Figure 2.8, and the
  nonzero pattern of the assembled matrix.

## Implementation notes

* The abstract form $a$ of the Galerkin part is a bounded bilinear form, the backbone's
  `SesqForm ℝ V`, and the stiffness matrix is `SesqForm.gramMatrix`. This form is not connected to
  `SaadSparse.Chapter02.energyForm`. The bridge would be the statement that the energy form
  restricted to $V_h \subseteq H^1_0(\Omega)$ is a bounded form on a Hilbert space, which is the
  missing Sobolev theory.
* The proof in the source that $a$ is positive definite on $V_h$ ($a(\phi, \phi) = 0$ forces
  $\nabla \phi = 0$, hence $\phi$ is constant by continuity and piecewise linearity, hence
  $\phi = 0$ by the boundary condition) quantifies over the concrete space $V_h$. It is a hypothesis
  of `SaadSparse.Chapter02.stiffness_posDef`, not a theorem. In the same way, the facts that
  $\sum_j \phi_j$ is the constant function and that $a$ annihilates it are a hypothesis of
  `SaadSparse.Chapter02.neumann_not_isUnit`.
* An element is a list `ι e : Fin 3 → Fin n` of the global numbers of its three vertices. The
  triangulation contributes only that the form splits as $a = \sum_e a_e$, with
  $a_e(\phi_i, \phi_j) = 0$ unless both $i$ and $j$ are vertices of $e$.

## Deviations from the source

* **Equations (2.45)–(2.46)** (reading). The source leaves implicit that $a_e(\phi_i, \phi_j) = 0$
  unless both $i$ and $j$ are vertices of the element $e$. This support condition is a hypothesis
  here; without it the scatter $P_e A_{K_e} P_e^T$ loses terms. See
  `SaadSparse.Chapter02.equation_2_45`.

## Not formalized

* **The divergence theorem (2.37) and the integration by parts (2.38)–(2.40).** Green's formula
  needs a surface measure on the boundary curve $\Gamma$ and an outward unit normal field along it,
  and Mathlib has neither: its divergence theorem is for boxes.
* **The weak formulation (2.41).** It is set in $H^1_0(\Omega)$, which the backbone has as
  `SobolevZero`, the closure of the test functions in $W^{1,2}(\Omega)$, but without a trace
  operator, so that Green's formula cannot be applied to it.
* **The discrete space $V_h$ of (2.42).** It needs a triangulation $\Omega_h = \bigcup K_i$ of a
  planar domain, the continuous piecewise affine functions on it, and the existence and uniqueness
  of the nodal interpolant.
* **The Neumann equation (2.47).** It needs the same boundary theory as (2.37)–(2.40).
* **The positive definiteness of $a$ on $V_h$.** It quantifies over the concrete finite element
  space, which is not formalized.
-/

open MeasureTheory
open scoped Gradient Matrix RealInnerProductSpace

namespace SaadSparse.Chapter02

/-!
### The energy form $a(u, v) = \int_\Omega \nabla u \cdot \nabla v$

The source introduces $a$ before any discretization and states one property of it, that it is
bilinear, "an immediate property". The definition and that property need only a measure and a
domain, so they are stated here on an arbitrary real Hilbert space. The boundary work of §2.3,
Green's formula and the weak formulation, needs the plane and is not formalized.
-/

section EnergyForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Where $u$ and $v$ are differentiable, $\nabla(u + v) = \nabla u + \nabla v$. -/
private theorem gradient_fun_add {u v : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) : ∇ (fun y => u y + v y) x = ∇ u x + ∇ v x := by
  simp only [gradient, fderiv_fun_add hu hv, map_add]

/-- Where $u$ is differentiable, $\nabla(cu) = c \nabla u$. -/
private theorem gradient_const_mul {c : ℝ} {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    ∇ (fun y => c * u y) x = c • ∇ u x := by
  simp only [gradient, fderiv_const_mul hu c, map_smulₛₗ, starRingEnd_apply, star_trivial]

/-- If $u_1$ and $u_2$ are differentiable everywhere, then $\nabla(c_1 u_1 + c_2 u_2) \cdot \nabla
v = c_1 \nabla u_1 \cdot \nabla v + c_2 \nabla u_2 \cdot \nabla v$ at every point. -/
private theorem inner_gradient_combo {c₁ c₂ : ℝ} {u₁ u₂ v : E → ℝ}
    (h₁ : ∀ x, DifferentiableAt ℝ u₁ x) (h₂ : ∀ x, DifferentiableAt ℝ u₂ x) (x : E) :
    ⟪∇ (fun y => c₁ * u₁ y + c₂ * u₂ y) x, ∇ v x⟫
      = c₁ * ⟪∇ u₁ x, ∇ v x⟫ + c₂ * ⟪∇ u₂ x, ∇ v x⟫ := by
  rw [gradient_fun_add ((h₁ x).const_mul c₁) ((h₂ x).const_mul c₂), gradient_const_mul (h₁ x),
    gradient_const_mul (h₂ x), inner_add_left, real_inner_smul_left, real_inner_smul_left]

variable [MeasurableSpace E]

/-- **Section 2.3** of [saad2003iterative], the energy form. Let $E$ be a real Hilbert space with a
measure $\mu$, and let $\Omega \subseteq E$. For functions $u, v : E \to \mathbb{R}$,
$$a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, d\mu.$$

In the source $E = \mathbb{R}^2$ and $\mu$ is the Lebesgue measure. The gradient is Mathlib's
`gradient`, which is $0$ where the function is not differentiable, and the integral is the
Bochner integral, which is $0$ when the integrand is not integrable on $\Omega$. -/
noncomputable def energyForm (μ : Measure E) (Ω : Set E) (u v : E → ℝ) : ℝ :=
  ∫ x in Ω, ⟪∇ u x, ∇ v x⟫ ∂μ

/-- **Section 2.3** of [saad2003iterative]: the energy form is symmetric, $a(u, v) = a(v, u)$ for
all $u, v : E \to \mathbb{R}$, because the inner product of two real gradients is symmetric. -/
theorem energyForm_symm (μ : Measure E) (Ω : Set E) (u v : E → ℝ) :
    energyForm μ Ω u v = energyForm μ Ω v u := by
  simp only [energyForm, real_inner_comm]

/-- **Section 2.3** of [saad2003iterative], the bilinearity of $a$. Let $c_1, c_2 \in \mathbb{R}$,
let $u_1, u_2 : E \to \mathbb{R}$ be differentiable everywhere, and let $v : E \to \mathbb{R}$
be such that $\nabla u_1 \cdot \nabla v$ and $\nabla u_2 \cdot \nabla v$ are integrable on
$\Omega$. Then
$$a(c_1 u_1 + c_2 u_2, v) = c_1 a(u_1, v) + c_2 a(u_2, v).$$

Linearity in the second argument follows from this statement and
`SaadSparse.Chapter02.energyForm_symm`. -/
theorem energyForm_bilinear (μ : Measure E) (Ω : Set E) (c₁ c₂ : ℝ) {u₁ u₂ v : E → ℝ}
    (h₁ : ∀ x, DifferentiableAt ℝ u₁ x) (h₂ : ∀ x, DifferentiableAt ℝ u₂ x)
    (hi₁ : IntegrableOn (fun x => ⟪∇ u₁ x, ∇ v x⟫) Ω μ)
    (hi₂ : IntegrableOn (fun x => ⟪∇ u₂ x, ∇ v x⟫) Ω μ) :
    energyForm μ Ω (fun y => c₁ * u₁ y + c₂ * u₂ y) v
      = c₁ * energyForm μ Ω u₁ v + c₂ * energyForm μ Ω u₂ v := by
  have hpt : (fun x => ⟪∇ (fun y => c₁ * u₁ y + c₂ * u₂ y) x, ∇ v x⟫)
      = fun x => c₁ * ⟪∇ u₁ x, ∇ v x⟫ + c₂ * ⟪∇ u₂ x, ∇ v x⟫ :=
    funext (inner_gradient_combo h₁ h₂)
  simp only [energyForm, hpt]
  rw [integral_add (hi₁.const_mul c₁) (hi₂.const_mul c₂), integral_const_mul, integral_const_mul]

end EnergyForm

/-!
### (2.43)–(2.44) The Galerkin system

The trial and test space is a finite-dimensional subspace $V_h$ with basis $\phi_1, \dots, \phi_n$.
The Galerkin condition (2.43), $u \in V_h$ and $a(u, v) = (f, v)$ for every $v \in V_h$, is the
backbone's `IsGalerkinSolution`. What §2.3 adds is the reading of that condition as a linear system.
-/

section Galerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- **Equation (2.44)** of [saad2003iterative], the stiffness matrix. Let $a$ be a bounded bilinear
form on a real inner product space $V$, and let $\phi_1, \dots, \phi_n \in V$. The stiffness
matrix is $A = (\alpha_{ij}) \in \mathbb{R}^{n \times n}$ with
$$\alpha_{ij} = a(\phi_j, \phi_i).$$

It is the backbone's `SesqForm.gramMatrix`, under the name that §2.3 gives it. -/
noncomputable abbrev stiffnessMatrix (a : SesqForm ℝ V) (φ : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := a.gramMatrix φ

/-- **Equation (2.44)** of [saad2003iterative], the right-hand side. Let $\ell$ be a bounded linear
functional on $V$, and let $\phi_1, \dots, \phi_n \in V$. The load vector is
$b = (\beta_i) \in \mathbb{R}^n$ with $\beta_i = \ell(\phi_i)$.

The source writes $\beta_i = (f, \phi_i)$, the $L^2$ pairing with $f$; here that pairing is the
functional $\ell$. -/
noncomputable abbrev loadVector (ℓ : V →L[ℝ] ℝ) (φ : Fin n → V) : Fin n → ℝ := fun i => ℓ (φ i)

/-- **Equation (2.44)** of [saad2003iterative]. Let $a$ be a bounded bilinear form and $\ell$ a
bounded linear functional on $V$, let $V_h \subseteq V$ be a subspace with basis
$\phi_1, \dots, \phi_n$, and let $\xi \in \mathbb{R}^n$. Then $u = \sum_j \xi_j \phi_j$
satisfies the Galerkin condition (2.43), $a(u, v) = \ell(v)$ for every $v \in V_h$, if and only
if
$$\sum_{j=1}^{n} \alpha_{ij} \xi_j = \beta_i, \qquad i = 1, \dots, n,$$
that is, $A\xi = b$ for the stiffness matrix $A$ and the load vector $b$.

The Galerkin condition is `IsGalerkinSolution a ℓ Vh u`. -/
theorem equation_2_44 (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) (Vh : Submodule ℝ V)
    (φ : Module.Basis (Fin n) ℝ Vh) (ξ : Fin n → ℝ) :
    IsGalerkinSolution a ℓ Vh (∑ j, ξ j • (φ j : V)) ↔
      (stiffnessMatrix a fun i => (φ i : V)).mulVec ξ = loadVector ℓ fun i => (φ i : V) := by
  have hstar : star ξ = ξ := funext fun i => star_trivial (ξ i)
  rw [IsGalerkinSolution.iff_gramMatrix_mulVec φ ξ, hstar]

/-- The entries of the stiffness matrix of (2.44) of [saad2003iterative] are
$\alpha_{ij} = a(\phi_j, \phi_i)$. -/
theorem stiffnessMatrix_apply (a : SesqForm ℝ V) (φ : Fin n → V) (i j : Fin n) :
    stiffnessMatrix a φ i j = a (φ j) (φ i) := rfl

/-- **Section 2.3** of [saad2003iterative]: if the form $a$ is symmetric, $a(u, v) = a(v, u)$ for
all $u, v$, then for every family $\phi_1, \dots, \phi_n$ the stiffness matrix is symmetric,
$\alpha_{ij} = \alpha_{ji}$. -/
theorem stiffness_isSymm {a : SesqForm ℝ V} (hs : a.IsHermitian) (φ : Fin n → V) :
    (stiffnessMatrix a φ).IsSymm :=
  Matrix.isHermitian_iff_isSymm.1 (a.gramMatrix_isHermitian hs φ)

/-- The quadratic form of the stiffness matrix of (2.44) of [saad2003iterative]: for
$\xi, \eta \in \mathbb{R}^n$,
$$\eta^T A \xi = a\Big(\sum_j \xi_j \phi_j, \sum_i \eta_i \phi_i\Big).$$
At $\eta = \xi$ this is $(A\xi, \xi) = a(\phi_\xi, \phi_\xi)$ with
$\phi_\xi = \sum_i \xi_i \phi_i$, the identity on which the positive definiteness argument of
§2.3 rests. -/
theorem dotProduct_stiffnessMatrix_mulVec (a : SesqForm ℝ V) (φ : Fin n → V) (ξ η : Fin n → ℝ) :
    η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) :=
  a.dotProduct_gramMatrix_mulVec_real φ ξ η

/-- **Section 2.3** of [saad2003iterative]: the stiffness matrix is positive definite. Let $a$ be
symmetric and coercive, $a(v, v) \ge c \|v\|^2$ for all $v \in V$ with a constant $c > 0$, and
let $\phi_1, \dots, \phi_n \in V$ be linearly independent. Then the stiffness matrix $A$ is
symmetric positive definite.

The coercivity hypothesis stands for the claim of the source that $a$ is positive definite on
$V_h$. The proof of that claim ($a(\phi, \phi) = 0$ forces $\phi$ to be constant on $\Omega_h$,
hence zero by the Dirichlet condition) quantifies over the concrete finite element space, and is
not formalized. Coercivity is assumed on all of $V$; to use it on $V_h$ alone, take $V = V_h$. -/
theorem stiffness_posDef {a : SesqForm ℝ V} {c : ℝ} (hc : 0 < c) (hs : a.IsHermitian)
    (hcoer : a.IsCoerciveWith c) {φ : Fin n → V} (hφ : LinearIndependent ℝ φ) :
    (stiffnessMatrix a φ).PosDef :=
  SesqForm.gramMatrix_posDef hc hs hcoer hφ

/-! ### The pure-Neumann system is singular -/

/-- The stiffness matrix applied to a coefficient vector is the form tested against the basis: for
$\xi \in \mathbb{R}^n$, $(A\xi)_i = a(\sum_j \xi_j \phi_j, \phi_i)$. -/
theorem stiffnessMatrix_mulVec_apply (a : SesqForm ℝ V) (φ : Fin n → V) (ξ : Fin n → ℝ)
    (i : Fin n) : (stiffnessMatrix a φ).mulVec ξ i = a (∑ j, ξ j • φ j) (φ i) := by
  simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]

/-- Let $\xi \in \mathbb{R}^n$ be nonzero with $a(\sum_j \xi_j \phi_j, \phi_i) = 0$ for every $i$.
Then the stiffness matrix is singular. This is the step behind the Neumann statement of §2.3 of
[saad2003iterative], `SaadSparse.Chapter02.neumann_not_isUnit`. -/
theorem not_isUnit_stiffnessMatrix (a : SesqForm ℝ V) (φ : Fin n → V) {ξ : Fin n → ℝ}
    (hξ : ξ ≠ 0) (hker : ∀ i, a (∑ j, ξ j • φ j) (φ i) = 0) :
    ¬ IsUnit (stiffnessMatrix a φ) := by
  intro hunit
  have hzero : (stiffnessMatrix a φ).mulVec ξ = (stiffnessMatrix a φ).mulVec 0 := by
    rw [Matrix.mulVec_zero]
    exact funext fun i => (stiffnessMatrix_mulVec_apply a φ ξ i).trans (hker i)
  exact hξ (Matrix.mulVec_injective_of_isUnit hunit hzero)

/-- **Section 2.3** of [saad2003iterative]: with Neumann conditions on the whole boundary, the
assembled system is singular. Let $n \ge 1$, and suppose that $a(\sum_j \phi_j, \phi_i) = 0$ for
every $i$. Then the stiffness matrix $A$ is singular.

The hypothesis is the concrete input that the finite element space would give: the constant
function $\sum_j \phi_j$ lies in $V_h$, and $a(1, v) = \int_\Omega \nabla 1 \cdot \nabla v = 0$
for every $v$. So the vector of all ones is in the null space of $A$. -/
theorem neumann_not_isUnit [NeZero n] (a : SesqForm ℝ V) (φ : Fin n → V)
    (hconst : ∀ i, a (∑ j, φ j) (φ i) = 0) : ¬ IsUnit (stiffnessMatrix a φ) := by
  refine not_isUnit_stiffnessMatrix a φ (ξ := fun _ => 1) ?_ ?_
  · intro h
    exact one_ne_zero (congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
  · simpa using hconst

end Galerkin

/-!
### (2.45)–(2.46) Assembly and the unassembled matrix–vector product

The element matrices and the Boolean connectivity matrices $P_e$ need no geometry. An element is a
list `ι e : Fin 3 → Fin n` of the global numbers of its three vertices, and the triangulation
contributes only that the form splits as $a = \sum_e a_e$ with $a_e(\phi_i, \phi_j) = 0$ unless both
$i$ and $j$ are vertices of $e$. The source leaves this support condition implicit, and without it
the scatter $P_e A_{K_e} P_e^T$ loses terms.
-/

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n nel : ℕ}

/-- If $a = \sum_e a_e$, then the stiffness matrix of $a$ is the sum of the stiffness matrices of
the forms $a_e$. -/
private theorem gramMatrix_eq_sum {a : SesqForm ℝ V} {ae : Fin nel → SesqForm ℝ V} {φ : Fin n → V}
    (hsplit : ∀ u v, a u v = ∑ e, ae e u v) :
    stiffnessMatrix a φ = ∑ e, (ae e).gramMatrix φ := by
  ext i j
  rw [Matrix.sum_apply]
  exact hsplit (φ j) (φ i)

/-- **Equation (2.45)** of [saad2003iterative], the element stiffness matrix. Let $a_e$ be the form
of an element whose vertices have the global numbers $\iota(1), \iota(2), \iota(3)$. Then
$A_{K_e} \in \mathbb{R}^{3 \times 3}$ is the stiffness matrix of $a_e$ restricted to these three
vertices: its entry $(p, q)$ is $a_e(\phi_{\iota(q)}, \phi_{\iota(p)})$. -/
noncomputable abbrev elementMatrix (ae : SesqForm ℝ V) (φ : Fin n → V) (ι : Fin 3 → Fin n) :
    Matrix (Fin 3) (Fin 3) ℝ := (ae.gramMatrix φ).submatrix ι ι

/-- **Equation (2.45)** of [saad2003iterative], the assembly of the stiffness matrix. Let
$a = \sum_e a_e$ be a sum of element forms over the elements $e$, let each element have an
injective vertex list $\iota_e$, and suppose that $a_e(\phi_j, \phi_i) = 0$ unless both $i$ and
$j$ are vertices of $e$. Then
$$A = \sum_e P_e A_{K_e} P_e^T,$$
where $P_e \in \mathbb{R}^{n \times 3}$ is the Boolean connectivity matrix of $\iota_e$, with
entry $1$ at $(\iota_e(p), p)$ and $0$ elsewhere.

**Reading.** The source leaves the support condition implicit. It is a hypothesis here, and
without it the scatter $P_e A_{K_e} P_e^T$ loses terms.

The matrix $P_e$ is `Matrix.connectivity (ι e)`. The general form of the assembly is in
`Numlib.LinearAlgebra.Matrix.Assembly`. -/
theorem equation_2_45 {a : SesqForm ℝ V} {ae : Fin nel → SesqForm ℝ V} {φ : Fin n → V}
    {ι : Fin nel → Fin 3 → Fin n} (hinj : ∀ e, Function.Injective (ι e))
    (hsplit : ∀ u v, a u v = ∑ e, ae e u v)
    (hsupp : ∀ e i j, (i ∉ Set.range (ι e) ∨ j ∉ Set.range (ι e)) → ae e (φ j) (φ i) = 0) :
    stiffnessMatrix a φ = ∑ e, Matrix.connectivity (ι e) * elementMatrix (ae e) φ (ι e) *
      (Matrix.connectivity (ι e) : Matrix (Fin n) (Fin 3) ℝ)ᵀ :=
  Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose hinj hsupp (gramMatrix_eq_sum hsplit)

/-- **Equation (2.46)** of [saad2003iterative], the unassembled matrix–vector product. Under the
hypotheses of `SaadSparse.Chapter02.equation_2_45`, for every $x \in \mathbb{R}^n$,
$$Ax = \sum_e P_e A_{K_e} (P_e^T x),$$
where $P_e^T x = (x_{\iota_e(1)}, x_{\iota_e(2)}, x_{\iota_e(3)})$. So the global matrix never
has to be formed: gather $x$ onto each element, apply its $3 \times 3$ matrix there, scatter the
result back and add.

**Reading.** As in (2.45), the support condition that the source leaves implicit is a
hypothesis. -/
theorem equation_2_46 {a : SesqForm ℝ V} {ae : Fin nel → SesqForm ℝ V} {φ : Fin n → V}
    {ι : Fin nel → Fin 3 → Fin n} (hinj : ∀ e, Function.Injective (ι e))
    (hsplit : ∀ u v, a u v = ∑ e, ae e u v)
    (hsupp : ∀ e i j, (i ∉ Set.range (ι e) ∨ j ∉ Set.range (ι e)) → ae e (φ j) (φ i) = 0)
    (x : Fin n → ℝ) :
    (stiffnessMatrix a φ).mulVec x
      = ∑ e, (Matrix.connectivity (ι e) : Matrix (Fin n) (Fin 3) ℝ) *ᵥ
          (elementMatrix (ae e) φ (ι e) *ᵥ fun p => x (ι e p)) :=
  Matrix.mulVec_eq_sum_connectivity hinj hsupp (gramMatrix_eq_sum hsplit) x

/-! ### Example 2.1: the assembly on the mesh of Figure 2.8 -/

/-- **Example 2.1** of [saad2003iterative], the mesh of Figure 2.8: six nodes and four triangles,
numbered from the bottom up. Each element carries the three global node numbers that the source
lists: the first element has the nodes 1, 2, 3, the second has 2, 3, 5, the third has 2, 4, 5
and the fourth has 4, 5, 6.

Node numbers are 0-based in Lean, so the book's node $k$ is `k - 1`. -/
def mesh_2_8 : Fin 4 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![1, 2, 4], ![1, 3, 4], ![3, 4, 5]]

/-- **Example 2.1** of [saad2003iterative], the assembly process (2.45) on the four-element,
six-node mesh of Figure 2.8, whose element node lists are `SaadSparse.Chapter02.mesh_2_8`. Let
$a = \sum_{e=1}^{4} a_e$ be bounded bilinear forms on $V$ and $\phi_1, \dots, \phi_6 \in V$, and
suppose that $a_e(\phi_j, \phi_i) = 0$ unless the nodes $i$ and $j$ are both vertices of the
element $e$. Then the following three statements hold.

* The node list of each element is injective, so each element has three distinct vertices, and
  (2.45) applies.
* The stiffness matrix is the sum $A = \sum_e P_e A_{K_e} P_e^T$ of the four scattered element
  matrices $A^{[e]}$ of Figure 2.9.
* An entry $a_{ij}$ can be nonzero only where the pattern matrix $M$ below has the entry $1$,
  that is, only when some element has both $i$ and $j$ among its vertices. This is the nonzero
  pattern drawn beside the mesh in Figure 2.8.

$$M = \begin{bmatrix} 1 & 1 & 1 & 0 & 0 & 0 \\ 1 & 1 & 1 & 1 & 1 & 0 \\ 1 & 1 & 1 & 0 & 1 & 0 \\
  0 & 1 & 0 & 1 & 1 & 1 \\ 0 & 1 & 1 & 1 & 1 & 1 \\ 0 & 0 & 0 & 1 & 1 & 1 \end{bmatrix}.$$

The element forms are arbitrary. Figure 2.9 prints numbers for one particular triangulation, and
nothing in the example depends on them beyond the support condition, which is the statement of
the source that $a_K(\phi_i, \phi_j)$ is zero unless the nodes $i$ and $j$ are both vertices of
$K$. -/
theorem example_2_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a : SesqForm ℝ V}
    {ae : Fin 4 → SesqForm ℝ V} {φ : Fin 6 → V} (hsplit : ∀ u v, a u v = ∑ e, ae e u v)
    (hsupp : ∀ e i j, (i ∉ Set.range (mesh_2_8 e) ∨ j ∉ Set.range (mesh_2_8 e)) →
      ae e (φ j) (φ i) = 0) :
    (∀ e, Function.Injective (mesh_2_8 e)) ∧
      stiffnessMatrix a φ = ∑ e, Matrix.connectivity (mesh_2_8 e) *
          elementMatrix (ae e) φ (mesh_2_8 e) *
          (Matrix.connectivity (mesh_2_8 e) : Matrix (Fin 6) (Fin 3) ℝ)ᵀ ∧
      ∀ i j, stiffnessMatrix a φ i j ≠ 0 →
        (!![1, 1, 1, 0, 0, 0;
            1, 1, 1, 1, 1, 0;
            1, 1, 1, 0, 1, 0;
            0, 1, 0, 1, 1, 1;
            0, 1, 1, 1, 1, 1;
            0, 0, 0, 1, 1, 1] : Matrix (Fin 6) (Fin 6) ℕ) i j = 1 := by
  have hinj : ∀ e, Function.Injective (mesh_2_8 e) := by decide
  refine ⟨hinj, equation_2_45 hinj hsplit hsupp, fun i j hij => ?_⟩
  have hne : ∃ e, ae e (φ j) (φ i) ≠ 0 := by
    by_contra hc
    have hc : ∀ e, ae e (φ j) (φ i) = 0 := fun e => not_not.1 (fun h => hc ⟨e, h⟩)
    exact hij (by
      rw [show stiffnessMatrix a φ i j = a (φ j) (φ i) from rfl, hsplit]
      exact Finset.sum_eq_zero fun e _ => hc e)
  obtain ⟨e, he⟩ := hne
  have hmem : i ∈ Set.range (mesh_2_8 e) ∧ j ∈ Set.range (mesh_2_8 e) := by
    by_contra hc
    exact he (hsupp e i j (by tauto))
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hmem
  have key : ∀ (e : Fin 4) (p q : Fin 3),
      (!![1, 1, 1, 0, 0, 0;
          1, 1, 1, 1, 1, 0;
          1, 1, 1, 0, 1, 0;
          0, 1, 0, 1, 1, 1;
          0, 1, 1, 1, 1, 1;
          0, 0, 0, 1, 1, 1] : Matrix (Fin 6) (Fin 6) ℕ)
        (mesh_2_8 e p) (mesh_2_8 e q) = 1 := by decide
  rw [← hp, ← hq]
  exact key e p q

end Assembly

end SaadSparse.Chapter02
