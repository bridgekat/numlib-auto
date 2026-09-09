import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Numlib.LinearAlgebra.Matrix.Assembly
import Numlib.Variational.Galerkin

/-!
# Saad §2.3: the finite element method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §2.3.

The section has two halves, and only one of them is here.

Its **analytic and geometric half** is not formalized, and cannot be with what Mathlib has: the
divergence theorem (2.37) and the integration by parts (2.38)–(2.40) that carry Green's formula
need a surface measure on the boundary curve `Γ` and an outward unit normal field along it, of
which Mathlib has neither — its divergence theorem is for boxes; the weak formulation (2.41) is set
in `H¹₀(Ω)`, and Mathlib has no Sobolev space on an open set and so no trace and no
zero-boundary-value subspace; and the discrete space `V_h` of (2.42) needs a triangulation
`Ω_h = ∪ K_i` of a planar domain together with the continuous piecewise-affine functions on it and
the existence and uniqueness of the nodal interpolant. Nothing in the chapter *proves* anything
with Sobolev theory — no Céa lemma, no Lax–Milgram theorem, no interpolation estimate and no
convergence result appears in §2.3 — so the missing theory is needed only to state (2.41) and to
build `V_h`, not to run any argument. The same missing boundary machinery is why (2.47), the
Neumann equation, is absent.

Its **algebraic half** is here, and it is what the rest of the book uses. Every statement below
takes as a hypothesis what the missing geometry would supply, and says so:

* `SaadSparse.Chapter02.energyForm` is Saad's `a(u, v) = ∫_Ω ∇u · ∇v dx` written out, with
  `energyForm_bilinear` its bilinearity — the one property of `a` that §2.3 asserts and that needs
  no geometry — and `energyForm_symm` its symmetry.
* `SaadSparse.Chapter02.equation_2_44`: with `u = ∑_j ξ_j φ_j`, the Galerkin condition (2.43) is
  the linear system `∑_j α_{ij} ξ_j = β_i`, `α_{ij} = a(φ_j, φ_i)`, `β_i = (f, φ_i)`.
* `stiffness_isSymm` and `stiffness_posDef`: the stiffness matrix is symmetric when `a` is, and
  positive definite when `a` is coercive on `V_h` and the `φ_j` are independent. Saad's proof
  *that* `a` is coercive on `V_h` — `a(φ, φ) = 0` forces `∇φ = 0`, hence `φ` constant by continuity
  and piecewise linearity, hence `φ = 0` by the boundary condition — is the part that quantifies
  over the concrete `V_h`, and it is a hypothesis here, not a theorem.
* `neumann_not_isUnit`: with Neumann conditions throughout, the constant function lies in `V_h` and
  `a` kills it, so the assembled matrix is singular. Again the concrete input — that `∑_j φ_j` is
  the constant function and that `a` annihilates it — is the hypothesis.
* `equation_2_45` and `equation_2_46`: the assembly `A = ∑_e P_e A_{K_e} P_eᵀ` and the unassembled
  matrix–vector product. These need no geometry at all, and the general form is the backbone's
  `Numlib.LinearAlgebra.Matrix.Assembly`.
* `example_2_1`: (2.45) on the four-element, six-node mesh of Figure 2.8, whose element node lists
  are `mesh_2_8`. The element matrices are left arbitrary — Figure 2.9's numbers belong to one
  triangulation and nothing in the example uses them — and what the example asserts beyond (2.45)
  is the nonzero pattern drawn beside the mesh in Figure 2.8.

The abstract form `a` of the Galerkin part is the backbone's `SesqForm ℝ V`, and the stiffness
matrix is `SesqForm.gramMatrix`. It is *not* connected to `energyForm` above: the bridge would be
the statement that `energyForm` restricted to `V_h ⊆ H¹₀(Ω)` is a bounded form on a Hilbert space,
which is exactly the missing Sobolev theory.

## References

Saad, *Iterative Methods for Sparse Linear Systems*, 2nd ed., §2.3 [saad2003iterative]: the weak
formulation (2.41), the nodal basis (2.42), the Galerkin system (2.43)–(2.44), and the assembly
(2.45)–(2.46).
-/

open MeasureTheory
open scoped Gradient Matrix RealInnerProductSpace

namespace SaadSparse.Chapter02

/-! ### The energy form `a(u, v) = ∫_Ω ∇u · ∇v`

Saad introduces `a` before any discretization and states one property of it, that it is bilinear —
"an immediate property", in his words. The definition and that property need only a measure and a
domain, so they are stated here on an arbitrary real Hilbert space; the *boundary* work of §2.3
(Green's formula, the weak formulation) is what needs the plane, and is absent. -/

section EnergyForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient is additive where both functions are differentiable. -/
private theorem gradient_fun_add {u v : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) : ∇ (fun y => u y + v y) x = ∇ u x + ∇ v x := by
  simp only [gradient, fderiv_fun_add hu hv, map_add]

/-- The gradient is homogeneous where the function is differentiable. -/
private theorem gradient_const_mul {c : ℝ} {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    ∇ (fun y => c * u y) x = c • ∇ u x := by
  simp only [gradient, fderiv_const_mul hu c, map_smulₛₗ, starRingEnd_apply, star_trivial]

/-- The integrand of `a(c₁u₁ + c₂u₂, v)` splits pointwise. -/
private theorem inner_gradient_combo {c₁ c₂ : ℝ} {u₁ u₂ v : E → ℝ}
    (h₁ : ∀ x, DifferentiableAt ℝ u₁ x) (h₂ : ∀ x, DifferentiableAt ℝ u₂ x) (x : E) :
    ⟪∇ (fun y => c₁ * u₁ y + c₂ * u₂ y) x, ∇ v x⟫
      = c₁ * ⟪∇ u₁ x, ∇ v x⟫ + c₂ * ⟪∇ u₂ x, ∇ v x⟫ := by
  rw [gradient_fun_add ((h₁ x).const_mul c₁) ((h₂ x).const_mul c₂), gradient_const_mul (h₁ x),
    gradient_const_mul (h₂ x), inner_add_left, real_inner_smul_left, real_inner_smul_left]

variable [MeasurableSpace E]

/-- Saad's energy form of §2.3, `a(u, v) = ∫_Ω ∇u · ∇v dx`. -/
noncomputable def energyForm (μ : Measure E) (Ω : Set E) (u v : E → ℝ) : ℝ :=
  ∫ x in Ω, ⟪∇ u x, ∇ v x⟫ ∂μ

/-- `a` is symmetric, because the inner product of two real gradients is. -/
theorem energyForm_symm (μ : Measure E) (Ω : Set E) (u v : E → ℝ) :
    energyForm μ Ω u v = energyForm μ Ω v u := by
  simp only [energyForm, real_inner_comm]

/-- **Saad §2.3, bilinearity of `a`.** `a(μ₁u₁ + μ₂u₂, v) = μ₁ a(u₁, v) + μ₂ a(u₂, v)`, for
functions differentiable everywhere and with both products integrable over `Ω`. Linearity in the
second argument follows from this one and `energyForm_symm`. -/
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

/-! ### (2.43)–(2.44) The Galerkin system

The trial and test space is a finite-dimensional subspace `V_h` with basis `φ_1, …, φ_n`, and the
Galerkin condition (2.43) — `u ∈ V_h` with `a(u, v) = (f, v)` for every `v ∈ V_h` — is the
backbone's `IsGalerkinSolution`. What §2.3 adds is the reading of that condition as a linear
system. -/

section Galerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- Saad's stiffness matrix `A = (α_{ij})` of (2.44), `α_{ij} = a(φ_j, φ_i)`: the backbone's
`SesqForm.gramMatrix` under the name §2.3 gives it. -/
noncomputable abbrev stiffnessMatrix (a : SesqForm ℝ V) (φ : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := a.gramMatrix φ

/-- Saad's right-hand side `b = (β_i)` of (2.44), `β_i = (f, φ_i)`, with the `L²` pairing against
`f` written as a bounded functional. -/
noncomputable abbrev loadVector (ℓ : V →L[ℝ] ℝ) (φ : Fin n → V) : Fin n → ℝ := fun i => ℓ (φ i)

/-- **Saad (2.44)**: for `u = ∑_j ξ_j φ_j` the Galerkin condition (2.43) is the linear system
`∑_j α_{ij} ξ_j = β_i`, that is `A ξ = b` in the stiffness matrix and the load vector. -/
theorem equation_2_44 (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) (Vh : Submodule ℝ V)
    (φ : Module.Basis (Fin n) ℝ Vh) (ξ : Fin n → ℝ) :
    IsGalerkinSolution a ℓ Vh (∑ j, ξ j • (φ j : V)) ↔
      (stiffnessMatrix a fun i => (φ i : V)).mulVec ξ = loadVector ℓ fun i => (φ i : V) := by
  have hstar : star ξ = ξ := funext fun i => star_trivial (ξ i)
  rw [IsGalerkinSolution.iff_gramMatrix_mulVec φ ξ, hstar]

/-- The entries of the stiffness matrix, `α_{ij} = a(φ_j, φ_i)`. -/
theorem stiffnessMatrix_apply (a : SesqForm ℝ V) (φ : Fin n → V) (i j : Fin n) :
    stiffnessMatrix a φ i j = a (φ j) (φ i) := rfl

/-- **Saad §2.3**: a symmetric `a` gives a symmetric stiffness matrix, `α_{ij} = α_{ji}`. -/
theorem stiffness_isSymm {a : SesqForm ℝ V} (hs : a.IsHermitian) (φ : Fin n → V) :
    (stiffnessMatrix a φ).IsSymm :=
  Matrix.isHermitian_iff_isSymm.1 (a.gramMatrix_isHermitian hs φ)

/-- The quadratic form of the stiffness matrix, `(Aξ, ξ) = a(φ_ξ, φ_ξ)` with `φ_ξ = ∑ ξ_i φ_i`:
the identity Saad's positive-definiteness argument runs on. -/
theorem dotProduct_stiffnessMatrix_mulVec (a : SesqForm ℝ V) (φ : Fin n → V) (ξ η : Fin n → ℝ) :
    η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) :=
  a.dotProduct_gramMatrix_mulVec_real φ ξ η

/-- **Saad §2.3**: the stiffness matrix is positive definite. The hypothesis `hcoer` is Saad's
claim that `a` is positive definite on `V_h`, whose proof — `a(φ, φ) = 0` forces `φ` constant on
`Ω_h`, hence zero by the Dirichlet condition — quantifies over the concrete finite element space
and is not formalized here. -/
theorem stiffness_posDef {a : SesqForm ℝ V} {c : ℝ} (hc : 0 < c) (hs : a.IsHermitian)
    (hcoer : a.IsCoerciveWith c) {φ : Fin n → V} (hφ : LinearIndependent ℝ φ) :
    (stiffnessMatrix a φ).PosDef :=
  SesqForm.gramMatrix_posDef hc hs hcoer hφ

/-! ### The pure-Neumann system is singular -/

/-- The stiffness matrix applied to a coefficient vector is the form tested against the basis:
`(A ξ)_i = a(∑_j ξ_j φ_j, φ_i)`. -/
theorem stiffnessMatrix_mulVec_apply (a : SesqForm ℝ V) (φ : Fin n → V) (ξ : Fin n → ℝ)
    (i : Fin n) : (stiffnessMatrix a φ).mulVec ξ i = a (∑ j, ξ j • φ j) (φ i) := by
  simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]

/-- If a nonzero coefficient vector spans an element that `a` annihilates on `V_h`, the stiffness
matrix is singular. -/
theorem not_isUnit_stiffnessMatrix (a : SesqForm ℝ V) (φ : Fin n → V) {ξ : Fin n → ℝ}
    (hξ : ξ ≠ 0) (hker : ∀ i, a (∑ j, ξ j • φ j) (φ i) = 0) :
    ¬ IsUnit (stiffnessMatrix a φ) := by
  intro hunit
  have hzero : (stiffnessMatrix a φ).mulVec ξ = (stiffnessMatrix a φ).mulVec 0 := by
    rw [Matrix.mulVec_zero]
    exact funext fun i => (stiffnessMatrix_mulVec_apply a φ ξ i).trans (hker i)
  exact hξ (Matrix.mulVec_injective_of_isUnit hunit hzero)

/-- **Saad §2.3**: with Neumann conditions imposed on the whole boundary the assembled system is
singular. The concrete input the missing finite element space would give is the hypothesis
`hconst`: the constant function `∑_j φ_j` lies in `V_h`, and `a(1, v) = ∫_Ω ∇1 · ∇v = 0` for every
`v`, so the all-ones vector is in the null space of `A`. -/
theorem neumann_not_isUnit [NeZero n] (a : SesqForm ℝ V) (φ : Fin n → V)
    (hconst : ∀ i, a (∑ j, φ j) (φ i) = 0) : ¬ IsUnit (stiffnessMatrix a φ) := by
  refine not_isUnit_stiffnessMatrix a φ (ξ := fun _ => 1) ?_ ?_
  · intro h
    exact one_ne_zero (congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
  · simpa using hconst

end Galerkin

/-! ### (2.45)–(2.46) Assembly and the unassembled matrix–vector product

The element matrices and the Boolean connectivity matrices `P_e` need no geometry: an element is a
list `ι e : Fin 3 → Fin n` of the global numbers of its three vertices, and the only thing the
triangulation contributes is that the form splits as `a = ∑_e a_e` with `a_e(φ_i, φ_j) = 0` unless
both `i` and `j` are vertices of `e`. That support condition is the hypothesis Saad leaves
implicit, and without it the scatter `P_e A_{K_e} P_eᵀ` loses terms. -/

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n nel : ℕ}

/-- A form that splits as a sum of element forms has a stiffness matrix that splits the same
way. -/
private theorem gramMatrix_eq_sum {a : SesqForm ℝ V} {ae : Fin nel → SesqForm ℝ V} {φ : Fin n → V}
    (hsplit : ∀ u v, a u v = ∑ e, ae e u v) :
    stiffnessMatrix a φ = ∑ e, (ae e).gramMatrix φ := by
  ext i j
  rw [Matrix.sum_apply]
  exact hsplit (φ j) (φ i)

/-- The `3 × 3` element stiffness matrix `A_{K_e}` of (2.45): the stiffness matrix of the element
form `a_e` restricted to the three vertices of the element. -/
noncomputable abbrev elementMatrix (ae : SesqForm ℝ V) (φ : Fin n → V) (ι : Fin 3 → Fin n) :
    Matrix (Fin 3) (Fin 3) ℝ := (ae.gramMatrix φ).submatrix ι ι

/-- **Saad (2.45)**, the assembly of the stiffness matrix: `A = ∑_{e} P_e A_{K_e} P_eᵀ`, with
`P_e` the Boolean connectivity matrix of the element's vertex list. -/
theorem equation_2_45 {a : SesqForm ℝ V} {ae : Fin nel → SesqForm ℝ V} {φ : Fin n → V}
    {ι : Fin nel → Fin 3 → Fin n} (hinj : ∀ e, Function.Injective (ι e))
    (hsplit : ∀ u v, a u v = ∑ e, ae e u v)
    (hsupp : ∀ e i j, (i ∉ Set.range (ι e) ∨ j ∉ Set.range (ι e)) → ae e (φ j) (φ i) = 0) :
    stiffnessMatrix a φ = ∑ e, Matrix.connectivity (ι e) * elementMatrix (ae e) φ (ι e) *
      (Matrix.connectivity (ι e) : Matrix (Fin n) (Fin 3) ℝ)ᵀ :=
  Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose hinj hsupp (gramMatrix_eq_sum hsplit)

/-- **Saad (2.46)**, the unassembled matrix–vector product: `A x = ∑_e P_e A_{K_e} (P_eᵀ x)`, so
that the global matrix never has to be formed — gather onto each element, apply its `3 × 3` matrix
there, scatter back and add up. -/
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

/-- The mesh of Figure 2.8: six nodes and four triangles, numbered from the bottom up, each
carrying the three global node numbers Saad lists in Example 2.1 — the first element contributes
to nodes 1, 2, 3, the second to 2, 3, 5, the third to 2, 4, 5 and the fourth to 4, 5, 6.  Node
numbers are `0`-based here, so the book's `k` is `k - 1`. -/
def mesh_2_8 : Fin 4 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![1, 2, 4], ![1, 3, 4], ![3, 4, 5]]

/-- **Saad Example 2.1**: the assembly process (2.45) run on the four-element, six-node mesh of
Figure 2.8, whose element node lists are `mesh_2_8`.

The three clauses are what the example asserts.  The node lists are injective, so each element
really has three distinct vertices and (2.45) applies; the assembled matrix is the sum of the four
scattered element matrices `A^{[e]} = P_e A_{K_e} P_eᵀ` of Figure 2.9, whatever the four element
forms are; and its nonzero pattern is the one drawn beside the mesh in Figure 2.8 — entry `(i, j)`
can be nonzero only when some one element has both `i` and `j` among its vertices.

The element forms are left arbitrary: Figure 2.9 prints numbers for one particular triangulation,
and nothing in the example depends on them beyond the support condition `hsupp`, which is Saad's
"`a_K(φ_i, φ_j)` is zero unless the nodes `i` and `j` are both vertices of `K`". -/
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
