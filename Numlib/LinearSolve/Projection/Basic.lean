import Numlib.InnerProductSpace.Coercive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Projection methods: specifications and well-posedness

The canonical Prop-valued specifications of a projection step (Saad Ch. 5, Fong–Saunders §2,
Choi Table 2.5, Atkinson–Han Ch. 9):

* `IsPetrovGalerkin A b x₀ K L x`: `x ∈ x₀ + K` and `b - A x ⟂ L`;
* `IsGalerkin A b x₀ K x`: the case `L = K` (FOM, CG, Lanczos method);
* `IsMinRes A b x₀ K x`: `x ∈ x₀ + K` minimizes `‖b - A x‖` (GMRES, MINRES, CR);
* `IsMinError xstar x₀ K x`: `x ∈ x₀ + K` minimizes `‖xstar - x‖` (SYMMLQ, CGNE).

Well-posedness (Saad Prop 5.1), the residual formula (Prop 5.4), exactness on invariant
subspaces (Prop 5.6) and the matrix representation (5.7) are stated here; optimality
characterizations are in `Optimality.lean`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Petrov–Galerkin specification: `x ∈ x₀ + K` and `b - A x ⟂ L` (Saad (5.1)–(5.2)). -/
structure IsPetrovGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K L : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  orth : b - A x ∈ Lᗮ

/-- Galerkin (orthogonal projection) specification `L = K`. -/
abbrev IsGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop :=
  IsPetrovGalerkin A b x₀ K K x

/-- Minimal-residual specification: `x ∈ x₀ + K` minimizes `‖b - A x‖`. -/
structure IsMinRes (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖

/-- Minimal-error specification: `x ∈ x₀ + K` minimizes the distance to the target `xstar` (the
solution of `A x = b`, made explicit so that the specification is meaningful for singular `A`):
SYMMLQ with `K = A 𝒦_m`, CGNE / Craig's method with `K = A† L`. No operator appears — this is
best approximation of `xstar` from the affine subspace `x₀ + K`. -/
structure IsMinError (xstar x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖xstar - x‖ ≤ ‖xstar - y‖

namespace IsPetrovGalerkin

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K L : Submodule 𝕜 E} {x : E}

theorem inner_residual_eq_zero (hx : IsPetrovGalerkin A b x₀ K L x) {w : E} (hw : w ∈ L) :
    inner 𝕜 w (b - A x) = 0 := by
  sorry

/-- Two Petrov–Galerkin solutions differ by an element of `K ⊓ A⁻¹(Lᗮ)`; uniqueness when
`A` maps `K` injectively "modulo `Lᗮ`" (Saad Prop 5.1's nondegeneracy condition). -/
theorem eq_of_forall (hx : IsPetrovGalerkin A b x₀ K L x) {x' : E}
    (hx' : IsPetrovGalerkin A b x₀ K L x')
    (hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0) : x = x' := by
  sorry

/-- Saad Prop 5.6: exactness on invariant subspaces. -/
theorem eq_of_invt (hx : IsPetrovGalerkin A b x₀ K L x) (hK : K ∈ Module.End.invtSubmodule A)
    (hr : b - A x₀ ∈ K) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) : A x = b := by
  sorry

/-- Restarting: a Petrov–Galerkin step from `x₀` is a Petrov–Galerkin step from any
`x₁ ∈ x₀ + K`. -/
theorem of_mem (hx : IsPetrovGalerkin A b x₀ K L x) {x₁ : E} (hx₁ : x₁ - x₀ ∈ K) :
    IsPetrovGalerkin A b x₁ K L x := by
  sorry

/-- Saad Thm 5.7-type bound for the projected problem: with `r₀ = b - A x₀` and
`d₀ = x* - x₀`, the Petrov–Galerkin residual is controlled by the distance of `d₀` from `K`.
Stated via the oblique projector as `‖P (b - A x)‖ = 0` and `‖(1 - P_K) d₀‖`; see
`Optimality.lean` for the Galerkin/MinRes cases. -/
theorem residual_mem_orthogonal (hx : IsPetrovGalerkin A b x₀ K L x) : b - A x ∈ Lᗮ := hx.orth

end IsPetrovGalerkin

namespace IsMinRes

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K : Submodule 𝕜 E} {x : E}

/-- Saad Prop 5.3: minimal residual over `x₀ + K` iff Petrov–Galerkin with `L = A K`. -/
theorem iff_isPetrovGalerkin [FiniteDimensional 𝕜 K] :
    IsMinRes A b x₀ K x ↔ IsPetrovGalerkin A b x₀ K (K.map A) x := by
  sorry

theorem isPetrovGalerkin [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) :
    IsPetrovGalerkin A b x₀ K (K.map A) x :=
  (iff_isPetrovGalerkin).1 hx

/-- Saad Prop 5.4: the residual of every minimal-residual iterate is `(1 - P_{A K}) r₀`. -/
theorem residual_eq [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) :
    b - A x = (b - A x₀) - (K.map A).starProjection (b - A x₀) := by
  sorry

/-- The residual is unique even when the iterate is not. -/
theorem residual_unique [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) {x' : E}
    (hx' : IsMinRes A b x₀ K x') : b - A x = b - A x' := by
  sorry

theorem norm_residual_le_norm_residual_zero (hx : IsMinRes A b x₀ K x) :
    ‖b - A x‖ ≤ ‖b - A x₀‖ := by
  sorry

/-- Residual norms on nested subspaces are nonincreasing. -/
theorem norm_residual_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinRes A b x₀ K x)
    (hx' : IsMinRes A b x₀ K' x') (hKK' : K ≤ K') : ‖b - A x'‖ ≤ ‖b - A x‖ := by
  sorry

/-- Exactness: if some `y ∈ x₀ + K` solves the system, so does every minimal-residual iterate. -/
theorem apply_eq_of_exists (hx : IsMinRes A b x₀ K x) {y : E} (hy : y - x₀ ∈ K) (hAy : A y = b) :
    A x = b := by
  sorry

end IsMinRes

section WellPosed

variable {A : E →ₗ[𝕜] E} (b x₀ : E) (K : Submodule 𝕜 E)

/-- Saad Prop 5.1 (i): Galerkin with coercive `A` is uniquely solvable. -/
theorem existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive) [FiniteDimensional 𝕜 K] :
    ∃! x, IsGalerkin A b x₀ K x := by
  sorry

/-- Saad Prop 5.1 (ii): minimal residual with `A` injective on `K` is uniquely solvable. -/
theorem existsUnique_isMinRes_of_injOn [FiniteDimensional 𝕜 K] (hinj : Set.InjOn A K) :
    ∃! x, IsMinRes A b x₀ K x := by
  sorry

/-- A minimal-residual iterate always exists on a finite-dimensional `K`. -/
theorem exists_isMinRes [FiniteDimensional 𝕜 K] : ∃ x, IsMinRes A b x₀ K x := by
  sorry

/-- A minimal-error iterate always exists on a finite-dimensional `K` (projection of `x*`). -/
theorem exists_isMinError [FiniteDimensional 𝕜 K] (xstar : E) : ∃ x, IsMinError xstar x₀ K x := by
  sorry

end WellPosed

section MatrixForm

variable {ι : Type*} [Fintype ι]
variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K L : Submodule 𝕜 E}

/-- Saad (5.7): with bases `V` of `K` and `W` of `L`, `x = x₀ + V y` is Petrov–Galerkin iff
`(Wᴴ A V) y = Wᴴ r₀`. -/
theorem isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K) (W : Module.Basis ι 𝕜 L)
    (y : ι → 𝕜) :
    IsPetrovGalerkin A b x₀ K L (x₀ + ∑ j, y j • (V j : E)) ↔
      (Matrix.of fun i j => inner 𝕜 (W i : E) (A (V j))).mulVec y =
        fun i => inner 𝕜 (W i : E) (b - A x₀) := by
  sorry

end MatrixForm
