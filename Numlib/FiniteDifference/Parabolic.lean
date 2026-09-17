import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Variational.Evolution

/-!
# The θ-method for `M u' + A u = f`

The θ-method for the linear system of ordinary differential equations `M u' + A u = f` with
symmetric positive definite `M` (the mass matrix) and `A` (the stiffness matrix): the
semi-discretization in space of a parabolic problem by finite differences (`M = 1`,
`A = ν h⁻² tridiag(-1, 2, -1)`) or by finite elements (Galerkin in a basis), and its time-stepping
`(M + θ Δt A) u^{k+1} = (M - (1-θ) Δt A) u^k + Δt (θ f^{k+1} + (1-θ) f^k)`
([quarteroni2000numerical] §13.2–13.3, (13.8)–(13.11), (13.14)–(13.16)).

The module is the matrix face of `Numlib/Variational/Evolution`, which it imports. In the
`M`-inner product `⟪x, y⟫_M = xᵀ M y` — the type synonym `FiniteDifference.MassSpace hM`, an
instance of `WithEnergy` for the Euclidean operator of `M` — the semi-discrete system is the
Galerkin ODE for the form `(x, y) ↦ (A x) ⬝ᵥ y`, the θ-step `FiniteDifference.thetaStep` is the
relation `Variational.IsThetaStep` for that form (`FiniteDifference.isThetaStep_toMass_iff`), and
the stability results — unconditional for `θ ≥ ½` (`thetaStep_dotProduct_mulVec_le`), conditional
on `(1 - 2θ) λ_max Δt ≤ 2` for `θ < ½` (`thetaStep_dotProduct_mulVec_le_of_le`), with `λ_max` the
largest generalized eigenvalue of the pencil `(A, M)`, given as the quadratic-form bound
`xᵀ A x ≤ λ_max xᵀ M x` — are the form-level theorems read in that inner product. The coordinate
bridge `FiniteDifference.isSemidiscreteGalerkin_iff_isSemidiscrete` says that a Galerkin
semi-discretization in a basis `φ` is this system with `M`, `A` the Gram matrices of the inner
product and of the form ([quarteroni2000numerical] (13.13) ⟺ (13.14)), and
`Variational.IsThetaStep.iff_thetaStep` is the same bridge for the θ-step ((13.17) ⟺ (13.16)).

The exact asymptotic-stability threshold — `u^k → 0` for every `u^0` iff every amplification factor
`r_θ(λ_i Δt) = (1 - (1-θ) λ_i Δt) / (1 + θ λ_i Δt)` has modulus `< 1`
(`FiniteDifference.forall_tendsto_thetaStep_iff`) — needs the generalized eigenvalues themselves:
the simultaneous diagonalization of the symmetric-definite pencil
(`Matrix.exists_simultaneous_diagonalization`, `Numlib/Eigen/Pencil`) turns the amplification
matrix into `W diag(r_θ(λ_i Δt)) W⁻¹` (`FiniteDifference.thetaAmplification_eq_conj`), which gives
its characteristic polynomial and its real and complex spectra. For `M = 1` and the finite
difference Laplacian `A = (ν/h²) tridiag(-1, 2, -1)` the eigenvalues are the discrete sine
eigenvalues `(4ν/h²) sin²((k+1)π/(2(m+1)))` of `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`,
and forward Euler is asymptotically stable iff `Δt (4ν/h²) sin²(mπ/(2(m+1))) < 2`
(`FiniteDifference.forwardEuler_heat_tendsto_iff`); the classical `Δt ≤ h²/(2ν)` of
[quarteroni2000numerical] (13.11) is the sufficient condition this implies
(`FiniteDifference.forwardEuler_heat_tendsto_of_le`), the book's "iff" being slightly inexact.
Backward Euler is unconditionally asymptotically stable
(`FiniteDifference.backwardEuler_tendsto`).

## Conventions

Matrices are real, indexed by a `Fintype` with decidable equality; vectors are `n → ℝ` and
`x ⬝ᵥ (M *ᵥ x)` is the quadratic form. The θ-step is defined through the inverse
`(M + θ Δt A)⁻¹` of Mathlib's `Matrix.inv`, and `FiniteDifference.mulVec_thetaStep` says that it
solves its linear system as soon as that matrix is invertible, which
`FiniteDifference.isUnit_add_smul_of_posDef` gives for positive definite `M`, a positive
semidefinite quadratic form of `A` (no symmetry of `A` is needed there, so the nonsymmetric
transport matrices are covered) and `θ Δt ≥ 0`.
-/

open Set Filter Topology Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace FiniteDifference

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The semi-discrete system -/

/-- **The semi-discrete system** `M u' + A u = f` ([quarteroni2000numerical] (13.8) with `M = 1`,
(13.14) in general): `u : ℝ → n → ℝ` solves it on `[0, T]` with `u 0 = u₀`, the derivative taken
within `[0, T]` and existentially quantified, as in `Variational.IsSemidiscreteGalerkin`. -/
def IsSemidiscrete (M A : Matrix n n ℝ) (f : ℝ → n → ℝ) (u₀ : n → ℝ) (T : ℝ)
    (u : ℝ → n → ℝ) : Prop :=
  u 0 = u₀ ∧ ∃ u' : ℝ → n → ℝ, ∀ t ∈ Icc 0 T,
    HasDerivWithinAt u (u' t) (Icc 0 T) t ∧ M *ᵥ u' t + A *ᵥ u t = f t

/-- **The normal form** ([quarteroni2000numerical] (13.15)): for invertible `M`, the system
`M u' + A u = f` is `u' = -M⁻¹ A u + M⁻¹ f`, i.e. the system with mass matrix `1`, stiffness matrix
`M⁻¹ A` and source `M⁻¹ f`. -/
theorem IsSemidiscrete.iff_normalForm {M : Matrix n n ℝ} (hM : IsUnit M) (A : Matrix n n ℝ)
    (f : ℝ → n → ℝ) (u₀ : n → ℝ) (T : ℝ) (u : ℝ → n → ℝ) :
    IsSemidiscrete M A f u₀ T u ↔
      IsSemidiscrete 1 (M⁻¹ * A) (fun t => M⁻¹ *ᵥ f t) u₀ T u := by
  have hdet := (isUnit_iff_isUnit_det M).1 hM
  have key : ∀ v w g : n → ℝ, M *ᵥ v + A *ᵥ w = g ↔ 1 *ᵥ v + (M⁻¹ * A) *ᵥ w = M⁻¹ *ᵥ g := by
    intro v w g
    constructor
    · rintro rfl
      rw [one_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul _ hdet,
        one_mulVec]
    · intro h
      have := congrArg (M *ᵥ ·) h
      simpa only [one_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc,
        mul_nonsing_inv _ hdet, Matrix.one_mul] using this
  simp only [IsSemidiscrete, key]

/-! ### The coordinate bridge -/

section Bridge

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] {ι : Type*} [Fintype ι]

/-- The coordinate bridge for one equation: `⟪w, v⟫ + a z v = F v` for every `v` iff
`M ξ_w + A ξ_z = (F (φ i))_i` for the coordinates `ξ_w = φ.equivFun w`, `ξ_z = φ.equivFun z` in
the basis `φ`, the mass matrix `M = (innerSL ℝ).gramMatrix φ` and the stiffness matrix
`A = a.gramMatrix φ`. Testing on the basis suffices because both sides are linear in `v`. -/
theorem forall_inner_add_eq_iff (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K) (F : K →L[ℝ] ℝ)
    (w z : K) :
    (∀ v, ⟪w, v⟫ + a z v = F v) ↔
      SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ φ.equivFun w + a.gramMatrix φ *ᵥ φ.equivFun z
        = fun i => F (φ i) := by
  have hM : ∀ i, (SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ φ.equivFun w) i = ⟪w, φ i⟫ := fun i => by
    rw [SesqForm.gramMatrix_mulVec_apply, φ.sum_equivFun, innerSL_apply_apply]
  have hA : ∀ i, (a.gramMatrix φ *ᵥ φ.equivFun z) i = a z (φ i) := fun i => by
    rw [SesqForm.gramMatrix_mulVec_apply, φ.sum_equivFun]
  constructor
  · intro h
    funext i
    rw [Pi.add_apply, hM, hA, h]
  · intro h v
    have hL : ((innerSL ℝ w + a z - F : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = 0 := by
      refine φ.ext fun i => ?_
      have := congrFun h i
      rw [Pi.add_apply, hM, hA] at this
      simp only [ContinuousLinearMap.coe_coe, _root_.sub_apply, _root_.add_apply,
        innerSL_apply_apply, LinearMap.zero_apply, this, sub_self]
    have := LinearMap.congr_fun hL v
    simp only [ContinuousLinearMap.coe_coe, _root_.sub_apply, _root_.add_apply,
      innerSL_apply_apply, LinearMap.zero_apply] at this
    linarith

variable [FiniteDimensional ℝ K]

-- the linter does not see the `Fintype` inside the sup norm of `ι → ℝ`
set_option linter.unusedFintypeInType false in
/-- Derivatives transfer along the coordinate map of a basis of a finite-dimensional space, in
both directions: `u` has derivative `u'` within `s` iff its coordinates have derivative the
coordinates of `u'`. -/
theorem hasDerivWithinAt_equivFun_iff (φ : Module.Basis ι ℝ K) (u : ℝ → K) (u' : K) (s : Set ℝ)
    (t : ℝ) :
    HasDerivWithinAt (fun t => φ.equivFun (u t)) (φ.equivFun u') s t ↔
      HasDerivWithinAt u u' s t := by
  set e : K ≃L[ℝ] (ι → ℝ) := φ.equivFun.toContinuousLinearEquiv
  constructor
  · intro h
    have := (e.symm.hasFDerivAt.comp_hasDerivWithinAt t h).congr_deriv (e.symm_apply_apply u')
    refine this.congr (fun x _ => ?_) ?_
    · exact (e.symm_apply_apply (u x)).symm
    · exact (e.symm_apply_apply (u t)).symm
  · intro h
    exact e.hasFDerivAt.comp_hasDerivWithinAt t h

/-- **The coordinate form of the semi-discrete Galerkin problem** ([quarteroni2000numerical]
(13.13) ⟺ (13.14)): for a basis `φ` of the finite-dimensional trial space and a time-independent
form `a`, `u` solves the Galerkin problem iff its coordinates `ξ t = φ.equivFun (u t)` solve
`M ξ' + A ξ = f` with the mass matrix `M_{ij} = ⟪φ_j, φ_i⟫`, the stiffness matrix
`A_{ij} = a(φ_j, φ_i)` and `f_i(t) = F t (φ i)`. -/
theorem isSemidiscreteGalerkin_iff_isSemidiscrete (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K)
    (F : ℝ → K →L[ℝ] ℝ) (u₀ : K) (T : ℝ) (u : ℝ → K) :
    Variational.IsSemidiscreteGalerkin (fun _ => a) F u₀ T u ↔
      IsSemidiscrete (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ)
        (fun t i => F t (φ i)) (φ.equivFun u₀) T (fun t => φ.equivFun (u t)) := by
  simp only [Variational.IsSemidiscreteGalerkin, IsSemidiscrete, φ.equivFun.injective.eq_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u', hu'⟩
    refine ⟨fun t => φ.equivFun (u' t), fun t ht => ?_⟩
    rw [hasDerivWithinAt_equivFun_iff, ← forall_inner_add_eq_iff φ]
    exact hu' t ht
  · rintro ⟨ξ', hξ'⟩
    refine ⟨fun t => φ.equivFun.symm (ξ' t), fun t ht => ?_⟩
    have h := hξ' t ht
    simp only
    rw [← hasDerivWithinAt_equivFun_iff φ, forall_inner_add_eq_iff φ,
      LinearEquiv.apply_symm_apply]
    exact h

omit [FiniteDimensional ℝ K] in
-- the linter does not see the `Fintype` inside `Matrix.PosDef`
set_option linter.unusedFintypeInType false in
/-- **The mass matrix is positive definite** ([quarteroni2000numerical] §13.3, after (13.14)):
the Gram matrix `M_{ij} = ⟪φ_j, φ_i⟫` of a linearly independent family. -/
theorem massMatrix_posDef {φ : ι → K} (hφ : LinearIndependent ℝ φ) :
    (SesqForm.gramMatrix (innerSL ℝ) φ).PosDef :=
  SesqForm.gramMatrix_posDef one_pos SesqForm.innerSL_isHermitian SesqForm.innerSL_isCoerciveWith hφ

end Bridge

/-! ### The θ-method in matrix form -/

section ThetaStep

variable (M A : Matrix n n ℝ) (θ Δt : ℝ)

/-- **One step of the θ-method** ([quarteroni2000numerical] (13.10), (13.16)):
`thetaStep M A θ Δt f₀ f₁ u = (M + θ Δt A)⁻¹ ((M - (1-θ) Δt A) u + Δt (θ f₁ + (1-θ) f₀))`, the
new iterate from the old one `u` and the sources `f₀` (old time) and `f₁` (new time). -/
def thetaStep (f₀ f₁ u : n → ℝ) : n → ℝ :=
  (M + (θ * Δt) • A)⁻¹ *ᵥ ((M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀))

/-- **The amplification matrix** `(M + θ Δt A)⁻¹ (M - (1-θ) Δt A)` of the θ-method, the
homogeneous part of the step. -/
def thetaAmplification : Matrix n n ℝ :=
  (M + (θ * Δt) • A)⁻¹ * (M - ((1 - θ) * Δt) • A)

/-- **The amplification factor** `r_θ(λ Δt) = (1 - (1-θ) λ Δt) / (1 + θ λ Δt)` of the θ-method on
a mode with generalized eigenvalue `λ` ([quarteroni2000numerical] §13.3.1). -/
def thetaFactor (lam : ℝ) : ℝ := (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt)

/-- The step is the amplification matrix applied to the old iterate plus the source term. -/
theorem thetaStep_eq_mulVec_add (f₀ f₁ u : n → ℝ) :
    thetaStep M A θ Δt f₀ f₁ u = thetaAmplification M A θ Δt *ᵥ u
      + (M + (θ * Δt) • A)⁻¹ *ᵥ (Δt • (θ • f₁ + (1 - θ) • f₀)) := by
  simp only [thetaStep, thetaAmplification, mulVec_add, mulVec_mulVec]

/-- The source-free step is the amplification matrix applied to the old iterate. -/
theorem thetaStep_zero_zero (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u = thetaAmplification M A θ Δt *ᵥ u := by
  simp [thetaStep_eq_mulVec_add]

variable {M A θ Δt}

/-- `M + c A` is invertible for `M` positive definite, `x ⬝ᵥ A x ≥ 0` and `c ≥ 0` — the matrix
`K = M + θ Δt A` of the θ-method's linear system ([quarteroni2000numerical] §13.3, after (13.16)).
No symmetry of `A` is needed: `x ⬝ᵥ (M + c A) x > 0` for `x ≠ 0` gives injectivity. -/
theorem isUnit_add_smul_of_posDef (hM : M.PosDef) (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) {c : ℝ}
    (hc : 0 ≤ c) : IsUnit (M + c • A) := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.2 hne
  have h0 : (M + c • A) *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  have h1 : 0 < (x - y) ⬝ᵥ (M *ᵥ (x - y)) := by simpa using hM.dotProduct_mulVec_pos hne'
  have h2 : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := hA _
  have h3 : (x - y) ⬝ᵥ ((M + c • A) *ᵥ (x - y)) = 0 := by rw [h0, dotProduct_zero]
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at h3
  nlinarith

/-- The θ-step solves its linear system
`(M + θ Δt A) u' = (M - (1-θ) Δt A) u + Δt (θ f₁ + (1-θ) f₀)` when the matrix is invertible. -/
theorem mulVec_thetaStep (hK : IsUnit (M + (θ * Δt) • A)) (f₀ f₁ u : n → ℝ) :
    (M + (θ * Δt) • A) *ᵥ thetaStep M A θ Δt f₀ f₁ u
      = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  rw [thetaStep, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hK), one_mulVec]

/-- The θ-step is the unique solution of its linear system when the matrix is invertible. -/
theorem eq_thetaStep_iff (hK : IsUnit (M + (θ * Δt) • A)) (f₀ f₁ u u' : n → ℝ) :
    u' = thetaStep M A θ Δt f₀ f₁ u ↔
      (M + (θ * Δt) • A) *ᵥ u' = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  constructor
  · rintro rfl
    exact mulVec_thetaStep hK f₀ f₁ u
  · intro h
    rw [thetaStep, ← h, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hK),
      one_mulVec]

omit [DecidableEq n] in
/-- The divided form of the θ-method ([quarteroni2000numerical] (13.16) as printed),
`M (u' - u)/Δt + A (θ u' + (1-θ) u) = θ f₁ + (1-θ) f₀`, is the multiplied-out linear system. -/
theorem divided_iff (hΔt : Δt ≠ 0) (f₀ f₁ u u' : n → ℝ) :
    M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ ↔
      (M + (θ * Δt) • A) *ᵥ u' = (M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀) := by
  have key : (M + (θ * Δt) • A) *ᵥ u'
      - ((M - ((1 - θ) * Δt) • A) *ᵥ u + Δt • (θ • f₁ + (1 - θ) • f₀))
      = Δt • (M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u)
        - (θ • f₁ + (1 - θ) • f₀)) := by
    simp only [add_mulVec, sub_mulVec, smul_mulVec, mulVec_add, mulVec_sub, mulVec_smul, smul_add,
      smul_sub, smul_smul, mul_inv_cancel₀ hΔt, one_smul]
    module
  rw [← sub_eq_zero (a := (M + (θ * Δt) • A) *ᵥ u'), key, smul_eq_zero, or_iff_right hΔt,
    sub_eq_zero]

/-- The θ-step characterized by the divided form
`M (u' - u)/Δt + A (θ u' + (1-θ) u) = θ f₁ + (1-θ) f₀`. -/
theorem eq_thetaStep_iff_divided (hK : IsUnit (M + (θ * Δt) • A)) (hΔt : Δt ≠ 0)
    (f₀ f₁ u u' : n → ℝ) :
    u' = thetaStep M A θ Δt f₀ f₁ u ↔
      M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ := by
  rw [eq_thetaStep_iff hK, divided_iff hΔt]

end ThetaStep

/-- **The coordinates of the form-level θ-step** ([quarteroni2000numerical] (13.17) ⟺ (13.16)):
for a basis `φ` of the finite-dimensional trial space, `0 ≤ θ`, `Δt > 0` and a positive form `a`,
`u'` is the θ-step of `u` for `a` and the sources `ℓ₀`, `ℓ₁` iff its coordinates are the matrix
θ-step of the coordinates of `u` for the mass matrix, the stiffness matrix and the source vectors
`(ℓ (φ i))_i`. -/
theorem _root_.Variational.IsThetaStep.iff_thetaStep {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [FiniteDimensional ℝ K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Module.Basis ι ℝ K) (a : SesqForm ℝ K) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u u' : K) :
    Variational.IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' ↔
      φ.equivFun u' = thetaStep (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ) θ Δt
        (fun i => ℓ₀ (φ i)) (fun i => ℓ₁ (φ i)) (φ.equivFun u) := by
  have hA : ∀ x, 0 ≤ x ⬝ᵥ (a.gramMatrix φ *ᵥ x) := fun x => by
    rw [SesqForm.dotProduct_gramMatrix_mulVec_real]
    simpa using hpos (∑ j, x j • φ j)
  have hK := isUnit_add_smul_of_posDef (massMatrix_posDef φ.linearIndependent) hA
    (mul_nonneg hθ hΔt.le)
  rw [eq_thetaStep_iff_divided hK hΔt.ne', ← map_sub, ← map_smul, ← map_smul, ← map_smul,
    ← map_add]
  have hF : ((θ • fun i => ℓ₁ (φ i)) + (1 - θ) • fun i => ℓ₀ (φ i) : ι → ℝ)
      = fun i => (θ • ℓ₁ + (1 - θ) • ℓ₀) (φ i) := by
    funext i
    simp
  rw [hF, ← forall_inner_add_eq_iff φ a]
  simp only [Variational.IsThetaStep, _root_.add_apply, _root_.smul_apply, smul_eq_mul]

/-! ### The `M`-inner product -/

section MassSpace

variable {M : Matrix n n ℝ} (hM : M.PosDef)

/-- **`ℝⁿ` with the `M`-inner product** `⟪x, y⟫_M = (M x) ⬝ᵥ y` of a positive definite matrix
`M`: the energy space `WithEnergy` of the Euclidean operator of `M`. In this space the
θ-method for `M u' + A u = f` is the form-level θ-method of `Numlib/Variational/Evolution`. -/
abbrev MassSpace : Type _ := WithEnergy (toEuclideanLin M) hM.isSymmetricCoercive_toEuclideanLin

/-- The identity `ℝⁿ ≃ₗ MassSpace hM`, the linear equivalence along which the form-level
theorems are read in coordinates. -/
def toMass : (n → ℝ) ≃ₗ[ℝ] MassSpace hM :=
  (WithLp.linearEquiv 2 ℝ (n → ℝ)).symm.trans (WithEnergy.equiv _ _)

instance : FiniteDimensional ℝ (MassSpace hM) := LinearEquiv.finiteDimensional (toMass hM)

instance : CompleteSpace (MassSpace hM) := FiniteDimensional.complete ℝ _

/-- The `M`-inner product is `(M x) ⬝ᵥ y`. -/
theorem inner_toMass (x y : n → ℝ) : ⟪toMass hM x, toMass hM y⟫ = (M *ᵥ x) ⬝ᵥ y := by
  change energyInner (toEuclideanLin M) (WithLp.toLp 2 x) (WithLp.toLp 2 y) = _
  rw [energyInner, toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial,
    dotProduct_comm]

/-- The squared `M`-norm is the quadratic form `x ⬝ᵥ M x`, the book's `‖u‖_M²`. -/
theorem norm_toMass_sq (x : n → ℝ) : ‖toMass hM x‖ ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq, inner_toMass, dotProduct_comm]

/-- The form `(ξ, η) ↦ (A ξ) ⬝ᵥ η` on the `M`-space: the coordinate form
`a(∑ ξ_j φ_j, ∑ η_i φ_i) = η ⬝ᵥ A ξ` of a bilinear form with stiffness matrix `A`
(`SesqForm.dotProduct_gramMatrix_mulVec_real`), and the form `⟪M⁻¹ A x, y⟫_M` of the operator
`M⁻¹ A`, which is `M`-symmetric when `A` is symmetric. -/
def massForm (A : Matrix n n ℝ) : SesqForm ℝ (MassSpace hM) :=
  SesqForm.ofBilin (LinearMap.mk₂ ℝ (fun p q => (A *ᵥ (toMass hM).symm p) ⬝ᵥ (toMass hM).symm q)
    (fun p p' q => by simp [mulVec_add, add_dotProduct])
    (fun c p q => by simp [mulVec_smul, smul_dotProduct])
    (fun p q q' => by simp [dotProduct_add])
    (fun c p q => by simp [dotProduct_smul]))

/-- The mass-space form in coordinates. -/
@[simp]
theorem massForm_apply (A : Matrix n n ℝ) (x y : n → ℝ) :
    massForm hM A (toMass hM x) (toMass hM y) = (A *ᵥ x) ⬝ᵥ y := by
  simp [massForm]

/-- The functional `η ↦ f ⬝ᵥ η` on the `M`-space: the coordinate form of a source functional with
load vector `f_i = F (φ i)`. -/
def massFunctional (f : n → ℝ) : MassSpace hM →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => f ⬝ᵥ (toMass hM).symm p
      map_add' := fun p q => by simp [dotProduct_add]
      map_smul' := fun c p => by simp [dotProduct_smul] }

/-- The mass-space functional in coordinates. -/
@[simp]
theorem massFunctional_apply (f y : n → ℝ) : massFunctional hM f (toMass hM y) = f ⬝ᵥ y := by
  simp [massFunctional]

/-- The functional of the zero load vector is the zero functional. -/
@[simp]
theorem massFunctional_zero : massFunctional hM (0 : n → ℝ) = 0 := by
  ext p
  simp [massFunctional]

/-- The mass-space form of `A` is positive when the quadratic form of `A` is. -/
theorem massForm_isCoerciveWith_zero {A : Matrix n n ℝ} (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) :
    (massForm hM A).IsCoerciveWith 0 := by
  intro p
  obtain ⟨x, rfl⟩ := (toMass hM).surjective p
  rw [massForm_apply, RCLike.re_to_real, zero_mul, dotProduct_comm]
  exact hA x

/-- The mass-space form of a symmetric `A` is symmetric. -/
theorem massForm_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (massForm hM A).IsHermitian := by
  intro p q
  obtain ⟨x, rfl⟩ := (toMass hM).surjective p
  obtain ⟨y, rfl⟩ := (toMass hM).surjective q
  rw [massForm_apply, massForm_apply, RCLike.conj_to_real, dotProduct_comm, dotProduct_mulVec,
    ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq]

/-- **The θ-step in the `M`-space**: `u'` is the form-level θ-step of `u` for the mass-space form
of `A` and the functionals of the load vectors `f₀`, `f₁` iff
`M (u' - u)/Δt + A (θ u' + (1-θ) u) = θ f₁ + (1-θ) f₀`, the divided form of the matrix θ-step. -/
theorem isThetaStep_toMass_iff (A : Matrix n n ℝ) {θ Δt : ℝ} (f₀ f₁ u u' : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt (massFunctional hM f₀) (massFunctional hM f₁)
        (toMass hM u) (toMass hM u') ↔
      M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u) = θ • f₁ + (1 - θ) • f₀ := by
  rw [Variational.IsThetaStep, (toMass hM).surjective.forall,
    ← sub_eq_zero (a := M *ᵥ (Δt⁻¹ • (u' - u)) + A *ᵥ (θ • u' + (1 - θ) • u)),
    ← dotProduct_eq_zero_iff]
  refine forall_congr' fun y => ?_
  rw [← map_sub, ← map_smul, ← map_smul, ← map_smul, ← map_add, inner_toMass, massForm_apply,
    massFunctional_apply, massFunctional_apply, sub_dotProduct, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, sub_eq_zero]

end MassSpace

/-! ### Stability in the `M`-norm -/

section Stability

variable {M A : Matrix n n ℝ} {θ Δt : ℝ}

/-- The matrix step is the form-level step in the `M`-space, with the zero sources as
mass-space functionals. -/
theorem isThetaStep_toMass_thetaStep' (hM : M.PosDef) (hK : IsUnit (M + (θ * Δt) • A))
    (hΔt : Δt ≠ 0) (u : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt (massFunctional hM 0) (massFunctional hM 0)
      (toMass hM u) (toMass hM (thetaStep M A θ Δt 0 0 u)) := by
  rw [isThetaStep_toMass_iff]
  exact (eq_thetaStep_iff_divided hK hΔt 0 0 u _).1 rfl

/-- The matrix θ-step (source-free) is the form-level θ-step in the `M`-space. -/
theorem isThetaStep_toMass_thetaStep (hM : M.PosDef) (hK : IsUnit (M + (θ * Δt) • A))
    (hΔt : Δt ≠ 0) (u : n → ℝ) :
    Variational.IsThetaStep (massForm hM A) θ Δt 0 0 (toMass hM u)
      (toMass hM (thetaStep M A θ Δt 0 0 u)) := by
  have h := isThetaStep_toMass_thetaStep' hM hK hΔt u
  rwa [massFunctional_zero] at h

/-- **Unconditional stability of the θ-method for `½ ≤ θ` in the `M`-norm**
([quarteroni2000numerical] §13.3.1, first conclusion): for `M` positive definite, `x ⬝ᵥ A x ≥ 0`
and `Δt > 0`, the source-free step satisfies `‖u'‖_M ≤ ‖u‖_M`, i.e. `u' ⬝ᵥ M u' ≤ u ⬝ᵥ M u`. This
is `Variational.IsThetaStep.norm_le_of_half_le` read in the `M`-space; no symmetry of `A` is
needed. -/
theorem thetaStep_dotProduct_mulVec_le (hM : M.PosDef) (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt) (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u ⬝ᵥ (M *ᵥ thetaStep M A θ Δt 0 0 u) ≤ u ⬝ᵥ (M *ᵥ u) := by
  have hK : IsUnit (M + (θ * Δt) • A) :=
    isUnit_add_smul_of_posDef hM hA (mul_nonneg (by linarith) hΔt.le)
  have h := (isThetaStep_toMass_thetaStep hM hK hΔt.ne' u).norm_le_of_half_le hθ hΔt
    (massForm_isCoerciveWith_zero hM hA)
  rw [← norm_toMass_sq, ← norm_toMass_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **Conditional stability of the θ-method in the `M`-norm** ([quarteroni2000numerical]
§13.3.1, `Δt ≤ 2 / ((1 - 2θ) λ_h^{N_h})`): for `M` positive definite, `A` symmetric with
`x ⬝ᵥ A x ≥ 0`, `θ ≥ 0`, `Δt > 0`, every generalized eigenvalue of the pencil `(A, M)` at most
`lmax` — stated as the quadratic-form bound `w ⬝ᵥ A w ≤ lmax (w ⬝ᵥ M w)` — and
`(1 - 2θ) lmax Δt ≤ 2`, the source-free step satisfies `u' ⬝ᵥ M u' ≤ u ⬝ᵥ M u`. This is
`Variational.IsThetaStep.norm_le_of_le_of_lt_half` in the `M`-space. -/
theorem thetaStep_dotProduct_mulVec_le_of_le (hM : M.PosDef) (hA : A.IsHermitian)
    (hA0 : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (hθ : 0 ≤ θ) (hΔt : 0 < Δt) {lmax : ℝ}
    (hl : ∀ w, w ⬝ᵥ (A *ᵥ w) ≤ lmax * (w ⬝ᵥ (M *ᵥ w))) (hcfl : (1 - 2 * θ) * lmax * Δt ≤ 2)
    (u : n → ℝ) :
    thetaStep M A θ Δt 0 0 u ⬝ᵥ (M *ᵥ thetaStep M A θ Δt 0 0 u) ≤ u ⬝ᵥ (M *ᵥ u) := by
  have hK : IsUnit (M + (θ * Δt) • A) := isUnit_add_smul_of_posDef hM hA0 (mul_nonneg hθ hΔt.le)
  have hle : ∀ v : MassSpace hM, massForm hM A v v ≤ lmax * ‖v‖ ^ 2 := by
    intro v
    obtain ⟨x, rfl⟩ := (toMass hM).surjective v
    rw [massForm_apply, norm_toMass_sq, dotProduct_comm]
    exact hl x
  have h := (isThetaStep_toMass_thetaStep hM hK hΔt.ne' u).norm_le_of_le_of_lt_half
    (massForm_isHermitian hM hA) (massForm_isCoerciveWith_zero hM hA0) hle hΔt hcfl
  rw [← norm_toMass_sq, ← norm_toMass_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Stability

/-! ### The spectrum of the amplification matrix -/

section Spectrum

variable {M A : Matrix n n ℝ} {θ Δt : ℝ}

/-- The simultaneous diagonalization of the symmetric-definite pencil `(A, M)`
(`Matrix.exists_simultaneous_diagonalization`), in real form: `Wᵀ M W = 1`, `Wᵀ A W = diag d`,
and the pencil spectrum is the range of `d`. -/
theorem exists_conj_eq_diagonal (hM : M.PosDef) (hA : A.IsHermitian) :
    ∃ (W : Matrix n n ℝ) (d : n → ℝ), IsUnit W ∧ star W * M * W = 1 ∧
      star W * A * W = diagonal d ∧ pencilSpectrum A M = Set.range d := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_simultaneous_diagonalization hA hM
  refine ⟨W, d, hW, hWM, ?_, ?_⟩
  · simpa [RCLike.ofReal_real_eq_id] using hWA
  · simpa [RCLike.ofReal_real_eq_id] using hspec

/-- **The amplification matrix is diagonalized by the pencil eigenvectors**: with `Wᵀ M W = 1`
and `Wᵀ A W = diag d` and all `1 + θ d_i Δt ≠ 0`,
`(M + θ Δt A)⁻¹ (M - (1-θ) Δt A) = W diag(r_θ(d_i Δt)) W⁻¹` ([quarteroni2000numerical] §13.3.1,
the θ-method in the eigenbasis, in matrix form). -/
theorem thetaAmplification_eq_conj {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) :
    thetaAmplification M A θ Δt = W * diagonal (fun i => thetaFactor θ Δt (d i)) * W⁻¹ := by
  have hWd := (isUnit_iff_isUnit_det W).1 hW
  have hWs : IsUnit (star W).det := (isUnit_iff_isUnit_det _).1 hW.star
  have hconj : ∀ c : ℝ, star W * (M + c • A) * W = diagonal (fun i => 1 + c * d i) := by
    intro c
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hWM, hWA,
      ← diagonal_one, ← diagonal_smul, ← diagonal_add]
    rfl
  have hK := hconj (θ * Δt)
  have hN : star W * (M - ((1 - θ) * Δt) • A) * W
      = diagonal (fun i => 1 + -((1 - θ) * Δt) * d i) := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact hconj _
  have hexp : ∀ (X : Matrix n n ℝ) (D : Matrix n n ℝ), star W * X * W = D →
      X = (star W)⁻¹ * D * W⁻¹ := by
    intro X D hX
    rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hWs, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hWd, Matrix.mul_one]
  have hK' := hexp _ _ hK
  have hN' := hexp _ _ hN
  have hKunit : IsUnit (M + (θ * Δt) • A) := by
    rw [hK']
    refine ((Matrix.isUnit_nonsing_inv_iff.2 hW.star).mul ?_).mul
      (Matrix.isUnit_nonsing_inv_iff.2 hW)
    rw [isUnit_diagonal, Pi.isUnit_iff]
    intro i
    rw [isUnit_iff_ne_zero]
    have := hden i
    intro h0
    apply this
    linear_combination h0
  have hprod : (M + (θ * Δt) • A) * (W * diagonal (fun i => thetaFactor θ Δt (d i)) * W⁻¹)
      = M - ((1 - θ) * Δt) • A := by
    rw [hK', hN']
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hWd, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    have hne : 1 + θ * Δt * d i ≠ 0 := by
      rw [show θ * Δt * d i = θ * d i * Δt by ring]
      exact hden i
    rw [thetaFactor, show 1 + θ * d i * Δt = 1 + θ * Δt * d i by ring, mul_div_cancel₀ _ hne]
    ring
  rw [thetaAmplification, ← hprod, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hKunit), Matrix.one_mul]

/-- The characteristic polynomial of the amplification matrix is `∏ᵢ (X - r_θ(d_i Δt))`. -/
theorem charpoly_thetaAmplification {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) :
    (thetaAmplification M A θ Δt).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C (thetaFactor θ Δt (d i))) := by
  rw [thetaAmplification_eq_conj hW hWM hWA hden]
  have := Matrix.charpoly_units_conj hW.unit (diagonal (fun i => thetaFactor θ Δt (d i)))
  rw [IsUnit.unit_spec] at this
  rw [this, charpoly_diagonal]

/-- The real spectrum of the amplification matrix is the set of amplification factors
`r_θ(d_i Δt)`. -/
theorem mem_spectrum_thetaAmplification_iff {W : Matrix n n ℝ} {d : n → ℝ} (hW : IsUnit W)
    (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) (μ : ℝ) :
    μ ∈ spectrum ℝ (thetaAmplification M A θ Δt) ↔ ∃ i, μ = thetaFactor θ Δt (d i) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_thetaAmplification hW hWM hWA hden,
    Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- The complex spectrum of the amplification matrix is the set of amplification factors
`r_θ(d_i Δt)`: no non-real eigenvalue appears. -/
theorem mem_spectrum_complexify_thetaAmplification_iff {W : Matrix n n ℝ} {d : n → ℝ}
    (hW : IsUnit W) (hWM : star W * M * W = 1) (hWA : star W * A * W = diagonal d)
    (hden : ∀ i, 1 + θ * d i * Δt ≠ 0) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (thetaAmplification M A θ Δt)) ↔
      ∃ i, μ = (thetaFactor θ Δt (d i) : ℂ) := by
  rw [Matrix.mem_spectrum_complexify_iff, charpoly_thetaAmplification hW hWM hWA hden,
    Polynomial.map_prod, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- The denominators `1 + θ λ Δt` of the amplification factors are positive for a positive
definite pencil, `θ ≥ 0` and `Δt ≥ 0`, since the generalized eigenvalues `λ` are positive. -/
theorem one_add_mul_pos_of_posDef (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt)
    {lam : ℝ} (hlam : lam ∈ pencilSpectrum A M) : 0 < 1 + θ * lam * Δt := by
  have hpos : 0 < lam := by simpa using re_pos_of_mem_pencilSpectrum_of_posDef hA hM hlam
  have := mul_nonneg (mul_nonneg hθ hpos.le) hΔt
  linarith

/-- **The eigenvalues of the θ-step** ([quarteroni2000numerical] §13.3.1): for `M`, `A` positive
definite, `θ ≥ 0` and `Δt ≥ 0`, `μ` is an eigenvalue of the amplification matrix iff
`μ = r_θ(λ Δt) = (1 - (1-θ) λ Δt) / (1 + θ λ Δt)` for a generalized eigenvalue `λ` of the pencil
`(A, M)`, i.e. a root of `det (A - λ M)`. -/
theorem thetaAmplification_hasEigenvalue_iff (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ)
    (hΔt : 0 ≤ Δt) (μ : ℝ) :
    Module.End.HasEigenvalue (toLin' (thetaAmplification M A θ Δt)) μ ↔
      ∃ lam ∈ pencilSpectrum A M, μ = thetaFactor θ Δt lam := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_conj_eq_diagonal hM hA.1
  have hden : ∀ i, 1 + θ * d i * Δt ≠ 0 := fun i =>
    (one_add_mul_pos_of_posDef hM hA hθ hΔt (hspec ▸ Set.mem_range_self i)).ne'
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    mem_spectrum_thetaAmplification_iff hW hWM hWA hden, hspec]
  simp

/-- The spectral radius of the amplification matrix is below one iff every amplification factor
is: `|1 - (1-θ) λ Δt| < 1 + θ λ Δt` for every generalized eigenvalue `λ` of `(A, M)`. -/
theorem complexSpectralRadius_thetaAmplification_lt_one_iff (hM : M.PosDef) (hA : A.PosDef)
    (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt) :
    complexSpectralRadius (thetaAmplification M A θ Δt) < 1 ↔
      ∀ lam ∈ pencilSpectrum A M, |1 - (1 - θ) * lam * Δt| < 1 + θ * lam * Δt := by
  obtain ⟨W, d, hW, hWM, hWA, hspec⟩ := exists_conj_eq_diagonal hM hA.1
  have hden' : ∀ i, 0 < 1 + θ * d i * Δt := fun i =>
    one_add_mul_pos_of_posDef hM hA hθ hΔt (hspec ▸ Set.mem_range_self i)
  have hspecC : spectrum ℂ (complexify (thetaAmplification M A θ Δt))
      = Set.range (fun i => (thetaFactor θ Δt (d i) : ℂ)) := by
    ext μ
    rw [mem_spectrum_complexify_thetaAmplification_iff hW hWM hWA fun i => (hden' i).ne']
    simp [eq_comm]
  rw [complexSpectralRadius_eq_iSup, hspecC, iSup_range, ← Finset.sup_univ_eq_iSup,
    Finset.sup_lt_iff (by simp), hspec]
  simp only [Finset.mem_univ, true_implies, Set.forall_mem_range]
  refine forall_congr' fun i => ?_
  rw [Complex.nnnorm_real, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm,
    NNReal.coe_one, Real.norm_eq_abs, thetaFactor, abs_div, abs_of_pos (hden' i),
    div_lt_one (hden' i)]

/-- **Asymptotic stability of the θ-method iff strict contraction on every mode**
([quarteroni2000numerical] §13.2, "asymptotically stable", and (13.11)): for `M`, `A` positive
definite, `θ ≥ 0` and `Δt ≥ 0`, the source-free iterates tend to zero from every datum iff
`|1 - (1-θ) λ Δt| < 1 + θ λ Δt` for every generalized eigenvalue `λ` of the pencil `(A, M)`; for
`θ ≥ ½` the condition always holds (for `Δt > 0`), for `θ < ½` it is `(1 - 2θ) λ Δt < 2`. Through
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` and the spectrum of the amplification
matrix. -/
theorem forall_tendsto_thetaStep_iff (hM : M.PosDef) (hA : A.PosDef) (hθ : 0 ≤ θ)
    (hΔt : 0 ≤ Δt) :
    (∀ u₀, Tendsto (fun k => (thetaAmplification M A θ Δt ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      ∀ lam ∈ pencilSpectrum A M, |1 - (1 - θ) * lam * Δt| < 1 + θ * lam * Δt := by
  rw [← Matrix.tendsto_pow_zero_iff_forall_mulVec, tendsto_pow_iff_complexSpectralRadius_lt_one,
    complexSpectralRadius_thetaAmplification_lt_one_iff hM hA hθ hΔt]

/-- **Backward Euler is unconditionally asymptotically stable** ([quarteroni2000numerical] §13.2,
after (13.11)): for `M`, `A` positive definite and `Δt > 0`, the iterates
`((M + Δt A)⁻¹ M)ᵏ u₀` tend to zero, the eigenvalues `1 / (1 + λ Δt)` lying in `(0, 1)`. -/
theorem backwardEuler_tendsto (hM : M.PosDef) (hA : A.PosDef) (hΔt : 0 < Δt) (u₀ : n → ℝ) :
    Tendsto (fun k => (thetaAmplification M A 1 Δt ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  refine (forall_tendsto_thetaStep_iff hM hA zero_le_one hΔt.le).2 (fun lam hlam => ?_) u₀
  have hpos : 0 < lam := by simpa using re_pos_of_mem_pencilSpectrum_of_posDef hA hM hlam
  rw [sub_self, zero_mul, zero_mul, sub_zero, abs_one, one_mul]
  nlinarith

end Spectrum

/-! ### The forward Euler scheme for the heat equation -/

/-- `2 - 2 cos (2x) = 4 sin² x`, in the form the discrete sine eigenvalues take. -/
theorem two_sub_two_mul_cos_eq (x : ℝ) : 2 + 2 * (-1) * Real.cos (2 * x) = 4 * Real.sin x ^ 2 := by
  rw [Real.sin_sq_eq_half_sub]
  ring

/-- The eigenvalues of `c tridiag(-1, 2, -1)` of order `m`, `c > 0`, are the `m` numbers
`4 c sin²((k+1)π/(2(m+1)))` ([quarteroni2000numerical] §13.2, the eigenvalues `μ_i` of `A_fd`):
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff` with the half-angle formula. -/
theorem mem_spectrum_smul_symmTridiagonalToeplitz_iff {m : ℕ} {c : ℝ} (hc : 0 < c) (lam : ℝ) :
    lam ∈ spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) ↔
      ∃ k : Fin m, lam
        = c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
  have h1 : lam ∈ spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) ↔
      c⁻¹ * lam ∈ spectrum ℝ (symmTridiagonalToeplitz m (-1) 2) := by
    have := spectrum.smul_mem_smul_iff (a := symmTridiagonalToeplitz m (-1) 2) (s := c⁻¹ * lam)
      (r := Units.mk0 c hc.ne')
    rw [Units.smul_def, Units.smul_def, Units.val_mk0, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul] at this
    exact this
  rw [h1, ← hasEigenvalue_toEuclideanLin_iff, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  have hang : (((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1)
      = 2 * ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    field_simp
  rw [hang, two_sub_two_mul_cos_eq, inv_mul_eq_iff_eq_mul₀ hc.ne']

/-- **Forward Euler for the finite difference heat equation** ([quarteroni2000numerical] (13.11)
and the display after it): for `A = (ν/h²) tridiag(-1, 2, -1)` of order `m` and `ν, h, Δt > 0`,
the iterates `(1 - Δt A)ᵏ u₀` tend to zero for every `u₀` iff
`Δt · (4ν/h²) sin²(mπ/(2(m+1))) < 2`, the exact threshold `Δt λ_max(A) < 2`. Since
`sin² < 1`, the book's condition `Δt ≤ h²/(2ν)` is sufficient, but its "iff" is not exact: the
true threshold `h²/(2ν sin²(mπ/(2(m+1))))` is slightly larger. The case `M = 1` of
`forall_tendsto_thetaStep_iff`, where the pencil spectrum is the spectrum of `A`. -/
theorem forwardEuler_heat_tendsto_iff (m : ℕ) {ν h Δt : ℝ} (hν : 0 < ν) (hh : 0 < h)
    (hΔt : 0 < Δt) :
    (∀ u₀ : Fin m → ℝ, Tendsto (fun k : ℕ =>
        ((1 - Δt • ((ν / h ^ 2) • symmTridiagonalToeplitz m (-1) 2)) ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      Δt * (4 * ν / h ^ 2 * Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) < 2 := by
  set c : ℝ := ν / h ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hA : (c • symmTridiagonalToeplitz m (-1) 2).PosDef :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).smul hc0
  have hamp : thetaAmplification 1 (c • symmTridiagonalToeplitz m (-1) 2) 0 Δt
      = 1 - Δt • (c • symmTridiagonalToeplitz m (-1) 2) := by
    simp [thetaAmplification]
  have hspecset : spectrum ℝ (c • symmTridiagonalToeplitz m (-1) 2) = Set.range fun k : Fin m =>
      c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
    ext lam
    rw [mem_spectrum_smul_symmTridiagonalToeplitz_iff hc0]
    simp [eq_comm]
  rw [← hamp, forall_tendsto_thetaStep_iff Matrix.PosDef.one hA le_rfl hΔt.le, pencilSpectrum_one,
    hspecset, Set.forall_mem_range]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  have hS : ∀ k : Fin m, 0 < Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    intro k
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
    nlinarith [Real.pi_pos]
  have hmono : ∀ k : Fin m, Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1)))
      ≤ Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) := by
    intro k
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
    have h0 : (0 : ℝ) ≤ (((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1)) := by positivity
    refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ?_ ?_
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk Real.pi_pos.le)
        (by positivity)
  have hfac : 4 * ν / h ^ 2 = 4 * c := by rw [hc]; ring
  rw [hfac]
  constructor
  · intro hall
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have := hall ⟨m - 1, Nat.sub_lt hm one_pos⟩
      have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
        rw [Nat.cast_sub hm, Nat.cast_one]
        ring
      rw [hcast, abs_lt] at this
      linarith [this.1]
  · intro hlt k
    have hsq : Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2
        ≤ Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (hS k).le (hmono k) 2
    have hpos := hS k
    have hx : 0 < c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2)
        * Δt := by positivity
    have hle : c * (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) * Δt
        ≤ Δt * (4 * c * Real.sin ((m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1))) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ c * 4 * Δt)
      linarith
    rw [abs_lt]
    constructor <;> linarith

/-- **The book's condition `Δt ≤ h²/(2ν)` is sufficient** ([quarteroni2000numerical] (13.11) and
the display after it): under it the forward Euler iterates `(1 - Δt A)ᵏ u₀` of the finite
difference heat equation tend to zero for every `u₀`. The threshold of
`forwardEuler_heat_tendsto_iff` carries the extra factor `sin²(mπ/(2(m+1))) < 1`, so the
condition is sufficient but not necessary; the book states it as an equivalence. -/
theorem forwardEuler_heat_tendsto_of_le (m : ℕ) {ν h Δt : ℝ} (hν : 0 < ν) (hh : 0 < h)
    (hΔt : 0 < Δt) (hle : Δt ≤ h ^ 2 / (2 * ν)) (u₀ : Fin m → ℝ) :
    Tendsto (fun k : ℕ =>
        ((1 - Δt • ((ν / h ^ 2) • symmTridiagonalToeplitz m (-1) 2)) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  refine (forwardEuler_heat_tendsto_iff m hν hh hΔt).2 ?_ u₀
  set x : ℝ := (m : ℝ) * Real.pi / (2 * ((m : ℝ) + 1)) with hx
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hxlt : x < Real.pi / 2 := by
    rw [hx, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hsq : Real.sin x ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have hfac : 0 < 4 * ν / h ^ 2 := by positivity
  have h1 : Δt * (4 * ν / h ^ 2 * Real.sin x ^ 2)
      ≤ h ^ 2 / (2 * ν) * (4 * ν / h ^ 2 * Real.sin x ^ 2) :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  have h2 : h ^ 2 / (2 * ν) * (4 * ν / h ^ 2 * Real.sin x ^ 2) = 2 * Real.sin x ^ 2 := by
    field_simp
    ring
  linarith

end FiniteDifference

end
