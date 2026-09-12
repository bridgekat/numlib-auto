import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Iterate
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearSolve.Projection.Basic

/-!
# The interface reduction of a two-block linear system

A linear system whose unknowns split into an *interior* block and an *interface* block,

`(B E; F C) (x; y) = (f; g)`,

reduces to a system on the interface block alone, `S y = g'` with `S = C - F B⁻¹ E` the Schur
complement and `g' = g - F B⁻¹ f`.  This module is about what a Krylov method does with that
reduction ([saad2003iterative], §14.4.1 and §14.5); the algebra of `S` itself is
`Numlib/LinearAlgebra/Matrix/SchurComplement`.

## The interface restriction

`DomainDecomposition.restrictMatrix R m n` is the boolean matrix `(0 I)` that reads off the second
block, and `DomainDecomposition.prolongMatrix R m n` its transpose, which extends a vector of the
interface by zero.  As operators on Euclidean space they are `DomainDecomposition.restrict` and
`DomainDecomposition.prolong`; the prolongation is an isometry onto the second block of coordinates
and is the adjoint of the restriction (`DomainDecomposition.adjoint_restrict`).

## Transfer along an intertwining isometry

The work is done by three theorems stated for an arbitrary linear map `P` intertwining two
operators, `T ∘ₗ P = P ∘ₗ S`:

* `DomainDecomposition.krylov_subspace_map_of_comp_eq`: `𝒦_k(T, P v) = P 𝒦_k(S, v)`;
* `DomainDecomposition.isMinResidual_map_iff` and `DomainDecomposition.isGalerkin_map_iff`: if moreover
  `P` preserves inner products and the initial residual of the big system is `P` of that of the
  small one, then the minimal-residual (respectively Galerkin) iterates of the two systems
  correspond, because the two minimizations are literally the same minimization.

## The block preconditioners

`DomainDecomposition.blockLower` and `DomainDecomposition.blockUpper` are the block triangular
preconditioners `L_A = (I 0; F B⁻¹ L_S)` and `U_A = (B E; 0 U_S)`.  They factor the system matrix as
`A = L_A (I ⊕ L_S⁻¹ S U_S⁻¹) U_A`, so the split-preconditioned operator `L_A⁻¹ A U_A⁻¹` is block
diagonal with the preconditioned Schur complement in its second block, and the residual of a
*consistent* initial guess `x₀ = (B⁻¹(f - E y₀); y₀)` lies entirely in that block.  The transfer
theorems then say that running a projection method on the preconditioned full system is running it
on the reduced system: `DomainDecomposition.isMinResidual_iff_isMinResidual_schurComplement` and its Galerkin
twin as an equivalence, and `DomainDecomposition.exists_isMinResidual_schurComplement` in the direction
that *every* iterate of the full system arises this way.

`DomainDecomposition.inducedPreconditioner` is the preconditioner a preconditioner `M_A` of the
whole matrix induces on the interface, `M_S = (R_y M_A⁻¹ R_yᵀ)⁻¹`; for a block triangular
factorization `M_A = L_A U_A` it is the product of the trailing diagonal blocks of the two factors.

## References

[saad2003iterative], §14.2.1 for the reduction, §14.4.1 for the induced preconditioner
(Proposition 14.10) and §14.5 for the equivalence of the full and the reduced iterations
(Propositions 14.11 and 14.12).
-/

namespace DomainDecomposition

open Matrix

/-! ### The interface restriction as a matrix -/

section RestrictMatrix

variable (R : Type*) [CommRing R] (m n : Type*) [DecidableEq n]

/-- **The interface restriction** `R_y = (0  I)`: the boolean matrix that reads off the second block
of a vector indexed by `m ⊕ n` ([saad2003iterative], Proposition 14.1 and §14.4.1). -/
def restrictMatrix : Matrix n (m ⊕ n) R := Matrix.fromCols 0 1

/-- **The interface prolongation** `R_yᵀ`: the boolean matrix that extends a vector indexed by `n`
to one indexed by `m ⊕ n` by zero. -/
def prolongMatrix : Matrix (m ⊕ n) n R := Matrix.fromRows 0 1

variable {R m n}

/-- The prolongation is the transpose of the restriction. -/
@[simp]
theorem transpose_restrictMatrix : (restrictMatrix R m n)ᵀ = prolongMatrix R m n := by
  ext (i | i) j <;> simp [restrictMatrix, prolongMatrix, Matrix.one_apply, eq_comm]

/-- The entries of `R_y` are `0` and `1`, so its conjugate transpose is its transpose: the adjoint
of the restriction is the prolongation. -/
@[simp]
theorem conjTranspose_restrictMatrix [StarRing R] :
    (restrictMatrix R m n)ᴴ = prolongMatrix R m n := by
  ext (i | i) j <;>
    simp [restrictMatrix, prolongMatrix, Matrix.one_apply, eq_comm, apply_ite star]

variable [Fintype n]

/-- `R_yᵀ` extends a vector of the interface by zero. -/
@[simp]
theorem prolongMatrix_mulVec (y : n → R) :
    prolongMatrix R m n *ᵥ y = Sum.elim (0 : m → R) y := by
  simp [prolongMatrix]

variable [Fintype m]

/-- `R_y` applied to a vector is its second block. -/
@[simp]
theorem restrictMatrix_mulVec (v : m ⊕ n → R) : restrictMatrix R m n *ᵥ v = v ∘ Sum.inr := by
  funext i
  simp [restrictMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- The rows of `R_y` are orthonormal: `R_y R_yᵀ = I`. -/
@[simp]
theorem restrictMatrix_mul_prolongMatrix : restrictMatrix R m n * prolongMatrix R m n = 1 := by
  simp [restrictMatrix, prolongMatrix, Matrix.fromCols_mul_fromRows]

/-- **`R_y M R_yᵀ` is the trailing diagonal block of `M`.**  This is the identity behind
[saad2003iterative], Proposition 14.10: the compression of a matrix to the interface variables is
its `(2,2)` block. -/
theorem restrictMatrix_mul_mul_prolongMatrix (M : Matrix (m ⊕ n) (m ⊕ n) R) :
    restrictMatrix R m n * M * prolongMatrix R m n = M.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [restrictMatrix, prolongMatrix, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp

end RestrictMatrix

/-! ### The interface restriction as an operator

The binders are staged: the prolongation needs nothing about the interior index type `m`, its
isometry statements need `Fintype m` for the norm of the big space, and the restriction needs
`DecidableEq m` as well, for the identity matrix indexed by `m ⊕ n`. -/

section Restrict

variable (𝕜 : Type*) [RCLike 𝕜] (m n : Type*) [Fintype n] [DecidableEq n]

/-- **The interface prolongation operator** `R_yᵀ`: it extends a vector of the interface by zero.
It is the adjoint of `DomainDecomposition.restrict` (`DomainDecomposition.adjoint_restrict`). -/
noncomputable def prolong : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) :=
  Matrix.toEuclideanLin (prolongMatrix 𝕜 m n)

variable {𝕜 m n}

/-- The prolongation extends by zero. -/
theorem prolong_apply (y : EuclideanSpace 𝕜 n) :
    prolong 𝕜 m n y = WithLp.toLp 2 (Sum.elim (0 : m → 𝕜) (WithLp.ofLp y)) := by
  simp [prolong, Matrix.toLpLin_apply]

/-- The prolongation of a plain vector. -/
theorem prolong_toLp (y : n → 𝕜) :
    prolong 𝕜 m n (WithLp.toLp 2 y) = WithLp.toLp 2 (Sum.elim (0 : m → 𝕜) y) :=
  prolong_apply _

/-- The prolongation is injective. -/
theorem prolong_injective : Function.Injective (prolong 𝕜 m n) := by
  intro a b hab
  rw [prolong_apply, prolong_apply] at hab
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  exact congrFun (congrArg WithLp.ofLp hab) (Sum.inr j)

/-- **The range of the prolongation is the second block of coordinates**: a vector is a prolonged
one exactly when its interior block vanishes. -/
theorem mem_range_prolong_iff (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    v ∈ LinearMap.range (prolong 𝕜 m n) ↔ ∀ i : m, WithLp.ofLp v (Sum.inl i) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i
    simp [prolong_apply]
  · intro h
    refine ⟨WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr), ?_⟩
    rw [prolong_toLp]
    refine WithLp.ofLp_injective 2 (funext fun j => ?_)
    cases j with
    | inl i => exact (h i).symm
    | inr j => rfl

section Isometry

variable (𝕜 m n)
variable [Fintype m]

/-- **The prolongation preserves inner products**: it is an isometry of `EuclideanSpace 𝕜 n` onto
the second block of coordinates. -/
theorem inner_prolong_prolong (a b : EuclideanSpace 𝕜 n) :
    inner 𝕜 (prolong 𝕜 m n a) (prolong 𝕜 m n b) = (inner 𝕜 a b : 𝕜) := by
  rw [prolong_apply, prolong_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type]

/-- The prolongation as a linear isometry. -/
noncomputable def prolongIsometry : EuclideanSpace 𝕜 n →ₗᵢ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) :=
  (prolong 𝕜 m n).isometryOfInner (inner_prolong_prolong 𝕜 m n)

@[simp]
theorem coe_prolongIsometry : ⇑(prolongIsometry 𝕜 m n) = prolong 𝕜 m n := rfl

variable {𝕜 m n}

/-- The prolongation preserves norms. -/
@[simp]
theorem norm_prolong (a : EuclideanSpace 𝕜 n) : ‖prolong 𝕜 m n a‖ = ‖a‖ :=
  (prolongIsometry 𝕜 m n).norm_map a

end Isometry

section RestrictOp

variable (𝕜 m n)
variable [Fintype m] [DecidableEq m]

/-- **The interface restriction operator** `R_y` of [saad2003iterative], Proposition 14.1: it sends
a vector of `EuclideanSpace 𝕜 (m ⊕ n)` to its interface block. -/
noncomputable def restrict : EuclideanSpace 𝕜 (m ⊕ n) →ₗ[𝕜] EuclideanSpace 𝕜 n :=
  Matrix.toEuclideanLin (restrictMatrix 𝕜 m n)

variable {𝕜 m n}

/-- The restriction reads off the second block. -/
theorem restrict_apply (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    restrict 𝕜 m n v = WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) := by
  simp [restrict, Matrix.toLpLin_apply]

/-- **`R_y R_yᵀ = I`**: restricting a prolonged vector returns it. -/
@[simp]
theorem restrict_prolong (y : EuclideanSpace 𝕜 n) : restrict 𝕜 m n (prolong 𝕜 m n y) = y := by
  rw [restrict_apply, prolong_apply]
  simp

/-- **`R_y R_yᵀ = I`**, as an identity of operators. -/
theorem restrict_comp_prolong : restrict 𝕜 m n ∘ₗ prolong 𝕜 m n = LinearMap.id :=
  LinearMap.ext fun y => restrict_prolong y

/-- **The prolongation is the adjoint of the restriction**: `R_y` and `R_yᵀ` in the notation of
[saad2003iterative], Proposition 14.1. -/
theorem adjoint_restrict : LinearMap.adjoint (restrict 𝕜 m n) = prolong 𝕜 m n :=
  ((LinearMap.eq_adjoint_iff (prolong 𝕜 m n) (restrict 𝕜 m n)).2 fun x y => by
    rw [prolong_apply, EuclideanSpace.inner_eq_star_dotProduct, restrict_apply,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fintype.sum_sum_type]).symm

end RestrictOp

end Restrict

/-! ### Krylov subspaces under an intertwiner -/

section Intertwine

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {P : N →ₗ[R] M} {T : Module.End R M} {S : Module.End R N}

/-- An intertwiner `T P = P S` commutes with the powers: `T^i P = P S^i`. -/
theorem pow_apply_of_comp_eq (h : T ∘ₗ P = P ∘ₗ S) (i : ℕ) (v : N) :
    (T ^ i) (P v) = P ((S ^ i) v) := by
  have hTP : ∀ w : N, T (P w) = P (S w) := fun w => LinearMap.congr_fun h w
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hTP, pow_succ', Module.End.mul_apply]

/-- **An intertwiner carries Krylov subspaces to Krylov subspaces**: if `T P = P S` then
`𝒦_k(T, P v) = P 𝒦_k(S, v)`.  This is the invariance statement behind every "the method on the
reduced system is the method on the full system" theorem. -/
theorem krylov_subspace_map_of_comp_eq (h : T ∘ₗ P = P ∘ₗ S) (v : N) (k : ℕ) :
    Krylov.subspace T (P v) k = (Krylov.subspace S v k).map P := by
  rw [Krylov.subspace, Krylov.subspace, Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(S ^ (i : ℕ)) v, ⟨i, rfl⟩, (pow_apply_of_comp_eq h i v).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, pow_apply_of_comp_eq h i v⟩

end Intertwine

/-! ### Projection specifications under an intertwining isometry -/

section Transfer

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
variable {P : Y →ₗ[𝕜] X} {T : X →ₗ[𝕜] X} {S : Y →ₗ[𝕜] Y} {b u₀ : X} {g y₀ : Y}

/-- A vector of the affine space `u₀ + P K` is `u₀ + P w` for some `w ∈ K`. -/
theorem exists_mem_of_sub_mem_map {K : Submodule 𝕜 Y} {u : X} (hu : u - u₀ ∈ K.map P) :
    ∃ w ∈ K, u = u₀ + P w := by
  obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.1 hu
  exact ⟨w, hw, by rw [hwu]; abel⟩

/-- An inner-product-preserving map identifies orthogonality against a subspace with orthogonality
against its image. -/
theorem mem_orthogonal_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (K : Submodule 𝕜 Y) (z : Y) : P z ∈ (K.map P)ᗮ ↔ z ∈ Kᗮ := by
  constructor
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [← hP u z]
    exact (Submodule.mem_orthogonal _ _).1 h _ (Submodule.mem_map_of_mem hu)
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [hP u z]
    exact (Submodule.mem_orthogonal _ _).1 h _ hu

/-- The residual of the big system at `u₀ + P w` is `P` of the residual of the small system at
`y₀ + w`. -/
theorem residual_map (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (w : Y) :
    b - T (u₀ + P w) = P (g - S (y₀ + w)) := by
  have hTP : T (P w) = P (S w) := LinearMap.congr_fun h w
  calc b - T (u₀ + P w) = b - T u₀ - T (P w) := by rw [map_add]; abel
    _ = P (g - S y₀) - P (S w) := by rw [hres, hTP]
    _ = P (g - S (y₀ + w)) := by rw [map_add, ← map_sub]; congr 1; abel

/-- **Minimal-residual iterates correspond under an intertwining isometry.**  If `T P = P S`, if `P`
preserves inner products, and if the initial residual of the big system is `P` of that of the small
one, then `u₀ + P (y - y₀)` is a minimal-residual iterate for `T u = b` over `u₀ + P K` exactly when
`y` is one for `S y = g` over `y₀ + K`: the two minimizations are the same minimization. -/
theorem isMinResidual_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (K : Submodule 𝕜 Y) (y : Y) :
    IsMinResidual T b u₀ (K.map P) (u₀ + P (y - y₀)) ↔ IsMinResidual S g y₀ K y := by
  have hinj : Function.Injective P := (LinearMap.isometryOfInner P hP).injective
  have hnorm : ∀ w : Y, ‖b - T (u₀ + P w)‖ = ‖g - S (y₀ + w)‖ := fun w => by
    rw [residual_map h hres w]
    exact (LinearMap.isometryOfInner P hP).norm_map _
  constructor
  · intro hx
    refine ⟨?_, fun y' hy' => ?_⟩
    · have hmem := hx.mem
      rw [add_sub_cancel_left] at hmem
      obtain ⟨w, hw, hwP⟩ := Submodule.mem_map.1 hmem
      rwa [hinj hwP] at hw
    · have hle := hx.min (u₀ + P (y' - y₀))
        (by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy')
      rwa [hnorm (y - y₀), hnorm (y' - y₀), add_sub_cancel, add_sub_cancel] at hle
  · intro hy
    refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy.mem, fun u hu => ?_⟩
    obtain ⟨w, hw, rfl⟩ := exists_mem_of_sub_mem_map hu
    rw [hnorm (y - y₀), hnorm w, add_sub_cancel]
    exact hy.min (y₀ + w) (by rw [add_sub_cancel_left]; exact hw)

/-- **Galerkin iterates correspond under an intertwining isometry**, the twin of
`DomainDecomposition.isMinResidual_map_iff`. -/
theorem isGalerkin_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (K : Submodule 𝕜 Y) (y : Y) :
    IsGalerkin T b u₀ (K.map P) (u₀ + P (y - y₀)) ↔ IsGalerkin S g y₀ K y := by
  have hinj : Function.Injective P := (LinearMap.isometryOfInner P hP).injective
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hmem := hx.mem
      rw [add_sub_cancel_left] at hmem
      obtain ⟨w, hw, hwP⟩ := Submodule.mem_map.1 hmem
      rwa [hinj hwP] at hw
    · have horth := hx.orth
      rw [residual_map h hres (y - y₀), add_sub_cancel] at horth
      exact (mem_orthogonal_map_iff hP K _).1 horth
  · intro hy
    refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy.mem, ?_⟩
    rw [residual_map h hres (y - y₀), add_sub_cancel]
    exact (mem_orthogonal_map_iff hP K _).2 hy.orth

/-- Every minimal-residual iterate of the big system over `u₀ + P K` comes from one of the small
system; `DomainDecomposition.isMinResidual_map_iff` read from the other side. -/
theorem exists_isMinResidual_of_isMinResidual_map
    (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜)) (h : T ∘ₗ P = P ∘ₗ S)
    (hres : b - T u₀ = P (g - S y₀)) {K : Submodule 𝕜 Y} {u : X}
    (hu : IsMinResidual T b u₀ (K.map P) u) : ∃ y, IsMinResidual S g y₀ K y ∧ u = u₀ + P (y - y₀) := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_sub_mem_map hu.mem
  refine ⟨y₀ + w, ?_, by rw [add_sub_cancel_left]⟩
  rw [← isMinResidual_map_iff hP h hres K (y₀ + w), add_sub_cancel_left]
  exact hu

/-- The Krylov subspace of the big system at the initial residual is the image of the Krylov
subspace of the small system at its own initial residual. -/
theorem krylov_subspace_residual_eq_map (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀))
    (k : ℕ) :
    Krylov.subspace T (b - T u₀) k = (Krylov.subspace S (g - S y₀) k).map P := by
  rw [hres]
  exact krylov_subspace_map_of_comp_eq h _ k

/-- **The minimal-residual Krylov iterates of the two systems correspond.**  The specialization of
`DomainDecomposition.isMinResidual_map_iff` to the Krylov subspaces generated by the initial residuals,
which is the form in which a Krylov method is specified. -/
theorem isMinResidualIterate_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) (y : Y) :
    Krylov.IsMinResidualIterate T b u₀ k (u₀ + P (y - y₀)) ↔ Krylov.IsMinResidualIterate S g y₀ k y := by
  have hK := krylov_subspace_residual_eq_map h hres k
  constructor
  · intro hx
    have hx' : IsMinResidual T b u₀ (Krylov.subspace T (b - T u₀) k) (u₀ + P (y - y₀)) := hx
    rw [hK] at hx'
    exact (isMinResidual_map_iff hP h hres _ y).1 hx'
  · intro hy
    have hy' : IsMinResidual S g y₀ (Krylov.subspace S (g - S y₀) k) y := hy
    have hx' := (isMinResidual_map_iff hP h hres _ y).2 hy'
    rw [← hK] at hx'
    exact hx'

/-- **The Galerkin Krylov iterates of the two systems correspond**, the twin of
`DomainDecomposition.isMinResidualIterate_map_iff`. -/
theorem isGalerkinIterate_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) (y : Y) :
    Krylov.IsGalerkinIterate T b u₀ k (u₀ + P (y - y₀)) ↔ Krylov.IsGalerkinIterate S g y₀ k y := by
  have hK := krylov_subspace_residual_eq_map h hres k
  constructor
  · intro hx
    have hx' : IsGalerkin T b u₀ (Krylov.subspace T (b - T u₀) k) (u₀ + P (y - y₀)) := hx
    rw [hK] at hx'
    exact (isGalerkin_map_iff hP h hres _ y).1 hx'
  · intro hy
    have hy' : IsGalerkin S g y₀ (Krylov.subspace S (g - S y₀) k) y := hy
    have hx' := (isGalerkin_map_iff hP h hres _ y).2 hy'
    rw [← hK] at hx'
    exact hx'

/-- **Every minimal-residual Krylov iterate of the big system has the form `u₀ + P (y - y₀)`**, with
`y` the corresponding iterate of the small system; `DomainDecomposition.isMinResidualIterate_map_iff`
read from the other side. -/
theorem exists_isMinResidualIterate_of_isMinResidualIterate_map
    (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜)) (h : T ∘ₗ P = P ∘ₗ S)
    (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) {u : X} (hu : Krylov.IsMinResidualIterate T b u₀ k u) :
    ∃ y, Krylov.IsMinResidualIterate S g y₀ k y ∧ u = u₀ + P (y - y₀) := by
  have hu' : IsMinResidual T b u₀ (Krylov.subspace T (b - T u₀) k) u := hu
  rw [krylov_subspace_residual_eq_map h hres k] at hu'
  obtain ⟨y, hy, hyu⟩ := exists_isMinResidual_of_isMinResidual_map hP h hres hu'
  exact ⟨y, hy, hyu⟩

end Transfer

/-! ### The block preconditioners of a two-block system -/

section Block

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}
  {LS US : Matrix n n R}

/-- **The block lower triangular left preconditioner** `L_A = (I 0; F B⁻¹ L_S)` of
[saad2003iterative], (14.49) and (14.55).  Taking `L_S = I` gives (14.49), and a factor `L_S` of an
approximate factorization `S ≈ L_S U_S` of the Schur complement gives (14.55). -/
noncomputable def blockLower (B : Matrix m m R) (F : Matrix n m R) (LS : Matrix n n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks 1 0 (F * B⁻¹) LS

/-- **The block upper triangular right preconditioner** `U_A = (B E; 0 U_S)` of
[saad2003iterative], (14.49) and (14.55). -/
def blockUpper (B : Matrix m m R) (E : Matrix m n R) (US : Matrix n n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks B E 0 US

/-- **The right-hand side of the reduced interface system**, `g' = g - F B⁻¹ f` of
[saad2003iterative], (14.4). -/
noncomputable def reducedRhs (B : Matrix m m R) (F : Matrix n m R) (f : m → R) (g : n → R) :
    n → R :=
  g - F *ᵥ (B⁻¹ *ᵥ f)

/-- **A consistent initial guess** `(B⁻¹(f - E y); y)` of [saad2003iterative], (14.50) and (14.56):
the vectors whose interior residual `f - B x - E y` vanishes.  Every iterate of the
block-preconditioned method started at such a guess is again of this form
(`DomainDecomposition.blockUpper_inv_mulVec`), which is (14.51) there. -/
noncomputable def consistentGuess (B : Matrix m m R) (E : Matrix m n R) (f : m → R) (y : n → R) :
    m ⊕ n → R :=
  Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y

/-- **The preconditioned Schur complement** `L_S⁻¹ S U_S⁻¹`, the interface block of the
split-preconditioned system matrix. -/
noncomputable def precondSchurComplement (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) (LS US : Matrix n n R) : Matrix n n R :=
  LS⁻¹ * (Matrix.fromBlocks B E F C).schurComplement * US⁻¹

/-- **The split-preconditioned system matrix** `L_A⁻¹ A U_A⁻¹` of [saad2003iterative], (14.53). -/
noncomputable def precondMatrix (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) (LS US : Matrix n n R) : Matrix (m ⊕ n) (m ⊕ n) R :=
  (blockLower B F LS)⁻¹ * Matrix.fromBlocks B E F C * (blockUpper B E US)⁻¹

/-- The left preconditioner is nonsingular exactly when its interface block is. -/
theorem isUnit_blockLower (hLS : IsUnit LS) : IsUnit (blockLower B F LS) := by
  rw [blockLower, Matrix.isUnit_fromBlocks_zero₁₂]
  exact ⟨isUnit_one, hLS⟩

/-- The right preconditioner is nonsingular exactly when its two diagonal blocks are. -/
theorem isUnit_blockUpper (hB : IsUnit B) (hUS : IsUnit US) : IsUnit (blockUpper B E US) := by
  rw [blockUpper, Matrix.isUnit_fromBlocks_zero₂₁]
  exact ⟨hB, hUS⟩

/-- The inverse of the left preconditioner, by block triangular inversion. -/
theorem inv_blockLower (hLS : IsUnit LS) :
    (blockLower B F LS)⁻¹ = Matrix.fromBlocks 1 0 (-(LS⁻¹ * (F * B⁻¹))) LS⁻¹ := by
  rw [blockLower, Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (iff_of_true isUnit_one hLS)]
  simp

/-- The inverse of the right preconditioner, by block triangular inversion. -/
theorem inv_blockUpper (hB : IsUnit B) (hUS : IsUnit US) :
    (blockUpper B E US)⁻¹ = Matrix.fromBlocks B⁻¹ (-(B⁻¹ * E * US⁻¹)) 0 US⁻¹ := by
  rw [blockUpper, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hB hUS)]

/-- **The block factorization** `A = L_A (I ⊕ L_S⁻¹ S U_S⁻¹) U_A` of [saad2003iterative], (14.52)
and (14.58). -/
theorem fromBlocks_eq_blockLower_mul (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    Matrix.fromBlocks B E F C
      = blockLower B F LS * Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US)
        * blockUpper B E US := by
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  have hLL : LS * LS⁻¹ = 1 := Matrix.mul_nonsing_inv LS ((Matrix.isUnit_iff_isUnit_det LS).1 hLS)
  have hUU : US⁻¹ * US = 1 := Matrix.nonsing_inv_mul US ((Matrix.isUnit_iff_isUnit_det US).1 hUS)
  have h1 : F * B⁻¹ * B = F := by rw [Matrix.mul_assoc, hBB, Matrix.mul_one]
  have h2 : LS * (LS⁻¹ * (C - F * B⁻¹ * E) * US⁻¹) * US = C - F * B⁻¹ * E := by
    rw [← mul_assoc LS _ US⁻¹, ← mul_assoc LS LS⁻¹, hLL, one_mul, mul_assoc, hUU, mul_one]
  rw [blockLower, blockUpper, precondSchurComplement, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add,
    Matrix.schurComplement_fromBlocks]
  rw [h1, h2]
  congr 1
  abel

/-- **The split-preconditioned system matrix is block diagonal**,
`L_A⁻¹ A U_A⁻¹ = I ⊕ L_S⁻¹ S U_S⁻¹` ([saad2003iterative], (14.53)).  This is the whole content of
the block preconditioning: the interface block of the preconditioned operator is the preconditioned
Schur complement, and the interior block is the identity. -/
theorem precondMatrix_eq (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    precondMatrix B E F C LS US
      = Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US) := by
  have hL : (blockLower B F LS)⁻¹ * blockLower B F LS = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_blockLower hLS))
  have hU : blockUpper B E US * (blockUpper B E US)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_blockUpper hB hUS))
  rw [precondMatrix, fromBlocks_eq_blockLower_mul hB hLS hUS, ← mul_assoc, ← mul_assoc, hL, one_mul,
    mul_assoc, hU, mul_one]

omit [DecidableEq n] in
/-- The right preconditioner sends a consistent guess to `(f; U_S y)`. -/
theorem blockUpper_mulVec_consistentGuess (hB : IsUnit B) (f : m → R) (y : n → R) :
    blockUpper B E US *ᵥ consistentGuess B E f y = Sum.elim f (US *ᵥ y) := by
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  rw [blockUpper, consistentGuess, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add]
  refine congrArg₂ Sum.elim ?_ rfl
  rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  abel

/-- **[saad2003iterative], (14.51)**: the inverse of the right preconditioner sends `(f; U_S y)`
back to the consistent guess at `y`.  Together with
`DomainDecomposition.blockUpper_mulVec_consistentGuess` this says that `U_A` is a bijection between
the consistent guesses and the vectors with first block `f`, which is why every iterate of the
preconditioned method has the form `x_m = (B⁻¹(f - E y_m); y_m)`. -/
theorem blockUpper_inv_mulVec (hB : IsUnit B) (hUS : IsUnit US) (f : m → R) (y : n → R) :
    (blockUpper B E US)⁻¹ *ᵥ Sum.elim f (US *ᵥ y) = consistentGuess B E f y := by
  have hUU : US⁻¹ * US = 1 := Matrix.nonsing_inv_mul US ((Matrix.isUnit_iff_isUnit_det US).1 hUS)
  rw [inv_blockUpper hB hUS, consistentGuess, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  refine congrArg₂ Sum.elim ?_ rfl
  rw [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_sub, Matrix.mul_assoc, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hUU, Matrix.mul_one]
  abel

/-- The left preconditioner turns the right-hand side into `(f; L_S⁻¹ g')`. -/
theorem blockLower_inv_mulVec (hLS : IsUnit LS) (f : m → R) (g : n → R) :
    (blockLower B F LS)⁻¹ *ᵥ Sum.elim f g = Sum.elim f (LS⁻¹ *ᵥ reducedRhs B F f g) := by
  rw [inv_blockLower hLS, reducedRhs, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec, add_zero]
  refine congrArg₂ Sum.elim rfl ?_
  rw [Matrix.mulVec_sub, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  abel

end Block

/-! ### The interface reduction of a block-preconditioned Krylov method -/

section Reduction

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]
variable {B : Matrix m m 𝕜} {E : Matrix m n 𝕜} {F : Matrix n m 𝕜} {C : Matrix n n 𝕜}
  {LS US : Matrix n n 𝕜}

/-- **A block lower triangular matrix leaves the interface block invariant**, and acts there as its
own trailing diagonal block: `(D 0; Z S) R_yᵀ = R_yᵀ S`. -/
theorem toEuclideanLin_fromBlocks_comp_prolong (D : Matrix m m 𝕜) (Z : Matrix n m 𝕜)
    (S : Matrix n n 𝕜) :
    Matrix.toEuclideanLin (Matrix.fromBlocks D 0 Z S) ∘ₗ prolong 𝕜 m n
      = prolong 𝕜 m n ∘ₗ Matrix.toEuclideanLin S :=
  LinearMap.ext fun y => by
    have h : Matrix.toEuclideanLin (Matrix.fromBlocks D 0 Z S) (prolong 𝕜 m n y)
        = WithLp.toLp 2 (Matrix.fromBlocks D 0 Z S *ᵥ Sum.elim (0 : m → 𝕜) (WithLp.ofLp y)) := by
      rw [prolong_apply]; rfl
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h, Matrix.fromBlocks_mulVec]
    simp [prolong_toLp, Matrix.toLpLin_apply]

omit [Fintype m] [DecidableEq m] in
/-- The transformed iterate `U_A x` of a consistent `x`, split off the initial one: `(f; U_S y)` is
`(f; U_S y₀)` plus the prolongation of `U_S y - U_S y₀`. -/
theorem toLp_sumElim_eq_add_prolong (f : m → 𝕜) (w w₀ : n → 𝕜) :
    (WithLp.toLp 2 (Sum.elim f w) : EuclideanSpace 𝕜 (m ⊕ n))
      = WithLp.toLp 2 (Sum.elim f w₀)
        + prolong 𝕜 m n (WithLp.toLp 2 w - WithLp.toLp 2 w₀) := by
  rw [show (WithLp.toLp 2 w - WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 n) = WithLp.toLp 2 (w - w₀) from
    rfl, prolong_toLp]
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  cases j with
  | inl i => simp
  | inr j => simp

/-- **The initial residual of the block-preconditioned system at a consistent initial guess lies in
the interface block** ([saad2003iterative], (14.53)): it is `(0; L_S⁻¹ (g' - S y₀))`. -/
theorem residual_consistentGuess (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : m → 𝕜)
    (g y₀ : n → 𝕜) :
    (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g) : EuclideanSpace 𝕜 (m ⊕ n))
        - Matrix.toEuclideanLin (precondMatrix B E F C LS US)
          (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀))
      = prolong 𝕜 m n (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
          - Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
            (WithLp.toLp 2 (US *ᵥ y₀))) := by
  rw [blockLower_inv_mulVec hLS, blockUpper_mulVec_consistentGuess hB,
    precondMatrix_eq hB hLS hUS]
  have hT : Matrix.toEuclideanLin (Matrix.fromBlocks 1 0 0
        (precondSchurComplement B E F C LS US)) (WithLp.toLp 2 (Sum.elim f (US *ᵥ y₀)))
      = WithLp.toLp 2 (Sum.elim f (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀))) := by
    change WithLp.toLp 2 (Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US) *ᵥ
      Sum.elim f (US *ᵥ y₀)) = _
    rw [Matrix.fromBlocks_mulVec]
    simp
  rw [hT]
  have hS : Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
      (WithLp.toLp 2 (US *ᵥ y₀))
      = WithLp.toLp 2 (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) := rfl
  rw [hS, show (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
      - WithLp.toLp 2 (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) :
        EuclideanSpace 𝕜 n)
    = WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g
      - precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) from rfl, prolong_toLp]
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  cases j with
  | inl i => simp
  | inr j => simp

/-- **The block-preconditioned operator leaves the interface block invariant**, and acts there as
the preconditioned Schur complement: `L_A⁻¹ A U_A⁻¹ R_yᵀ = R_yᵀ (L_S⁻¹ S U_S⁻¹)`.  This is the
intertwining hypothesis of the transfer theorems. -/
theorem precondMatrix_comp_prolong (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    Matrix.toEuclideanLin (precondMatrix B E F C LS US) ∘ₗ prolong 𝕜 m n
      = prolong 𝕜 m n ∘ₗ Matrix.toEuclideanLin (precondSchurComplement B E F C LS US) := by
  rw [precondMatrix_eq hB hLS hUS]
  exact toEuclideanLin_fromBlocks_comp_prolong 1 0 _

/-- **[saad2003iterative], (14.54)**: with a consistent initial guess, the Krylov subspace of the
block-preconditioned full system is the prolongation of the Krylov subspace of the reduced system.
Every Krylov vector has a vanishing interior block, which is the whole of the argument. -/
theorem krylov_subspace_eq_map_of_consistent (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : m → 𝕜) (g y₀ : n → 𝕜) (k : ℕ) :
    Krylov.subspace (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        ((WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g) : EuclideanSpace 𝕜 (m ⊕ n))
          - Matrix.toEuclideanLin (precondMatrix B E F C LS US)
            (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀))) k
      = (Krylov.subspace (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
            - Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
              (WithLp.toLp 2 (US *ᵥ y₀))) k).map (prolong 𝕜 m n) := by
  exact krylov_subspace_residual_eq_map (precondMatrix_comp_prolong hB hLS hUS)
    (residual_consistentGuess hB hLS hUS f g y₀) k

/-- **[saad2003iterative], Propositions 14.11 and 14.12.**  Run a minimal-residual Krylov method on
the full system preconditioned on the left by `L_A` and on the right by `U_A`, from a consistent
initial guess `x₀ = (B⁻¹(f - E y₀); y₀)`; then `x = (B⁻¹(f - E y); y)` is its iterate at step `k`
exactly when `y` is the iterate of the same method on the reduced system `S y = g'` preconditioned
on the left by `L_S` and on the right by `U_S`, from `y₀`.  Both sides are written in the variable
the split-preconditioned method actually iterates on, `u = U_A x` on the left and `w = U_S y` on the
right.

Taking `L_S = U_S = I` is Proposition 14.11 and the general case is Proposition 14.12. -/
theorem isMinResidual_iff_isMinResidual_schurComplement (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : m → 𝕜) (g y₀ y : n → 𝕜) (k : ℕ) :
    Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResidualIterate
        (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  rw [blockUpper_mulVec_consistentGuess hB, blockUpper_mulVec_consistentGuess hB,
    toLp_sumElim_eq_add_prolong f (US *ᵥ y) (US *ᵥ y₀),
    ← blockUpper_mulVec_consistentGuess (E := E) (US := US) hB f y₀]
  exact isMinResidualIterate_map_iff (inner_prolong_prolong 𝕜 m n) hcomm
    (residual_consistentGuess hB hLS hUS f g y₀) k _

/-- **[saad2003iterative], Proposition 14.11 and (14.51), in the direction the book states them**:
*every* minimal-residual iterate of the block-preconditioned full system, started from a consistent
initial guess, is `U_A x` for a consistent `x = (B⁻¹(f - E y); y)`, and that `y` is the iterate of
the same method on the reduced system.  Together with
`DomainDecomposition.blockUpper_inv_mulVec`, which recovers `x` from `U_A x`, this is the book's
"produces iterates of the form (14.51)". -/
theorem exists_isMinResidual_schurComplement (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : m → 𝕜) (g y₀ : n → 𝕜) (k : ℕ) {u : EuclideanSpace 𝕜 (m ⊕ n)}
    (hu : Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
      (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : n → 𝕜,
      Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
          (WithLp.toLp 2 (US *ᵥ y))
        ∧ u = WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  obtain ⟨w, hw, hwu⟩ := exists_isMinResidualIterate_of_isMinResidualIterate_map
    (inner_prolong_prolong 𝕜 m n) hcomm (residual_consistentGuess hB hLS hUS f g y₀) k hu
  have hUS' : US *ᵥ (US⁻¹ *ᵥ WithLp.ofLp w) = WithLp.ofLp w := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv US ((Matrix.isUnit_iff_isUnit_det US).1 hUS), Matrix.one_mulVec]
  refine ⟨US⁻¹ *ᵥ WithLp.ofLp w, by rwa [hUS'], ?_⟩
  rw [blockUpper_mulVec_consistentGuess hB, hUS', hwu,
    blockUpper_mulVec_consistentGuess (E := E) (US := US) hB,
    toLp_sumElim_eq_add_prolong f (WithLp.ofLp w) (US *ᵥ y₀)]

/-- **The Galerkin twin of `DomainDecomposition.isMinResidual_iff_isMinResidual_schurComplement`**: the same
correspondence for the orthogonal-projection specification, so that [saad2003iterative],
Propositions 14.11 and 14.12 apply to FOM, CG and the Lanczos method as well as to GMRES and
MINRES. -/
theorem isGalerkin_iff_isGalerkin_schurComplement (hB : IsUnit B) (hLS : IsUnit LS)
    (hUS : IsUnit US) (f : m → 𝕜) (g y₀ y : n → 𝕜) (k : ℕ) :
    Krylov.IsGalerkinIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate
        (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  rw [blockUpper_mulVec_consistentGuess hB, blockUpper_mulVec_consistentGuess hB,
    toLp_sumElim_eq_add_prolong f (US *ᵥ y) (US *ᵥ y₀),
    ← blockUpper_mulVec_consistentGuess (E := E) (US := US) hB f y₀]
  exact isGalerkinIterate_map_iff (inner_prolong_prolong 𝕜 m n) hcomm
    (residual_consistentGuess hB hLS hUS f g y₀) k _

end Reduction

/-! ### The preconditioner induced on the interface -/

section Induced

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- **The induced preconditioner** `M_S = (R_y M_A⁻¹ R_yᵀ)⁻¹` of [saad2003iterative], (14.46): the
preconditioner that a preconditioner `M_A` of the whole matrix induces on the interface system.
Applying `M_S⁻¹` to a vector `v` means solving `M_A (x; y) = (0; v)` approximately and keeping `y`.
-/
noncomputable def inducedPreconditioner (MA : Matrix (m ⊕ n) (m ⊕ n) R) : Matrix n n R :=
  ((MA⁻¹).toBlocks₂₂)⁻¹

/-- The induced preconditioner written with the interface restriction, as in
[saad2003iterative], (14.46). -/
theorem inducedPreconditioner_eq_inv_restrict_mul (MA : Matrix (m ⊕ n) (m ⊕ n) R) :
    inducedPreconditioner MA = (restrictMatrix R m n * MA⁻¹ * prolongMatrix R m n)⁻¹ := by
  rw [inducedPreconditioner, restrictMatrix_mul_mul_prolongMatrix]

variable {LB UB : Matrix m m R} {X : Matrix n m R} {Y : Matrix m n R} {LS US : Matrix n n R}

/-- The interface block of the inverse of a block triangular product is `U_S⁻¹ L_S⁻¹`: the
computation displayed in [saad2003iterative], §14.4.1, where the other blocks are starred out. -/
theorem toBlocks₂₂_inv_fromBlocks_mul (hLB : IsUnit LB) (hLS : IsUnit LS) (hUB : IsUnit UB)
    (hUS : IsUnit US) :
    (((Matrix.fromBlocks LB 0 X LS * Matrix.fromBlocks UB Y 0 US)⁻¹).toBlocks₂₂)
      = US⁻¹ * LS⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hUB hUS),
    Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (iff_of_true hLB hLS),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
  simp

/-- **[saad2003iterative], Proposition 14.10.**  If a preconditioner of the whole matrix is given in
block triangular factored form `M_A = L_A U_A`, with `L_A` block lower triangular and `U_A` block
upper triangular, then the preconditioner it induces on the interface is the product of the trailing
diagonal blocks of the two factors, `M_S = L_S U_S`.  Written with the interface restriction
(`DomainDecomposition.restrictMatrix_mul_mul_prolongMatrix`), `L_S = R_y L_A R_yᵀ` and
`U_S = R_y U_A R_yᵀ`: the `L` and `U` factors of `M_S` are the `(2,2)` blocks of the `L` and `U`
factors of `M_A`. -/
theorem inducedPreconditioner_eq (hLB : IsUnit LB) (hLS : IsUnit LS) (hUB : IsUnit UB)
    (hUS : IsUnit US) :
    inducedPreconditioner (Matrix.fromBlocks LB 0 X LS * Matrix.fromBlocks UB Y 0 US)
      = LS * US := by
  rw [inducedPreconditioner, toBlocks₂₂_inv_fromBlocks_mul hLB hLS hUB hUS, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hLS),
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hUS)]

end Induced

end DomainDecomposition
