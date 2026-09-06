import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.LinearSolve.Projection.Additive

/-!
# Coordinate subspaces of `EuclideanSpace`

The trial and test spaces of a *block* relaxation are coordinate subspaces: the vectors supported on
a set `s` of indices (`EuclideanSpace.coordSubspace`), and in particular the vectors supported on
one fibre of a block labelling `π` (`EuclideanSpace.blockSubspace`).  Two facts are what the block
theory needs, and both are immediate from the coordinate form of the Euclidean inner product:
membership is "vanishing off `s`" and membership in the orthogonal complement is "vanishing on `s`"
(`EuclideanSpace.mem_orthogonal_coordSubspace`).  Together they turn a Petrov–Galerkin condition for
such a pair into a statement about individual entries of a matrix-vector product, which is how
[saad2003iterative] §5.4 identifies block Jacobi with the additive projection process and block
Gauss–Seidel with the multiplicative one.
-/

namespace EuclideanSpace

variable (𝕜 : Type*) [RCLike 𝕜] {n ι : Type*}

/-- The **coordinate subspace** on a set `s` of indices: the vectors of `EuclideanSpace 𝕜 n` whose
entries vanish outside `s`. -/
def coordSubspace (s : Set n) : Submodule 𝕜 (EuclideanSpace 𝕜 n) where
  carrier := {v | ∀ j ∉ s, v j = 0}
  add_mem' hu hv j hj := by rw [PiLp.add_apply, hu j hj, hv j hj, add_zero]
  zero_mem' j _ := rfl
  smul_mem' c _ hv j hj := by rw [PiLp.smul_apply, hv j hj, smul_zero]

/-- The **block subspace** of a labelling `π : n → ι`: the coordinate subspace of the fibre over the
label `i`, that is the vectors whose entries vanish outside the `i`-th block. -/
def blockSubspace (π : n → ι) (i : ι) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  coordSubspace 𝕜 (π ⁻¹' {i})

variable {𝕜}

@[simp]
theorem mem_coordSubspace {s : Set n} {v : EuclideanSpace 𝕜 n} :
    v ∈ coordSubspace 𝕜 s ↔ ∀ j ∉ s, v j = 0 := Iff.rfl

@[simp]
theorem mem_blockSubspace {π : n → ι} {i : ι} {v : EuclideanSpace 𝕜 n} :
    v ∈ blockSubspace 𝕜 π i ↔ ∀ j, π j ≠ i → v j = 0 := Iff.rfl

variable [DecidableEq n]

/-- A basis vector of an index of `s` lies in the coordinate subspace of `s`. -/
theorem single_mem_coordSubspace {s : Set n} {j : n} (hj : j ∈ s) (a : 𝕜) :
    EuclideanSpace.single j a ∈ coordSubspace 𝕜 s := fun k hk => by
  have hkj : k ≠ j := by rintro rfl; exact hk hj
  simp [hkj]

variable [Fintype n]

omit [DecidableEq n] in
/-- **The orthogonal complement of a coordinate subspace is the complementary one**: a vector is
orthogonal to everything supported on `s` exactly when it vanishes on `s`. -/
theorem mem_orthogonal_coordSubspace {s : Set n} {v : EuclideanSpace 𝕜 n} :
    v ∈ (coordSubspace 𝕜 s)ᗮ ↔ ∀ j ∈ s, v j = 0 := by
  classical
  refine ⟨fun h j hj => ?_, fun h => (Submodule.mem_orthogonal _ _).2 fun u hu => ?_⟩
  · have := (Submodule.mem_orthogonal _ _).1 h (EuclideanSpace.single j 1)
      (single_mem_coordSubspace hj 1)
    rwa [EuclideanSpace.inner_single_left, map_one, one_mul] at this
  · rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ s
    · rw [h j hj, inner_zero_right]
    · rw [hu j hj, inner_zero_left]

omit [DecidableEq n] in
/-- A vector is orthogonal to the `i`-th block subspace exactly when it vanishes on that block. -/
theorem mem_orthogonal_blockSubspace {π : n → ι} {i : ι} {v : EuclideanSpace 𝕜 n} :
    v ∈ (blockSubspace 𝕜 π i)ᗮ ↔ ∀ j, π j = i → v j = 0 :=
  mem_orthogonal_coordSubspace

end EuclideanSpace
