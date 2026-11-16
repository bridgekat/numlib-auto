/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Projection.Additive

/-!
# Coordinate subspaces of Euclidean space

In a *block* relaxation method the trial and test spaces are coordinate subspaces of $\mathbb{K}^n$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ and the index set $n$ is any type. For a set $s$
of indices, the coordinate subspace of $s$ consists of the vectors whose entries vanish outside $s$.
For a block labelling $\pi : n \to I$ and a label $i$, the block subspace is the coordinate subspace
of the block $\pi^{-1}(i)$. The block theory needs two facts, and both follow at once from the
coordinate form of the Euclidean inner product: a vector lies in the coordinate subspace of $s$ if
and only if it vanishes off $s$, and it lies in the orthogonal complement if and only if it vanishes
on $s$. With these facts, a Petrov–Galerkin condition for a pair of such subspaces becomes a
statement about individual entries of a matrix-vector product. This is how [saad2003iterative] §5.4
identifies block Jacobi with the additive projection process and block Gauss–Seidel with the
multiplicative one.

## Main definitions

* `EuclideanSpace.coordSubspace`: the vectors whose entries vanish outside a set $s$ of indices.
* `EuclideanSpace.blockSubspace`: the vectors whose entries vanish outside the block $\pi^{-1}(i)$.

## Main results

* `EuclideanSpace.mem_orthogonal_coordSubspace`: a vector is orthogonal to the coordinate subspace
  of $s$ if and only if it vanishes on $s$.
* `EuclideanSpace.mem_orthogonal_blockSubspace`: a vector is orthogonal to the $i$-th block subspace
  if and only if it vanishes on the $i$-th block.

## Implementation notes

* The index type $n$ is arbitrary in the definitions. The results about orthogonal complements need
  $n$ to be finite.
-/

namespace EuclideanSpace

variable (𝕜 : Type*) [RCLike 𝕜] {n ι : Type*}

/-- The **coordinate subspace** of a set $s \subseteq n$ of indices: the subspace of $\mathbb{K}^n$
of the vectors $v$ with $v_j = 0$ for every $j \notin s$. -/
def coordSubspace (s : Set n) : Submodule 𝕜 (EuclideanSpace 𝕜 n) where
  carrier := {v | ∀ j ∉ s, v j = 0}
  add_mem' hu hv j hj := by rw [PiLp.add_apply, hu j hj, hv j hj, add_zero]
  zero_mem' j _ := rfl
  smul_mem' c _ hv j hj := by rw [PiLp.smul_apply, hv j hj, smul_zero]

/-- The **block subspace** of a labelling $\pi : n \to I$ at the label $i \in I$: the coordinate
subspace of the block $\pi^{-1}(i)$, that is, the vectors $v$ with $v_j = 0$ whenever
$\pi(j) \neq i$. -/
def blockSubspace (π : n → ι) (i : ι) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  coordSubspace 𝕜 (π ⁻¹' {i})

variable {𝕜}

/-- A vector $v$ lies in the coordinate subspace of $s$ if and only if $v_j = 0$ for every
$j \notin s$. -/
@[simp]
theorem mem_coordSubspace {s : Set n} {v : EuclideanSpace 𝕜 n} :
    v ∈ coordSubspace 𝕜 s ↔ ∀ j ∉ s, v j = 0 := Iff.rfl

/-- A vector $v$ lies in the block subspace of $\pi$ at $i$ if and only if $v_j = 0$ for every $j$
with $\pi(j) \neq i$. -/
@[simp]
theorem mem_blockSubspace {π : n → ι} {i : ι} {v : EuclideanSpace 𝕜 n} :
    v ∈ blockSubspace 𝕜 π i ↔ ∀ j, π j ≠ i → v j = 0 := Iff.rfl

variable [DecidableEq n]

/-- For $j \in s$ and every scalar $a$, the vector $a e_j$ lies in the coordinate subspace of $s$.
-/
theorem single_mem_coordSubspace {s : Set n} {j : n} (hj : j ∈ s) (a : 𝕜) :
    EuclideanSpace.single j a ∈ coordSubspace 𝕜 s := fun k hk => by
  have hkj : k ≠ j := by rintro rfl; exact hk hj
  simp [hkj]

variable [Fintype n]

omit [DecidableEq n] in
/-- **Orthogonal complement of a coordinate subspace.** Let the index set $n$ be finite and let
$s \subseteq n$. A vector $v \in \mathbb{K}^n$ is orthogonal to the coordinate subspace of $s$
if and only if $v_j = 0$ for every $j \in s$. So the orthogonal complement is the coordinate
subspace of the complement of $s$. -/
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
/-- Let the index set $n$ be finite, let $\pi : n \to I$ and $i \in I$. A vector
$v \in \mathbb{K}^n$ is orthogonal to the block subspace of $\pi$ at $i$ if and only if
$v_j = 0$ for every $j$ with $\pi(j) = i$. -/
theorem mem_orthogonal_blockSubspace {π : n → ι} {i : ι} {v : EuclideanSpace 𝕜 n} :
    v ∈ (blockSubspace 𝕜 π i)ᗮ ↔ ∀ j, π j = i → v j = 0 :=
  mem_orthogonal_coordSubspace

end EuclideanSpace
