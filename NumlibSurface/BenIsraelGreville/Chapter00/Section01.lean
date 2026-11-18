/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Scalars and vectors

This section fixes the coordinate basis, complementary sums and projections, and the
conventions for inner products and norms in [benIsrael2003generalized], Chapter 0, §1.

## Main definitions

* `BenIsraelGreville.Chapter00.standardBasis` is the basis of coordinate unit vectors.
* `BenIsraelGreville.Chapter00.projectionAlong` maps a vector to its component in one of two
  complementary subspaces.
* `BenIsraelGreville.Chapter00.IsInnerProduct` uses first-slot complex linearity.
* `BenIsraelGreville.Chapter00.IsVectorNorm` is the norm predicate for an arbitrary function on a
  complex vector space.

## Main results

* `BenIsraelGreville.Chapter00.existsUnique_sum_of_complementary` gives the unique component pair
  for two complementary subspaces.
-/

open scoped BigOperators ENNReal InnerProductSpace

namespace BenIsraelGreville.Chapter00

variable {n : Type*} [DecidableEq n]

/-- The $i$th unit vector is one at $i$ and zero elsewhere.
[benIsrael2003generalized], Chapter 0, §1.2. -/
def unitVector (i : n) : n → ℂ := Pi.single i 1

/-- The standard basis of a coordinate space consists of the coordinate unit vectors.
[benIsrael2003generalized], Chapter 0, §1.2. -/
noncomputable def standardBasis [Finite n] : Module.Basis n ℂ (n → ℂ) :=
  Pi.basisFun ℂ n

/-- Evaluating the $i$th standard basis vector produces the $i$th coordinate unit vector. -/
@[simp]
theorem standardBasis_apply [Finite n] (i : n) : standardBasis i = unitVector i :=
  Pi.basisFun_apply ℂ n i

section Sums

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The sum of two subspaces consists of sums of one vector from each.
[benIsrael2003generalized], Chapter 0, §1.3. -/
theorem mem_subspaceSum {L M : Submodule ℂ V} {x : V} :
    x ∈ L ⊔ M ↔ ∃ y ∈ L, ∃ z ∈ M, y + z = x :=
  Submodule.mem_sup

/-- The sum of two subspaces is direct when they intersect only at zero.
[benIsrael2003generalized], Chapter 0, §1.3. -/
def isDirectSum (L M : Submodule ℂ V) : Prop := L ⊓ M = ⊥

/-- Two subspaces are complementary if their sum is direct and is the whole space.
[benIsrael2003generalized], Chapter 0, Equation (1). -/
abbrev areComplementary (L M : Submodule ℂ V) : Prop := IsCompl L M

/-- Complementarity is equivalent to having direct sum equal to the ambient space. -/
theorem areComplementary_iff (L M : Submodule ℂ V) :
    areComplementary L M ↔ isDirectSum L M ∧ L ⊔ M = ⊤ :=
  ⟨fun h => ⟨h.inf_eq_bot, h.sup_eq_top⟩, fun h =>
    ⟨disjoint_iff.mpr h.1, codisjoint_iff.mpr h.2⟩⟩

/-- With complementary $L$ and $M$, every vector has a unique decomposition as a sum of a vector
in $L$ and a vector in $M$. [benIsrael2003generalized], Chapter 0, Equation (2). -/
theorem existsUnique_sum_of_complementary {L M : Submodule ℂ V} (h : areComplementary L M)
    (x : V) : ∃! p : L × M, (p.1 : V) + (p.2 : V) = x := by
  let e := Submodule.prodEquivOfIsCompl L M h
  change ∃! p, e p = x
  exact ⟨e.symm x, e.apply_symm_apply x,
    fun p hp => e.injective (hp.trans (e.apply_symm_apply x).symm)⟩

/-- Projection on $L$ along a complementary subspace $M$ selects the $L$-component of a vector.
[benIsrael2003generalized], Chapter 0, §1.3. -/
noncomputable def projectionAlong {L M : Submodule ℂ V} (h : areComplementary L M) :
    V →ₗ[ℂ] L := L.projectionOnto M h

/-- The difference between a vector and its projection onto $L$ along $M$ lies in $M$. -/
theorem sub_projectionAlong_mem {L M : Submodule ℂ V} (h : areComplementary L M) (x : V) :
    x - (projectionAlong h x : V) ∈ M :=
  L.sub_projection_mem h x

end Sums

section Inner

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An inner product is a complex form that is linear in the first argument, Hermitian symmetric,
and positive definite. [benIsrael2003generalized], Chapter 0, §1.4. -/
structure IsInnerProduct (f : V → V → ℂ) : Prop where
  linear_left (a : ℂ) (x y z : V) : f (a • x + y) z = a * f x z + f y z
  conjugate_symm (x y : V) : f x y = star (f y x)
  nonneg (x : V) : 0 ≤ (f x x).re
  eq_zero_iff (x : V) : f x x = 0 ↔ x = 0

/-- An inner product vanishes when its first argument is zero.
[benIsrael2003generalized], Chapter 0, §1.4, Note (c). -/
theorem IsInnerProduct.zero_left {f : V → V → ℂ} (h : IsInnerProduct f) (z : V) :
    f 0 z = 0 := by
  have h' := h.linear_left 1 0 0 z
  simp only [smul_zero, add_zero, one_mul] at h'
  exact add_right_cancel (h'.symm.trans (zero_add _).symm)

/-- An inner product scales by the conjugate scalar when its second argument is scaled.
[benIsrael2003generalized], Chapter 0, §1.4, Note (a). -/
theorem IsInnerProduct.conjLinear_right {f : V → V → ℂ} (h : IsInnerProduct f)
    (a : ℂ) (x y : V) : f x (a • y) = star a * f x y := by
  have hy : f (a • y) x = a * f y x := by
    simpa only [add_zero, h.zero_left] using h.linear_left a y 0 x
  rw [h.conjugate_symm x (a • y), hy, star_mul', h.conjugate_symm x y]

/-- The value of an inner product on two equal vectors is fixed by conjugation, hence real.
[benIsrael2003generalized], Chapter 0, §1.4, Note (b). -/
theorem IsInnerProduct.self_real {f : V → V → ℂ} (h : IsInnerProduct f) (x : V) :
    star (f x x) = f x x :=
  (h.conjugate_symm x x).symm

omit [DecidableEq n] in
/-- The standard inner product, written with the first-slot-linear convention, is the sum
of the products of the coordinates of the first vector and the conjugated coordinates
of the second. [benIsrael2003generalized], Chapter 0, Equation (3). -/
theorem standardInner_eq_sum [Fintype n] (x y : EuclideanSpace ℂ n) :
    ⟪y, x⟫_ℂ = ∑ i, x i * star (y i) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, RCLike.star_def]

end Inner

section Norms

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A vector norm is a nonnegative, definite, absolutely homogeneous and subadditive function.
[benIsrael2003generalized], Chapter 0, §1.5. -/
structure IsVectorNorm (f : V → ℝ) : Prop where
  nonneg (x : V) : 0 ≤ f x
  eq_zero_iff (x : V) : f x = 0 ↔ x = 0
  smul (a : ℂ) (x : V) : f (a • x) = ‖a‖ * f x
  triangle (x y : V) : f (x + y) ≤ f x + f y

/-- Absolute homogeneity forces a vector norm to vanish at zero.
[benIsrael2003generalized], Chapter 0, §1.5, Note (a). -/
theorem IsVectorNorm.map_zero {f : V → ℝ} (h : IsVectorNorm f) : f 0 = 0 := by
  simpa only [zero_smul, norm_zero, zero_mul] using h.smul 0 0

/-- The Cauchy–Schwarz inequality bounds the modulus of the inner product by the product of
the two norms. [benIsrael2003generalized], Chapter 0, Exercise 2. -/
theorem norm_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    ‖⟪y, x⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ :=
  (norm_inner_le_norm y x).trans_eq (mul_comm _ _)

/-- The norm induced by a complex inner product is the square root of the real part of its
self-value. [benIsrael2003generalized], Chapter 0, Exercise 3. -/
theorem norm_eq_sqrt_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : ‖x‖ = Real.sqrt (Complex.re ⟪x, x⟫_ℂ) :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) x

/-- The angle of two nonzero real vectors is the arccosine of the inner product divided by the
product of their norms. [benIsrael2003generalized], Chapter 0, Exercise 5. -/
theorem angle_eq_arccos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    InnerProductGeometry.angle x y = Real.arccos (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)) :=
  rfl

/-- A family is orthonormal exactly when its pairwise inner products are Kronecker deltas.
[benIsrael2003generalized], Chapter 0, Exercise 6. -/
theorem orthonormal_iff_inner_eq_delta {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : n → E) :
    Orthonormal ℂ v ↔ ∀ i j, ⟪v j, v i⟫_ℂ = if i = j then 1 else 0 := by
  rw [orthonormal_iff_ite]
  exact ⟨fun h i j => by simpa only [eq_comm] using h j i,
    fun h i j => by simpa only [eq_comm] using h j i⟩

/-- The coordinate $\ell_p$ norm is the $p$th root of the sum of the $p$th powers of the
coordinate moduli for finite $p\geq1$, and the largest coordinate modulus for $p=\infty$.
[benIsrael2003generalized], Chapter 0, Exercises 9–10. -/
noncomputable def lpNorm [Fintype n] (p : ℝ≥0∞) (x : n → ℂ) : ℝ :=
  if p = ∞ then ⨆ i, ‖x i‖ else (∑ i, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal)

end Norms

end BenIsraelGreville.Chapter00
