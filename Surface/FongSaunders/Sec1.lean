import Numlib

/-!
# §1: the setting, Krylov subspaces and the Lanczos process

Surface library for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical
comparison*, SQU Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R).

§1 fixes the problem: a real symmetric positive definite system `A x = b` of order `n`, solved
from `x₀ = 0`, with `‖·‖` the 2-norm on vectors. This file introduces the surface vocabulary
(`FongSaunders.Vec`, the product `A ⬝ x`, `krylov`, the Lanczos vectors and `T̲_k`), proves the
glue lemmas to the backbone (`Numlib`), and formalizes the unnumbered facts of §1 and §1.1:
the Lanczos relation `A V_k = V_{k+1} T̲_k` with termination at `ℓ ≤ n`, the parametrization
`x_k = V_k y_k` of the `k`-th Krylov subspace, and the existence and uniqueness of `x*`.
-/

namespace FongSaunders

open Krylov Matrix

/-- The real inner product `xᵀ y` of the paper. -/
scoped notation "⟪" x ", " y "⟫_ℝ" => inner ℝ x y

/-- `ℝⁿ` as the paper's vector space: `Fin n`-indexed reals with the 2-norm. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The paper's matrix–vector product `A x`, as a map `Vec n → Vec n`. -/
noncomputable abbrev mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Vec n :=
  Matrix.toEuclideanLin A x

@[inherit_doc] scoped infixr:73 " ⬝ " => mulVecE

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n)

/-! ### D1: the matrix–vector product -/

section Glue

variable {A} {x y : Vec n} {c : ℝ}

/-- The product is additive in the vector. -/
theorem mulVecE_add : A ⬝ (x + y) = A ⬝ x + A ⬝ y := map_add _ _ _

/-- The product is homogeneous in the vector. -/
theorem mulVecE_smul : A ⬝ (c • x) = c • (A ⬝ x) := map_smul _ _ _

/-- The product distributes over a difference of vectors. -/
theorem mulVecE_sub : A ⬝ (x - y) = A ⬝ x - A ⬝ y := map_sub _ _ _

/-- `A 0 = 0`. -/
@[simp] theorem mulVecE_zero : A ⬝ (0 : Vec n) = 0 := map_zero _

/-- `0 x = 0`. -/
@[simp] theorem zero_mulVecE (x : Vec n) : (0 : Matrix (Fin n) (Fin n) ℝ) ⬝ x = 0 := by
  change Matrix.toEuclideanLin 0 x = 0
  rw [map_zero, LinearMap.zero_apply]

/-- The paper's product is the backbone's operator applied to `x`.  `mulVecE` is reducible, so
this is `rfl`; it is stated so that `rw` and `simp only` can normalise towards the backbone. -/
theorem mulVecE_eq (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    A ⬝ x = Matrix.toEuclideanLin A x := rfl

/-- The product in coordinates: `A ⬝ x` is `Matrix.mulVec`. -/
theorem ofLp_mulVecE : WithLp.ofLp (A ⬝ x) = A *ᵥ WithLp.ofLp x := rfl

/-- `⟪x, A y⟫ = xᵀ (A y)`. -/
theorem inner_mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x y : Vec n) :
    ⟪x, A ⬝ y⟫_ℝ = WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp y) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- A positive definite matrix is symmetric (Mathlib's `PosDef` bundles `IsHermitian`). -/
theorem isSymm_of_posDef (hA : A.PosDef) : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.1

/-- A symmetric matrix induces a symmetric operator on `Vec n`. -/
theorem isSymmetric_toEuclideanLin (hA : A.IsSymm) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 (Matrix.isHermitian_iff_isSymm.2 hA)

/-- Symmetry moves `A` across the inner product: `xᵀ A y = (A x)ᵀ y`. -/
theorem inner_mulVecE_comm (hA : A.IsSymm) (x y : Vec n) : ⟪x, A ⬝ y⟫_ℝ = ⟪A ⬝ x, y⟫_ℝ :=
  ((isSymmetric_toEuclideanLin hA) x y).symm

/-- Powers of `A` act as powers of the operator. -/
theorem mulVecE_pow (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (x : Vec n) :
    (A ^ i) ⬝ x = (Matrix.toEuclideanLin A ^ i) x :=
  DFunLike.congr_fun (Matrix.toEuclideanLin_pow A i) x

/-- Mathlib's `Matrix.PosDef` is the backbone's symmetric coercivity of `toEuclideanLin A`
(`A ≻ 0` in the paper's notation). -/
theorem isSymmetricCoercive_of_posDef (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- Expansion of the quadratic form along a line, for symmetric `A`:
`(u + c p)ᵀ A (u + c p) = uᵀ A u + 2c (A u)ᵀ p + c² pᵀ A p`. -/
theorem inner_mulVecE_add_smul (hA : A.IsSymm) (u p : Vec n) (c : ℝ) :
    ⟪u + c • p, A ⬝ (u + c • p)⟫_ℝ
      = ⟪u, A ⬝ u⟫_ℝ + 2 * c * ⟪A ⬝ u, p⟫_ℝ + c ^ 2 * ⟪p, A ⬝ p⟫_ℝ := by
  simp only [mulVecE_add, mulVecE_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_mulVecE_comm hA u p, real_inner_comm (A ⬝ u) p]
  ring

/-- The quadratic form of a positive definite matrix is positive off the origin. -/
theorem inner_mulVecE_self_pos (hA : A.PosDef) {x : Vec n} (hx : x ≠ 0) : 0 < ⟪x, A ⬝ x⟫_ℝ := by
  have h := (isSymmetricCoercive_of_posDef hA).isCoercive.inner_self_pos hx
  rw [RCLike.re_to_real] at h
  rwa [real_inner_comm]

/-- The quadratic form of a positive definite matrix is nonnegative. -/
theorem inner_mulVecE_self_nonneg (hA : A.PosDef) (x : Vec n) : 0 ≤ ⟪x, A ⬝ x⟫_ℝ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (inner_mulVecE_self_pos hA hx).le

/-- The quadratic form of a positive definite matrix vanishes only at `0`. -/
theorem eq_zero_of_inner_mulVecE_self_eq_zero (hA : A.PosDef) {x : Vec n}
    (hx : ⟪x, A ⬝ x⟫_ℝ = 0) : x = 0 := by
  by_contra h
  exact absurd hx (inner_mulVecE_self_pos hA h).ne'

/-- A positive definite matrix on a space with a nonzero vector is itself nonzero.  This makes
`‖A‖ ≠ 0` free in §3, where the paper's ratios `‖E‖/‖A‖` are otherwise degenerate. -/
theorem ne_zero_of_posDef (hA : A.PosDef) {x : Vec n} (hx : x ≠ 0) : A ≠ 0 := by
  rintro rfl
  exact absurd (by rw [zero_mulVecE, inner_zero_right]) (inner_mulVecE_self_pos hA hx).ne'

end Glue

/-! ### D2: Krylov subspaces and the Lanczos objects -/

/-- `𝒦_k(A, b) = span{b, A b, …, A^(k−1) b}`. -/
noncomputable def krylov (k : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range fun i : Fin k => (A ^ (i : ℕ)) ⬝ b)

/-- The paper's Lanczos vector `v_{j+1}` (the surface indexes from `0`).  The Lanczos vectors
are not redefined here: they are the backbone's Arnoldi vectors, which for symmetric `A` obey the
three-term recurrence. -/
noncomputable abbrev lanczosVec (j : ℕ) : Vec n := Arnoldi.vec (Matrix.toEuclideanLin A) b j

/-- The paper's `(k+1) × k` tridiagonal matrix `T̲_k`. -/
noncomputable abbrev lanczosT (k : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Lanczos.tridiagExt (Matrix.toEuclideanLin A) b k

/-- The paper's square tridiagonal matrix `T_k`. -/
noncomputable abbrev lanczosTsq (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Lanczos.tridiag (Matrix.toEuclideanLin A) b k

/-- The paper's termination index `ℓ`: the grade of `b` with respect to `A`. -/
noncomputable abbrev lanczosTerm : ℕ := Krylov.grade (Matrix.toEuclideanLin A) b

/-- The surface Krylov subspace is the backbone one. -/
theorem krylov_eq (k : ℕ) : krylov A b k = Krylov.subspace (Matrix.toEuclideanLin A) b k :=
  (Matrix.krylov_subspace_toEuclideanLin A b k).symm

/-- The Krylov subspaces are nested. -/
theorem krylov_mono {k l : ℕ} (h : k ≤ l) : krylov A b k ≤ krylov A b l := by
  rw [krylov_eq, krylov_eq]
  exact Krylov.subspace_mono _ _ h

/-- The zeroth Krylov subspace is trivial, which is the paper's `x_0 = 0`. -/
@[simp] theorem krylov_zero : krylov A b 0 = ⊥ := by rw [krylov_eq, Krylov.subspace_zero]

/-- R1.2: the elements of `𝒦_k(A, b)` are exactly the vectors `V_k y`. -/
theorem mem_krylov_iff_exists_lanczos (k : ℕ) (x : Vec n) :
    x ∈ krylov A b k ↔ ∃ y : Fin k → ℝ, x = ∑ j, y j • lanczosVec A b j := by
  have hspan : krylov A b k =
      Submodule.span ℝ (Set.range fun j : Fin k => lanczosVec A b (j : ℕ)) := by
    rw [krylov_eq, ← Arnoldi.span_vec (Matrix.toEuclideanLin A) b k]
    congr 1
    ext v
    simp [lanczosVec, Set.mem_range, Fin.exists_iff]
  rw [hspan, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

section ZeroStart

variable {A b}

/-- The initial residual at `x₀ = 0` is `b`. -/
theorem sub_mulVecE_zero : b - Matrix.toEuclideanLin A 0 = b := by rw [map_zero, sub_zero]

/-- Membership in the `k`-th Krylov subspace is the backbone condition at `x₀ = 0`. -/
theorem sub_zero_mem_subspace_iff {k : ℕ} {x : Vec n} :
    x - 0 ∈ Krylov.subspace (Matrix.toEuclideanLin A) (b - Matrix.toEuclideanLin A 0) k
      ↔ x ∈ krylov A b k := by
  rw [sub_zero, sub_mulVecE_zero, krylov_eq]

end ZeroStart

/-! ### R1.1: the Lanczos relation and termination -/

/-- `A V_k = V_{k+1} T̲_k` in coordinates, for every `k` (beyond `ℓ` the extra Lanczos vectors
are `0`, so the relation is vacuously maintained). -/
theorem lanczos_relation (hA : A.IsSymm) (k : ℕ) (y : Fin k → ℝ) :
    A ⬝ (∑ j, y j • lanczosVec A b j) =
      ∑ i : Fin (k + 1), (lanczosT A b k).mulVec y i • lanczosVec A b i := by
  have h := Arnoldi.apply_sum (Matrix.toEuclideanLin A) b k y
  rw [Lanczos.hessenberg_eq_map_tridiagExt b (isSymmetric_toEuclideanLin hA) k] at h
  simpa [lanczosVec, lanczosT, Matrix.map_apply, Matrix.mulVec, dotProduct] using h

/-- Termination: at `k = ℓ` the relation closes up, `A V_ℓ = V_ℓ T_ℓ`. -/
theorem lanczos_relation_term (hA : A.IsSymm) (y : Fin (lanczosTerm A b) → ℝ) :
    A ⬝ (∑ j, y j • lanczosVec A b j) =
      ∑ i, (lanczosTsq A b (lanczosTerm A b)).mulVec y i • lanczosVec A b i := by
  have h := Lanczos.apply_sum_grade b (isSymmetric_toEuclideanLin hA) y
  simpa [lanczosVec, lanczosTsq, lanczosTerm, Matrix.map_apply, Matrix.mulVec, dotProduct]
    using h

/-- The Lanczos vectors `v_1, …, v_ℓ` are orthonormal. -/
theorem lanczosVec_orthonormal :
    Orthonormal ℝ fun j : Fin (lanczosTerm A b) => lanczosVec A b (j : ℕ) :=
  Arnoldi.orthonormal (Matrix.toEuclideanLin A) b

/-- `V_k` spans `𝒦_k(A, b)`. -/
theorem span_lanczosVec (k : ℕ) :
    Submodule.span ℝ (lanczosVec A b '' Set.Iio k) = krylov A b k := by
  rw [krylov_eq]
  exact Arnoldi.span_vec (Matrix.toEuclideanLin A) b k

/-- `ℓ ≤ n`. -/
theorem lanczosTerm_le : lanczosTerm A b ≤ n := by
  have h := Krylov.grade_le_finrank (Matrix.toEuclideanLin A) b
  rwa [finrank_euclideanSpace_fin] at h

/-! ### D3 and R1.3: the exact solution `x*` -/

/-- R1.3: `A x = b` has a unique solution when `A ≻ 0`. -/
theorem existsUnique_solution {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b : Vec n) :
    ∃! x : Vec n, A ⬝ x = b := by
  have hinj : Function.Injective (Matrix.toEuclideanLin A) :=
    (isSymmetricCoercive_of_posDef hA).isCoercive.injective
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.1 hinj b
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

/-- The exact solution `x* = A⁻¹ b`. -/
noncomputable def xstar : Vec n := A⁻¹ ⬝ b

variable {A b}

/-- `A x* = b`. -/
@[simp] theorem mulVecE_xstar (hA : A.PosDef) : A ⬝ xstar A b = b := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have h : A ⬝ xstar A b = (A * A⁻¹) ⬝ b := by
    change Matrix.toEuclideanLin A (Matrix.toEuclideanLin A⁻¹ b)
      = Matrix.toEuclideanLin (A * A⁻¹) b
    rw [Matrix.toEuclideanLin_mul]; rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ⬝ b = b := by
    change Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) b = b
    rw [Matrix.toEuclideanLin_one]; rfl
  rw [h, Matrix.mul_nonsing_inv A hdet, h1]

/-- Any solution of `A x = b` is `x*`. -/
theorem xstar_unique (hA : A.PosDef) {x : Vec n} (h : A ⬝ x = b) : x = xstar A b :=
  (isSymmetricCoercive_of_posDef hA).isCoercive.injective (h.trans (mulVecE_xstar hA).symm)

end FongSaunders
