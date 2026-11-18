import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Krylov.Subspace
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Exact block preconditioning of saddle-point matrices

Block diagonal and block triangular preconditioning with exact blocks lead to low-degree
annihilating polynomials. No symmetry of the coupled matrix is required.

## Main results

* `Matrix.fromBlocks_one_zero_cubic`: a cubic annihilator of $[I,U;V,0]$ when $VU=I$.
* `Matrix.fromBlocks_one_zero_eigenvalue`: the corresponding spectral restriction.
* `Matrix.right_preconditioned_fromBlocks_upper`: exact triangular preconditioning is
  unit lower triangular on the right.
* `Matrix.charpoly_left_preconditioned_fromBlocks_upper` and
  `Matrix.sq_sub_one_left_preconditioned_fromBlocks_upper`: characteristic polynomial and
  square-zero identity for exact triangular preconditioning on the left.
-/

namespace Matrix

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable [CommRing R]

/-- The nonsingular inverse of a negated matrix is the negated inverse, also when
the inverse is zero by convention. -/
theorem nonsing_inv_neg_eq_neg {A : Matrix n n R} : (-A)⁻¹ = -A⁻¹ := by
  by_cases hA : IsUnit A
  · apply inv_eq_left_inv
    simp [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA)]
  · have hneg : ¬ IsUnit (-A) := fun h => hA (by simpa using h.neg)
    rw [nonsing_inv_apply_not_isUnit _ (fun h => hneg ((isUnit_iff_isUnit_det _).mpr h)),
      nonsing_inv_apply_not_isUnit _ (fun h => hA ((isUnit_iff_isUnit_det _).mpr h)), neg_zero]

/-- The inverse of an upper block triangular matrix with invertible diagonal blocks. -/
theorem inv_fromBlocks_upper {A : Matrix n n R} (E : Matrix n m R) {S : Matrix m m R}
    (hA : IsUnit A) (hS : IsUnit S) :
    (fromBlocks A E 0 S)⁻¹ = fromBlocks A⁻¹ (-(A⁻¹ * E * S⁻¹)) 0 S⁻¹ := by
  have hAA := nonsing_inv_mul A ((isUnit_iff_isUnit_det A).mp hA)
  have hSS := nonsing_inv_mul S ((isUnit_iff_isUnit_det S).mp hS)
  apply inv_eq_left_inv
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp [Matrix.mul_assoc, hAA, hSS]

/-- A block diagonal inverse is obtained by inverting its diagonal blocks. -/
theorem inv_fromBlocks_diag_of_isUnit {A : Matrix n n R} {S : Matrix m m R}
    (hA : IsUnit A) (hS : IsUnit S) :
    (fromBlocks A 0 0 S)⁻¹ = fromBlocks A⁻¹ 0 0 S⁻¹ := by
  simpa using inv_fromBlocks_upper (0 : Matrix n m R) hA hS

/-- If $VU=I$, the inverse of $[I,U;V,0]$ is $[I-UV,U;V,-I]$. -/
theorem inv_fromBlocks_diag_one_zero_of_mul_eq_one {U : Matrix n m R} {V : Matrix m n R}
    (h : V * U = 1) :
    (fromBlocks 1 U V 0)⁻¹ = fromBlocks (1 - U * V) U V (-1) := by
  apply inv_eq_left_inv
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp [Matrix.sub_mul, Matrix.mul_assoc, h]

/-- If $VU=I$, the matrix $M=[I,U;V,0]$ is annihilated by $(X-1)(X^2-X-1)$. -/
theorem fromBlocks_one_zero_cubic {U : Matrix n m R} {V : Matrix m n R} (h : V * U = 1) :
    let M := fromBlocks 1 U V 0
    (M - 1) * (M ^ 2 - M - 1) = 0 := by
  dsimp only
  have hM : (fromBlocks 1 U V 0) ^ 2 - fromBlocks 1 U V 0 - 1 =
      fromBlocks (U * V - 1) 0 0 (0 : Matrix m m R) := by
    simp [pow_two, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
      fromBlocks_multiply, h]
  rw [hM]
  simp [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
    fromBlocks_multiply, Matrix.mul_add, ← Matrix.mul_assoc, h, fromBlocks_zero]

/-- Each eigenvalue of $[I,U;V,0]$ with $VU=I$ is a root of $(X-1)(X^2-X-1)$. -/
theorem fromBlocks_one_zero_eigenvalue {K : Type*} [Field K] {U : Matrix n m K}
    {V : Matrix m n K} (h : V * U = 1) {μ : K} (hμ : μ ∈ spectrum K (fromBlocks 1 U V 0)) :
    (μ - 1) * (μ ^ 2 - μ - 1) = 0 := by
  let p : Polynomial K := (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.X - 1)
  have hp : Polynomial.aeval (fromBlocks 1 U V 0) p = 0 := by
    simpa [p] using fromBlocks_one_zero_cubic h
  have hs := spectrum.subset_polynomial_aeval (fromBlocks 1 U V 0) p
    ⟨μ, hμ, rfl⟩
  rw [hp] at hs
  by_contra hn
  have hne : Polynomial.eval μ p ≠ 0 := by simpa [p] using hn
  have hu := IsUnit.map (algebraMap K (Matrix (n ⊕ m) (n ⊕ m) K))
    (isUnit_iff_ne_zero.mpr hne)
  exact (spectrum.mem_iff.mp hs) (by simpa using hu)

variable {A : Matrix n n R} {E : Matrix n m R} {F : Matrix m n R} {C : Matrix m m R}

/-- Exact right triangular preconditioning of a two-by-two block matrix gives a unit lower
triangular matrix, with subdiagonal block $FA^{-1}$. -/
theorem right_preconditioned_fromBlocks_upper (hA : IsUnit A)
    (hS : IsUnit (C - F * A⁻¹ * E)) :
    fromBlocks A E F C * (fromBlocks A E 0 (C - F * A⁻¹ * E))⁻¹ =
      fromBlocks 1 0 (F * A⁻¹) 1 := by
  conv_lhs => rw [fromBlocks_eq_mul_fromBlocks_schurComplement hA, schurComplement_fromBlocks]
  rw [Matrix.mul_assoc, inv_fromBlocks_upper E hA hS, fromBlocks_multiply]
  have hAA := mul_nonsing_inv A ((isUnit_iff_isUnit_det A).mp hA)
  have hSS := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)
  simp [← Matrix.mul_assoc, hAA, hSS, fromBlocks_one]

/-- The characteristic polynomial for exact left triangular preconditioning is a power
of $X-1$, including in dimension zero. -/
theorem charpoly_left_preconditioned_fromBlocks_upper (hA : IsUnit A)
    (hS : IsUnit (C - F * A⁻¹ * E)) :
    ((fromBlocks A E 0 (C - F * A⁻¹ * E))⁻¹ * fromBlocks A E F C).charpoly =
      (Polynomial.X - 1) ^ (Fintype.card n + Fintype.card m) := by
  rw [charpoly_mul_comm, right_preconditioned_fromBlocks_upper hA hS,
    charpoly_fromBlocks_zero₁₂, charpoly_one, charpoly_one, pow_add]

/-- Exact left triangular preconditioning is annihilated by $(X-1)^2$. -/
theorem sq_sub_one_left_preconditioned_fromBlocks_upper (hA : IsUnit A)
    (hS : IsUnit (C - F * A⁻¹ * E)) :
    ((fromBlocks A E 0 (C - F * A⁻¹ * E))⁻¹ * fromBlocks A E F C - 1) ^ 2 = 0 := by
  let P := fromBlocks A E 0 (C - F * A⁻¹ * E)
  let L := fromBlocks (1 : Matrix n n R) 0 (F * A⁻¹) (1 : Matrix m m R)
  have hLP : fromBlocks A E F C = L * P := by
    simpa [L, P, schurComplement_fromBlocks] using
      (fromBlocks_eq_mul_fromBlocks_schurComplement (E := E) (F := F) (C := C) hA)
  have hPP : P * P⁻¹ = 1 := by
    dsimp [P]
    rw [inv_fromBlocks_upper E hA hS, fromBlocks_multiply, ← fromBlocks_one]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)]
  have hL : (L - 1) ^ 2 = 0 := by
    simp [L, pow_two, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
      fromBlocks_multiply, fromBlocks_zero]
  change (P⁻¹ * fromBlocks A E F C - 1) ^ 2 = 0
  have hP' : P⁻¹ * P = 1 := mul_eq_one_comm.mp hPP
  rw [hLP, show P⁻¹ * (L * P) - 1 = P⁻¹ * (L - 1) * P by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP', Matrix.mul_assoc]]
  calc
    (P⁻¹ * (L - 1) * P) ^ 2 = P⁻¹ * ((L - 1) ^ 2) * P := by
      simp only [pow_two]
      calc
        P⁻¹ * (L - 1) * P * (P⁻¹ * (L - 1) * P) =
            P⁻¹ * (L - 1) * (P * P⁻¹) * (L - 1) * P := by simp only [Matrix.mul_assoc]
        _ = P⁻¹ * ((L - 1) * (L - 1)) * P := by simp [hPP, Matrix.mul_assoc]
    _ = 0 := by rw [hL]; simp

/-- An annihilating polynomial of a square matrix bounds the dimension of every Krylov space
generated by that matrix. -/
theorem krylov_grade_le_of_aeval_eq_zero {K : Type*} [Field K] (M : Matrix n n K)
    {p : Polynomial K} (hp : p ≠ 0) (hM : Polynomial.aeval M p = 0) (r : n → K) :
    Krylov.grade (toLinAlgEquiv' M) r ≤ p.natDegree := by
  rw [← Krylov.natDegree_minpolyVec]
  apply Polynomial.natDegree_le_of_dvd _ hp
  apply (Krylov.minpolyVec_dvd_iff _ _).mpr
  rw [Polynomial.aeval_algHom_apply toLinAlgEquiv', hM, map_zero, LinearMap.zero_apply]

end Matrix
