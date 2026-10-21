import Numlib.Optimization.SecularStepDerivatives
import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Exact factored solves for secular derivatives

An `L D Lᵀ` certificate supports forward substitution, diagonal division, and backward
substitution. The resulting positive recurrence is an auxiliary sequence; its terms have
alternating signs relative to the actual derivatives of a negative shifted inverse.
-/

open scoped InnerProductSpace
open Matrix

namespace Optimization.SecularResolvent

variable {n : ℕ}

/-- Forward substitution through the lower factor, in Euclidean coordinates. -/
noncomputable def ldlForward (L : Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Matrix.forwardSubst L (WithLp.ofLp b))

/-- Division through the diagonal factor, in Euclidean coordinates. -/
noncomputable def ldlDiagonal (D : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => y i / D i i)

/-- Backward substitution through the transpose of the lower factor. -/
noncomputable def ldlBackward (L : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Matrix.backSubst Lᵀ (WithLp.ofLp z))

/-- Exact solution by three factor solves. -/
noncomputable def ldlSolve (L D : Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ldlBackward L (ldlDiagonal D (ldlForward L b))

variable {A L D M : Matrix (Fin n) (Fin n) ℝ}

/-- Nonsingularity of an exact lower-diagonal-transpose factorization excludes zero pivots
in both factors. No unit normalization of the lower factor is required. -/
theorem ldl_pivots_ne_zero (hL : L.IsLowerTriangular) (hD : D.IsDiag)
    (hf : L * D * Lᵀ = A) (hA : IsUnit A) :
    (∀ i, L i i ≠ 0) ∧ (∀ i, D i i ≠ 0) := by
  have ha : A.det ≠ 0 := (isUnit_iff_ne_zero).1
    ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  rw [← hf, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at ha
  have hl : L.det ≠ 0 := (mul_ne_zero_iff.1 ha).2
  have hd : D.det ≠ 0 := (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 ha).1).2
  exact ⟨hL.isUnit_iff.1 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hl)),
    hD.isUpperTriangular.isUnit_iff.1
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))⟩

/-- Forward substitution solves the first factor equation. -/
theorem ldlForward_equation (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (b : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin L (ldlForward L b) = b := by
  apply WithLp.ofLp_injective
  change L *ᵥ Matrix.forwardSubst L (WithLp.ofLp b) = WithLp.ofLp b
  exact Matrix.mulVec_forwardSubst _ hL hld

/-- Diagonal division solves the second factor equation. -/
theorem ldlDiagonal_equation (hD : D.IsDiag) (hd : ∀ i, D i i ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin D (ldlDiagonal D y) = y := by
  apply WithLp.ofLp_injective
  change D *ᵥ (fun i => y i / D i i) = WithLp.ofLp y
  rw [← hD.diagonal_diag]
  ext i
  simp only [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, Matrix.diag_apply]
  exact mul_div_cancel₀ (y i) (hd i)

/-- Backward substitution solves the last factor equation. -/
theorem ldlBackward_equation (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin Lᵀ (ldlBackward L z) = z := by
  apply WithLp.ofLp_injective
  change Lᵀ *ᵥ Matrix.backSubst Lᵀ (WithLp.ofLp z) = WithLp.ofLp z
  exact Matrix.mulVec_backSubst _ hL.transpose_isUpperTriangular hld

/-- The exact factor solve satisfies the original system. -/
theorem ldlSolve_equation (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (hD : D.IsDiag) (hd : ∀ i, D i i ≠ 0) (hf : L * D * Lᵀ = A)
    (b : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A (ldlSolve L D b) = b := by
  rw [← hf, Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_mul_apply,
    ldlSolve, ldlBackward_equation hL hld,
    ldlDiagonal_equation hD hd, ldlForward_equation hL hld]

/-- Auxiliary step vectors generated with the positive right-hand sides of factor solves. -/
noncomputable def ldlAuxiliary (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => ldlSolve L D (-g)
  | k + 1 => ldlSolve L D (((k + 1 : ℕ) : ℝ) •
      Matrix.toEuclideanLin M (ldlAuxiliary L D M g k))

/-- The positive auxiliary sequence solves the differentiated systems with alternating signs. -/
theorem ldlAuxiliary_equation (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (hD : D.IsDiag) (hd : ∀ i, D i i ≠ 0) (hf : L * D * Lᵀ = A)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix.toEuclideanLin A (ldlAuxiliary L D M g (k + 1)) =
      ((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M (ldlAuxiliary L D M g k) :=
  ldlSolve_equation hL hld hD hd hf _

/-- The forward and backward factors preserve the pairing through transposition. -/
theorem ldl_factor_pairing {u v y z : EuclideanSpace ℝ (Fin n)} {c : ℝ}
    (hy : Matrix.toEuclideanLin L y = c • Matrix.toEuclideanLin M u)
    (hz : Matrix.toEuclideanLin Lᵀ v = z) (hM : M.IsSymm) :
    inner ℝ y z = c * inner ℝ u (Matrix.toEuclideanLin M v) := by
  rw [← hz]
  have ht := Matrix.toEuclideanLin_conjTranspose_inner_right L y v
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at ht
  rw [ht, hy, real_inner_smul_left]
  rw [hM.isSymmetric_toEuclideanLin]

/-- The scalar coefficient for an odd-order secular derivative. -/
noncomputable def secularOddCoefficient (k : ℕ) : ℝ :=
  2 * secularDerivativeCoefficient k / (k + 1)

/-- The even coefficient is updated from the preceding odd coefficient. -/
theorem secularDerivativeCoefficient_eq_oddCoefficient (k : ℕ) :
    secularDerivativeCoefficient (k + 1) =
      (2 * (k : ℝ) + 3) * secularOddCoefficient k := by
  rw [secularDerivativeCoefficient_succ, secularOddCoefficient]
  ring

/-- Identification of the positive auxiliary sequence with alternating signed solutions
of the negative differentiated recurrence. -/
theorem ldlAuxiliary_eq_sign (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (hD : D.IsDiag) (hd : ∀ i, D i i ≠ 0) (hf : L * D * Lᵀ = A)
    (hinj : Function.Injective (Matrix.toEuclideanLin A))
    (g : EuclideanSpace ℝ (Fin n)) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (hzero : Matrix.toEuclideanLin A (u 0) = -g)
    (hsucc : ∀ k, Matrix.toEuclideanLin A (u (k + 1)) =
      -((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M (u k)) (k : ℕ) :
    ldlAuxiliary L D M g k = (-1 : ℝ) ^ k • u k := by
  induction k with
  | zero =>
    simp only [pow_zero, one_smul]
    apply hinj
    exact (ldlSolve_equation hL hld hD hd hf _).trans hzero.symm
  | succ k ih =>
    apply hinj
    rw [ldlAuxiliary_equation hL hld hD hd hf, ih, map_smul, map_smul, hsucc,
      smul_smul, smul_smul, pow_succ]
    congr 1
    ring

/-- Opposite consecutive signs reverse a real inner product. -/
theorem inner_alternating_consecutive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (k : ℕ) :
    inner ℝ ((-1 : ℝ) ^ k • u) ((-1 : ℝ) ^ (k + 1) • v) = -inner ℝ u v := by
  rw [real_inner_smul_left, real_inner_smul_right]
  have hs : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 1) = -1 := by
    rw [← pow_add, show k + (k + 1) = 2 * k + 1 by omega]
    simp [pow_add, pow_mul]
  rw [← mul_assoc, hs, neg_one_mul]

/-- Equal alternating signs cancel in a real inner product. -/
theorem inner_alternating_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (k : ℕ) :
    inner ℝ ((-1 : ℝ) ^ k • u) ((-1 : ℝ) ^ k • v) = inner ℝ u v := by
  rw [real_inner_smul_left, real_inner_smul_right]
  have hs : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, show k + k = 2 * k by omega]
    simp [pow_mul]
  rw [← mul_assoc, hs, one_mul]

/-- The initial or positive differentiated right-hand side of the factor algorithm. -/
noncomputable def ldlAuxiliaryRhs (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => -g
  | k + 1 => ((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M (ldlAuxiliary L D M g k)

/-- Forward solve at an auxiliary order. -/
noncomputable def ldlAuxiliaryY (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ldlForward L (ldlAuxiliaryRhs L D M g k)

/-- Diagonal solve at an auxiliary order. -/
noncomputable def ldlAuxiliaryZ (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ldlDiagonal D (ldlAuxiliaryY L D M g k)

/-- The auxiliary vector is the final backward solve. -/
theorem ldlAuxiliary_eq_backward (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ldlAuxiliary L D M g k = ldlBackward L (ldlAuxiliaryZ L D M g k) := by
  cases k <;> rfl

/-- An odd scalar output uses only the forward and diagonal solves at the next order. -/
noncomputable def ldlOddOutput (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  -secularOddCoefficient k * inner ℝ
    (ldlAuxiliaryY L D M g (k + 1)) (ldlAuxiliaryZ L D M g (k + 1))

/-- An even scalar output uses the backward solve at its half-order. -/
noncomputable def ldlEvenOutput (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  secularDerivativeCoefficient k * inner ℝ
    (ldlAuxiliary L D M g k) (Matrix.toEuclideanLin M (ldlAuxiliary L D M g k))

/-- Scalar derivative outputs indexed by their actual order. This definition computes no
output whose index has not been requested. -/
noncomputable def ldlSecularOutput (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) : ℝ :=
  if j % 2 = 1 then ldlOddOutput L D M g (j / 2)
  else ldlEvenOutput L D M g (j / 2)

/-- Odd output indexing. -/
@[simp] theorem ldlSecularOutput_odd (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ldlSecularOutput L D M g (2 * k + 1) = ldlOddOutput L D M g k := by
  have hm : (2 * k + 1) % 2 = 1 := by omega
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [ldlSecularOutput, hm, hd]

/-- Even output indexing, including the zeroth output. -/
@[simp] theorem ldlSecularOutput_even (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ldlSecularOutput L D M g (2 * k) = ldlEvenOutput L D M g k := by
  have hd : (2 * k) / 2 = k := by omega
  simp [ldlSecularOutput, hd]

/-- Factor-pairing identity for the positive auxiliary recurrence. -/
theorem ldlAuxiliary_pairing (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (hM : M.IsSymm) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    inner ℝ (ldlAuxiliaryY L D M g (k + 1)) (ldlAuxiliaryZ L D M g (k + 1)) =
      ((k + 1 : ℕ) : ℝ) * inner ℝ (ldlAuxiliary L D M g k)
        (Matrix.toEuclideanLin M (ldlAuxiliary L D M g (k + 1))) := by
  apply ldl_factor_pairing (hM := hM)
  · exact ldlForward_equation hL hld _
  · rw [ldlAuxiliary_eq_backward]
    exact ldlBackward_equation hL hld _

/-- Odd output pairing for the source's positive auxiliary convention. -/
theorem ldlOddOutput_eq_pairing (hL : L.IsLowerTriangular) (hld : ∀ i, L i i ≠ 0)
    (hM : M.IsSymm) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ldlOddOutput L D M g k = -2 * secularDerivativeCoefficient k *
      inner ℝ (ldlAuxiliary L D M g k)
        (Matrix.toEuclideanLin M (ldlAuxiliary L D M g (k + 1))) := by
  rw [ldlOddOutput, ldlAuxiliary_pairing hL hld hM, secularOddCoefficient]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- For Cholesky factors the diagonal solve is the identity. -/
@[simp] theorem ldlDiagonal_one (y : EuclideanSpace ℝ (Fin n)) :
    ldlDiagonal (1 : Matrix (Fin n) (Fin n) ℝ) y = y := by
  ext i
  simp [ldlDiagonal]

/-- Cholesky odd outputs contain one copy of the odd coefficient, with no extra factor two. -/
theorem ldlOddOutput_cholesky (L M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ldlOddOutput L 1 M g k = -secularOddCoefficient k *
      ‖ldlAuxiliaryY L 1 M g (k + 1)‖ ^ 2 := by
  rw [ldlOddOutput, ldlAuxiliaryZ, ldlDiagonal_one, real_inner_self_eq_norm_sq]

end Optimization.SecularResolvent
