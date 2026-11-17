/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Krylov.JacobiMatrix
import Numlib.Krylov.Quadrature

/-!
# Reconstructing a Jacobi matrix by Lanczos

The Krylov matrix of a diagonal matrix $D=\operatorname{diag}(\theta_i)$ and an initial
vector $\zeta$ is the Vandermonde matrix of $(\theta_i)$ with its rows scaled by $\zeta_i$.
When all $\zeta_i$ are nonzero and the $\theta_i$ are distinct, Lanczos runs to full dimension.
The resulting Jacobi matrix is orthogonally similar to $D$, with normalized first eigenvector
components given by the normalized starting vector.

## Main results

* `Krylov.grade_toEuclideanLin_diagonal` gives the full grade of a fully supported vector.
* `Lanczos.isJacobiMatrix_tridiag_of_le_grade` shows that a Lanczos matrix is Jacobi up to
  the grade.
* `Lanczos.tridiag_diagonal_spectralData` recovers the prescribed spectrum and first
  eigenvector components.
* `Lanczos.eq_tridiag_diagonal_of_jacobiMatrix` proves uniqueness of the reconstruction.
* `Lanczos.tridiag_diagonal_eq_of_sq_eq` proves invariance under changing component signs.
* `Matrix.IsJacobiMatrix.leadingBlock_aeval_apply_first` identifies the leading-block
  quadrature moments.
* `Matrix.IsJacobiMatrix.leadingBlock_charpoly_eq_C_mul_lanczosPoly` identifies the monic
  Lanczos polynomials as the characteristic polynomials of proper leading blocks.
* `Matrix.IsJacobiMatrix.eigenvector_apply_eq_first_mul_eval_lanczosPoly` gives the components
  of a Jacobi eigenvector as evaluations of the Lanczos polynomials.
* `Matrix.IsJacobiMatrix.exists_eigenvalue_between_leading` finds a full-matrix eigenvalue
  in every open gap between distinct eigenvalues of a strict leading block.
* `OrthogonalPolynomial.jacobiMatrix_apply_eq_integral` gives the matrix entries of
  multiplication by the variable in an orthonormal polynomial basis.
-/

open Matrix

namespace Krylov

/-- A vector with all coordinates nonzero has full grade for a diagonal matrix with distinct
diagonal entries. Its Krylov matrix is a Vandermonde matrix with invertibly scaled rows. -/
theorem grade_toEuclideanLin_diagonal {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {θ ζ : Fin n → 𝕜} (hθ : Function.Injective θ) (hζ : ∀ i, ζ i ≠ 0) :
    grade (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) = n := by
  have hK : krylovMatrix (diagonal θ) ζ n = diagonal ζ * vandermonde θ := by
    ext i j
    rw [krylovMatrix_apply, diagonal_pow, mulVec_diagonal, diagonal_mul, vandermonde_apply]
    exact mul_comm _ _
  have hD : IsUnit (diagonal ζ) := (isUnit_iff_isUnit_det _).2 (by
    rw [det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 (fun i _ => hζ i)).isUnit)
  have hV : IsUnit (vandermonde θ) := (isUnit_iff_isUnit_det _).2
    ((det_vandermonde_ne_zero_iff.2 hθ).isUnit)
  rw [grade_eq_rank_krylovMatrix, Fintype.card_fin, hK, rank_of_isUnit _ (hD.mul hV),
    Fintype.card_fin]

end Krylov

namespace Lanczos

/-- At any order up to the grade, the real tridiagonal matrix of Lanczos has positive
subdiagonal and is a Jacobi matrix. -/
theorem isJacobiMatrix_tridiag_of_le_grade {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E →ₗ[𝕜] E) (v : E)
    [FiniteDimensional 𝕜 (Krylov.fullSubspace A v)] {n : ℕ} (hn : n ≤ Krylov.grade A v) :
    (tridiag A v n).IsJacobiMatrix := by
  refine ⟨tridiag_isSymm A v n, tridiag_isTridiagonal A v n, fun i j hij => ?_⟩
  rw [tridiag_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hij]
  exact lt_of_le_of_ne (beta_nonneg A v j) fun h =>
    (by
      have hgrade := (beta_eq_zero_iff (A := A) v j).1 h.symm
      have hi := i.isLt
      omega)

/-- For a real diagonal matrix with distinct entries, Lanczos from a vector with nonzero
coordinates gives a full Jacobi matrix $T$ with orthonormal eigenvector matrix $Z$.
The first row of $Z$ is the normalized starting vector. -/
theorem tridiag_diagonal_spectralData {n : ℕ} {θ ζ : Fin (n + 1) → ℝ}
    (hθ : Function.Injective θ) (hζ : ∀ i, ζ i ≠ 0) :
    let D := diagonal θ
    let q : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 ζ
    let T := tridiag D.toEuclideanLin q (n + 1)
    T.IsJacobiMatrix ∧ ∃ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      Zᵀ * Z = 1 ∧ T * Z = Z * D ∧ ∀ i, Z 0 i = ‖q‖⁻¹ * ζ i := by
  let D := diagonal θ
  let q : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 ζ
  let T := tridiag D.toEuclideanLin q (n + 1)
  let Q := Arnoldi.basisMatrix D q (n + 1)
  have hg : n + 1 ≤ Krylov.grade D.toEuclideanLin q :=
    (Krylov.grade_toEuclideanLin_diagonal hθ hζ).ge
  have hQ : Qᵀ * Q = 1 := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Arnoldi.conjTranspose_basisMatrix_mul_self D q hg
  have hQt : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  have hDs : D.toEuclideanLin.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2 (isHermitian_diagonal _)
  have hT : Qᵀ * D * Q = T := by
    have h := Arnoldi.conjTranspose_basisMatrix_mul_mul_basisMatrix D q hg
    simpa [conjTranspose_eq_transpose_of_trivial, hessenbergSq_eq_map_tridiag q hDs, T] using h
  have hq0 : q ≠ 0 := fun he => hζ 0 (by
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0) he
    exact h)
  change T.IsJacobiMatrix ∧ ∃ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    Zᵀ * Z = 1 ∧ T * Z = Z * D ∧ ∀ i, Z 0 i = ‖q‖⁻¹ * ζ i
  refine ⟨isJacobiMatrix_tridiag_of_le_grade _ _ hg, Qᵀ, by simpa using hQt, ?_, ?_⟩
  · calc T * Qᵀ = Qᵀ * D * (Q * Qᵀ) := by rw [← hT, Matrix.mul_assoc (Qᵀ * D)]
      _ = Qᵀ * D := by rw [hQt, mul_one]
  · intro i
    change (Arnoldi.vec D.toEuclideanLin q 0) i = ‖q‖⁻¹ * ζ i
    rw [Arnoldi.vec_zero _ _ hq0]
    simp [q, RCLike.ofReal_real_eq_id]

/-- A Jacobi matrix $T$ with orthonormal eigenvectors $Z$ of eigenvalues $\theta_i$ and first
coordinates $\zeta_i$ is the Lanczos matrix of $\operatorname{diag}(\theta_i)$ started at
$\zeta$. The transpose of the eigenvector matrix gives the square Arnoldi decomposition. -/
theorem eq_tridiag_diagonal_of_jacobiMatrix {n : ℕ} {θ ζ : Fin (n + 1) → ℝ}
    {T Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hT : T.IsJacobiMatrix)
    (hZ : Zᵀ * Z = 1) (hTZ : T * Z = Z * diagonal θ) (hfirst : ∀ i, Z 0 i = ζ i) :
    T = tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) (n + 1) := by
  have hDQ : diagonal θ * Zᵀ = Zᵀ * T := by
    simpa only [transpose_mul, diagonal_transpose, hT.isSymm.eq] using
      (congrArg Matrix.transpose hTZ).symm
  have hQQ : (Zᵀ)ᴴ * Zᵀ = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
    exact mul_eq_one_comm.1 hZ
  have hdec : (diagonal θ).IsArnoldiDecomposition Zᵀ T 0 :=
    ⟨⟨hQQ, by simp, by simpa using hDQ⟩, hT.isTridiagonal.isUpperHessenberg⟩
  have hH := (hdec.eq_basisMatrix fun i => hT.subdiagonal_pos i.succ i.castSucc rfl).2.2.1
  have hcol : (Zᵀ).col 0 = ζ := funext hfirst
  rw [Matrix.mulVec_single_one, hcol,
    hessenbergSq_eq_map_tridiag _ (isSymmetric_toEuclideanLin_iff.2 (isHermitian_diagonal θ))] at hH
  simpa using hH

/-- For a unit, fully supported starting vector and distinct real diagonal entries, the full
Lanczos matrix depends on the squares of the coordinates of the starting vector. -/
theorem tridiag_diagonal_eq_of_sq_eq {n : ℕ} {θ ζ η : Fin (n + 1) → ℝ}
    (hθ : Function.Injective θ) (hζ : ∀ i, ζ i ≠ 0)
    (hu : ‖(WithLp.toLp 2 ζ : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1)
    (hη : ∀ i, ζ i ^ 2 = η i ^ 2) :
    tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) (n + 1) =
      tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 η) (n + 1) := by
  obtain ⟨hT, Z, hZ, hTZ, hz⟩ := tridiag_diagonal_spectralData hθ hζ
  let T := tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) (n + 1)
  change T.IsJacobiMatrix at hT
  change T * Z = Z * diagonal θ at hTZ
  have hf (i : Fin (n + 1)) : Z 0 i = ζ i := by
    simpa [hu] using hz i
  let s : Fin (n + 1) → ℝ := fun i => η i / ζ i
  let S := diagonal s
  have hsq (i : Fin (n + 1)) : s i * s i = 1 := by
    change η i / ζ i * (η i / ζ i) = 1
    rw [← pow_two, div_pow, ← hη i, div_self (pow_ne_zero _ (hζ i))]
  have hS : Sᵀ * S = 1 := by
    rw [show Sᵀ = S by simp [S], show S * S = diagonal (fun i => s i * s i) by
      rw [show S = diagonal s from rfl, diagonal_mul_diagonal]]
    simp only [hsq, diagonal_one]
  have hcomm : diagonal θ * S = S * diagonal θ := by
    simp [S, diagonal_mul_diagonal, mul_comm]
  have hZs : (Z * S)ᵀ * (Z * S) = 1 := calc
    (Z * S)ᵀ * (Z * S) = Sᵀ * (Zᵀ * Z) * S := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hZ, mul_one, hS]
  have hTZs : T * (Z * S) = Z * S * diagonal θ := by
    rw [← Matrix.mul_assoc, hTZ, Matrix.mul_assoc Z, hcomm, ← Matrix.mul_assoc]
  refine eq_tridiag_diagonal_of_jacobiMatrix hT hZs hTZs fun i => ?_
  rw [show S = diagonal s from rfl, mul_diagonal, hf, show s i = η i / ζ i from rfl]
  rw [mul_comm, div_mul_cancel₀ _ (hζ i)]

end Lanczos

namespace Matrix.IsJacobiMatrix

variable {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- Every Jacobi matrix is determined by its diagonal and positive off-diagonal sequences,
with arbitrary continuation beyond its last row. -/
theorem exists_symmTridiagonalOf (hT : T.IsJacobiMatrix) :
    ∃ d b : ℕ → ℝ, T = Matrix.symmTridiagonalOf d b (n + 1) ∧
      ∀ j, j + 1 < n + 1 → 0 < b j := by
  let d (i : ℕ) := if hi : i < n + 1 then T ⟨i, hi⟩ ⟨i, hi⟩ else 0
  let b (j : ℕ) := if hj : j + 1 < n + 1 then T ⟨j + 1, hj⟩ ⟨j, by omega⟩ else 0
  refine ⟨d, b, ?_, fun j hj => ?_⟩
  · ext i j
    rw [Matrix.symmTridiagonalOf_apply]
    split_ifs with heq hi hj
    · obtain rfl : i = j := Fin.ext heq
      simp only [d, dite_eq_left i.isLt]
    · have hjlt : (i : ℕ) + 1 < n + 1 := by omega
      have hjeq : (⟨(i : ℕ) + 1, hjlt⟩ : Fin (n + 1)) = j := Fin.ext hi
      rw [show b i = T j i by simp only [b, dite_eq_left hjlt, hjeq]]
      exact hT.isSymm.apply _ _
    · have hilt : (j : ℕ) + 1 < n + 1 := by omega
      have hieq : (⟨(j : ℕ) + 1, hilt⟩ : Fin (n + 1)) = i := Fin.ext hj
      rw [show b j = T i j by simp only [b, dite_eq_left hilt, hieq]]
    · exact Matrix.isTridiagonal_iff_fin.1 hT.isTridiagonal i j (by omega)
  · simp only [b, dite_eq_left hj]
    exact hT.subdiagonal_pos _ _ rfl

/-- For a Jacobi matrix the first coordinate vector has full grade. -/
theorem grade_basisFun (hT : T.IsJacobiMatrix) :
    Krylov.grade T.toEuclideanLin (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) = n + 1 := by
  rw [EuclideanSpace.basisFun_apply]
  change Krylov.grade T.toEuclideanLin (WithLp.toLp 2 (Pi.single 0 1)) = n + 1
  rw [Krylov.grade_eq_rank_krylovMatrix, Fintype.card_fin,
    Matrix.rank_of_isUnit _ hT.isUnreducedUpperHessenberg.isUnit_krylovMatrix,
    Fintype.card_fin]

/-- Applied to a Jacobi matrix from the first coordinate vector, Lanczos returns the leading
principal submatrix at every order up to the full order. -/
theorem lanczos_tridiag_basisFun (hT : T.IsJacobiMatrix) {m : ℕ} (hm : m ≤ n + 1) :
    Lanczos.tridiag T.toEuclideanLin (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) m =
      T.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hvec (i : Fin (n + 1)) : Arnoldi.vec T.toEuclideanLin (b 0) i = b i := by
    simpa [b] using Arnoldi.vec_toEuclideanLin_map_of_positive_tridiagonal
      (𝕜 := ℝ) hT.isTridiagonal hT.subdiagonal_pos i
  have hentry (i j : Fin (n + 1)) : inner ℝ (b i) (T.toEuclideanLin (b j)) = T i j := by
    rw [← OrthonormalBasis.repr_apply_apply b, EuclideanSpace.basisFun_repr]
    change WithLp.ofLp (T.toEuclideanLin (b j)) i = T i j
    rw [ofLp_toEuclideanLin, show b j = EuclideanSpace.single j 1 from
      EuclideanSpace.basisFun_apply (Fin (n + 1)) ℝ j]
    change (T *ᵥ Pi.single j 1) i = T i j
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have hH : Arnoldi.hessenbergSq T.toEuclideanLin (b 0) m =
      T.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
    ext i j
    change inner ℝ (Arnoldi.vec T.toEuclideanLin (b 0) (Fin.castLE hm i))
      (T.toEuclideanLin (Arnoldi.vec T.toEuclideanLin (b 0) (Fin.castLE hm j))) = _
    rw [hvec, hvec, hentry]
    rfl
  simpa only [Lanczos.hessenbergSq_eq_map_tridiag _
    (isSymmetric_toEuclideanLin_iff.2 hT.isHermitian),
    Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using hH

/-- The characteristic polynomial of a proper leading block is a positive scalar multiple
of the Lanczos polynomial for the full Jacobi matrix and its first coordinate vector. -/
theorem leadingBlock_charpoly_eq_C_mul_lanczosPoly (hT : T.IsJacobiMatrix) {m : ℕ}
    (hm : m < n + 1) :
    let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
    ∃ c > 0, (T.submatrix (Fin.castLE hm.le) (Fin.castLE hm.le)).charpoly =
      Polynomial.C c * Lanczos.poly T.toEuclideanLin v m := by
  let A := T.toEuclideanLin
  let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  have hA : A.IsSymmetric := isSymmetric_toEuclideanLin_iff.2 hT.isHermitian
  have hg : m < Krylov.grade A v := by
    rw [show Krylov.grade A v = n + 1 from hT.grade_basisFun]
    exact hm
  let c := ‖v‖ * ∏ i ∈ Finset.range m, Lanczos.beta A v i
  have hc : 0 ≤ c := mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun i _ => Lanczos.beta_nonneg A v i)
  refine ⟨c, lt_of_le_of_ne hc (Lanczos.norm_mul_prod_beta_ne_zero A v hg).symm, ?_⟩
  have h := Lanczos.charpoly_tridiag_eq hA v hg
  simp only [Algebra.algebraMap_self, Polynomial.map_id] at h
  rw [← hT.lanczos_tridiag_basisFun hm.le]
  exact h

/-- A Jacobi eigenvector is proportional to the vector of Lanczos polynomials evaluated at
its eigenvalue. Its first coordinate supplies the scalar of proportionality. -/
theorem eigenvector_apply_eq_first_mul_eval_lanczosPoly (hT : T.IsJacobiMatrix)
    {θ : ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : T.toEuclideanLin z = θ • z) (i : Fin (n + 1)) :
    z i = z 0 *
      (Lanczos.poly T.toEuclideanLin (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) i).eval θ := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let A := T.toEuclideanLin
  let p := Lanczos.poly A (b 0) i
  have hA : A.IsSymmetric := isSymmetric_toEuclideanLin_iff.2 hT.isHermitian
  have hsym (q : Polynomial ℝ) : (Polynomial.aeval A q).IsSymmetric := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | monomial k a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact LinearMap.IsSymmetric.smul (star_trivial _) (hA.pow k)
  have hvec : Polynomial.aeval A p (b 0) = b i := by
    rw [Lanczos.aeval_poly hA]
    exact Arnoldi.vec_toEuclideanLin_map_of_positive_tridiagonal
      (𝕜 := ℝ) hT.isTridiagonal hT.subdiagonal_pos i
  have hcoordinate (j : Fin (n + 1)) : inner ℝ (b j) z = z j := by
    rw [← OrthonormalBasis.repr_apply_apply b, EuclideanSpace.basisFun_repr]
  change z i = z 0 * p.eval θ
  rw [← hcoordinate i, ← hvec, hsym p, Module.End.aeval_apply_of_mem_apply_eq_smul hz,
    real_inner_smul_right, hcoordinate 0, mul_comm]

/-- The last coordinate of every nonzero Jacobi eigenvector is nonzero. Reversing the
coordinates gives a Jacobi eigenvector with this value in its first coordinate. -/
theorem last_ne_zero (hT : T.IsJacobiMatrix) {θ : ℝ} {z : Fin (n + 1) → ℝ} (hz : z ≠ 0)
    (heig : T.mulVec z = θ • z) : z (Fin.last n) ≠ 0 := by
  let S := T.submatrix Fin.rev Fin.rev
  have hS : S.IsJacobiMatrix := by
    refine ⟨hT.isSymm.submatrix Fin.rev, Matrix.isTridiagonal_iff_fin.2 ?_, ?_⟩
    · intro i j hij
      change T i.rev j.rev = 0
      exact Matrix.isTridiagonal_iff_fin.1 hT.isTridiagonal _ _ (by
        have hi := Fin.rev_add_cast i
        have hj := Fin.rev_add_cast j
        omega)
    · intro i j hij
      change 0 < T i.rev j.rev
      rw [hT.isSymm.apply]
      exact hT.subdiagonal_pos _ _ (by
        have hi := Fin.rev_add_cast i
        have hj := Fin.rev_add_cast j
        omega)
  let y := z ∘ Fin.rev
  have hy : y ≠ 0 := by
    intro h
    apply hz
    funext i
    simpa [y] using congrFun h i.rev
  have hSy : S.mulVec y = θ • y := by
    let r : Equiv.Perm (Fin (n + 1)) := Fin.revPerm
    change (T.submatrix Fin.rev r).mulVec y = θ • y
    rw [Matrix.submatrix_mulVec_equiv]
    have hcomp : y ∘ r.symm = z := by
      funext i
      change z i.rev.rev = z i
      rw [Fin.rev_rev]
    rw [hcomp, heig]
    rfl
  simpa [y] using hS.first_ne_zero (Nat.succ_pos n) hy hSy

/-- Let $S$ be the leading block of order $m+1$ of a Jacobi matrix $T$. Then $p(T)$ and $p(S)$
have the same first diagonal entry for every polynomial $p$ of degree less than $2(m+1)$. -/
theorem leadingBlock_aeval_apply_first (hT : T.IsJacobiMatrix) {m : ℕ} (hm : m + 1 ≤ n + 1)
    {p : Polynomial ℝ} (hp : p.natDegree < 2 * (m + 1)) :
    Polynomial.aeval T p 0 0 =
      Polynomial.aeval (T.submatrix (Fin.castLE hm) (Fin.castLE hm)) p 0 0 := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let v := b 0
  let A := T.toEuclideanLin
  have hAs : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hT.isHermitian
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  have hdimK : Module.finrank ℝ (Krylov.subspace A v (m + 1)) = m + 1 := by
    rw [Krylov.finrank_subspace, hT.grade_basisFun, min_eq_left hm]
  have hv : ‖v‖ = 1 := b.orthonormal.1 0
  have hfull :
      (∫ t, p.eval t ∂(Krylov.spectralMeasure hAs hdim v)) = Polynomial.aeval T p 0 0 := by
    have h := (Krylov.inner_aeval_eq_integral hAs hdim v p).symm
    simp only [Algebra.algebraMap_self, Polynomial.map_id, RCLike.ofReal_real_eq_id, id_eq] at h
    change (∫ t, p.eval t ∂(Krylov.spectralMeasure hAs hdim v)) =
      inner ℝ (b 0) (Polynomial.aeval T.toEuclideanLin p (b 0)) at h
    rw [h, ← OrthonormalBasis.repr_apply_apply b, EuclideanSpace.basisFun_repr,
      ← Matrix.toEuclideanLin_aeval]
    change WithLp.ofLp ((Polynomial.aeval T p).toEuclideanLin (b 0)) 0 = _
    rw [ofLp_toEuclideanLin, show b 0 = EuclideanSpace.single 0 1 from
      EuclideanSpace.basisFun_apply (Fin (n + 1)) ℝ 0]
    change (Polynomial.aeval T p *ᵥ Pi.single 0 1) 0 = _
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have h := Lanczos.gauss_quadrature hAs hdim v (Nat.succ_pos m) hdimK hp
  rw [hfull, Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hAs v
    (Nat.succ_pos m) hdimK, hv, one_pow, one_mul,
    ← Matrix.IsHermitian.aeval_apply_self] at h
  exact h.trans (congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ =>
    Polynomial.aeval M p 0 0) (hT.lanczos_tridiag_basisFun hm))

/-- Every open gap between two distinct eigenvalues of a strict leading block of a Jacobi
matrix contains an eigenvalue of the full matrix. -/
theorem exists_eigenvalue_between_leading (hT : T.IsJacobiMatrix) {m : ℕ} (hm : m + 1 < n + 1)
    (i j : Fin (m + 1))
    (hij : (hT.leadingBlock hm.le).isHermitian.eigenvalues i <
      (hT.leadingBlock hm.le).isHermitian.eigenvalues j) :
    ∃ k, (hT.leadingBlock hm.le).isHermitian.eigenvalues i < hT.isHermitian.eigenvalues k ∧
      hT.isHermitian.eigenvalues k < (hT.leadingBlock hm.le).isHermitian.eigenvalues j := by
  classical
  let S := T.submatrix (Fin.castLE hm.le) (Fin.castLE hm.le)
  let hS := (hT.leadingBlock hm.le).isHermitian
  let θ := hS.eigenvalues
  let e := hT.isHermitian.eigenvalues
  let w := fun k => (hT.isHermitian.eigenvectorBasis k 0) ^ 2
  let s := (Finset.univ.erase i).erase j
  let q := Lagrange.nodal s θ
  let u := Polynomial.X - Polynomial.C (θ i)
  let v := Polynomial.X - Polynomial.C (θ j)
  let p := u * v * q ^ 2
  have hij' : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
  have hij'' : i.val ≠ j.val := fun h => hij' (Fin.ext h)
  have hs : s.card = m - 1 := by
    rw [show s = (Finset.univ.erase i).erase j from rfl,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hij', Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hp : p.natDegree < 2 * (m + 1) := by
    have hu : u.natDegree = 1 := Polynomial.natDegree_X_sub_C _
    have hv : v.natDegree = 1 := Polynomial.natDegree_X_sub_C _
    have huv := Polynomial.natDegree_mul_le (p := u) (q := v)
    rw [hu, hv] at huv
    have hq : q.natDegree = m - 1 := by
      change (Lagrange.nodal s θ).natDegree = _
      rw [Lagrange.natDegree_nodal, hs]
    have hq2 : (q ^ 2).natDegree = 2 * (m - 1) := by rw [Polynomial.natDegree_pow, hq]
    exact lt_of_le_of_lt (Polynomial.natDegree_mul_le (p := u * v) (q := q ^ 2))
      (by rw [hq2]; omega)
  have hEval (t : ℝ) : p.eval t = (t - θ i) * (t - θ j) * q.eval t ^ 2 := by
    simp [p, u, v]
  have hvanish (l : Fin (m + 1)) : p.eval (θ l) = 0 := by
    rw [hEval]
    by_cases hl : l = i
    · simp [hl]
    by_cases hlj : l = j
    · simp [hlj]
    have hmem : l ∈ s := Finset.mem_erase.2 ⟨hlj, Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩⟩
    have hroot : q.eval (θ l) = 0 := Lagrange.eval_nodal_at_node hmem
    simp [hroot]
  have hsum : ∑ k, w k * p.eval (e k) = 0 := by
    have h := hT.leadingBlock_aeval_apply_first hm.le hp
    change Polynomial.aeval T p 0 0 = Polynomial.aeval S p 0 0 at h
    rw [Matrix.IsHermitian.aeval_apply_self hT.isHermitian p 0,
      Matrix.IsHermitian.aeval_apply_self hS p 0] at h
    change (∑ k, w k * p.eval (e k)) = ∑ l, (hS.eigenvectorBasis l 0) ^ 2 * p.eval (θ l) at h
    simpa [hvanish] using h
  have hex : ∃ k, ∀ l, e k ≠ θ l := by
    by_contra! hall
    choose f hf using hall
    have hinj : Function.Injective f := fun k l h => hT.eigenvalues_injective (by
      change e k = e l
      rw [hf k, hf l, h])
    have hcard := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hcard
    omega
  have hw (k : Fin (n + 1)) : 0 < w k := by
    let z := hT.isHermitian.eigenvectorBasis k
    have hz : (⇑z : Fin (n + 1) → ℝ) ≠ 0 := by
      intro h
      apply hT.isHermitian.eigenvectorBasis.orthonormal.linearIndependent.ne_zero k
      exact WithLp.ofLp_injective 2 h
    exact sq_pos_of_ne_zero (hT.first_ne_zero (Nat.succ_pos n) hz
      (hT.isHermitian.mulVec_eigenvectorBasis k))
  change ∃ k, θ i < e k ∧ e k < θ j
  by_contra! hno
  have hnonneg (k : Fin (n + 1)) : 0 ≤ p.eval (e k) := by
    rw [hEval]
    rcases le_or_gt (e k) (θ i) with hlow | hhigh
    · exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hlow)
        (sub_nonpos.2 (hlow.trans hij.le))) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg (sub_nonneg.2 hhigh.le)
        (sub_nonneg.2 (hno k hhigh))) (sq_nonneg _)
  obtain ⟨k, hk⟩ := hex
  have hq : q.eval (e k) ≠ 0 := Lagrange.eval_nodal_not_at_node (fun l _ => hk l)
  have hpos : 0 < p.eval (e k) := by
    rw [hEval]
    rcases lt_or_gt_of_ne (hk i) with hlow | hhigh
    · exact mul_pos (mul_pos_of_neg_of_neg (sub_neg.2 hlow)
        (sub_neg.2 (hlow.trans hij))) (sq_pos_of_ne_zero hq)
    · exact mul_pos (mul_pos (sub_pos.2 hhigh)
        (sub_pos.2 (lt_of_le_of_ne (hno k hhigh) (Ne.symm (hk j))))) (sq_pos_of_ne_zero hq)
  have hpSum : 0 < ∑ l, w l * p.eval (e l) := Finset.sum_pos'
    (fun l _ => mul_nonneg (hw l).le (hnonneg l)) ⟨k, Finset.mem_univ _, mul_pos (hw k) hpos⟩
  rw [hsum] at hpSum
  exact (lt_irrefl 0) hpSum

end Matrix.IsJacobiMatrix

namespace OrthogonalPolynomial

open MeasureTheory Polynomial
open scoped Polynomial

variable {μ : Measure ℝ}

/-- An orthonormal polynomial corresponding to a positive squared norm still has its assigned
degree. -/
theorem degree_orthonormalFamily_of_normSq_pos {k : ℕ} (h : 0 < normSq μ k) :
    (orthonormalFamily μ k).degree = k := by
  have hnorm : 0 < normOf μ k := Real.sqrt_pos.2 h
  rw [orthonormalFamily, degree_C_mul_of_isUnit (inv_ne_zero hnorm.ne').isUnit, degree_family]

/-- The recurrence matrix of an orthogonal polynomial family is Jacobi as long as each of
the involved polynomials has positive norm. -/
theorem isJacobiMatrix_jacobiMatrix {n : ℕ} (hnorm : ∀ k < n, 0 < normSq μ k) :
    (jacobiMatrix μ n).IsJacobiMatrix := by
  refine ⟨jacobiMatrix_isSymm μ n, Matrix.isTridiagonal_iff_fin.2 ?_, ?_⟩
  · intro i j hij
    rw [jacobiMatrix_apply, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  · intro i j hij
    rw [jacobiMatrix_apply, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left hij.symm]
    exact Real.sqrt_pos.2 (div_pos (hnorm _ (hij.symm ▸ i.isLt)) (hnorm _ j.isLt))

/-- The Jacobi matrix is the matrix of multiplication by $X$ compressed to the orthonormal
polynomials of degrees less than its order, provided these polynomials have positive norm.
Its $(i,j)$ entry is $\int t\,\varphi_i(t)\varphi_j(t)\,d\mu(t)$. -/
theorem jacobiMatrix_apply_eq_integral
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {n : ℕ}
    (hnorm : ∀ k < n, 0 < normSq μ k) (i j : Fin n) :
    jacobiMatrix μ n i j =
      ∫ t, t * (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t ∂μ := by
  let J (a b : ℕ) := ∫ t, t * (family μ a).eval t * (family μ b).eval t ∂μ
  let I (a b : ℕ) := ∫ t, t * (orthonormalFamily μ a).eval t * (orthonormalFamily μ b).eval t ∂μ
  have hI : ∀ a b, I a b = ((normOf μ a)⁻¹ * (normOf μ b)⁻¹) * J a b := by
    intro a b
    unfold I J
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [eval_orthonormalFamily, eval_orthonormalFamily]
    ring
  have hJ (a b : ℕ) : J a b = J b a :=
    integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)
  have hsym (a b : ℕ) : I a b = I b a := by
    rw [hI, hI, hJ a b]
    ring
  have hnormSq (a : ℕ) (ha : a < n) : normOf μ a ^ 2 = normSq μ a :=
    Real.sq_sqrt (hnorm a ha).le
  have hdiag (a : ℕ) (ha : a < n) : I a a = alpha μ a := by
    rw [hI, alpha, ← hnormSq a ha]
    have h : J a a = ∫ t, t * (family μ a).eval t ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)
    rw [h, div_eq_mul_inv, ← inv_pow, sq]
    ring
  have hJoff (a : ℕ) (ha : a + 1 < n) : J (a + 1) a = normSq μ (a + 1) :=
    integral_X_mul_family_succ_mul_family_of_integrable hint
      (fun j hj => (hnorm j (hj.trans ha)).ne')
  have hoff (a : ℕ) (ha : a + 1 < n) : I (a + 1) a = √(beta μ a) := by
    rw [hI, hJoff a ha, beta, Real.sqrt_div (hnorm _ ha).le]
    change (normOf μ (a + 1))⁻¹ * (normOf μ a)⁻¹ * normSq μ (a + 1) =
      normOf μ (a + 1) / normOf μ a
    rw [← hnormSq (a + 1) ha]
    have h₁ : 0 < normOf μ (a + 1) := Real.sqrt_pos.2 (hnorm _ ha)
    have h₀ : 0 < normOf μ a := Real.sqrt_pos.2 (hnorm a (by omega))
    field_simp [h₁.ne', h₀.ne']
  have hzero (a b : ℕ) (hb : b < n) (hab : a + 1 < b) : I a b = 0 := by
    have hdeg : (X * family μ a).degree < (b : WithBot ℕ) := by
      rw [degree_mul, degree_X, degree_family]
      exact_mod_cast (show 1 + a < b by omega)
    rw [hI]
    have h : J a b = ∫ t, (family μ b).eval t * (X * family μ a).eval t ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => by
        dsimp only
        rw [eval_mul, eval_X]
        ring)
    rw [h, integral_family_mul_of_degree_lt_of_integrable hint
      (fun k hk => (hnorm k (hk.trans hb)).ne') hdeg, mul_zero]
  change jacobiMatrix μ n i j = I i j
  rw [jacobiMatrix_apply]
  split_ifs with heq hsucc hsuc'
  · rw [heq, hdiag _ j.isLt]
  · have hjlt : (i : ℕ) + 1 < n := by omega
    rw [hsucc, hsym i.val (i.val + 1), hoff _ hjlt]
  · have hilt : (j : ℕ) + 1 < n := by omega
    rw [hsuc', hoff _ hilt]
  · rcases lt_or_ge (i : ℕ) j with hlt | hle
    · exact (hzero _ _ j.isLt (by omega)).symm
    · rw [hsym]
      exact (hzero _ _ i.isLt (by omega)).symm

/-- Orthonormal polynomials of degree below $n$ have identity Gram matrix once their
norms are positive and all polynomial evaluations are integrable. -/
theorem integral_orthonormalFamily_mul_of_normSq_pos
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {n : ℕ}
    (hnorm : ∀ k < n, 0 < normSq μ k) (i j : Fin n) :
    (∫ t, (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t ∂μ) =
      if i = j then 1 else 0 := by
  have he (t : ℝ) :
      (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t =
        ((normOf μ i)⁻¹ * (normOf μ j)⁻¹) * ((family μ i).eval t * (family μ j).eval t) := by
    rw [eval_orthonormalFamily, eval_orthonormalFamily]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have h : (∫ t, (family μ i).eval t * (family μ i).eval t ∂μ) = normSq μ i :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => (sq _).symm)
    have hs : normOf μ i ^ 2 = normSq μ i := Real.sq_sqrt (hnorm _ i.isLt).le
    rw [h, ← hs]
    have hne : normOf μ i ≠ 0 := (Real.sqrt_pos.2 (hnorm _ i.isLt)).ne'
    field_simp [hne]
  · rw [ite_eq_right hij]
    have horth (a b : Fin n) (h : (b : ℕ) < a) :
        ∫ t, (family μ a).eval t * (family μ b).eval t ∂μ = 0 :=
      integral_family_mul_of_degree_lt_of_integrable hint
        (fun k hk => (hnorm k (hk.trans a.isLt)).ne') (by rw [degree_family]; exact_mod_cast h)
    rcases lt_or_gt_of_ne hij with h | h
    · simp_rw [mul_comm ((family μ i).eval _), horth j i (Fin.lt_def.1 h), mul_zero]
    · rw [horth i j (Fin.lt_def.1 h), mul_zero]

end OrthogonalPolynomial
