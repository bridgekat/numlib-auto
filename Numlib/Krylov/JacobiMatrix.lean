/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Perturbation
import Numlib.Eigen.Sturm
import Numlib.Krylov.Decomposition

/-!
# Jacobi matrices and Arnoldi vectors

An orthonormal basis in which a matrix has an upper Hessenberg representation with positive
subdiagonal is the Arnoldi basis generated from its first vector. In particular, starting Arnoldi at
the first coordinate vector of a tridiagonal matrix with positive subdiagonal produces the
coordinate basis in order. For a Jacobi matrix the same statement applies to Hermitian Lanczos.

## Main definitions

* `Matrix.IsJacobiMatrix` is the predicate of real symmetric tridiagonal matrices with
  strictly positive subdiagonal.
* `Matrix.leadingZeroPad` extends a leading-block vector by zeros.

## Main results

* `Matrix.IsJacobiMatrix.eigenvalues_injective` gives simplicity of the Jacobi spectrum.
* `Matrix.IsJacobiMatrix.first_ne_zero` gives nonvanishing of the first entry of an eigenvector.
* `Matrix.IsJacobiMatrix.leadingBlock_residual_norm` computes the norm of the padded residual.
* `Matrix.IsJacobiMatrix.leadingBlock_persistence` bounds the displacement of a leading
  block eigenvalue by the residual norm of its padded eigenvector.
* `Arnoldi.vec_eq_col_of_mul_eq_mul` recovers the vectors of a square Arnoldi decomposition.
* `Arnoldi.vec_toEuclideanLin_map_of_positive_tridiagonal` identifies the Arnoldi vectors with
  the standard basis vectors.
-/

/-- A real square matrix is Jacobi if it is symmetric and tridiagonal, and each entry on its
first subdiagonal is strictly positive. -/
structure Matrix.IsJacobiMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The matrix is symmetric. -/
  isSymm : T.IsSymm
  /-- The matrix is supported on the main diagonal and the adjacent diagonals. -/
  isTridiagonal : T.IsTridiagonal
  /-- Every subdiagonal entry is positive. -/
  subdiagonal_pos : ∀ i j : Fin n, (j : ℕ) + 1 = i → 0 < T i j

/-- Embed a vector in a larger real Euclidean space by padding its trailing entries with zeros. -/
def Matrix.leadingZeroPad {m n : ℕ} (_h : m ≤ n) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => if hi : (i : ℕ) < m then z ⟨i, hi⟩ else 0

/-- Trailing zero padding preserves the Euclidean norm. -/
theorem Matrix.norm_leadingZeroPad {m n : ℕ} (h : m ≤ n) (z : EuclideanSpace ℝ (Fin m)) :
    ‖Matrix.leadingZeroPad h z‖ = ‖z‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_eq_sum_castLE_of_forall_le h _ fun j hj => by
      simp [leadingZeroPad, dite_eq_right hj.not_gt]]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [leadingZeroPad, j.isLt]

namespace Matrix.IsJacobiMatrix

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}

/-- A real Jacobi matrix is Hermitian. -/
theorem isHermitian (hT : T.IsJacobiMatrix) : T.IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 hT.isSymm

/-- A Jacobi matrix is unreduced upper Hessenberg because it is tridiagonal and its
subdiagonal entries are positive. -/
theorem isUnreducedUpperHessenberg (hT : T.IsJacobiMatrix) : T.IsUnreducedUpperHessenberg :=
  Matrix.isUnreducedUpperHessenberg_iff_fin.2
    ⟨hT.isTridiagonal.isUpperHessenberg, fun i hi =>
      (hT.subdiagonal_pos ⟨i + 1, hi⟩ ⟨i, by omega⟩ rfl).ne'⟩

/-- The real eigenvalues in an orthonormal diagonalization of a Jacobi matrix are pairwise
distinct. -/
theorem eigenvalues_injective (hT : T.IsJacobiMatrix) :
    Function.Injective hT.isHermitian.eigenvalues :=
  hT.isHermitian.eigenvalues_injective_of_isUnreducedUpperHessenberg hT.isUnreducedUpperHessenberg

/-- An eigenvector of a Jacobi matrix of positive order has nonzero first component. -/
theorem first_ne_zero (hT : T.IsJacobiMatrix) (hn : 0 < n) {θ : ℝ} {z : Fin n → ℝ}
    (hz : z ≠ 0) (hθ : T *ᵥ z = θ • z) : z ⟨0, hn⟩ ≠ 0 :=
  hT.isUnreducedUpperHessenberg.apply_zero_ne_zero_of_isSymm hT.isSymm hθ hz hn

/-- A leading principal submatrix of a Jacobi matrix is a Jacobi matrix. -/
theorem leadingBlock {m : ℕ} (hT : T.IsJacobiMatrix) (h : m ≤ n) :
    (T.submatrix (Fin.castLE h) (Fin.castLE h)).IsJacobiMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    exact hT.isSymm.apply _ _
  · refine isTridiagonal_iff_fin.2 fun i j hij => ?_
    exact isTridiagonal_iff_fin.1 hT.isTridiagonal _ _ hij
  · exact fun i j hij => hT.subdiagonal_pos (Fin.castLE h i) (Fin.castLE h j) hij

/-- If $z$ is an eigenvector of the leading block of order $m+1$ of a Jacobi matrix $T$,
its extension $x$ by zeros has residual norm $\|Tx-\theta x\|=T_{m+1,m}|z_m|$.
Indices start at zero. -/
theorem leadingBlock_residual_norm (hT : T.IsJacobiMatrix) {m : ℕ} (h : m + 1 < n)
    {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))}
    (heig : (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).toEuclideanLin z = θ • z) :
    let x := leadingZeroPad h.le z
    ‖T.toEuclideanLin x - θ • x‖ = T ⟨m + 1, h⟩ ⟨m, by omega⟩ * |z (Fin.last m)| := by
  let y : Fin n → ℝ := fun i => if hi : (i : ℕ) < m + 1 then z ⟨i, hi⟩ else 0
  have hy (i : Fin (m + 1)) : y (Fin.castLE h.le i) = z i := by
    dsimp [y]
    rw [ite_eq_left i.isLt]
  have hy0 (i : Fin n) (hi : m + 1 ≤ (i : ℕ)) : y i = 0 :=
    dite_eq_right hi.not_gt
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hmul (i : Fin n) :
      (T *ᵥ y) i = ∑ j : Fin (m + 1), T i (Fin.castLE h.le j) * z j := by
    rw [Matrix.mulVec, dotProduct, Fin.sum_eq_sum_castLE_of_forall_le h.le _
      fun j hj => by rw [hy0 j hj, mul_zero]]
    exact Finset.sum_congr rfl fun j _ => by rw [hy]
  let i₀ : Fin n := ⟨m + 1, h⟩
  let r := T i₀ ⟨m, by omega⟩ * z (Fin.last m)
  have hres (i : Fin n) : (T.toEuclideanLin x - θ • x) i = if i = i₀ then r else 0 := by
    change (T *ᵥ y) i - θ * y i = _
    rw [hmul]
    rcases lt_trichotomy (i : ℕ) (m + 1) with hi | hi | hi
    · let j : Fin (m + 1) := ⟨i, hi⟩
      have hj : Fin.castLE h.le j = i := Fin.ext rfl
      have hne : i ≠ i₀ := fun he => hi.ne (congrArg Fin.val he)
      have he := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v j) heig
      change (∑ l : Fin (m + 1), T (Fin.castLE h.le j) (Fin.castLE h.le l) * z l) =
        θ * z j at he
      rw [← hj, hy, he, sub_self, hj, ite_eq_right hne]
    · have heq : i = i₀ := Fin.ext hi
      rw [heq, ite_eq_left rfl, hy0 _ (by exact le_rfl), mul_zero, sub_zero,
        Finset.sum_eq_single (Fin.last m)]
      · rfl
      · intro j _ hj
        have hjm : (j : ℕ) ≠ m := fun hval => hj (Fin.ext hval)
        rw [isTridiagonal_iff_fin.1 hT.isTridiagonal _ _ (Or.inl (by
          have hval := j.isLt
          change (j : ℕ) + 1 < m + 1
          omega)), zero_mul]
      · simp
    · have hne : i ≠ i₀ := fun he => hi.ne' (congrArg Fin.val he)
      rw [ite_eq_right hne, hy0 i hi.le, mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [isTridiagonal_iff_fin.1 hT.isTridiagonal _ _ (Or.inl (by
        have hval := j.isLt
        change (j : ℕ) + 1 < i
        omega)), zero_mul]
  have hresnorm : ‖T.toEuclideanLin x - θ • x‖ = |r| := by
    have hsq : ‖T.toEuclideanLin x - θ • x‖ ^ 2 = |r| ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, sq_abs]
      simp only [hres]
      rw [Finset.sum_eq_single i₀]
      · rw [ite_eq_left rfl]
      · intro i _ hi
        simp [hi]
      · simp
    exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg r) two_ne_zero).1 hsq
  change ‖T.toEuclideanLin x - θ • x‖ = T i₀ ⟨m, by omega⟩ * |z (Fin.last m)|
  rw [hresnorm, show r = T i₀ ⟨m, by omega⟩ * z (Fin.last m) by rfl,
    abs_mul, abs_of_pos (hT.subdiagonal_pos _ _ rfl)]

/-- Let $S$ be the leading principal block of order $m+1$ of a Jacobi matrix $T$ of order $n$,
with $m+1<n$. If $Sz=\theta z$ and $\|z\|=1$, some eigenvalue of $T$ lies within
$T_{m+1,m}|z_m|$ of $\theta$. Indices start at zero. -/
theorem leadingBlock_persistence (hT : T.IsJacobiMatrix) {m : ℕ} (h : m + 1 < n)
    {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : ‖z‖ = 1)
    (heig : (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).toEuclideanLin z = θ • z) :
    ∃ μ ∈ spectrum ℝ T, |μ - θ| ≤ T ⟨m + 1, h⟩ ⟨m, by omega⟩ * |z (Fin.last m)| := by
  let x := leadingZeroPad h.le z
  have hnorm : ‖x‖ = 1 := (norm_leadingZeroPad h.le z).trans hz
  obtain ⟨μ, hμ, hd⟩ := (Matrix.isSymmetric_toEuclideanLin_iff.2
    hT.isHermitian).exists_hasEigenvalue_dist_le θ
      (norm_ne_zero_iff.1 (by rw [hnorm]; norm_num))
  refine ⟨μ, (Matrix.hasEigenvalue_toEuclideanLin_iff _ _).1 hμ, ?_⟩
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
  change ‖μ - θ‖ ≤ ‖T.toEuclideanLin x - θ • x‖ / ‖x‖ at hd
  rw [hnorm, div_one, show ‖T.toEuclideanLin x - θ • x‖ = _ from
    hT.leadingBlock_residual_norm h heig] at hd
  simpa only [Real.norm_eq_abs] using hd

end Matrix.IsJacobiMatrix

namespace Arnoldi

open Matrix

open scoped Matrix ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Let $Q$ be an orthonormal basis in matrix form, and suppose $AQ = QH$ for an upper
Hessenberg matrix $H$ with positive subdiagonal. Arnoldi applied to $A$ from the first column of $Q$
generates the columns of $Q$ in order. -/
theorem vec_eq_col_of_mul_eq_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} {Q : Matrix ι (Fin (n + 1)) 𝕜}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hQ : Qᴴ * Q = 1) (hAQ : A * Q = Q * H)
    (hH : H.IsUpperHessenberg) (hpos : ∀ i : Fin n, 0 < H i.succ i.castSucc)
    (i : Fin (n + 1)) :
    vec A.toEuclideanLin (WithLp.toLp 2 (Q.col 0)) i = WithLp.toLp 2 (Q.col i) := by
  have hdecomp : A.IsArnoldiDecomposition Q H 0 := ⟨⟨hQ, by simp, by simpa using hAQ⟩, hH⟩
  have hb := (hdecomp.eq_basisMatrix hpos).2.1
  rw [Matrix.mulVec_single_one] at hb
  apply WithLp.ofLp_injective 2
  rw [WithLp.ofLp_toLp, ← col_basisMatrix]
  exact congrArg (fun M => M.col i) hb.symm

/-- If $T$ is a real tridiagonal matrix with positive subdiagonal, Arnoldi applied to $T$ and
the first coordinate vector outputs the standard orthonormal basis in order. The process may use
any scalar field `𝕜` with an `RCLike` instance. -/
theorem vec_toEuclideanLin_map_of_positive_tridiagonal
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (htri : T.IsTridiagonal)
    (hpos : ∀ i j : Fin (n + 1), (j : ℕ) + 1 = i → 0 < T i j) (i : Fin (n + 1)) :
    vec (T.map (algebraMap ℝ 𝕜)).toEuclideanLin (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜 0) i =
      EuclideanSpace.basisFun (Fin (n + 1)) 𝕜 i := by
  let H := T.map (algebraMap ℝ 𝕜)
  have hH : H.IsUpperHessenberg := by
    intro j k hjk
    simp [H, htri.isUpperHessenberg j k hjk]
  have hp (j : Fin n) : 0 < H j.succ j.castSucc := by
    change 0 < (T j.succ j.castSucc : 𝕜)
    exact RCLike.ofReal_pos.mpr (hpos _ _ rfl)
  have hone (j : Fin (n + 1)) :
      WithLp.toLp 2 ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜).col j) =
        EuclideanSpace.basisFun (Fin (n + 1)) 𝕜 j := by
    rw [← Matrix.mulVec_single_one, Matrix.one_mulVec, EuclideanSpace.basisFun_apply]
    rfl
  simpa only [hone] using
    (vec_eq_col_of_mul_eq_mul (Q := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜))
      (A := H) (by simp) (by simp) hH hp i)

end Arnoldi
