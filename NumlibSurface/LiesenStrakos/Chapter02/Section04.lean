/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.LiesenStrakos.Chapter02.Section02
import Numlib.Krylov.JacobiMatrix
import Numlib.Krylov.Lanczos
import Numlib.Krylov.BiLanczos

/-!
# §2.4. The Arnoldi and Lanczos algorithms

Arnoldi generates an orthonormal Krylov basis and an upper Hessenberg matrix. For a Hermitian
operator the compression is real symmetric tridiagonal and the recurrence has three terms. The
two-sided recurrence uses biorthogonal trial and test vectors [liesen2013krylov].

## Main definitions

* `LiesenStrakos.arnoldiVector` and `LiesenStrakos.arnoldiMGSVector` are the vector families
  for the classical and modified Gram–Schmidt algorithms.
* `LiesenStrakos.IsJacobiMatrix` is the positive-subdiagonal symmetric tridiagonal condition.
* `LiesenStrakos.biLanczosVector` gives the vector pair with the normalization of Algorithm 2.4.4.

## Main results

* `LiesenStrakos.arnoldi_basis` identifies the orthonormal basis before breakdown.
* `LiesenStrakos.arnoldiMGSVector_eq` identifies the two exact-arithmetic Arnoldi algorithms.
* `LiesenStrakos.lanczos_isJacobiMatrix` gives the Jacobi property through the grade.
* `LiesenStrakos.arnoldiHessenberg_eq_lanczosTridiagonal` identifies their compressions
  for a Hermitian operator.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The vectors of Algorithm 2.4.1 are the successive normalized classical Gram–Schmidt
orthogonalizations in the Arnoldi recurrence. Lean starts the indexing at zero. -/
noncomputable abbrev arnoldiVector (A : E →ₗ[𝕜] E) (v : E) : ℕ → E := Arnoldi.vec A v

/-- The vectors of Algorithm 2.4.2 are obtained by modified Gram–Schmidt in place of classical
Gram–Schmidt. -/
noncomputable abbrev arnoldiMGSVector (A : E →ₗ[𝕜] E) (v : E) : ℕ → E := Arnoldi.mgsVec A v

/-- In exact arithmetic the classical and modified Gram–Schmidt Arnoldi vectors coincide. -/
theorem arnoldiMGSVector_eq (A : E →ₗ[𝕜] E) (v : E) :
    arnoldiMGSVector A v = arnoldiVector A v :=
  Arnoldi.mgsVec_eq_vec A v

/-- The square Arnoldi matrix in (2.4.3) has entries $\langle v_i,Av_j\rangle$. -/
noncomputable abbrev arnoldiHessenberg (A : E →ₗ[𝕜] E) (v : E) (n : ℕ) :
    Matrix (Fin n) (Fin n) 𝕜 := Arnoldi.hessenbergSq A v n

/-- The Hermitian Lanczos matrix (2.4.6) is the real tridiagonal matrix of diagonal and
off-diagonal recurrence coefficients. -/
noncomputable abbrev lanczosTridiagonal (A : E →ₗ[𝕜] E) (v : E) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := Lanczos.tridiag A v n

/-- **Definition 2.4.1** of [liesen2013krylov].
A Jacobi matrix is real symmetric and tridiagonal with strictly positive subdiagonal entries. -/
abbrev IsJacobiMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop := T.IsJacobiMatrix

/-- Through the grade of the starting vector, the first $n$ Arnoldi vectors give an
orthonormal basis of the $n$th Krylov subspace. -/
theorem arnoldi_basis [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (v : E) {n : ℕ}
    (hn : n ≤ grade A v) :
    ∃ V : OrthonormalBasis (Fin n) 𝕜 (krylovSubspace A v n),
      ∀ i, (V i : E) = arnoldiVector A v i :=
  ⟨Arnoldi.orthonormalBasis A v hn, Arnoldi.coe_orthonormalBasis_apply A v hn⟩

/-- The Hermitian Lanczos compression through the grade is a Jacobi matrix. -/
theorem lanczos_isJacobiMatrix [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E)
    (v : E) {n : ℕ} (hn : n ≤ grade A v) :
    IsJacobiMatrix (lanczosTridiagonal A v n) := by
  refine ⟨Lanczos.tridiag_isSymm A v n, Lanczos.tridiag_isTridiagonal A v n, ?_⟩
  intro i j hij
  change 0 < Lanczos.tridiag A v n i j
  rw [Lanczos.tridiag_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hij]
  exact lt_of_le_of_ne (Lanczos.beta_nonneg A v j)
    (by
      intro h
      have hgrade := (Lanczos.beta_eq_zero_iff (A := A) v j).1 h.symm
      change n ≤ Krylov.grade A v at hn
      omega)

/-- For Hermitian $A$, the Arnoldi Hessenberg matrix agrees with the real Lanczos tridiagonal
matrix after casting each entry to the scalar field. -/
theorem arnoldiHessenberg_eq_lanczosTridiagonal (A : E →ₗ[𝕜] E) (hA : A.IsSymmetric)
    (v : E) (n : ℕ) :
    arnoldiHessenberg A v n = (lanczosTridiagonal A v n).map (algebraMap ℝ 𝕜) :=
  Lanczos.hessenbergSq_eq_map_tridiag v hA n

private noncomputable def bookBiLanczosStep (A B : E →ₗ[𝕜] E) (s : BiLanczos.State 𝕜 E) :
    Option (BiLanczos.State 𝕜 E) := by
  classical
  exact
    let vh := BiLanczos.stepVhat A s
    let wh := BiLanczos.stepWhat A B s
    let δ := (‖vh‖ : 𝕜)
    let v := δ⁻¹ • vh
    let β := inner 𝕜 wh v
    if δ = 0 ∨ β = 0 then none
    else some {
      v := v
      w := (starRingEnd 𝕜 β)⁻¹ • wh
      vPrev := s.v
      wPrev := s.w
      beta := β
      delta := δ }

private noncomputable def bookBiLanczosState (A B : E →ₗ[𝕜] E) (v w : E) :
    ℕ → Option (BiLanczos.State 𝕜 E)
  | 0 => some { v := v, w := w, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }
  | n + 1 => (bookBiLanczosState A B v w n).bind (bookBiLanczosStep A B)

/-- The right and left vectors of Algorithm 2.4.4 through breakdown. The first right vector
has unit norm, and each left vector is scaled using the conjugate of the pairing so that
its inner product with the corresponding right vector is one. Here $B=A^*$ in the book.
Once a normalization divisor vanishes, no further pair is produced. -/
noncomputable def biLanczosVector (A B : E →ₗ[𝕜] E) (v w : E)
    (_hvw : inner 𝕜 w v ≠ 0) (n : ℕ) : Option (E × E) :=
  let v₁ := (↑(‖v‖⁻¹) : 𝕜) • v
  let w₁ := (starRingEnd 𝕜 (inner 𝕜 w v₁))⁻¹ • w
  (bookBiLanczosState A B v₁ w₁ n).map fun s => (s.v, s.w)

end LiesenStrakos
