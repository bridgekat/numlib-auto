/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Moments

/-!
# Vorobyev's moment problem

The reduction of $A$ to $\mathcal K_n(A,v)$ by orthogonal compression preserves powers through
degree $n-1$ on $v$. For a Hermitian operator the reduction matches scalar moments through
degree $2n-1$. These are the operator forms of the identities of §3.7 of [liesen2013krylov].

## Main definitions

* `LiesenStrakos.Chapter03.vorobyevReduction` restricts $A$ to the Krylov space and projects the
  image orthogonally back to that space.

## Main results

* `LiesenStrakos.Chapter03.theorem_3_7_1` is the Hermitian scalar moment identity.
* `LiesenStrakos.Chapter03.theorem_3_7_4` proves the Arnoldi moment identities on the compressed
  operator.
* `LiesenStrakos.Chapter03.theorem_3_7_1_lanczos` gives the Lanczos matrix form of the Hermitian
  moment identity.
* `LiesenStrakos.Chapter03.theorem_3_7_2` proves the two-sided Lanczos moment identity.
* `LiesenStrakos.Chapter03.theorem_3_7_4_arnoldi` gives the Arnoldi matrix form of moment matching.
* `LiesenStrakos.Chapter03.bilanczos_quadrature` extends the two-sided identity to polynomials.

## Deviations from the source

* **Theorem 3.7.2** (generalization). The moment identity only uses the normalization
  $\langle w,v\rangle=1$ of the starting pair.
-/

open Polynomial
open scoped Polynomial

namespace LiesenStrakos.Chapter03

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {v : E} {n : ℕ}

/-- The Vorobyev reduction of $A$ to its Krylov space $\mathcal K_n(A,v)$ maps each vector
in the space to the orthogonal projection of its image under $A$. This is the operator of
(3.7.2)–(3.7.3) of [liesen2013krylov]. -/
noncomputable def vorobyevReduction (A : E →ₗ[𝕜] E) (v : E) (n : ℕ)
    [(Krylov.subspace A v n).HasOrthogonalProjection] :
    Krylov.subspace A v n →ₗ[𝕜] Krylov.subspace A v n :=
  compression A (Krylov.subspace A v n)

variable [(Krylov.subspace A v n).HasOrthogonalProjection]

/-- **Theorem 3.7.1, equation (3.7.4)** of [liesen2013krylov]. For Hermitian $A$, the
Vorobyev reduction to the Krylov space of order $n$ matches the moments
$\langle v,A^kv\rangle$ for $0\le k<2n$. -/
theorem theorem_3_7_1 (hA : A.IsSymmetric) (hn : 0 < n) {k : ℕ} (hk : k < 2 * n) :
    inner 𝕜 v ((A ^ k) v) =
      inner 𝕜 (⟨v, Krylov.self_mem_subspace A v hn⟩ : Krylov.subspace A v n)
        (((vorobyevReduction A v n) ^ k) ⟨v, Krylov.self_mem_subspace A v hn⟩) :=
  (Krylov.inner_compression_pow_apply_of_isSymmetric hA hn hk).symm

/-- **Theorem 3.7.4, operator form** of [liesen2013krylov]. The orthogonal compression to
$\mathcal K_n(A,v)$ matches $\langle u,A^kv\rangle$ for any test vector $u$ when $k<n$.
When $u=v$ this also holds for $k=n$. -/
theorem theorem_3_7_4 (hn : 0 < n) :
    (∀ (u : E) (k : ℕ), k < n →
      inner 𝕜 u ((A ^ k) v) =
        inner 𝕜 u ((((vorobyevReduction A v n) ^ k) ⟨v, Krylov.self_mem_subspace A v hn⟩) : E)) ∧
    inner 𝕜 v ((A ^ n) v) =
      inner 𝕜 v ((((vorobyevReduction A v n) ^ n) ⟨v, Krylov.self_mem_subspace A v hn⟩) : E) := by
  let K := Krylov.subspace A v n
  let Q : E →ₗ[𝕜] K := K.orthogonalProjectionOnto
  have hQ : ∀ x : K, Q x = x := K.orthogonalProjectionOnto_mem_subspace_eq_self
  constructor
  · intro u k hk
    change inner 𝕜 u ((A ^ k) v) = inner 𝕜 u ((((compressionBy Q A) ^ k) ⟨v, _⟩) : E)
    rw [Krylov.compressionBy_pow_apply hn Q hQ hk]
  · change inner 𝕜 v ((A ^ n) v) = inner 𝕜 v ((((compressionBy Q A) ^ n) ⟨v, _⟩) : E)
    rw [Krylov.compressionBy_pow_apply_projected hn Q hQ le_rfl]
    change inner 𝕜 v ((A ^ n) v) = inner 𝕜 v (K.starProjection ((A ^ n) v))
    rw [← K.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (Krylov.self_mem_subspace A v hn)]

section ArnoldiCoordinates

variable [FiniteDimensional 𝕜 (Krylov.fullSubspace A v)]

/-- The first-coordinate column of a power of the Arnoldi matrix consists of the coefficients
of the corresponding compressed power applied to the unit starting vector. -/
private theorem hessenbergSq_pow_entry (hv : ‖v‖ = 1) (hn : 0 < n)
    (hg : n ≤ Krylov.grade A v) (k : ℕ) (i : Fin n) :
    (Arnoldi.hessenbergSq A v n ^ k) i ⟨0, hn⟩ =
      inner 𝕜 (Arnoldi.vec A v i)
        ((((vorobyevReduction A v n) ^ k) ⟨v, Krylov.self_mem_subspace A v hn⟩) : E) := by
  let V := Arnoldi.orthonormalBasis A v hg
  have hv₀ : v ≠ 0 := by
    intro he
    simp [he] at hv
  have hfirst : V ⟨0, hn⟩ = ⟨v, Krylov.self_mem_subspace A v hn⟩ := by
    apply Subtype.ext
    rw [Arnoldi.coe_orthonormalBasis_apply, show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl,
      Arnoldi.vec_zero A v hv₀, hv]
    simp
  rw [Arnoldi.hessenbergSq_eq_toMatrix_compression A v hg]
  change ((LinearMap.toMatrixAlgEquiv V.toBasis (vorobyevReduction A v n)) ^ k) i ⟨0, hn⟩ = _
  rw [← map_pow, LinearMap.toMatrixAlgEquiv_apply, OrthonormalBasis.coe_toBasis, hfirst,
    OrthonormalBasis.coe_toBasis_repr_apply, V.repr_apply_apply, Submodule.coe_inner,
    Arnoldi.coe_orthonormalBasis_apply]

/-- **Theorem 3.7.1, equation (3.7.5)** of [liesen2013krylov]. For a Hermitian operator
and a unit starting vector, the $(0,0)$ entry of the $k$th power of its Lanczos matrix
matches the scalar moment for $k<2n$. -/
theorem theorem_3_7_1_lanczos (hA : A.IsSymmetric) (hv : ‖v‖ = 1) (hn : 0 < n)
    (hg : n ≤ Krylov.grade A v) {k : ℕ} (hk : k < 2 * n) :
    inner 𝕜 v ((A ^ k) v) = (((Lanczos.tridiag A v n ^ k) ⟨0, hn⟩ ⟨0, hn⟩ : ℝ) : 𝕜) := by
  have hv₀ : v ≠ 0 := by
    intro he
    simp [he] at hv
  have h₀ : Arnoldi.vec A v (⟨0, hn⟩ : Fin n) = v := by
    rw [show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl, Arnoldi.vec_zero A v hv₀, hv]
    simp
  have h := hessenbergSq_pow_entry hv hn hg k ⟨0, hn⟩
  rw [h₀] at h
  change (Arnoldi.hessenbergSq A v n ^ k) ⟨0, hn⟩ ⟨0, hn⟩ =
      inner 𝕜 (⟨v, Krylov.self_mem_subspace A v hn⟩ : Krylov.subspace A v n)
        (((vorobyevReduction A v n) ^ k) ⟨v, Krylov.self_mem_subspace A v hn⟩) at h
  rw [theorem_3_7_1 hA hn hk, ← h, Lanczos.hessenbergSq_eq_map_tridiag v hA]
  change ((((algebraMap ℝ 𝕜).mapMatrix (Lanczos.tridiag A v n)) ^ k) ⟨0, hn⟩ ⟨0, hn⟩) = _
  rw [← map_pow]
  rfl

/-- **Theorem 3.7.4, equation (3.7.17)** of [liesen2013krylov]. For a unit starting vector,
the Arnoldi moment of order $k<n$ is obtained by pairing the first column of $H_n^k$ with the
coordinates of the test vector projected onto the Krylov space. -/
theorem theorem_3_7_4_arnoldi (hv : ‖v‖ = 1) (hn : 0 < n) (hg : n ≤ Krylov.grade A v)
    (u : E) {k : ℕ} (hk : k < n) :
    inner 𝕜 u ((A ^ k) v) =
      ∑ i : Fin n, inner 𝕜 u (Arnoldi.vec A v i) * (Arnoldi.hessenbergSq A v n ^ k) i ⟨0, hn⟩ := by
  let V := Arnoldi.orthonormalBasis A v hg
  rw [(theorem_3_7_4 hn).1 u k hk]
  let y : Krylov.subspace A v n :=
    (vorobyevReduction A v n ^ k) ⟨v, Krylov.self_mem_subspace A v hn⟩
  change inner 𝕜 u (y : E) = _
  have hy := congrArg Subtype.val (V.sum_repr y)
  simp only [Submodule.coe_sum, SetLike.val_smul] at hy
  rw [← hy, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, mul_comm, hessenbergSq_pow_entry hv hn hg,
    ← Arnoldi.coe_orthonormalBasis_apply A v hg, ← Submodule.coe_inner, ← V.repr_apply_apply]

/-- **Theorem 3.7.4, final case** of [liesen2013krylov]. For the unit starting vector as test
vector the moment of order $n$ is also matched, at the first diagonal entry of $H_n^n$. -/
theorem theorem_3_7_4_arnoldi_self (hv : ‖v‖ = 1) (hn : 0 < n)
    (hg : n ≤ Krylov.grade A v) :
    inner 𝕜 v ((A ^ n) v) = (Arnoldi.hessenbergSq A v n ^ n) ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hv₀ : v ≠ 0 := by
    intro he
    simp [he] at hv
  have h₀ : Arnoldi.vec A v (⟨0, hn⟩ : Fin n) = v := by
    rw [show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl, Arnoldi.vec_zero A v hv₀, hv]
    simp
  rw [hessenbergSq_pow_entry hv hn hg, h₀]
  exact (theorem_3_7_4 hn).2

end ArnoldiCoordinates

/-- **Theorem 3.7.2** of [liesen2013krylov]. If two-sided Lanczos runs without breakdown
through step $m+1$, its tridiagonal matrix agrees with the first $2(m+1)$ scalar moments of
the original operator for the starting pair.

The normalization $\langle w,v\rangle=1$ is part of the no-breakdown hypothesis. The
identity also holds when the norm of $v$ differs from one. -/
theorem theorem_3_7_2 {B : E →ₗ[𝕜] E} {w : E} {m : ℕ}
    (h : BiLanczos.NoBreakdown A B v w (m + 1)) {k : ℕ} (hk : k < 2 * (m + 1)) :
    inner 𝕜 w ((A ^ k) v) =
      (Krylov.hessenbergSqOf (BiLanczos.coeff A B v w) (m + 1) ^ k) 0 0 :=
  BiLanczos.moment_eq_hessenbergSqOf h hk

/-- The generalized Gauss–Christoffel quadrature of §3.7.4 of [liesen2013krylov] replaces
$\langle w,p(A)v\rangle$ with the first diagonal entry of $p(T_{m+1})$. It is exact for
polynomials of degree less than $2(m+1)$ when two-sided Lanczos runs without breakdown
through step $m+1$. -/
theorem bilanczos_quadrature {B : E →ₗ[𝕜] E} {w : E} {m : ℕ}
    (h : BiLanczos.NoBreakdown A B v w (m + 1)) {p : 𝕜[X]} (hp : p.natDegree < 2 * (m + 1)) :
    BiLanczos.moment A v w p =
      aeval (Krylov.hessenbergSqOf (BiLanczos.coeff A B v w) (m + 1)) p 0 0 := by
  unfold BiLanczos.moment
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, inner_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [LinearMap.smul_apply, inner_smul_right, Matrix.smul_apply, smul_eq_mul,
    theorem_3_7_2 h (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.1 hj)) hp)]

end LiesenStrakos.Chapter03
