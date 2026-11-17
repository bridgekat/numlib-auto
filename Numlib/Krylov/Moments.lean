/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.BiLanczos
import Numlib.Analysis.InnerProductSpace.Projection.Compression

/-!
# Moment matching by Krylov compression

For an operator $A$ and initial vector $v$, the compression of $A$ to $\mathcal K_n(A,v)$
reproduces the first $n$ vectors $A^jv$. Its $n$th power gives the projection of $A^nv$. A
two-sided moment $\langle w,A^kv\rangle$ can be split into a left power and a right power,
extending the matching range if the projection preserves tests against a left Krylov space.

## Main results

* `Krylov.compressionBy_pow_apply` identifies powers below $n$.
* `Krylov.compressionBy_pow_apply_projected` identifies powers up to $n$ after projection.
* `Krylov.inner_compressionBy_pow_apply` proves the two-sided moment identity.
* `Krylov.inner_compression_pow_apply_of_isSymmetric` proves the Hermitian moment identity.
* `BiLanczos.moment_eq_hessenbergSqOf` shows that the two-sided Lanczos tridiagonal matrix
  matches the first $2n$ moments.
-/

open Polynomial

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A B : E →ₗ[𝕜] E} {v w : E} {n : ℕ}

/-- Let $Q$ fix the Krylov space $\mathcal K_n(A,v)$, and let $A_Q=QA|_{\mathcal K_n}$. Then
$A_Q^k v=A^kv$ for $k<n$. -/
theorem compressionBy_pow_apply (hn : 0 < n) (Q : E →ₗ[𝕜] subspace A v n)
    (hQ : ∀ x : subspace A v n, Q x = x) {k : ℕ} (hk : k < n) :
    (((compressionBy Q A) ^ k) ⟨v, self_mem_subspace A v hn⟩ : E) = (A ^ k) v := by
  simpa only [map_pow, aeval_X] using
    (compressionBy.aeval_apply_of_forall_pow_mem Q hQ A
      ((X : 𝕜[X]) ^ k) (x := ⟨v, self_mem_subspace A v hn⟩) fun i hi =>
        pow_apply_mem_subspace A v
          (lt_of_le_of_lt (by simpa only [natDegree_X_pow] using hi) hk))

/-- Let $Q$ fix the Krylov space $\mathcal K_n(A,v)$, and let $A_Q=QA|_{\mathcal K_n}$. Then
$A_Q^k v=Q(A^kv)$ for $k\le n$. -/
theorem compressionBy_pow_apply_projected (hn : 0 < n)
    (Q : E →ₗ[𝕜] subspace A v n) (hQ : ∀ x : subspace A v n, Q x = x) {k : ℕ} (hk : k ≤ n) :
    ((compressionBy Q A) ^ k) ⟨v, self_mem_subspace A v hn⟩ = Q ((A ^ k) v) := by
  symm
  simpa only [map_pow, aeval_X] using
    (compressionBy.apply_aeval_of_forall_pow_lt_mem Q hQ A
      ((X : 𝕜[X]) ^ k) (x := ⟨v, self_mem_subspace A v hn⟩) fun i hi =>
        pow_apply_mem_subspace A v
          (lt_of_lt_of_le (by simpa only [natDegree_X_pow] using hi) hk))

/-- Let $A_Q$ be the compression of $A$ to $\mathcal K_n(A,v)$ through a projection $Q$.
If $Q$ preserves inner products against $w,A^*w,\ldots,(A^*)^{m-1}w$ for $m>0$, then
$\langle w,A_Q^kv\rangle=\langle w,A^kv\rangle$ for $k<n+m$. -/
theorem inner_compressionBy_pow_apply (hn : 0 < n) {m : ℕ} (hm : 0 < m)
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
    (Q : E →ₗ[𝕜] subspace A v n) (hQ : ∀ x : subspace A v n, Q x = x)
    (hdual : ∀ i < m, ∀ y : E, inner 𝕜 ((B ^ i) w) (Q y : E) = inner 𝕜 ((B ^ i) w) y)
    {k : ℕ} (hk : k < n + m) :
    inner 𝕜 w ((((compressionBy Q A) ^ k) ⟨v, self_mem_subspace A v hn⟩) : E) =
      inner 𝕜 w ((A ^ k) v) := by
  have hmove (j i : ℕ) (hij : i + j ≤ m) (y : subspace A v n) :
      inner 𝕜 ((B ^ i) w) (((compressionBy Q A) ^ j) y : E) =
        inner 𝕜 ((B ^ (i + j)) w) (y : E) := by
    induction j generalizing i with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      change inner 𝕜 ((B ^ i) w) (Q (A (((compressionBy Q A) ^ j) y : E)) : E) = _
      rw [hdual i (by omega), BiLanczos.inner_apply_eq hB,
        ← Module.End.mul_apply, ← pow_succ', ih (i + 1) (by omega),
        show i + 1 + j = i + (j + 1) by omega]
  let i := k - n
  let j := min n k
  have hij : i + j = k := by dsimp [i, j]; omega
  have hi : i < m := by dsimp [i]; omega
  have hj : j ≤ n := min_le_left ..
  let x : subspace A v n := ⟨v, self_mem_subspace A v hn⟩
  change inner 𝕜 w (((compressionBy Q A) ^ k) x : E) = _
  rw [← hij, pow_add (compressionBy Q A), Module.End.mul_apply]
  have hmove' := hmove i 0 (by omega) (((compressionBy Q A) ^ j) x)
  simp only [pow_zero, Module.End.one_apply, zero_add] at hmove'
  rw [hmove', compressionBy_pow_apply_projected hn Q hQ hj, hdual i hi,
    BiLanczos.inner_pow_apply_eq hB, pow_add A, Module.End.mul_apply]

/-- The orthogonal compression of a symmetric operator $A$ to $\mathcal K_n(A,v)$
matches the first $2n$ moments $\langle v,A^kv\rangle$. -/
theorem inner_compression_pow_apply_of_isSymmetric (hA : A.IsSymmetric) (hn : 0 < n)
    {k : ℕ} (hk : k < 2 * n) :
    inner 𝕜 (⟨v, self_mem_subspace A v hn⟩ : subspace A v n)
        (((compression A (subspace A v n)) ^ k) ⟨v, self_mem_subspace A v hn⟩) =
      inner 𝕜 v ((A ^ k) v) := by
  rw [compression.eq_compressionBy, Submodule.coe_inner]
  refine inner_compressionBy_pow_apply (B := A) (w := v) (m := n) hn hn
    ((LinearMap.isSymmetric_iff_sesqForm A).1 hA) _
    (subspace A v n).orthogonalProjectionOnto_mem_subspace_eq_self ?_ (by omega)
  intro i hi y
  have h := (subspace A v n).starProjection_inner_eq_zero y ((A ^ i) v)
    (pow_apply_mem_subspace A v hi)
  rw [inner_sub_left, sub_eq_zero] at h
  change inner 𝕜 ((A ^ i) v) ((subspace A v n).starProjection y) = inner 𝕜 ((A ^ i) v) y
  simpa only [inner_conj_symm] using congrArg (starRingEnd 𝕜) h.symm

end Krylov

namespace BiLanczos

open Matrix

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A B : E →ₗ[𝕜] E} {v w : E} {m : ℕ}

/-- If the two-sided Lanczos process for $A$ and its adjoint runs without breakdown through
step $m+1$, its tridiagonal matrix $T_{m+1}$ satisfies
$\langle w,A^kv\rangle=(T_{m+1}^k)_{00}$ for every $k<2(m+1)$. The pairing of the starting
vectors is normalized to one. -/
theorem moment_eq_hessenbergSqOf (h : NoBreakdown A B v w (m + 1)) {k : ℕ}
    (hk : k < 2 * (m + 1)) :
    inner 𝕜 w ((A ^ k) v) =
      (Krylov.hessenbergSqOf (coeff A B v w) (m + 1) ^ k) 0 0 := by
  let K := Krylov.subspace A v (m + 1)
  let V : (Fin (m + 1) → 𝕜) →ₗ[𝕜] E :=
    Fintype.linearCombination 𝕜 (fun i : Fin (m + 1) => vec A B v w i)
  let W : E →ₗ[𝕜] (Fin (m + 1) → 𝕜) :=
    LinearMap.pi (fun i : Fin (m + 1) => innerₛₗ 𝕜 (dualVec A B v w i))
  have hV : LinearMap.range V = K := by
    change LinearMap.range (Fintype.linearCombination 𝕜 _) = Krylov.subspace A v (m + 1)
    rw [Fintype.range_linearCombination, ← span_vec h]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  let Q : E →ₗ[𝕜] K := (V.comp W).codRestrict K fun z =>
    hV ▸ LinearMap.mem_range_self V (W z)
  have hW (z : E) (i : Fin (m + 1)) : W z i = inner 𝕜 (dualVec A B v w i) z := rfl
  have hWV (y : Fin (m + 1) → 𝕜) : W (V y) = y := by
    ext i
    have hδ (j : Fin (m + 1)) :
        inner 𝕜 (dualVec A B v w i) (vec A B v w j) = if i = j then 1 else 0 := by
      simpa only [Fin.val_inj] using
        inner_dualVec_vec h (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt)
    rw [hW, show V y = ∑ j : Fin (m + 1), y j • vec A B v w j from
      Fintype.linearCombination_apply _ _ _, inner_sum]
    simp_rw [inner_smul_right, hδ]
    simp [mul_ite]
  have hQfix (x : K) : Q x = x := by
    obtain ⟨y, hxy⟩ : (x : E) ∈ LinearMap.range V := hV.symm ▸ x.2
    apply Subtype.ext
    change V (W x) = (x : E)
    rw [← hxy, hWV]
  have hQtest (z : E) (i : Fin (m + 1)) :
      inner 𝕜 (dualVec A B v w i) (Q z : E) = inner 𝕜 (dualVec A B v w i) z := by
    rw [← hW, ← hW]
    change W (V (W z)) i = W z i
    rw [hWV]
  have hQo (z : E) : z - (Q z : E) ∈ (Krylov.subspace B w (m + 1))ᗮ := by
    rw [← span_dualVec h, Submodule.mem_orthogonal_span]
    rintro _ ⟨i, hi, rfl⟩
    rw [inner_sub_right, hQtest z ⟨i, hi⟩, sub_self]
  have hMatch := Krylov.inner_compressionBy_pow_apply (v := v) (w := w)
    (Nat.succ_pos m) (Nat.succ_pos m) h.adjoint Q hQfix (fun i hi z => by
      have h0 := (Submodule.mem_orthogonal _ _).1 (hQo z) ((B ^ i) w)
        (Krylov.pow_apply_mem_subspace B w hi)
      rw [inner_sub_right, sub_eq_zero] at h0
      exact h0.symm) (k := k) (by omega)
  let T := Krylov.hessenbergSqOf (coeff A B v w) (m + 1)
  have hT (y : Fin (m + 1) → 𝕜) : T *ᵥ y = W (A (V y)) := by
    ext i
    rw [hW, show V y = ∑ j : Fin (m + 1), y j • vec A B v w j from
      Fintype.linearCombination_apply _ _ _, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change coeff A B v w i j * y j = _
    rw [inner_dualVec_apply_vec h (Nat.le_of_lt i.isLt) (Nat.lt_succ_iff.1 j.isLt), mul_comm]
  have hQT (x : K) : W (compressionBy Q A x : E) = T *ᵥ W x := by
    rw [hT]
    change W (V (W (A x))) = W (A (V (W x)))
    rw [hWV]
    have heq : V (W x) = (x : E) := congrArg Subtype.val (hQfix x)
    rw [heq]
  have hpower (j : ℕ) (x : K) :
      W (((compressionBy Q A) ^ j) x : E) = (T ^ j) *ᵥ W x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' (compressionBy Q A), Module.End.mul_apply, hQT, ih,
        pow_succ' T, Matrix.mulVec_mulVec]
  have hv : W v = Pi.single (0 : Fin (m + 1)) 1 := by
    ext i
    rw [hW, Pi.single_apply]
    simpa only [vec_zero, Fin.ext_iff, Fin.val_zero] using
      inner_dualVec_vec h (Nat.le_of_lt i.isLt) (Nat.zero_le _)
  rw [← hMatch]
  have hpow := congrFun (hpower k ⟨v, Krylov.self_mem_subspace A v (Nat.succ_pos m)⟩) 0
  change W (((compressionBy Q A) ^ k) ⟨v, _⟩ : E) 0 = ((T ^ k) *ᵥ W v) 0 at hpow
  rw [hW, hv, Matrix.mulVec_single_one] at hpow
  simpa [T] using hpow

end BiLanczos
